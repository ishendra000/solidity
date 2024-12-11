/*
	This file is part of solidity.

	solidity is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.

	solidity is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with solidity.  If not, see <http://www.gnu.org/licenses/>.
*/
// SPDX-License-Identifier: GPL-3.0


#include <libsolutil/Visitor.h>
#include <libyul/backends/evm/SSACFGEVMCodeTransform.h>

#include <libyul/backends/evm/ControlFlowGraph.h>
#include <libyul/backends/evm/SSAControlFlowGraphBuilder.h>

#include <range/v3/range/conversion.hpp>
#include <range/v3/view/enumerate.hpp>
#include <range/v3/view/filter.hpp>
#include <range/v3/view/reverse.hpp>
#include <range/v3/view/zip.hpp>

using namespace solidity::yul;

void ssacfg::Stack::pop()
{
	yulAssert(!m_stack.empty());
	m_stack.pop_back();
	m_assembly.get().appendInstruction(evmasm::Instruction::POP);
}

void ssacfg::Stack::swap(size_t const _depth)
{
	yulAssert(m_stack.size() > _depth);
	std::swap(m_stack[m_stack.size() - _depth - 1], m_stack.back());
	m_assembly.get().appendInstruction(evmasm::swapInstruction(static_cast<unsigned>(_depth)));
}

void ssacfg::Stack::bringUpSlot(StackSlot const& _slot, SSACFG const& _cfg)
{
	std::visit(util::GenericVisitor{
		[&](SSACFG::ValueId _value) {
			if (auto depth = util::findOffset(m_stack | ranges::views::reverse, _slot))
			{
				m_assembly.get().appendInstruction(evmasm::dupInstruction(static_cast<unsigned>(*depth + 1)));
				m_stack.emplace_back(_slot);
				return;
			}
			std::visit(util::GenericVisitor{
				[&](SSACFG::UnreachableValue const&) { solAssert(false); },
				[&](SSACFG::VariableValue const&) { solAssert(false); },
				[&](SSACFG::PhiValue const&) { solAssert(false); },
				[&](SSACFG::LiteralValue const& _literal) {
					m_assembly.get().appendConstant(_literal.value);
					m_stack.emplace_back(_value);
				}
			}, _cfg.valueInfo(_value));
		},
		[&](AbstractAssembly::LabelID _label) {
			m_assembly.get().appendLabelReference(_label);
			m_stack.emplace_back(_label);
		}
	}, _slot);
}

void ssacfg::Stack::createExactStack(std::vector<StackSlot> const& _target)
{
	auto const targetPositions = [&](StackSlot const& _slot){
		std::vector<size_t> positions;
		for (auto const& [targetPosition, slot]: _target | ranges::views::enumerate)
			if (slot == _slot)
				positions.emplace_back(targetPosition);
		return positions;
	};
	// as long as the stack isn't final, dup and swap the current top wherever it needs to go
	while (m_stack.size() > _target.size() || (!m_stack.empty() && _target[m_stack.size() - 1] != m_stack.back()))
	{
		// Try to swap it to where it is still needed - or otherwise pop it.
		swapTopToTargetOrPop();
	}
	yulAssert(_target == m_stack);
}


std::vector<StackTooDeepError> SSACFGEVMCodeTransform::run(
	AbstractAssembly& _assembly,
	ControlFlowLiveness const& _liveness,
	BuiltinContext& _builtinContext,
	UseNamedLabels _useNamedLabelsForFunctions)
{
	{
		// todo remove, just for debugging
		fmt::print("{}\n", _liveness.toDot());
		std::fflush(nullptr);
	}
	auto const& controlFlow = _liveness.controlFlow.get();
	auto functionLabels = registerFunctionLabels(_assembly, controlFlow, _useNamedLabelsForFunctions);

	SSACFGEVMCodeTransform mainCodeTransform(
		_assembly,
		_builtinContext,
		functionLabels,
		*controlFlow.mainGraph,
		*_liveness.mainLiveness
	);

	// Force main entry block to start from an empty stack.
	mainCodeTransform.blockData(SSACFG::BlockId{0}).stackIn = std::make_optional<std::vector<ssacfg::StackSlot>>();
	mainCodeTransform(SSACFG::BlockId{0});

	std::vector<StackTooDeepError> stackErrors;
	if (!mainCodeTransform.m_stackErrors.empty())
		stackErrors = std::move(mainCodeTransform.m_stackErrors);

	for (auto const& [functionAndGraph, functionLiveness]: ranges::zip_view(controlFlow.functionGraphMapping, _liveness.functionLiveness))
	{
		auto const& [function, functionGraph] = functionAndGraph;
		SSACFGEVMCodeTransform functionCodeTransform(
			_assembly,
			_builtinContext,
			functionLabels,
			*functionGraph,
			*functionLiveness
		);
		functionCodeTransform.transformFunction(*function);
		if (!functionCodeTransform.m_stackErrors.empty())
			stackErrors.insert(stackErrors.end(), functionCodeTransform.m_stackErrors.begin(), functionCodeTransform.m_stackErrors.end());
	}

	/*if (auto adapter = dynamic_cast<EthAssemblyAdapter*>(&_assembly))
	{
		// todo remove, just for debugging
		std::cout << "------------------------------------------" << std::endl;
		std::cout << *adapter << std::endl;
	}*/
	return stackErrors;
}

std::map<Scope::Function const*, AbstractAssembly::LabelID> SSACFGEVMCodeTransform::registerFunctionLabels
(
	AbstractAssembly& _assembly,
	ControlFlow const& _controlFlow,
	UseNamedLabels _useNamedLabelsForFunctions
)
{
	std::map<Scope::Function const*, AbstractAssembly::LabelID> functionLabels;

	for (auto const& [_function, _functionGraph]: _controlFlow.functionGraphMapping)
	{
		std::set<YulString> assignedFunctionNames;
		bool nameAlreadySeen = !assignedFunctionNames.insert(_function->name).second;
		if (_useNamedLabelsForFunctions == UseNamedLabels::YesAndForceUnique)
			yulAssert(!nameAlreadySeen);
		bool useNamedLabel = _useNamedLabelsForFunctions != UseNamedLabels::Never && !nameAlreadySeen;
		functionLabels[_function] = useNamedLabel ?
			_assembly.namedLabel(
				_function->name.str(),
				_functionGraph->arguments.size(),
				_functionGraph->returns.size(),
				_functionGraph->debugData ? _functionGraph->debugData->astID : std::nullopt
			) :
			_assembly.newLabelId();
	}
	return functionLabels;
}

 SSACFGEVMCodeTransform::SSACFGEVMCodeTransform(
	AbstractAssembly& _assembly,
	BuiltinContext& _builtinContext,
	FunctionLabels _functionLabels,
	SSACFG const& _cfg,
	SSACFGLiveness const& _liveness
):
	m_assembly(_assembly),
	m_builtinContext(_builtinContext),
	m_cfg(_cfg),
	m_liveness(_liveness),
	m_functionLabels(std::move(_functionLabels)),
	m_stack(_assembly),
	m_blockData(_cfg.numBlocks()),
	m_generatedBlocks(_cfg.numBlocks(), false)
{ }

void SSACFGEVMCodeTransform::transformFunction(Scope::Function const& _function)
{
	// Force function entry block to start from initial function layout.
	m_assembly.appendLabel(functionLabel(_function));
	blockData(m_cfg.entry).stackIn = m_cfg.arguments | ranges::views::transform([](auto&& _tuple) { return std::get<1>(_tuple); }) | ranges::to<std::vector<ssacfg::StackSlot>>;
	(*this)(m_cfg.entry);
}

void SSACFGEVMCodeTransform::operator()(SSACFG::BlockId const _block)
{
	yulAssert(!m_generatedBlocks[_block.value]);
	m_generatedBlocks[_block.value] = true;

	auto &data = blockData(_block);
	if (!data.label) {
		data.label = m_assembly.newLabelId();
		m_assembly.appendLabel(*data.label);
	}

	{
		// copy stackIn into stack
		yulAssert(data.stackIn, fmt::format("No starting layout for block id {}", _block.value));
		m_stack = ssacfg::Stack{m_assembly, *data.stackIn};
	}

	m_assembly.setStackHeight(static_cast<int>(m_stack.size()));
	// check that we have as much liveness info as there are ops in the block
	yulAssert(m_cfg.block(_block).operations.size() == m_liveness.operationsLiveOut(_block).size());

	// for each op with respective live-out, descend into op
	for (auto&& [op, liveOut]: ranges::zip_view(m_cfg.block(_block).operations, m_liveness.operationsLiveOut(_block)))
		(*this)(op, liveOut);

	util::GenericVisitor exitVisitor{
		[&](SSACFG::BasicBlock::MainExit const& /*_mainExit*/)
		{
			m_assembly.appendInstruction(evmasm::Instruction::STOP);
		},
		[](auto const&)
		{
			yulAssert(false, "unhandled");
		}
	};
	std::visit(exitVisitor, m_cfg.block(_block).exit);
}

void SSACFGEVMCodeTransform::operator()(SSACFG::Operation const& _operation, std::set<SSACFG::ValueId> const& _liveOut)
{
	std::vector<ssacfg::StackSlot> requiredStackTop;
	std::optional<AbstractAssembly::LabelID> returnLabel;
	if (auto const* call = std::get_if<SSACFG::Call>(&_operation.kind))
		if (call->canContinue)
		{
			returnLabel = m_assembly.newLabelId();
			requiredStackTop.emplace_back(*returnLabel);
		}
	// todo sort by inverse order of occurrence
	requiredStackTop += _operation.inputs;
	// literals should have been pulled out
	// todo double check and document reason!
	yulAssert(std::none_of(
		_liveOut.begin(),
		_liveOut.end(),
		[this](SSACFG::ValueId _valueId){ return m_cfg.isLiteralValue(_valueId); }
	));
	m_stack.createExactStack(std::vector<ssacfg::StackSlot>(_liveOut.begin(), _liveOut.end()) + requiredStackTop);
}
