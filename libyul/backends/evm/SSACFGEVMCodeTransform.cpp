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
#include <range/v3/view/zip.hpp>

using namespace solidity::yul;

std::vector<StackTooDeepError> SSACFGEVMCodeTransform::run(
	AbstractAssembly& _assembly,
	AsmAnalysisInfo& _analysisInfo,
	Block const& _block,
	EVMDialect const& _dialect,
	BuiltinContext& _builtinContext,
	UseNamedLabels _useNamedLabelsForFunctions)
{
	std::unique_ptr<ControlFlow> controlFlow = SSAControlFlowGraphBuilder::build(_analysisInfo, _dialect, _block);
	ControlFlowLiveness liveness(*controlFlow);
	{
		// todo remove, just for debugging
		fmt::print("{}\n", controlFlow->toDot(&liveness));
		std::fflush(nullptr);
	}
	auto functionLabels = registerFunctionLabels(_assembly, *controlFlow, _useNamedLabelsForFunctions);

	SSACFGEVMCodeTransform mainCodeTransform(
		_assembly,
		_builtinContext,
		functionLabels,
		*controlFlow->mainGraph,
		*liveness.mainLiveness
	);

	// Force main entry block to start from an empty stack.
	mainCodeTransform.blockData(SSACFG::BlockId{0}).stackIn = std::make_optional(std::vector<StackSlot>{});
	mainCodeTransform(SSACFG::BlockId{0});

	std::vector<StackTooDeepError> stackErrors;
	if (!mainCodeTransform.m_stackErrors.empty())
		stackErrors = std::move(mainCodeTransform.m_stackErrors);

	for (auto const& [functionAndGraph, functionLiveness]: ranges::zip_view(controlFlow->functionGraphMapping, liveness.functionLiveness))
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
	m_blockData(_cfg.numBlocks()),
	m_generatedBlocks(_cfg.numBlocks(), false)
{ }

void SSACFGEVMCodeTransform::transformFunction(Scope::Function const& _function)
{
	// Force function entry block to start from initial function layout.
	m_assembly.appendLabel(functionLabel(_function));
	blockData(m_cfg.entry).stackIn = m_cfg.arguments | ranges::views::transform([](auto&& _tuple) { return std::get<1>(_tuple); }) | ranges::to<std::vector<StackSlot>>;
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
		m_stack = *data.stackIn;
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
	std::vector<StackSlot> requiredStackTop;
	std::optional<AbstractAssembly::LabelID> returnLabel;
	if (auto const* call = std::get_if<SSACFG::Call>(&_operation.kind))
		if (call->canContinue)
		{
			returnLabel = m_assembly.newLabelId();
			requiredStackTop.emplace_back(*returnLabel);
		}
	// todo sort by inverse order of occurrence
	requiredStackTop += _operation.inputs;
	yulAssert(std::none_of(
		_liveOut.begin(),
		_liveOut.end(),
		[this](SSACFG::ValueId _valueId){ return m_cfg.isLiteralValue(_valueId); }
	));

}
