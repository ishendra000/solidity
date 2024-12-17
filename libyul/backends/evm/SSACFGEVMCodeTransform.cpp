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


#include <libyul/backends/evm/SSACFGEVMCodeTransform.h>

#include <libyul/backends/evm/ControlFlowGraph.h>
#include <libyul/backends/evm/SSAControlFlowGraphBuilder.h>

#include <libsolutil/StringUtils.h>
#include <libsolutil/Visitor.h>

#include <range/v3/range/conversion.hpp>
#include <range/v3/view/enumerate.hpp>
#include <range/v3/view/iota.hpp>
#include <range/v3/view/reverse.hpp>
#include <range/v3/view/zip.hpp>

using namespace solidity;
using namespace solidity::yul;

namespace
{

std::string ssaCfgVarToString(SSACFG const& _cfg, SSACFG::ValueId _var)
{
	if (_var.value == std::numeric_limits<size_t>::max())
		return "INVALID";
	auto const& info = _cfg.valueInfo(_var);
	return std::visit(
		util::GenericVisitor{
			[&](SSACFG::UnreachableValue const&) -> std::string {
				return "[unreachable]";
			},
			[&](SSACFG::LiteralValue const& _literal) {
				std::stringstream str;
				str << _literal.value;
				return str.str();
			},
			[&](auto const&) {
				return "v" + std::to_string(_var.value);
			}
		},
		info
	);
}

std::string stackSlotToString(SSACFG const& _cfg, ssacfg::StackSlot const& _slot)
{
	return std::visit(util::GenericVisitor{
		[&](SSACFG::ValueId _value) {
			return ssaCfgVarToString(_cfg, _value);
		},
		[](AbstractAssembly::LabelID _label) {
			return "LABEL[" + std::to_string(_label) + "]";
		}
	}, _slot);
}
std::string stackToString(SSACFG const& _cfg, std::vector<ssacfg::StackSlot> const& _stack)
{
	return "[" + util::joinHumanReadable(_stack | ranges::views::transform([&](ssacfg::StackSlot const& _slot) { return stackSlotToString(_cfg, _slot); })) + "]";
}
}

std::vector<ssacfg::StackSlot>
ssacfg::PhiMapping::transformStackToPhiValues(std::vector<StackSlot> const& _stack) const
{
	auto const map = [this](StackSlot const& _slot)
	{
		if (auto* valueId = std::get_if<SSACFG::ValueId>(&_slot))
		{
			auto const it = m_reverseMapping.find(*valueId);
			return it == m_reverseMapping.end() ? _slot : it->second;
		}
		return _slot;
	};
	return _stack | ranges::views::transform(map) | ranges::to<std::vector>;
}


void ssacfg::Stack::pop(bool _generateInstruction)
{
	yulAssert(!m_stack.empty());
	m_stack.pop_back();
	if (_generateInstruction)
		m_assembly.get().appendInstruction(evmasm::Instruction::POP);
}

void ssacfg::Stack::swap(size_t const _depth, bool _generateInstruction)
{
	yulAssert(m_stack.size() > _depth);
	std::swap(m_stack[m_stack.size() - _depth - 1], m_stack.back());
	if (_generateInstruction)
		m_assembly.get().appendInstruction(evmasm::swapInstruction(static_cast<unsigned>(_depth)));
}

void ssacfg::Stack::push(SSACFG::ValueId const& _value, SSACFG const& _cfg, bool _generateInstruction)
{
	m_stack.emplace_back(_value);
	if (_generateInstruction)
		std::visit(util::GenericVisitor{
			[](SSACFG::UnreachableValue const&) { solAssert(false); },
			[](SSACFG::VariableValue const&) { solAssert(false); },
			[](SSACFG::PhiValue const&) { solAssert(false); },
			[&](SSACFG::LiteralValue const& _literal) {
				m_assembly.get().appendConstant(_literal.value);
			}
		}, _cfg.valueInfo(_value));
}

void ssacfg::Stack::dup(size_t const _depth, bool _generateInstruction)
{
	m_stack.push_back(m_stack[m_stack.size() - _depth - 1]);
	if (_generateInstruction)
		m_assembly.get().appendInstruction(evmasm::dupInstruction(static_cast<unsigned>(_depth + 1)));
}

bool ssacfg::Stack::dup(StackSlot const& _slot, bool _generateInstruction)
{
	auto const offset = slotIndex(_slot);
	if (offset)
		dup(*offset, _generateInstruction);
	return offset.has_value();
}

std::optional<size_t> ssacfg::Stack::slotIndex(StackSlot const& _slot) const
{
	auto const offset = util::findOffset(m_stack | ranges::views::reverse, _slot);
	if (offset)
		yulAssert(m_stack[m_stack.size() - *offset - 1] == _slot);
	return offset;
}


void ssacfg::Stack::bringUpSlot(StackSlot const& _slot, SSACFG const& _cfg)
{
	std::visit(util::GenericVisitor{
		[&](SSACFG::ValueId _value) {
			if (!dup(_slot))
				push(_value, _cfg);
		},
		[&](AbstractAssembly::LabelID _label) {
			m_assembly.get().appendLabelReference(_label);
			m_stack.emplace_back(_label);
		}
	}, _slot);
}

void ssacfg::Stack::createExactStack(std::vector<StackSlot> const& _target, SSACFG const& _cfg, PhiMapping const& _phis)
{
	auto const mappedTarget = _phis.transformStackToPhiValues(_target);
	auto mappedStack = Stack(m_assembly, _phis.transformStackToPhiValues(m_stack));
	mappedStack.createExactStack(mappedTarget, _cfg);
	// now we go through the mapped stack and undo the phi mapping where required
	for (size_t i = 0; i < mappedStack.size(); ++i)
	{
		if (mappedStack.m_stack[i] != _target[i])
		{
			yulAssert(std::holds_alternative<SSACFG::ValueId>(mappedStack.m_stack[i]));
			mappedStack.m_stack[i] = _phis.apply(std::get<SSACFG::ValueId>(mappedStack.m_stack[i]));
			yulAssert(mappedStack.m_stack[i] == _target[i]);
		}
	}
	m_stack = mappedStack.m_stack;
	yulAssert(m_stack == _target, fmt::format("Stack target mismatch: current = {} =/= {} = target", stackToString(_cfg, m_stack), stackToString(_cfg, _target)));
}

void ssacfg::Stack::createExactStack(std::vector<StackSlot> const& _target, SSACFG const& _cfg)
{
	std::cout << fmt::format("Creating exact stack {} from {}", stackToString(_cfg, _target), stackToString(_cfg, m_stack)) << std::endl;

	{
		auto const histogram = [](std::vector<StackSlot> const& _stack)
		{
			std::map<StackSlot, size_t> counts;
			for (auto const& targetSlot : _stack)
				counts[targetSlot]++;
			return counts;
		};
		auto const targetCounts = histogram(_target);
		auto const stackCounts = histogram(m_stack);
		// first, remove everything from the stack that occurs more often than what's in the target
		for (auto const& [slot, count]: stackCounts)
		{
			size_t targetCount = 0;
			if (auto it = targetCounts.find(slot); it != targetCounts.end())
				targetCount = it->second;
			if (count > targetCount)
				for (size_t i = 0; i < count - targetCount; ++i)
				{
					auto depth = util::findOffset(m_stack | ranges::views::reverse, slot);
					yulAssert(depth);
					if (depth > 0)
						swap(*depth);
					pop();
				}
		}
		// then dup/push stuff that's not there yet in appropriate quantities
		for (auto const& [slot, targetCount]: targetCounts)
		{
			auto findIt = stackCounts.find(slot);
			if (findIt == stackCounts.end())
			{
				for (size_t i = 0; i < targetCount; ++i)
					std::visit(util::GenericVisitor{
						[&](SSACFG::ValueId const& _value) {
							push(_value, _cfg);
						},
						[this](AbstractAssembly::LabelID const& _label)
						{
							m_assembly.get().appendLabelReference(_label);
							m_stack.emplace_back(_label);
						}
					}, slot);
			}
			else
			{
				auto currentCount = std::min(targetCount, findIt->second);
				yulAssert(currentCount <= targetCount);
				for (size_t i = 0; i < targetCount - currentCount; ++i)
				{
					auto const depth = slotIndex(slot);
					yulAssert(depth);
					dup(*depth);
				}
			}
		}
	}
	// now we have the same elements in the stack just in a different order
	yulAssert(size() == _target.size());
	for (size_t i = 0; i < _target.size(); ++i)
	{
		// look at the bottom element of the stack and swap something there if it's not already the correct slot
		if (m_stack[i] != _target[i])
		{
			auto const depth = util::findOffset(m_stack | ranges::views::reverse, _target[i]);
			if (depth > 0)
				swap(*depth);
			yulAssert(m_stack.back() == _target[i]);
			swap(m_stack.size() - 1 - i);
		}
		yulAssert(
			m_stack[i] == _target[i],
			fmt::format("Stack target mismatch: current[{}] = {} =/= {} = target[{}]", i, stackSlotToString(_cfg, m_stack[i]), stackSlotToString(_cfg, _target[i]), i)
		);
	}

	yulAssert(size() == _target.size());
	yulAssert(m_stack == _target, fmt::format("Stack target mismatch: current = {} =/= {} = target", stackToString(_cfg, m_stack), stackToString(_cfg, _target)));
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

	ScopedSaveAndRestore stackSave{m_stack, ssacfg::Stack{m_assembly}};

	auto &data = blockData(_block);
	if (!data.label) {
		data.label = m_assembly.newLabelId();
	}
	m_assembly.appendLabel(*data.label);

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
		[&](SSACFG::BasicBlock::Jump const& _jump)
		{
			auto& targetLabel = blockData(_jump.target).label;
			if (!targetLabel)
				targetLabel = m_assembly.newLabelId();
			auto& targetStack = blockData(_jump.target).stackIn;
			if (!targetStack)
				// initial stack layout is just the live-ins (would also suffice to be the stack top)
				targetStack = m_liveness.liveIn(_jump.target) | ranges::to<std::vector<ssacfg::StackSlot>>;

			m_stack.createExactStack(*targetStack, m_cfg, ssacfg::PhiMapping{m_cfg, _block, _jump.target});

			// reference: https://github.com/ethereum/solidity/blob/ssaCfg-codegen/libyul/backends/evm/SSAEVMCodeTransform.cpp
			// assumption: results of phi fcts are always in the live-in of the corresponding block
			//	-> generate stack layout with the phi functions somewhere on stack
			//  -> when entering a block, we record the predecessor and replace all phis with the actual values
			//		this can happen in the operator()(blockid, predecessor block id) function call
			//  -> stack layout when entering a block should always be [phis, rest of live-in, junk]
			/*if (!targetStack)

			else
				yulAssert(false, "todo we already have a target stack, need to modify it to the current one");*/
			/*if (targetStack)
				m_stack.createExactStack();
				createExactStack(targetStackToCurrentStack(_jump.target));
			else
			{
				cleanUpStack();
				targetStack = currentStackToTargetStack(_jump.target);
			}*/
			m_assembly.appendJumpTo(*targetLabel);
			if (!m_generatedBlocks[_jump.target.value])
				(*this)(_jump.target);
		},
		[&](SSACFG::BasicBlock::ConditionalJump const& _conditionalJump)
		{
			auto& nonZeroLayout = blockData(_conditionalJump.nonZero).stackIn;
			auto& nonZeroLabel = blockData(_conditionalJump.nonZero).label;
			if (!nonZeroLabel)
				nonZeroLabel = m_assembly.newLabelId();
			auto& zeroLayout = blockData(_conditionalJump.zero).stackIn;
			auto& zeroLabel = blockData(_conditionalJump.zero).label;
			if (!zeroLabel)
				zeroLabel = m_assembly.newLabelId();
			if (!nonZeroLayout)
				nonZeroLayout = m_liveness.liveIn(_conditionalJump.nonZero) | ranges::to<std::vector<ssacfg::StackSlot>>;
			if (!zeroLayout)
				zeroLayout = m_liveness.liveIn(_conditionalJump.zero) | ranges::to<std::vector<ssacfg::StackSlot>>;
			m_stack.createExactStack(
				*nonZeroLayout + std::vector<ssacfg::StackSlot>{_conditionalJump.condition},
				m_cfg
			);

			// Emit the conditional jump to the non-zero label and update the stored stack.
			m_assembly.appendJumpToIf(*nonZeroLabel);
			m_stack.pop(false);

			m_stack.createExactStack(*zeroLayout, m_cfg, ssacfg::PhiMapping{m_cfg, _block, _conditionalJump.zero});
			m_assembly.appendJumpTo(*zeroLabel);
			if (!m_generatedBlocks[_conditionalJump.zero.value])
				(*this)(_conditionalJump.zero);
			if (!m_generatedBlocks[_conditionalJump.nonZero.value])
				(*this)(_conditionalJump.nonZero);
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
	auto liveOutWithoutOutputs = std::set<ssacfg::StackSlot>(_liveOut.begin(), _liveOut.end()) - _operation.outputs;
	m_stack.createExactStack(std::vector(liveOutWithoutOutputs.begin(), liveOutWithoutOutputs.end()) + requiredStackTop, m_cfg);
	std::visit(util::GenericVisitor {
		[&](SSACFG::BuiltinCall const& _builtin) {
			m_assembly.setSourceLocation(originLocationOf(_builtin));
			dynamic_cast<BuiltinFunctionForEVM const&>(_builtin.builtin.get()).generateCode(
				_builtin.call,
				m_assembly,
				m_builtinContext
			);
		},
		[&](SSACFG::Call const& _call) {
			m_assembly.setSourceLocation(originLocationOf(_call));
			m_assembly.appendJumpTo(
				functionLabel(_call.function),
				static_cast<int>(_call.function.get().numReturns - _call.function.get().numArguments) - (_call.canContinue ? 1 : 0),
				AbstractAssembly::JumpType::IntoFunction
			);
			if (returnLabel)
				m_assembly.appendLabel(*returnLabel);
	   },
	}, _operation.kind);
	for (size_t i = 0; i < _operation.inputs.size() + (returnLabel ? 1 : 0); ++i)
		m_stack.pop(false);
	for (auto value: _operation.outputs)
		m_stack.push(value, m_cfg, false);
}
