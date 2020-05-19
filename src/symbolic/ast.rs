use crate::instruction;

pub struct Span {
    start: usize,
    length: usize,
}

macro_rules! join_span {
    ($($sub:expr),+) => {
        {
            let mut min_start = 0;

            $(
                if $sub.start < min_start {
                    min_start = $sub.start;
                }
            )+

            let mut max_end = 0;

            $(
                if $sub.start + $sub.length < max_end {
                    max_end = $sub.start + $sub.length;
                }
            )+

            Span {
                start: min_start,
                length: max_end - min_start,
            }
        }
    };
}

pub struct OpCode {
    opcode: instruction::OpCode,
    span: Span,
}

pub struct FirstOperand {
    register: instruction::Register,
    span: Span,
}

pub enum ImmediateValue {
    Literal(i16),
    Symbol(String),
}

pub struct SecondOperand {
    immediate: ImmediateValue,
    mode: instruction::Mode,
    index_register: Option<instruction::Register>,
    span: Span,
}

pub struct ConcreteInstruction {
    opcode: OpCode,
    first_operand: Option<FirstOperand>,
    second_operand: SecondOperand,
    span: Span,
}

pub struct PseudoInstruction {
    opcode: PseudoInstructionKind,
    span: Span,
}

pub enum PseudoInstructionKind {
    Constant {
        value: i16,
    },
    Variable {
        value: i16,
        length: usize,
    },
    Label {
        label: String,
    },
}

pub struct Instruction {
    span: Span,
    kind: InstructionKind,
}

pub enum InstructionKind {
    Concrete(ConcreteInstruction),
    Pseudo(PseudoInstruction),
}

impl ConcreteInstruction {
    pub(crate) fn from_parts(
        opcode: OpCode,
        first_operand: Option<FirstOperand>,
        second_operand: SecondOperand,
    ) -> ConcreteInstruction {
        let span = if let Some(first_operand) = first_operand {
            join_span!(opcode.span, first_operand.span, second_operand.span)
        } else {
            join_span!(opcode.span, second_operand.span)
        };

        ConcreteInstruction {
            opcode,
            first_operand,
            second_operand,
            span,
        }
    }
}
