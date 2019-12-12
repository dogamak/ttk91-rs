//! types for representing instructions and their parts

use std::fmt;

/// Describes the predicate for a (un)conditional jump instruction.
///
/// These conditions can be negated with the [`Jump` opcode](OpCode::Jump)'s `negated` field.
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum JumpCondition {
    /// Unconditional jump. (`JUMP`)
    Unconditional,

    /// Jump if the first operand is positive. (`JPOS`)
    Positive,

    /// Jump if the first operand is negative. (`JNEG`)
    Negative,

    /// Jump if the first operand is zero. (`JZER`)
    Zero,

    /// Jump if the [equal-flag](crate::emulator::Flags::equal) is set. (`JEQU`)
    Equal,

    /// Jump if the [less-flag](crate::emulator::Flags::less) is set. (`JLES`)
    Less,

    /// Jump if the [greater-flag](crate::emulator::Flags::less) is set. (`JLES`)
    Greater,
}

/// Instructions of the TTK91 instruction architecture.
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum OpCode {
    /// Does nothing besides incrementing the program counter.
    NoOperation,

    /// Copies a value from a register into a memory location.
    Store,

    /// Copies a constant value or a value from a memory location into a register.
    Load,

    /// Requests a value from an input device.
    In,

    /// Sends a value from a register to an output device.
    Out,

    /// Adds the value of the second operand into a register.
    Add,

    /// Subtracts the value of the second operand from a register.
    Subtract,

    /// Multiplies the value of a register by the value of the second operand.
    Multiply,

    /// Divides the value of a register by the value of the second operand.
    Divide,

    /// Divides the value of a register with the value of the second operand and stores the
    /// remainder.
    Modulo,

    /// Performs a binary and operation on a register.
    And,

    /// Performs a binary or operation on a register.
    Or,
    
    /// Performs a binary xor operation on a register.
    Xor,

    /// Shifts the value of a register left by the number of bits defined by the second operand.
    ShiftLeft,

    /// Shifts the value of a register right by the number of bits defined by the second operand.
    ShiftRight,

    /// Performs a bitwise not operation on a register.
    Not,

    /// Shifts the value of a register by a number of bits defined by the second operand.
    /// Preserves the sign of the value.
    ArithmeticShiftRight,

    /// Compares the value of the first operand with the value of the second operand and stores the
    /// result in the [State register](crate::emulator::Flags).
    Compare,

    /// Changes the value of the program counter if a condition is met. The condition defined with
    /// the `condition` field can be negated with the `negated` field.
    Jump {
        /// The condition that needs to be met in order for the jump to happen.
        condition: JumpCondition,
        /// If this is set to `true`, jump is the condition is _not_ met.
        negated: bool,
    },

    Call,
    Exit,
    Push,
    Pop,
    PushRegisters,
    PopRegisters,

    SupervisorCall,
}

impl OpCode {
    pub fn as_byte(&self) -> u8 {
        match self {
            OpCode::NoOperation => 0x00,

            OpCode::Store => 0x01,
            OpCode::Load => 0x02,
            OpCode::In => 0x03,
            OpCode::Out => 0x04,

            OpCode::Add => 0x11,
            OpCode::Subtract => 0x12,
            OpCode::Multiply => 0x13,
            OpCode::Divide => 0x14,
            OpCode::Modulo => 0x15,

            OpCode::And => 0x16,
            OpCode::Or => 0x17,
            OpCode::Xor => 0x18,
            OpCode::ShiftLeft => 0x19,
            OpCode::ShiftRight => 0x1A,
            OpCode::Not => 0x1B,
            OpCode::ArithmeticShiftRight => 0x1C,

            OpCode::Compare => 0x1F,

            OpCode::Jump { negated: _, condition: JumpCondition::Unconditional } => 0x20,

            OpCode::Jump { negated: false, condition: JumpCondition::Negative } => 0x21,
            OpCode::Jump { negated: false, condition: JumpCondition::Zero } => 0x22,
            OpCode::Jump { negated: false, condition: JumpCondition::Positive } => 0x23,

            OpCode::Jump { negated: true,  condition: JumpCondition::Negative } => 0x24,
            OpCode::Jump { negated: true,  condition: JumpCondition::Zero } => 0x25,
            OpCode::Jump { negated: true,  condition: JumpCondition::Positive } => 0x26,

            OpCode::Jump { negated: false, condition: JumpCondition::Less } => 0x27,
            OpCode::Jump { negated: false, condition: JumpCondition::Equal } => 0x28,
            OpCode::Jump { negated: false, condition: JumpCondition::Greater } => 0x29,

            OpCode::Jump { negated: true,  condition: JumpCondition::Less } => 0x2A,
            OpCode::Jump { negated: true,  condition: JumpCondition::Equal } => 0x2B,
            OpCode::Jump { negated: true,  condition: JumpCondition::Greater } => 0x2C,

            OpCode::Call => 0x31,
            OpCode::Exit => 0x32,
            OpCode::Push => 0x33,
            OpCode::Pop => 0x34,
            OpCode::PushRegisters => 0x35,
            OpCode::PopRegisters => 0x36,

            OpCode::SupervisorCall => 0x70,
        }
    }

    pub fn from_byte(byte: u8) -> OpCode {
        match byte {
            0x00 => OpCode::NoOperation,

            0x01 => OpCode::Store,
            0x02 => OpCode::Load,
            0x03 => OpCode::In,
            0x04 => OpCode::Out,

            0x11 => OpCode::Add,
            0x12 => OpCode::Subtract,
            0x13 => OpCode::Multiply,
            0x14 => OpCode::Divide,
            0x15 => OpCode::Modulo,

            0x16 => OpCode::And,
            0x17 => OpCode::Or,
            0x18 => OpCode::Xor,
            0x19 => OpCode::ShiftLeft,
            0x1A => OpCode::ShiftRight,
            0x1B => OpCode::Not,
            0x1C => OpCode::ArithmeticShiftRight,

            0x1F => OpCode::Compare,

            0x20 => OpCode::Jump { negated: false, condition: JumpCondition::Unconditional },

            0x21 => OpCode::Jump { negated: false, condition: JumpCondition::Negative },
            0x22 => OpCode::Jump { negated: false, condition: JumpCondition::Zero },
            0x23 => OpCode::Jump { negated: false, condition: JumpCondition::Positive },

            0x24 => OpCode::Jump { negated: true,  condition: JumpCondition::Negative },
            0x25 => OpCode::Jump { negated: true,  condition: JumpCondition::Zero },
            0x26 => OpCode::Jump { negated: true,  condition: JumpCondition::Positive },

            0x27 => OpCode::Jump { negated: false, condition: JumpCondition::Less },
            0x28 => OpCode::Jump { negated: false, condition: JumpCondition::Equal },
            0x29 => OpCode::Jump { negated: false, condition: JumpCondition::Greater },

            0x2A => OpCode::Jump { negated: true,  condition: JumpCondition::Less },
            0x2B => OpCode::Jump { negated: true,  condition: JumpCondition::Equal },
            0x2C => OpCode::Jump { negated: true,  condition: JumpCondition::Greater },

            0x31 => OpCode::Call,
            0x32 => OpCode::Exit,
            0x33 => OpCode::Push,
            0x34 => OpCode::Pop,
            0x35 => OpCode::PushRegisters,
            0x36 => OpCode::PopRegisters,

            0x70 => OpCode::SupervisorCall,

            _ => panic!("invalid opcode {}", byte),
        }
    }
}

impl fmt::Display for OpCode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let OpCode::Jump { negated, condition } = self {
            if JumpCondition::Unconditional == *condition {
                write!(f, "JUMP")
            } else {
                let end = match condition {
                    JumpCondition::Equal => "EQU",
                    JumpCondition::Less => "LES",
                    JumpCondition::Greater => "GRE",
                    JumpCondition::Positive => "POS",
                    JumpCondition::Negative => "NEG",
                    JumpCondition::Zero => "ZER",
                    JumpCondition::Unconditional => unreachable!(),
                };

                match negated {
                    true => write!(f, "JN{}", end),
                    false => write!(f, "J{}", end)
                }
            }
        } else {
            write!(f, "{}", match self {
                OpCode::NoOperation => "NOP",

                OpCode::Store => "STORE",
                OpCode::Load => "LOAD",
                OpCode::In => "IN",
                OpCode::Out => "OUT",

                OpCode::Add => "ADD",
                OpCode::Subtract => "SUB",
                OpCode::Multiply => "MUL",
                OpCode::Divide => "DIV",
                OpCode::Modulo => "MOD",

                OpCode::And => "AND",
                OpCode::Or => "OR",
                OpCode::Xor => "XOR",
                OpCode::ShiftLeft => "SHL",
                OpCode::ShiftRight => "SHR",
                OpCode::Not => "NOT",
                OpCode::ArithmeticShiftRight => "ASHL",

                OpCode::Compare => "COMP",

                OpCode::Call => "CALL",
                OpCode::Exit => "EXIT",
                OpCode::Push => "PUSH",
                OpCode::Pop => "POP",
                OpCode::PushRegisters => "PUSHR",
                OpCode::PopRegisters => "POPR",

                OpCode::SupervisorCall => "SVC",

                OpCode::Jump { .. } => unreachable!(),
            })
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Mode {
    Direct,
    Indirect,
    Immediate,
}

impl Mode {
    pub fn from_byte(byte: u8) -> Mode {
        match byte {
            0 => Mode::Immediate,
            1 => Mode::Direct,
            2 => Mode::Indirect,
            _ => panic!("invalid instruction mode {}", byte),
        }
    }

    pub fn as_byte(&self) -> u8 {
        match self {
            Mode::Immediate => 0,
            Mode::Direct => 1,
            Mode::Indirect => 2,
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Register {
    R0,
    R1,
    R2,
    R3,
    R4,
    R5,
    R6,
    R7,
}

impl Register {
    pub fn from_byte(byte: u8) -> Register {
        match byte {
            0 => Register::R0,
            1 => Register::R1,
            2 => Register::R2,
            3 => Register::R3,
            4 => Register::R4,
            5 => Register::R5,
            6 => Register::R6,
            7 => Register::R7,
            _ => panic!("invalid register {}", byte),
        }
    }

    pub fn index(&self) -> usize {
        match self {
            Register::R0 => 0,
            Register::R1 => 1,
            Register::R2 => 2,
            Register::R3 => 3,
            Register::R4 => 4,
            Register::R5 => 5,
            Register::R6 => 6,
            Register::R7 => 7,
        }
    }
}

impl fmt::Display for Register {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Register::R0 => write!(f, "R0"),
            Register::R1 => write!(f, "R1"),
            Register::R2 => write!(f, "R2"),
            Register::R3 => write!(f, "R3"),
            Register::R4 => write!(f, "R4"),
            Register::R5 => write!(f, "R5"),
            Register::R6 => write!(f, "R6"),
            Register::R7 => write!(f, "R7"),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Instruction {
    pub opcode: OpCode,
    pub mode: Mode,
    pub index_register: Register,
    pub register: Register,
    pub immediate: u16,
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Mode::*;

        write!(f, "{} {}, {}",
            self.opcode,
            self.register,
            match (self.mode, self.immediate, self.index_register) {
                (Immediate, imm, _reg) => format!("=0x{:04x}", imm),
                (Direct, 0, reg) => reg.to_string(),
                (Direct, imm, reg) => format!("0x{:04x}({})", imm, reg),
                (Indirect, 0, reg) => format!("@{}", reg),
                (Indirect, imm, reg) => format!("@0x{:04x}({})", imm, reg),
            })
    }
}

impl Into<u32> for Instruction {
    fn into(self) -> u32 {
        let mut res = self.opcode.as_byte();
        let [imm1, imm2] = self.immediate.to_be_bytes();


        let reg_byte: u8 = self.register.index() as u8;
        let mode_byte: u8 = self.mode.as_byte();
        let i_reg_byte: u8 = self.index_register.index() as u8;

        let registers = i_reg_byte | (mode_byte << 3) | (reg_byte << 5);

        //let mode = (flags & 0b0001_1000) >> 3;
        //let reg  = (flags & 0b1110_0000) >> 5;
        //let ireg = (flags & 0b0000_0111) >> 0;

        u32::from_be_bytes([
            self.opcode.as_byte(),
            registers,
            imm1,
            imm2,
        ])
    }
}

use std::convert::TryFrom;

impl TryFrom<u32> for Instruction {
    type Error = ();

    fn try_from(line: u32) -> Result<Instruction, Self::Error> {
        Instruction::try_from(&line.to_be_bytes())
    }
}

impl TryFrom<&[u8; 4]> for Instruction {
    type Error = ();

    fn try_from(bytes: &[u8; 4]) -> Result<Instruction, Self::Error> {
        let opcode = bytes[0];

        let flags = bytes[1];

        let mode = (flags & 0b0001_1000) >> 3;
        let reg  = (flags & 0b1110_0000) >> 5;
        let ireg = (flags & 0b0000_0111) >> 0;

        let immediate = u16::from_be_bytes([bytes[2], bytes[3]]);

        Ok(Instruction {
            opcode: OpCode::from_byte(opcode),
            mode: Mode::from_byte(mode),
            index_register: Register::from_byte(ireg),
            register: Register::from_byte(reg),
            immediate,
        })
    }
}
