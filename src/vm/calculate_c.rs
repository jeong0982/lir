use crate::ir::*;
use crate::vm::vm_types::Value;
use crate::vm::*;
use lang_c::ast;
use std::cmp::Ordering;

pub fn calculate_integer_binary_operator_expression(
    op: &ast::BinaryOperator,
    lhs: u8,
    rhs: u8,
    width: usize,
    is_signed: bool,
) -> Result<Value, ()> {
    let result = match op {
        // TODO: explain why plus & minus do not need to consider `is_signed'
        ast::BinaryOperator::Plus => (lhs as i8 + rhs as i8) as u8,
        ast::BinaryOperator::Minus => (lhs as i8 - rhs as i8) as u8,
        ast::BinaryOperator::Multiply => {
            if is_signed {
                (lhs as i8 * rhs as i8) as u8
            } else {
                lhs * rhs
            }
        }
        ast::BinaryOperator::Divide => {
            assert!(rhs != 0);
            if is_signed {
                (lhs as i8 / rhs as i8) as u8
            } else {
                lhs / rhs
            }
        }
        ast::BinaryOperator::Modulo => {
            assert!(rhs != 0);
            if is_signed {
                (lhs as i8 % rhs as i8) as u8
            } else {
                lhs % rhs
            }
        }
        ast::BinaryOperator::ShiftLeft => {
            let rhs = if is_signed {
                let rhs = rhs as i8;
                assert!(rhs >= 0);
                assert!(rhs < (width as i8));
                rhs as u8
            } else {
                assert!(rhs < (width as u8));
                rhs
            };

            lhs << rhs
        }
        ast::BinaryOperator::ShiftRight => {
            if is_signed {
                // arithmetic shift right
                let rhs = rhs as i8;
                assert!(rhs >= 0);
                assert!(rhs < (width as i8));
                ((lhs as i8) >> rhs) as u8
            } else {
                // logical shift right
                assert!(rhs < (width as u8));
                let bit_mask = (1u8 << width as u8) - 1;
                let lhs = lhs & bit_mask;
                lhs >> rhs
            }
        }
        ast::BinaryOperator::BitwiseAnd => lhs & rhs,
        ast::BinaryOperator::BitwiseXor => lhs ^ rhs,
        ast::BinaryOperator::BitwiseOr => lhs | rhs,
        ast::BinaryOperator::Equals => {
            let result = (lhs == rhs).into();
            return Ok(Value::int(result, 1, false));
        }
        ast::BinaryOperator::NotEquals => {
            let result = (lhs != rhs).into();
            return Ok(Value::int(result, 1, false));
        }
        ast::BinaryOperator::Less => {
            let condition = if is_signed {
                (lhs as i8) < (rhs as i8)
            } else {
                lhs < rhs
            };
            let result = condition.into();
            return Ok(Value::int(result, 1, false));
        }
        ast::BinaryOperator::Greater => {
            let condition = if is_signed {
                (lhs as i8) > (rhs as i8)
            } else {
                lhs > rhs
            };
            let result = condition.into();
            return Ok(Value::int(result, 1, false));
        }
        ast::BinaryOperator::LessOrEqual => {
            let condition = if is_signed {
                (lhs as i8) <= (rhs as i8)
            } else {
                lhs <= rhs
            };
            let result = condition.into();
            return Ok(Value::int(result, 1, false));
        }
        ast::BinaryOperator::GreaterOrEqual => {
            let condition = if is_signed {
                (lhs as i8) >= (rhs as i8)
            } else {
                lhs >= rhs
            };
            let result = condition.into();
            return Ok(Value::int(result, 1, false));
        }
        _ => todo!(
            "calculate_binary_operator_expression: not supported operator {:?}",
            op
        ),
    };

    let result = if is_signed {
        sign_extension(result, width as u8)
    } else {
        trim_unnecessary_bits(result, width as u8)
    };

    Ok(Value::int(result, width, is_signed))
}

// TODO: change to template function in the future
pub fn calculate_binary_operator_expression(
    op: &ast::BinaryOperator,
    lhs: Value,
    rhs: Value,
) -> Result<Value, ()> {
    match (lhs, rhs) {
        (Value::Undef { dtype }, _) => Ok(Value::undef(dtype)),
        (_, Value::Undef { dtype }) => Ok(Value::undef(dtype)),
        (
            Value::Int {
                value: lhs,
                width: lhs_w,
                is_signed: lhs_s,
            },
            Value::Int {
                value: rhs,
                width: rhs_w,
                is_signed: rhs_s,
            },
        ) => {
            assert_eq!(lhs_w, rhs_w);
            assert_eq!(lhs_s, rhs_s);

            calculate_integer_binary_operator_expression(op, lhs, rhs, lhs_w, lhs_s)
        }
        (
            Value::Pointer { bid, offset, .. },
            Value::Pointer {
                bid: other_bid,
                offset: other_offset,
                ..
            },
        ) => match op {
            ast::BinaryOperator::Equals => {
                let result = (bid == other_bid && offset == other_offset).into();
                Ok(Value::int(result, 1, false))
            }
            ast::BinaryOperator::NotEquals => {
                let result = (!(bid == other_bid && offset == other_offset)).into();
                Ok(Value::int(result, 1, false))
            }
            _ => todo!(
                "calculate_binary_operator_expression: not supported case for \
                     {:?} between pointer and integer value",
                op,
            ),
        },
        (lhs, rhs) => todo!(
            "calculate_binary_operator_expression: not supported case for {:?} {:?} {:?}",
            op,
            lhs,
            rhs
        ),
    }
}

pub fn calculate_unary_operator_expression(
    op: &ast::UnaryOperator,
    operand: Value,
) -> Result<Value, ()> {
    match operand {
        Value::Undef { dtype } => Ok(Value::undef(dtype)),
        Value::Int {
            value,
            width,
            is_signed,
        } => {
            match op {
                ast::UnaryOperator::Plus => Ok(Value::int(value, width, is_signed)),
                ast::UnaryOperator::Minus => {
                    let result = if is_signed {
                        (-(value as i8)) as u8
                    } else {
                        let value = (-(value as i8)) as u8;
                        let width = width as u8;
                        trim_unnecessary_bits(value, width)
                    };
                    Ok(Value::int(result, width, is_signed))
                }
                ast::UnaryOperator::Negate => {
                    // Check if it is boolean
                    assert!(width == 1);
                    let result = (value == 0).into();
                    Ok(Value::int(result, width, is_signed))
                }
                _ => todo!(
                    "calculate_unary_operator_expression: not supported case for {:?} {:?}",
                    op,
                    operand,
                ),
            }
        }
        _ => todo!(
            "calculate_unary_operator_expression: not supported case for {:?} {:?}",
            op,
            operand,
        ),
    }
}
