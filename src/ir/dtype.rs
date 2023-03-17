use core::fmt;
use core::ops::Deref;

use itertools::*;
use lang_c::ast;
use lang_c::span::Node;
use thiserror::Error;

use super::Named;

#[derive(Debug, PartialEq, Eq, Error)]
pub enum DtypeError {
    #[error("{message}")]
    Misc { message: String },
}

pub trait HasDtype {
    fn dtype(&self) -> Dtype;
}

#[derive(Default)]
struct BaseDtype {
    scalar: Option<ast::TypeSpecifier>,
    signed_option: Option<ast::TypeSpecifier>,
}

impl BaseDtype {
    #[inline]
    fn apply_type_specifier(
        &mut self,
        type_specifier: &ast::TypeSpecifier,
    ) -> Result<(), DtypeError> {
        match type_specifier {
            ast::TypeSpecifier::Unsigned | ast::TypeSpecifier::Signed => {
                if self.signed_option.is_some() {
                    return Err(DtypeError::Misc {
                        message: "duplicate signed option".to_string(),
                    });
                }
                self.signed_option = Some(type_specifier.clone());
            }
            ast::TypeSpecifier::Void
            | ast::TypeSpecifier::Bool
            | ast::TypeSpecifier::Char
            | ast::TypeSpecifier::Int => {
                if self.scalar.is_some() {
                    return Err(DtypeError::Misc {
                        message: "two or more scalar types in declaration specifiers".to_string(),
                    });
                }
                self.scalar = Some(type_specifier.clone());
            }
            _ => todo!("apply_type_specifier: support {:?}", type_specifier),
        }
        Ok(())
    }

    pub fn apply_declaration_specifier(
        &mut self,
        declaration_specifier: &ast::DeclarationSpecifier,
    ) -> Result<(), DtypeError> {
        match declaration_specifier {
            ast::DeclarationSpecifier::TypeSpecifier(type_specifier) => {
                self.apply_type_specifier(&type_specifier.node)?
            }
            ds => {
                return Err(DtypeError::Misc {
                    message: format!("unsupported declaration qualifier: {ds:#?}"),
                })
            }
        }

        Ok(())
    }

    pub fn apply_declaration_specifiers(
        &mut self,
        declaration_specifiers: &[Node<ast::DeclarationSpecifier>],
    ) -> Result<(), DtypeError> {
        for ast_spec in declaration_specifiers {
            self.apply_declaration_specifier(&ast_spec.node)?;
        }

        Ok(())
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Dtype {
    Unit,
    Int { width: usize, is_signed: bool },
    Function { ret: Box<Dtype>, params: Vec<Dtype> },
    // Array {
    //     inner: Box<Dtype>,
    //     size: usize,
    // },
}

impl TryFrom<BaseDtype> for Dtype {
    type Error = DtypeError;

    fn try_from(spec: BaseDtype) -> Result<Self, Self::Error> {
        let mut dtype = if let Some(t) = spec.scalar {
            match t {
                ast::TypeSpecifier::Void => Self::unit(),
                ast::TypeSpecifier::Bool => Self::BOOL,
                ast::TypeSpecifier::Char => Self::CHAR,
                ast::TypeSpecifier::Int => Self::INT,
                _ => panic!("Dtype::try_from::<BaseDtype>: {t:?} is not a scalar type"),
            }
        } else {
            Self::default()
        };
        if let Some(signed_option) = spec.signed_option {
            let is_signed = match signed_option {
                ast::TypeSpecifier::Signed => true,
                ast::TypeSpecifier::Unsigned => false,
                _ => {
                    panic!("Dtype::try_from::<BaseDtype>: {signed_option:?} is not a signed option")
                }
            };

            dtype = dtype.set_signed(is_signed);
        }
        Ok(dtype)
    }
}

impl Dtype {
    pub const BITS_OF_BYTE: usize = 1;
    pub const SIZE_OF_CHAR: usize = 1;
    pub const SIZE_OF_INT: usize = 4;
    pub const BOOL: Self = Self::Int {
        width: 1,
        is_signed: false,
    };

    pub const CHAR: Self = Self::int(Self::SIZE_OF_CHAR * Self::BITS_OF_BYTE);
    pub const INT: Self = Self::int(Self::SIZE_OF_INT * Self::BITS_OF_BYTE);

    #[inline]
    pub const fn unit() -> Self {
        Self::Unit
    }

    #[inline]
    pub const fn int(width: usize) -> Self {
        Self::Int {
            width,
            is_signed: true,
        }
    }

    #[inline]
    pub fn function(ret: Dtype, params: Vec<Dtype>) -> Self {
        Self::Function {
            ret: Box::new(ret),
            params,
        }
    }

    #[must_use]
    pub fn set_signed(&self, is_signed: bool) -> Self {
        match self {
            Self::Int { width, .. } => Self::Int {
                width: *width,
                is_signed,
            },
            _ => panic!("`signed` and `unsigned` only be applied to `Dtype::Int`"),
        }
    }

    #[inline]
    pub fn get_function_inner(&self) -> Option<(&Self, &Vec<Self>)> {
        if let Self::Function { ret, params } = self {
            Some((ret.deref(), params))
        } else {
            None
        }
    }

    /// Derive a data type from declaration specifiers.
    pub fn try_from_ast_declaration_specifiers(
        specifiers: &[Node<ast::DeclarationSpecifier>],
    ) -> Result<Self, DtypeError> {
        let mut spec = BaseDtype::default();
        BaseDtype::apply_declaration_specifiers(&mut spec, specifiers)?;
        let dtype = Self::try_from(spec)?;

        Ok(dtype)
    }

    pub fn with_ast_declarator(
        mut self,
        declarator: &ast::Declarator,
    ) -> Result<Named<Self>, DtypeError> {
        for derived_decl in &declarator.derived {
            self = match &derived_decl.node {
                ast::DerivedDeclarator::Function(func_decl) => {
                    let mut params = func_decl
                        .node
                        .parameters
                        .iter()
                        .map(|p| Self::try_from(&p.node))
                        .collect::<Result<Vec<_>, _>>()?;

                    // if there is no function parameter
                    if params.len() == 1 && params[0] == Dtype::unit() {
                        let _ = params.pop();
                    }

                    Self::function(self, params)
                }
                _ => panic!("Unsupported declarator"),
            };
        }
        let declarator_kind = &declarator.kind;
        match &declarator_kind.node {
            ast::DeclaratorKind::Abstract => Ok(Named::new(None, self)),
            ast::DeclaratorKind::Identifier(id) => Ok(Named::new(Some(id.node.name.clone()), self)),
            ast::DeclaratorKind::Declarator(decl) => self.with_ast_declarator(&decl.node),
        }
    }
}

impl fmt::Display for Dtype {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unit => write!(f, "unit"),
            Self::Int { width, is_signed } => {
                write!(f, "{}{}", if *is_signed { "i" } else { "u" }, width)
            }
            Self::Function { ret, params } => {
                write!(f, "[ret:{} params:({})]", ret, params.iter().format(", "))
            }
        }
    }
}

impl TryFrom<&ast::ParameterDeclaration> for Dtype {
    type Error = DtypeError;

    /// Generate `Dtype` based on parameter declaration.
    fn try_from(parameter_decl: &ast::ParameterDeclaration) -> Result<Self, Self::Error> {
        let mut spec = BaseDtype::default();
        BaseDtype::apply_declaration_specifiers(&mut spec, &parameter_decl.specifiers)?;
        let mut dtype = Self::try_from(spec)?;

        if let Some(declarator) = &parameter_decl.declarator {
            dtype = dtype.with_ast_declarator(&declarator.node)?.into_inner();
        }
        Ok(dtype)
    }
}

impl Default for Dtype {
    fn default() -> Self {
        // default dtype is `int`(i32)
        Self::INT
    }
}
