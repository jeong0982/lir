use lang_c::ast::*;
use lang_c::span::Node;

use core::ops::Deref;
use std::io::{Result, Write};

use crate::write_base::*;

impl<T: WriteLine> WriteLine for Node<T> {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        self.node.write_line(indent, write)
    }
}

impl<T: WriteString> WriteString for Node<T> {
    fn write_string(&self) -> String {
        self.node.write_string()
    }
}

impl<T: WriteString> WriteString for Box<T> {
    fn write_string(&self) -> String {
        self.deref().write_string()
    }
}

impl<T: WriteString> WriteString for &T {
    fn write_string(&self) -> String {
        (*self).write_string()
    }
}

impl<T: WriteString> WriteString for Option<T> {
    fn write_string(&self) -> String {
        if let Some(this) = self {
            this.write_string()
        } else {
            "".to_string()
        }
    }
}

impl WriteLine for TranslationUnit {
    fn write_line(&self, _indent: usize, _write: &mut dyn Write) -> Result<()> {
        for ext_decl in &self.0 {
            ext_decl.write_line(_indent, _write)?;
            writeln!(_write)?;
        }
        Ok(())
    }
}

impl WriteLine for ExternalDeclaration {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        match self {
            Self::Declaration(decl) => decl.write_line(indent, write),
            Self::StaticAssert(_) => Ok(()),
            Self::FunctionDefinition(fdef) => fdef.write_line(indent, write),
        }
    }
}

impl WriteLine for Declaration {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        write_indent(indent, write)?;
        writeln!(write, "{};", self.write_string())?;
        Ok(())
    }
}

impl WriteString for Initializer {
    fn write_string(&self) -> String {
        match self {
            Self::Expression(expr) => format!("= {}", expr.write_string()),
            Self::List(lst) => format!("= {{{}}}", lst.write_string()),
        }
    }
}

impl WriteString for InitDeclarator {
    fn write_string(&self) -> String {
        format!(
            "{} {}",
            self.declarator.write_string(),
            self.initializer.write_string()
        )
    }
}

impl WriteString for Declaration {
    fn write_string(&self) -> String {
        (&self.specifiers, &self.declarators).write_string()
    }
}
impl WriteString for Identifier {
    fn write_string(&self) -> String {
        (&self.name).to_string()
    }
}

impl WriteString for DeclaratorKind {
    fn write_string(&self) -> String {
        match self {
            Self::Abstract => String::from(""),
            Self::Declarator(decl) => decl.write_string(),
            Self::Identifier(id) => id.write_string(),
        }
    }
}

impl WriteString for TypeQualifier {
    fn write_string(&self) -> String {
        match self {
            Self::Const => "const".to_string(),
            _ => "".to_string(),
        }
    }
}

impl WriteString for PointerQualifier {
    fn write_string(&self) -> String {
        match self {
            Self::TypeQualifier(t) => t.write_string(),
            Self::Extension(_) => "".to_string(),
        }
    }
}

impl WriteString for ArraySize {
    fn write_string(&self) -> String {
        match &self {
            Self::Unknown => "".to_string(),
            Self::VariableUnknown => "*".to_string(),
            Self::StaticExpression(e) => format!("static {}", e.write_string()),
            Self::VariableExpression(v) => v.write_string(),
        }
    }
}

impl WriteString for ArrayDeclarator {
    fn write_string(&self) -> String {
        format!(
            "{}[{}]",
            (&self.qualifiers).write_string(),
            self.size.write_string()
        )
    }
}

// foo (^int n^)
impl WriteString for ParameterDeclaration {
    fn write_string(&self) -> String {
        format!(
            "{} {}",
            self.specifiers
                .iter()
                .map(WriteString::write_string)
                .collect::<Vec<_>>()
                .join(" "),
            self.declarator.as_ref().map(|d| &d.node).write_string()
        )
    }
}

impl WriteString for FunctionDeclarator {
    fn write_string(&self) -> String {
        format!(
            "({})",
            self.parameters
                .iter()
                .map(WriteString::write_string)
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

impl WriteString for (&Box<Node<Expression>>, &Vec<Node<Expression>>) {
    fn write_string(&self) -> String {
        format!(
            "{}({})",
            self.0.write_string(),
            self.1
                .iter()
                .map(WriteString::write_string)
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

impl WriteString for &Vec<Node<InitializerListItem>> {
    fn write_string(&self) -> String {
        self.iter()
            .map(WriteString::write_string)
            .collect::<Vec<_>>()
            .join(", ")
    }
}

impl WriteString for InitializerListItem {
    fn write_string(&self) -> String {
        match &self.initializer.node {
            Initializer::Expression(exp) => exp.write_string(),
            Initializer::List(list) => format!("{{{}}}", list.write_string()),
        }
    }
}

impl WriteString for &Vec<Node<TypeQualifier>> {
    fn write_string(&self) -> String {
        self.iter()
            .map(WriteString::write_string)
            .collect::<Vec<_>>()
            .join(" ")
    }
}

impl WriteString for &Vec<Node<Identifier>> {
    fn write_string(&self) -> String {
        self.iter()
            .map(WriteString::write_string)
            .collect::<Vec<_>>()
            .join(" ")
    }
}

impl WriteString for &Vec<Node<PointerQualifier>> {
    fn write_string(&self) -> String {
        self.iter()
            .map(WriteString::write_string)
            .collect::<Vec<_>>()
            .join("")
    }
}

impl WriteString for &Vec<Node<DeclarationSpecifier>> {
    fn write_string(&self) -> String {
        self.iter()
            .map(WriteString::write_string)
            .collect::<Vec<_>>()
            .join(" ")
    }
}

impl WriteString for &Vec<Node<InitDeclarator>> {
    fn write_string(&self) -> String {
        self.iter()
            .map(WriteString::write_string)
            .collect::<Vec<_>>()
            .join(", ")
    }
}

impl WriteString for &Vec<Node<SpecifierQualifier>> {
    fn write_string(&self) -> String {
        self.iter()
            .map(WriteString::write_string)
            .collect::<Vec<_>>()
            .join(" ")
    }
}

impl WriteString for (&Vec<Node<DeclarationSpecifier>>, &Vec<Node<InitDeclarator>>) {
    fn write_string(&self) -> String {
        format!("{} {}", self.0.write_string(), self.1.write_string())
    }
}

impl WriteString for (&Node<Identifier>, &Vec<Node<DerivedDeclarator>>) {
    fn write_string(&self) -> String {
        let mut s = self.0.write_string();
        for d in self.1 {
            s = match &d.node {
                DerivedDeclarator::Pointer(po) => format!("{}*{}", po.write_string(), s),
                DerivedDeclarator::Array(ar) => format!("{}{}", s, ar.write_string()),
                DerivedDeclarator::Function(fnc) => format!("{}{}", s, fnc.write_string()),
                DerivedDeclarator::KRFunction(kr) => format!("{}({})", s, kr.write_string()),
                DerivedDeclarator::Block(po) => format!("{}^{}", po.write_string(), s)
            }
        }
        s
    }
}

/// <Declarator>
impl WriteString for Declarator {
    fn write_string(&self) -> String {
        match &self.kind.node {
            DeclaratorKind::Abstract => {
                let mut s = "".to_string();
                for d in &self.derived {
                    s = match &d.node {
                        DerivedDeclarator::Pointer(po) => format!("{}*{}", &po.write_string(), s),
                        DerivedDeclarator::Array(ar) => format!("{}{}", s, ar.write_string()),
                        DerivedDeclarator::Function(fnc) => format!("{}{}", s, fnc.write_string()),
                        DerivedDeclarator::KRFunction(kr) => {
                            format!("{}({})", s, &kr.write_string())
                        },
                        DerivedDeclarator::Block(po) => format!("{}^{}", po.write_string(), s)
                    }
                }
                s
            }
            DeclaratorKind::Identifier(id) => (id, &self.derived).write_string(),
            DeclaratorKind::Declarator(decl) => {
                let mut s = format!("({})", decl.write_string());
                for d in &self.derived {
                    s = match &d.node {
                        DerivedDeclarator::Pointer(po) => format!("{}*{}", &po.write_string(), s),
                        DerivedDeclarator::Array(ar) => format!("{}{}", s, ar.write_string()),
                        DerivedDeclarator::Function(fnc) => format!("{}{}", s, fnc.write_string()),
                        DerivedDeclarator::KRFunction(kr) => {
                            format!("{}({})", s, &kr.write_string())
                        },
                        DerivedDeclarator::Block(po) => format!("{}^{}", po.write_string(), s)
                    }
                }
                s
            }
        }
    }
}

/// <StorageClassSpecifier>
impl WriteString for StorageClassSpecifier {
    fn write_string(&self) -> String {
        match &self {
            Self::Typedef => "typedef".to_string(),
            Self::Extern => "extern".to_string(),
            Self::Static => "static".to_string(),
            Self::ThreadLocal => "_Thread_local".to_string(),
            Self::Auto => "auto".to_string(),
            Self::Register => "register".to_string(),
        }
    }
}

impl WriteString for StructKind {
    fn write_string(&self) -> String {
        match self {
            Self::Struct => "struct".to_string(),
            Self::Union => "union".to_string(),
        }
    }
}

impl WriteString for StructField {
    fn write_string(&self) -> String {
        format!(
            "{} {};",
            (&self.specifiers)
                .iter()
                .map(WriteString::write_string)
                .collect::<Vec<_>>()
                .join(" "),
            (&self.declarators)
                .iter()
                .map(WriteString::write_string)
                .collect::<Vec<_>>()
                .join(" "),
        )
    }
}

impl WriteString for StructDeclarator {
    fn write_string(&self) -> String {
        self.declarator.write_string()
    }
}

impl WriteString for StructDeclaration {
    fn write_string(&self) -> String {
        match self {
            Self::Field(f) => f.write_string(),
            Self::StaticAssert(_) => "".to_string(),
        }
    }
}

impl WriteString for StructType {
    fn write_string(&self) -> String {
        match &self.declarations {
            Some(d) => format!(
                "{} {} {{ {} }}",
                self.kind.write_string(),
                self.identifier.write_string(),
                (&d).iter()
                    .map(WriteString::write_string)
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            None => format!(
                "{} {}",
                self.kind.write_string(),
                self.identifier.write_string()
            ),
        }
    }
}

impl WriteString for TypeSpecifier {
    fn write_string(&self) -> String {
        match self {
            Self::Void => String::from("void"),
            Self::Int => String::from("int"),
            Self::Char => String::from("char"),
            Self::Bool => String::from("bool"),
            Self::Short => String::from("short"),
            Self::Long => String::from("long"),
            Self::Float => String::from("float"),
            Self::Double => String::from("double"),
            Self::Signed => String::from("__signed"),
            Self::Unsigned => String::from("unsigned"),
            Self::TypedefName(td) => td.write_string(),
            Self::Struct(s) => s.write_string(),
            _ => panic!("unsupported"),
        }
    }
}

impl WriteString for DeclarationSpecifier {
    fn write_string(&self) -> String {
        match self {
            Self::StorageClass(s) => s.write_string(),
            Self::TypeSpecifier(t) => t.write_string(),
            Self::TypeQualifier(t) => t.write_string(),
            _ => "".to_string(),
        }
    }
}

impl WriteString for (&Vec<Node<DeclarationSpecifier>>, &Declarator) {
    fn write_string(&self) -> String {
        format!(
            "{} {}",
            self.0
                .iter()
                .map(WriteString::write_string)
                .collect::<Vec<_>>()
                .join(" "),
            self.1.write_string()
        )
    }
}

/// <FunctionDefiniton>
impl WriteLine for FunctionDefinition {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        write_indent(indent, write)?;
        writeln!(
            write,
            "{}",
            (&self.specifiers, &self.declarator.node).write_string()
        )?;
        self.statement.write_line(indent, write)?;
        Ok(())
    }
}

impl WriteString for Integer {
    fn write_string(&self) -> String {
        match self.base {
            IntegerBase::Decimal => format!(
                "{}{}",
                self.number.deref().to_string(),
                self.suffix.write_string()
            ),
            IntegerBase::Octal => format!(
                "0{}{}",
                self.number.deref().to_string(),
                self.suffix.write_string()
            ),
            IntegerBase::Hexadecimal => format!(
                "0x{}{}",
                self.number.deref().to_string(),
                self.suffix.write_string()
            ),
            _ => panic!("Unsupported(write binary integerbase)")
        }
    }
}

impl WriteString for IntegerSuffix {
    fn write_string(&self) -> String {
        if self.unsigned {
            format!("u{}", self.size.write_string())
        } else {
            self.size.write_string()
        }
    }
}

impl WriteString for IntegerSize {
    fn write_string(&self) -> String {
        match self {
            Self::Int => "".to_string(),
            Self::Long => "l".to_string(),
            Self::LongLong => "ll".to_string(),
        }
    }
}

impl WriteString for FloatSuffix {
    fn write_string(&self) -> String {
        self.format.write_string()
    }
}

impl WriteString for FloatFormat {
    fn write_string(&self) -> String {
        match self {
            Self::Float => "f".to_string(),
            Self::Double => "".to_string(),
            Self::LongDouble => "l".to_string(),
            Self::TS18661Format(_) => "".to_string(),
        }
    }
}

impl WriteString for Float {
    fn write_string(&self) -> String {
        match self.base {
            FloatBase::Decimal => format!(
                "{}{}",
                self.number.deref().to_string(),
                self.suffix.write_string()
            ),
            FloatBase::Hexadecimal => format!(
                "0x{}{}",
                self.number.deref().to_string(),
                self.suffix.write_string()
            ),
        }
    }
}

impl WriteString for Constant {
    fn write_string(&self) -> String {
        match self {
            Self::Integer(i) => i.write_string(),
            Self::Character(c) => c.into(),
            Self::Float(f) => f.write_string(),
        }
    }
}

impl WriteString for Label {
    fn write_string(&self) -> String {
        match self {
            Self::Identifier(id) => id.write_string(),
            Self::Case(e) => format!("case {}:", e.write_string()),
            Self::Default => "default:".to_string(),
            _ => panic!("Unsupported (write case range)")
        }
    }
}

impl WriteString for BinaryOperator {
    fn write_string(&self) -> String {
        match self {
            Self::Index => "".to_string(),
            Self::Multiply => "*".to_string(),
            Self::Divide => "/".to_string(),
            Self::Modulo => "%".to_string(),
            Self::Plus => "+".to_string(),
            Self::Minus => "-".to_string(),
            Self::ShiftLeft => "<<".to_string(),
            Self::ShiftRight => ">>".to_string(),
            Self::Less => "<".to_string(),
            Self::Greater => ">".to_string(),
            Self::LessOrEqual => "<=".to_string(),
            Self::GreaterOrEqual => ">=".to_string(),
            Self::Equals => "==".to_string(),
            Self::NotEquals => "!=".to_string(),
            Self::BitwiseAnd => "&".to_string(),
            Self::BitwiseXor => "^".to_string(),
            Self::BitwiseOr => "|".to_string(),
            Self::LogicalAnd => "&&".to_string(),
            Self::LogicalOr => "||".to_string(),
            Self::Assign => "=".to_string(),
            Self::AssignMultiply => "*=".to_string(),
            Self::AssignDivide => "/=".to_string(),
            Self::AssignModulo => "%=".to_string(),
            Self::AssignPlus => "+=".to_string(),
            Self::AssignMinus => "-=".to_string(),
            Self::AssignShiftLeft => "<<=".to_string(),
            Self::AssignShiftRight => ">>=".to_string(),
            Self::AssignBitwiseAnd => "&=".to_string(),
            Self::AssignBitwiseXor => "^=".to_string(),
            Self::AssignBitwiseOr => "|=".to_string(),
        }
    }
}

impl WriteString for BinaryOperatorExpression {
    fn write_string(&self) -> String {
        match &self.operator.node {
            BinaryOperator::Index => {
                format!("{}[{}]", self.lhs.write_string(), self.rhs.write_string())
            }
            _ => format!(
                "({} {} {})",
                self.lhs.write_string(),
                self.operator.write_string(),
                self.rhs.write_string()
            ),
        }
    }
}

impl WriteString for UnaryOperatorExpression {
    fn write_string(&self) -> String {
        match self.operator.node {
            UnaryOperator::PostIncrement => format!("{}++", self.operand.write_string()),
            UnaryOperator::PostDecrement => format!("{}--", self.operand.write_string()),
            UnaryOperator::PreIncrement => format!("++{}", self.operand.write_string()),
            UnaryOperator::PreDecrement => format!("--{}", self.operand.write_string()),
            UnaryOperator::Address => format!("&{}", self.operand.write_string()),
            UnaryOperator::Indirection => format!("*{}", self.operand.write_string()),
            UnaryOperator::Plus => format!("+{}", self.operand.write_string()),
            UnaryOperator::Minus => format!("-{}", self.operand.write_string()),
            UnaryOperator::Complement => format!("~{}", self.operand.write_string()),
            UnaryOperator::Negate => format!("!{}", self.operand.write_string()),
        }
    }
}

impl WriteString for CallExpression {
    fn write_string(&self) -> String {
        (&self.callee, &self.arguments).write_string()
    }
}

impl WriteString for MemberOperator {
    fn write_string(&self) -> String {
        match self {
            Self::Direct => ".".to_string(),
            Self::Indirect => "->".to_string(),
        }
    }
}

impl WriteString for MemberExpression {
    fn write_string(&self) -> String {
        format!(
            "{}{}{}",
            self.expression.write_string(),
            self.operator.write_string(),
            self.identifier.write_string()
        )
    }
}

impl WriteString for SpecifierQualifier {
    fn write_string(&self) -> String {
        match self {
            Self::TypeQualifier(tq) => tq.write_string(),
            Self::TypeSpecifier(ts) => ts.write_string(),
            _ => panic!("Unsupported (write extension)")
        }
    }
}

impl WriteString for TypeName {
    fn write_string(&self) -> String {
        match &self.declarator {
            Some(_) => format!(
                "{} {}",
                (&self.specifiers).write_string(),
                self.declarator.write_string()
            ),
            None => (&self.specifiers).write_string(),
        }
    }
}

impl WriteString for ConditionalExpression {
    fn write_string(&self) -> String {
        format!(
            "({} ? {} : {})",
            self.condition.write_string(),
            self.then_expression.write_string(),
            self.else_expression.write_string()
        )
    }
}

impl WriteString for CastExpression {
    fn write_string(&self) -> String {
        format!(
            "({}) {}",
            self.type_name.write_string(),
            self.expression.write_string()
        )
    }
}

impl WriteString for AlignOf {
    fn write_string(&self) -> String {
        self.0.write_string()
    }
}

impl WriteString for Expression {
    fn write_string(&self) -> String {
        match self {
            Self::Identifier(id) => id.write_string(),
            Self::Constant(c) => c.write_string(),
            Self::BinaryOperator(be) => be.write_string(),
            Self::Call(call) => call.write_string(),
            Self::Member(me) => me.write_string(),
            Self::AlignOf(tn) => format!("_Alignof({})", tn.write_string()),
            Self::UnaryOperator(ue) => format!("({})", ue.write_string()),
            Self::Conditional(ce) => ce.write_string(),
            Self::Cast(ce) => ce.write_string(),
            Self::Comma(c) => format!(
                "({})",
                c.deref()
                    .iter()
                    .map(WriteString::write_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            _ => String::from("TODO"),
        }
    }
}

impl WriteLine for BlockItem {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        match self {
            Self::Declaration(decl) => {
                write_indent(indent, write)?;
                writeln!(write, "{};", decl.write_string())?;
                Ok(())
            }
            Self::StaticAssert(_) => Ok(()),
            Self::Statement(stmt) => {
                stmt.write_line(indent, write)?;
                Ok(())
            }
        }
    }
}

impl WriteLine for IfStatement {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        write_indent(indent, write)?;
        writeln!(write, "if ({})", self.condition.write_string())?;
        self.then_statement.write_line(indent, write)?;
        match &self.else_statement {
            Some(s) => {
                write_indent(indent, write)?;
                writeln!(write, "else")?;
                s.write_line(indent, write)?;
            }
            None => (),
        }
        Ok(())
    }
}

impl WriteString for ForInitializer {
    fn write_string(&self) -> String {
        match self {
            Self::Empty => "".to_string(),
            Self::Expression(expr) => expr.write_string(),
            Self::Declaration(decl) => decl.write_string(),
            Self::StaticAssert(_) => "".to_string(),
        }
    }
}

impl WriteLine for ForStatement {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        write_indent(indent, write)?;
        writeln!(
            write,
            "for ({}; {}; {})",
            self.initializer.write_string(),
            self.condition.write_string(),
            self.step.write_string()
        )?;
        self.statement.write_line(indent, write)?;
        Ok(())
    }
}

impl WriteLine for SwitchStatement {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        write_indent(indent, write)?;
        writeln!(write, "switch ({})", self.expression.write_string())?;
        self.statement.write_line(indent, write)?;
        Ok(())
    }
}

impl WriteLine for WhileStatement {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        write_indent(indent, write)?;
        writeln!(write, "while ({})", self.expression.write_string())?;
        self.statement.write_line(indent, write)?;
        Ok(())
    }
}

impl WriteLine for DoWhileStatement {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        write_indent(indent, write)?;
        writeln!(write, "do")?;
        self.statement.write_line(indent, write)?;
        write_indent(indent, write)?;
        writeln!(write, "while ({});", self.expression.write_string())?;
        Ok(())
    }
}

impl WriteLine for Statement {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        match self {
            Self::Labeled(stmt) => {
                write_indent(indent, write)?;
                writeln!(write, "{}", stmt.node.label.write_string())?;
                stmt.node.statement.write_line(indent + 1, write)?;
                Ok(())
            }
            Self::Compound(items) => {
                write_indent(indent, write)?;
                writeln!(write, "{{")?;

                for item in items.iter() {
                    item.write_line(indent + 1, write)?;
                }

                write_indent(indent, write)?;
                writeln!(write, "}}")?;

                Ok(())
            }
            Self::Expression(expr) => {
                write_indent(indent, write)?;
                writeln!(write, "{};", expr.write_string())?;
                Ok(())
            }
            Self::Return(ret) => {
                write_indent(indent, write)?;
                writeln!(write, "return {};", ret.write_string())?;
                Ok(())
            }
            Self::If(ifstmt) => ifstmt.write_line(indent, write),
            Self::For(fstmt) => fstmt.write_line(indent, write),
            Self::Switch(s) => s.write_line(indent, write),
            Self::While(w) => w.write_line(indent, write),
            Self::DoWhile(dw) => dw.write_line(indent, write),
            Self::Break => {
                write_indent(indent, write)?;
                writeln!(write, "break;")?;
                Ok(())
            }
            Self::Continue => {
                write_indent(indent, write)?;
                writeln!(write, "continue;")?;
                Ok(())
            }
            _ => Ok(()),
        }
    }
}
