use crate::diag::Span;

pub type ExprId = u32;
pub type PatId = u32;

#[derive(Debug, Clone, PartialEq)]
pub struct Program {
    pub items: Vec<Item>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Item {
    Def(Def),
    /// `extern "C" def ...` with no body. Binds to C symbol `rush_<name>`.
    Extern(Def),
    Struct(StructDef),
    Enum(EnumDef),
    Trait(TraitDef),
    Impl(ImplDef),
}

#[derive(Debug, Clone, PartialEq)]
pub struct GenericParam {
    pub name: String,
    pub bounds: Vec<String>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct Generics {
    pub params: Vec<GenericParam>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SelfKind {
    Value,
    Ref,
    RefMut,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Def {
    pub name: String,
    pub generics: Generics,
    /// `Some` for methods. References are erased until Plan 3.
    pub self_param: Option<SelfKind>,
    /// Excludes `self`.
    pub params: Vec<Param>,
    pub ret: Option<TypeExpr>,
    /// Empty for extern defs and required trait methods.
    pub body: Block,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Param {
    pub name: String,
    pub ty: Option<TypeExpr>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct StructDef {
    pub name: String,
    pub generics: Generics,
    pub derives: Vec<String>,
    pub fields: Vec<FieldDef>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FieldDef {
    pub name: String,
    pub ty: TypeExpr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct EnumDef {
    pub name: String,
    pub generics: Generics,
    pub derives: Vec<String>,
    pub variants: Vec<VariantDef>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct VariantDef {
    pub name: String,
    pub fields: VariantFields,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum VariantFields {
    Unit,
    Tuple(Vec<TypeExpr>),
    Named(Vec<FieldDef>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct TraitDef {
    pub name: String,
    pub supertraits: Vec<String>,
    pub methods: Vec<Def>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ImplDef {
    pub generics: Generics,
    pub trait_name: Option<String>,
    pub self_ty: TypeExpr,
    pub methods: Vec<Def>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeExpr {
    /// `Int`, `List[T]`, `Self`, `T`
    Name(String, Vec<TypeExpr>, Span),
    /// `(A, B)`; `()` is Unit
    Tuple(Vec<TypeExpr>, Span),
    /// `A -> B`, right-associative
    Fn(Box<TypeExpr>, Box<TypeExpr>, Span),
    /// `&T` (false) or `&mut T` (true); erased until Plan 3
    Ref(bool, Box<TypeExpr>, Span),
}

impl TypeExpr {
    pub fn span(&self) -> Span {
        match self {
            TypeExpr::Name(_, _, s) | TypeExpr::Tuple(_, s) | TypeExpr::Fn(_, _, s) | TypeExpr::Ref(_, _, s) => *s,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    Let { pat: Pattern, mutable: bool, init: Expr, span: Span },
    Expr(Expr),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Pattern {
    pub id: PatId,
    pub kind: PatKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum PatKind {
    Wild,
    Bind(String),
    Lit(Lit),
    Tuple(Vec<Pattern>),
    /// `Circle(r)`, `None`
    Variant { name: String, fields: Vec<Pattern> },
    /// `Point { x: a, y: b }`, `Rect { w: a, h: b }`
    Struct { name: String, fields: Vec<(String, Pattern)> },
    Or(Vec<Pattern>),
    At(String, Box<Pattern>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Lit {
    Int(i64),
    Float(f64),
    Str(String),
    Bool(bool),
    Unit,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Arm {
    pub pat: Pattern,
    pub guard: Option<Expr>,
    pub body: Block,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Expr {
    pub id: ExprId,
    pub kind: ExprKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ExprKind {
    Int(i64),
    Float(f64),
    Str(String),
    Bool(bool),
    Unit,
    Var(String),
    Tuple(Vec<Expr>),
    StructLit { name: String, fields: Vec<(String, Expr)> },
    /// `p.x`, `p.m`, `p.m(a)`; `args` is `None` when no parentheses were written
    Dot { recv: Box<Expr>, name: String, args: Option<Vec<Expr>> },
    TupleIndex(Box<Expr>, usize),
    /// `&e` (false) or `&mut e` (true)
    Ref(bool, Box<Expr>),
    /// `*e`
    Deref(Box<Expr>),
    Unary(UnOp, Box<Expr>),
    Binary(BinOp, Box<Expr>, Box<Expr>),
    Call(Box<Expr>, Vec<Expr>),
    If { cond: Box<Expr>, then: Block, els: Option<Block> },
    While { cond: Box<Expr>, body: Block },
    Case { scrutinee: Box<Expr>, arms: Vec<Arm> },
    Interp(Vec<InterpPart>),
    Assign(Box<Expr>, Box<Expr>),
    Return(Option<Box<Expr>>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum InterpPart {
    Lit(String),
    Expr(Expr),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    Neg,
    Not,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add, Sub, Mul, Div, Rem,
    Eq, Ne, Lt, Le, Gt, Ge,
    And, Or,
}
