use std::fmt;
use std::hash::{Hash, Hasher};

use super::GoExpression;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GoPackage {
    Prim,
    Array,
    Direct,
    Object,
    Nullable,
    Exception,
    Aff,
    EventLoop,
    Promise,
    ForeignValue,
    Tauri,
    Regex,
    Lazy,
    Alloc,
    Argonaut,
    AVar,
    YogaOm,
    BigInts,
    DateTime,
    Now,
    Spec,
    RefEq,
    Console,
    JsBigInt,
    Int64,
    HashMap,
    Random,
    Cmp,
    Maps,
    Math,
    MathBig,
    MathBits,
    Os,
    Slices,
    Strconv,
    Strings,
    Sync,
}

impl GoPackage {
    pub fn path(self) -> &'static str {
        match self {
            GoPackage::Prim => "github.com/i-am-the-slime/iris-go/prim",
            GoPackage::Array => "github.com/i-am-the-slime/iris-go/array",
            GoPackage::Direct => "github.com/i-am-the-slime/iris-go/direct",
            GoPackage::Object => "github.com/i-am-the-slime/iris-go/object",
            GoPackage::Nullable => "github.com/i-am-the-slime/iris-go/nullable",
            GoPackage::Aff => "github.com/i-am-the-slime/iris-go/aff",
            GoPackage::EventLoop => "github.com/i-am-the-slime/iris-go/eventloop",
            GoPackage::Promise => "github.com/i-am-the-slime/iris-go/promise",
            GoPackage::ForeignValue => "github.com/i-am-the-slime/iris-go/foreignvalue",
            GoPackage::Tauri => "github.com/i-am-the-slime/iris-go/tauri",
            GoPackage::Regex => "github.com/i-am-the-slime/iris-go/regex",
            GoPackage::Lazy => "github.com/i-am-the-slime/iris-go/lazy",
            GoPackage::Alloc => "github.com/i-am-the-slime/iris-go/alloc",
            GoPackage::Argonaut => "github.com/i-am-the-slime/iris-go/argonaut",
            GoPackage::AVar => "github.com/i-am-the-slime/iris-go/avar",
            GoPackage::YogaOm => "github.com/i-am-the-slime/iris-go/yogaom",
            GoPackage::BigInts => "github.com/i-am-the-slime/iris-go/bigints",
            GoPackage::DateTime => "github.com/i-am-the-slime/iris-go/datetime",
            GoPackage::Now => "github.com/i-am-the-slime/iris-go/now",
            GoPackage::Spec => "github.com/i-am-the-slime/iris-go/spec",
            GoPackage::RefEq => "github.com/i-am-the-slime/iris-go/refeq",
            GoPackage::Console => "github.com/i-am-the-slime/iris-go/console",
            GoPackage::JsBigInt => "github.com/i-am-the-slime/iris-go/jsbigint",
            GoPackage::Int64 => "github.com/i-am-the-slime/iris-go/ffi/Data_Int64_Internal_ffi",
            GoPackage::HashMap => "github.com/i-am-the-slime/iris-go/ffi/Data_HashMap_ffi",
            GoPackage::Random => "github.com/i-am-the-slime/iris-go/random",
            GoPackage::Exception => "github.com/i-am-the-slime/iris-go/exception",
            GoPackage::Cmp => "cmp",
            GoPackage::Maps => "maps",
            GoPackage::Math => "math",
            GoPackage::MathBig => "math/big",
            GoPackage::MathBits => "math/bits",
            GoPackage::Os => "os",
            GoPackage::Slices => "slices",
            GoPackage::Strconv => "strconv",
            GoPackage::Strings => "strings",
            GoPackage::Sync => "sync",
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            GoPackage::Prim => "prim",
            GoPackage::Array => "array",
            GoPackage::Direct => "direct",
            GoPackage::Object => "object",
            GoPackage::Nullable => "nullable",
            GoPackage::Exception => "exception",
            GoPackage::Aff => "aff",
            GoPackage::EventLoop => "eventloop",
            GoPackage::Promise => "promise",
            GoPackage::ForeignValue => "foreignvalue",
            GoPackage::Tauri => "tauri",
            GoPackage::Regex => "regex",
            GoPackage::Lazy => "lazy",
            GoPackage::Alloc => "alloc",
            GoPackage::Argonaut => "argonaut",
            GoPackage::AVar => "avar",
            GoPackage::YogaOm => "yogaom",
            GoPackage::BigInts => "bigints",
            GoPackage::DateTime => "datetime",
            GoPackage::Now => "now",
            GoPackage::Spec => "spec",
            GoPackage::RefEq => "refeq",
            GoPackage::Console => "console",
            GoPackage::JsBigInt => "jsbigint",
            GoPackage::Int64 => "Data_Int64_Internal_ffi",
            GoPackage::HashMap => "Data_HashMap_ffi",
            GoPackage::Random => "random",
            GoPackage::Cmp => "cmp",
            GoPackage::Maps => "maps",
            GoPackage::Math => "math",
            GoPackage::MathBig => "big",
            GoPackage::MathBits => "bits",
            GoPackage::Os => "os",
            GoPackage::Slices => "slices",
            GoPackage::Strconv => "strconv",
            GoPackage::Strings => "strings",
            GoPackage::Sync => "sync",
        }
    }
}

#[derive(Debug, Clone, Eq)]
pub enum GoQualifier {
    Package(GoPackage),
    Named(String),
}

impl GoQualifier {
    pub fn name(&self) -> &str {
        match self {
            GoQualifier::Package(package) => package.name(),
            GoQualifier::Named(name) => name,
        }
    }

    pub fn is(&self, package: GoPackage) -> bool {
        self.name() == package.name()
    }
}

impl PartialEq for GoQualifier {
    fn eq(&self, other: &GoQualifier) -> bool {
        self.name() == other.name()
    }
}

impl Hash for GoQualifier {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name().hash(state);
    }
}

impl fmt::Display for GoQualifier {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.name())
    }
}

impl GoExpression {
    pub fn qualified(package: GoPackage, name: &str) -> GoExpression {
        GoExpression::Qualified { package: GoQualifier::Package(package), name: name.to_string() }
    }

    pub fn name_in(&self, package: GoPackage) -> Option<&str> {
        match self {
            GoExpression::Qualified { package: qualifier, name } if qualifier.is(package) => {
                Some(name)
            }
            _ => None,
        }
    }

    pub fn is_qualified(&self, package: GoPackage, name: &str) -> bool {
        self.name_in(package) == Some(name)
    }

    pub fn is_call_to(&self, package: GoPackage, name: &str) -> bool {
        matches!(self, GoExpression::Call { function, .. } if function.is_qualified(package, name))
    }
}
