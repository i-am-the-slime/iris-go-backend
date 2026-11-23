use super::{Boundary, Foreign, GoFunction, GoPackage, MaybeConstructors, PLAIN};

const fn hash_map(name: &'static str, arity: usize, boundary: Boundary) -> Foreign {
    let function = GoFunction { package: GoPackage::HashMap, name };
    Foreign::Call { function, arity, boundary }
}

const fn uncurrying(callbacks: &'static [(usize, usize)]) -> Boundary {
    Boundary { uncurried: callbacks, ..PLAIN }
}

const fn ignoring_uncurrying(
    ignored: &'static [usize],
    callbacks: &'static [(usize, usize)],
) -> Boundary {
    Boundary { ignored, uncurried: callbacks, ..PLAIN }
}

const INSTANTIATE: Boundary = Boundary { instantiate: true, ..PLAIN };

const LOOKUP_MAYBE: Option<MaybeConstructors> =
    Some(MaybeConstructors { just: 1, nothing: 0, witness: None, elements: false });

struct HashMapForeign {
    name: &'static str,
    keyed: Foreign,
    native: Foreign,
}

const fn both(name: &'static str, foreign: Foreign) -> HashMapForeign {
    HashMapForeign { name, keyed: foreign, native: foreign }
}

const HASH_MAP_FOREIGNS: &[HashMapForeign] = &[
    HashMapForeign {
        name: "empty",
        keyed: hash_map("Empty", 0, INSTANTIATE),
        native: hash_map("NativeEmpty", 0, INSTANTIATE),
    },
    HashMapForeign {
        name: "singletonPurs",
        keyed: hash_map("Singleton", 3, PLAIN),
        native: hash_map("NativeSingleton", 3, Boundary { ignored: &[1], ..PLAIN }),
    },
    HashMapForeign {
        name: "lookupPurs",
        keyed: hash_map("Lookup", 6, Boundary { maybe: LOOKUP_MAYBE, ..uncurrying(&[(2, 2)]) }),
        native: hash_map(
            "NativeLookup",
            6,
            Boundary { maybe: LOOKUP_MAYBE, ignored: &[2, 4], ..PLAIN },
        ),
    },
    HashMapForeign {
        name: "insertPurs",
        keyed: hash_map("Insert", 5, uncurrying(&[(0, 2)])),
        native: hash_map("NativeInsert", 5, Boundary { ignored: &[0, 1], ..PLAIN }),
    },
    HashMapForeign {
        name: "insertWithPurs",
        keyed: hash_map("InsertWith", 6, uncurrying(&[(0, 2), (2, 2)])),
        native: hash_map("NativeInsertWith", 6, ignoring_uncurrying(&[0, 1], &[(2, 2)])),
    },
    HashMapForeign {
        name: "deletePurs",
        keyed: hash_map("Delete", 4, uncurrying(&[(0, 2)])),
        native: hash_map("NativeDelete", 4, Boundary { ignored: &[0, 2], ..PLAIN }),
    },
    HashMapForeign {
        name: "fromArrayPurs",
        keyed: hash_map("FromArray", 5, uncurrying(&[(0, 2), (2, 1), (3, 1)])),
        native: hash_map("NativeFromArray", 5, ignoring_uncurrying(&[0, 1], &[(2, 1), (3, 1)])),
    },
    HashMapForeign {
        name: "toArrayBy",
        keyed: hash_map("ToArrayBy", 2, uncurrying(&[(0, 2)])),
        native: hash_map("NativeToArrayBy", 2, uncurrying(&[(0, 2)])),
    },
    HashMapForeign {
        name: "isEmpty",
        keyed: hash_map("IsEmpty", 1, PLAIN),
        native: hash_map("NativeIsEmpty", 1, PLAIN),
    },
    HashMapForeign {
        name: "size",
        keyed: hash_map("Size", 1, PLAIN),
        native: hash_map("NativeSize", 1, PLAIN),
    },
    HashMapForeign {
        name: "unionWithPurs",
        keyed: hash_map("UnionWith", 5, uncurrying(&[(0, 2), (2, 2)])),
        native: hash_map("NativeUnionWith", 5, ignoring_uncurrying(&[0, 1], &[(2, 2)])),
    },
    HashMapForeign {
        name: "intersectionWithPurs",
        keyed: hash_map("IntersectionWith", 7, ignoring_uncurrying(&[0, 1], &[(2, 2), (4, 2)])),
        native: hash_map(
            "NativeIntersectionWith",
            7,
            ignoring_uncurrying(&[0, 1, 2, 3], &[(4, 2)]),
        ),
    },
    HashMapForeign {
        name: "filterWithKey",
        keyed: hash_map("FilterWithKey", 2, uncurrying(&[(0, 2)])),
        native: hash_map("NativeFilterWithKey", 2, uncurrying(&[(0, 2)])),
    },
    HashMapForeign {
        name: "eqPurs",
        keyed: hash_map("Equal", 4, uncurrying(&[(0, 2), (1, 2)])),
        native: hash_map("NativeEqual", 4, ignoring_uncurrying(&[0], &[(1, 2)])),
    },
    HashMapForeign {
        name: "hashPurs",
        keyed: hash_map("Hash", 2, PLAIN),
        native: hash_map("NativeHash", 2, PLAIN),
    },
    HashMapForeign {
        name: "mapWithIndexPurs",
        keyed: hash_map("MapWithIndex", 2, uncurrying(&[(0, 2)])),
        native: hash_map("NativeMapWithIndex", 2, uncurrying(&[(0, 2)])),
    },
    HashMapForeign {
        name: "foldMapWithIndexPurs",
        keyed: hash_map("FoldMapWithIndex", 4, uncurrying(&[(1, 2), (2, 2)])),
        native: hash_map("NativeFoldMapWithIndex", 4, uncurrying(&[(1, 2), (2, 2)])),
    },
    HashMapForeign {
        name: "anyPurs",
        keyed: hash_map("Any", 2, PLAIN),
        native: hash_map("NativeAny", 2, PLAIN),
    },
    both("nubHashPurs", hash_map("NubHash", 5, ignoring_uncurrying(&[0, 1], &[(2, 2)]))),
];

const HASHABLE_FOREIGNS: &[HashMapForeign] = &[
    both("hashString", hash_map("HashString", 1, PLAIN)),
    both("hashNumber", hash_map("HashNumber", 1, PLAIN)),
];

pub fn hash_map_import(module_name: &str, name: &str, native: bool) -> Option<&'static Foreign> {
    let foreigns = match module_name {
        "Data.HashMap" => HASH_MAP_FOREIGNS,
        "Data.Hashable" => HASHABLE_FOREIGNS,
        _ => return None,
    };
    let foreign = foreigns.iter().find(|foreign| foreign.name == name)?;
    match native {
        true => Some(&foreign.native),
        false => Some(&foreign.keyed),
    }
}
