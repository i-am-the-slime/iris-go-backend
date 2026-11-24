use super::Specializer;
use crate::error::GoResult;
use crate::foreign::{self, Foreign};
use crate::monotype::{Monotype, MonotypeId};

impl<'q, Q> Specializer<'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn hash_map_foreign(
        &mut self,
        module_name: &str,
        name: &str,
        monotype: MonotypeId,
    ) -> GoResult<Option<&'static Foreign>> {
        if foreign::hash_map_import(module_name, name, false).is_none() {
            return Ok(None);
        }
        let native = self.mentions_native_hash_map(monotype)?;
        Ok(foreign::hash_map_import(module_name, name, native))
    }

    fn mentions_native_hash_map(&mut self, monotype: MonotypeId) -> GoResult<bool> {
        let mut mentioned = vec![];
        let mut current = monotype;
        while let Some((parameter, result)) = self.monotypes.function_parts(current) {
            mentioned.push(parameter);
            current = result;
        }
        mentioned.push(current);
        for monotype in mentioned {
            let Monotype::ForeignData(data) = self.monotypes.get(monotype).clone() else {
                continue;
            };
            if let Some(native) = crate::monotype::native_hash_map(&mut self.context, &data)? {
                return Ok(native);
            }
        }
        Ok(false)
    }
}
