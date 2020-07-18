use std::fmt;
use std::collections::HashMap;

#[derive(Copy, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct VarId(u32);

#[derive(Debug)]
pub struct SymbolTable<'a> {
    var_count: u32,
    variables: HashMap<&'a str, VarId>,
}

impl <'a> SymbolTable<'a> {
    pub fn new() -> SymbolTable<'a> {
        SymbolTable {
            var_count: 0,
            variables: HashMap::new()
        }
    }
    pub fn make_var(&mut self) -> VarId {
        let var = VarId(self.var_count);
        self.var_count += 1;
        var
    }
    /// Return the VarId associated with `name`, if any
    pub fn var_id(&self, name: &'a str) -> Option<VarId> {
        self.variables.get(name).map(|var| *var)
    }
    /// Rebind `name` to a new VarId, returning it and the necessary information to restore the variable
    pub fn shadow_var(&mut self, name: &'a str) -> (VarId, ShadowInformation<'a>) {
        let var = self.make_var();
        let opt_prev = self.variables.insert(name, var);
        (var, ShadowInformation(name, opt_prev))
    }
    /// Restore the previous binding based on `shadow_info`
    pub fn restore_binding(&mut self, shadow_info: ShadowInformation<'a>) {
        match shadow_info {
            ShadowInformation(name, Some(var)) => {
                // there was something previous, we can restore it with the shadow information
                self.variables.insert(name, var);
            }
            ShadowInformation(name, None) => {
                // there was nothing previous, we want to remove whatever's there now
                self.variables.remove(name);
            }
        }
    }
}

/// Opaque wrapper struct for dealing with variable shadows and scoping while parsing
/// Stores the information necessary to restore a binding that has been shadowed
pub struct ShadowInformation<'a>(&'a str, Option<VarId>);

impl fmt::Debug for VarId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "${}", self.0)
    }
}
