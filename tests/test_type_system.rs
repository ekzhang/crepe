// This test checks multiple output relations with complex joins.
// It demonstrates a simple type system with subtyping relationships.

use crepe::crepe;

#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq, PartialOrd, Ord)]
enum Type {
    Int,
    Float,
    String,
    Bool,
    Any,
}

crepe! {
    @input
    struct Subtype(Type, Type);

    @output
    struct IsSubtype(Type, Type);

    @output
    struct Compatible(Type, Type);

    @output
    struct NotRelated(Type, Type);

    struct AllTypes(Type);

    // Reflexive: every type is a subtype of itself
    IsSubtype(t, t) <- Subtype(t, _);
    IsSubtype(t, t) <- Subtype(_, t);

    // Direct subtype relationships
    IsSubtype(t1, t2) <- Subtype(t1, t2);

    // Transitive: if A <: B and B <: C, then A <: C
    IsSubtype(t1, t3) <- IsSubtype(t1, t2), IsSubtype(t2, t3);

    // Types are compatible if one is a subtype of the other
    Compatible(t1, t2) <- IsSubtype(t1, t2);
    Compatible(t1, t2) <- IsSubtype(t2, t1);

    // Collect all types
    AllTypes(t) <- Subtype(t, _);
    AllTypes(t) <- Subtype(_, t);

    // Types are not related if they're not compatible
    NotRelated(t1, t2) <- AllTypes(t1), AllTypes(t2), !Compatible(t1, t2);
}

#[test]
fn test_type_system() {
    let mut runtime = Crepe::new();
    runtime.extend([
        Subtype(Type::Int, Type::Float),
        Subtype(Type::Int, Type::Any),
        Subtype(Type::Float, Type::Any),
        Subtype(Type::String, Type::Any),
        Subtype(Type::Bool, Type::Any),
    ]);

    let (is_subtype, compatible, not_related) = runtime.run();
    
    let sub_vec: Vec<_> = is_subtype
        .into_iter()
        .map(|IsSubtype(t1, t2)| (t1, t2))
        .collect();
    
    // Check reflexivity
    assert!(sub_vec.contains(&(Type::Int, Type::Int)));
    assert!(sub_vec.contains(&(Type::Float, Type::Float)));
    
    // Check direct relationships
    assert!(sub_vec.contains(&(Type::Int, Type::Float)));
    assert!(sub_vec.contains(&(Type::Int, Type::Any)));
    
    // Check transitivity: Int <: Float <: Any implies Int <: Any (already added directly)
    assert!(sub_vec.contains(&(Type::Int, Type::Any)));
    
    let comp_vec: Vec<_> = compatible
        .into_iter()
        .map(|Compatible(t1, t2)| (t1, t2))
        .collect();
    
    // Int and Float are compatible
    assert!(comp_vec.contains(&(Type::Int, Type::Float)) || 
            comp_vec.contains(&(Type::Float, Type::Int)));
    
    // Everything is compatible with Any
    assert!(comp_vec.contains(&(Type::String, Type::Any)) || 
            comp_vec.contains(&(Type::Any, Type::String)));
    
    let not_rel_vec: Vec<_> = not_related
        .into_iter()
        .map(|NotRelated(t1, t2)| (t1, t2))
        .collect();
    
    // String and Int are not related
    assert!(not_rel_vec.contains(&(Type::String, Type::Int)) || 
            not_rel_vec.contains(&(Type::Int, Type::String)));
    
    // Bool and Float are not related
    assert!(not_rel_vec.contains(&(Type::Bool, Type::Float)) || 
            not_rel_vec.contains(&(Type::Float, Type::Bool)));
}
