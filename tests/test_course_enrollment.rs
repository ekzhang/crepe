// This test checks stratified negation with multiple strata.
// It demonstrates complex negation patterns and set difference operations.

use crepe::crepe;

crepe! {
    @input
    struct Student(&'static str);

    @input
    struct EnrolledIn(&'static str, &'static str);

    @input
    struct Prerequisite(&'static str, &'static str);

    @output
    struct CanEnroll(&'static str, &'static str);

    @output
    struct MissingPrereq(&'static str, &'static str);

    struct HasPrerequisite(&'static str, &'static str);

    // Student has taken the prerequisite if enrolled in it
    HasPrerequisite(student, course) <-
        Prerequisite(course, prereq),
        EnrolledIn(student, prereq);

    // Student can enroll if not already enrolled
    // and either no prerequisite exists or they have it
    CanEnroll(student, course) <-
        Student(student),
        Prerequisite(course, _),
        !EnrolledIn(student, course),
        HasPrerequisite(student, course);

    // Can also enroll if no prerequisites exist
    CanEnroll(student, course) <-
        Student(student),
        Prerequisite(course, _),
        !EnrolledIn(student, course),
        !Prerequisite(course, _);

    // Missing prerequisite
    MissingPrereq(student, course) <-
        Student(student),
        Prerequisite(course, prereq),
        !EnrolledIn(student, prereq);
}

#[test]
fn test_stratified_negation() {
    let mut runtime = Crepe::new();
    runtime.extend([
        Student("alice"),
        Student("bob"),
        Student("charlie"),
    ]);
    runtime.extend([
        EnrolledIn("alice", "math101"),
        EnrolledIn("alice", "cs101"),
        EnrolledIn("bob", "math101"),
        EnrolledIn("charlie", "cs101"),
    ]);
    runtime.extend([
        Prerequisite("cs201", "cs101"),
        Prerequisite("math201", "math101"),
        Prerequisite("cs301", "cs201"),
    ]);

    let (can_enroll, missing) = runtime.run();
    
    let can_vec: Vec<_> = can_enroll
        .into_iter()
        .map(|CanEnroll(s, c)| (s, c))
        .collect();
    
    // Alice has both cs101 and math101, can enroll in cs201 and math201
    assert!(can_vec.contains(&("alice", "cs201")));
    assert!(can_vec.contains(&("alice", "math201")));
    
    // Bob only has math101
    assert!(can_vec.contains(&("bob", "math201")));
    assert!(!can_vec.contains(&("bob", "cs201")));
    
    let missing_vec: Vec<_> = missing
        .into_iter()
        .map(|MissingPrereq(s, c)| (s, c))
        .collect();
    
    // Bob is missing cs101 for cs201
    assert!(missing_vec.contains(&("bob", "cs201")));
    
    // Charlie is missing math101 for math201
    assert!(missing_vec.contains(&("charlie", "math201")));
}
