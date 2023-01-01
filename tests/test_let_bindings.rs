// This test ensures that variables defined in `let` bindings are registered.

use crepe::crepe;

struct Wrapper<T> {
    x: T,
}

enum Wrapper2<T> {
    Inner { y: T },
}

impl<T> Wrapper2<T> {
    fn new(y: T) -> Self {
        Self::Inner { y }
    }
}

crepe! {
    @input
    struct Input(i32);

    @output
    #[derive(Debug)]
    struct Output(i32);

    Output(x) <-
        Input(x),
        let y = 2 * x,
        let Some(y) = Some(y),
        let Wrapper { x: y } = (Wrapper { x: y }),
        let Wrapper2::Inner { y } = Wrapper2::new(y),
        Input(y);
}

#[test]
fn test_let_bindings() {
    let mut rt = Crepe::new();
    rt.extend([Input(2), Input(3), Input(4)]);
    let (res,) = rt.run();
    let res: Vec<_> = res.into_iter().collect();
    assert_eq!(res, vec![Output(2)]);
}
