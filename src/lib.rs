//! Spy crate is inspired by such famous Javascript testing tools
//! as Jasmine and Sinon.js. It provides easy configurable spies
//! with predefined behaviour.
//!
//! ```rust
//! #[test]
//! fn iterator_all_test() {
//!    let integers = vec![0i32, 1i32, 2i32];
//!    
//!    // create spy function that returns true if provided
//!    // argument is an even number
//!    let (spy_fn, spy) = spy!(|n| n % 2 == 0);
//!
//!    // test call
//!    let res = integers.iter().all(spy_fn);
//!
//!    // check Iterator::all result
//!    assert!(!res, "should be false");
//!
//!    // take a snapshot of made calls
//!    let snapshot = spy.snapshot();
//!
//!    // make assertions
//!    assert!(snapshot.called(), "should be called");
//!    assert!(
//!        snapshot.called_with(&(&1i32)),
//!        "should be called with 1i32 at least once"
//!    );
//!    assert!(
//!        !snapshot.each_called_with(&(&1i32)),
//!        "should be called with different arguments"
//!    );
//!    assert_eq!(snapshot.all_calls(), &vec![(&0i32), (&1i32)]);
//!    assert_eq!(snapshot.first_call().expect("should be Some"), &(&0i32));
//!    assert_eq!(snapshot.last_call().expect("should be Some"), &(&1i32));
//!    assert_eq!(snapshot.nth_call(1).expect("should be Some"), &(&1i32));
//!}
//! ```

use std::sync::mpsc::Receiver;

/// Spy object that tracks calls of associated spy function.
pub struct Spy<Args> {
    calls_recv: Receiver<Args>,
}

impl<Args: PartialEq> Spy<Args> {
    /// It takes a snapshot of a spy object. Taken snapshot
    /// contains all the calls starting from previous snapshot.
    pub fn snapshot(&self) -> SpySnapshot<Args> {
        let mut calls: Vec<Args> = vec![];
        loop {
            match self.calls_recv.recv() {
                Ok(args) => calls.push(args),
                Err(_) => {
                    break;
                }
            }
        }
        SpySnapshot { calls }
    }
}

/// The structure represents a snapshot of a spy object. Taken snapshot
/// contains all the calls starting from the moment when `Spy` object was created
/// or previous snapshot if there was taken one.
///
/// Generic type `Args` is in fact a tuple that describes argument values for each
/// call.
pub struct SpySnapshot<Args: PartialEq> {
    calls: Vec<Args>,
}

impl<Args: PartialEq> SpySnapshot<Args> {
    /// It returns `true` if spy function was called at least once and `false` otherwise.
    pub fn called(&self) -> bool {
        !self.calls.is_empty()
    }

    /// It returns `true` if spy function was called at least once
    /// with provided arguments and `false` otherwise.
    pub fn called_with(&self, args: &Args) -> bool {
        for call in &self.calls {
            if args == call {
                return true;
            }
        }
        false
    }

    /// It returns `true` if spy function was called with provided arguments each time
    /// it was called.
    pub fn each_called_with(&self, args: &Args) -> bool {
        for call in &self.calls {
            if args != call {
                return false;
            }
        }
        true
    }

    /// It returns how many times spy function was called.
    pub fn num_of_calls(&self) -> usize {
        self.calls.len()
    }

    /// It returns a vector that contains all calls arguments.
    pub fn all_calls(&self) -> &Vec<Args> {
        &self.calls
    }

    /// It returns first call arguments. `None` will be returned if spy function was not
    /// called till the moment when a snapshot was taken.
    pub fn first_call(&self) -> Option<&Args> {
        self.calls.first()
    }

    /// It returns last call arguments. `None` will be returned if spy function was not
    /// called till the moment when a snapshot was taken.
    pub fn last_call(&self) -> Option<&Args> {
        self.calls.last()
    }

    /// It returns n-th call arguments. `None` will be returned if spy function was not
    /// called enough times till the moment when a snapshot was taken.
    pub fn nth_call(&self, n: usize) -> Option<&Args> {
        self.calls.get(n)
    }
}

/// The macro that creates a pair of a `Spy` object and a spy function tracked by returned
/// spy.
///
/// ```rust
/// /// spy function that takes no argument and returns no value
/// let (spy_fn, spy) = spy!();
///
/// /// spy function that takes one argument argument and returns no value.
/// let (spy_fn, spy) = spy!(|n|);
///
/// /// spy function that takes one argument argument and returns some value
/// /// evaluated basing on taken argument.
/// let (spy_fn, spy) = spy!(|n| n % 2 == 0);
/// ```
#[macro_export]
macro_rules! spy {
    () => {
        {
            let (s, recv) = ::std::sync::mpsc::channel();
            let spy_fn = move || {
                s.send(())
                    .expect("Problem with call agregation: cannot send call arguments to channel");
            };
            (spy_fn, Spy{ calls_recv: recv })
        }
    };
    (|$($arg:ident),*|) => {
        {
            let (s, recv) = ::std::sync::mpsc::channel();
            let spy_fn = move |$($arg),*| {
                s.send($($arg),*)
                    .expect("Problem with call agregation: cannot send call arguments to channel");
            };
            (spy_fn, Spy{ calls_recv: recv })
        }
    };
    (|$($arg:ident),*| $expression:expr) => {
        {
            let (s, recv) = ::std::sync::mpsc::channel();
            let spy_fn = move |$($arg),*| {
                s.send($($arg),*)
                    .expect("Problem with call agregation: cannot send call arguments to channel");
                $expression
            };
            (spy_fn, Spy{ calls_recv: recv })
        }
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    fn no_args_cb<F>(cb: F)
    where
        F: Fn() + Sized,
    {
        // 3 times call
        cb();
        cb();
        cb();
    }

    #[test]
    fn create_spy_test() {
        // create spy function that takes no arguments
        let (spy_fn, spy) = spy!();

        no_args_cb(spy_fn);
        let snapshot = spy.snapshot();

        assert!(snapshot.called(), "should be called");
        assert!(
            snapshot.called_with(&()),
            "should be called with () at least once"
        );
        assert!(
            snapshot.each_called_with(&()),
            "should be called with () each time"
        );
        assert_eq!(snapshot.num_of_calls(), 3, "should be called 3 times");
        assert_eq!(snapshot.all_calls(), &vec![(), (), ()]);
        assert_eq!(snapshot.first_call().expect("should be Some"), &());
        assert_eq!(snapshot.last_call().expect("should be Some"), &());
        assert_eq!(snapshot.nth_call(1).expect("should be Some"), &());
    }

    #[test]
    fn create_spy_with_args_test() {
        // create spy function that takes no arguments
        let integers = vec![0i32, 1i32, 2i32];

        let (spy_fn, spy) = spy!(|n|);

        // test via Iterator::for_each
        integers.iter().for_each(spy_fn);
        let snapshot = spy.snapshot();

        assert!(snapshot.called(), "should be called");
        assert!(
            snapshot.called_with(&(&1i32)),
            "should be called with &1i32 at least once"
        );
        assert!(
            !snapshot.each_called_with(&(&1i32)),
            "should be called with different arguments"
        );
        assert_eq!(snapshot.num_of_calls(), 3, "should be called 3 times");
        assert_eq!(snapshot.all_calls(), &vec![(&0i32), (&1i32), (&2i32)]);
        assert_eq!(snapshot.first_call().expect("should be Some"), &(&0i32));
        assert_eq!(snapshot.last_call().expect("should be Some"), &(&2i32));
        assert_eq!(snapshot.nth_call(1).expect("should be Some"), &(&1i32));
    }

    #[test]
    fn create_spy_with_args_and_return_test() {
        // create spy function that takes no arguments
        let integers = vec![0i32, 1i32, 2i32];

        let (spy_fn, spy) = spy!(|n| n % 2 == 0);

        // test via Iterator::all
        let res = integers.iter().all(spy_fn);

        assert!(!res, "should be false");

        let snapshot = spy.snapshot();

        assert!(snapshot.called(), "should be called");
        assert!(
            snapshot.called_with(&(&1i32)),
            "should be called with &1i32 at least once"
        );
        assert!(
            !snapshot.each_called_with(&(&1i32)),
            "should be called with different arguments"
        );
        assert_eq!(snapshot.all_calls(), &vec![(&0i32), (&1i32)]);
        assert_eq!(snapshot.first_call().expect("should be Some"), &(&0i32));
        assert_eq!(snapshot.last_call().expect("should be Some"), &(&1i32));
        assert_eq!(snapshot.nth_call(1).expect("should be Some"), &(&1i32));
    }
}
