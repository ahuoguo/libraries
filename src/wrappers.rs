use vstd::prelude::*;

verus! {
    
// ************ These need to be defined again or already exist? ************    
    // enum Option<T>{
    //     None,
    //     Some(T),
    // }

    // enum Result<T,R>{
    //     Ok(T),
    //     Err(R),
    // }

    // enum Outcome<E>{
    //     Pass,
    //     Fail(E),
    // }
    
    // impl<T> Option<T>{
    //     //to_result, as_result, ok_or
    //     fn ok_or<R>(&self, error: R) -> Result<T,R>
    //     {
    //         match &self{
    //             Some(v) => Ok(v),
    //             None => Err(error),
    //         }
    //     }
    // }
    impl vstd::Option<T>
    {    
        fn ok_or<E>(option: vstd::Option<T>, error: E) -> vstd::Result<T,E>
            {
                match option{
                    Some(v) => Ok(v),
                    None => Err(error),
                }
            }
    }

    fn main(){}
}