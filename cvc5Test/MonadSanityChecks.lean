import cvc5



/-! # Class inference sanity checks -/
namespace cvc5.Test.ClassInference

variable [Monad m]

example : Monad Env := inferInstance

example : MonadLiftT (Except Error) (EnvT m) := inferInstance
example : MonadLiftT (Except Error) Env := inferInstance
example : MonadLiftT m (EnvT m) := inferInstance

example [MonadLiftT BaseIO m] : MonadLiftT BaseIO (EnvT m) := inferInstance
example : MonadLiftT IO Env := inferInstance
example : MonadLiftT BaseIO Env := inferInstance

example : MonadExcept Error Env := inferInstance

end ClassInference
