{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE ScopedTypeVariables        #-}

module TRP (
    Trigger(..),
    Behavior(..),
    Dynamic(..),
    MakeDynamic(..),
    distribute,
    disburse,
    merge,
    filterT,
    apply,
    update,
    accum,
    switchT,
    switchB,
    filterJust,
    filterApply,
    whenT,
    once,
    mapAccum
) where

    import           Control.Concurrent.STM
    import           Control.Monad                        (join)
    import           Control.Monad.ST
    import           Control.Selective
    import           Data.Bitraversable
    import           Data.Foldable                        (traverse_)
    import           Data.Functor.Contravariant
    import           Data.Functor.Contravariant.Divisible
    import           Data.IORef
    import           Data.STRef
    import           Data.Void

    newtype Trigger m a = Trigger { trigger :: a -> m () }

    instance Contravariant (Trigger m) where
        contramap f tri = Trigger $ trigger tri . f
        b >$ trig = Trigger $ \_ -> trigger trig b

    distribute :: forall m f a b .
                    (Bitraversable f
                    , Applicative m)
                    => Trigger m a
                    -> Trigger m b
                    -> Trigger m (f a b)
    distribute tra trb =
        Trigger $
            \f -> const () <$> bitraverse (trigger tra) (trigger trb) f

    disburse :: forall m f a .
                    (Foldable f
                    , Applicative m)
                    => f (Trigger m a)
                    -> Trigger m a
    disburse fs = Trigger $ \a -> traverse_ (flip trigger a) fs

    instance Applicative m => Divisible (Trigger m) where
        divide f trb trc = contramap f $ distribute trb trc
        conquer = Trigger $ \_ -> pure ()

    instance Applicative m => Decidable (Trigger m) where
        choose f trb trc = contramap f $ distribute trb trc
        lose f = Trigger $ \a -> absurd (f a)

    newtype Behavior m a = Behavior { sample :: m a }
        deriving (Functor, Applicative, Monad, Selective)

    data Dynamic m a = Dynamic {
                            getTrigger :: Trigger m a,
                            getBehavior :: Behavior m a
                        }

    class MakeDynamic m n where
        makeDynamic :: forall a . a -> n (Dynamic m a)

    instance MakeDynamic STM IO where
        makeDynamic x = fixup <$> newTVarIO x
            where
                fixup :: TVar a -> Dynamic STM a
                fixup tvar = Dynamic {
                                getTrigger = Trigger (writeTVar tvar),
                                getBehavior = Behavior (readTVar tvar) }


    instance MakeDynamic IO IO where
        makeDynamic x = fixup <$> newIORef x
            where
                fixup :: IORef a -> Dynamic IO a
                fixup ref = Dynamic {
                                getTrigger = Trigger (writeIORef ref),
                                getBehavior = Behavior (readIORef ref) }

    instance MakeDynamic (ST s) (ST s) where
        makeDynamic x = fixup <$> newSTRef x 
            where
                fixup :: STRef s a -> Dynamic (ST s) a
                fixup ref = Dynamic {
                                getTrigger = Trigger (writeSTRef ref),
                                getBehavior = Behavior (readSTRef ref) }

    merge :: Applicative m => Trigger m a -> Trigger m a -> Trigger m a
    merge = divide (\a -> (a, a))

    filterT :: Applicative m => (a -> Bool) -> Trigger m a -> Trigger m a
    filterT test tr =
        Trigger $ \a ->
            if test a
            then trigger tr a
            else pure ()

    apply :: Monad m
                => Behavior m (a -> b)
                -> Trigger m b
                -> Trigger m a
    apply bh tr = Trigger $ \a -> do
                        f :: a -> b <- sample bh
                        let b = f a
                        trigger tr b

    update :: Monad m
                => Dynamic m a
                -> Trigger m (a -> a)
    update dyn = Trigger $ \f -> do
                    curr <- sample (getBehavior dyn)
                    let new = f curr
                    trigger (getTrigger dyn) new

    -- This replaces both accumE and accumB
    accum :: forall m n a . 
                (Monad m
                , MakeDynamic m n
                , Functor n) 
                => a 
                -> Trigger m a 
                -> n (Trigger m (a -> a), Behavior m a)
    accum x sink = go <$> makeDynamic x
        where
            go :: Dynamic m a -> (Trigger m (a -> a), Behavior m a)
            go dyn = (doUpdate dyn, getBehavior dyn)

            doUpdate :: Dynamic m a -> Trigger m (a -> a)
            doUpdate dyn = Trigger $ \f -> do
                curr <- sample (getBehavior dyn)
                let new = f curr
                trigger (getTrigger dyn) new
                trigger sink new

    switchT :: Monad m => Behavior m (Trigger m a) -> Trigger m a
    switchT beh = Trigger $ \a -> do
                        t <- sample beh
                        trigger t a

    switchB :: forall m n a .
                (MakeDynamic m n
                , Functor n
                , Monad m)
                => Behavior m a
                -> n (Behavior m a, Trigger m (Behavior m a))
    switchB x = go <$> makeDynamic x
        where
            go :: Dynamic m (Behavior m a)
                    -> (Behavior m a, Trigger m (Behavior m a))
            go dyn = (join (getBehavior dyn), getTrigger dyn)
            

    filterJust :: Monad m => Trigger m a -> Trigger m (Maybe a)
    filterJust tri = Trigger $ \m ->
        case m of
            Just a  -> trigger tri a
            Nothing -> pure ()
    
    filterApply :: Monad m
                    => Behavior m (a -> Bool)
                    -> Trigger m a
                    -> Trigger m a
    filterApply beh tri = Trigger $ \a -> do
                                f <- sample beh
                                if f a
                                then trigger tri a
                                else pure ()

    whenT :: Monad m
                => Behavior m Bool
                -> Trigger m a
                -> Trigger m a
    whenT beh tri = Trigger $ \a -> do
                        b <- sample beh
                        if b
                        then trigger tri a
                        else pure ()

    once :: forall m n a .
            (MakeDynamic m n
            , Functor n
            , Monad m)
            => Trigger m a
            -> n (Trigger m a)
    once tri = go <$> makeDynamic True
        where
            go :: Dynamic m Bool -> Trigger m a
            go dyn = Trigger $ \a -> do
                        b <- sample (getBehavior dyn)
                        if b
                        then do
                            trigger (getTrigger dyn) False
                            trigger tri a
                        else pure ()

    mapAccum :: forall m n a acc .
                (MakeDynamic m n
                , Functor n
                , Monad m)
                => acc
                -> Trigger m a
                -> n (Trigger m (acc -> (a, acc)), Behavior m acc)
    mapAccum acc tri = go <$> makeDynamic acc
        where
            go :: Dynamic m acc
                    -> (Trigger m (acc -> (a, acc)), Behavior m acc)
            go dyn = (doUpdate dyn, getBehavior dyn)

            doUpdate :: Dynamic m acc -> Trigger m (acc -> (a, acc))
            doUpdate dyn = Trigger $ \f -> do
                curr <- sample (getBehavior dyn)
                let (a, new) = f curr
                trigger (getTrigger dyn) new
                trigger tri a

