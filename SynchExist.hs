{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ImpredicativeTypes #-}
module SynchExist where

import Prelude hiding (const)

data CStream t = forall s. Co (s -> (t, s)) s

co_pre v (Co tx ix) = Co (\(s,sx) -> let (v1,sx1) = tx sx
                                     in  (s, (v1,sx1))
                         ) (v,ix)

co_plus (Co tx ix) (Co ty iy) =
  Co (\(sx,sy) -> let (vx,sx') = tx sx
                      (vy,sy') = ty sy
                  in  ((vx+vy),(sx',sy'))
     ) (ix,iy)

co_even (Co tx ix) = Co (\sx -> let (vx1, sx1) = tx sx
                                    (vx2, sx2) = tx sx1
                                in  (vx2, sx2)
                        ) ix

run (Co tx sx) = let (vx, sx') = tx sx
                 in vx : run (Co tx sx')


teven tx sx = (\sx -> let (vx1, sx1) = tx sx
                          (vx2, sx2) = tx sx1
                      in  (vx2, sx2)
              )

seven tx sx = sx

co_even1 (Co tx sx) = Co (teven tx sx) (seven tx sx)

tpre vx sx = (sx,vx)

co_pre1 v (Co tx sx) =
  Co (\(s,sx) -> let (vx, sx') = tx sx
                     (v, s')   = tpre vx s
                 in (v, (s', sx'))
     ) (v,sx)

-- Length-preserving functions

data State s = Nil | St s

co_const :: t -> CStream t
co_const v = Co (\s -> (v,Nil)) Nil

co_extend :: CStream (t -> t') -> CStream t -> CStream t'
co_extend (Co f i) (Co e ie) =
  Co (\(sf,se) -> let (vf,sf') = f sf
                      (ve,se') = e se
                  in ((vf ve), (sf',se'))
     ) (i,ie)

co_plus1 x y = co_extend (co_extend (co_const (+)) x) y

co_fby :: CStream t -> CStream t -> CStream t
Co tx ix `co_fby` Co ty iy =
  Co (\(init,sx,sy) -> let (vx, sx') = tx sx
                           (vy, sy') = ty sy
                       in case init of
                            Nil  -> (vx, ((St vy),sx',sy'))
                            St v -> (v,  ((St vy),sx',sy'))
     ) (Nil,ix,iy)

co_apply :: CStream (t -> State s' -> (t' ,State s')) -> 
            CStream t -> CStream t'
co_apply (Co tf sf) (Co te se) =
  Co (\(st,sf,se) ->
        let (vf, sf') = tf sf
            (ve, se') = te se
            (v,  st') = vf ve st
        in (v, (st',sf',se'))
     ) (Nil,sf,se)

{- Couldn't make this work in GHC. The support for impredicative types is
   still weak.

co_lambda :: (CStream t -> CStream t') ->
             CStream (forall s. t -> State s -> (t',State s))
co_lambda f =
  co_const (\v s -> case f (co_const v) of
                      Co t i ->
                        let (v',s') = t s1
                            s1      = case s of Nil   -> i
                                                St s2 -> s2
                        in (v',St s')
           )
-}
co_const' :: (forall s. t -> State s -> (t', State s)) ->
             CStream (forall s. t -> State s -> (t', State s))
co_const' v = Co (\s -> (v,Nil)) Nil


apa :: (forall a. a -> a) -> (forall a. a -> a, forall a. a -> a)
apa id = (id,id)

bepa :: (forall a. a -> a) -> CStream (forall a. a -> a)
bepa id = Co (\_ -> (id,Nil)) Nil

data P a = P a

cepa :: (forall a. a -> a) -> P (forall a. a -> a)
cepa id = P id

co_nat = Co (\s -> (s, s+1)) 0

co_rec :: CStream (t -> State s -> (t,State s)) ->
          CStream t
co_rec (Co t i) = Co (\(se,s) ->
                         let (v,  s')  = t s
                             (ve, se') = v ve se
                         in  (ve, (se',s'))
                     ) (Nil, i)

co_product :: CStream t1 -> CStream t2 ->
              CStream (t1,t2)
co_product (Co e1 i1) (Co e2 i2) =
  Co (\(s1,s2) -> let (v1,s1') = e1 s1
                      (v2,s2') = e2 s2
                  in  ((v1,v2), (s1',s2'))
     ) (i1, i2)

