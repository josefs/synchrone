{-# LANGUAGE NPlusKPatterns #-}
module Synch where

import Prelude hiding (even,const)

-- data Stream t = t : Stream t

-- Co-iteration

pre v (x:xs) = v : pre x xs

plus (x:xs) (y:ys) = x + y : plus xs ys

even (x:x':xs) = x : even xs

type F t s = (t, s)

data CStream t s = Co (s -> F t s) s

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

const v = v : const v

data State s = Nil | St s

co_const :: t -> CStream t (State s)
co_const v = Co (\s -> (v,Nil)) Nil

extend (f:fs) (e:es) = f e : extend fs es

co_extend :: (CStream (t -> t') s') -> (CStream t s) -> CStream t' (s',s)
co_extend (Co f i) (Co e ie) =
  Co (\(sf,se) -> let (vf,sf') = f sf
                      (ve,se') = e se
                  in ((vf ve), (sf',se'))
     ) (i,ie)

-- In the paper this function is written in terms of streams, which seems
-- to be wrong
co_plus1 x y = co_extend (co_extend (co_const (+)) x) y

(x:xs) `fby` ys = x : ys

co_fby :: CStream t s -> CStream t s' -> CStream t ((State t), s,s')
Co tx ix `co_fby` Co ty iy =
  Co (\(init,sx,sy) -> let (vx, sx') = tx sx
                           (vy, sy') = ty sy
                       in case init of
                            Nil  -> (vx, ((St vy),sx',sy'))
                            St v -> (v,  ((St vy),sx',sy'))
     ) (Nil,ix,iy)

co_apply :: CStream (t -> State s' -> F t' (State s')) sf -> 
            CStream t s -> CStream t' ((State s'), sf, s)
co_apply (Co tf sf) (Co te se) =
  Co (\(st,sf,se) ->
        let (vf, sf') = tf sf
            (ve, se') = te se
            (v,  st') = vf ve st
        in (v, (st',sf',se'))
     ) (Nil,sf,se)

co_lambda :: (CStream t (State s) -> CStream t' s') ->
             CStream (t -> State s' -> F t' (State s')) (State sf)
co_lambda f =
  co_const (\v s -> let Co t i  = f (co_const v)
                        s1      = case s of Nil   -> i
                                            St s2 -> s2
                        (v',s') = t s1
                    in (v',St s')
           )

nat = pre 0 (plus nat (const 1))

co_nat = Co (\s -> (s, s+1)) 0

co_rec :: CStream (t -> State s -> F t (State s)) s' ->
          CStream t (State s, s')
co_rec (Co t i) = Co (\(se,s) ->
                         let (v,  s')  = t s
                             (ve, se') = v ve se
                         in  (ve, (se',s'))
                     ) (Nil, i)

co_product :: CStream t1 s1 -> CStream t2 s2 ->
              CStream (t1,t2) (s1,s2)
co_product (Co e1 i1) (Co e2 i2) =
  Co (\(s1,s2) -> let (v1,s1') = e1 s1
                      (v2,s2') = e2 s2
                  in  ((v1,v2), (s1',s2'))
     ) (i1, i2)

-- Non length-preserving stream functions

(x:xs) `when` (True :cs) = x : xs `when` cs
(x:xs) `when` (False:cs) = xs `when` cs

data F' t s = P t s | S s
data CStream' t s = Co' (s -> F' t s) s

co_even2 (Co' tx ix) = Co' (\(e,sx) ->
                             case tx sx of
                               S sx'    -> S (e, sx')
                               P vx sx' -> if e
                                           then P vx (False,sx')
                                           else S (True,sx')
                           ) (True,ix)

data Val t = E | V t

dest (v : vs) = case v of E   -> S vs
                          V v -> P v vs
{- Stuff used in proof of theorem 4
   Needs a definition of tx.

next s = case tx s of S s' -> s'; P v s' -> s'
nextN n s = if n == 0 then (next s) else nextN (n-1) (next s)

runS s 0 = case t s of S s' -> E ; P v s' -> V v
runS s (n+1) = run (next s) n

-}

clock s n = case s n of E -> False ; V v -> True

co_extend' :: CStream (Val (t -> t')) s' -> CStream (Val t) s
           -> CStream (Val t') (s',s)
co_extend' (Co f i) (Co e ie) =
  Co (\(sf,se) ->
       case ((f sf),(e se)) of
         ((E, sf),(E, se)) -> (E, (sf,se))
         ((V vf, sf),(V ve, se)) -> (V (vf ve), (sf,se))
     ) (i,ie)

copre :: t -> CStream (Val t) s -> CStream (Val t) (t,s)
copre v (Co e ie) =
  Co (\(pre,se) -> case e se of
                     (E, se')   -> (E, (pre,se'))
                     (V v, se') -> (V pre, (v,se'))
     ) (v,ie)

-- deadlock
xx = co_rec (co_lambda (\x -> copre 0 x))

x = pre 0 x

co_pre' :: t -> CStream (Val t) s -> CStream Bool s'
        -> CStream (Val t) (t,s,s')
co_pre' v (Co e ie) (Co cl icl) =
  Co (\(pre,se,scl) ->
       case cl scl of
         (False, scl') ->
           (E, let (E, se') = e se in (pre,se',scl'))
         (True, scl') ->
           (V pre, let (V v, se') = e se in (v,se',scl'))
     ) (v,ie,icl)

co_const1 v (Co tc ic) =
  Co (\s -> case tc s of (True, s')  -> (V v, s')
                         (False, s') -> (E, s')
     ) ic

co_fby' :: CStream (Val t) s -> CStream (Val t) s' ->
           CStream (Val t) ((State t), s, s')
Co tx ix `co_fby'` Co ty iy =
  Co (\(init,sx,sy) ->
       case tx sx of
         (E, sx') -> (E, let (E, sy') = ty sy
                         in (init,sx',sy'))
         (V vx, sx') -> (case init of
                           Nil -> V vx
                           St v -> V v
                        ,let (V v, sy') = ty sy
                         in ((St v),sx',sy'))
     ) (Nil,ix,iy)

co_when :: CStream (Val t) s -> CStream (Val Bool) sc
        -> CStream (Val t) (s, sc)
Co tx ix `co_when` Co tc ic =
  Co (\(sx,sc) ->
        case (tx sx, tc sc) of
          ((E, sx'),(E,sc'))     -> (E, (sx',sc'))
          ((V vx, sx'),(V True, sc')) -> (V vx, (sx',sc'))
          ((V vx, sx'),(V False,sc')) -> (E, (sx',sc'))
     ) (ix,ic)

on :: CStream Bool sc -> CStream (Val Bool) s
   -> CStream Bool (sc, s)
Co tcl icl `on` Co tc ic =
  Co (\(scl,sc) -> case tcl scl of
                     (False, scl') -> let (E, sc') = tc sc
                                      in (False, (scl',sc'))
                     (True,  scl') -> let (V vc, sc') = tc sc
                                      in  (vc, (scl',sc'))
     ) (icl,ic)


merge (False:cs) xs (y:ys) = y : merge cs xs ys
merge (True :cs) (x:xs) ys = x : merge cs xs ys

co_merge :: CStream (Val Bool) sc -> CStream (Val t) s ->
            CStream (Val t) s' -> CStream (Val t) (sc, s, s')
co_merge (Co tc ic) (Co tx ix) (Co ty iy) =
  Co (\(sc,sx,sy) ->
       case (tc sc, tx sx, ty sy) of
         ((E, sc'),(E,sx'),(E,sy')) ->
           (E, (sc',sx',sy'))
         ((V True,  sc'),(V vx,sx'),(E,sy')) ->
           (V vx, (sc',sx',sy'))
         ((V False, sc'),(E,sx'),(V vy,sy')) ->
           (V vy, (sc',sx',sy'))
     ) (ic,ix,iy)

