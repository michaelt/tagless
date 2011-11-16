-- Sample functions to use for type-directed partial evaluation (TDPE)
-- Compiling this module makes for a nicer example

module ToTDPE where

-- ``black-box'' functions

bbf1 x y = x

bbf2 f = f . f . (id f)
