{-# OPTIONS --without-K #-}

module example-daysOfWeek where 
 
 
import 00-preamble 
open 00-preamble public

data day : Type lzero where
  Sunday Monday Tuesday Wednesday Thursday Friday Saturday : day 

next : day → day 
next Sunday = Monday
next Monday = Tuesday
next Tuesday = Wednesday
next Wednesday = Thursday
next Thursday = Friday
next Friday = Saturday
next Saturday = Sunday

prev : day → day 
prev Sunday = Saturday
prev Monday = Sunday
prev Tuesday = Monday
prev Wednesday = Tuesday
prev Thursday = Wednesday
prev Friday = Thursday
prev Saturday = Friday

