def Foo.x : Unit := ()
def Bar.x : Unit := ()
def y : Unit := Foo.x

open Foo Bar

#print y

def y' : Unit := x

def x := 1

namespace Rig
def x := _root_.x
#print x
