section

parameter n : false
def blah (n : false) : false := n
#check @blah -- blah : false

end

#check @blah -- blah : false

theorem fs : false → false := blah -- failed to add declaration to environment, it contains local constants

#print blah -- error: invalid #print command (reported at a line below)
