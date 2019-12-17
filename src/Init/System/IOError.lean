/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/

prelude
import Init.Core
import Init.Data.UInt
import Init.Data.ToString
import Init.Data.String.Basic

/-
Immitate the structure of IOErrorType in Haskell:
https://hackage.haskell.org/package/base-4.12.0.0/docs/System-IO-Error.html#t:IOErrorType
-/
inductive IO.Error
| alreadyExists (details : String) -- EEXIST, EINPROGRESS, EISCONN
| otherError (details : String)    -- EFAULT, default
| resourceBusy (details : String)
    -- EADDRINUSE, EBUSY, EDEADLK, ETXTBSY
| resourceVanished (details : String)
    -- ECONNRESET, EIDRM, ENETDOWN, ENETRESET,
    -- ENOLINK, EPIPE
| unsupportedOperation (details : String)
    -- EADDRNOTAVAIL, EAFNOSUPPORT, ENODEV, ENOPROTOOPT
    -- ENOSYS, EOPNOTSUPP, ERANGE, ESPIPE, EXDEV
| hardwareFault (details : String)          -- EIO
| unsatisfiedConstraints (details : String) -- ENOTEMPTY
| illegalOperation (details : String)       -- ENOTTY
| protocolError (details : String)
    -- EPROTO, EPROTONOSUPPORT, EPROTOTYPE
| timeExpired (details : String)
    -- ETIME, ETIMEDOUT

| interrupted (filename : String) (details : String)       -- EINTR
| noFileOrDirectory (filename : String) (details : String) -- ENOENT
| invalidArgument (filename : Option String) (details : String)
    -- ELOOP, ENAMETOOLONG, EDESTADDRREQ, EILSEQ, EINVAL, EDOM, EBADF
    -- ENOEXEC, ENOSTR, ENOTCONN, ENOTSOCK
| permissionDenied (filename : Option String) (details : String)
    -- EACCES, EROFS, ECONNABORTED, EFBIG, EPERM
| resourceExhausted (filename : Option String) (details : String)
    -- EMFILE, ENFILE, ENOSPC, E2BIG, EAGAIN, EMLINK:
    -- EMSGSIZE, ENOBUFS, ENOLCK, ENOMEM, ENOSR:
| inappropriateType (filename : Option String) (details : String)
    -- EISDIR, EBADMSG, ENOTDIR:
| noSuchThing (filename : Option String) (details : String)
    -- ENXIO, EHOSTUNREACH, ENETUNREACH, ECHILD, ECONNREFUSED,
    -- ENODATA, ENOMSG, ESRCH
-- overflow -- EOVERFLOW

| unexpectedEof
| userError (msg : String)

@[export mk_io_user_error]
def IO.userError (s : String) : IO.Error :=
IO.Error.userError s

namespace IO.Error

@[export lean_mk_io_error_eof]
def mkEofError : IO.Error := unexpectedEof

@[export lean_mk_io_error_inappropriate_type_file]
def mkInappropriateTypeFile : String → String → IO.Error :=
inappropriateType ∘ some

@[export lean_mk_io_error_interrupted]
def mkInterrupted : String → String → IO.Error :=
interrupted

@[export lean_mk_io_error_invalid_argument_file]
def mkInvalidArgumentFile : String → String → IO.Error :=
invalidArgument ∘ some

@[export lean_mk_io_error_no_file_or_directory]
def mkNoFileOrDirectory : String → String → IO.Error :=
noFileOrDirectory

@[export lean_mk_io_error_no_such_thing_file]
def mkNoSuchThingFile : String → String → IO.Error :=
noSuchThing ∘ some

@[export lean_mk_io_error_permission_denied_file]
def mkPermissionDeniedFile : String → String → IO.Error :=
permissionDenied ∘ some

@[export lean_mk_io_error_resource_exhausted_file]
def mkResourceExhaustedFile : String → String → IO.Error :=
resourceExhausted ∘ some

@[export lean_mk_io_error_unsupported_operation]
def mkUnsupportedOperation : String → IO.Error :=
unsupportedOperation

@[export lean_mk_io_error_resource_exhausted]
def mkResourceExhausted : String → IO.Error :=
resourceExhausted none

@[export lean_mk_io_error_already_exists]
def mkAlreadyExists : String → IO.Error :=
alreadyExists

@[export lean_mk_io_error_inappropriate_type]
def mkInappropriateType : String → IO.Error :=
inappropriateType none

@[export lean_mk_io_error_no_such_thing]
def mkNoSuchThing : String → IO.Error :=
noSuchThing none

@[export lean_mk_io_error_resource_vanished]
def mkResourceVanished : String → IO.Error :=
resourceVanished

@[export lean_mk_io_error_resource_busy]
def mkResourceBusy : String → IO.Error :=
resourceBusy

@[export lean_mk_io_error_invalid_argument]
def mkInvalidArgument : String → IO.Error :=
invalidArgument none

@[export lean_mk_io_error_other_error]
def mkOtherError : String → IO.Error :=
otherError

@[export lean_mk_io_error_permission_denied]
def mkPermissionDenied : String → IO.Error :=
permissionDenied none

@[export lean_mk_io_error_hardware_fault]
def mkHardwareFault : String → IO.Error :=
hardwareFault

@[export lean_mk_io_error_unsatisfied_constraints]
def mkUnsatisfiedConstraints : String → IO.Error :=
unsatisfiedConstraints

@[export lean_mk_io_error_illegal_operation]
def mkIllegalOperation : String → IO.Error :=
illegalOperation

@[export lean_mk_io_error_protocol_error]
def mkProtocolError : String → IO.Error :=
protocolError

@[export lean_mk_io_error_time_expired]
def mkTimeExpired : String → IO.Error :=
timeExpired

private def downCaseFirst (s : String) : String := s.set 0 (s.get 0).toLower

def fopenErrorToString (gist fn : String) : Option String → String
| some details => gist ++ ": " ++ downCaseFirst details ++ "\n  file: " ++ fn
| none => gist ++ "\n  file: " ++ fn

def otherErrorToString (gist : String) : Option String → String
| some details => gist ++ ": " ++ downCaseFirst details
| none => gist

@[export lean_io_error_to_string]
def toString : IO.Error → String
| unexpectedEof                       => "End of file"
| inappropriateType (some fn) details => fopenErrorToString "Inappropriate type" fn details
| inappropriateType none details      => otherErrorToString "Inappropriate type" details
| interrupted fn details              => fopenErrorToString "Interrupted system call" fn details
| invalidArgument (some fn) details   => fopenErrorToString "Invalid argument" fn details
| invalidArgument none details        => otherErrorToString "Invalid argument" details
| noFileOrDirectory fn details        => fopenErrorToString "No such file or directory" fn none
| noSuchThing (some fn) details       => fopenErrorToString "No such thing" fn details
| noSuchThing none details            => otherErrorToString "No such thing" details
| permissionDenied (some fn) details  => fopenErrorToString details fn none
| permissionDenied none details       => otherErrorToString details none
| resourceExhausted (some fn) details => fopenErrorToString "Resource exhausted" fn details
| resourceExhausted none details      => otherErrorToString "Resource exhausted" details
| alreadyExists details               => otherErrorToString "Already exists" details
| otherError details                  => details
| resourceBusy details                => otherErrorToString "Resource busy" details
| resourceVanished details            => otherErrorToString "Resource vanished" details
| hardwareFault _                     => otherErrorToString "Hardware fault" none
| illegalOperation details            => otherErrorToString "Illegal operation" details
| protocolError details               => otherErrorToString "Protocol error" details
| timeExpired details                 => otherErrorToString "Time expired" details
| unsatisfiedConstraints details      => otherErrorToString "Directory not empty" none
| unsupportedOperation details        => otherErrorToString "Unsupported operation" details
| userError msg                       => msg

instance : HasToString IO.Error := ⟨ IO.Error.toString ⟩
instance : Inhabited IO.Error := ⟨ userError "" ⟩

end IO.Error
