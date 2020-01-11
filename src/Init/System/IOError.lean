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
Imitate the structure of IOErrorType in Haskell:
https://hackage.haskell.org/package/base-4.12.0.0/docs/System-IO-Error.html#t:IOErrorType
-/
inductive IO.Error
| alreadyExists (osCode : UInt32) (details : String) -- EEXIST, EINPROGRESS, EISCONN
| otherError (osCode : UInt32) (details : String)    -- EFAULT, default
| resourceBusy (osCode : UInt32) (details : String)
    -- EADDRINUSE, EBUSY, EDEADLK, ETXTBSY
| resourceVanished (osCode : UInt32) (details : String)
    -- ECONNRESET, EIDRM, ENETDOWN, ENETRESET,
    -- ENOLINK, EPIPE
| unsupportedOperation (osCode : UInt32) (details : String)
    -- EADDRNOTAVAIL, EAFNOSUPPORT, ENODEV, ENOPROTOOPT
    -- ENOSYS, EOPNOTSUPP, ERANGE, ESPIPE, EXDEV
| hardwareFault (osCode : UInt32) (details : String)          -- EIO
| unsatisfiedConstraints (osCode : UInt32) (details : String) -- ENOTEMPTY
| illegalOperation (osCode : UInt32) (details : String)       -- ENOTTY
| protocolError (osCode : UInt32) (details : String)
    -- EPROTO, EPROTONOSUPPORT, EPROTOTYPE
| timeExpired (osCode : UInt32) (details : String)
    -- ETIME, ETIMEDOUT

| interrupted (filename : String) (osCode : UInt32) (details : String)       -- EINTR
| noFileOrDirectory (filename : String) (osCode : UInt32) (details : String) -- ENOENT
| invalidArgument (filename : Option String) (osCode : UInt32) (details : String)
    -- ELOOP, ENAMETOOLONG, EDESTADDRREQ, EILSEQ, EINVAL, EDOM, EBADF
    -- ENOEXEC, ENOSTR, ENOTCONN, ENOTSOCK
| permissionDenied (filename : Option String) (osCode : UInt32) (details : String)
    -- EACCES, EROFS, ECONNABORTED, EFBIG, EPERM
| resourceExhausted (filename : Option String) (osCode : UInt32) (details : String)
    -- EMFILE, ENFILE, ENOSPC, E2BIG, EAGAIN, EMLINK:
    -- EMSGSIZE, ENOBUFS, ENOLCK, ENOMEM, ENOSR:
| inappropriateType (filename : Option String) (osCode : UInt32) (details : String)
    -- EISDIR, EBADMSG, ENOTDIR:
| noSuchThing (filename : Option String) (osCode : UInt32) (details : String)
    -- ENXIO, EHOSTUNREACH, ENETUNREACH, ECHILD, ECONNREFUSED,
    -- ENODATA, ENOMSG, ESRCH

| unexpectedEof
| userError (msg : String)

@[export mk_io_user_error]
def IO.userError (s : String) : IO.Error :=
IO.Error.userError s

namespace IO.Error

@[export lean_mk_io_error_eof]
def mkEofError : IO.Error := unexpectedEof

@[export lean_mk_io_error_inappropriate_type_file]
def mkInappropriateTypeFile : String → UInt32 → String → IO.Error :=
inappropriateType ∘ some

@[export lean_mk_io_error_interrupted]
def mkInterrupted : String → UInt32 → String → IO.Error :=
interrupted

@[export lean_mk_io_error_invalid_argument_file]
def mkInvalidArgumentFile : String → UInt32 → String → IO.Error :=
invalidArgument ∘ some

@[export lean_mk_io_error_no_file_or_directory]
def mkNoFileOrDirectory : String → UInt32 → String → IO.Error :=
noFileOrDirectory

@[export lean_mk_io_error_no_such_thing_file]
def mkNoSuchThingFile : String → UInt32 → String → IO.Error :=
noSuchThing ∘ some

@[export lean_mk_io_error_permission_denied_file]
def mkPermissionDeniedFile : String → UInt32 → String → IO.Error :=
permissionDenied ∘ some

@[export lean_mk_io_error_resource_exhausted_file]
def mkResourceExhaustedFile : String → UInt32 → String → IO.Error :=
resourceExhausted ∘ some

@[export lean_mk_io_error_unsupported_operation]
def mkUnsupportedOperation : UInt32 → String → IO.Error :=
unsupportedOperation

@[export lean_mk_io_error_resource_exhausted]
def mkResourceExhausted : UInt32 → String → IO.Error :=
resourceExhausted none

@[export lean_mk_io_error_already_exists]
def mkAlreadyExists : UInt32 → String → IO.Error :=
alreadyExists

@[export lean_mk_io_error_inappropriate_type]
def mkInappropriateType : UInt32 → String → IO.Error :=
inappropriateType none

@[export lean_mk_io_error_no_such_thing]
def mkNoSuchThing : UInt32 → String → IO.Error :=
noSuchThing none

@[export lean_mk_io_error_resource_vanished]
def mkResourceVanished : UInt32 → String → IO.Error :=
resourceVanished

@[export lean_mk_io_error_resource_busy]
def mkResourceBusy : UInt32 → String → IO.Error :=
resourceBusy

@[export lean_mk_io_error_invalid_argument]
def mkInvalidArgument : UInt32 → String → IO.Error :=
invalidArgument none

@[export lean_mk_io_error_other_error]
def mkOtherError : UInt32 → String → IO.Error :=
otherError

@[export lean_mk_io_error_permission_denied]
def mkPermissionDenied : UInt32 → String → IO.Error :=
permissionDenied none

@[export lean_mk_io_error_hardware_fault]
def mkHardwareFault : UInt32 → String → IO.Error :=
hardwareFault

@[export lean_mk_io_error_unsatisfied_constraints]
def mkUnsatisfiedConstraints : UInt32 → String → IO.Error :=
unsatisfiedConstraints

@[export lean_mk_io_error_illegal_operation]
def mkIllegalOperation : UInt32 → String → IO.Error :=
illegalOperation

@[export lean_mk_io_error_protocol_error]
def mkProtocolError : UInt32 → String → IO.Error :=
protocolError

@[export lean_mk_io_error_time_expired]
def mkTimeExpired : UInt32 → String → IO.Error :=
timeExpired

private def downCaseFirst (s : String) : String := s.modify 0 Char.toLower

def fopenErrorToString (gist fn : String) (code : UInt32) : Option String → String
| some details => gist ++ " (error code: " ++ toString code ++ ", " ++ downCaseFirst details ++ ")\n  file: " ++ fn
| none => gist ++ " (error code: " ++ toString code ++ ")\n  file: " ++ fn

def otherErrorToString (gist : String) (code : UInt32) : Option String → String
| some details => gist ++ " (error code: " ++ toString code ++ ", " ++ downCaseFirst details ++ ")"
| none => gist ++ " (error code: " ++ toString code ++ ")"

@[export lean_io_error_to_string]
def toString : IO.Error → String
| unexpectedEof                            => "End of file"
| inappropriateType (some fn) code details => fopenErrorToString "Inappropriate type" fn code details
| inappropriateType none code details      => otherErrorToString "Inappropriate type" code details
| interrupted fn code details              => fopenErrorToString "Interrupted system call" fn code details
| invalidArgument (some fn) code details   => fopenErrorToString "Invalid argument" fn code details
| invalidArgument none code details        => otherErrorToString "Invalid argument" code details
| noFileOrDirectory fn code _              => fopenErrorToString "No such file or directory" fn code none
| noSuchThing (some fn) code details       => fopenErrorToString "No such thing" fn code details
| noSuchThing none code details            => otherErrorToString "No such thing" code details
| permissionDenied (some fn) code details  => fopenErrorToString details fn code none
| permissionDenied none code details       => otherErrorToString details code none
| resourceExhausted (some fn) code details => fopenErrorToString "Resource exhausted" fn code details
| resourceExhausted none code details      => otherErrorToString "Resource exhausted" code details
| alreadyExists code details               => otherErrorToString "Already exists" code details
| otherError code details                  => otherErrorToString details code none
| resourceBusy code details                => otherErrorToString "Resource busy" code details
| resourceVanished code details            => otherErrorToString "Resource vanished" code details
| hardwareFault code _                     => otherErrorToString "Hardware fault" code none
| illegalOperation code details            => otherErrorToString "Illegal operation" code details
| protocolError code details               => otherErrorToString "Protocol error" code details
| timeExpired code details                 => otherErrorToString "Time expired" code details
| unsatisfiedConstraints code _            => otherErrorToString "Directory not empty" code none
| unsupportedOperation code details        => otherErrorToString "Unsupported operation" code details
| userError msg                            => msg

instance : HasToString IO.Error := ⟨ IO.Error.toString ⟩
instance : Inhabited IO.Error := ⟨ userError "" ⟩

end IO.Error
