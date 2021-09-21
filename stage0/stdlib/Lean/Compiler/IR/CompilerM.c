// Lean compiler output
// Module: Lean.Compiler.IR.CompilerM
// Imports: Init Lean.Environment Lean.Compiler.IR.Basic Lean.Compiler.IR.Format
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_contains___at_Lean_IR_containsDecl___spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_IR_containsDecl_x27___spec__1(lean_object*, lean_object*, size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_getEnv___boxed(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
static lean_object* l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____lambda__2___closed__5;
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* lean_ir_add_decl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_mkEntryArray___spec__4(lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_Std_Format_defWidth;
static lean_object* l_Lean_IR_findEnvDecl_x27___closed__2;
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___at_Lean_IR_getDecls___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__6___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint32_t l_Lean_IR_declMapExt___elambda__4___rarg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_mkEntryArray(lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMapImp_contains___at_Lean_IR_containsDecl___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_AssocList_contains___at_Lean_IR_containsDecl___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getState___at_Lean_IR_findEnvDecl___spec__1___boxed(lean_object*, lean_object*);
size_t l_USize_sub(size_t, size_t);
static lean_object* l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_addDecls___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instHashableName;
LEAN_EXPORT lean_object* l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364_(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_log___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_mkEntryArray___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__2(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_declMapExt___elambda__4___rarg(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3___closed__6;
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____closed__4;
LEAN_EXPORT lean_object* l_Lean_IR_getEnv___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_fmt(lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_getState___at_Lean_IR_findEnvDecl___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_mkEntryArray___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_mkEntryArray___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_containsAux___at_Lean_IR_containsDecl___spec__5(lean_object*, size_t, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Log_format___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Log_format___spec__1___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_declMapExt___elambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__7(lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_name(lean_object*);
static lean_object* l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____lambda__2___closed__4;
static lean_object* l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__6___lambda__4___closed__1;
extern lean_object* l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_invalidExtMsg;
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__6___lambda__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_declMapExt___elambda__1(lean_object*);
size_t l_UInt64_toUSize(uint64_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__4(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__6___lambda__4___closed__2;
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3___closed__4;
static lean_object* l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____lambda__2___closed__2;
lean_object* l_Std_HashMap_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__6___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_tracePrefixOptionName___closed__5;
LEAN_EXPORT lean_object* l_Lean_IR_log(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____lambda__2___closed__1;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__6___lambda__4(lean_object*);
static lean_object* l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____closed__5;
static size_t l_Std_PersistentHashMap_containsAux___at_Lean_IR_containsDecl___spec__5___closed__2;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_SMap_contains___at_Lean_IR_containsDecl___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_IR_LogEntry_fmt___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_getDecls(lean_object*);
lean_object* l_EStateM_bind___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_logDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_declMapExt___elambda__3___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____closed__3;
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_containsAtAux___at_Lean_IR_containsDecl___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
static lean_object* l_Lean_IR_LogEntry_fmt___closed__6;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_ir_log_to_string(lean_object*);
static lean_object* l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____lambda__2___closed__3;
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAtAux___at_Lean_IR_containsDecl___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__6(lean_object*, lean_object*);
lean_object* l_Lean_SMap_instInhabitedSMap___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___at_Lean_IR_getDecls___spec__1(lean_object*, lean_object*);
uint64_t l_Lean_Name_hash(lean_object*);
lean_object* l_Nat_repr(lean_object*);
static lean_object* l_Lean_IR_declMapExt___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_logMessage(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at_Lean_IR_findEnvDecl___spec__4(lean_object*, lean_object*);
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_getDecl___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_IR_getDecl___closed__2;
static lean_object* l_Lean_IR_declMapExt___closed__5;
static lean_object* l_Lean_IR_getDecl___closed__1;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_shiftLeft(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_declMapExt___elambda__2(lean_object*);
static lean_object* l_Lean_IR_declMapExt___closed__7;
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_persistentEnvExtensionsRef;
static lean_object* l_Lean_IR_LogEntry_fmt___closed__5;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Log_format___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_getEnv(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_getDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_IR_findEnvDecl_x27___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__7___lambda__1(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_declMapExt___elambda__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_IR_containsDecl_x27___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_instToFormatLogEntry;
LEAN_EXPORT lean_object* l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__7___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_getDecl_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_IR_findEnvDecl___spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_LogEntry_fmt___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_modifyEnv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_declMapExt___elambda__4(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
static lean_object* l_Lean_IR_declMapExt___closed__4;
static lean_object* l_Lean_IR_tracePrefixOptionName___closed__6;
static lean_object* l_Lean_IR_tracePrefixOptionName___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_addDecls(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__7___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_tracePrefixOptionName;
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_addDecls___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_LogEntry_fmt___closed__3;
static lean_object* l_Lean_IR_declMapExt___closed__2;
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_contains___at_Lean_IR_containsDecl___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Log_format(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAux___at_Lean_IR_containsDecl___spec__5___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_declMapExt___closed__1;
LEAN_EXPORT lean_object* l_Std_HashMapImp_contains___at_Lean_IR_containsDecl___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_LogEntry_fmt___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_logDecls(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3___closed__2;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_IR_LogEntry_instToFormatLogEntry___closed__1;
lean_object* l_Lean_IR_formatDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_getState___at_Lean_IR_findEnvDecl___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_addDecls___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getState___at_Lean_IR_findEnvDecl___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__6___lambda__3(lean_object*, lean_object*);
static lean_object* l_Lean_IR_tracePrefixOptionName___closed__4;
static lean_object* l_Lean_IR_declMapExt___closed__6;
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_mkEntryArray___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_contains___at_Lean_IR_containsDecl___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_IR_tracePrefixOptionName___closed__1;
static lean_object* l_Lean_IR_findEnvDecl_x27___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Log_format___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_IR_findEnvDecl___spec__5(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__7___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentEnvExtensionState___rarg(lean_object*);
static size_t l_Std_PersistentHashMap_containsAux___at_Lean_IR_containsDecl___spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____lambda__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_addDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_findCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Log_format___boxed(lean_object*);
static lean_object* l_Lean_IR_LogEntry_fmt___closed__4;
static lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__7___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_modifyEnv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__7___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_ir_find_env_decl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_decl_get_sorry_dep(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_mkEntryArray___closed__1;
lean_object* lean_string_length(lean_object*);
static lean_object* l_Lean_IR_LogEntry_fmt___closed__1;
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3(lean_object*, lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__8(lean_object*, lean_object*, size_t, size_t);
static lean_object* l_Lean_IR_declMapExt___elambda__4___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__6___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_IR_findEnvDecl___spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_contains___at_Lean_IR_containsDecl___spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_CompilerState_log___default;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_IR_findEnvDecl_x27___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_declMapExt___elambda__2___boxed(lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_declMapExt___elambda__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_declMapExt;
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__3(lean_object*, size_t, size_t, lean_object*);
lean_object* l_EStateM_pure___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_IR_CompilerState_log___default___closed__1;
uint32_t lean_uint32_of_nat(lean_object*);
static lean_object* l_Lean_IR_tracePrefixOptionName___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_getDecl_x27(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____closed__6;
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__5(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__6___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_findDecl(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_Name_instBEqName;
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_mkEntryArray___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_LogEntry_fmt___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_box(1);
x_8 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_unsigned_to_nat(2u);
x_10 = l_Lean_IR_formatDecl(x_6, x_9);
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = 1;
x_13 = x_2 + x_12;
x_2 = x_13;
x_4 = x_11;
goto _start;
}
else
{
return x_4;
}
}
}
static lean_object* _init_l_Lean_IR_LogEntry_fmt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("[");
return x_1;
}
}
static lean_object* _init_l_Lean_IR_LogEntry_fmt___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_LogEntry_fmt___closed__1;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_LogEntry_fmt___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_LogEntry_fmt___closed__2;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_LogEntry_fmt___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_LogEntry_fmt___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_LogEntry_fmt___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("]");
return x_1;
}
}
static lean_object* _init_l_Lean_IR_LogEntry_fmt___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_LogEntry_fmt___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_fmt(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = 1;
x_5 = l_Lean_Name_toString(x_2, x_4);
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l_Lean_IR_LogEntry_fmt___closed__4;
x_8 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = l_Lean_IR_LogEntry_fmt___closed__6;
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_IR_LogEntry_fmt___closed__3;
x_12 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = 0;
x_14 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
x_15 = lean_array_get_size(x_3);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_lt(x_16, x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_3);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_15, x_15);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_15);
lean_dec(x_3);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = 0;
x_24 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_25 = lean_box(0);
x_26 = l_Array_foldlMUnsafe_fold___at_Lean_IR_LogEntry_fmt___spec__1(x_3, x_23, x_24, x_25);
lean_dec(x_3);
x_27 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec(x_1);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_LogEntry_fmt___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_IR_LogEntry_fmt___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_IR_LogEntry_instToFormatLogEntry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_LogEntry_fmt), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_LogEntry_instToFormatLogEntry() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_LogEntry_instToFormatLogEntry___closed__1;
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_IR_Log_format___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_IR_Log_format___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlMUnsafe_fold___at_Lean_IR_Log_format___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Log_format___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_IR_Log_format___spec__1___closed__2;
x_8 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
x_13 = l_Lean_IR_LogEntry_fmt(x_6);
x_14 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
x_16 = 1;
x_17 = x_2 + x_16;
x_2 = x_17;
x_4 = x_15;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Log_format(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_lt(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_2, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_box(0);
return x_7;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_IR_Log_format___spec__1(x_1, x_8, x_9, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Log_format___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_IR_Log_format___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Log_format___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_Log_format(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_ir_log_to_string(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_IR_Log_format(x_1);
lean_dec(x_1);
x_3 = l_Std_Format_defWidth;
x_4 = lean_format_pretty(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_CompilerState_log___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_CompilerState_log___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_CompilerState_log___default___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_log(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_array_push(x_5, x_1);
lean_ctor_set(x_3, 1, x_6);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = lean_array_push(x_10, x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_log___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_log(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_tracePrefixOptionName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("trace");
return x_1;
}
}
static lean_object* _init_l_Lean_IR_tracePrefixOptionName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_tracePrefixOptionName___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_tracePrefixOptionName___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("compiler");
return x_1;
}
}
static lean_object* _init_l_Lean_IR_tracePrefixOptionName___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName___closed__2;
x_2 = l_Lean_IR_tracePrefixOptionName___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_tracePrefixOptionName___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ir");
return x_1;
}
}
static lean_object* _init_l_Lean_IR_tracePrefixOptionName___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName___closed__4;
x_2 = l_Lean_IR_tracePrefixOptionName___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_tracePrefixOptionName() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_tracePrefixOptionName___closed__6;
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_KVMap_findCore(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; uint8_t x_6; 
x_4 = l_Lean_IR_tracePrefixOptionName;
x_5 = 0;
x_6 = l_Lean_KVMap_getBool(x_1, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec(x_7);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; uint8_t x_11; 
lean_dec(x_7);
x_9 = l_Lean_IR_tracePrefixOptionName;
x_10 = 0;
x_11 = l_Lean_KVMap_getBool(x_1, x_9, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(x_4, x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_3);
x_10 = l_Lean_IR_log(x_9, x_4, x_5);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_IR_tracePrefixOptionName;
lean_inc(x_1);
x_6 = l_Lean_Name_append(x_5, x_1);
x_7 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_6, x_1, x_2, x_3, x_4);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_logDecls(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(x_4, x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_apply_1(x_1, x_3);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Lean_IR_log(x_10, x_4, x_5);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_IR_tracePrefixOptionName;
x_7 = l_Lean_Name_append(x_6, x_2);
x_8 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___rarg(x_1, x_7, x_3, x_4, x_5);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_logMessageIf___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_logMessageIf___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_IR_tracePrefixOptionName;
x_7 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___rarg(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessage(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_logMessage___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_logMessage___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_modifyEnv(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_apply_1(x_1, x_5);
lean_ctor_set(x_3, 0, x_6);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = lean_apply_1(x_1, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_modifyEnv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_modifyEnv(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_mkHashMap___at___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_mkEntryArray___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_mkEntryArray___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_IR_Decl_name(x_3);
x_6 = l_Lean_Name_instBEqName;
x_7 = l_Lean_instHashableName;
x_8 = l_Std_HashMap_insert___rarg(x_6, x_7, x_1, x_5, x_3);
x_1 = x_8;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_mkEntryArray___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_array_push(x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_mkEntryArray___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Std_AssocList_foldlM___at___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_mkEntryArray___spec__3(x_4, x_6);
x_8 = 1;
x_9 = x_2 + x_8;
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_mkEntryArray___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_mkEntryArray(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_mkEntryArray___closed__1;
x_3 = l_List_foldl___at___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_mkEntryArray___spec__2(x_2, x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = l_Lean_IR_CompilerState_log___default___closed__1;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_5, x_5);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_4);
x_10 = l_Lean_IR_CompilerState_log___default___closed__1;
return x_10;
}
else
{
size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_13 = l_Lean_IR_CompilerState_log___default___closed__1;
x_14 = l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_mkEntryArray___spec__4(x_4, x_11, x_12, x_13);
lean_dec(x_4);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_mkHashMap___at___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_mkEntryArray___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMap___at___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_mkEntryArray___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_mkEntryArray___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_mkEntryArray___spec__4(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Name_instBEqName;
x_8 = l_Lean_instHashableName;
x_9 = l_Std_PersistentHashMap_insert___rarg(x_7, x_8, x_6, x_2, x_3);
x_10 = 0;
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_10);
return x_1;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
x_13 = l_Lean_Name_instBEqName;
x_14 = l_Lean_instHashableName;
x_15 = l_Std_PersistentHashMap_insert___rarg(x_13, x_14, x_12, x_2, x_3);
x_16 = 0;
x_17 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_1);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = l_Lean_Name_instBEqName;
x_21 = l_Lean_instHashableName;
x_22 = l_Std_HashMap_insert___rarg(x_20, x_21, x_19, x_2, x_3);
x_23 = 1;
lean_ctor_set(x_1, 0, x_22);
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_23);
return x_1;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_1);
x_26 = l_Lean_Name_instBEqName;
x_27 = l_Lean_instHashableName;
x_28 = l_Std_HashMap_insert___rarg(x_26, x_27, x_24, x_2, x_3);
x_29 = 1;
x_30 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_25);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_IR_Decl_name(x_6);
x_8 = l_Lean_SMap_insert___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__1(x_4, x_7, x_6);
x_9 = 1;
x_10 = x_2 + x_9;
x_2 = x_10;
x_4 = x_8;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
x_10 = 1;
x_11 = x_2 + x_10;
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
x_2 = x_11;
goto _start;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_7, x_7);
if (x_13 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
x_2 = x_11;
goto _start;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_17 = l_Array_foldlMUnsafe_fold___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__3(x_6, x_15, x_16, x_4);
lean_dec(x_6);
x_2 = x_11;
x_4 = x_17;
goto _start;
}
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_3, x_3);
if (x_6 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__4(x_2, x_7, x_8, x_1);
lean_dec(x_2);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__5(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_2 == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 0;
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = 0;
x_8 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*2, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_name_eq(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = x_3 + x_10;
x_3 = x_11;
goto _start;
}
else
{
uint8_t x_13; 
x_13 = 1;
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__7___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_IR_CompilerState_log___default___closed__1;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__7___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__7___lambda__1), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__7___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 5);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__7___lambda__2___closed__1;
x_11 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_11, 0, x_5);
lean_closure_set(x_11, 1, x_10);
x_12 = l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(x_11, x_3);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_4);
lean_ctor_set(x_15, 2, x_6);
lean_ctor_set(x_15, 3, x_7);
lean_ctor_set(x_15, 4, x_8);
lean_ctor_set(x_15, 5, x_9);
x_16 = l_Lean_persistentEnvExtensionsRef;
x_17 = lean_st_ref_take(x_16, x_14);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_15);
x_20 = x_15;
x_21 = lean_array_push(x_18, x_20);
x_22 = lean_st_ref_set(x_16, x_21, x_19);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_15);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_15);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_27 = !lean_is_exclusive(x_12);
if (x_27 == 0)
{
return x_12;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_12, 0);
x_29 = lean_ctor_get(x_12, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_12);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
static lean_object* _init_l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid environment extension, '");
return x_1;
}
}
static lean_object* _init_l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__7___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' has already been used");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_persistentEnvExtensionsRef;
x_4 = lean_st_ref_get(x_3, x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_free_object(x_4);
lean_dec(x_6);
x_11 = lean_box(0);
x_12 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__7___lambda__2(x_1, x_11, x_7);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_8, x_8);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
lean_free_object(x_4);
lean_dec(x_6);
x_14 = lean_box(0);
x_15 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__7___lambda__2(x_1, x_14, x_7);
return x_15;
}
else
{
size_t x_16; size_t x_17; uint8_t x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_18 = l_Array_anyMUnsafe_any___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__8(x_1, x_6, x_16, x_17);
lean_dec(x_6);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_free_object(x_4);
x_19 = lean_box(0);
x_20 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__7___lambda__2(x_1, x_19, x_7);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = 1;
x_23 = l_Lean_Name_toString(x_21, x_22);
x_24 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__7___closed__1;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__7___closed__2;
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_28);
return x_4;
}
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_4, 0);
x_30 = lean_ctor_get(x_4, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_4);
x_31 = lean_array_get_size(x_29);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_nat_dec_lt(x_32, x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_31);
lean_dec(x_29);
x_34 = lean_box(0);
x_35 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__7___lambda__2(x_1, x_34, x_30);
return x_35;
}
else
{
uint8_t x_36; 
x_36 = lean_nat_dec_le(x_31, x_31);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_31);
lean_dec(x_29);
x_37 = lean_box(0);
x_38 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__7___lambda__2(x_1, x_37, x_30);
return x_38;
}
else
{
size_t x_39; size_t x_40; uint8_t x_41; 
x_39 = 0;
x_40 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_41 = l_Array_anyMUnsafe_any___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__8(x_1, x_29, x_39, x_40);
lean_dec(x_29);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_box(0);
x_43 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__7___lambda__2(x_1, x_42, x_30);
return x_43;
}
else
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
lean_dec(x_1);
x_45 = 1;
x_46 = l_Lean_Name_toString(x_44, x_45);
x_47 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__7___closed__1;
x_48 = lean_string_append(x_47, x_46);
lean_dec(x_46);
x_49 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__7___closed__2;
x_50 = lean_string_append(x_48, x_49);
x_51 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_30);
return x_52;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__6___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_apply_1(x_1, x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__6___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_2(x_8, x_6, x_3);
lean_ctor_set(x_2, 1, x_9);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_3);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_apply_2(x_13, x_11, x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__6___lambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_List_reverse___rarg(x_4);
x_6 = lean_apply_1(x_3, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__6___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("number of local entries: ");
return x_1;
}
}
static lean_object* _init_l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__6___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__6___lambda__4___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__6___lambda__4(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_List_lengthTRAux___rarg(x_2, x_3);
x_5 = l_Nat_repr(x_4);
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__6___lambda__4___closed__2;
x_8 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__6___lambda__4___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_box(0);
x_6 = l_Lean_IR_CompilerState_log___default___closed__1;
lean_inc(x_4);
x_7 = lean_apply_1(x_4, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_closure((void*)(l_EStateM_pure___rarg), 2, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__6___lambda__1___boxed), 5, 2);
lean_closure_set(x_10, 0, x_4);
lean_closure_set(x_10, 1, x_5);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__6___lambda__2), 3, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__6___lambda__3), 2, 1);
lean_closure_set(x_12, 0, x_1);
x_13 = l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__6___closed__1;
x_14 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_10);
lean_ctor_set(x_14, 3, x_11);
lean_ctor_set(x_14, 4, x_12);
lean_ctor_set(x_14, 5, x_13);
x_15 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__7(x_14, x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_IR_Decl_name(x_2);
x_4 = l_Lean_SMap_insert___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__1(x_1, x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____lambda__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____lambda__2___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____lambda__2___closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____lambda__2___closed__1;
x_3 = l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____lambda__2___closed__4;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____lambda__2___closed__5;
x_3 = l_Lean_mkStateFromImportedEntries___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__2(x_2, x_1);
x_4 = l_Lean_SMap_switch___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__5(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("IRDecls");
return x_1;
}
}
static lean_object* _init_l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____lambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____lambda__2), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_mkEntryArray), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____closed__2;
x_2 = l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____closed__3;
x_3 = l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____closed__4;
x_4 = l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____closed__5;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____closed__6;
x_3 = l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__6(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__4(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__8(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__7___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__7___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__6___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__6___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__6___lambda__4___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__6___lambda__4(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_declMapExt___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_declMapExt___elambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_CompilerState_log___default___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_declMapExt___elambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static uint32_t _init_l_Lean_IR_declMapExt___elambda__4___rarg___closed__1() {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint32_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_declMapExt___elambda__4___rarg___closed__2() {
_start:
{
lean_object* x_1; uint32_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_declMapExt___elambda__4___rarg___closed__1;
x_3 = l_Array_foldlMUnsafe_fold___at_Lean_IR_Log_format___spec__1___closed__1;
x_4 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint32(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_declMapExt___elambda__4___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_IR_declMapExt___elambda__4___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_declMapExt___elambda__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_IR_declMapExt___elambda__4___rarg), 1, 0);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_declMapExt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_declMapExt___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_IR_declMapExt___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_declMapExt___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_declMapExt___elambda__4___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_declMapExt___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_declMapExt___elambda__3___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_declMapExt___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_declMapExt___elambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_declMapExt___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_declMapExt___elambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_declMapExt___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_IR_declMapExt___closed__2;
x_2 = lean_box(0);
x_3 = l_Lean_IR_declMapExt___closed__3;
x_4 = l_Lean_IR_declMapExt___closed__4;
x_5 = l_Lean_IR_declMapExt___closed__5;
x_6 = l_Lean_IR_declMapExt___closed__6;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_declMapExt___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_declMapExt___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_declMapExt___elambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_declMapExt___elambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_declMapExt___elambda__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_declMapExt___elambda__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_declMapExt___elambda__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_declMapExt___elambda__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Name_instBEqName;
x_2 = l_Lean_instHashableName;
x_3 = l_Lean_SMap_instInhabitedSMap___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3___closed__2;
x_2 = l_Lean_instInhabitedPersistentEnvExtensionState___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Environment");
return x_1;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.EnvExtensionInterfaceUnsafe.getState");
return x_1;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3___closed__4;
x_2 = l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3___closed__5;
x_3 = lean_unsigned_to_nat(223u);
x_4 = lean_unsigned_to_nat(4u);
x_5 = l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_invalidExtMsg;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3___closed__3;
x_8 = l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3___closed__6;
x_9 = lean_panic_fn(x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_fget(x_4, x_3);
x_11 = x_10;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_getState___at_Lean_IR_findEnvDecl___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3(x_3, x_2);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getState___at_Lean_IR_findEnvDecl___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentEnvExtension_getState___at_Lean_IR_findEnvDecl___spec__2(x_1, x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_IR_findEnvDecl___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_name_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_IR_findEnvDecl___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = (size_t)x_5;
x_7 = lean_usize_modn(x_6, x_4);
lean_dec(x_4);
x_8 = lean_array_uget(x_3, x_7);
lean_dec(x_3);
x_9 = l_Std_AssocList_find_x3f___at_Lean_IR_findEnvDecl___spec__6(x_2, x_8);
lean_dec(x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at_Lean_IR_findEnvDecl___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_Name_instBEqName;
x_7 = l_Lean_instHashableName;
lean_inc(x_2);
x_8 = l_Std_PersistentHashMap_find_x3f___rarg(x_6, x_7, x_5, x_2);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = l_Std_HashMapImp_find_x3f___at_Lean_IR_findEnvDecl___spec__5(x_4, x_2);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_4);
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
return x_8;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l_Std_HashMapImp_find_x3f___at_Lean_IR_findEnvDecl___spec__5(x_13, x_2);
return x_14;
}
}
}
LEAN_EXPORT lean_object* lean_ir_find_env_decl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_IR_declMapExt;
x_4 = l_Lean_SimplePersistentEnvExtension_getState___at_Lean_IR_findEnvDecl___spec__1(x_3, x_1);
lean_dec(x_1);
x_5 = l_Lean_SMap_find_x3f___at_Lean_IR_findEnvDecl___spec__4(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_getState___at_Lean_IR_findEnvDecl___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentEnvExtension_getState___at_Lean_IR_findEnvDecl___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getState___at_Lean_IR_findEnvDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SimplePersistentEnvExtension_getState___at_Lean_IR_findEnvDecl___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_IR_findEnvDecl___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at_Lean_IR_findEnvDecl___spec__6(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ir_find_env_decl(x_4, x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_findDecl(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_AssocList_contains___at_Lean_IR_containsDecl___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_name_eq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_HashMapImp_contains___at_Lean_IR_containsDecl___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; size_t x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = (size_t)x_5;
x_7 = lean_usize_modn(x_6, x_4);
lean_dec(x_4);
x_8 = lean_array_uget(x_3, x_7);
lean_dec(x_3);
x_9 = l_Std_AssocList_contains___at_Lean_IR_containsDecl___spec__3(x_2, x_8);
lean_dec(x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_containsAtAux___at_Lean_IR_containsDecl___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_name_eq(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
uint8_t x_14; 
lean_dec(x_4);
x_14 = 1;
return x_14;
}
}
}
}
static size_t _init_l_Std_PersistentHashMap_containsAux___at_Lean_IR_containsDecl___spec__5___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = x_1 << x_2 % (sizeof(size_t) * 8);
return x_3;
}
}
static size_t _init_l_Std_PersistentHashMap_containsAux___at_Lean_IR_containsDecl___spec__5___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Std_PersistentHashMap_containsAux___at_Lean_IR_containsDecl___spec__5___closed__1;
x_3 = x_2 - x_1;
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_containsAux___at_Lean_IR_containsDecl___spec__5(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_containsAux___at_Lean_IR_containsDecl___spec__5___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = x_2 >> x_5 % (sizeof(size_t) * 8);
x_1 = x_13;
x_2 = x_14;
goto _start;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Std_PersistentHashMap_containsAtAux___at_Lean_IR_containsDecl___spec__6(x_17, x_18, lean_box(0), x_19, x_3);
lean_dec(x_18);
lean_dec(x_17);
return x_20;
}
}
}
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_contains___at_Lean_IR_containsDecl___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = (size_t)x_4;
x_6 = l_Std_PersistentHashMap_containsAux___at_Lean_IR_containsDecl___spec__5(x_3, x_5, x_2);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_SMap_contains___at_Lean_IR_containsDecl___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
lean_inc(x_2);
x_6 = l_Std_HashMapImp_contains___at_Lean_IR_containsDecl___spec__2(x_4, x_2);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = l_Std_PersistentHashMap_contains___at_Lean_IR_containsDecl___spec__4(x_5, x_2);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_5);
lean_dec(x_2);
x_8 = 1;
return x_8;
}
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Std_HashMapImp_contains___at_Lean_IR_containsDecl___spec__2(x_9, x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l_Lean_IR_declMapExt;
x_6 = l_Lean_SimplePersistentEnvExtension_getState___at_Lean_IR_findEnvDecl___spec__1(x_5, x_4);
lean_dec(x_4);
x_7 = l_Lean_SMap_contains___at_Lean_IR_containsDecl___spec__1(x_6, x_1);
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_contains___at_Lean_IR_containsDecl___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_AssocList_contains___at_Lean_IR_containsDecl___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_HashMapImp_contains___at_Lean_IR_containsDecl___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_HashMapImp_contains___at_Lean_IR_containsDecl___spec__2(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAtAux___at_Lean_IR_containsDecl___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Std_PersistentHashMap_containsAtAux___at_Lean_IR_containsDecl___spec__6(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAux___at_Lean_IR_containsDecl___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_containsAux___at_Lean_IR_containsDecl___spec__5(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_contains___at_Lean_IR_containsDecl___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_PersistentHashMap_contains___at_Lean_IR_containsDecl___spec__4(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_contains___at_Lean_IR_containsDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_SMap_contains___at_Lean_IR_containsDecl___spec__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_containsDecl(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_getDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown declaration '");
return x_1;
}
}
static lean_object* _init_l_Lean_IR_getDecl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_4 = l_Lean_IR_findDecl(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = 1;
x_9 = l_Lean_Name_toString(x_1, x_8);
x_10 = l_Lean_IR_getDecl___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_Lean_IR_getDecl___closed__2;
x_13 = lean_string_append(x_11, x_12);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_13);
return x_4;
}
else
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_dec(x_4);
x_15 = 1;
x_16 = l_Lean_Name_toString(x_1, x_15);
x_17 = l_Lean_IR_getDecl___closed__1;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_Lean_IR_getDecl___closed__2;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_14);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_4);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_4, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_5, 0);
lean_inc(x_24);
lean_dec(x_5);
lean_ctor_set(x_4, 0, x_24);
return x_4;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_4, 1);
lean_inc(x_25);
lean_dec(x_4);
x_26 = lean_ctor_get(x_5, 0);
lean_inc(x_26);
lean_dec(x_5);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_getDecl(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lean_ir_add_decl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_IR_declMapExt;
x_4 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___at_Lean_IR_getDecls___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentEnvExtension_getState___at_Lean_IR_findEnvDecl___spec__2(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecls(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_IR_declMapExt;
x_3 = l_Lean_SimplePersistentEnvExtension_getEntries___at_Lean_IR_getDecls___spec__1(x_2, x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___at_Lean_IR_getDecls___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SimplePersistentEnvExtension_getEntries___at_Lean_IR_getDecls___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getEnv___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getEnv(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_getEnv___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getEnv___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_getEnv(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lean_IR_declMapExt;
x_7 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_6, x_5, x_1);
lean_ctor_set(x_3, 0, x_7);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_12 = l_Lean_IR_declMapExt;
x_13 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_12, x_10, x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_addDecl(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_addDecls___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_2 == x_3;
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
lean_dec(x_4);
x_8 = lean_array_uget(x_1, x_2);
x_9 = l_Lean_IR_addDecl(x_8, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 1;
x_13 = x_2 + x_12;
x_2 = x_13;
x_4 = x_10;
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_4, x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = 0;
x_13 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_14 = lean_box(0);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_IR_addDecls___spec__1(x_1, x_12, x_13, x_14, x_2, x_3);
lean_dec(x_2);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_addDecls___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_IR_addDecls___spec__1(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_addDecls(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_IR_findEnvDecl_x27___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_5 < x_4;
if (x_7 == 0)
{
lean_inc(x_6);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_uget(x_3, x_5);
x_9 = l_Lean_IR_Decl_name(x_8);
x_10 = lean_name_eq(x_9, x_1);
lean_dec(x_9);
if (x_10 == 0)
{
size_t x_11; size_t x_12; 
lean_dec(x_8);
x_11 = 1;
x_12 = x_5 + x_11;
{
size_t _tmp_4 = x_12;
lean_object* _tmp_5 = x_2;
x_5 = _tmp_4;
x_6 = _tmp_5;
}
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_8);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_findEnvDecl_x27___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_findEnvDecl_x27___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_6 = 0;
x_7 = l_Lean_IR_findEnvDecl_x27___closed__1;
x_8 = l_Array_forInUnsafe_loop___at_Lean_IR_findEnvDecl_x27___spec__1(x_2, x_7, x_3, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_IR_declMapExt;
x_11 = l_Lean_SimplePersistentEnvExtension_getState___at_Lean_IR_findEnvDecl___spec__1(x_10, x_1);
x_12 = l_Lean_SMap_find_x3f___at_Lean_IR_findEnvDecl___spec__4(x_11, x_2);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_IR_findEnvDecl_x27___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_forInUnsafe_loop___at_Lean_IR_findEnvDecl_x27___spec__1(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_findEnvDecl_x27___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_findEnvDecl_x27(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = l_Lean_IR_findEnvDecl_x27(x_5, x_1, x_2);
lean_dec(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_findDecl_x27(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_IR_containsDecl_x27___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_IR_Decl_name(x_6);
lean_dec(x_6);
x_8 = lean_name_eq(x_7, x_1);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = x_3 + x_9;
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = l_Lean_IR_declMapExt;
x_10 = l_Lean_SimplePersistentEnvExtension_getState___at_Lean_IR_findEnvDecl___spec__1(x_9, x_8);
lean_dec(x_8);
x_11 = l_Lean_SMap_contains___at_Lean_IR_containsDecl___spec__1(x_10, x_1);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_5, x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_5);
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
x_16 = l_Lean_IR_declMapExt;
x_17 = l_Lean_SimplePersistentEnvExtension_getState___at_Lean_IR_findEnvDecl___spec__1(x_16, x_15);
lean_dec(x_15);
x_18 = l_Lean_SMap_contains___at_Lean_IR_containsDecl___spec__1(x_17, x_1);
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_4);
return x_20;
}
else
{
size_t x_21; size_t x_22; uint8_t x_23; 
x_21 = 0;
x_22 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_23 = l_Array_anyMUnsafe_any___at_Lean_IR_containsDecl_x27___spec__1(x_1, x_2, x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_4, 0);
lean_inc(x_24);
x_25 = l_Lean_IR_declMapExt;
x_26 = l_Lean_SimplePersistentEnvExtension_getState___at_Lean_IR_findEnvDecl___spec__1(x_25, x_24);
lean_dec(x_24);
x_27 = l_Lean_SMap_contains___at_Lean_IR_containsDecl___spec__1(x_26, x_1);
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_4);
return x_29;
}
else
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_1);
x_30 = 1;
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_4);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_IR_containsDecl_x27___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_IR_containsDecl_x27___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_containsDecl_x27(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
lean_inc(x_1);
x_5 = l_Lean_IR_findDecl_x27(x_1, x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = 1;
x_10 = l_Lean_Name_toString(x_1, x_9);
x_11 = l_Lean_IR_getDecl___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lean_IR_getDecl___closed__2;
x_14 = lean_string_append(x_12, x_13);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_14);
return x_5;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_dec(x_5);
x_16 = 1;
x_17 = l_Lean_Name_toString(x_1, x_16);
x_18 = l_Lean_IR_getDecl___closed__1;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = l_Lean_IR_getDecl___closed__2;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_15);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_5);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_5, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_6, 0);
lean_inc(x_25);
lean_dec(x_6);
lean_ctor_set(x_5, 0, x_25);
return x_5;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
lean_dec(x_5);
x_27 = lean_ctor_get(x_6, 0);
lean_inc(x_27);
lean_dec(x_6);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_getDecl_x27(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* lean_decl_get_sorry_dep(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_IR_declMapExt;
x_4 = l_Lean_SimplePersistentEnvExtension_getState___at_Lean_IR_findEnvDecl___spec__1(x_3, x_1);
lean_dec(x_1);
x_5 = l_Lean_SMap_find_x3f___at_Lean_IR_findEnvDecl___spec__4(x_4, x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 4);
lean_inc(x_8);
lean_dec(x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_7);
x_9 = lean_box(0);
return x_9;
}
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Environment(lean_object*);
lean_object* initialize_Lean_Compiler_IR_Basic(lean_object*);
lean_object* initialize_Lean_Compiler_IR_Format(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_CompilerM(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Format(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_LogEntry_fmt___closed__1 = _init_l_Lean_IR_LogEntry_fmt___closed__1();
lean_mark_persistent(l_Lean_IR_LogEntry_fmt___closed__1);
l_Lean_IR_LogEntry_fmt___closed__2 = _init_l_Lean_IR_LogEntry_fmt___closed__2();
lean_mark_persistent(l_Lean_IR_LogEntry_fmt___closed__2);
l_Lean_IR_LogEntry_fmt___closed__3 = _init_l_Lean_IR_LogEntry_fmt___closed__3();
lean_mark_persistent(l_Lean_IR_LogEntry_fmt___closed__3);
l_Lean_IR_LogEntry_fmt___closed__4 = _init_l_Lean_IR_LogEntry_fmt___closed__4();
lean_mark_persistent(l_Lean_IR_LogEntry_fmt___closed__4);
l_Lean_IR_LogEntry_fmt___closed__5 = _init_l_Lean_IR_LogEntry_fmt___closed__5();
lean_mark_persistent(l_Lean_IR_LogEntry_fmt___closed__5);
l_Lean_IR_LogEntry_fmt___closed__6 = _init_l_Lean_IR_LogEntry_fmt___closed__6();
lean_mark_persistent(l_Lean_IR_LogEntry_fmt___closed__6);
l_Lean_IR_LogEntry_instToFormatLogEntry___closed__1 = _init_l_Lean_IR_LogEntry_instToFormatLogEntry___closed__1();
lean_mark_persistent(l_Lean_IR_LogEntry_instToFormatLogEntry___closed__1);
l_Lean_IR_LogEntry_instToFormatLogEntry = _init_l_Lean_IR_LogEntry_instToFormatLogEntry();
lean_mark_persistent(l_Lean_IR_LogEntry_instToFormatLogEntry);
l_Array_foldlMUnsafe_fold___at_Lean_IR_Log_format___spec__1___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lean_IR_Log_format___spec__1___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_IR_Log_format___spec__1___closed__1);
l_Array_foldlMUnsafe_fold___at_Lean_IR_Log_format___spec__1___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Lean_IR_Log_format___spec__1___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_IR_Log_format___spec__1___closed__2);
l_Lean_IR_CompilerState_log___default___closed__1 = _init_l_Lean_IR_CompilerState_log___default___closed__1();
lean_mark_persistent(l_Lean_IR_CompilerState_log___default___closed__1);
l_Lean_IR_CompilerState_log___default = _init_l_Lean_IR_CompilerState_log___default();
lean_mark_persistent(l_Lean_IR_CompilerState_log___default);
l_Lean_IR_tracePrefixOptionName___closed__1 = _init_l_Lean_IR_tracePrefixOptionName___closed__1();
lean_mark_persistent(l_Lean_IR_tracePrefixOptionName___closed__1);
l_Lean_IR_tracePrefixOptionName___closed__2 = _init_l_Lean_IR_tracePrefixOptionName___closed__2();
lean_mark_persistent(l_Lean_IR_tracePrefixOptionName___closed__2);
l_Lean_IR_tracePrefixOptionName___closed__3 = _init_l_Lean_IR_tracePrefixOptionName___closed__3();
lean_mark_persistent(l_Lean_IR_tracePrefixOptionName___closed__3);
l_Lean_IR_tracePrefixOptionName___closed__4 = _init_l_Lean_IR_tracePrefixOptionName___closed__4();
lean_mark_persistent(l_Lean_IR_tracePrefixOptionName___closed__4);
l_Lean_IR_tracePrefixOptionName___closed__5 = _init_l_Lean_IR_tracePrefixOptionName___closed__5();
lean_mark_persistent(l_Lean_IR_tracePrefixOptionName___closed__5);
l_Lean_IR_tracePrefixOptionName___closed__6 = _init_l_Lean_IR_tracePrefixOptionName___closed__6();
lean_mark_persistent(l_Lean_IR_tracePrefixOptionName___closed__6);
l_Lean_IR_tracePrefixOptionName = _init_l_Lean_IR_tracePrefixOptionName();
lean_mark_persistent(l_Lean_IR_tracePrefixOptionName);
l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_mkEntryArray___closed__1 = _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_mkEntryArray___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_mkEntryArray___closed__1);
l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__7___lambda__2___closed__1 = _init_l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__7___lambda__2___closed__1();
lean_mark_persistent(l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__7___lambda__2___closed__1);
l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__7___closed__1 = _init_l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__7___closed__1();
lean_mark_persistent(l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__7___closed__1);
l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__7___closed__2 = _init_l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__7___closed__2();
lean_mark_persistent(l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__7___closed__2);
l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__6___lambda__4___closed__1 = _init_l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__6___lambda__4___closed__1();
lean_mark_persistent(l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__6___lambda__4___closed__1);
l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__6___lambda__4___closed__2 = _init_l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__6___lambda__4___closed__2();
lean_mark_persistent(l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__6___lambda__4___closed__2);
l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__6___closed__1 = _init_l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__6___closed__1();
lean_mark_persistent(l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____spec__6___closed__1);
l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____lambda__2___closed__1 = _init_l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____lambda__2___closed__1();
lean_mark_persistent(l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____lambda__2___closed__1);
l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____lambda__2___closed__2 = _init_l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____lambda__2___closed__2();
lean_mark_persistent(l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____lambda__2___closed__2);
l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____lambda__2___closed__3 = _init_l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____lambda__2___closed__3();
lean_mark_persistent(l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____lambda__2___closed__3);
l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____lambda__2___closed__4 = _init_l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____lambda__2___closed__4();
lean_mark_persistent(l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____lambda__2___closed__4);
l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____lambda__2___closed__5 = _init_l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____lambda__2___closed__5();
lean_mark_persistent(l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____lambda__2___closed__5);
l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____closed__1 = _init_l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____closed__1();
lean_mark_persistent(l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____closed__1);
l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____closed__2 = _init_l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____closed__2();
lean_mark_persistent(l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____closed__2);
l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____closed__3 = _init_l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____closed__3();
lean_mark_persistent(l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____closed__3);
l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____closed__4 = _init_l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____closed__4();
lean_mark_persistent(l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____closed__4);
l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____closed__5 = _init_l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____closed__5();
lean_mark_persistent(l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____closed__5);
l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____closed__6 = _init_l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____closed__6();
lean_mark_persistent(l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364____closed__6);
l_Lean_IR_declMapExt___elambda__4___rarg___closed__1 = _init_l_Lean_IR_declMapExt___elambda__4___rarg___closed__1();
l_Lean_IR_declMapExt___elambda__4___rarg___closed__2 = _init_l_Lean_IR_declMapExt___elambda__4___rarg___closed__2();
lean_mark_persistent(l_Lean_IR_declMapExt___elambda__4___rarg___closed__2);
l_Lean_IR_declMapExt___closed__1 = _init_l_Lean_IR_declMapExt___closed__1();
lean_mark_persistent(l_Lean_IR_declMapExt___closed__1);
l_Lean_IR_declMapExt___closed__2 = _init_l_Lean_IR_declMapExt___closed__2();
lean_mark_persistent(l_Lean_IR_declMapExt___closed__2);
l_Lean_IR_declMapExt___closed__3 = _init_l_Lean_IR_declMapExt___closed__3();
lean_mark_persistent(l_Lean_IR_declMapExt___closed__3);
l_Lean_IR_declMapExt___closed__4 = _init_l_Lean_IR_declMapExt___closed__4();
lean_mark_persistent(l_Lean_IR_declMapExt___closed__4);
l_Lean_IR_declMapExt___closed__5 = _init_l_Lean_IR_declMapExt___closed__5();
lean_mark_persistent(l_Lean_IR_declMapExt___closed__5);
l_Lean_IR_declMapExt___closed__6 = _init_l_Lean_IR_declMapExt___closed__6();
lean_mark_persistent(l_Lean_IR_declMapExt___closed__6);
l_Lean_IR_declMapExt___closed__7 = _init_l_Lean_IR_declMapExt___closed__7();
lean_mark_persistent(l_Lean_IR_declMapExt___closed__7);
res = l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_364_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_IR_declMapExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_IR_declMapExt);
lean_dec_ref(res);
l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3___closed__1 = _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3___closed__1();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3___closed__1);
l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3___closed__2 = _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3___closed__2();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3___closed__2);
l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3___closed__3 = _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3___closed__3();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3___closed__3);
l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3___closed__4 = _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3___closed__4();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3___closed__4);
l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3___closed__5 = _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3___closed__5();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3___closed__5);
l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3___closed__6 = _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3___closed__6();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_IR_findEnvDecl___spec__3___closed__6);
l_Std_PersistentHashMap_containsAux___at_Lean_IR_containsDecl___spec__5___closed__1 = _init_l_Std_PersistentHashMap_containsAux___at_Lean_IR_containsDecl___spec__5___closed__1();
l_Std_PersistentHashMap_containsAux___at_Lean_IR_containsDecl___spec__5___closed__2 = _init_l_Std_PersistentHashMap_containsAux___at_Lean_IR_containsDecl___spec__5___closed__2();
l_Lean_IR_getDecl___closed__1 = _init_l_Lean_IR_getDecl___closed__1();
lean_mark_persistent(l_Lean_IR_getDecl___closed__1);
l_Lean_IR_getDecl___closed__2 = _init_l_Lean_IR_getDecl___closed__2();
lean_mark_persistent(l_Lean_IR_getDecl___closed__2);
l_Lean_IR_findEnvDecl_x27___closed__1 = _init_l_Lean_IR_findEnvDecl_x27___closed__1();
lean_mark_persistent(l_Lean_IR_findEnvDecl_x27___closed__1);
l_Lean_IR_findEnvDecl_x27___closed__2 = _init_l_Lean_IR_findEnvDecl_x27___closed__2();
lean_mark_persistent(l_Lean_IR_findEnvDecl_x27___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
