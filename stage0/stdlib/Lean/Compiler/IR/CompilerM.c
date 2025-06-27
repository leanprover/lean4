// Lean compiler output
// Module: Lean.Compiler.IR.CompilerM
// Imports: Lean.Environment Lean.Compiler.IR.Basic Lean.Compiler.IR.Format
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
static lean_object* l_Lean_IR_findEnvDecl___closed__0;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_477__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_getDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_IR_findEnvDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0;
static lean_object* l_Lean_IR_LogEntry_fmt___closed__0;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_477__spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__2;
LEAN_EXPORT lean_object* lean_ir_find_env_decl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_IR_findEnvDecl_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_addDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_log___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_initFn___closed__2____x40_Lean_Compiler_IR_CompilerM___hyg_477_;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_fmt(lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_fmt___lam__0___boxed(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_addDecl(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Log_format_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_logDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_ir_log_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_log(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_IR_tracePrefixOptionName___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_addDecls(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_IR_findEnvDecl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__1____x40_Lean_Compiler_IR_CompilerM___hyg_477____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_modifyEnv(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_tracePrefixOptionName___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_initFn___closed__1____x40_Lean_Compiler_IR_CompilerM___hyg_477_;
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* l_Lean_Environment_addExtraName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__2____x40_Lean_Compiler_IR_CompilerM___hyg_477_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Log_format(lean_object*);
static lean_object* l_Lean_IR_initFn___closed__3____x40_Lean_Compiler_IR_CompilerM___hyg_477_;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_getDecl___redArg(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_addDecls___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_instToFormat;
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_modifyEnv___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_LogEntry_fmt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_getDecl_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_IR_findEnvDecl___closed__2;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_IR_containsDecl_x27_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_getDecl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lean_IR_getDecl___redArg___closed__1;
static lean_object* l_Lean_IR_LogEntry_instToFormat___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_addDecls_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_log___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_declMapExt;
LEAN_EXPORT lean_object* lean_decl_get_sorry_dep(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_IR_containsDecl_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Log_format_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_477__spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_getDecl_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_initFn___lam__0___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_477_;
lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l_Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_477_;
LEAN_EXPORT lean_object* l_Lean_IR_getEnv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_findEnvDecl_x27___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_getEnv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_formatDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_getDecl_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_logDecls(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_IR_findEnvDecl_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Log_format___boxed(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__3____x40_Lean_Compiler_IR_CompilerM___hyg_477_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_addDecls_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_477__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__0____x40_Lean_Compiler_IR_CompilerM___hyg_477_(lean_object*);
static lean_object* l_Lean_IR_initFn___lam__2___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_477_;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_477__spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__1;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_477__spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_IR_findEnvDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_initFn___lam__2___closed__1____x40_Lean_Compiler_IR_CompilerM___hyg_477_;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_logMessage(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_initFn___lam__1____x40_Lean_Compiler_IR_CompilerM___hyg_477_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qsort_sort___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_getDecls(lean_object*);
static lean_object* l_Lean_IR_findEnvDecl___closed__4;
LEAN_EXPORT uint8_t l_Lean_IR_LogEntry_fmt___lam__0(lean_object*);
lean_object* l_Array_binSearchAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_477__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_modifyEnv___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_IR_getDecl___redArg___closed__2;
static lean_object* l_Lean_IR_tracePrefixOptionName___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_LogEntry_fmt_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_addDecls_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_ir_add_decl(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_tracePrefixOptionName;
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_LogEntry_fmt___closed__2;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_getDecl_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
static lean_object* l_Lean_IR_getDecl___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Log_format_spec__0___closed__1;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_IR_findEnvDecl___closed__1;
lean_object* l_Lean_KVMap_findCore(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_477_(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_tracePrefixOptionName___closed__0;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Log_format_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_getEnv___redArg(lean_object*);
static lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0;
static lean_object* l_Lean_IR_LogEntry_fmt___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__2____x40_Lean_Compiler_IR_CompilerM___hyg_477____boxed(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_IR_LogEntry_fmt___closed__1;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_IR_findEnvDecl_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
static lean_object* l_Lean_IR_findEnvDecl___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_containsOnBranch_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_LogEntry_fmt___closed__4;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_LogEntry_fmt_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_box(1);
x_8 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_unsigned_to_nat(2u);
x_10 = l_Lean_IR_formatDecl(x_6, x_9);
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
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
LEAN_EXPORT uint8_t l_Lean_IR_LogEntry_fmt___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_LogEntry_fmt___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_LogEntry_fmt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_LogEntry_fmt___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_LogEntry_fmt___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_LogEntry_fmt___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_LogEntry_fmt___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_LogEntry_fmt___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_fmt(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_alloc_closure((void*)(l_Lean_IR_LogEntry_fmt___lam__0___boxed), 1, 0);
x_6 = lean_box(1);
x_7 = lean_unbox(x_6);
x_8 = l_Lean_Name_toString(x_3, x_7, x_5);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Lean_IR_LogEntry_fmt___closed__2;
x_11 = l_Lean_IR_LogEntry_fmt___closed__3;
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set(x_1, 0, x_11);
x_12 = l_Lean_IR_LogEntry_fmt___closed__4;
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_unbox(x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_17);
x_18 = lean_box(0);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_get_size(x_4);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_20);
lean_dec(x_4);
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_20, x_20);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_20);
lean_dec(x_4);
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_18);
return x_24;
}
else
{
size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; 
x_25 = 0;
x_26 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_27 = l_Array_foldlMUnsafe_fold___at___Lean_IR_LogEntry_fmt_spec__0(x_4, x_25, x_26, x_18);
lean_dec(x_4);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_16);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_29 = lean_ctor_get(x_1, 0);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_1);
x_31 = lean_alloc_closure((void*)(l_Lean_IR_LogEntry_fmt___lam__0___boxed), 1, 0);
x_32 = lean_box(1);
x_33 = lean_unbox(x_32);
x_34 = l_Lean_Name_toString(x_29, x_33, x_31);
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = l_Lean_IR_LogEntry_fmt___closed__2;
x_37 = l_Lean_IR_LogEntry_fmt___closed__3;
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
x_39 = l_Lean_IR_LogEntry_fmt___closed__4;
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_43, 0, x_41);
x_44 = lean_unbox(x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_44);
x_45 = lean_box(0);
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_array_get_size(x_30);
x_48 = lean_nat_dec_lt(x_46, x_47);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_47);
lean_dec(x_30);
x_49 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_49, 0, x_43);
lean_ctor_set(x_49, 1, x_45);
return x_49;
}
else
{
uint8_t x_50; 
x_50 = lean_nat_dec_le(x_47, x_47);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_47);
lean_dec(x_30);
x_51 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_51, 0, x_43);
lean_ctor_set(x_51, 1, x_45);
return x_51;
}
else
{
size_t x_52; size_t x_53; lean_object* x_54; lean_object* x_55; 
x_52 = 0;
x_53 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_54 = l_Array_foldlMUnsafe_fold___at___Lean_IR_LogEntry_fmt_spec__0(x_30, x_52, x_53, x_45);
lean_dec(x_30);
x_55 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_55, 0, x_43);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
else
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_1, 0);
lean_inc(x_56);
lean_dec(x_1);
return x_56;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_LogEntry_fmt_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_IR_LogEntry_fmt_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_fmt___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_LogEntry_fmt___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_LogEntry_instToFormat___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_LogEntry_fmt), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_LogEntry_instToFormat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_LogEntry_instToFormat___closed__0;
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___Lean_IR_Log_format_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___Lean_IR_Log_format_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Log_format_spec__0___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Log_format_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Log_format_spec__0___closed__1;
x_8 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
x_13 = l_Lean_IR_LogEntry_fmt(x_6);
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_box(0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Log_format_spec__0(x_1, x_7, x_8, x_2);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Log_format_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Log_format_spec__0(x_1, x_5, x_6, x_4);
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_IR_Log_format(x_1);
lean_dec(x_1);
x_3 = lean_unsigned_to_nat(120u);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_format_pretty(x_2, x_3, x_4, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_log___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_box(0);
x_6 = lean_array_push(x_4, x_1);
lean_ctor_set(x_2, 1, x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = lean_array_push(x_9, x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_log(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_log___redArg(x_1, x_3);
return x_4;
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
static lean_object* _init_l_Lean_IR_tracePrefixOptionName___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trace", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_tracePrefixOptionName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("compiler", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_tracePrefixOptionName___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ir", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_tracePrefixOptionName___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_IR_tracePrefixOptionName___closed__2;
x_2 = l_Lean_IR_tracePrefixOptionName___closed__1;
x_3 = l_Lean_IR_tracePrefixOptionName___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_tracePrefixOptionName() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_tracePrefixOptionName___closed__3;
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_KVMap_findCore(x_1, x_2);
if (lean_obj_tag(x_8) == 0)
{
goto block_7;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 1)
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_9, 0);
lean_dec(x_9);
return x_10;
}
else
{
lean_dec(x_9);
goto block_7;
}
}
block_7:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; 
x_3 = l_Lean_IR_tracePrefixOptionName;
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
x_6 = l_Lean_KVMap_getBool(x_1, x_3, x_5);
return x_6;
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
x_10 = l_Lean_IR_log___redArg(x_9, x_5);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_11 = l_Lean_IR_log___redArg(x_10, x_5);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_IR_tracePrefixOptionName;
x_7 = l_Lean_Name_append(x_6, x_2);
x_8 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(x_1, x_7, x_3, x_4, x_5);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_IR_tracePrefixOptionName;
x_8 = l_Lean_Name_append(x_7, x_3);
x_9 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(x_2, x_8, x_4, x_5, x_6);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_logMessageIf___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_logMessageIf(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_IR_tracePrefixOptionName;
x_6 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(x_1, x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessage(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_IR_tracePrefixOptionName;
x_7 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(x_2, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_logMessage___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_logMessage(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_modifyEnv___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 0, x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = lean_apply_1(x_1, x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
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
x_6 = lean_box(0);
x_7 = lean_apply_1(x_1, x_5);
lean_ctor_set(x_3, 0, x_7);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
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
x_11 = lean_box(0);
x_12 = lean_apply_1(x_1, x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
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
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 0);
x_3 = x_7;
goto block_6;
block_6:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_Name_quickLt(x_3, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_13; 
x_5 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0;
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
lean_dec(x_2);
x_13 = lean_nat_dec_le(x_3, x_7);
if (x_13 == 0)
{
lean_inc(x_7);
x_8 = x_7;
goto block_12;
}
else
{
x_8 = x_3;
goto block_12;
}
block_12:
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_8, x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_inc(x_8);
x_10 = l_Array_qsort_sort___redArg(x_5, x_1, x_8, x_8);
lean_dec(x_8);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = l_Array_qsort_sort___redArg(x_5, x_1, x_8, x_7);
lean_dec(x_7);
return x_11;
}
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___boxed), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_2);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_4, x_7);
lean_dec(x_4);
x_9 = lean_nat_dec_le(x_3, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_2);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0;
x_12 = lean_box(0);
x_13 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__1;
x_14 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_12);
lean_ctor_set(x_14, 3, x_13);
x_15 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0;
x_16 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__2;
x_17 = l_Array_binSearchAux___redArg(x_15, x_16, x_1, x_14, x_3, x_8);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_477__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_array_push(x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_477__spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 0);
x_3 = x_7;
goto block_6;
block_6:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_Name_quickLt(x_3, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_477__spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_alloc_closure((void*)(l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_477__spec__1___redArg___lam__0___boxed), 2, 0);
lean_inc(x_2);
x_6 = l_Array_qpartition___redArg(x_1, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_nat_dec_le(x_3, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_477__spec__1___redArg(x_8, x_2, x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_477__spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_477__spec__1___redArg(x_2, x_3, x_4);
return x_8;
}
}
static lean_object* _init_l_Lean_IR_initFn___lam__0___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_477_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__0____x40_Lean_Compiler_IR_CompilerM___hyg_477_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_IR_initFn___lam__0___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_477_;
x_4 = l_List_foldl___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_477__spec__0(x_3, x_1);
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_eq(x_5, x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_14; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_5, x_7);
lean_dec(x_5);
x_14 = lean_nat_dec_le(x_2, x_8);
if (x_14 == 0)
{
lean_inc(x_8);
x_9 = x_8;
goto block_13;
}
else
{
x_9 = x_2;
goto block_13;
}
block_13:
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_9, x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_inc(x_9);
x_11 = l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_477__spec__1___redArg(x_4, x_9, x_9);
lean_dec(x_9);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_477__spec__1___redArg(x_4, x_9, x_8);
lean_dec(x_8);
return x_12;
}
}
}
else
{
lean_dec(x_5);
return x_4;
}
}
}
LEAN_EXPORT uint8_t l_Lean_IR_initFn___lam__1____x40_Lean_Compiler_IR_CompilerM___hyg_477_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_10; 
x_10 = lean_ctor_get(x_2, 0);
x_3 = x_10;
goto block_9;
block_9:
{
uint8_t x_4; 
x_4 = l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_containsOnBranch_spec__0_spec__0___redArg(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(1);
x_6 = lean_unbox(x_5);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
return x_8;
}
}
}
}
static lean_object* _init_l_Lean_IR_initFn___lam__2___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_477_() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_IR_initFn___lam__2___closed__1____x40_Lean_Compiler_IR_CompilerM___hyg_477_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_initFn___lam__2___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_477_;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__2____x40_Lean_Compiler_IR_CompilerM___hyg_477_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_initFn___lam__2___closed__1____x40_Lean_Compiler_IR_CompilerM___hyg_477_;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__3____x40_Lean_Compiler_IR_CompilerM___hyg_477_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0___redArg(x_1, x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_477_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_initFn___closed__1____x40_Lean_Compiler_IR_CompilerM___hyg_477_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("IR", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_initFn___closed__2____x40_Lean_Compiler_IR_CompilerM___hyg_477_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("declMapExt", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_initFn___closed__3____x40_Lean_Compiler_IR_CompilerM___hyg_477_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_IR_initFn___closed__2____x40_Lean_Compiler_IR_CompilerM___hyg_477_;
x_2 = l_Lean_IR_initFn___closed__1____x40_Lean_Compiler_IR_CompilerM___hyg_477_;
x_3 = l_Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_477_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_477_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_initFn___lam__0____x40_Lean_Compiler_IR_CompilerM___hyg_477_), 1, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_IR_initFn___lam__1____x40_Lean_Compiler_IR_CompilerM___hyg_477____boxed), 2, 0);
x_4 = lean_alloc_closure((void*)(l_Lean_IR_initFn___lam__2____x40_Lean_Compiler_IR_CompilerM___hyg_477____boxed), 1, 0);
x_5 = lean_alloc_closure((void*)(l_Lean_IR_initFn___lam__3____x40_Lean_Compiler_IR_CompilerM___hyg_477_), 2, 0);
x_6 = l_Lean_IR_initFn___closed__3____x40_Lean_Compiler_IR_CompilerM___hyg_477_;
x_7 = lean_box(0);
x_8 = lean_box(0);
lean_inc(x_5);
x_9 = lean_alloc_closure((void*)(l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed), 7, 4);
lean_closure_set(x_9, 0, lean_box(0));
lean_closure_set(x_9, 1, lean_box(0));
lean_closure_set(x_9, 2, x_3);
lean_closure_set(x_9, 3, x_5);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 2, x_4);
lean_ctor_set(x_11, 3, x_2);
lean_ctor_set(x_11, 4, x_7);
lean_ctor_set(x_11, 5, x_10);
x_12 = lean_unbox(x_8);
lean_ctor_set_uint8(x_11, sizeof(void*)*6, x_12);
x_13 = l_Lean_registerSimplePersistentEnvExtension___redArg(x_11, x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_477__spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_477__spec__1___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_477__spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_477__spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_477__spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_477__spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__1____x40_Lean_Compiler_IR_CompilerM___hyg_477____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_initFn___lam__1____x40_Lean_Compiler_IR_CompilerM___hyg_477_(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__2____x40_Lean_Compiler_IR_CompilerM___hyg_477____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_initFn___lam__2____x40_Lean_Compiler_IR_CompilerM___hyg_477_(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_IR_findEnvDecl_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_nat_add(x_3, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_shiftr(x_5, x_6);
lean_dec(x_5);
x_8 = lean_array_fget(x_1, x_7);
x_9 = l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_477__spec__1___redArg___lam__0(x_8, x_2);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_4);
x_10 = l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_477__spec__1___redArg___lam__0(x_2, x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_8);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
lean_dec(x_8);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_7, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_nat_sub(x_7, x_6);
lean_dec(x_7);
x_15 = lean_nat_dec_lt(x_14, x_3);
if (x_15 == 0)
{
x_4 = x_14;
goto _start;
}
else
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_3);
x_17 = lean_box(0);
return x_17;
}
}
else
{
lean_object* x_18; 
lean_dec(x_7);
lean_dec(x_3);
x_18 = lean_box(0);
return x_18;
}
}
}
else
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_8);
lean_dec(x_3);
x_19 = lean_nat_add(x_7, x_6);
lean_dec(x_7);
x_20 = lean_nat_dec_le(x_19, x_4);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_19);
lean_dec(x_4);
x_21 = lean_box(0);
return x_21;
}
else
{
x_3 = x_19;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_IR_findEnvDecl_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_binSearchAux___at___Lean_IR_findEnvDecl_spec__0___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_findEnvDecl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_findEnvDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_hash___override___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_findEnvDecl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_findEnvDecl___closed__1;
x_2 = l_Lean_IR_findEnvDecl___closed__0;
x_3 = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_findEnvDecl___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_declMapExt;
return x_1;
}
}
static lean_object* _init_l_Lean_IR_findEnvDecl___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_findEnvDecl___closed__2;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_ir_find_env_decl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_IR_findEnvDecl___closed__2;
x_4 = l_Lean_Environment_getModuleIdxFor_x3f(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l_Lean_IR_findEnvDecl___closed__3;
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
lean_dec(x_6);
x_8 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_3, x_5, x_1, x_7);
x_9 = l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0___redArg(x_8, x_2);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec(x_4);
x_11 = l_Lean_IR_findEnvDecl___closed__4;
x_12 = l_Lean_IR_findEnvDecl___closed__3;
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
x_15 = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(x_11, x_12, x_1, x_10, x_14);
lean_dec(x_10);
lean_dec(x_1);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_get_size(x_15);
x_18 = lean_nat_dec_lt(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_2);
x_19 = lean_box(0);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_17, x_20);
lean_dec(x_17);
x_22 = lean_nat_dec_le(x_16, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_2);
x_23 = lean_box(0);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0;
x_25 = lean_box(0);
x_26 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__1;
x_27 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_25);
lean_ctor_set(x_27, 3, x_26);
x_28 = l_Array_binSearchAux___at___Lean_IR_findEnvDecl_spec__0___redArg(x_15, x_27, x_16, x_21);
lean_dec(x_27);
lean_dec(x_15);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_IR_findEnvDecl_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___at___Lean_IR_findEnvDecl_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_IR_findEnvDecl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_binSearchAux___at___Lean_IR_findEnvDecl_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ir_find_env_decl(x_3, x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_findDecl___redArg(x_1, x_3);
return x_4;
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
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_IR_findDecl___redArg(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
x_7 = lean_box(0);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8_t x_11; 
lean_dec(x_4);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_3, 0);
lean_dec(x_12);
x_13 = lean_box(1);
lean_ctor_set(x_3, 0, x_13);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_box(1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_containsDecl___redArg(x_1, x_3);
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
static lean_object* _init_l_Lean_IR_getDecl___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_LogEntry_fmt___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_getDecl___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown declaration '", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_getDecl___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
lean_inc(x_1);
x_3 = l_Lean_IR_findDecl___redArg(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
x_7 = l_Lean_IR_getDecl___redArg___closed__0;
x_8 = l_Lean_IR_getDecl___redArg___closed__1;
x_9 = lean_box(1);
x_10 = lean_unbox(x_9);
x_11 = l_Lean_Name_toString(x_1, x_10, x_7);
x_12 = lean_string_append(x_8, x_11);
lean_dec(x_11);
x_13 = l_Lean_IR_getDecl___redArg___closed__2;
x_14 = lean_string_append(x_12, x_13);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_14);
return x_3;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_dec(x_3);
x_16 = l_Lean_IR_getDecl___redArg___closed__0;
x_17 = l_Lean_IR_getDecl___redArg___closed__1;
x_18 = lean_box(1);
x_19 = lean_unbox(x_18);
x_20 = l_Lean_Name_toString(x_1, x_19, x_16);
x_21 = lean_string_append(x_17, x_20);
lean_dec(x_20);
x_22 = l_Lean_IR_getDecl___redArg___closed__2;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_15);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_3);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_3, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_4, 0);
lean_inc(x_27);
lean_dec(x_4);
lean_ctor_set(x_3, 0, x_27);
return x_3;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_3, 1);
lean_inc(x_28);
lean_dec(x_3);
x_29 = lean_ctor_get(x_4, 0);
lean_inc(x_29);
lean_dec(x_4);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_getDecl___redArg(x_1, x_3);
return x_4;
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
lean_object* x_3; lean_object* x_4; lean_object* x_8; 
x_3 = l_Lean_IR_findEnvDecl___closed__3;
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_4 = x_8;
goto block_7;
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Environment_addExtraName(x_1, x_4);
x_6 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_3, x_5, x_2);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecls(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_IR_findEnvDecl___closed__2;
x_3 = l_Lean_IR_findEnvDecl___closed__3;
x_4 = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getEnv___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_IR_getEnv(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_getEnv___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getEnv___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_getEnv(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_14; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_5 = x_2;
} else {
 lean_dec_ref(x_2);
 x_5 = lean_box(0);
}
x_6 = lean_box(0);
x_7 = l_Lean_IR_findEnvDecl___closed__3;
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_8 = x_14;
goto block_13;
block_13:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Lean_Environment_addExtraName(x_3, x_8);
x_10 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_7, x_9, x_1);
if (lean_is_scalar(x_5)) {
 x_11 = lean_alloc_ctor(0, 2, 0);
} else {
 x_11 = x_5;
}
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_addDecl___redArg(x_1, x_3);
return x_4;
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_addDecls_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
lean_dec(x_4);
x_7 = lean_array_uget(x_1, x_2);
x_8 = l_Lean_IR_addDecl___redArg(x_7, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_9;
x_5 = x_10;
goto _start;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_addDecls_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_IR_addDecls_spec__0___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_1);
x_6 = lean_box(0);
x_7 = lean_nat_dec_lt(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_3);
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
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_13 = l_Array_foldlMUnsafe_fold___at___Lean_IR_addDecls_spec__0___redArg(x_1, x_11, x_12, x_6, x_3);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_addDecls_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_foldlMUnsafe_fold___at___Lean_IR_addDecls_spec__0___redArg(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_addDecls_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_IR_addDecls_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
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
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_IR_findEnvDecl_x27_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_6, x_5);
if (x_8 == 0)
{
lean_dec(x_2);
lean_inc(x_7);
return x_7;
}
else
{
lean_object* x_9; uint8_t x_10; lean_object* x_18; uint8_t x_19; 
x_9 = lean_array_uget(x_4, x_6);
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
x_19 = lean_name_eq(x_18, x_3);
lean_dec(x_18);
x_10 = x_19;
goto block_17;
block_17:
{
if (x_10 == 0)
{
size_t x_11; size_t x_12; 
lean_dec(x_9);
x_11 = 1;
x_12 = lean_usize_add(x_6, x_11);
{
size_t _tmp_5 = x_12;
lean_object* _tmp_6 = x_1;
x_6 = _tmp_5;
x_7 = _tmp_6;
}
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_9);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_2);
return x_16;
}
}
}
}
}
static lean_object* _init_l_Lean_IR_findEnvDecl_x27___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_box(0);
x_5 = l_Lean_IR_findEnvDecl_x27___closed__0;
x_6 = lean_array_size(x_3);
x_7 = 0;
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lean_IR_findEnvDecl_x27_spec__0(x_5, x_4, x_2, x_3, x_6, x_7, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ir_find_env_decl(x_1, x_2);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ir_find_env_decl(x_1, x_2);
return x_12;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_IR_findEnvDecl_x27_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_IR_findEnvDecl_x27_spec__0(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_findEnvDecl_x27(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l_Lean_IR_findEnvDecl_x27(x_4, x_1, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_findDecl_x27___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_findDecl_x27___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
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
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_IR_containsDecl_x27_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_6 = lean_box(1);
x_13 = lean_array_uget(x_2, x_3);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_name_eq(x_14, x_1);
lean_dec(x_14);
x_7 = x_15;
goto block_12;
block_12:
{
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = lean_unbox(x_6);
return x_11;
}
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_box(0);
x_17 = lean_unbox(x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_5);
x_7 = l_Lean_IR_containsDecl___redArg(x_1, x_3);
return x_7;
}
else
{
if (x_6 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = l_Lean_IR_containsDecl___redArg(x_1, x_3);
return x_8;
}
else
{
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_11 = l_Array_anyMUnsafe_any___at___Lean_IR_containsDecl_x27_spec__0(x_1, x_2, x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_IR_containsDecl___redArg(x_1, x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = lean_box(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
return x_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_containsDecl_x27___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_IR_containsDecl_x27_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Lean_IR_containsDecl_x27_spec__0(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_containsDecl_x27___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
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
LEAN_EXPORT lean_object* l_Lean_IR_getDecl_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_4 = l_Lean_IR_findDecl_x27___redArg(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = l_Lean_IR_getDecl___redArg___closed__0;
x_9 = l_Lean_IR_getDecl___redArg___closed__1;
x_10 = lean_box(1);
x_11 = lean_unbox(x_10);
x_12 = l_Lean_Name_toString(x_1, x_11, x_8);
x_13 = lean_string_append(x_9, x_12);
lean_dec(x_12);
x_14 = l_Lean_IR_getDecl___redArg___closed__2;
x_15 = lean_string_append(x_13, x_14);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_15);
return x_4;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_dec(x_4);
x_17 = l_Lean_IR_getDecl___redArg___closed__0;
x_18 = l_Lean_IR_getDecl___redArg___closed__1;
x_19 = lean_box(1);
x_20 = lean_unbox(x_19);
x_21 = l_Lean_Name_toString(x_1, x_20, x_17);
x_22 = lean_string_append(x_18, x_21);
lean_dec(x_21);
x_23 = l_Lean_IR_getDecl___redArg___closed__2;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_16);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_4);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_4, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_5, 0);
lean_inc(x_28);
lean_dec(x_5);
lean_ctor_set(x_4, 0, x_28);
return x_4;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_4, 1);
lean_inc(x_29);
lean_dec(x_4);
x_30 = lean_ctor_get(x_5, 0);
lean_inc(x_30);
lean_dec(x_5);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_getDecl_x27___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl_x27___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_getDecl_x27___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
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
lean_object* x_3; 
x_3 = lean_ir_find_env_decl(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_5);
x_7 = lean_box(0);
return x_7;
}
}
}
}
lean_object* initialize_Lean_Environment(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_Format(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Environment(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Format(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_LogEntry_fmt___closed__0 = _init_l_Lean_IR_LogEntry_fmt___closed__0();
lean_mark_persistent(l_Lean_IR_LogEntry_fmt___closed__0);
l_Lean_IR_LogEntry_fmt___closed__1 = _init_l_Lean_IR_LogEntry_fmt___closed__1();
lean_mark_persistent(l_Lean_IR_LogEntry_fmt___closed__1);
l_Lean_IR_LogEntry_fmt___closed__2 = _init_l_Lean_IR_LogEntry_fmt___closed__2();
lean_mark_persistent(l_Lean_IR_LogEntry_fmt___closed__2);
l_Lean_IR_LogEntry_fmt___closed__3 = _init_l_Lean_IR_LogEntry_fmt___closed__3();
lean_mark_persistent(l_Lean_IR_LogEntry_fmt___closed__3);
l_Lean_IR_LogEntry_fmt___closed__4 = _init_l_Lean_IR_LogEntry_fmt___closed__4();
lean_mark_persistent(l_Lean_IR_LogEntry_fmt___closed__4);
l_Lean_IR_LogEntry_instToFormat___closed__0 = _init_l_Lean_IR_LogEntry_instToFormat___closed__0();
lean_mark_persistent(l_Lean_IR_LogEntry_instToFormat___closed__0);
l_Lean_IR_LogEntry_instToFormat = _init_l_Lean_IR_LogEntry_instToFormat();
lean_mark_persistent(l_Lean_IR_LogEntry_instToFormat);
l_Array_foldlMUnsafe_fold___at___Lean_IR_Log_format_spec__0___closed__0 = _init_l_Array_foldlMUnsafe_fold___at___Lean_IR_Log_format_spec__0___closed__0();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___Lean_IR_Log_format_spec__0___closed__0);
l_Array_foldlMUnsafe_fold___at___Lean_IR_Log_format_spec__0___closed__1 = _init_l_Array_foldlMUnsafe_fold___at___Lean_IR_Log_format_spec__0___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___Lean_IR_Log_format_spec__0___closed__1);
l_Lean_IR_tracePrefixOptionName___closed__0 = _init_l_Lean_IR_tracePrefixOptionName___closed__0();
lean_mark_persistent(l_Lean_IR_tracePrefixOptionName___closed__0);
l_Lean_IR_tracePrefixOptionName___closed__1 = _init_l_Lean_IR_tracePrefixOptionName___closed__1();
lean_mark_persistent(l_Lean_IR_tracePrefixOptionName___closed__1);
l_Lean_IR_tracePrefixOptionName___closed__2 = _init_l_Lean_IR_tracePrefixOptionName___closed__2();
lean_mark_persistent(l_Lean_IR_tracePrefixOptionName___closed__2);
l_Lean_IR_tracePrefixOptionName___closed__3 = _init_l_Lean_IR_tracePrefixOptionName___closed__3();
lean_mark_persistent(l_Lean_IR_tracePrefixOptionName___closed__3);
l_Lean_IR_tracePrefixOptionName = _init_l_Lean_IR_tracePrefixOptionName();
lean_mark_persistent(l_Lean_IR_tracePrefixOptionName);
l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0 = _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0();
lean_mark_persistent(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0);
l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0 = _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0();
lean_mark_persistent(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0);
l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__1 = _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__1);
l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__2 = _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__2();
lean_mark_persistent(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__2);
l_Lean_IR_initFn___lam__0___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_477_ = _init_l_Lean_IR_initFn___lam__0___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_477_();
lean_mark_persistent(l_Lean_IR_initFn___lam__0___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_477_);
l_Lean_IR_initFn___lam__2___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_477_ = _init_l_Lean_IR_initFn___lam__2___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_477_();
lean_mark_persistent(l_Lean_IR_initFn___lam__2___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_477_);
l_Lean_IR_initFn___lam__2___closed__1____x40_Lean_Compiler_IR_CompilerM___hyg_477_ = _init_l_Lean_IR_initFn___lam__2___closed__1____x40_Lean_Compiler_IR_CompilerM___hyg_477_();
lean_mark_persistent(l_Lean_IR_initFn___lam__2___closed__1____x40_Lean_Compiler_IR_CompilerM___hyg_477_);
l_Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_477_ = _init_l_Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_477_();
lean_mark_persistent(l_Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_477_);
l_Lean_IR_initFn___closed__1____x40_Lean_Compiler_IR_CompilerM___hyg_477_ = _init_l_Lean_IR_initFn___closed__1____x40_Lean_Compiler_IR_CompilerM___hyg_477_();
lean_mark_persistent(l_Lean_IR_initFn___closed__1____x40_Lean_Compiler_IR_CompilerM___hyg_477_);
l_Lean_IR_initFn___closed__2____x40_Lean_Compiler_IR_CompilerM___hyg_477_ = _init_l_Lean_IR_initFn___closed__2____x40_Lean_Compiler_IR_CompilerM___hyg_477_();
lean_mark_persistent(l_Lean_IR_initFn___closed__2____x40_Lean_Compiler_IR_CompilerM___hyg_477_);
l_Lean_IR_initFn___closed__3____x40_Lean_Compiler_IR_CompilerM___hyg_477_ = _init_l_Lean_IR_initFn___closed__3____x40_Lean_Compiler_IR_CompilerM___hyg_477_();
lean_mark_persistent(l_Lean_IR_initFn___closed__3____x40_Lean_Compiler_IR_CompilerM___hyg_477_);
if (builtin) {res = l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_477_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_IR_declMapExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_IR_declMapExt);
lean_dec_ref(res);
}l_Lean_IR_findEnvDecl___closed__0 = _init_l_Lean_IR_findEnvDecl___closed__0();
lean_mark_persistent(l_Lean_IR_findEnvDecl___closed__0);
l_Lean_IR_findEnvDecl___closed__1 = _init_l_Lean_IR_findEnvDecl___closed__1();
lean_mark_persistent(l_Lean_IR_findEnvDecl___closed__1);
l_Lean_IR_findEnvDecl___closed__2 = _init_l_Lean_IR_findEnvDecl___closed__2();
lean_mark_persistent(l_Lean_IR_findEnvDecl___closed__2);
l_Lean_IR_findEnvDecl___closed__3 = _init_l_Lean_IR_findEnvDecl___closed__3();
lean_mark_persistent(l_Lean_IR_findEnvDecl___closed__3);
l_Lean_IR_findEnvDecl___closed__4 = _init_l_Lean_IR_findEnvDecl___closed__4();
lean_mark_persistent(l_Lean_IR_findEnvDecl___closed__4);
l_Lean_IR_getDecl___redArg___closed__0 = _init_l_Lean_IR_getDecl___redArg___closed__0();
lean_mark_persistent(l_Lean_IR_getDecl___redArg___closed__0);
l_Lean_IR_getDecl___redArg___closed__1 = _init_l_Lean_IR_getDecl___redArg___closed__1();
lean_mark_persistent(l_Lean_IR_getDecl___redArg___closed__1);
l_Lean_IR_getDecl___redArg___closed__2 = _init_l_Lean_IR_getDecl___redArg___closed__2();
lean_mark_persistent(l_Lean_IR_getDecl___redArg___closed__2);
l_Lean_IR_findEnvDecl_x27___closed__0 = _init_l_Lean_IR_findEnvDecl_x27___closed__0();
lean_mark_persistent(l_Lean_IR_findEnvDecl_x27___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
