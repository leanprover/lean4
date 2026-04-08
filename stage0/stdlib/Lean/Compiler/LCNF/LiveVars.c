// Lean compiler output
// Module: Lean.Compiler.LCNF.LiveVars
// Imports: public import Lean.Compiler.LCNF.CompilerM import Lean.Compiler.LCNF.DependsOn
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
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_instHashableFVarId_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqFVarId_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn(uint8_t, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
extern lean_object* l_Lean_instEmptyCollectionFVarIdHashSet;
lean_object* l_Lean_instSingletonFVarIdFVarIdSet___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_visitVar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_visitVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_visitVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_visitVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqFVarId_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableFVarId_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1_spec__3_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__2_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "_private.Lean.Compiler.LCNF.LiveVars.0.Lean.Compiler.LCNF.Code.isFVarLiveIn.go"};
static const lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Compiler.LCNF.LiveVars"};
static const lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1_spec__3_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_isFVarLiveIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_isFVarLiveIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_visitVar___redArg(lean_object* v_fvarId_1_, lean_object* v_x_2_, lean_object* v_a_3_){
_start:
{
uint8_t v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_5_ = l_Lean_instBEqFVarId_beq(v_x_2_, v_fvarId_1_);
v___x_6_ = lean_box(v___x_5_);
v___x_7_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7_, 0, v___x_6_);
lean_ctor_set(v___x_7_, 1, v_a_3_);
v___x_8_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_visitVar___redArg___boxed(lean_object* v_fvarId_9_, lean_object* v_x_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_visitVar___redArg(v_fvarId_9_, v_x_10_, v_a_11_);
lean_dec(v_x_10_);
lean_dec(v_fvarId_9_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_visitVar(lean_object* v_fvarId_14_, lean_object* v_x_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_){
_start:
{
uint8_t v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_23_ = l_Lean_instBEqFVarId_beq(v_x_15_, v_fvarId_14_);
v___x_24_ = lean_box(v___x_23_);
v___x_25_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_25_, 0, v___x_24_);
lean_ctor_set(v___x_25_, 1, v_a_17_);
v___x_26_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_visitVar___boxed(lean_object* v_fvarId_27_, lean_object* v_x_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_visitVar(v_fvarId_27_, v_x_28_, v_a_29_, v_a_30_, v_a_31_, v_a_32_, v_a_33_, v_a_34_);
lean_dec(v_a_34_);
lean_dec_ref(v_a_33_);
lean_dec(v_a_32_);
lean_dec_ref(v_a_31_);
lean_dec_ref(v_a_29_);
lean_dec(v_x_28_);
lean_dec(v_fvarId_27_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg(lean_object* v_jp_39_, lean_object* v_a_40_){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_42_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg___closed__0));
v___x_43_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg___closed__1));
v___x_44_ = lean_box(0);
v___x_45_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_42_, v___x_43_, v_a_40_, v_jp_39_, v___x_44_);
v___x_46_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_46_, 0, v___x_44_);
lean_ctor_set(v___x_46_, 1, v___x_45_);
v___x_47_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg___boxed(lean_object* v_jp_48_, lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg(v_jp_48_, v_a_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited(lean_object* v_jp_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_60_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg___closed__0));
v___x_61_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg___closed__1));
v___x_62_ = lean_box(0);
v___x_63_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_60_, v___x_61_, v_a_54_, v_jp_52_, v___x_62_);
v___x_64_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_64_, 0, v___x_62_);
lean_ctor_set(v___x_64_, 1, v___x_63_);
v___x_65_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___boxed(lean_object* v_jp_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited(v_jp_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_);
lean_dec(v_a_72_);
lean_dec_ref(v_a_71_);
lean_dec(v_a_70_);
lean_dec_ref(v_a_69_);
lean_dec_ref(v_a_67_);
return v_res_74_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__0(void){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l_instMonadEIO(lean_box(0));
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2(lean_object* v_msg_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v_toApplicative_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_163_; 
v___x_88_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__0);
v___x_89_ = l_StateRefT_x27_instMonad___redArg(v___x_88_);
v_toApplicative_90_ = lean_ctor_get(v___x_89_, 0);
v_isSharedCheck_163_ = !lean_is_exclusive(v___x_89_);
if (v_isSharedCheck_163_ == 0)
{
lean_object* v_unused_164_; 
v_unused_164_ = lean_ctor_get(v___x_89_, 1);
lean_dec(v_unused_164_);
v___x_92_ = v___x_89_;
v_isShared_93_ = v_isSharedCheck_163_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_toApplicative_90_);
lean_dec(v___x_89_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_163_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v_toFunctor_94_; lean_object* v_toSeq_95_; lean_object* v_toSeqLeft_96_; lean_object* v_toSeqRight_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_161_; 
v_toFunctor_94_ = lean_ctor_get(v_toApplicative_90_, 0);
v_toSeq_95_ = lean_ctor_get(v_toApplicative_90_, 2);
v_toSeqLeft_96_ = lean_ctor_get(v_toApplicative_90_, 3);
v_toSeqRight_97_ = lean_ctor_get(v_toApplicative_90_, 4);
v_isSharedCheck_161_ = !lean_is_exclusive(v_toApplicative_90_);
if (v_isSharedCheck_161_ == 0)
{
lean_object* v_unused_162_; 
v_unused_162_ = lean_ctor_get(v_toApplicative_90_, 1);
lean_dec(v_unused_162_);
v___x_99_ = v_toApplicative_90_;
v_isShared_100_ = v_isSharedCheck_161_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_toSeqRight_97_);
lean_inc(v_toSeqLeft_96_);
lean_inc(v_toSeq_95_);
lean_inc(v_toFunctor_94_);
lean_dec(v_toApplicative_90_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_161_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___f_101_; lean_object* v___f_102_; lean_object* v___f_103_; lean_object* v___f_104_; lean_object* v___x_105_; lean_object* v___f_106_; lean_object* v___f_107_; lean_object* v___f_108_; lean_object* v___x_110_; 
v___f_101_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__1));
v___f_102_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__2));
lean_inc_ref(v_toFunctor_94_);
v___f_103_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_103_, 0, v_toFunctor_94_);
v___f_104_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_104_, 0, v_toFunctor_94_);
v___x_105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_105_, 0, v___f_103_);
lean_ctor_set(v___x_105_, 1, v___f_104_);
v___f_106_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_106_, 0, v_toSeqRight_97_);
v___f_107_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_107_, 0, v_toSeqLeft_96_);
v___f_108_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_108_, 0, v_toSeq_95_);
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 4, v___f_106_);
lean_ctor_set(v___x_99_, 3, v___f_107_);
lean_ctor_set(v___x_99_, 2, v___f_108_);
lean_ctor_set(v___x_99_, 1, v___f_101_);
lean_ctor_set(v___x_99_, 0, v___x_105_);
v___x_110_ = v___x_99_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v___x_105_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v___f_101_);
lean_ctor_set(v_reuseFailAlloc_160_, 2, v___f_108_);
lean_ctor_set(v_reuseFailAlloc_160_, 3, v___f_107_);
lean_ctor_set(v_reuseFailAlloc_160_, 4, v___f_106_);
v___x_110_ = v_reuseFailAlloc_160_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
lean_object* v___x_112_; 
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 1, v___f_102_);
lean_ctor_set(v___x_92_, 0, v___x_110_);
v___x_112_ = v___x_92_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_110_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v___f_102_);
v___x_112_ = v_reuseFailAlloc_159_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
lean_object* v___x_113_; lean_object* v_toApplicative_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_157_; 
v___x_113_ = l_StateRefT_x27_instMonad___redArg(v___x_112_);
v_toApplicative_114_ = lean_ctor_get(v___x_113_, 0);
v_isSharedCheck_157_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_157_ == 0)
{
lean_object* v_unused_158_; 
v_unused_158_ = lean_ctor_get(v___x_113_, 1);
lean_dec(v_unused_158_);
v___x_116_ = v___x_113_;
v_isShared_117_ = v_isSharedCheck_157_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_toApplicative_114_);
lean_dec(v___x_113_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_157_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v_toFunctor_118_; lean_object* v_toSeq_119_; lean_object* v_toSeqLeft_120_; lean_object* v_toSeqRight_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_155_; 
v_toFunctor_118_ = lean_ctor_get(v_toApplicative_114_, 0);
v_toSeq_119_ = lean_ctor_get(v_toApplicative_114_, 2);
v_toSeqLeft_120_ = lean_ctor_get(v_toApplicative_114_, 3);
v_toSeqRight_121_ = lean_ctor_get(v_toApplicative_114_, 4);
v_isSharedCheck_155_ = !lean_is_exclusive(v_toApplicative_114_);
if (v_isSharedCheck_155_ == 0)
{
lean_object* v_unused_156_; 
v_unused_156_ = lean_ctor_get(v_toApplicative_114_, 1);
lean_dec(v_unused_156_);
v___x_123_ = v_toApplicative_114_;
v_isShared_124_ = v_isSharedCheck_155_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_toSeqRight_121_);
lean_inc(v_toSeqLeft_120_);
lean_inc(v_toSeq_119_);
lean_inc(v_toFunctor_118_);
lean_dec(v_toApplicative_114_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_155_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___f_125_; lean_object* v___f_126_; lean_object* v___f_127_; lean_object* v___f_128_; lean_object* v___x_129_; lean_object* v___f_130_; lean_object* v___f_131_; lean_object* v___f_132_; lean_object* v___x_134_; 
v___f_125_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__3));
v___f_126_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__4));
lean_inc_ref(v_toFunctor_118_);
v___f_127_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_127_, 0, v_toFunctor_118_);
v___f_128_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_128_, 0, v_toFunctor_118_);
v___x_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_129_, 0, v___f_127_);
lean_ctor_set(v___x_129_, 1, v___f_128_);
v___f_130_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_130_, 0, v_toSeqRight_121_);
v___f_131_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_131_, 0, v_toSeqLeft_120_);
v___f_132_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_132_, 0, v_toSeq_119_);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 4, v___f_130_);
lean_ctor_set(v___x_123_, 3, v___f_131_);
lean_ctor_set(v___x_123_, 2, v___f_132_);
lean_ctor_set(v___x_123_, 1, v___f_125_);
lean_ctor_set(v___x_123_, 0, v___x_129_);
v___x_134_ = v___x_123_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_129_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v___f_125_);
lean_ctor_set(v_reuseFailAlloc_154_, 2, v___f_132_);
lean_ctor_set(v_reuseFailAlloc_154_, 3, v___f_131_);
lean_ctor_set(v_reuseFailAlloc_154_, 4, v___f_130_);
v___x_134_ = v_reuseFailAlloc_154_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
lean_object* v___x_136_; 
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 1, v___f_126_);
lean_ctor_set(v___x_116_, 0, v___x_134_);
v___x_136_ = v___x_116_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v___x_134_);
lean_ctor_set(v_reuseFailAlloc_153_, 1, v___f_126_);
v___x_136_ = v_reuseFailAlloc_153_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
lean_object* v___f_137_; lean_object* v___f_138_; lean_object* v___f_139_; lean_object* v___f_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; uint8_t v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___f_150_; lean_object* v___x_17243__overap_151_; lean_object* v___x_152_; 
lean_inc_ref_n(v___x_136_, 6);
v___f_137_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_137_, 0, v___x_136_);
v___f_138_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_138_, 0, v___x_136_);
v___f_139_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_139_, 0, v___x_136_);
v___f_140_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_140_, 0, v___x_136_);
v___x_141_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_141_, 0, lean_box(0));
lean_closure_set(v___x_141_, 1, lean_box(0));
lean_closure_set(v___x_141_, 2, v___x_136_);
v___x_142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
lean_ctor_set(v___x_142_, 1, v___f_137_);
v___x_143_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_143_, 0, lean_box(0));
lean_closure_set(v___x_143_, 1, lean_box(0));
lean_closure_set(v___x_143_, 2, v___x_136_);
v___x_144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_144_, 0, v___x_142_);
lean_ctor_set(v___x_144_, 1, v___x_143_);
lean_ctor_set(v___x_144_, 2, v___f_138_);
lean_ctor_set(v___x_144_, 3, v___f_139_);
lean_ctor_set(v___x_144_, 4, v___f_140_);
v___x_145_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_145_, 0, lean_box(0));
lean_closure_set(v___x_145_, 1, lean_box(0));
lean_closure_set(v___x_145_, 2, v___x_136_);
v___x_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_146_, 0, v___x_144_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
v___x_147_ = 0;
v___x_148_ = lean_box(v___x_147_);
v___x_149_ = l_instInhabitedOfMonad___redArg(v___x_146_, v___x_148_);
v___f_150_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_150_, 0, v___x_149_);
v___x_17243__overap_151_ = lean_panic_fn_borrowed(v___f_150_, v_msg_80_);
lean_dec_ref(v___f_150_);
lean_inc(v___y_86_);
lean_inc_ref(v___y_85_);
lean_inc(v___y_84_);
lean_inc_ref(v___y_83_);
lean_inc_ref(v___y_81_);
v___x_152_ = lean_apply_7(v___x_17243__overap_151_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, lean_box(0));
return v___x_152_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___boxed(lean_object* v_msg_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2(v_msg_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec_ref(v___y_166_);
return v_res_173_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0___redArg(lean_object* v_a_174_, lean_object* v_x_175_){
_start:
{
if (lean_obj_tag(v_x_175_) == 0)
{
uint8_t v___x_176_; 
v___x_176_ = 0;
return v___x_176_;
}
else
{
lean_object* v_key_177_; lean_object* v_tail_178_; uint8_t v___x_179_; 
v_key_177_ = lean_ctor_get(v_x_175_, 0);
v_tail_178_ = lean_ctor_get(v_x_175_, 2);
v___x_179_ = l_Lean_instBEqFVarId_beq(v_key_177_, v_a_174_);
if (v___x_179_ == 0)
{
v_x_175_ = v_tail_178_;
goto _start;
}
else
{
return v___x_179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0___redArg___boxed(lean_object* v_a_181_, lean_object* v_x_182_){
_start:
{
uint8_t v_res_183_; lean_object* v_r_184_; 
v_res_183_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0___redArg(v_a_181_, v_x_182_);
lean_dec(v_x_182_);
lean_dec(v_a_181_);
v_r_184_ = lean_box(v_res_183_);
return v_r_184_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___redArg(lean_object* v_m_185_, lean_object* v_a_186_){
_start:
{
lean_object* v_buckets_187_; lean_object* v___x_188_; uint64_t v___x_189_; uint64_t v___x_190_; uint64_t v___x_191_; uint64_t v_fold_192_; uint64_t v___x_193_; uint64_t v___x_194_; uint64_t v___x_195_; size_t v___x_196_; size_t v___x_197_; size_t v___x_198_; size_t v___x_199_; size_t v___x_200_; lean_object* v___x_201_; uint8_t v___x_202_; 
v_buckets_187_ = lean_ctor_get(v_m_185_, 1);
v___x_188_ = lean_array_get_size(v_buckets_187_);
v___x_189_ = l_Lean_instHashableFVarId_hash(v_a_186_);
v___x_190_ = 32ULL;
v___x_191_ = lean_uint64_shift_right(v___x_189_, v___x_190_);
v_fold_192_ = lean_uint64_xor(v___x_189_, v___x_191_);
v___x_193_ = 16ULL;
v___x_194_ = lean_uint64_shift_right(v_fold_192_, v___x_193_);
v___x_195_ = lean_uint64_xor(v_fold_192_, v___x_194_);
v___x_196_ = lean_uint64_to_usize(v___x_195_);
v___x_197_ = lean_usize_of_nat(v___x_188_);
v___x_198_ = ((size_t)1ULL);
v___x_199_ = lean_usize_sub(v___x_197_, v___x_198_);
v___x_200_ = lean_usize_land(v___x_196_, v___x_199_);
v___x_201_ = lean_array_uget_borrowed(v_buckets_187_, v___x_200_);
v___x_202_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0___redArg(v_a_186_, v___x_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___redArg___boxed(lean_object* v_m_203_, lean_object* v_a_204_){
_start:
{
uint8_t v_res_205_; lean_object* v_r_206_; 
v_res_205_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___redArg(v_m_203_, v_a_204_);
lean_dec(v_a_204_);
lean_dec_ref(v_m_203_);
v_r_206_ = lean_box(v_res_205_);
return v_r_206_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3(lean_object* v_a_207_, lean_object* v_as_208_, size_t v_i_209_, size_t v_stop_210_){
_start:
{
uint8_t v___x_211_; 
v___x_211_ = lean_usize_dec_eq(v_i_209_, v_stop_210_);
if (v___x_211_ == 0)
{
lean_object* v_targetSet_212_; lean_object* v___x_213_; uint8_t v___x_214_; uint8_t v___x_215_; 
v_targetSet_212_ = lean_ctor_get(v_a_207_, 0);
v___x_213_ = lean_array_uget_borrowed(v_as_208_, v_i_209_);
v___x_214_ = 1;
v___x_215_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn(v___x_214_, v___x_213_, v_targetSet_212_);
if (v___x_215_ == 0)
{
size_t v___x_216_; size_t v___x_217_; 
v___x_216_ = ((size_t)1ULL);
v___x_217_ = lean_usize_add(v_i_209_, v___x_216_);
v_i_209_ = v___x_217_;
goto _start;
}
else
{
return v___x_215_;
}
}
else
{
uint8_t v___x_219_; 
v___x_219_ = 0;
return v___x_219_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3___boxed(lean_object* v_a_220_, lean_object* v_as_221_, lean_object* v_i_222_, lean_object* v_stop_223_){
_start:
{
size_t v_i_boxed_224_; size_t v_stop_boxed_225_; uint8_t v_res_226_; lean_object* v_r_227_; 
v_i_boxed_224_ = lean_unbox_usize(v_i_222_);
lean_dec(v_i_222_);
v_stop_boxed_225_ = lean_unbox_usize(v_stop_223_);
lean_dec(v_stop_223_);
v_res_226_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3(v_a_220_, v_as_221_, v_i_boxed_224_, v_stop_boxed_225_);
lean_dec_ref(v_as_221_);
lean_dec_ref(v_a_220_);
v_r_227_ = lean_box(v_res_226_);
return v_r_227_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1_spec__3_spec__7___redArg(lean_object* v_x_228_, lean_object* v_x_229_){
_start:
{
if (lean_obj_tag(v_x_229_) == 0)
{
return v_x_228_;
}
else
{
lean_object* v_key_230_; lean_object* v_value_231_; lean_object* v_tail_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_255_; 
v_key_230_ = lean_ctor_get(v_x_229_, 0);
v_value_231_ = lean_ctor_get(v_x_229_, 1);
v_tail_232_ = lean_ctor_get(v_x_229_, 2);
v_isSharedCheck_255_ = !lean_is_exclusive(v_x_229_);
if (v_isSharedCheck_255_ == 0)
{
v___x_234_ = v_x_229_;
v_isShared_235_ = v_isSharedCheck_255_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_tail_232_);
lean_inc(v_value_231_);
lean_inc(v_key_230_);
lean_dec(v_x_229_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_255_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_236_; uint64_t v___x_237_; uint64_t v___x_238_; uint64_t v___x_239_; uint64_t v_fold_240_; uint64_t v___x_241_; uint64_t v___x_242_; uint64_t v___x_243_; size_t v___x_244_; size_t v___x_245_; size_t v___x_246_; size_t v___x_247_; size_t v___x_248_; lean_object* v___x_249_; lean_object* v___x_251_; 
v___x_236_ = lean_array_get_size(v_x_228_);
v___x_237_ = l_Lean_instHashableFVarId_hash(v_key_230_);
v___x_238_ = 32ULL;
v___x_239_ = lean_uint64_shift_right(v___x_237_, v___x_238_);
v_fold_240_ = lean_uint64_xor(v___x_237_, v___x_239_);
v___x_241_ = 16ULL;
v___x_242_ = lean_uint64_shift_right(v_fold_240_, v___x_241_);
v___x_243_ = lean_uint64_xor(v_fold_240_, v___x_242_);
v___x_244_ = lean_uint64_to_usize(v___x_243_);
v___x_245_ = lean_usize_of_nat(v___x_236_);
v___x_246_ = ((size_t)1ULL);
v___x_247_ = lean_usize_sub(v___x_245_, v___x_246_);
v___x_248_ = lean_usize_land(v___x_244_, v___x_247_);
v___x_249_ = lean_array_uget_borrowed(v_x_228_, v___x_248_);
lean_inc(v___x_249_);
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 2, v___x_249_);
v___x_251_ = v___x_234_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_key_230_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v_value_231_);
lean_ctor_set(v_reuseFailAlloc_254_, 2, v___x_249_);
v___x_251_ = v_reuseFailAlloc_254_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
lean_object* v___x_252_; 
v___x_252_ = lean_array_uset(v_x_228_, v___x_248_, v___x_251_);
v_x_228_ = v___x_252_;
v_x_229_ = v_tail_232_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1_spec__3___redArg(lean_object* v_i_256_, lean_object* v_source_257_, lean_object* v_target_258_){
_start:
{
lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_259_ = lean_array_get_size(v_source_257_);
v___x_260_ = lean_nat_dec_lt(v_i_256_, v___x_259_);
if (v___x_260_ == 0)
{
lean_dec_ref(v_source_257_);
lean_dec(v_i_256_);
return v_target_258_;
}
else
{
lean_object* v_es_261_; lean_object* v___x_262_; lean_object* v_source_263_; lean_object* v_target_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v_es_261_ = lean_array_fget(v_source_257_, v_i_256_);
v___x_262_ = lean_box(0);
v_source_263_ = lean_array_fset(v_source_257_, v_i_256_, v___x_262_);
v_target_264_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1_spec__3_spec__7___redArg(v_target_258_, v_es_261_);
v___x_265_ = lean_unsigned_to_nat(1u);
v___x_266_ = lean_nat_add(v_i_256_, v___x_265_);
lean_dec(v_i_256_);
v_i_256_ = v___x_266_;
v_source_257_ = v_source_263_;
v_target_258_ = v_target_264_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1___redArg(lean_object* v_data_268_){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v_nbuckets_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_269_ = lean_array_get_size(v_data_268_);
v___x_270_ = lean_unsigned_to_nat(2u);
v_nbuckets_271_ = lean_nat_mul(v___x_269_, v___x_270_);
v___x_272_ = lean_unsigned_to_nat(0u);
v___x_273_ = lean_box(0);
v___x_274_ = lean_mk_array(v_nbuckets_271_, v___x_273_);
v___x_275_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1_spec__3___redArg(v___x_272_, v_data_268_, v___x_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0___redArg(lean_object* v_m_276_, lean_object* v_a_277_, lean_object* v_b_278_){
_start:
{
lean_object* v_size_279_; lean_object* v_buckets_280_; lean_object* v___x_281_; uint64_t v___x_282_; uint64_t v___x_283_; uint64_t v___x_284_; uint64_t v_fold_285_; uint64_t v___x_286_; uint64_t v___x_287_; uint64_t v___x_288_; size_t v___x_289_; size_t v___x_290_; size_t v___x_291_; size_t v___x_292_; size_t v___x_293_; lean_object* v_bkt_294_; uint8_t v___x_295_; 
v_size_279_ = lean_ctor_get(v_m_276_, 0);
v_buckets_280_ = lean_ctor_get(v_m_276_, 1);
v___x_281_ = lean_array_get_size(v_buckets_280_);
v___x_282_ = l_Lean_instHashableFVarId_hash(v_a_277_);
v___x_283_ = 32ULL;
v___x_284_ = lean_uint64_shift_right(v___x_282_, v___x_283_);
v_fold_285_ = lean_uint64_xor(v___x_282_, v___x_284_);
v___x_286_ = 16ULL;
v___x_287_ = lean_uint64_shift_right(v_fold_285_, v___x_286_);
v___x_288_ = lean_uint64_xor(v_fold_285_, v___x_287_);
v___x_289_ = lean_uint64_to_usize(v___x_288_);
v___x_290_ = lean_usize_of_nat(v___x_281_);
v___x_291_ = ((size_t)1ULL);
v___x_292_ = lean_usize_sub(v___x_290_, v___x_291_);
v___x_293_ = lean_usize_land(v___x_289_, v___x_292_);
v_bkt_294_ = lean_array_uget_borrowed(v_buckets_280_, v___x_293_);
v___x_295_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0___redArg(v_a_277_, v_bkt_294_);
if (v___x_295_ == 0)
{
lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_316_; 
lean_inc_ref(v_buckets_280_);
lean_inc(v_size_279_);
v_isSharedCheck_316_ = !lean_is_exclusive(v_m_276_);
if (v_isSharedCheck_316_ == 0)
{
lean_object* v_unused_317_; lean_object* v_unused_318_; 
v_unused_317_ = lean_ctor_get(v_m_276_, 1);
lean_dec(v_unused_317_);
v_unused_318_ = lean_ctor_get(v_m_276_, 0);
lean_dec(v_unused_318_);
v___x_297_ = v_m_276_;
v_isShared_298_ = v_isSharedCheck_316_;
goto v_resetjp_296_;
}
else
{
lean_dec(v_m_276_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_316_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_299_; lean_object* v_size_x27_300_; lean_object* v___x_301_; lean_object* v_buckets_x27_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_299_ = lean_unsigned_to_nat(1u);
v_size_x27_300_ = lean_nat_add(v_size_279_, v___x_299_);
lean_dec(v_size_279_);
lean_inc(v_bkt_294_);
v___x_301_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_301_, 0, v_a_277_);
lean_ctor_set(v___x_301_, 1, v_b_278_);
lean_ctor_set(v___x_301_, 2, v_bkt_294_);
v_buckets_x27_302_ = lean_array_uset(v_buckets_280_, v___x_293_, v___x_301_);
v___x_303_ = lean_unsigned_to_nat(4u);
v___x_304_ = lean_nat_mul(v_size_x27_300_, v___x_303_);
v___x_305_ = lean_unsigned_to_nat(3u);
v___x_306_ = lean_nat_div(v___x_304_, v___x_305_);
lean_dec(v___x_304_);
v___x_307_ = lean_array_get_size(v_buckets_x27_302_);
v___x_308_ = lean_nat_dec_le(v___x_306_, v___x_307_);
lean_dec(v___x_306_);
if (v___x_308_ == 0)
{
lean_object* v_val_309_; lean_object* v___x_311_; 
v_val_309_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1___redArg(v_buckets_x27_302_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 1, v_val_309_);
lean_ctor_set(v___x_297_, 0, v_size_x27_300_);
v___x_311_ = v___x_297_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_size_x27_300_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v_val_309_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
else
{
lean_object* v___x_314_; 
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 1, v_buckets_x27_302_);
lean_ctor_set(v___x_297_, 0, v_size_x27_300_);
v___x_314_ = v___x_297_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_size_x27_300_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v_buckets_x27_302_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
else
{
lean_dec(v_b_278_);
lean_dec(v_a_277_);
return v_m_276_;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__3(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_322_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__2));
v___x_323_ = lean_unsigned_to_nat(48u);
v___x_324_ = lean_unsigned_to_nat(76u);
v___x_325_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__1));
v___x_326_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__0));
v___x_327_ = l_mkPanicMessageWithDecl(v___x_326_, v___x_325_, v___x_324_, v___x_323_, v___x_322_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go(lean_object* v_fvarId_328_, lean_object* v_c_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_){
_start:
{
switch(lean_obj_tag(v_c_329_))
{
case 0:
{
lean_object* v_decl_337_; lean_object* v_k_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_351_; 
v_decl_337_ = lean_ctor_get(v_c_329_, 0);
v_k_338_ = lean_ctor_get(v_c_329_, 1);
v_isSharedCheck_351_ = !lean_is_exclusive(v_c_329_);
if (v_isSharedCheck_351_ == 0)
{
v___x_340_ = v_c_329_;
v_isShared_341_ = v_isSharedCheck_351_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_k_338_);
lean_inc(v_decl_337_);
lean_dec(v_c_329_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_351_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v_targetSet_342_; uint8_t v___x_343_; uint8_t v___x_344_; 
v_targetSet_342_ = lean_ctor_get(v_a_330_, 0);
v___x_343_ = 1;
v___x_344_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn(v___x_343_, v_decl_337_, v_targetSet_342_);
lean_dec_ref(v_decl_337_);
if (v___x_344_ == 0)
{
lean_del_object(v___x_340_);
v_c_329_ = v_k_338_;
goto _start;
}
else
{
lean_object* v___x_346_; lean_object* v___x_348_; 
lean_dec_ref(v_k_338_);
v___x_346_ = lean_box(v___x_344_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 1, v_a_331_);
lean_ctor_set(v___x_340_, 0, v___x_346_);
v___x_348_ = v___x_340_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_346_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v_a_331_);
v___x_348_ = v_reuseFailAlloc_350_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
lean_object* v___x_349_; 
v___x_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
return v___x_349_;
}
}
}
}
case 2:
{
lean_object* v_decl_352_; lean_object* v_k_353_; lean_object* v_fvarId_354_; lean_object* v_value_355_; lean_object* v___x_356_; 
v_decl_352_ = lean_ctor_get(v_c_329_, 0);
lean_inc_ref(v_decl_352_);
v_k_353_ = lean_ctor_get(v_c_329_, 1);
lean_inc_ref(v_k_353_);
lean_dec_ref(v_c_329_);
v_fvarId_354_ = lean_ctor_get(v_decl_352_, 0);
lean_inc(v_fvarId_354_);
v_value_355_ = lean_ctor_get(v_decl_352_, 4);
lean_inc_ref(v_value_355_);
lean_dec_ref(v_decl_352_);
v___x_356_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go(v_fvarId_328_, v_value_355_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_);
if (lean_obj_tag(v___x_356_) == 0)
{
lean_object* v_a_357_; lean_object* v_fst_358_; uint8_t v___x_359_; 
v_a_357_ = lean_ctor_get(v___x_356_, 0);
lean_inc(v_a_357_);
v_fst_358_ = lean_ctor_get(v_a_357_, 0);
v___x_359_ = lean_unbox(v_fst_358_);
if (v___x_359_ == 0)
{
lean_object* v_snd_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
lean_dec_ref(v___x_356_);
v_snd_360_ = lean_ctor_get(v_a_357_, 1);
lean_inc(v_snd_360_);
lean_dec(v_a_357_);
v___x_361_ = lean_box(0);
v___x_362_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0___redArg(v_snd_360_, v_fvarId_354_, v___x_361_);
v_c_329_ = v_k_353_;
v_a_331_ = v___x_362_;
goto _start;
}
else
{
lean_dec(v_a_357_);
lean_dec(v_fvarId_354_);
lean_dec_ref(v_k_353_);
return v___x_356_;
}
}
else
{
lean_dec(v_fvarId_354_);
lean_dec_ref(v_k_353_);
return v___x_356_;
}
}
case 3:
{
lean_object* v_fvarId_364_; lean_object* v_args_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_404_; 
v_fvarId_364_ = lean_ctor_get(v_c_329_, 0);
v_args_365_ = lean_ctor_get(v_c_329_, 1);
v_isSharedCheck_404_ = !lean_is_exclusive(v_c_329_);
if (v_isSharedCheck_404_ == 0)
{
v___x_367_ = v_c_329_;
v_isShared_368_ = v_isSharedCheck_404_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_args_365_);
lean_inc(v_fvarId_364_);
lean_dec(v_c_329_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_404_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
uint8_t v___y_370_; lean_object* v___x_395_; lean_object* v___x_396_; uint8_t v___x_397_; 
v___x_395_ = lean_unsigned_to_nat(0u);
v___x_396_ = lean_array_get_size(v_args_365_);
v___x_397_ = lean_nat_dec_lt(v___x_395_, v___x_396_);
if (v___x_397_ == 0)
{
lean_dec_ref(v_args_365_);
v___y_370_ = v___x_397_;
goto v___jp_369_;
}
else
{
if (v___x_397_ == 0)
{
lean_dec_ref(v_args_365_);
v___y_370_ = v___x_397_;
goto v___jp_369_;
}
else
{
size_t v___x_398_; size_t v___x_399_; uint8_t v___x_400_; 
v___x_398_ = ((size_t)0ULL);
v___x_399_ = lean_usize_of_nat(v___x_396_);
v___x_400_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3(v_a_330_, v_args_365_, v___x_398_, v___x_399_);
lean_dec_ref(v_args_365_);
if (v___x_400_ == 0)
{
v___y_370_ = v___x_400_;
goto v___jp_369_;
}
else
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
lean_del_object(v___x_367_);
lean_dec(v_fvarId_364_);
v___x_401_ = lean_box(v___x_400_);
v___x_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
lean_ctor_set(v___x_402_, 1, v_a_331_);
v___x_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
return v___x_403_;
}
}
}
v___jp_369_:
{
uint8_t v___x_371_; 
v___x_371_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___redArg(v_a_331_, v_fvarId_364_);
if (v___x_371_ == 0)
{
uint8_t v___x_372_; lean_object* v___x_373_; 
lean_del_object(v___x_367_);
v___x_372_ = 1;
v___x_373_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_372_, v_fvarId_364_, v_a_333_);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v_a_374_; 
v_a_374_ = lean_ctor_get(v___x_373_, 0);
lean_inc(v_a_374_);
lean_dec_ref(v___x_373_);
if (lean_obj_tag(v_a_374_) == 1)
{
lean_object* v_val_375_; lean_object* v_value_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v_val_375_ = lean_ctor_get(v_a_374_, 0);
lean_inc(v_val_375_);
lean_dec_ref(v_a_374_);
v_value_376_ = lean_ctor_get(v_val_375_, 4);
lean_inc_ref(v_value_376_);
lean_dec(v_val_375_);
v___x_377_ = lean_box(0);
v___x_378_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0___redArg(v_a_331_, v_fvarId_364_, v___x_377_);
v_c_329_ = v_value_376_;
v_a_331_ = v___x_378_;
goto _start;
}
else
{
lean_object* v___x_380_; lean_object* v___x_381_; 
lean_dec(v_a_374_);
lean_dec(v_fvarId_364_);
v___x_380_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__3, &l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__3);
v___x_381_ = l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2(v___x_380_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_);
return v___x_381_;
}
}
else
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_389_; 
lean_dec(v_fvarId_364_);
lean_dec_ref(v_a_331_);
v_a_382_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_389_ == 0)
{
v___x_384_ = v___x_373_;
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_373_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_387_; 
if (v_isShared_385_ == 0)
{
v___x_387_ = v___x_384_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_a_382_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
else
{
lean_object* v___x_390_; lean_object* v___x_392_; 
lean_dec(v_fvarId_364_);
v___x_390_ = lean_box(v___y_370_);
if (v_isShared_368_ == 0)
{
lean_ctor_set_tag(v___x_367_, 0);
lean_ctor_set(v___x_367_, 1, v_a_331_);
lean_ctor_set(v___x_367_, 0, v___x_390_);
v___x_392_ = v___x_367_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_390_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v_a_331_);
v___x_392_ = v_reuseFailAlloc_394_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
lean_object* v___x_393_; 
v___x_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
return v___x_393_;
}
}
}
}
}
case 4:
{
lean_object* v_cases_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_433_; 
v_cases_405_ = lean_ctor_get(v_c_329_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v_c_329_);
if (v_isSharedCheck_433_ == 0)
{
v___x_407_ = v_c_329_;
v_isShared_408_ = v_isSharedCheck_433_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_cases_405_);
lean_dec(v_c_329_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_433_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v_discr_409_; lean_object* v_alts_410_; uint8_t v___x_411_; 
v_discr_409_ = lean_ctor_get(v_cases_405_, 2);
lean_inc(v_discr_409_);
v_alts_410_ = lean_ctor_get(v_cases_405_, 3);
lean_inc_ref(v_alts_410_);
lean_dec_ref(v_cases_405_);
v___x_411_ = l_Lean_instBEqFVarId_beq(v_discr_409_, v_fvarId_328_);
lean_dec(v_discr_409_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; lean_object* v___x_413_; uint8_t v___x_414_; 
v___x_412_ = lean_unsigned_to_nat(0u);
v___x_413_ = lean_array_get_size(v_alts_410_);
v___x_414_ = lean_nat_dec_lt(v___x_412_, v___x_413_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_418_; 
lean_dec_ref(v_alts_410_);
v___x_415_ = lean_box(v___x_411_);
v___x_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
lean_ctor_set(v___x_416_, 1, v_a_331_);
if (v_isShared_408_ == 0)
{
lean_ctor_set_tag(v___x_407_, 0);
lean_ctor_set(v___x_407_, 0, v___x_416_);
v___x_418_ = v___x_407_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_416_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
else
{
if (v___x_414_ == 0)
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_423_; 
lean_dec_ref(v_alts_410_);
v___x_420_ = lean_box(v___x_411_);
v___x_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
lean_ctor_set(v___x_421_, 1, v_a_331_);
if (v_isShared_408_ == 0)
{
lean_ctor_set_tag(v___x_407_, 0);
lean_ctor_set(v___x_407_, 0, v___x_421_);
v___x_423_ = v___x_407_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_421_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
else
{
size_t v___x_425_; size_t v___x_426_; lean_object* v___x_427_; 
lean_del_object(v___x_407_);
v___x_425_ = ((size_t)0ULL);
v___x_426_ = lean_usize_of_nat(v___x_413_);
v___x_427_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__4(v_fvarId_328_, v_alts_410_, v___x_425_, v___x_426_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_);
lean_dec_ref(v_alts_410_);
return v___x_427_;
}
}
}
else
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_431_; 
lean_dec_ref(v_alts_410_);
v___x_428_ = lean_box(v___x_411_);
v___x_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
lean_ctor_set(v___x_429_, 1, v_a_331_);
if (v_isShared_408_ == 0)
{
lean_ctor_set_tag(v___x_407_, 0);
lean_ctor_set(v___x_407_, 0, v___x_429_);
v___x_431_ = v___x_407_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_429_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_444_; 
v_fvarId_434_ = lean_ctor_get(v_c_329_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v_c_329_);
if (v_isSharedCheck_444_ == 0)
{
v___x_436_ = v_c_329_;
v_isShared_437_ = v_isSharedCheck_444_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_fvarId_434_);
lean_dec(v_c_329_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_444_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
uint8_t v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_442_; 
v___x_438_ = l_Lean_instBEqFVarId_beq(v_fvarId_434_, v_fvarId_328_);
lean_dec(v_fvarId_434_);
v___x_439_ = lean_box(v___x_438_);
v___x_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
lean_ctor_set(v___x_440_, 1, v_a_331_);
if (v_isShared_437_ == 0)
{
lean_ctor_set_tag(v___x_436_, 0);
lean_ctor_set(v___x_436_, 0, v___x_440_);
v___x_442_ = v___x_436_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___x_440_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
case 6:
{
lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_454_; 
v_isSharedCheck_454_ = !lean_is_exclusive(v_c_329_);
if (v_isSharedCheck_454_ == 0)
{
lean_object* v_unused_455_; 
v_unused_455_ = lean_ctor_get(v_c_329_, 0);
lean_dec(v_unused_455_);
v___x_446_ = v_c_329_;
v_isShared_447_ = v_isSharedCheck_454_;
goto v_resetjp_445_;
}
else
{
lean_dec(v_c_329_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_454_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
uint8_t v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_452_; 
v___x_448_ = 0;
v___x_449_ = lean_box(v___x_448_);
v___x_450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
lean_ctor_set(v___x_450_, 1, v_a_331_);
if (v_isShared_447_ == 0)
{
lean_ctor_set_tag(v___x_446_, 0);
lean_ctor_set(v___x_446_, 0, v___x_450_);
v___x_452_ = v___x_446_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_450_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
case 7:
{
lean_object* v_fvarId_456_; lean_object* v_y_457_; lean_object* v_k_458_; uint8_t v___x_459_; 
v_fvarId_456_ = lean_ctor_get(v_c_329_, 0);
lean_inc(v_fvarId_456_);
v_y_457_ = lean_ctor_get(v_c_329_, 2);
lean_inc(v_y_457_);
v_k_458_ = lean_ctor_get(v_c_329_, 3);
lean_inc_ref(v_k_458_);
lean_dec_ref(v_c_329_);
v___x_459_ = l_Lean_instBEqFVarId_beq(v_fvarId_456_, v_fvarId_328_);
lean_dec(v_fvarId_456_);
if (v___x_459_ == 0)
{
lean_object* v_targetSet_460_; uint8_t v___x_461_; uint8_t v___x_462_; 
v_targetSet_460_ = lean_ctor_get(v_a_330_, 0);
v___x_461_ = 1;
v___x_462_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn(v___x_461_, v_y_457_, v_targetSet_460_);
lean_dec(v_y_457_);
if (v___x_462_ == 0)
{
v_c_329_ = v_k_458_;
goto _start;
}
else
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
lean_dec_ref(v_k_458_);
v___x_464_ = lean_box(v___x_462_);
v___x_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
lean_ctor_set(v___x_465_, 1, v_a_331_);
v___x_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
return v___x_466_;
}
}
else
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
lean_dec_ref(v_k_458_);
lean_dec(v_y_457_);
v___x_467_ = lean_box(v___x_459_);
v___x_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
lean_ctor_set(v___x_468_, 1, v_a_331_);
v___x_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
return v___x_469_;
}
}
case 8:
{
lean_object* v_fvarId_470_; lean_object* v_y_471_; lean_object* v_k_472_; uint8_t v___x_473_; 
v_fvarId_470_ = lean_ctor_get(v_c_329_, 0);
lean_inc(v_fvarId_470_);
v_y_471_ = lean_ctor_get(v_c_329_, 2);
lean_inc(v_y_471_);
v_k_472_ = lean_ctor_get(v_c_329_, 3);
lean_inc_ref(v_k_472_);
lean_dec_ref(v_c_329_);
v___x_473_ = l_Lean_instBEqFVarId_beq(v_fvarId_470_, v_fvarId_328_);
lean_dec(v_fvarId_470_);
if (v___x_473_ == 0)
{
uint8_t v___x_474_; 
v___x_474_ = l_Lean_instBEqFVarId_beq(v_y_471_, v_fvarId_328_);
lean_dec(v_y_471_);
if (v___x_474_ == 0)
{
v_c_329_ = v_k_472_;
goto _start;
}
else
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
lean_dec_ref(v_k_472_);
v___x_476_ = lean_box(v___x_474_);
v___x_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
lean_ctor_set(v___x_477_, 1, v_a_331_);
v___x_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
return v___x_478_;
}
}
else
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
lean_dec_ref(v_k_472_);
lean_dec(v_y_471_);
v___x_479_ = lean_box(v___x_473_);
v___x_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
lean_ctor_set(v___x_480_, 1, v_a_331_);
v___x_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
return v___x_481_;
}
}
case 9:
{
lean_object* v_fvarId_482_; lean_object* v_y_483_; lean_object* v_k_484_; uint8_t v___x_485_; 
v_fvarId_482_ = lean_ctor_get(v_c_329_, 0);
lean_inc(v_fvarId_482_);
v_y_483_ = lean_ctor_get(v_c_329_, 3);
lean_inc(v_y_483_);
v_k_484_ = lean_ctor_get(v_c_329_, 5);
lean_inc_ref(v_k_484_);
lean_dec_ref(v_c_329_);
v___x_485_ = l_Lean_instBEqFVarId_beq(v_fvarId_482_, v_fvarId_328_);
lean_dec(v_fvarId_482_);
if (v___x_485_ == 0)
{
uint8_t v___x_486_; 
v___x_486_ = l_Lean_instBEqFVarId_beq(v_y_483_, v_fvarId_328_);
lean_dec(v_y_483_);
if (v___x_486_ == 0)
{
v_c_329_ = v_k_484_;
goto _start;
}
else
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
lean_dec_ref(v_k_484_);
v___x_488_ = lean_box(v___x_486_);
v___x_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
lean_ctor_set(v___x_489_, 1, v_a_331_);
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
return v___x_490_;
}
}
else
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
lean_dec_ref(v_k_484_);
lean_dec(v_y_483_);
v___x_491_ = lean_box(v___x_485_);
v___x_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
lean_ctor_set(v___x_492_, 1, v_a_331_);
v___x_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
return v___x_493_;
}
}
case 13:
{
lean_object* v_fvarId_494_; lean_object* v_k_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_506_; 
v_fvarId_494_ = lean_ctor_get(v_c_329_, 0);
v_k_495_ = lean_ctor_get(v_c_329_, 1);
v_isSharedCheck_506_ = !lean_is_exclusive(v_c_329_);
if (v_isSharedCheck_506_ == 0)
{
v___x_497_ = v_c_329_;
v_isShared_498_ = v_isSharedCheck_506_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_k_495_);
lean_inc(v_fvarId_494_);
lean_dec(v_c_329_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_506_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
uint8_t v___x_499_; 
v___x_499_ = l_Lean_instBEqFVarId_beq(v_fvarId_494_, v_fvarId_328_);
lean_dec(v_fvarId_494_);
if (v___x_499_ == 0)
{
lean_del_object(v___x_497_);
v_c_329_ = v_k_495_;
goto _start;
}
else
{
lean_object* v___x_501_; lean_object* v___x_503_; 
lean_dec_ref(v_k_495_);
v___x_501_ = lean_box(v___x_499_);
if (v_isShared_498_ == 0)
{
lean_ctor_set_tag(v___x_497_, 0);
lean_ctor_set(v___x_497_, 1, v_a_331_);
lean_ctor_set(v___x_497_, 0, v___x_501_);
v___x_503_ = v___x_497_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_501_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v_a_331_);
v___x_503_ = v_reuseFailAlloc_505_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
lean_object* v___x_504_; 
v___x_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
return v___x_504_;
}
}
}
}
default: 
{
lean_object* v_fvarId_507_; lean_object* v_k_508_; uint8_t v___x_509_; 
v_fvarId_507_ = lean_ctor_get(v_c_329_, 0);
lean_inc(v_fvarId_507_);
v_k_508_ = lean_ctor_get(v_c_329_, 2);
lean_inc_ref(v_k_508_);
lean_dec_ref(v_c_329_);
v___x_509_ = l_Lean_instBEqFVarId_beq(v_fvarId_507_, v_fvarId_328_);
lean_dec(v_fvarId_507_);
if (v___x_509_ == 0)
{
v_c_329_ = v_k_508_;
goto _start;
}
else
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
lean_dec_ref(v_k_508_);
v___x_511_ = lean_box(v___x_509_);
v___x_512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
lean_ctor_set(v___x_512_, 1, v_a_331_);
v___x_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
return v___x_513_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__4(lean_object* v_fvarId_514_, lean_object* v_as_515_, size_t v_i_516_, size_t v_stop_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
uint8_t v___x_525_; 
v___x_525_ = lean_usize_dec_eq(v_i_516_, v_stop_517_);
if (v___x_525_ == 0)
{
uint8_t v___x_526_; lean_object* v___y_528_; lean_object* v___x_554_; 
v___x_526_ = 1;
v___x_554_ = lean_array_uget_borrowed(v_as_515_, v_i_516_);
switch(lean_obj_tag(v___x_554_))
{
case 0:
{
lean_object* v_code_555_; 
v_code_555_ = lean_ctor_get(v___x_554_, 2);
lean_inc_ref(v_code_555_);
v___y_528_ = v_code_555_;
goto v___jp_527_;
}
case 1:
{
lean_object* v_code_556_; 
v_code_556_ = lean_ctor_get(v___x_554_, 1);
lean_inc_ref(v_code_556_);
v___y_528_ = v_code_556_;
goto v___jp_527_;
}
default: 
{
lean_object* v_code_557_; 
v_code_557_ = lean_ctor_get(v___x_554_, 0);
lean_inc_ref(v_code_557_);
v___y_528_ = v_code_557_;
goto v___jp_527_;
}
}
v___jp_527_:
{
lean_object* v___x_529_; 
v___x_529_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go(v_fvarId_514_, v___y_528_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_553_; 
v_a_530_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_553_ == 0)
{
v___x_532_ = v___x_529_;
v_isShared_533_ = v_isSharedCheck_553_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_529_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_553_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v_fst_534_; uint8_t v___x_535_; 
v_fst_534_ = lean_ctor_get(v_a_530_, 0);
v___x_535_ = lean_unbox(v_fst_534_);
if (v___x_535_ == 0)
{
lean_object* v_snd_536_; size_t v___x_537_; size_t v___x_538_; 
lean_del_object(v___x_532_);
v_snd_536_ = lean_ctor_get(v_a_530_, 1);
lean_inc(v_snd_536_);
lean_dec(v_a_530_);
v___x_537_ = ((size_t)1ULL);
v___x_538_ = lean_usize_add(v_i_516_, v___x_537_);
v_i_516_ = v___x_538_;
v___y_519_ = v_snd_536_;
goto _start;
}
else
{
lean_object* v_snd_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_551_; 
v_snd_540_ = lean_ctor_get(v_a_530_, 1);
v_isSharedCheck_551_ = !lean_is_exclusive(v_a_530_);
if (v_isSharedCheck_551_ == 0)
{
lean_object* v_unused_552_; 
v_unused_552_ = lean_ctor_get(v_a_530_, 0);
lean_dec(v_unused_552_);
v___x_542_ = v_a_530_;
v_isShared_543_ = v_isSharedCheck_551_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_snd_540_);
lean_dec(v_a_530_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_551_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_544_; lean_object* v___x_546_; 
v___x_544_ = lean_box(v___x_526_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 0, v___x_544_);
v___x_546_ = v___x_542_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_544_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v_snd_540_);
v___x_546_ = v_reuseFailAlloc_550_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
lean_object* v___x_548_; 
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 0, v___x_546_);
v___x_548_ = v___x_532_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v___x_546_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
}
}
}
else
{
return v___x_529_;
}
}
}
else
{
uint8_t v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_558_ = 0;
v___x_559_ = lean_box(v___x_558_);
v___x_560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
lean_ctor_set(v___x_560_, 1, v___y_519_);
v___x_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
return v___x_561_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__4___boxed(lean_object* v_fvarId_562_, lean_object* v_as_563_, lean_object* v_i_564_, lean_object* v_stop_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
size_t v_i_boxed_573_; size_t v_stop_boxed_574_; lean_object* v_res_575_; 
v_i_boxed_573_ = lean_unbox_usize(v_i_564_);
lean_dec(v_i_564_);
v_stop_boxed_574_ = lean_unbox_usize(v_stop_565_);
lean_dec(v_stop_565_);
v_res_575_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__4(v_fvarId_562_, v_as_563_, v_i_boxed_573_, v_stop_boxed_574_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec_ref(v___y_566_);
lean_dec_ref(v_as_563_);
lean_dec(v_fvarId_562_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___boxed(lean_object* v_fvarId_576_, lean_object* v_c_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go(v_fvarId_576_, v_c_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_);
lean_dec(v_a_583_);
lean_dec_ref(v_a_582_);
lean_dec(v_a_581_);
lean_dec_ref(v_a_580_);
lean_dec_ref(v_a_578_);
lean_dec(v_fvarId_576_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0(lean_object* v_00_u03b2_586_, lean_object* v_m_587_, lean_object* v_a_588_, lean_object* v_b_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0___redArg(v_m_587_, v_a_588_, v_b_589_);
return v___x_590_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1(lean_object* v_00_u03b2_591_, lean_object* v_m_592_, lean_object* v_a_593_){
_start:
{
uint8_t v___x_594_; 
v___x_594_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___redArg(v_m_592_, v_a_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___boxed(lean_object* v_00_u03b2_595_, lean_object* v_m_596_, lean_object* v_a_597_){
_start:
{
uint8_t v_res_598_; lean_object* v_r_599_; 
v_res_598_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1(v_00_u03b2_595_, v_m_596_, v_a_597_);
lean_dec(v_a_597_);
lean_dec_ref(v_m_596_);
v_r_599_ = lean_box(v_res_598_);
return v_r_599_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0(lean_object* v_00_u03b2_600_, lean_object* v_a_601_, lean_object* v_x_602_){
_start:
{
uint8_t v___x_603_; 
v___x_603_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0___redArg(v_a_601_, v_x_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_604_, lean_object* v_a_605_, lean_object* v_x_606_){
_start:
{
uint8_t v_res_607_; lean_object* v_r_608_; 
v_res_607_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0(v_00_u03b2_604_, v_a_605_, v_x_606_);
lean_dec(v_x_606_);
lean_dec(v_a_605_);
v_r_608_ = lean_box(v_res_607_);
return v_r_608_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1(lean_object* v_00_u03b2_609_, lean_object* v_data_610_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1___redArg(v_data_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_612_, lean_object* v_i_613_, lean_object* v_source_614_, lean_object* v_target_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1_spec__3___redArg(v_i_613_, v_source_614_, v_target_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_617_, lean_object* v_x_618_, lean_object* v_x_619_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1_spec__3_spec__7___redArg(v_x_618_, v_x_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_isFVarLiveIn(lean_object* v_c_621_, lean_object* v_fvarId_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_628_ = l_Lean_instEmptyCollectionFVarIdHashSet;
lean_inc_n(v_fvarId_622_, 2);
v___x_629_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_fvarId_622_);
v___x_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
lean_ctor_set(v___x_630_, 1, v_fvarId_622_);
v___x_631_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go(v_fvarId_622_, v_c_621_, v___x_630_, v___x_628_, v_a_623_, v_a_624_, v_a_625_, v_a_626_);
lean_dec_ref(v___x_630_);
lean_dec(v_fvarId_622_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_640_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_640_ == 0)
{
v___x_634_ = v___x_631_;
v_isShared_635_ = v_isSharedCheck_640_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_631_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_640_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v_fst_636_; lean_object* v___x_638_; 
v_fst_636_ = lean_ctor_get(v_a_632_, 0);
lean_inc(v_fst_636_);
lean_dec(v_a_632_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 0, v_fst_636_);
v___x_638_ = v___x_634_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_fst_636_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
else
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_648_; 
v_a_641_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_648_ == 0)
{
v___x_643_ = v___x_631_;
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_631_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
if (v_isShared_644_ == 0)
{
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_a_641_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_isFVarLiveIn___boxed(lean_object* v_c_649_, lean_object* v_fvarId_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Lean_Compiler_LCNF_Code_isFVarLiveIn(v_c_649_, v_fvarId_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
lean_dec(v_a_654_);
lean_dec_ref(v_a_653_);
lean_dec(v_a_652_);
lean_dec_ref(v_a_651_);
return v_res_656_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_DependsOn(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_LiveVars(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_DependsOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_LiveVars(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_DependsOn(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_LiveVars(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_DependsOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_LiveVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_LiveVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_LiveVars(builtin);
}
#ifdef __cplusplus
}
#endif
