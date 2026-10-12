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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
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
lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_visitVar___redArg(lean_object* v_fvarId_1_, lean_object* v_x_2_, lean_object* v_a_3_){
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
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_visitVar___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_1_ = stack[0].m_obj;
lean_object* v_x_2_ = stack[1].m_obj;
lean_object* v_a_3_ = stack[2].m_obj;
lean_object* v_res_9_;
v_res_9_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_visitVar___redArg(v_fvarId_1_, v_x_2_, v_a_3_);
stack->m_obj
 = v_res_9_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_visitVar___redArg___boxed(lean_object* v_fvarId_10_, lean_object* v_x_11_, lean_object* v_a_12_, lean_object* v_a_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_visitVar___redArg(v_fvarId_10_, v_x_11_, v_a_12_);
lean_dec(v_x_11_);
lean_dec(v_fvarId_10_);
return v_res_14_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_visitVar(lean_object* v_fvarId_15_, lean_object* v_x_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_){
_start:
{
uint8_t v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_24_ = l_Lean_instBEqFVarId_beq(v_x_16_, v_fvarId_15_);
v___x_25_ = lean_box(v___x_24_);
v___x_26_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
lean_ctor_set(v___x_26_, 1, v_a_18_);
v___x_27_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_27_, 0, v___x_26_);
return v___x_27_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_visitVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_15_ = stack[0].m_obj;
lean_object* v_x_16_ = stack[1].m_obj;
lean_object* v_a_17_ = stack[2].m_obj;
lean_object* v_a_18_ = stack[3].m_obj;
lean_object* v_a_19_ = stack[4].m_obj;
lean_object* v_a_20_ = stack[5].m_obj;
lean_object* v_a_21_ = stack[6].m_obj;
lean_object* v_a_22_ = stack[7].m_obj;
lean_object* v_res_28_;
v_res_28_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_visitVar(v_fvarId_15_, v_x_16_, v_a_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_, v_a_22_);
stack->m_obj
 = v_res_28_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_visitVar___boxed(lean_object* v_fvarId_29_, lean_object* v_x_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_visitVar(v_fvarId_29_, v_x_30_, v_a_31_, v_a_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_);
lean_dec(v_a_36_);
lean_dec_ref(v_a_35_);
lean_dec(v_a_34_);
lean_dec_ref(v_a_33_);
lean_dec_ref(v_a_31_);
lean_dec(v_x_30_);
lean_dec(v_fvarId_29_);
return v_res_38_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg(lean_object* v_jp_41_, lean_object* v_a_42_){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_44_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg___closed__0));
v___x_45_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg___closed__1));
v___x_46_ = lean_box(0);
v___x_47_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_44_, v___x_45_, v_a_42_, v_jp_41_, v___x_46_);
v___x_48_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_48_, 0, v___x_46_);
lean_ctor_set(v___x_48_, 1, v___x_47_);
v___x_49_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_49_, 0, v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_jp_41_ = stack[0].m_obj;
lean_object* v_a_42_ = stack[1].m_obj;
lean_object* v_res_50_;
v_res_50_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg(v_jp_41_, v_a_42_);
stack->m_obj
 = v_res_50_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg___boxed(lean_object* v_jp_51_, lean_object* v_a_52_, lean_object* v_a_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg(v_jp_51_, v_a_52_);
return v_res_54_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited(lean_object* v_jp_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_63_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg___closed__0));
v___x_64_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg___closed__1));
v___x_65_ = lean_box(0);
v___x_66_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_63_, v___x_64_, v_a_57_, v_jp_55_, v___x_65_);
v___x_67_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_67_, 0, v___x_65_);
lean_ctor_set(v___x_67_, 1, v___x_66_);
v___x_68_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited_0interp(lean_interpreter_value* stack)
{
lean_object* v_jp_55_ = stack[0].m_obj;
lean_object* v_a_56_ = stack[1].m_obj;
lean_object* v_a_57_ = stack[2].m_obj;
lean_object* v_a_58_ = stack[3].m_obj;
lean_object* v_a_59_ = stack[4].m_obj;
lean_object* v_a_60_ = stack[5].m_obj;
lean_object* v_a_61_ = stack[6].m_obj;
lean_object* v_res_69_;
v_res_69_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited(v_jp_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_);
stack->m_obj
 = v_res_69_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___boxed(lean_object* v_jp_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited(v_jp_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_, v_a_76_);
lean_dec(v_a_76_);
lean_dec_ref(v_a_75_);
lean_dec(v_a_74_);
lean_dec_ref(v_a_73_);
lean_dec_ref(v_a_71_);
return v_res_78_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__0(void){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_instMonadEIO___redArg();
return v___x_79_;
}
}
lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2(lean_object* v_msg_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v_toApplicative_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_167_; 
v___x_92_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__0);
v___x_93_ = l_StateRefT_x27_instMonad___redArg(v___x_92_);
v_toApplicative_94_ = lean_ctor_get(v___x_93_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_93_);
if (v_isSharedCheck_167_ == 0)
{
lean_object* v_unused_168_; 
v_unused_168_ = lean_ctor_get(v___x_93_, 1);
lean_dec(v_unused_168_);
v___x_96_ = v___x_93_;
v_isShared_97_ = v_isSharedCheck_167_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_toApplicative_94_);
lean_dec(v___x_93_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_167_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v_toFunctor_98_; lean_object* v_toSeq_99_; lean_object* v_toSeqLeft_100_; lean_object* v_toSeqRight_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_165_; 
v_toFunctor_98_ = lean_ctor_get(v_toApplicative_94_, 0);
v_toSeq_99_ = lean_ctor_get(v_toApplicative_94_, 2);
v_toSeqLeft_100_ = lean_ctor_get(v_toApplicative_94_, 3);
v_toSeqRight_101_ = lean_ctor_get(v_toApplicative_94_, 4);
v_isSharedCheck_165_ = !lean_is_exclusive(v_toApplicative_94_);
if (v_isSharedCheck_165_ == 0)
{
lean_object* v_unused_166_; 
v_unused_166_ = lean_ctor_get(v_toApplicative_94_, 1);
lean_dec(v_unused_166_);
v___x_103_ = v_toApplicative_94_;
v_isShared_104_ = v_isSharedCheck_165_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_toSeqRight_101_);
lean_inc(v_toSeqLeft_100_);
lean_inc(v_toSeq_99_);
lean_inc(v_toFunctor_98_);
lean_dec(v_toApplicative_94_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_165_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___f_105_; lean_object* v___f_106_; lean_object* v___f_107_; lean_object* v___f_108_; lean_object* v___x_109_; lean_object* v___f_110_; lean_object* v___f_111_; lean_object* v___f_112_; lean_object* v___x_114_; 
v___f_105_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__1));
v___f_106_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__2));
lean_inc_ref(v_toFunctor_98_);
v___f_107_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_107_, 0, v_toFunctor_98_);
v___f_108_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_108_, 0, v_toFunctor_98_);
v___x_109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_109_, 0, v___f_107_);
lean_ctor_set(v___x_109_, 1, v___f_108_);
v___f_110_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_110_, 0, v_toSeqRight_101_);
v___f_111_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_111_, 0, v_toSeqLeft_100_);
v___f_112_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_112_, 0, v_toSeq_99_);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 4, v___f_110_);
lean_ctor_set(v___x_103_, 3, v___f_111_);
lean_ctor_set(v___x_103_, 2, v___f_112_);
lean_ctor_set(v___x_103_, 1, v___f_105_);
lean_ctor_set(v___x_103_, 0, v___x_109_);
v___x_114_ = v___x_103_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v___x_109_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v___f_105_);
lean_ctor_set(v_reuseFailAlloc_164_, 2, v___f_112_);
lean_ctor_set(v_reuseFailAlloc_164_, 3, v___f_111_);
lean_ctor_set(v_reuseFailAlloc_164_, 4, v___f_110_);
v___x_114_ = v_reuseFailAlloc_164_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
lean_object* v___x_116_; 
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 1, v___f_106_);
lean_ctor_set(v___x_96_, 0, v___x_114_);
v___x_116_ = v___x_96_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_114_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v___f_106_);
v___x_116_ = v_reuseFailAlloc_163_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
lean_object* v___x_117_; lean_object* v_toApplicative_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_161_; 
v___x_117_ = l_StateRefT_x27_instMonad___redArg(v___x_116_);
v_toApplicative_118_ = lean_ctor_get(v___x_117_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_161_ == 0)
{
lean_object* v_unused_162_; 
v_unused_162_ = lean_ctor_get(v___x_117_, 1);
lean_dec(v_unused_162_);
v___x_120_ = v___x_117_;
v_isShared_121_ = v_isSharedCheck_161_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_toApplicative_118_);
lean_dec(v___x_117_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_161_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v_toFunctor_122_; lean_object* v_toSeq_123_; lean_object* v_toSeqLeft_124_; lean_object* v_toSeqRight_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_159_; 
v_toFunctor_122_ = lean_ctor_get(v_toApplicative_118_, 0);
v_toSeq_123_ = lean_ctor_get(v_toApplicative_118_, 2);
v_toSeqLeft_124_ = lean_ctor_get(v_toApplicative_118_, 3);
v_toSeqRight_125_ = lean_ctor_get(v_toApplicative_118_, 4);
v_isSharedCheck_159_ = !lean_is_exclusive(v_toApplicative_118_);
if (v_isSharedCheck_159_ == 0)
{
lean_object* v_unused_160_; 
v_unused_160_ = lean_ctor_get(v_toApplicative_118_, 1);
lean_dec(v_unused_160_);
v___x_127_ = v_toApplicative_118_;
v_isShared_128_ = v_isSharedCheck_159_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_toSeqRight_125_);
lean_inc(v_toSeqLeft_124_);
lean_inc(v_toSeq_123_);
lean_inc(v_toFunctor_122_);
lean_dec(v_toApplicative_118_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_159_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___f_129_; lean_object* v___f_130_; lean_object* v___f_131_; lean_object* v___f_132_; lean_object* v___x_133_; lean_object* v___f_134_; lean_object* v___f_135_; lean_object* v___f_136_; lean_object* v___x_138_; 
v___f_129_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__3));
v___f_130_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__4));
lean_inc_ref(v_toFunctor_122_);
v___f_131_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_131_, 0, v_toFunctor_122_);
v___f_132_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_132_, 0, v_toFunctor_122_);
v___x_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_133_, 0, v___f_131_);
lean_ctor_set(v___x_133_, 1, v___f_132_);
v___f_134_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_134_, 0, v_toSeqRight_125_);
v___f_135_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_135_, 0, v_toSeqLeft_124_);
v___f_136_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_136_, 0, v_toSeq_123_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 4, v___f_134_);
lean_ctor_set(v___x_127_, 3, v___f_135_);
lean_ctor_set(v___x_127_, 2, v___f_136_);
lean_ctor_set(v___x_127_, 1, v___f_129_);
lean_ctor_set(v___x_127_, 0, v___x_133_);
v___x_138_ = v___x_127_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_133_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v___f_129_);
lean_ctor_set(v_reuseFailAlloc_158_, 2, v___f_136_);
lean_ctor_set(v_reuseFailAlloc_158_, 3, v___f_135_);
lean_ctor_set(v_reuseFailAlloc_158_, 4, v___f_134_);
v___x_138_ = v_reuseFailAlloc_158_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
lean_object* v___x_140_; 
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 1, v___f_130_);
lean_ctor_set(v___x_120_, 0, v___x_138_);
v___x_140_ = v___x_120_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v___x_138_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v___f_130_);
v___x_140_ = v_reuseFailAlloc_157_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
lean_object* v___f_141_; lean_object* v___f_142_; lean_object* v___f_143_; lean_object* v___f_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; uint8_t v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___f_154_; lean_object* v___x_16076__overap_155_; lean_object* v___x_156_; 
lean_inc_ref_n(v___x_140_, 6);
v___f_141_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_141_, 0, v___x_140_);
v___f_142_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_142_, 0, v___x_140_);
v___f_143_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_143_, 0, v___x_140_);
v___f_144_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_144_, 0, v___x_140_);
v___x_145_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_145_, 0, lean_box(0));
lean_closure_set(v___x_145_, 1, lean_box(0));
lean_closure_set(v___x_145_, 2, v___x_140_);
v___x_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
lean_ctor_set(v___x_146_, 1, v___f_141_);
v___x_147_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_147_, 0, lean_box(0));
lean_closure_set(v___x_147_, 1, lean_box(0));
lean_closure_set(v___x_147_, 2, v___x_140_);
v___x_148_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_148_, 0, v___x_146_);
lean_ctor_set(v___x_148_, 1, v___x_147_);
lean_ctor_set(v___x_148_, 2, v___f_142_);
lean_ctor_set(v___x_148_, 3, v___f_143_);
lean_ctor_set(v___x_148_, 4, v___f_144_);
v___x_149_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_149_, 0, lean_box(0));
lean_closure_set(v___x_149_, 1, lean_box(0));
lean_closure_set(v___x_149_, 2, v___x_140_);
v___x_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_150_, 0, v___x_148_);
lean_ctor_set(v___x_150_, 1, v___x_149_);
v___x_151_ = 0;
v___x_152_ = lean_box(v___x_151_);
v___x_153_ = l_instInhabitedOfMonad___redArg(v___x_150_, v___x_152_);
v___f_154_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_154_, 0, v___x_153_);
v___x_16076__overap_155_ = lean_panic_fn_borrowed(v___f_154_, v_msg_84_);
lean_dec_ref(v___f_154_);
lean_inc(v___y_90_);
lean_inc_ref(v___y_89_);
lean_inc(v___y_88_);
lean_inc_ref(v___y_87_);
lean_inc_ref(v___y_85_);
v___x_156_ = lean_apply_7(v___x_16076__overap_155_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, lean_box(0));
return v___x_156_;
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
LEAN_EXPORT void l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_84_ = stack[0].m_obj;
lean_object* v___y_85_ = stack[1].m_obj;
lean_object* v___y_86_ = stack[2].m_obj;
lean_object* v___y_87_ = stack[3].m_obj;
lean_object* v___y_88_ = stack[4].m_obj;
lean_object* v___y_89_ = stack[5].m_obj;
lean_object* v___y_90_ = stack[6].m_obj;
lean_object* v_res_169_;
v_res_169_ = l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2(v_msg_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_);
stack->m_obj
 = v_res_169_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___boxed(lean_object* v_msg_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2(v_msg_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec_ref(v___y_171_);
return v_res_178_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0___redArg(lean_object* v_a_179_, lean_object* v_x_180_){
_start:
{
if (lean_obj_tag(v_x_180_) == 0)
{
uint8_t v___x_181_; 
v___x_181_ = 0;
return v___x_181_;
}
else
{
lean_object* v_key_182_; lean_object* v_tail_183_; uint8_t v___x_184_; 
v_key_182_ = lean_ctor_get(v_x_180_, 0);
v_tail_183_ = lean_ctor_get(v_x_180_, 2);
v___x_184_ = l_Lean_instBEqFVarId_beq(v_key_182_, v_a_179_);
if (v___x_184_ == 0)
{
v_x_180_ = v_tail_183_;
goto _start;
}
else
{
return v___x_184_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_179_ = stack[0].m_obj;
lean_object* v_x_180_ = stack[1].m_obj;
uint8_t v_res_186_;
v_res_186_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0___redArg(v_a_179_, v_x_180_);
stack->m_num = v_res_186_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0___redArg___boxed(lean_object* v_a_187_, lean_object* v_x_188_){
_start:
{
uint8_t v_res_189_; lean_object* v_r_190_; 
v_res_189_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0___redArg(v_a_187_, v_x_188_);
lean_dec(v_x_188_);
lean_dec(v_a_187_);
v_r_190_ = lean_box(v_res_189_);
return v_r_190_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___redArg(lean_object* v_m_191_, lean_object* v_a_192_){
_start:
{
lean_object* v_buckets_193_; lean_object* v___x_194_; uint64_t v___x_195_; uint64_t v___x_196_; uint64_t v___x_197_; uint64_t v_fold_198_; uint64_t v___x_199_; uint64_t v___x_200_; uint64_t v___x_201_; size_t v___x_202_; size_t v___x_203_; size_t v___x_204_; size_t v___x_205_; size_t v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; 
v_buckets_193_ = lean_ctor_get(v_m_191_, 1);
v___x_194_ = lean_array_get_size(v_buckets_193_);
v___x_195_ = l_Lean_instHashableFVarId_hash(v_a_192_);
v___x_196_ = 32ULL;
v___x_197_ = lean_uint64_shift_right(v___x_195_, v___x_196_);
v_fold_198_ = lean_uint64_xor(v___x_195_, v___x_197_);
v___x_199_ = 16ULL;
v___x_200_ = lean_uint64_shift_right(v_fold_198_, v___x_199_);
v___x_201_ = lean_uint64_xor(v_fold_198_, v___x_200_);
v___x_202_ = lean_uint64_to_usize(v___x_201_);
v___x_203_ = lean_usize_of_nat(v___x_194_);
v___x_204_ = ((size_t)1ULL);
v___x_205_ = lean_usize_sub(v___x_203_, v___x_204_);
v___x_206_ = lean_usize_land(v___x_202_, v___x_205_);
v___x_207_ = lean_array_uget_borrowed(v_buckets_193_, v___x_206_);
v___x_208_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0___redArg(v_a_192_, v___x_207_);
return v___x_208_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_191_ = stack[0].m_obj;
lean_object* v_a_192_ = stack[1].m_obj;
uint8_t v_res_209_;
v_res_209_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___redArg(v_m_191_, v_a_192_);
stack->m_num = v_res_209_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___redArg___boxed(lean_object* v_m_210_, lean_object* v_a_211_){
_start:
{
uint8_t v_res_212_; lean_object* v_r_213_; 
v_res_212_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___redArg(v_m_210_, v_a_211_);
lean_dec(v_a_211_);
lean_dec_ref(v_m_210_);
v_r_213_ = lean_box(v_res_212_);
return v_r_213_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3(lean_object* v_a_214_, lean_object* v_as_215_, size_t v_i_216_, size_t v_stop_217_){
_start:
{
uint8_t v___x_218_; 
v___x_218_ = lean_usize_dec_eq(v_i_216_, v_stop_217_);
if (v___x_218_ == 0)
{
lean_object* v_targetSet_219_; lean_object* v___x_220_; uint8_t v___x_221_; uint8_t v___x_222_; 
v_targetSet_219_ = lean_ctor_get(v_a_214_, 0);
v___x_220_ = lean_array_uget_borrowed(v_as_215_, v_i_216_);
v___x_221_ = 1;
v___x_222_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn(v___x_221_, v___x_220_, v_targetSet_219_);
if (v___x_222_ == 0)
{
size_t v___x_223_; size_t v___x_224_; 
v___x_223_ = ((size_t)1ULL);
v___x_224_ = lean_usize_add(v_i_216_, v___x_223_);
v_i_216_ = v___x_224_;
goto _start;
}
else
{
return v___x_222_;
}
}
else
{
uint8_t v___x_226_; 
v___x_226_ = 0;
return v___x_226_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_214_ = stack[0].m_obj;
lean_object* v_as_215_ = stack[1].m_obj;
size_t v_i_216_ = stack[2].m_num;
size_t v_stop_217_ = stack[3].m_num;
uint8_t v_res_227_;
v_res_227_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3(v_a_214_, v_as_215_, v_i_216_, v_stop_217_);
stack->m_num = v_res_227_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3___boxed(lean_object* v_a_228_, lean_object* v_as_229_, lean_object* v_i_230_, lean_object* v_stop_231_){
_start:
{
size_t v_i_boxed_232_; size_t v_stop_boxed_233_; uint8_t v_res_234_; lean_object* v_r_235_; 
v_i_boxed_232_ = lean_unbox_usize(v_i_230_);
lean_dec(v_i_230_);
v_stop_boxed_233_ = lean_unbox_usize(v_stop_231_);
lean_dec(v_stop_231_);
v_res_234_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3(v_a_228_, v_as_229_, v_i_boxed_232_, v_stop_boxed_233_);
lean_dec_ref(v_as_229_);
lean_dec_ref(v_a_228_);
v_r_235_ = lean_box(v_res_234_);
return v_r_235_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1_spec__3_spec__7___redArg(lean_object* v_x_236_, lean_object* v_x_237_){
_start:
{
if (lean_obj_tag(v_x_237_) == 0)
{
return v_x_236_;
}
else
{
lean_object* v_key_238_; lean_object* v_value_239_; lean_object* v_tail_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_263_; 
v_key_238_ = lean_ctor_get(v_x_237_, 0);
v_value_239_ = lean_ctor_get(v_x_237_, 1);
v_tail_240_ = lean_ctor_get(v_x_237_, 2);
v_isSharedCheck_263_ = !lean_is_exclusive(v_x_237_);
if (v_isSharedCheck_263_ == 0)
{
v___x_242_ = v_x_237_;
v_isShared_243_ = v_isSharedCheck_263_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_tail_240_);
lean_inc(v_value_239_);
lean_inc(v_key_238_);
lean_dec(v_x_237_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_263_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_244_; uint64_t v___x_245_; uint64_t v___x_246_; uint64_t v___x_247_; uint64_t v_fold_248_; uint64_t v___x_249_; uint64_t v___x_250_; uint64_t v___x_251_; size_t v___x_252_; size_t v___x_253_; size_t v___x_254_; size_t v___x_255_; size_t v___x_256_; lean_object* v___x_257_; lean_object* v___x_259_; 
v___x_244_ = lean_array_get_size(v_x_236_);
v___x_245_ = l_Lean_instHashableFVarId_hash(v_key_238_);
v___x_246_ = 32ULL;
v___x_247_ = lean_uint64_shift_right(v___x_245_, v___x_246_);
v_fold_248_ = lean_uint64_xor(v___x_245_, v___x_247_);
v___x_249_ = 16ULL;
v___x_250_ = lean_uint64_shift_right(v_fold_248_, v___x_249_);
v___x_251_ = lean_uint64_xor(v_fold_248_, v___x_250_);
v___x_252_ = lean_uint64_to_usize(v___x_251_);
v___x_253_ = lean_usize_of_nat(v___x_244_);
v___x_254_ = ((size_t)1ULL);
v___x_255_ = lean_usize_sub(v___x_253_, v___x_254_);
v___x_256_ = lean_usize_land(v___x_252_, v___x_255_);
v___x_257_ = lean_array_uget_borrowed(v_x_236_, v___x_256_);
lean_inc(v___x_257_);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 2, v___x_257_);
v___x_259_ = v___x_242_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_key_238_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v_value_239_);
lean_ctor_set(v_reuseFailAlloc_262_, 2, v___x_257_);
v___x_259_ = v_reuseFailAlloc_262_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
lean_object* v___x_260_; 
v___x_260_ = lean_array_uset(v_x_236_, v___x_256_, v___x_259_);
v_x_236_ = v___x_260_;
v_x_237_ = v_tail_240_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1_spec__3___redArg(lean_object* v_i_264_, lean_object* v_source_265_, lean_object* v_target_266_){
_start:
{
lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_267_ = lean_array_get_size(v_source_265_);
v___x_268_ = lean_nat_dec_lt(v_i_264_, v___x_267_);
if (v___x_268_ == 0)
{
lean_dec_ref(v_source_265_);
lean_dec(v_i_264_);
return v_target_266_;
}
else
{
lean_object* v_es_269_; lean_object* v___x_270_; lean_object* v_source_271_; lean_object* v_target_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v_es_269_ = lean_array_fget(v_source_265_, v_i_264_);
v___x_270_ = lean_box(0);
v_source_271_ = lean_array_fset(v_source_265_, v_i_264_, v___x_270_);
v_target_272_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1_spec__3_spec__7___redArg(v_target_266_, v_es_269_);
v___x_273_ = lean_unsigned_to_nat(1u);
v___x_274_ = lean_nat_add(v_i_264_, v___x_273_);
lean_dec(v_i_264_);
v_i_264_ = v___x_274_;
v_source_265_ = v_source_271_;
v_target_266_ = v_target_272_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1___redArg(lean_object* v_data_276_){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v_nbuckets_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_277_ = lean_array_get_size(v_data_276_);
v___x_278_ = lean_unsigned_to_nat(2u);
v_nbuckets_279_ = lean_nat_mul(v___x_277_, v___x_278_);
v___x_280_ = lean_unsigned_to_nat(0u);
v___x_281_ = lean_box(0);
v___x_282_ = lean_mk_array(v_nbuckets_279_, v___x_281_);
v___x_283_ = lean_array_propagate_mark(v_data_276_, v___x_282_);
v___x_284_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1_spec__3___redArg(v___x_280_, v_data_276_, v___x_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0___redArg(lean_object* v_m_285_, lean_object* v_a_286_, lean_object* v_b_287_){
_start:
{
lean_object* v_size_288_; lean_object* v_buckets_289_; lean_object* v___x_290_; uint64_t v___x_291_; uint64_t v___x_292_; uint64_t v___x_293_; uint64_t v_fold_294_; uint64_t v___x_295_; uint64_t v___x_296_; uint64_t v___x_297_; size_t v___x_298_; size_t v___x_299_; size_t v___x_300_; size_t v___x_301_; size_t v___x_302_; lean_object* v_bkt_303_; uint8_t v___x_304_; 
v_size_288_ = lean_ctor_get(v_m_285_, 0);
v_buckets_289_ = lean_ctor_get(v_m_285_, 1);
v___x_290_ = lean_array_get_size(v_buckets_289_);
v___x_291_ = l_Lean_instHashableFVarId_hash(v_a_286_);
v___x_292_ = 32ULL;
v___x_293_ = lean_uint64_shift_right(v___x_291_, v___x_292_);
v_fold_294_ = lean_uint64_xor(v___x_291_, v___x_293_);
v___x_295_ = 16ULL;
v___x_296_ = lean_uint64_shift_right(v_fold_294_, v___x_295_);
v___x_297_ = lean_uint64_xor(v_fold_294_, v___x_296_);
v___x_298_ = lean_uint64_to_usize(v___x_297_);
v___x_299_ = lean_usize_of_nat(v___x_290_);
v___x_300_ = ((size_t)1ULL);
v___x_301_ = lean_usize_sub(v___x_299_, v___x_300_);
v___x_302_ = lean_usize_land(v___x_298_, v___x_301_);
v_bkt_303_ = lean_array_uget_borrowed(v_buckets_289_, v___x_302_);
v___x_304_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0___redArg(v_a_286_, v_bkt_303_);
if (v___x_304_ == 0)
{
lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_325_; 
lean_inc_ref(v_buckets_289_);
lean_inc(v_size_288_);
v_isSharedCheck_325_ = !lean_is_exclusive(v_m_285_);
if (v_isSharedCheck_325_ == 0)
{
lean_object* v_unused_326_; lean_object* v_unused_327_; 
v_unused_326_ = lean_ctor_get(v_m_285_, 1);
lean_dec(v_unused_326_);
v_unused_327_ = lean_ctor_get(v_m_285_, 0);
lean_dec(v_unused_327_);
v___x_306_ = v_m_285_;
v_isShared_307_ = v_isSharedCheck_325_;
goto v_resetjp_305_;
}
else
{
lean_dec(v_m_285_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_325_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_308_; lean_object* v_size_x27_309_; lean_object* v___x_310_; lean_object* v_buckets_x27_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_308_ = lean_unsigned_to_nat(1u);
v_size_x27_309_ = lean_nat_add(v_size_288_, v___x_308_);
lean_dec(v_size_288_);
lean_inc(v_bkt_303_);
v___x_310_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_310_, 0, v_a_286_);
lean_ctor_set(v___x_310_, 1, v_b_287_);
lean_ctor_set(v___x_310_, 2, v_bkt_303_);
v_buckets_x27_311_ = lean_array_uset(v_buckets_289_, v___x_302_, v___x_310_);
v___x_312_ = lean_unsigned_to_nat(4u);
v___x_313_ = lean_nat_mul(v_size_x27_309_, v___x_312_);
v___x_314_ = lean_unsigned_to_nat(3u);
v___x_315_ = lean_nat_div(v___x_313_, v___x_314_);
lean_dec(v___x_313_);
v___x_316_ = lean_array_get_size(v_buckets_x27_311_);
v___x_317_ = lean_nat_dec_le(v___x_315_, v___x_316_);
lean_dec(v___x_315_);
if (v___x_317_ == 0)
{
lean_object* v_val_318_; lean_object* v___x_320_; 
v_val_318_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1___redArg(v_buckets_x27_311_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 1, v_val_318_);
lean_ctor_set(v___x_306_, 0, v_size_x27_309_);
v___x_320_ = v___x_306_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_size_x27_309_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v_val_318_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
else
{
lean_object* v___x_323_; 
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 1, v_buckets_x27_311_);
lean_ctor_set(v___x_306_, 0, v_size_x27_309_);
v___x_323_ = v___x_306_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_size_x27_309_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v_buckets_x27_311_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
else
{
lean_dec(v_b_287_);
lean_dec(v_a_286_);
return v_m_285_;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__3(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_331_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__2));
v___x_332_ = lean_unsigned_to_nat(48u);
v___x_333_ = lean_unsigned_to_nat(76u);
v___x_334_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__1));
v___x_335_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__0));
v___x_336_ = l_mkPanicMessageWithDecl(v___x_335_, v___x_334_, v___x_333_, v___x_332_, v___x_331_);
return v___x_336_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go(lean_object* v_fvarId_337_, lean_object* v_c_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_){
_start:
{
switch(lean_obj_tag(v_c_338_))
{
case 0:
{
lean_object* v_decl_346_; lean_object* v_k_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_360_; 
v_decl_346_ = lean_ctor_get(v_c_338_, 0);
v_k_347_ = lean_ctor_get(v_c_338_, 1);
v_isSharedCheck_360_ = !lean_is_exclusive(v_c_338_);
if (v_isSharedCheck_360_ == 0)
{
v___x_349_ = v_c_338_;
v_isShared_350_ = v_isSharedCheck_360_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_k_347_);
lean_inc(v_decl_346_);
lean_dec(v_c_338_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_360_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v_targetSet_351_; uint8_t v___x_352_; uint8_t v___x_353_; 
v_targetSet_351_ = lean_ctor_get(v_a_339_, 0);
v___x_352_ = 1;
v___x_353_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn(v___x_352_, v_decl_346_, v_targetSet_351_);
lean_dec_ref(v_decl_346_);
if (v___x_353_ == 0)
{
lean_del_object(v___x_349_);
v_c_338_ = v_k_347_;
goto _start;
}
else
{
lean_object* v___x_355_; lean_object* v___x_357_; 
lean_dec_ref(v_k_347_);
v___x_355_ = lean_box(v___x_353_);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 1, v_a_340_);
lean_ctor_set(v___x_349_, 0, v___x_355_);
v___x_357_ = v___x_349_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v___x_355_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v_a_340_);
v___x_357_ = v_reuseFailAlloc_359_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
lean_object* v___x_358_; 
v___x_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
return v___x_358_;
}
}
}
}
case 2:
{
lean_object* v_decl_361_; lean_object* v_k_362_; lean_object* v_fvarId_363_; lean_object* v_value_364_; lean_object* v___x_365_; 
v_decl_361_ = lean_ctor_get(v_c_338_, 0);
lean_inc_ref(v_decl_361_);
v_k_362_ = lean_ctor_get(v_c_338_, 1);
lean_inc_ref(v_k_362_);
lean_dec_ref_known(v_c_338_, 2);
v_fvarId_363_ = lean_ctor_get(v_decl_361_, 0);
lean_inc(v_fvarId_363_);
v_value_364_ = lean_ctor_get(v_decl_361_, 4);
lean_inc_ref(v_value_364_);
lean_dec_ref(v_decl_361_);
v___x_365_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go(v_fvarId_337_, v_value_364_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v_a_366_; lean_object* v_fst_367_; uint8_t v___x_368_; 
v_a_366_ = lean_ctor_get(v___x_365_, 0);
v_fst_367_ = lean_ctor_get(v_a_366_, 0);
v___x_368_ = lean_unbox(v_fst_367_);
if (v___x_368_ == 0)
{
lean_object* v_snd_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
lean_inc(v_a_366_);
lean_dec_ref_known(v___x_365_, 1);
v_snd_369_ = lean_ctor_get(v_a_366_, 1);
lean_inc(v_snd_369_);
lean_dec(v_a_366_);
v___x_370_ = lean_box(0);
v___x_371_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0___redArg(v_snd_369_, v_fvarId_363_, v___x_370_);
v_c_338_ = v_k_362_;
v_a_340_ = v___x_371_;
goto _start;
}
else
{
lean_dec(v_fvarId_363_);
lean_dec_ref(v_k_362_);
return v___x_365_;
}
}
else
{
lean_dec(v_fvarId_363_);
lean_dec_ref(v_k_362_);
return v___x_365_;
}
}
case 3:
{
lean_object* v_fvarId_373_; lean_object* v_args_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_413_; 
v_fvarId_373_ = lean_ctor_get(v_c_338_, 0);
v_args_374_ = lean_ctor_get(v_c_338_, 1);
v_isSharedCheck_413_ = !lean_is_exclusive(v_c_338_);
if (v_isSharedCheck_413_ == 0)
{
v___x_376_ = v_c_338_;
v_isShared_377_ = v_isSharedCheck_413_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_args_374_);
lean_inc(v_fvarId_373_);
lean_dec(v_c_338_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_413_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
uint8_t v___y_379_; lean_object* v___x_404_; lean_object* v___x_405_; uint8_t v___x_406_; 
v___x_404_ = lean_unsigned_to_nat(0u);
v___x_405_ = lean_array_get_size(v_args_374_);
v___x_406_ = lean_nat_dec_lt(v___x_404_, v___x_405_);
if (v___x_406_ == 0)
{
lean_dec_ref(v_args_374_);
v___y_379_ = v___x_406_;
goto v___jp_378_;
}
else
{
if (v___x_406_ == 0)
{
lean_dec_ref(v_args_374_);
v___y_379_ = v___x_406_;
goto v___jp_378_;
}
else
{
size_t v___x_407_; size_t v___x_408_; uint8_t v___x_409_; 
v___x_407_ = ((size_t)0ULL);
v___x_408_ = lean_usize_of_nat(v___x_405_);
v___x_409_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3(v_a_339_, v_args_374_, v___x_407_, v___x_408_);
lean_dec_ref(v_args_374_);
if (v___x_409_ == 0)
{
v___y_379_ = v___x_409_;
goto v___jp_378_;
}
else
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
lean_del_object(v___x_376_);
lean_dec(v_fvarId_373_);
v___x_410_ = lean_box(v___x_409_);
v___x_411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
lean_ctor_set(v___x_411_, 1, v_a_340_);
v___x_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
return v___x_412_;
}
}
}
v___jp_378_:
{
uint8_t v___x_380_; 
v___x_380_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___redArg(v_a_340_, v_fvarId_373_);
if (v___x_380_ == 0)
{
uint8_t v___x_381_; lean_object* v___x_382_; 
lean_del_object(v___x_376_);
v___x_381_ = 1;
v___x_382_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_381_, v_fvarId_373_, v_a_342_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v_a_383_; 
v_a_383_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_a_383_);
lean_dec_ref_known(v___x_382_, 1);
if (lean_obj_tag(v_a_383_) == 1)
{
lean_object* v_val_384_; lean_object* v_value_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v_val_384_ = lean_ctor_get(v_a_383_, 0);
lean_inc(v_val_384_);
lean_dec_ref_known(v_a_383_, 1);
v_value_385_ = lean_ctor_get(v_val_384_, 4);
lean_inc_ref(v_value_385_);
lean_dec(v_val_384_);
v___x_386_ = lean_box(0);
v___x_387_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0___redArg(v_a_340_, v_fvarId_373_, v___x_386_);
v_c_338_ = v_value_385_;
v_a_340_ = v___x_387_;
goto _start;
}
else
{
lean_object* v___x_389_; lean_object* v___x_390_; 
lean_dec(v_a_383_);
lean_dec(v_fvarId_373_);
v___x_389_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__3, &l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__3);
v___x_390_ = l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2(v___x_389_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_);
return v___x_390_;
}
}
else
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
lean_dec(v_fvarId_373_);
lean_dec_ref(v_a_340_);
v_a_391_ = lean_ctor_get(v___x_382_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___x_382_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_382_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_396_; 
if (v_isShared_394_ == 0)
{
v___x_396_ = v___x_393_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_391_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
else
{
lean_object* v___x_399_; lean_object* v___x_401_; 
lean_dec(v_fvarId_373_);
v___x_399_ = lean_box(v___y_379_);
if (v_isShared_377_ == 0)
{
lean_ctor_set_tag(v___x_376_, 0);
lean_ctor_set(v___x_376_, 1, v_a_340_);
lean_ctor_set(v___x_376_, 0, v___x_399_);
v___x_401_ = v___x_376_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_399_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v_a_340_);
v___x_401_ = v_reuseFailAlloc_403_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
lean_object* v___x_402_; 
v___x_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
return v___x_402_;
}
}
}
}
}
case 4:
{
lean_object* v_cases_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_442_; 
v_cases_414_ = lean_ctor_get(v_c_338_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v_c_338_);
if (v_isSharedCheck_442_ == 0)
{
v___x_416_ = v_c_338_;
v_isShared_417_ = v_isSharedCheck_442_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_cases_414_);
lean_dec(v_c_338_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_442_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v_discr_418_; lean_object* v_alts_419_; uint8_t v___x_420_; 
v_discr_418_ = lean_ctor_get(v_cases_414_, 2);
lean_inc(v_discr_418_);
v_alts_419_ = lean_ctor_get(v_cases_414_, 3);
lean_inc_ref(v_alts_419_);
lean_dec_ref(v_cases_414_);
v___x_420_ = l_Lean_instBEqFVarId_beq(v_discr_418_, v_fvarId_337_);
lean_dec(v_discr_418_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; lean_object* v___x_422_; uint8_t v___x_423_; 
v___x_421_ = lean_unsigned_to_nat(0u);
v___x_422_ = lean_array_get_size(v_alts_419_);
v___x_423_ = lean_nat_dec_lt(v___x_421_, v___x_422_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_427_; 
lean_dec_ref(v_alts_419_);
v___x_424_ = lean_box(v___x_423_);
v___x_425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
lean_ctor_set(v___x_425_, 1, v_a_340_);
if (v_isShared_417_ == 0)
{
lean_ctor_set_tag(v___x_416_, 0);
lean_ctor_set(v___x_416_, 0, v___x_425_);
v___x_427_ = v___x_416_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_425_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
else
{
if (v___x_423_ == 0)
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_432_; 
lean_dec_ref(v_alts_419_);
v___x_429_ = lean_box(v___x_423_);
v___x_430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
lean_ctor_set(v___x_430_, 1, v_a_340_);
if (v_isShared_417_ == 0)
{
lean_ctor_set_tag(v___x_416_, 0);
lean_ctor_set(v___x_416_, 0, v___x_430_);
v___x_432_ = v___x_416_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_430_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
else
{
size_t v___x_434_; size_t v___x_435_; lean_object* v___x_436_; 
lean_del_object(v___x_416_);
v___x_434_ = ((size_t)0ULL);
v___x_435_ = lean_usize_of_nat(v___x_422_);
v___x_436_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__4(v_fvarId_337_, v_alts_419_, v___x_434_, v___x_435_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_);
lean_dec_ref(v_alts_419_);
return v___x_436_;
}
}
}
else
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_440_; 
lean_dec_ref(v_alts_419_);
v___x_437_ = lean_box(v___x_420_);
v___x_438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
lean_ctor_set(v___x_438_, 1, v_a_340_);
if (v_isShared_417_ == 0)
{
lean_ctor_set_tag(v___x_416_, 0);
lean_ctor_set(v___x_416_, 0, v___x_438_);
v___x_440_ = v___x_416_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_438_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_453_; 
v_fvarId_443_ = lean_ctor_get(v_c_338_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v_c_338_);
if (v_isSharedCheck_453_ == 0)
{
v___x_445_ = v_c_338_;
v_isShared_446_ = v_isSharedCheck_453_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_fvarId_443_);
lean_dec(v_c_338_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_453_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
uint8_t v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_451_; 
v___x_447_ = l_Lean_instBEqFVarId_beq(v_fvarId_443_, v_fvarId_337_);
lean_dec(v_fvarId_443_);
v___x_448_ = lean_box(v___x_447_);
v___x_449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
lean_ctor_set(v___x_449_, 1, v_a_340_);
if (v_isShared_446_ == 0)
{
lean_ctor_set_tag(v___x_445_, 0);
lean_ctor_set(v___x_445_, 0, v___x_449_);
v___x_451_ = v___x_445_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_449_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
case 6:
{
lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_463_; 
v_isSharedCheck_463_ = !lean_is_exclusive(v_c_338_);
if (v_isSharedCheck_463_ == 0)
{
lean_object* v_unused_464_; 
v_unused_464_ = lean_ctor_get(v_c_338_, 0);
lean_dec(v_unused_464_);
v___x_455_ = v_c_338_;
v_isShared_456_ = v_isSharedCheck_463_;
goto v_resetjp_454_;
}
else
{
lean_dec(v_c_338_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_463_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
uint8_t v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_461_; 
v___x_457_ = 0;
v___x_458_ = lean_box(v___x_457_);
v___x_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
lean_ctor_set(v___x_459_, 1, v_a_340_);
if (v_isShared_456_ == 0)
{
lean_ctor_set_tag(v___x_455_, 0);
lean_ctor_set(v___x_455_, 0, v___x_459_);
v___x_461_ = v___x_455_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_459_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
case 7:
{
lean_object* v_fvarId_465_; lean_object* v_y_466_; lean_object* v_k_467_; uint8_t v___x_468_; 
v_fvarId_465_ = lean_ctor_get(v_c_338_, 0);
lean_inc(v_fvarId_465_);
v_y_466_ = lean_ctor_get(v_c_338_, 2);
lean_inc(v_y_466_);
v_k_467_ = lean_ctor_get(v_c_338_, 3);
lean_inc_ref(v_k_467_);
lean_dec_ref_known(v_c_338_, 4);
v___x_468_ = l_Lean_instBEqFVarId_beq(v_fvarId_465_, v_fvarId_337_);
lean_dec(v_fvarId_465_);
if (v___x_468_ == 0)
{
lean_object* v_targetSet_469_; uint8_t v___x_470_; uint8_t v___x_471_; 
v_targetSet_469_ = lean_ctor_get(v_a_339_, 0);
v___x_470_ = 1;
v___x_471_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn(v___x_470_, v_y_466_, v_targetSet_469_);
lean_dec(v_y_466_);
if (v___x_471_ == 0)
{
v_c_338_ = v_k_467_;
goto _start;
}
else
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
lean_dec_ref(v_k_467_);
v___x_473_ = lean_box(v___x_471_);
v___x_474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
lean_ctor_set(v___x_474_, 1, v_a_340_);
v___x_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
return v___x_475_;
}
}
else
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
lean_dec_ref(v_k_467_);
lean_dec(v_y_466_);
v___x_476_ = lean_box(v___x_468_);
v___x_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
lean_ctor_set(v___x_477_, 1, v_a_340_);
v___x_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
return v___x_478_;
}
}
case 8:
{
lean_object* v_fvarId_479_; lean_object* v_y_480_; lean_object* v_k_481_; uint8_t v___x_482_; 
v_fvarId_479_ = lean_ctor_get(v_c_338_, 0);
lean_inc(v_fvarId_479_);
v_y_480_ = lean_ctor_get(v_c_338_, 2);
lean_inc(v_y_480_);
v_k_481_ = lean_ctor_get(v_c_338_, 3);
lean_inc_ref(v_k_481_);
lean_dec_ref_known(v_c_338_, 4);
v___x_482_ = l_Lean_instBEqFVarId_beq(v_fvarId_479_, v_fvarId_337_);
lean_dec(v_fvarId_479_);
if (v___x_482_ == 0)
{
uint8_t v___x_483_; 
v___x_483_ = l_Lean_instBEqFVarId_beq(v_y_480_, v_fvarId_337_);
lean_dec(v_y_480_);
if (v___x_483_ == 0)
{
v_c_338_ = v_k_481_;
goto _start;
}
else
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
lean_dec_ref(v_k_481_);
v___x_485_ = lean_box(v___x_483_);
v___x_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
lean_ctor_set(v___x_486_, 1, v_a_340_);
v___x_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
return v___x_487_;
}
}
else
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
lean_dec_ref(v_k_481_);
lean_dec(v_y_480_);
v___x_488_ = lean_box(v___x_482_);
v___x_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
lean_ctor_set(v___x_489_, 1, v_a_340_);
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
return v___x_490_;
}
}
case 9:
{
lean_object* v_fvarId_491_; lean_object* v_y_492_; lean_object* v_k_493_; uint8_t v___x_494_; 
v_fvarId_491_ = lean_ctor_get(v_c_338_, 0);
lean_inc(v_fvarId_491_);
v_y_492_ = lean_ctor_get(v_c_338_, 3);
lean_inc(v_y_492_);
v_k_493_ = lean_ctor_get(v_c_338_, 5);
lean_inc_ref(v_k_493_);
lean_dec_ref_known(v_c_338_, 6);
v___x_494_ = l_Lean_instBEqFVarId_beq(v_fvarId_491_, v_fvarId_337_);
lean_dec(v_fvarId_491_);
if (v___x_494_ == 0)
{
uint8_t v___x_495_; 
v___x_495_ = l_Lean_instBEqFVarId_beq(v_y_492_, v_fvarId_337_);
lean_dec(v_y_492_);
if (v___x_495_ == 0)
{
v_c_338_ = v_k_493_;
goto _start;
}
else
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
lean_dec_ref(v_k_493_);
v___x_497_ = lean_box(v___x_495_);
v___x_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
lean_ctor_set(v___x_498_, 1, v_a_340_);
v___x_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
return v___x_499_;
}
}
else
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
lean_dec_ref(v_k_493_);
lean_dec(v_y_492_);
v___x_500_ = lean_box(v___x_494_);
v___x_501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
lean_ctor_set(v___x_501_, 1, v_a_340_);
v___x_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
return v___x_502_;
}
}
case 12:
{
lean_object* v_fvarId_503_; lean_object* v_k_504_; uint8_t v___x_505_; 
v_fvarId_503_ = lean_ctor_get(v_c_338_, 0);
lean_inc(v_fvarId_503_);
v_k_504_ = lean_ctor_get(v_c_338_, 3);
lean_inc_ref(v_k_504_);
lean_dec_ref_known(v_c_338_, 4);
v___x_505_ = l_Lean_instBEqFVarId_beq(v_fvarId_503_, v_fvarId_337_);
lean_dec(v_fvarId_503_);
if (v___x_505_ == 0)
{
v_c_338_ = v_k_504_;
goto _start;
}
else
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
lean_dec_ref(v_k_504_);
v___x_507_ = lean_box(v___x_505_);
v___x_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
lean_ctor_set(v___x_508_, 1, v_a_340_);
v___x_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
return v___x_509_;
}
}
case 13:
{
lean_object* v_fvarId_510_; lean_object* v_k_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_522_; 
v_fvarId_510_ = lean_ctor_get(v_c_338_, 0);
v_k_511_ = lean_ctor_get(v_c_338_, 1);
v_isSharedCheck_522_ = !lean_is_exclusive(v_c_338_);
if (v_isSharedCheck_522_ == 0)
{
v___x_513_ = v_c_338_;
v_isShared_514_ = v_isSharedCheck_522_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_k_511_);
lean_inc(v_fvarId_510_);
lean_dec(v_c_338_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_522_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
uint8_t v___x_515_; 
v___x_515_ = l_Lean_instBEqFVarId_beq(v_fvarId_510_, v_fvarId_337_);
lean_dec(v_fvarId_510_);
if (v___x_515_ == 0)
{
lean_del_object(v___x_513_);
v_c_338_ = v_k_511_;
goto _start;
}
else
{
lean_object* v___x_517_; lean_object* v___x_519_; 
lean_dec_ref(v_k_511_);
v___x_517_ = lean_box(v___x_515_);
if (v_isShared_514_ == 0)
{
lean_ctor_set_tag(v___x_513_, 0);
lean_ctor_set(v___x_513_, 1, v_a_340_);
lean_ctor_set(v___x_513_, 0, v___x_517_);
v___x_519_ = v___x_513_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_517_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v_a_340_);
v___x_519_ = v_reuseFailAlloc_521_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
lean_object* v___x_520_; 
v___x_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
return v___x_520_;
}
}
}
}
default: 
{
lean_object* v_fvarId_523_; lean_object* v_k_524_; uint8_t v___x_525_; 
v_fvarId_523_ = lean_ctor_get(v_c_338_, 0);
lean_inc(v_fvarId_523_);
v_k_524_ = lean_ctor_get(v_c_338_, 2);
lean_inc_ref(v_k_524_);
lean_dec_ref(v_c_338_);
v___x_525_ = l_Lean_instBEqFVarId_beq(v_fvarId_523_, v_fvarId_337_);
lean_dec(v_fvarId_523_);
if (v___x_525_ == 0)
{
v_c_338_ = v_k_524_;
goto _start;
}
else
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
lean_dec_ref(v_k_524_);
v___x_527_ = lean_box(v___x_525_);
v___x_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
lean_ctor_set(v___x_528_, 1, v_a_340_);
v___x_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
return v___x_529_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_337_ = stack[0].m_obj;
lean_object* v_c_338_ = stack[1].m_obj;
lean_object* v_a_339_ = stack[2].m_obj;
lean_object* v_a_340_ = stack[3].m_obj;
lean_object* v_a_341_ = stack[4].m_obj;
lean_object* v_a_342_ = stack[5].m_obj;
lean_object* v_a_343_ = stack[6].m_obj;
lean_object* v_a_344_ = stack[7].m_obj;
lean_object* v_res_530_;
v_res_530_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go(v_fvarId_337_, v_c_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_);
stack->m_obj
 = v_res_530_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__4(lean_object* v_fvarId_531_, lean_object* v_as_532_, size_t v_i_533_, size_t v_stop_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
uint8_t v___x_542_; 
v___x_542_ = lean_usize_dec_eq(v_i_533_, v_stop_534_);
if (v___x_542_ == 0)
{
uint8_t v___x_543_; lean_object* v___y_545_; lean_object* v___x_571_; 
v___x_543_ = 1;
v___x_571_ = lean_array_uget_borrowed(v_as_532_, v_i_533_);
switch(lean_obj_tag(v___x_571_))
{
case 0:
{
lean_object* v_code_572_; 
v_code_572_ = lean_ctor_get(v___x_571_, 2);
lean_inc_ref(v_code_572_);
v___y_545_ = v_code_572_;
goto v___jp_544_;
}
case 1:
{
lean_object* v_code_573_; 
v_code_573_ = lean_ctor_get(v___x_571_, 1);
lean_inc_ref(v_code_573_);
v___y_545_ = v_code_573_;
goto v___jp_544_;
}
default: 
{
lean_object* v_code_574_; 
v_code_574_ = lean_ctor_get(v___x_571_, 0);
lean_inc_ref(v_code_574_);
v___y_545_ = v_code_574_;
goto v___jp_544_;
}
}
v___jp_544_:
{
lean_object* v___x_546_; 
v___x_546_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go(v_fvarId_531_, v___y_545_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_570_; 
v_a_547_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_570_ == 0)
{
v___x_549_ = v___x_546_;
v_isShared_550_ = v_isSharedCheck_570_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_546_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_570_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v_fst_551_; uint8_t v___x_552_; 
v_fst_551_ = lean_ctor_get(v_a_547_, 0);
v___x_552_ = lean_unbox(v_fst_551_);
if (v___x_552_ == 0)
{
lean_object* v_snd_553_; size_t v___x_554_; size_t v___x_555_; 
lean_del_object(v___x_549_);
v_snd_553_ = lean_ctor_get(v_a_547_, 1);
lean_inc(v_snd_553_);
lean_dec(v_a_547_);
v___x_554_ = ((size_t)1ULL);
v___x_555_ = lean_usize_add(v_i_533_, v___x_554_);
v_i_533_ = v___x_555_;
v___y_536_ = v_snd_553_;
goto _start;
}
else
{
lean_object* v_snd_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_568_; 
v_snd_557_ = lean_ctor_get(v_a_547_, 1);
v_isSharedCheck_568_ = !lean_is_exclusive(v_a_547_);
if (v_isSharedCheck_568_ == 0)
{
lean_object* v_unused_569_; 
v_unused_569_ = lean_ctor_get(v_a_547_, 0);
lean_dec(v_unused_569_);
v___x_559_ = v_a_547_;
v_isShared_560_ = v_isSharedCheck_568_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_snd_557_);
lean_dec(v_a_547_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_568_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_561_; lean_object* v___x_563_; 
v___x_561_ = lean_box(v___x_543_);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 0, v___x_561_);
v___x_563_ = v___x_559_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_561_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v_snd_557_);
v___x_563_ = v_reuseFailAlloc_567_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
lean_object* v___x_565_; 
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 0, v___x_563_);
v___x_565_ = v___x_549_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_563_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
}
}
else
{
return v___x_546_;
}
}
}
else
{
uint8_t v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_575_ = 0;
v___x_576_ = lean_box(v___x_575_);
v___x_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
lean_ctor_set(v___x_577_, 1, v___y_536_);
v___x_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
return v___x_578_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_531_ = stack[0].m_obj;
lean_object* v_as_532_ = stack[1].m_obj;
size_t v_i_533_ = stack[2].m_num;
size_t v_stop_534_ = stack[3].m_num;
lean_object* v___y_535_ = stack[4].m_obj;
lean_object* v___y_536_ = stack[5].m_obj;
lean_object* v___y_537_ = stack[6].m_obj;
lean_object* v___y_538_ = stack[7].m_obj;
lean_object* v___y_539_ = stack[8].m_obj;
lean_object* v___y_540_ = stack[9].m_obj;
lean_object* v_res_579_;
v_res_579_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__4(v_fvarId_531_, v_as_532_, v_i_533_, v_stop_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
stack->m_obj
 = v_res_579_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__4___boxed(lean_object* v_fvarId_580_, lean_object* v_as_581_, lean_object* v_i_582_, lean_object* v_stop_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
size_t v_i_boxed_591_; size_t v_stop_boxed_592_; lean_object* v_res_593_; 
v_i_boxed_591_ = lean_unbox_usize(v_i_582_);
lean_dec(v_i_582_);
v_stop_boxed_592_ = lean_unbox_usize(v_stop_583_);
lean_dec(v_stop_583_);
v_res_593_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__4(v_fvarId_580_, v_as_581_, v_i_boxed_591_, v_stop_boxed_592_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec_ref(v___y_584_);
lean_dec_ref(v_as_581_);
lean_dec(v_fvarId_580_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___boxed(lean_object* v_fvarId_594_, lean_object* v_c_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go(v_fvarId_594_, v_c_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_);
lean_dec(v_a_601_);
lean_dec_ref(v_a_600_);
lean_dec(v_a_599_);
lean_dec_ref(v_a_598_);
lean_dec_ref(v_a_596_);
lean_dec(v_fvarId_594_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0(lean_object* v_00_u03b2_604_, lean_object* v_m_605_, lean_object* v_a_606_, lean_object* v_b_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0___redArg(v_m_605_, v_a_606_, v_b_607_);
return v___x_608_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1(lean_object* v_00_u03b2_609_, lean_object* v_m_610_, lean_object* v_a_611_){
_start:
{
uint8_t v___x_612_; 
v___x_612_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___redArg(v_m_610_, v_a_611_);
return v___x_612_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_610_ = stack[1].m_obj;
lean_object* v_a_611_ = stack[2].m_obj;
uint8_t v_res_613_;
v_res_613_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1(lean_box(0), v_m_610_, v_a_611_);
stack->m_num = v_res_613_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___boxed(lean_object* v_00_u03b2_614_, lean_object* v_m_615_, lean_object* v_a_616_){
_start:
{
uint8_t v_res_617_; lean_object* v_r_618_; 
v_res_617_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1(v_00_u03b2_614_, v_m_615_, v_a_616_);
lean_dec(v_a_616_);
lean_dec_ref(v_m_615_);
v_r_618_ = lean_box(v_res_617_);
return v_r_618_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0(lean_object* v_00_u03b2_619_, lean_object* v_a_620_, lean_object* v_x_621_){
_start:
{
uint8_t v___x_622_; 
v___x_622_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0___redArg(v_a_620_, v_x_621_);
return v___x_622_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_620_ = stack[1].m_obj;
lean_object* v_x_621_ = stack[2].m_obj;
uint8_t v_res_623_;
v_res_623_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0(lean_box(0), v_a_620_, v_x_621_);
stack->m_num = v_res_623_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_624_, lean_object* v_a_625_, lean_object* v_x_626_){
_start:
{
uint8_t v_res_627_; lean_object* v_r_628_; 
v_res_627_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0(v_00_u03b2_624_, v_a_625_, v_x_626_);
lean_dec(v_x_626_);
lean_dec(v_a_625_);
v_r_628_ = lean_box(v_res_627_);
return v_r_628_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1(lean_object* v_00_u03b2_629_, lean_object* v_data_630_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1___redArg(v_data_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_632_, lean_object* v_i_633_, lean_object* v_source_634_, lean_object* v_target_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1_spec__3___redArg(v_i_633_, v_source_634_, v_target_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_637_, lean_object* v_x_638_, lean_object* v_x_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1_spec__3_spec__7___redArg(v_x_638_, v_x_639_);
return v___x_640_;
}
}
lean_object* l_Lean_Compiler_LCNF_Code_isFVarLiveIn(lean_object* v_c_641_, lean_object* v_fvarId_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_648_ = l_Lean_instEmptyCollectionFVarIdHashSet;
lean_inc_n(v_fvarId_642_, 2);
v___x_649_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_fvarId_642_);
v___x_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_650_, 0, v___x_649_);
lean_ctor_set(v___x_650_, 1, v_fvarId_642_);
v___x_651_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go(v_fvarId_642_, v_c_641_, v___x_650_, v___x_648_, v_a_643_, v_a_644_, v_a_645_, v_a_646_);
lean_dec_ref_known(v___x_650_, 2);
lean_dec(v_fvarId_642_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_660_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_660_ == 0)
{
v___x_654_ = v___x_651_;
v_isShared_655_ = v_isSharedCheck_660_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_651_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_660_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v_fst_656_; lean_object* v___x_658_; 
v_fst_656_ = lean_ctor_get(v_a_652_, 0);
lean_inc(v_fst_656_);
lean_dec(v_a_652_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v_fst_656_);
v___x_658_ = v___x_654_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_fst_656_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
else
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_668_; 
v_a_661_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_668_ == 0)
{
v___x_663_ = v___x_651_;
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_651_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_664_ == 0)
{
v___x_666_ = v___x_663_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_661_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Code_isFVarLiveIn_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_641_ = stack[0].m_obj;
lean_object* v_fvarId_642_ = stack[1].m_obj;
lean_object* v_a_643_ = stack[2].m_obj;
lean_object* v_a_644_ = stack[3].m_obj;
lean_object* v_a_645_ = stack[4].m_obj;
lean_object* v_a_646_ = stack[5].m_obj;
lean_object* v_res_669_;
v_res_669_ = l_Lean_Compiler_LCNF_Code_isFVarLiveIn(v_c_641_, v_fvarId_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_);
stack->m_obj
 = v_res_669_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_isFVarLiveIn___boxed(lean_object* v_c_670_, lean_object* v_fvarId_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_Compiler_LCNF_Code_isFVarLiveIn(v_c_670_, v_fvarId_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
lean_dec(v_a_675_);
lean_dec_ref(v_a_674_);
lean_dec(v_a_673_);
lean_dec_ref(v_a_672_);
return v_res_677_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_DependsOn(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_LiveVars(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
