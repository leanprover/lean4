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
v___x_75_ = l_instMonadEIO___redArg();
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
lean_object* v___f_137_; lean_object* v___f_138_; lean_object* v___f_139_; lean_object* v___f_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; uint8_t v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___f_150_; lean_object* v___x_16637__overap_151_; lean_object* v___x_152_; 
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
v___x_16637__overap_151_ = lean_panic_fn_borrowed(v___f_150_, v_msg_80_);
lean_dec_ref(v___f_150_);
lean_inc(v___y_86_);
lean_inc_ref(v___y_85_);
lean_inc(v___y_84_);
lean_inc_ref(v___y_83_);
lean_inc_ref(v___y_81_);
v___x_152_ = lean_apply_7(v___x_16637__overap_151_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, lean_box(0));
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
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v_nbuckets_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_269_ = lean_array_get_size(v_data_268_);
v___x_270_ = lean_unsigned_to_nat(2u);
v_nbuckets_271_ = lean_nat_mul(v___x_269_, v___x_270_);
v___x_272_ = lean_unsigned_to_nat(0u);
v___x_273_ = lean_box(0);
v___x_274_ = lean_mk_array(v_nbuckets_271_, v___x_273_);
v___x_275_ = lean_array_propagate_mark(v_data_268_, v___x_274_);
v___x_276_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1_spec__3___redArg(v___x_272_, v_data_268_, v___x_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0___redArg(lean_object* v_m_277_, lean_object* v_a_278_, lean_object* v_b_279_){
_start:
{
lean_object* v_size_280_; lean_object* v_buckets_281_; lean_object* v___x_282_; uint64_t v___x_283_; uint64_t v___x_284_; uint64_t v___x_285_; uint64_t v_fold_286_; uint64_t v___x_287_; uint64_t v___x_288_; uint64_t v___x_289_; size_t v___x_290_; size_t v___x_291_; size_t v___x_292_; size_t v___x_293_; size_t v___x_294_; lean_object* v_bkt_295_; uint8_t v___x_296_; 
v_size_280_ = lean_ctor_get(v_m_277_, 0);
v_buckets_281_ = lean_ctor_get(v_m_277_, 1);
v___x_282_ = lean_array_get_size(v_buckets_281_);
v___x_283_ = l_Lean_instHashableFVarId_hash(v_a_278_);
v___x_284_ = 32ULL;
v___x_285_ = lean_uint64_shift_right(v___x_283_, v___x_284_);
v_fold_286_ = lean_uint64_xor(v___x_283_, v___x_285_);
v___x_287_ = 16ULL;
v___x_288_ = lean_uint64_shift_right(v_fold_286_, v___x_287_);
v___x_289_ = lean_uint64_xor(v_fold_286_, v___x_288_);
v___x_290_ = lean_uint64_to_usize(v___x_289_);
v___x_291_ = lean_usize_of_nat(v___x_282_);
v___x_292_ = ((size_t)1ULL);
v___x_293_ = lean_usize_sub(v___x_291_, v___x_292_);
v___x_294_ = lean_usize_land(v___x_290_, v___x_293_);
v_bkt_295_ = lean_array_uget_borrowed(v_buckets_281_, v___x_294_);
v___x_296_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0___redArg(v_a_278_, v_bkt_295_);
if (v___x_296_ == 0)
{
lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_317_; 
lean_inc_ref(v_buckets_281_);
lean_inc(v_size_280_);
v_isSharedCheck_317_ = !lean_is_exclusive(v_m_277_);
if (v_isSharedCheck_317_ == 0)
{
lean_object* v_unused_318_; lean_object* v_unused_319_; 
v_unused_318_ = lean_ctor_get(v_m_277_, 1);
lean_dec(v_unused_318_);
v_unused_319_ = lean_ctor_get(v_m_277_, 0);
lean_dec(v_unused_319_);
v___x_298_ = v_m_277_;
v_isShared_299_ = v_isSharedCheck_317_;
goto v_resetjp_297_;
}
else
{
lean_dec(v_m_277_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_317_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_300_; lean_object* v_size_x27_301_; lean_object* v___x_302_; lean_object* v_buckets_x27_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_300_ = lean_unsigned_to_nat(1u);
v_size_x27_301_ = lean_nat_add(v_size_280_, v___x_300_);
lean_dec(v_size_280_);
lean_inc(v_bkt_295_);
v___x_302_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_302_, 0, v_a_278_);
lean_ctor_set(v___x_302_, 1, v_b_279_);
lean_ctor_set(v___x_302_, 2, v_bkt_295_);
v_buckets_x27_303_ = lean_array_uset(v_buckets_281_, v___x_294_, v___x_302_);
v___x_304_ = lean_unsigned_to_nat(4u);
v___x_305_ = lean_nat_mul(v_size_x27_301_, v___x_304_);
v___x_306_ = lean_unsigned_to_nat(3u);
v___x_307_ = lean_nat_div(v___x_305_, v___x_306_);
lean_dec(v___x_305_);
v___x_308_ = lean_array_get_size(v_buckets_x27_303_);
v___x_309_ = lean_nat_dec_le(v___x_307_, v___x_308_);
lean_dec(v___x_307_);
if (v___x_309_ == 0)
{
lean_object* v_val_310_; lean_object* v___x_312_; 
v_val_310_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1___redArg(v_buckets_x27_303_);
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 1, v_val_310_);
lean_ctor_set(v___x_298_, 0, v_size_x27_301_);
v___x_312_ = v___x_298_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_size_x27_301_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v_val_310_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
else
{
lean_object* v___x_315_; 
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 1, v_buckets_x27_303_);
lean_ctor_set(v___x_298_, 0, v_size_x27_301_);
v___x_315_ = v___x_298_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_size_x27_301_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v_buckets_x27_303_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
}
else
{
lean_dec(v_b_279_);
lean_dec(v_a_278_);
return v_m_277_;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__3(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_323_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__2));
v___x_324_ = lean_unsigned_to_nat(48u);
v___x_325_ = lean_unsigned_to_nat(76u);
v___x_326_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__1));
v___x_327_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__0));
v___x_328_ = l_mkPanicMessageWithDecl(v___x_327_, v___x_326_, v___x_325_, v___x_324_, v___x_323_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go(lean_object* v_fvarId_329_, lean_object* v_c_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
switch(lean_obj_tag(v_c_330_))
{
case 0:
{
lean_object* v_decl_338_; lean_object* v_k_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_352_; 
v_decl_338_ = lean_ctor_get(v_c_330_, 0);
v_k_339_ = lean_ctor_get(v_c_330_, 1);
v_isSharedCheck_352_ = !lean_is_exclusive(v_c_330_);
if (v_isSharedCheck_352_ == 0)
{
v___x_341_ = v_c_330_;
v_isShared_342_ = v_isSharedCheck_352_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_k_339_);
lean_inc(v_decl_338_);
lean_dec(v_c_330_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_352_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v_targetSet_343_; uint8_t v___x_344_; uint8_t v___x_345_; 
v_targetSet_343_ = lean_ctor_get(v_a_331_, 0);
v___x_344_ = 1;
v___x_345_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn(v___x_344_, v_decl_338_, v_targetSet_343_);
lean_dec_ref(v_decl_338_);
if (v___x_345_ == 0)
{
lean_del_object(v___x_341_);
v_c_330_ = v_k_339_;
goto _start;
}
else
{
lean_object* v___x_347_; lean_object* v___x_349_; 
lean_dec_ref(v_k_339_);
v___x_347_ = lean_box(v___x_345_);
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 1, v_a_332_);
lean_ctor_set(v___x_341_, 0, v___x_347_);
v___x_349_ = v___x_341_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_347_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v_a_332_);
v___x_349_ = v_reuseFailAlloc_351_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
lean_object* v___x_350_; 
v___x_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
return v___x_350_;
}
}
}
}
case 2:
{
lean_object* v_decl_353_; lean_object* v_k_354_; lean_object* v_fvarId_355_; lean_object* v_value_356_; lean_object* v___x_357_; 
v_decl_353_ = lean_ctor_get(v_c_330_, 0);
lean_inc_ref(v_decl_353_);
v_k_354_ = lean_ctor_get(v_c_330_, 1);
lean_inc_ref(v_k_354_);
lean_dec_ref_known(v_c_330_, 2);
v_fvarId_355_ = lean_ctor_get(v_decl_353_, 0);
lean_inc(v_fvarId_355_);
v_value_356_ = lean_ctor_get(v_decl_353_, 4);
lean_inc_ref(v_value_356_);
lean_dec_ref(v_decl_353_);
v___x_357_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go(v_fvarId_329_, v_value_356_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v_a_358_; lean_object* v_fst_359_; uint8_t v___x_360_; 
v_a_358_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_a_358_);
v_fst_359_ = lean_ctor_get(v_a_358_, 0);
v___x_360_ = lean_unbox(v_fst_359_);
if (v___x_360_ == 0)
{
lean_object* v_snd_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
lean_dec_ref_known(v___x_357_, 1);
v_snd_361_ = lean_ctor_get(v_a_358_, 1);
lean_inc(v_snd_361_);
lean_dec(v_a_358_);
v___x_362_ = lean_box(0);
v___x_363_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0___redArg(v_snd_361_, v_fvarId_355_, v___x_362_);
v_c_330_ = v_k_354_;
v_a_332_ = v___x_363_;
goto _start;
}
else
{
lean_dec(v_a_358_);
lean_dec(v_fvarId_355_);
lean_dec_ref(v_k_354_);
return v___x_357_;
}
}
else
{
lean_dec(v_fvarId_355_);
lean_dec_ref(v_k_354_);
return v___x_357_;
}
}
case 3:
{
lean_object* v_fvarId_365_; lean_object* v_args_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_405_; 
v_fvarId_365_ = lean_ctor_get(v_c_330_, 0);
v_args_366_ = lean_ctor_get(v_c_330_, 1);
v_isSharedCheck_405_ = !lean_is_exclusive(v_c_330_);
if (v_isSharedCheck_405_ == 0)
{
v___x_368_ = v_c_330_;
v_isShared_369_ = v_isSharedCheck_405_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_args_366_);
lean_inc(v_fvarId_365_);
lean_dec(v_c_330_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_405_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
uint8_t v___y_371_; lean_object* v___x_396_; lean_object* v___x_397_; uint8_t v___x_398_; 
v___x_396_ = lean_unsigned_to_nat(0u);
v___x_397_ = lean_array_get_size(v_args_366_);
v___x_398_ = lean_nat_dec_lt(v___x_396_, v___x_397_);
if (v___x_398_ == 0)
{
lean_dec_ref(v_args_366_);
v___y_371_ = v___x_398_;
goto v___jp_370_;
}
else
{
if (v___x_398_ == 0)
{
lean_dec_ref(v_args_366_);
v___y_371_ = v___x_398_;
goto v___jp_370_;
}
else
{
size_t v___x_399_; size_t v___x_400_; uint8_t v___x_401_; 
v___x_399_ = ((size_t)0ULL);
v___x_400_ = lean_usize_of_nat(v___x_397_);
v___x_401_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3(v_a_331_, v_args_366_, v___x_399_, v___x_400_);
lean_dec_ref(v_args_366_);
if (v___x_401_ == 0)
{
v___y_371_ = v___x_401_;
goto v___jp_370_;
}
else
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
lean_del_object(v___x_368_);
lean_dec(v_fvarId_365_);
v___x_402_ = lean_box(v___x_401_);
v___x_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
lean_ctor_set(v___x_403_, 1, v_a_332_);
v___x_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
return v___x_404_;
}
}
}
v___jp_370_:
{
uint8_t v___x_372_; 
v___x_372_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___redArg(v_a_332_, v_fvarId_365_);
if (v___x_372_ == 0)
{
uint8_t v___x_373_; lean_object* v___x_374_; 
lean_del_object(v___x_368_);
v___x_373_ = 1;
v___x_374_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_373_, v_fvarId_365_, v_a_334_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v_a_375_; 
v_a_375_ = lean_ctor_get(v___x_374_, 0);
lean_inc(v_a_375_);
lean_dec_ref_known(v___x_374_, 1);
if (lean_obj_tag(v_a_375_) == 1)
{
lean_object* v_val_376_; lean_object* v_value_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v_val_376_ = lean_ctor_get(v_a_375_, 0);
lean_inc(v_val_376_);
lean_dec_ref_known(v_a_375_, 1);
v_value_377_ = lean_ctor_get(v_val_376_, 4);
lean_inc_ref(v_value_377_);
lean_dec(v_val_376_);
v___x_378_ = lean_box(0);
v___x_379_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0___redArg(v_a_332_, v_fvarId_365_, v___x_378_);
v_c_330_ = v_value_377_;
v_a_332_ = v___x_379_;
goto _start;
}
else
{
lean_object* v___x_381_; lean_object* v___x_382_; 
lean_dec(v_a_375_);
lean_dec(v_fvarId_365_);
v___x_381_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__3, &l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__3);
v___x_382_ = l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2(v___x_381_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_);
return v___x_382_;
}
}
else
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_390_; 
lean_dec(v_fvarId_365_);
lean_dec_ref(v_a_332_);
v_a_383_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_390_ == 0)
{
v___x_385_ = v___x_374_;
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_374_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_388_; 
if (v_isShared_386_ == 0)
{
v___x_388_ = v___x_385_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_383_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
else
{
lean_object* v___x_391_; lean_object* v___x_393_; 
lean_dec(v_fvarId_365_);
v___x_391_ = lean_box(v___y_371_);
if (v_isShared_369_ == 0)
{
lean_ctor_set_tag(v___x_368_, 0);
lean_ctor_set(v___x_368_, 1, v_a_332_);
lean_ctor_set(v___x_368_, 0, v___x_391_);
v___x_393_ = v___x_368_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_391_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_a_332_);
v___x_393_ = v_reuseFailAlloc_395_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
lean_object* v___x_394_; 
v___x_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
return v___x_394_;
}
}
}
}
}
case 4:
{
lean_object* v_cases_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_434_; 
v_cases_406_ = lean_ctor_get(v_c_330_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v_c_330_);
if (v_isSharedCheck_434_ == 0)
{
v___x_408_ = v_c_330_;
v_isShared_409_ = v_isSharedCheck_434_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_cases_406_);
lean_dec(v_c_330_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_434_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v_discr_410_; lean_object* v_alts_411_; uint8_t v___x_412_; 
v_discr_410_ = lean_ctor_get(v_cases_406_, 2);
lean_inc(v_discr_410_);
v_alts_411_ = lean_ctor_get(v_cases_406_, 3);
lean_inc_ref(v_alts_411_);
lean_dec_ref(v_cases_406_);
v___x_412_ = l_Lean_instBEqFVarId_beq(v_discr_410_, v_fvarId_329_);
lean_dec(v_discr_410_);
if (v___x_412_ == 0)
{
lean_object* v___x_413_; lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_413_ = lean_unsigned_to_nat(0u);
v___x_414_ = lean_array_get_size(v_alts_411_);
v___x_415_ = lean_nat_dec_lt(v___x_413_, v___x_414_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_419_; 
lean_dec_ref(v_alts_411_);
v___x_416_ = lean_box(v___x_415_);
v___x_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
lean_ctor_set(v___x_417_, 1, v_a_332_);
if (v_isShared_409_ == 0)
{
lean_ctor_set_tag(v___x_408_, 0);
lean_ctor_set(v___x_408_, 0, v___x_417_);
v___x_419_ = v___x_408_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_417_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
else
{
if (v___x_415_ == 0)
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_424_; 
lean_dec_ref(v_alts_411_);
v___x_421_ = lean_box(v___x_415_);
v___x_422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
lean_ctor_set(v___x_422_, 1, v_a_332_);
if (v_isShared_409_ == 0)
{
lean_ctor_set_tag(v___x_408_, 0);
lean_ctor_set(v___x_408_, 0, v___x_422_);
v___x_424_ = v___x_408_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_422_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
else
{
size_t v___x_426_; size_t v___x_427_; lean_object* v___x_428_; 
lean_del_object(v___x_408_);
v___x_426_ = ((size_t)0ULL);
v___x_427_ = lean_usize_of_nat(v___x_414_);
v___x_428_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__4(v_fvarId_329_, v_alts_411_, v___x_426_, v___x_427_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_);
lean_dec_ref(v_alts_411_);
return v___x_428_;
}
}
}
else
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_432_; 
lean_dec_ref(v_alts_411_);
v___x_429_ = lean_box(v___x_412_);
v___x_430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
lean_ctor_set(v___x_430_, 1, v_a_332_);
if (v_isShared_409_ == 0)
{
lean_ctor_set_tag(v___x_408_, 0);
lean_ctor_set(v___x_408_, 0, v___x_430_);
v___x_432_ = v___x_408_;
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
}
}
case 5:
{
lean_object* v_fvarId_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_445_; 
v_fvarId_435_ = lean_ctor_get(v_c_330_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v_c_330_);
if (v_isSharedCheck_445_ == 0)
{
v___x_437_ = v_c_330_;
v_isShared_438_ = v_isSharedCheck_445_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_fvarId_435_);
lean_dec(v_c_330_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_445_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
uint8_t v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_439_ = l_Lean_instBEqFVarId_beq(v_fvarId_435_, v_fvarId_329_);
lean_dec(v_fvarId_435_);
v___x_440_ = lean_box(v___x_439_);
v___x_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
lean_ctor_set(v___x_441_, 1, v_a_332_);
if (v_isShared_438_ == 0)
{
lean_ctor_set_tag(v___x_437_, 0);
lean_ctor_set(v___x_437_, 0, v___x_441_);
v___x_443_ = v___x_437_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_441_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
case 6:
{
lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_455_; 
v_isSharedCheck_455_ = !lean_is_exclusive(v_c_330_);
if (v_isSharedCheck_455_ == 0)
{
lean_object* v_unused_456_; 
v_unused_456_ = lean_ctor_get(v_c_330_, 0);
lean_dec(v_unused_456_);
v___x_447_ = v_c_330_;
v_isShared_448_ = v_isSharedCheck_455_;
goto v_resetjp_446_;
}
else
{
lean_dec(v_c_330_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_455_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
uint8_t v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_453_; 
v___x_449_ = 0;
v___x_450_ = lean_box(v___x_449_);
v___x_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_451_, 0, v___x_450_);
lean_ctor_set(v___x_451_, 1, v_a_332_);
if (v_isShared_448_ == 0)
{
lean_ctor_set_tag(v___x_447_, 0);
lean_ctor_set(v___x_447_, 0, v___x_451_);
v___x_453_ = v___x_447_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_451_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
case 7:
{
lean_object* v_fvarId_457_; lean_object* v_y_458_; lean_object* v_k_459_; uint8_t v___x_460_; 
v_fvarId_457_ = lean_ctor_get(v_c_330_, 0);
lean_inc(v_fvarId_457_);
v_y_458_ = lean_ctor_get(v_c_330_, 2);
lean_inc(v_y_458_);
v_k_459_ = lean_ctor_get(v_c_330_, 3);
lean_inc_ref(v_k_459_);
lean_dec_ref_known(v_c_330_, 4);
v___x_460_ = l_Lean_instBEqFVarId_beq(v_fvarId_457_, v_fvarId_329_);
lean_dec(v_fvarId_457_);
if (v___x_460_ == 0)
{
lean_object* v_targetSet_461_; uint8_t v___x_462_; uint8_t v___x_463_; 
v_targetSet_461_ = lean_ctor_get(v_a_331_, 0);
v___x_462_ = 1;
v___x_463_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn(v___x_462_, v_y_458_, v_targetSet_461_);
lean_dec(v_y_458_);
if (v___x_463_ == 0)
{
v_c_330_ = v_k_459_;
goto _start;
}
else
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
lean_dec_ref(v_k_459_);
v___x_465_ = lean_box(v___x_463_);
v___x_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
lean_ctor_set(v___x_466_, 1, v_a_332_);
v___x_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
return v___x_467_;
}
}
else
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
lean_dec_ref(v_k_459_);
lean_dec(v_y_458_);
v___x_468_ = lean_box(v___x_460_);
v___x_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
lean_ctor_set(v___x_469_, 1, v_a_332_);
v___x_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
return v___x_470_;
}
}
case 8:
{
lean_object* v_fvarId_471_; lean_object* v_y_472_; lean_object* v_k_473_; uint8_t v___x_474_; 
v_fvarId_471_ = lean_ctor_get(v_c_330_, 0);
lean_inc(v_fvarId_471_);
v_y_472_ = lean_ctor_get(v_c_330_, 2);
lean_inc(v_y_472_);
v_k_473_ = lean_ctor_get(v_c_330_, 3);
lean_inc_ref(v_k_473_);
lean_dec_ref_known(v_c_330_, 4);
v___x_474_ = l_Lean_instBEqFVarId_beq(v_fvarId_471_, v_fvarId_329_);
lean_dec(v_fvarId_471_);
if (v___x_474_ == 0)
{
uint8_t v___x_475_; 
v___x_475_ = l_Lean_instBEqFVarId_beq(v_y_472_, v_fvarId_329_);
lean_dec(v_y_472_);
if (v___x_475_ == 0)
{
v_c_330_ = v_k_473_;
goto _start;
}
else
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
lean_dec_ref(v_k_473_);
v___x_477_ = lean_box(v___x_475_);
v___x_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
lean_ctor_set(v___x_478_, 1, v_a_332_);
v___x_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
return v___x_479_;
}
}
else
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
lean_dec_ref(v_k_473_);
lean_dec(v_y_472_);
v___x_480_ = lean_box(v___x_474_);
v___x_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
lean_ctor_set(v___x_481_, 1, v_a_332_);
v___x_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
return v___x_482_;
}
}
case 9:
{
lean_object* v_fvarId_483_; lean_object* v_y_484_; lean_object* v_k_485_; uint8_t v___x_486_; 
v_fvarId_483_ = lean_ctor_get(v_c_330_, 0);
lean_inc(v_fvarId_483_);
v_y_484_ = lean_ctor_get(v_c_330_, 3);
lean_inc(v_y_484_);
v_k_485_ = lean_ctor_get(v_c_330_, 5);
lean_inc_ref(v_k_485_);
lean_dec_ref_known(v_c_330_, 6);
v___x_486_ = l_Lean_instBEqFVarId_beq(v_fvarId_483_, v_fvarId_329_);
lean_dec(v_fvarId_483_);
if (v___x_486_ == 0)
{
uint8_t v___x_487_; 
v___x_487_ = l_Lean_instBEqFVarId_beq(v_y_484_, v_fvarId_329_);
lean_dec(v_y_484_);
if (v___x_487_ == 0)
{
v_c_330_ = v_k_485_;
goto _start;
}
else
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
lean_dec_ref(v_k_485_);
v___x_489_ = lean_box(v___x_487_);
v___x_490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
lean_ctor_set(v___x_490_, 1, v_a_332_);
v___x_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
return v___x_491_;
}
}
else
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
lean_dec_ref(v_k_485_);
lean_dec(v_y_484_);
v___x_492_ = lean_box(v___x_486_);
v___x_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
lean_ctor_set(v___x_493_, 1, v_a_332_);
v___x_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
return v___x_494_;
}
}
case 12:
{
lean_object* v_fvarId_495_; lean_object* v_k_496_; uint8_t v___x_497_; 
v_fvarId_495_ = lean_ctor_get(v_c_330_, 0);
lean_inc(v_fvarId_495_);
v_k_496_ = lean_ctor_get(v_c_330_, 3);
lean_inc_ref(v_k_496_);
lean_dec_ref_known(v_c_330_, 4);
v___x_497_ = l_Lean_instBEqFVarId_beq(v_fvarId_495_, v_fvarId_329_);
lean_dec(v_fvarId_495_);
if (v___x_497_ == 0)
{
v_c_330_ = v_k_496_;
goto _start;
}
else
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
lean_dec_ref(v_k_496_);
v___x_499_ = lean_box(v___x_497_);
v___x_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
lean_ctor_set(v___x_500_, 1, v_a_332_);
v___x_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
return v___x_501_;
}
}
case 13:
{
lean_object* v_fvarId_502_; lean_object* v_k_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_514_; 
v_fvarId_502_ = lean_ctor_get(v_c_330_, 0);
v_k_503_ = lean_ctor_get(v_c_330_, 1);
v_isSharedCheck_514_ = !lean_is_exclusive(v_c_330_);
if (v_isSharedCheck_514_ == 0)
{
v___x_505_ = v_c_330_;
v_isShared_506_ = v_isSharedCheck_514_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_k_503_);
lean_inc(v_fvarId_502_);
lean_dec(v_c_330_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_514_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
uint8_t v___x_507_; 
v___x_507_ = l_Lean_instBEqFVarId_beq(v_fvarId_502_, v_fvarId_329_);
lean_dec(v_fvarId_502_);
if (v___x_507_ == 0)
{
lean_del_object(v___x_505_);
v_c_330_ = v_k_503_;
goto _start;
}
else
{
lean_object* v___x_509_; lean_object* v___x_511_; 
lean_dec_ref(v_k_503_);
v___x_509_ = lean_box(v___x_507_);
if (v_isShared_506_ == 0)
{
lean_ctor_set_tag(v___x_505_, 0);
lean_ctor_set(v___x_505_, 1, v_a_332_);
lean_ctor_set(v___x_505_, 0, v___x_509_);
v___x_511_ = v___x_505_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_509_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v_a_332_);
v___x_511_ = v_reuseFailAlloc_513_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
lean_object* v___x_512_; 
v___x_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
return v___x_512_;
}
}
}
}
default: 
{
lean_object* v_fvarId_515_; lean_object* v_k_516_; uint8_t v___x_517_; 
v_fvarId_515_ = lean_ctor_get(v_c_330_, 0);
lean_inc(v_fvarId_515_);
v_k_516_ = lean_ctor_get(v_c_330_, 2);
lean_inc_ref(v_k_516_);
lean_dec_ref(v_c_330_);
v___x_517_ = l_Lean_instBEqFVarId_beq(v_fvarId_515_, v_fvarId_329_);
lean_dec(v_fvarId_515_);
if (v___x_517_ == 0)
{
v_c_330_ = v_k_516_;
goto _start;
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
lean_dec_ref(v_k_516_);
v___x_519_ = lean_box(v___x_517_);
v___x_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
lean_ctor_set(v___x_520_, 1, v_a_332_);
v___x_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
return v___x_521_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__4(lean_object* v_fvarId_522_, lean_object* v_as_523_, size_t v_i_524_, size_t v_stop_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
uint8_t v___x_533_; 
v___x_533_ = lean_usize_dec_eq(v_i_524_, v_stop_525_);
if (v___x_533_ == 0)
{
uint8_t v___x_534_; lean_object* v___y_536_; lean_object* v___x_562_; 
v___x_534_ = 1;
v___x_562_ = lean_array_uget_borrowed(v_as_523_, v_i_524_);
switch(lean_obj_tag(v___x_562_))
{
case 0:
{
lean_object* v_code_563_; 
v_code_563_ = lean_ctor_get(v___x_562_, 2);
lean_inc_ref(v_code_563_);
v___y_536_ = v_code_563_;
goto v___jp_535_;
}
case 1:
{
lean_object* v_code_564_; 
v_code_564_ = lean_ctor_get(v___x_562_, 1);
lean_inc_ref(v_code_564_);
v___y_536_ = v_code_564_;
goto v___jp_535_;
}
default: 
{
lean_object* v_code_565_; 
v_code_565_ = lean_ctor_get(v___x_562_, 0);
lean_inc_ref(v_code_565_);
v___y_536_ = v_code_565_;
goto v___jp_535_;
}
}
v___jp_535_:
{
lean_object* v___x_537_; 
v___x_537_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go(v_fvarId_522_, v___y_536_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_561_; 
v_a_538_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_561_ == 0)
{
v___x_540_ = v___x_537_;
v_isShared_541_ = v_isSharedCheck_561_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v___x_537_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_561_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v_fst_542_; uint8_t v___x_543_; 
v_fst_542_ = lean_ctor_get(v_a_538_, 0);
v___x_543_ = lean_unbox(v_fst_542_);
if (v___x_543_ == 0)
{
lean_object* v_snd_544_; size_t v___x_545_; size_t v___x_546_; 
lean_del_object(v___x_540_);
v_snd_544_ = lean_ctor_get(v_a_538_, 1);
lean_inc(v_snd_544_);
lean_dec(v_a_538_);
v___x_545_ = ((size_t)1ULL);
v___x_546_ = lean_usize_add(v_i_524_, v___x_545_);
v_i_524_ = v___x_546_;
v___y_527_ = v_snd_544_;
goto _start;
}
else
{
lean_object* v_snd_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_559_; 
v_snd_548_ = lean_ctor_get(v_a_538_, 1);
v_isSharedCheck_559_ = !lean_is_exclusive(v_a_538_);
if (v_isSharedCheck_559_ == 0)
{
lean_object* v_unused_560_; 
v_unused_560_ = lean_ctor_get(v_a_538_, 0);
lean_dec(v_unused_560_);
v___x_550_ = v_a_538_;
v_isShared_551_ = v_isSharedCheck_559_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_snd_548_);
lean_dec(v_a_538_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_559_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_552_; lean_object* v___x_554_; 
v___x_552_ = lean_box(v___x_534_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 0, v___x_552_);
v___x_554_ = v___x_550_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_552_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_snd_548_);
v___x_554_ = v_reuseFailAlloc_558_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
lean_object* v___x_556_; 
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 0, v___x_554_);
v___x_556_ = v___x_540_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_554_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
}
}
else
{
return v___x_537_;
}
}
}
else
{
uint8_t v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_566_ = 0;
v___x_567_ = lean_box(v___x_566_);
v___x_568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
lean_ctor_set(v___x_568_, 1, v___y_527_);
v___x_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
return v___x_569_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__4___boxed(lean_object* v_fvarId_570_, lean_object* v_as_571_, lean_object* v_i_572_, lean_object* v_stop_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
size_t v_i_boxed_581_; size_t v_stop_boxed_582_; lean_object* v_res_583_; 
v_i_boxed_581_ = lean_unbox_usize(v_i_572_);
lean_dec(v_i_572_);
v_stop_boxed_582_ = lean_unbox_usize(v_stop_573_);
lean_dec(v_stop_573_);
v_res_583_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__4(v_fvarId_570_, v_as_571_, v_i_boxed_581_, v_stop_boxed_582_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec_ref(v___y_574_);
lean_dec_ref(v_as_571_);
lean_dec(v_fvarId_570_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___boxed(lean_object* v_fvarId_584_, lean_object* v_c_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go(v_fvarId_584_, v_c_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_);
lean_dec(v_a_591_);
lean_dec_ref(v_a_590_);
lean_dec(v_a_589_);
lean_dec_ref(v_a_588_);
lean_dec_ref(v_a_586_);
lean_dec(v_fvarId_584_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0(lean_object* v_00_u03b2_594_, lean_object* v_m_595_, lean_object* v_a_596_, lean_object* v_b_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0___redArg(v_m_595_, v_a_596_, v_b_597_);
return v___x_598_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1(lean_object* v_00_u03b2_599_, lean_object* v_m_600_, lean_object* v_a_601_){
_start:
{
uint8_t v___x_602_; 
v___x_602_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___redArg(v_m_600_, v_a_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___boxed(lean_object* v_00_u03b2_603_, lean_object* v_m_604_, lean_object* v_a_605_){
_start:
{
uint8_t v_res_606_; lean_object* v_r_607_; 
v_res_606_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1(v_00_u03b2_603_, v_m_604_, v_a_605_);
lean_dec(v_a_605_);
lean_dec_ref(v_m_604_);
v_r_607_ = lean_box(v_res_606_);
return v_r_607_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0(lean_object* v_00_u03b2_608_, lean_object* v_a_609_, lean_object* v_x_610_){
_start:
{
uint8_t v___x_611_; 
v___x_611_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0___redArg(v_a_609_, v_x_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_612_, lean_object* v_a_613_, lean_object* v_x_614_){
_start:
{
uint8_t v_res_615_; lean_object* v_r_616_; 
v_res_615_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0(v_00_u03b2_612_, v_a_613_, v_x_614_);
lean_dec(v_x_614_);
lean_dec(v_a_613_);
v_r_616_ = lean_box(v_res_615_);
return v_r_616_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1(lean_object* v_00_u03b2_617_, lean_object* v_data_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1___redArg(v_data_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_620_, lean_object* v_i_621_, lean_object* v_source_622_, lean_object* v_target_623_){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1_spec__3___redArg(v_i_621_, v_source_622_, v_target_623_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_625_, lean_object* v_x_626_, lean_object* v_x_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1_spec__3_spec__7___redArg(v_x_626_, v_x_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_isFVarLiveIn(lean_object* v_c_629_, lean_object* v_fvarId_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_636_ = l_Lean_instEmptyCollectionFVarIdHashSet;
lean_inc_n(v_fvarId_630_, 2);
v___x_637_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_fvarId_630_);
v___x_638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
lean_ctor_set(v___x_638_, 1, v_fvarId_630_);
v___x_639_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go(v_fvarId_630_, v_c_629_, v___x_638_, v___x_636_, v_a_631_, v_a_632_, v_a_633_, v_a_634_);
lean_dec_ref_known(v___x_638_, 2);
lean_dec(v_fvarId_630_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_648_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_648_ == 0)
{
v___x_642_ = v___x_639_;
v_isShared_643_ = v_isSharedCheck_648_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_639_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_648_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v_fst_644_; lean_object* v___x_646_; 
v_fst_644_ = lean_ctor_get(v_a_640_, 0);
lean_inc(v_fst_644_);
lean_dec(v_a_640_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 0, v_fst_644_);
v___x_646_ = v___x_642_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_fst_644_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
else
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_656_; 
v_a_649_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_656_ == 0)
{
v___x_651_ = v___x_639_;
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v___x_639_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_649_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_isFVarLiveIn___boxed(lean_object* v_c_657_, lean_object* v_fvarId_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Lean_Compiler_LCNF_Code_isFVarLiveIn(v_c_657_, v_fvarId_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_);
lean_dec(v_a_662_);
lean_dec_ref(v_a_661_);
lean_dec(v_a_660_);
lean_dec_ref(v_a_659_);
return v_res_664_;
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
