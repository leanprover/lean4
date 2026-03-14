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
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
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
lean_object* lean_panic_fn(lean_object*, lean_object*);
extern lean_object* l_Lean_instEmptyCollectionFVarIdHashSet;
extern lean_object* l_Lean_instSingletonFVarIdFVarIdSet;
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
v___x_75_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2(lean_object* v_msg_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v_toApplicative_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_163_; 
v___x_88_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__0);
v___x_89_ = l_ReaderT_instMonad___redArg(v___x_88_);
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
v___x_113_ = l_ReaderT_instMonad___redArg(v___x_112_);
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
lean_object* v___f_137_; lean_object* v___f_138_; lean_object* v___f_139_; lean_object* v___f_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; uint8_t v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___f_150_; lean_object* v___x_17248__overap_151_; lean_object* v___x_152_; 
lean_inc_ref(v___x_136_);
v___f_137_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_137_, 0, v___x_136_);
lean_inc_ref(v___x_136_);
v___f_138_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_138_, 0, v___x_136_);
lean_inc_ref(v___x_136_);
v___f_139_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_139_, 0, v___x_136_);
lean_inc_ref(v___x_136_);
v___f_140_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_140_, 0, v___x_136_);
lean_inc_ref(v___x_136_);
v___x_141_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_141_, 0, lean_box(0));
lean_closure_set(v___x_141_, 1, lean_box(0));
lean_closure_set(v___x_141_, 2, v___x_136_);
v___x_142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
lean_ctor_set(v___x_142_, 1, v___f_137_);
lean_inc_ref(v___x_136_);
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
v___x_17248__overap_151_ = lean_panic_fn(v___f_150_, v_msg_80_);
v___x_152_ = lean_apply_7(v___x_17248__overap_151_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, lean_box(0));
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
lean_object* v_decl_337_; lean_object* v_k_338_; lean_object* v_targetSet_339_; uint8_t v___x_340_; uint8_t v___x_341_; 
v_decl_337_ = lean_ctor_get(v_c_329_, 0);
lean_inc_ref(v_decl_337_);
v_k_338_ = lean_ctor_get(v_c_329_, 1);
lean_inc_ref(v_k_338_);
lean_dec_ref(v_c_329_);
v_targetSet_339_ = lean_ctor_get(v_a_330_, 0);
v___x_340_ = 1;
v___x_341_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn(v___x_340_, v_decl_337_, v_targetSet_339_);
lean_dec_ref(v_decl_337_);
if (v___x_341_ == 0)
{
v_c_329_ = v_k_338_;
goto _start;
}
else
{
lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_351_; 
lean_dec_ref(v_k_338_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
v_isSharedCheck_351_ = !lean_is_exclusive(v_a_330_);
if (v_isSharedCheck_351_ == 0)
{
lean_object* v_unused_352_; lean_object* v_unused_353_; 
v_unused_352_ = lean_ctor_get(v_a_330_, 1);
lean_dec(v_unused_352_);
v_unused_353_ = lean_ctor_get(v_a_330_, 0);
lean_dec(v_unused_353_);
v___x_344_ = v_a_330_;
v_isShared_345_ = v_isSharedCheck_351_;
goto v_resetjp_343_;
}
else
{
lean_dec(v_a_330_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_351_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_346_; lean_object* v___x_348_; 
v___x_346_ = lean_box(v___x_341_);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 1, v_a_331_);
lean_ctor_set(v___x_344_, 0, v___x_346_);
v___x_348_ = v___x_344_;
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
lean_object* v_decl_354_; lean_object* v_k_355_; lean_object* v_fvarId_356_; lean_object* v_value_357_; lean_object* v___x_358_; 
v_decl_354_ = lean_ctor_get(v_c_329_, 0);
lean_inc_ref(v_decl_354_);
v_k_355_ = lean_ctor_get(v_c_329_, 1);
lean_inc_ref(v_k_355_);
lean_dec_ref(v_c_329_);
v_fvarId_356_ = lean_ctor_get(v_decl_354_, 0);
lean_inc(v_fvarId_356_);
v_value_357_ = lean_ctor_get(v_decl_354_, 4);
lean_inc_ref(v_value_357_);
lean_dec_ref(v_decl_354_);
lean_inc(v_a_335_);
lean_inc_ref(v_a_334_);
lean_inc(v_a_333_);
lean_inc_ref(v_a_332_);
lean_inc_ref(v_a_330_);
v___x_358_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go(v_fvarId_328_, v_value_357_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_object* v_a_359_; lean_object* v_fst_360_; uint8_t v___x_361_; 
v_a_359_ = lean_ctor_get(v___x_358_, 0);
lean_inc(v_a_359_);
v_fst_360_ = lean_ctor_get(v_a_359_, 0);
v___x_361_ = lean_unbox(v_fst_360_);
if (v___x_361_ == 0)
{
lean_object* v_snd_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
lean_dec_ref(v___x_358_);
v_snd_362_ = lean_ctor_get(v_a_359_, 1);
lean_inc(v_snd_362_);
lean_dec(v_a_359_);
v___x_363_ = lean_box(0);
v___x_364_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0___redArg(v_snd_362_, v_fvarId_356_, v___x_363_);
v_c_329_ = v_k_355_;
v_a_331_ = v___x_364_;
goto _start;
}
else
{
lean_dec(v_a_359_);
lean_dec(v_fvarId_356_);
lean_dec_ref(v_k_355_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec_ref(v_a_330_);
return v___x_358_;
}
}
else
{
lean_dec(v_fvarId_356_);
lean_dec_ref(v_k_355_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec_ref(v_a_330_);
return v___x_358_;
}
}
case 3:
{
lean_object* v_fvarId_366_; lean_object* v_args_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_406_; 
v_fvarId_366_ = lean_ctor_get(v_c_329_, 0);
v_args_367_ = lean_ctor_get(v_c_329_, 1);
v_isSharedCheck_406_ = !lean_is_exclusive(v_c_329_);
if (v_isSharedCheck_406_ == 0)
{
v___x_369_ = v_c_329_;
v_isShared_370_ = v_isSharedCheck_406_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_args_367_);
lean_inc(v_fvarId_366_);
lean_dec(v_c_329_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_406_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
uint8_t v___y_372_; lean_object* v___x_397_; lean_object* v___x_398_; uint8_t v___x_399_; 
v___x_397_ = lean_unsigned_to_nat(0u);
v___x_398_ = lean_array_get_size(v_args_367_);
v___x_399_ = lean_nat_dec_lt(v___x_397_, v___x_398_);
if (v___x_399_ == 0)
{
lean_dec_ref(v_args_367_);
v___y_372_ = v___x_399_;
goto v___jp_371_;
}
else
{
if (v___x_399_ == 0)
{
lean_dec_ref(v_args_367_);
v___y_372_ = v___x_399_;
goto v___jp_371_;
}
else
{
size_t v___x_400_; size_t v___x_401_; uint8_t v___x_402_; 
v___x_400_ = ((size_t)0ULL);
v___x_401_ = lean_usize_of_nat(v___x_398_);
v___x_402_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3(v_a_330_, v_args_367_, v___x_400_, v___x_401_);
lean_dec_ref(v_args_367_);
if (v___x_402_ == 0)
{
v___y_372_ = v___x_402_;
goto v___jp_371_;
}
else
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
lean_del_object(v___x_369_);
lean_dec(v_fvarId_366_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec_ref(v_a_330_);
v___x_403_ = lean_box(v___x_402_);
v___x_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
lean_ctor_set(v___x_404_, 1, v_a_331_);
v___x_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
return v___x_405_;
}
}
}
v___jp_371_:
{
uint8_t v___x_373_; 
v___x_373_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___redArg(v_a_331_, v_fvarId_366_);
if (v___x_373_ == 0)
{
uint8_t v___x_374_; lean_object* v___x_375_; 
lean_del_object(v___x_369_);
v___x_374_ = 1;
v___x_375_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_374_, v_fvarId_366_, v_a_333_);
if (lean_obj_tag(v___x_375_) == 0)
{
lean_object* v_a_376_; 
v_a_376_ = lean_ctor_get(v___x_375_, 0);
lean_inc(v_a_376_);
lean_dec_ref(v___x_375_);
if (lean_obj_tag(v_a_376_) == 1)
{
lean_object* v_val_377_; lean_object* v_value_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v_val_377_ = lean_ctor_get(v_a_376_, 0);
lean_inc(v_val_377_);
lean_dec_ref(v_a_376_);
v_value_378_ = lean_ctor_get(v_val_377_, 4);
lean_inc_ref(v_value_378_);
lean_dec(v_val_377_);
v___x_379_ = lean_box(0);
v___x_380_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0___redArg(v_a_331_, v_fvarId_366_, v___x_379_);
v_c_329_ = v_value_378_;
v_a_331_ = v___x_380_;
goto _start;
}
else
{
lean_object* v___x_382_; lean_object* v___x_383_; 
lean_dec(v_a_376_);
lean_dec(v_fvarId_366_);
v___x_382_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__3, &l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__3);
v___x_383_ = l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2(v___x_382_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_);
return v___x_383_;
}
}
else
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_391_; 
lean_dec(v_fvarId_366_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec_ref(v_a_330_);
v_a_384_ = lean_ctor_get(v___x_375_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_391_ == 0)
{
v___x_386_ = v___x_375_;
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v___x_375_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
if (v_isShared_387_ == 0)
{
v___x_389_ = v___x_386_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_a_384_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
else
{
lean_object* v___x_392_; lean_object* v___x_394_; 
lean_dec(v_fvarId_366_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec_ref(v_a_330_);
v___x_392_ = lean_box(v___y_372_);
if (v_isShared_370_ == 0)
{
lean_ctor_set_tag(v___x_369_, 0);
lean_ctor_set(v___x_369_, 1, v_a_331_);
lean_ctor_set(v___x_369_, 0, v___x_392_);
v___x_394_ = v___x_369_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_392_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v_a_331_);
v___x_394_ = v_reuseFailAlloc_396_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
lean_object* v___x_395_; 
v___x_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
return v___x_395_;
}
}
}
}
}
case 4:
{
lean_object* v_cases_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_435_; 
v_cases_407_ = lean_ctor_get(v_c_329_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v_c_329_);
if (v_isSharedCheck_435_ == 0)
{
v___x_409_ = v_c_329_;
v_isShared_410_ = v_isSharedCheck_435_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_cases_407_);
lean_dec(v_c_329_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_435_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v_discr_411_; lean_object* v_alts_412_; uint8_t v___x_413_; 
v_discr_411_ = lean_ctor_get(v_cases_407_, 2);
lean_inc(v_discr_411_);
v_alts_412_ = lean_ctor_get(v_cases_407_, 3);
lean_inc_ref(v_alts_412_);
lean_dec_ref(v_cases_407_);
v___x_413_ = l_Lean_instBEqFVarId_beq(v_discr_411_, v_fvarId_328_);
lean_dec(v_discr_411_);
if (v___x_413_ == 0)
{
lean_object* v___x_414_; lean_object* v___x_415_; uint8_t v___x_416_; 
v___x_414_ = lean_unsigned_to_nat(0u);
v___x_415_ = lean_array_get_size(v_alts_412_);
v___x_416_ = lean_nat_dec_lt(v___x_414_, v___x_415_);
if (v___x_416_ == 0)
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_420_; 
lean_dec_ref(v_alts_412_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec_ref(v_a_330_);
v___x_417_ = lean_box(v___x_413_);
v___x_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
lean_ctor_set(v___x_418_, 1, v_a_331_);
if (v_isShared_410_ == 0)
{
lean_ctor_set_tag(v___x_409_, 0);
lean_ctor_set(v___x_409_, 0, v___x_418_);
v___x_420_ = v___x_409_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_418_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
else
{
if (v___x_416_ == 0)
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_425_; 
lean_dec_ref(v_alts_412_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec_ref(v_a_330_);
v___x_422_ = lean_box(v___x_413_);
v___x_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
lean_ctor_set(v___x_423_, 1, v_a_331_);
if (v_isShared_410_ == 0)
{
lean_ctor_set_tag(v___x_409_, 0);
lean_ctor_set(v___x_409_, 0, v___x_423_);
v___x_425_ = v___x_409_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_423_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
else
{
size_t v___x_427_; size_t v___x_428_; lean_object* v___x_429_; 
lean_del_object(v___x_409_);
v___x_427_ = ((size_t)0ULL);
v___x_428_ = lean_usize_of_nat(v___x_415_);
v___x_429_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__4(v_fvarId_328_, v_alts_412_, v___x_427_, v___x_428_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_);
lean_dec_ref(v_alts_412_);
return v___x_429_;
}
}
}
else
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_433_; 
lean_dec_ref(v_alts_412_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec_ref(v_a_330_);
v___x_430_ = lean_box(v___x_413_);
v___x_431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
lean_ctor_set(v___x_431_, 1, v_a_331_);
if (v_isShared_410_ == 0)
{
lean_ctor_set_tag(v___x_409_, 0);
lean_ctor_set(v___x_409_, 0, v___x_431_);
v___x_433_ = v___x_409_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_431_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_446_; 
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec_ref(v_a_330_);
v_fvarId_436_ = lean_ctor_get(v_c_329_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v_c_329_);
if (v_isSharedCheck_446_ == 0)
{
v___x_438_ = v_c_329_;
v_isShared_439_ = v_isSharedCheck_446_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_fvarId_436_);
lean_dec(v_c_329_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_446_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
uint8_t v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_444_; 
v___x_440_ = l_Lean_instBEqFVarId_beq(v_fvarId_436_, v_fvarId_328_);
lean_dec(v_fvarId_436_);
v___x_441_ = lean_box(v___x_440_);
v___x_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
lean_ctor_set(v___x_442_, 1, v_a_331_);
if (v_isShared_439_ == 0)
{
lean_ctor_set_tag(v___x_438_, 0);
lean_ctor_set(v___x_438_, 0, v___x_442_);
v___x_444_ = v___x_438_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_442_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
case 6:
{
lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_456_; 
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec_ref(v_a_330_);
v_isSharedCheck_456_ = !lean_is_exclusive(v_c_329_);
if (v_isSharedCheck_456_ == 0)
{
lean_object* v_unused_457_; 
v_unused_457_ = lean_ctor_get(v_c_329_, 0);
lean_dec(v_unused_457_);
v___x_448_ = v_c_329_;
v_isShared_449_ = v_isSharedCheck_456_;
goto v_resetjp_447_;
}
else
{
lean_dec(v_c_329_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_456_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
uint8_t v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_454_; 
v___x_450_ = 0;
v___x_451_ = lean_box(v___x_450_);
v___x_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
lean_ctor_set(v___x_452_, 1, v_a_331_);
if (v_isShared_449_ == 0)
{
lean_ctor_set_tag(v___x_448_, 0);
lean_ctor_set(v___x_448_, 0, v___x_452_);
v___x_454_ = v___x_448_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_452_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
case 7:
{
lean_object* v_fvarId_458_; lean_object* v_y_459_; lean_object* v_k_460_; uint8_t v___x_461_; 
v_fvarId_458_ = lean_ctor_get(v_c_329_, 0);
lean_inc(v_fvarId_458_);
v_y_459_ = lean_ctor_get(v_c_329_, 2);
lean_inc(v_y_459_);
v_k_460_ = lean_ctor_get(v_c_329_, 3);
lean_inc_ref(v_k_460_);
lean_dec_ref(v_c_329_);
v___x_461_ = l_Lean_instBEqFVarId_beq(v_fvarId_458_, v_fvarId_328_);
lean_dec(v_fvarId_458_);
if (v___x_461_ == 0)
{
lean_object* v_targetSet_462_; uint8_t v___x_463_; uint8_t v___x_464_; 
v_targetSet_462_ = lean_ctor_get(v_a_330_, 0);
v___x_463_ = 1;
v___x_464_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn(v___x_463_, v_y_459_, v_targetSet_462_);
lean_dec(v_y_459_);
if (v___x_464_ == 0)
{
v_c_329_ = v_k_460_;
goto _start;
}
else
{
lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_474_; 
lean_dec_ref(v_k_460_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
v_isSharedCheck_474_ = !lean_is_exclusive(v_a_330_);
if (v_isSharedCheck_474_ == 0)
{
lean_object* v_unused_475_; lean_object* v_unused_476_; 
v_unused_475_ = lean_ctor_get(v_a_330_, 1);
lean_dec(v_unused_475_);
v_unused_476_ = lean_ctor_get(v_a_330_, 0);
lean_dec(v_unused_476_);
v___x_467_ = v_a_330_;
v_isShared_468_ = v_isSharedCheck_474_;
goto v_resetjp_466_;
}
else
{
lean_dec(v_a_330_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_474_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_469_; lean_object* v___x_471_; 
v___x_469_ = lean_box(v___x_464_);
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 1, v_a_331_);
lean_ctor_set(v___x_467_, 0, v___x_469_);
v___x_471_ = v___x_467_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_469_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v_a_331_);
v___x_471_ = v_reuseFailAlloc_473_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_472_; 
v___x_472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
return v___x_472_;
}
}
}
}
else
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
lean_dec_ref(v_k_460_);
lean_dec(v_y_459_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec_ref(v_a_330_);
v___x_477_ = lean_box(v___x_461_);
v___x_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
lean_ctor_set(v___x_478_, 1, v_a_331_);
v___x_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
return v___x_479_;
}
}
case 8:
{
lean_object* v_fvarId_480_; lean_object* v_y_481_; lean_object* v_k_482_; uint8_t v___x_483_; 
v_fvarId_480_ = lean_ctor_get(v_c_329_, 0);
lean_inc(v_fvarId_480_);
v_y_481_ = lean_ctor_get(v_c_329_, 2);
lean_inc(v_y_481_);
v_k_482_ = lean_ctor_get(v_c_329_, 3);
lean_inc_ref(v_k_482_);
lean_dec_ref(v_c_329_);
v___x_483_ = l_Lean_instBEqFVarId_beq(v_fvarId_480_, v_fvarId_328_);
lean_dec(v_fvarId_480_);
if (v___x_483_ == 0)
{
uint8_t v___x_484_; 
v___x_484_ = l_Lean_instBEqFVarId_beq(v_y_481_, v_fvarId_328_);
lean_dec(v_y_481_);
if (v___x_484_ == 0)
{
v_c_329_ = v_k_482_;
goto _start;
}
else
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
lean_dec_ref(v_k_482_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec_ref(v_a_330_);
v___x_486_ = lean_box(v___x_484_);
v___x_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
lean_ctor_set(v___x_487_, 1, v_a_331_);
v___x_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
return v___x_488_;
}
}
else
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
lean_dec_ref(v_k_482_);
lean_dec(v_y_481_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec_ref(v_a_330_);
v___x_489_ = lean_box(v___x_483_);
v___x_490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
lean_ctor_set(v___x_490_, 1, v_a_331_);
v___x_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
return v___x_491_;
}
}
case 9:
{
lean_object* v_fvarId_492_; lean_object* v_y_493_; lean_object* v_k_494_; uint8_t v___x_495_; 
v_fvarId_492_ = lean_ctor_get(v_c_329_, 0);
lean_inc(v_fvarId_492_);
v_y_493_ = lean_ctor_get(v_c_329_, 3);
lean_inc(v_y_493_);
v_k_494_ = lean_ctor_get(v_c_329_, 5);
lean_inc_ref(v_k_494_);
lean_dec_ref(v_c_329_);
v___x_495_ = l_Lean_instBEqFVarId_beq(v_fvarId_492_, v_fvarId_328_);
lean_dec(v_fvarId_492_);
if (v___x_495_ == 0)
{
uint8_t v___x_496_; 
v___x_496_ = l_Lean_instBEqFVarId_beq(v_y_493_, v_fvarId_328_);
lean_dec(v_y_493_);
if (v___x_496_ == 0)
{
v_c_329_ = v_k_494_;
goto _start;
}
else
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
lean_dec_ref(v_k_494_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec_ref(v_a_330_);
v___x_498_ = lean_box(v___x_496_);
v___x_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
lean_ctor_set(v___x_499_, 1, v_a_331_);
v___x_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
return v___x_500_;
}
}
else
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
lean_dec_ref(v_k_494_);
lean_dec(v_y_493_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec_ref(v_a_330_);
v___x_501_ = lean_box(v___x_495_);
v___x_502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
lean_ctor_set(v___x_502_, 1, v_a_331_);
v___x_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
return v___x_503_;
}
}
case 13:
{
lean_object* v_fvarId_504_; lean_object* v_k_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_516_; 
v_fvarId_504_ = lean_ctor_get(v_c_329_, 0);
v_k_505_ = lean_ctor_get(v_c_329_, 1);
v_isSharedCheck_516_ = !lean_is_exclusive(v_c_329_);
if (v_isSharedCheck_516_ == 0)
{
v___x_507_ = v_c_329_;
v_isShared_508_ = v_isSharedCheck_516_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_k_505_);
lean_inc(v_fvarId_504_);
lean_dec(v_c_329_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_516_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
uint8_t v___x_509_; 
v___x_509_ = l_Lean_instBEqFVarId_beq(v_fvarId_504_, v_fvarId_328_);
lean_dec(v_fvarId_504_);
if (v___x_509_ == 0)
{
lean_del_object(v___x_507_);
v_c_329_ = v_k_505_;
goto _start;
}
else
{
lean_object* v___x_511_; lean_object* v___x_513_; 
lean_dec_ref(v_k_505_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec_ref(v_a_330_);
v___x_511_ = lean_box(v___x_509_);
if (v_isShared_508_ == 0)
{
lean_ctor_set_tag(v___x_507_, 0);
lean_ctor_set(v___x_507_, 1, v_a_331_);
lean_ctor_set(v___x_507_, 0, v___x_511_);
v___x_513_ = v___x_507_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_a_331_);
v___x_513_ = v_reuseFailAlloc_515_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
lean_object* v___x_514_; 
v___x_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
return v___x_514_;
}
}
}
}
default: 
{
lean_object* v_fvarId_517_; lean_object* v_k_518_; uint8_t v___x_519_; 
v_fvarId_517_ = lean_ctor_get(v_c_329_, 0);
lean_inc(v_fvarId_517_);
v_k_518_ = lean_ctor_get(v_c_329_, 2);
lean_inc_ref(v_k_518_);
lean_dec_ref(v_c_329_);
v___x_519_ = l_Lean_instBEqFVarId_beq(v_fvarId_517_, v_fvarId_328_);
lean_dec(v_fvarId_517_);
if (v___x_519_ == 0)
{
v_c_329_ = v_k_518_;
goto _start;
}
else
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
lean_dec_ref(v_k_518_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec_ref(v_a_330_);
v___x_521_ = lean_box(v___x_519_);
v___x_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
lean_ctor_set(v___x_522_, 1, v_a_331_);
v___x_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
return v___x_523_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__4(lean_object* v_fvarId_524_, lean_object* v_as_525_, size_t v_i_526_, size_t v_stop_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
uint8_t v___x_535_; 
v___x_535_ = lean_usize_dec_eq(v_i_526_, v_stop_527_);
if (v___x_535_ == 0)
{
uint8_t v___x_536_; lean_object* v___y_538_; lean_object* v___x_564_; 
v___x_536_ = 1;
v___x_564_ = lean_array_uget_borrowed(v_as_525_, v_i_526_);
switch(lean_obj_tag(v___x_564_))
{
case 0:
{
lean_object* v_code_565_; 
v_code_565_ = lean_ctor_get(v___x_564_, 2);
lean_inc_ref(v_code_565_);
v___y_538_ = v_code_565_;
goto v___jp_537_;
}
case 1:
{
lean_object* v_code_566_; 
v_code_566_ = lean_ctor_get(v___x_564_, 1);
lean_inc_ref(v_code_566_);
v___y_538_ = v_code_566_;
goto v___jp_537_;
}
default: 
{
lean_object* v_code_567_; 
v_code_567_ = lean_ctor_get(v___x_564_, 0);
lean_inc_ref(v_code_567_);
v___y_538_ = v_code_567_;
goto v___jp_537_;
}
}
v___jp_537_:
{
lean_object* v___x_539_; 
lean_inc(v___y_533_);
lean_inc_ref(v___y_532_);
lean_inc(v___y_531_);
lean_inc_ref(v___y_530_);
lean_inc_ref(v___y_528_);
v___x_539_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go(v_fvarId_524_, v___y_538_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_563_; 
v_a_540_ = lean_ctor_get(v___x_539_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_563_ == 0)
{
v___x_542_ = v___x_539_;
v_isShared_543_ = v_isSharedCheck_563_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_539_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_563_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v_fst_544_; uint8_t v___x_545_; 
v_fst_544_ = lean_ctor_get(v_a_540_, 0);
v___x_545_ = lean_unbox(v_fst_544_);
if (v___x_545_ == 0)
{
lean_object* v_snd_546_; size_t v___x_547_; size_t v___x_548_; 
lean_del_object(v___x_542_);
v_snd_546_ = lean_ctor_get(v_a_540_, 1);
lean_inc(v_snd_546_);
lean_dec(v_a_540_);
v___x_547_ = ((size_t)1ULL);
v___x_548_ = lean_usize_add(v_i_526_, v___x_547_);
v_i_526_ = v___x_548_;
v___y_529_ = v_snd_546_;
goto _start;
}
else
{
lean_object* v_snd_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_561_; 
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec_ref(v___y_528_);
v_snd_550_ = lean_ctor_get(v_a_540_, 1);
v_isSharedCheck_561_ = !lean_is_exclusive(v_a_540_);
if (v_isSharedCheck_561_ == 0)
{
lean_object* v_unused_562_; 
v_unused_562_ = lean_ctor_get(v_a_540_, 0);
lean_dec(v_unused_562_);
v___x_552_ = v_a_540_;
v_isShared_553_ = v_isSharedCheck_561_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_snd_550_);
lean_dec(v_a_540_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_561_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_554_ = lean_box(v___x_536_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 0, v___x_554_);
v___x_556_ = v___x_552_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_554_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v_snd_550_);
v___x_556_ = v_reuseFailAlloc_560_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
lean_object* v___x_558_; 
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 0, v___x_556_);
v___x_558_ = v___x_542_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_556_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
}
}
else
{
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec_ref(v___y_528_);
return v___x_539_;
}
}
}
else
{
uint8_t v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec_ref(v___y_528_);
v___x_568_ = 0;
v___x_569_ = lean_box(v___x_568_);
v___x_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
lean_ctor_set(v___x_570_, 1, v___y_529_);
v___x_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
return v___x_571_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__4___boxed(lean_object* v_fvarId_572_, lean_object* v_as_573_, lean_object* v_i_574_, lean_object* v_stop_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
size_t v_i_boxed_583_; size_t v_stop_boxed_584_; lean_object* v_res_585_; 
v_i_boxed_583_ = lean_unbox_usize(v_i_574_);
lean_dec(v_i_574_);
v_stop_boxed_584_ = lean_unbox_usize(v_stop_575_);
lean_dec(v_stop_575_);
v_res_585_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__4(v_fvarId_572_, v_as_573_, v_i_boxed_583_, v_stop_boxed_584_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
lean_dec_ref(v_as_573_);
lean_dec(v_fvarId_572_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___boxed(lean_object* v_fvarId_586_, lean_object* v_c_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go(v_fvarId_586_, v_c_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_);
lean_dec(v_fvarId_586_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0(lean_object* v_00_u03b2_596_, lean_object* v_m_597_, lean_object* v_a_598_, lean_object* v_b_599_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0___redArg(v_m_597_, v_a_598_, v_b_599_);
return v___x_600_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1(lean_object* v_00_u03b2_601_, lean_object* v_m_602_, lean_object* v_a_603_){
_start:
{
uint8_t v___x_604_; 
v___x_604_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___redArg(v_m_602_, v_a_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___boxed(lean_object* v_00_u03b2_605_, lean_object* v_m_606_, lean_object* v_a_607_){
_start:
{
uint8_t v_res_608_; lean_object* v_r_609_; 
v_res_608_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1(v_00_u03b2_605_, v_m_606_, v_a_607_);
lean_dec(v_a_607_);
lean_dec_ref(v_m_606_);
v_r_609_ = lean_box(v_res_608_);
return v_r_609_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0(lean_object* v_00_u03b2_610_, lean_object* v_a_611_, lean_object* v_x_612_){
_start:
{
uint8_t v___x_613_; 
v___x_613_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0___redArg(v_a_611_, v_x_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_614_, lean_object* v_a_615_, lean_object* v_x_616_){
_start:
{
uint8_t v_res_617_; lean_object* v_r_618_; 
v_res_617_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0(v_00_u03b2_614_, v_a_615_, v_x_616_);
lean_dec(v_x_616_);
lean_dec(v_a_615_);
v_r_618_ = lean_box(v_res_617_);
return v_r_618_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1(lean_object* v_00_u03b2_619_, lean_object* v_data_620_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1___redArg(v_data_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_622_, lean_object* v_i_623_, lean_object* v_source_624_, lean_object* v_target_625_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1_spec__3___redArg(v_i_623_, v_source_624_, v_target_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_627_, lean_object* v_x_628_, lean_object* v_x_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1_spec__3_spec__7___redArg(v_x_628_, v_x_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_isFVarLiveIn(lean_object* v_c_631_, lean_object* v_fvarId_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_){
_start:
{
lean_object* v___x_638_; lean_object* v___x_12__overap_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_638_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_12__overap_639_ = l_Lean_instSingletonFVarIdFVarIdSet;
lean_inc(v_fvarId_632_);
v___x_640_ = lean_apply_1(v___x_12__overap_639_, v_fvarId_632_);
lean_inc(v_fvarId_632_);
v___x_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
lean_ctor_set(v___x_641_, 1, v_fvarId_632_);
v___x_642_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go(v_fvarId_632_, v_c_631_, v___x_641_, v___x_638_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
lean_dec(v_fvarId_632_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_651_; 
v_a_643_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_651_ == 0)
{
v___x_645_ = v___x_642_;
v_isShared_646_ = v_isSharedCheck_651_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_642_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_651_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v_fst_647_; lean_object* v___x_649_; 
v_fst_647_ = lean_ctor_get(v_a_643_, 0);
lean_inc(v_fst_647_);
lean_dec(v_a_643_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 0, v_fst_647_);
v___x_649_ = v___x_645_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_fst_647_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
else
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
v_a_652_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v___x_642_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_642_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_a_652_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_isFVarLiveIn___boxed(lean_object* v_c_660_, lean_object* v_fvarId_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Lean_Compiler_LCNF_Code_isFVarLiveIn(v_c_660_, v_fvarId_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_);
return v_res_667_;
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
