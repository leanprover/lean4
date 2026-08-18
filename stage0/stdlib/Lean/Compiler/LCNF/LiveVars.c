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
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Lean_instHashableFVarId_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqFVarId_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(uint8_t, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn(uint8_t, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
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
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__4(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___redArg___boxed(lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__2_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "_private.Lean.Compiler.LCNF.LiveVars.0.Lean.Compiler.LCNF.Code.isFVarLiveIn.go"};
static const lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Compiler.LCNF.LiveVars"};
static const lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___y_46_; lean_object* v___y_50_; lean_object* v_i_51_; lean_object* v___y_57_; lean_object* v___y_67_; lean_object* v_i_68_; lean_object* v___x_83_; 
v___x_42_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg___closed__0));
v___x_43_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg___closed__1));
v___x_44_ = lean_box(0);
lean_inc(v_jp_39_);
v___x_83_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_42_, v___x_43_, v_a_40_, v_jp_39_);
switch(lean_obj_tag(v___x_83_))
{
case 0:
{
lean_dec_ref_known(v___x_83_, 3);
lean_dec(v_jp_39_);
v___y_46_ = v_a_40_;
goto v___jp_45_;
}
case 1:
{
lean_object* v_index_84_; lean_object* v_size_85_; lean_object* v_keyArray_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; 
v_index_84_ = lean_ctor_get(v___x_83_, 0);
lean_inc(v_index_84_);
lean_dec_ref_known(v___x_83_, 1);
v_size_85_ = lean_ctor_get(v_a_40_, 0);
v_keyArray_86_ = lean_ctor_get(v_a_40_, 1);
v___x_87_ = lean_unsigned_to_nat(1u);
v___x_88_ = lean_nat_add(v_size_85_, v___x_87_);
v___x_89_ = lean_array_get_size(v_keyArray_86_);
v___x_90_ = lean_nat_dec_lt(v___x_88_, v___x_89_);
if (v___x_90_ == 0)
{
lean_dec(v___x_88_);
lean_dec(v_index_84_);
goto v___jp_73_;
}
else
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; uint8_t v___x_95_; 
v___x_91_ = lean_unsigned_to_nat(4u);
v___x_92_ = lean_nat_mul(v___x_88_, v___x_91_);
v___x_93_ = lean_unsigned_to_nat(3u);
v___x_94_ = lean_nat_mul(v___x_89_, v___x_93_);
v___x_95_ = lean_nat_dec_le(v___x_92_, v___x_94_);
lean_dec(v___x_94_);
lean_dec(v___x_92_);
if (v___x_95_ == 0)
{
lean_dec(v___x_88_);
lean_dec(v_index_84_);
goto v___jp_73_;
}
else
{
lean_object* v___x_96_; 
v___x_96_ = l_Std_DHashMap_Raw_setEntry___redArg(v_a_40_, v___x_88_, v_index_84_, v_jp_39_, v___x_44_);
lean_dec(v_index_84_);
v___y_46_ = v___x_96_;
goto v___jp_45_;
}
}
}
default: 
{
lean_object* v_size_97_; lean_object* v_keyArray_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; 
v_size_97_ = lean_ctor_get(v_a_40_, 0);
v_keyArray_98_ = lean_ctor_get(v_a_40_, 1);
v___x_99_ = lean_unsigned_to_nat(1u);
v___x_100_ = lean_nat_add(v_size_97_, v___x_99_);
v___x_101_ = lean_array_get_size(v_keyArray_98_);
v___x_102_ = lean_nat_dec_lt(v___x_100_, v___x_101_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; 
lean_dec(v___x_100_);
v___x_103_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_42_, v___x_43_, v_a_40_);
v___y_57_ = v___x_103_;
goto v___jp_56_;
}
else
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_104_ = lean_unsigned_to_nat(4u);
v___x_105_ = lean_nat_mul(v___x_100_, v___x_104_);
lean_dec(v___x_100_);
v___x_106_ = lean_unsigned_to_nat(3u);
v___x_107_ = lean_nat_mul(v___x_101_, v___x_106_);
v___x_108_ = lean_nat_dec_le(v___x_105_, v___x_107_);
lean_dec(v___x_107_);
lean_dec(v___x_105_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; 
v___x_109_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_42_, v___x_43_, v_a_40_);
v___y_57_ = v___x_109_;
goto v___jp_56_;
}
else
{
v___y_57_ = v_a_40_;
goto v___jp_56_;
}
}
}
}
v___jp_45_:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_47_, 0, v___x_44_);
lean_ctor_set(v___x_47_, 1, v___y_46_);
v___x_48_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
return v___x_48_;
}
v___jp_49_:
{
lean_object* v_size_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v_size_52_ = lean_ctor_get(v___y_50_, 0);
v___x_53_ = lean_unsigned_to_nat(1u);
v___x_54_ = lean_nat_add(v_size_52_, v___x_53_);
v___x_55_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_50_, v___x_54_, v_i_51_, v_jp_39_, v___x_44_);
lean_dec(v_i_51_);
v___y_46_ = v___x_55_;
goto v___jp_45_;
}
v___jp_56_:
{
lean_object* v___x_58_; 
lean_inc(v_jp_39_);
v___x_58_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_42_, v___x_43_, v___y_57_, v_jp_39_);
switch(lean_obj_tag(v___x_58_))
{
case 0:
{
lean_object* v_index_59_; lean_object* v_size_60_; lean_object* v___x_61_; 
v_index_59_ = lean_ctor_get(v___x_58_, 0);
lean_inc(v_index_59_);
lean_dec_ref_known(v___x_58_, 3);
v_size_60_ = lean_ctor_get(v___y_57_, 0);
lean_inc(v_size_60_);
v___x_61_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_57_, v_size_60_, v_index_59_, v_jp_39_, v___x_44_);
lean_dec(v_index_59_);
v___y_46_ = v___x_61_;
goto v___jp_45_;
}
case 1:
{
lean_object* v_index_62_; 
v_index_62_ = lean_ctor_get(v___x_58_, 0);
lean_inc(v_index_62_);
lean_dec_ref_known(v___x_58_, 1);
v___y_50_ = v___y_57_;
v_i_51_ = v_index_62_;
goto v___jp_49_;
}
default: 
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = lean_unsigned_to_nat(0u);
v___x_64_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_57_, v___x_63_);
if (lean_obj_tag(v___x_64_) == 0)
{
lean_object* v_index_65_; 
v_index_65_ = lean_ctor_get(v___x_64_, 0);
lean_inc(v_index_65_);
lean_dec_ref_known(v___x_64_, 1);
v___y_50_ = v___y_57_;
v_i_51_ = v_index_65_;
goto v___jp_49_;
}
else
{
lean_dec(v_jp_39_);
v___y_46_ = v___y_57_;
goto v___jp_45_;
}
}
}
}
v___jp_66_:
{
lean_object* v_size_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v_size_69_ = lean_ctor_get(v___y_67_, 0);
v___x_70_ = lean_unsigned_to_nat(1u);
v___x_71_ = lean_nat_add(v_size_69_, v___x_70_);
v___x_72_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_67_, v___x_71_, v_i_68_, v_jp_39_, v___x_44_);
lean_dec(v_i_68_);
v___y_46_ = v___x_72_;
goto v___jp_45_;
}
v___jp_73_:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_42_, v___x_43_, v_a_40_);
lean_inc(v_jp_39_);
v___x_75_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_42_, v___x_43_, v___x_74_, v_jp_39_);
switch(lean_obj_tag(v___x_75_))
{
case 0:
{
lean_object* v_index_76_; lean_object* v_size_77_; lean_object* v___x_78_; 
v_index_76_ = lean_ctor_get(v___x_75_, 0);
lean_inc(v_index_76_);
lean_dec_ref_known(v___x_75_, 3);
v_size_77_ = lean_ctor_get(v___x_74_, 0);
lean_inc(v_size_77_);
v___x_78_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_74_, v_size_77_, v_index_76_, v_jp_39_, v___x_44_);
lean_dec(v_index_76_);
v___y_46_ = v___x_78_;
goto v___jp_45_;
}
case 1:
{
lean_object* v_index_79_; 
v_index_79_ = lean_ctor_get(v___x_75_, 0);
lean_inc(v_index_79_);
lean_dec_ref_known(v___x_75_, 1);
v___y_67_ = v___x_74_;
v_i_68_ = v_index_79_;
goto v___jp_66_;
}
default: 
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = lean_unsigned_to_nat(0u);
v___x_81_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_74_, v___x_80_);
if (lean_obj_tag(v___x_81_) == 0)
{
lean_object* v_index_82_; 
v_index_82_ = lean_ctor_get(v___x_81_, 0);
lean_inc(v_index_82_);
lean_dec_ref_known(v___x_81_, 1);
v___y_67_ = v___x_74_;
v_i_68_ = v_index_82_;
goto v___jp_66_;
}
else
{
lean_dec(v_jp_39_);
v___y_46_ = v___x_74_;
goto v___jp_45_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg___boxed(lean_object* v_jp_110_, lean_object* v_a_111_, lean_object* v_a_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg(v_jp_110_, v_a_111_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited(lean_object* v_jp_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___y_126_; lean_object* v___y_130_; lean_object* v_i_131_; lean_object* v___y_137_; lean_object* v___y_147_; lean_object* v_i_148_; lean_object* v___x_163_; 
v___x_122_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg___closed__0));
v___x_123_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg___closed__1));
v___x_124_ = lean_box(0);
lean_inc(v_jp_114_);
v___x_163_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_122_, v___x_123_, v_a_116_, v_jp_114_);
switch(lean_obj_tag(v___x_163_))
{
case 0:
{
lean_dec_ref_known(v___x_163_, 3);
lean_dec(v_jp_114_);
v___y_126_ = v_a_116_;
goto v___jp_125_;
}
case 1:
{
lean_object* v_index_164_; lean_object* v_size_165_; lean_object* v_keyArray_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; uint8_t v___x_170_; 
v_index_164_ = lean_ctor_get(v___x_163_, 0);
lean_inc(v_index_164_);
lean_dec_ref_known(v___x_163_, 1);
v_size_165_ = lean_ctor_get(v_a_116_, 0);
v_keyArray_166_ = lean_ctor_get(v_a_116_, 1);
v___x_167_ = lean_unsigned_to_nat(1u);
v___x_168_ = lean_nat_add(v_size_165_, v___x_167_);
v___x_169_ = lean_array_get_size(v_keyArray_166_);
v___x_170_ = lean_nat_dec_lt(v___x_168_, v___x_169_);
if (v___x_170_ == 0)
{
lean_dec(v___x_168_);
lean_dec(v_index_164_);
goto v___jp_153_;
}
else
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_171_ = lean_unsigned_to_nat(4u);
v___x_172_ = lean_nat_mul(v___x_168_, v___x_171_);
v___x_173_ = lean_unsigned_to_nat(3u);
v___x_174_ = lean_nat_mul(v___x_169_, v___x_173_);
v___x_175_ = lean_nat_dec_le(v___x_172_, v___x_174_);
lean_dec(v___x_174_);
lean_dec(v___x_172_);
if (v___x_175_ == 0)
{
lean_dec(v___x_168_);
lean_dec(v_index_164_);
goto v___jp_153_;
}
else
{
lean_object* v___x_176_; 
v___x_176_ = l_Std_DHashMap_Raw_setEntry___redArg(v_a_116_, v___x_168_, v_index_164_, v_jp_114_, v___x_124_);
lean_dec(v_index_164_);
v___y_126_ = v___x_176_;
goto v___jp_125_;
}
}
}
default: 
{
lean_object* v_size_177_; lean_object* v_keyArray_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; uint8_t v___x_182_; 
v_size_177_ = lean_ctor_get(v_a_116_, 0);
v_keyArray_178_ = lean_ctor_get(v_a_116_, 1);
v___x_179_ = lean_unsigned_to_nat(1u);
v___x_180_ = lean_nat_add(v_size_177_, v___x_179_);
v___x_181_ = lean_array_get_size(v_keyArray_178_);
v___x_182_ = lean_nat_dec_lt(v___x_180_, v___x_181_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; 
lean_dec(v___x_180_);
v___x_183_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_122_, v___x_123_, v_a_116_);
v___y_137_ = v___x_183_;
goto v___jp_136_;
}
else
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_184_ = lean_unsigned_to_nat(4u);
v___x_185_ = lean_nat_mul(v___x_180_, v___x_184_);
lean_dec(v___x_180_);
v___x_186_ = lean_unsigned_to_nat(3u);
v___x_187_ = lean_nat_mul(v___x_181_, v___x_186_);
v___x_188_ = lean_nat_dec_le(v___x_185_, v___x_187_);
lean_dec(v___x_187_);
lean_dec(v___x_185_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; 
v___x_189_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_122_, v___x_123_, v_a_116_);
v___y_137_ = v___x_189_;
goto v___jp_136_;
}
else
{
v___y_137_ = v_a_116_;
goto v___jp_136_;
}
}
}
}
v___jp_125_:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_127_, 0, v___x_124_);
lean_ctor_set(v___x_127_, 1, v___y_126_);
v___x_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
return v___x_128_;
}
v___jp_129_:
{
lean_object* v_size_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v_size_132_ = lean_ctor_get(v___y_130_, 0);
v___x_133_ = lean_unsigned_to_nat(1u);
v___x_134_ = lean_nat_add(v_size_132_, v___x_133_);
v___x_135_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_130_, v___x_134_, v_i_131_, v_jp_114_, v___x_124_);
lean_dec(v_i_131_);
v___y_126_ = v___x_135_;
goto v___jp_125_;
}
v___jp_136_:
{
lean_object* v___x_138_; 
lean_inc(v_jp_114_);
v___x_138_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_122_, v___x_123_, v___y_137_, v_jp_114_);
switch(lean_obj_tag(v___x_138_))
{
case 0:
{
lean_object* v_index_139_; lean_object* v_size_140_; lean_object* v___x_141_; 
v_index_139_ = lean_ctor_get(v___x_138_, 0);
lean_inc(v_index_139_);
lean_dec_ref_known(v___x_138_, 3);
v_size_140_ = lean_ctor_get(v___y_137_, 0);
lean_inc(v_size_140_);
v___x_141_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_137_, v_size_140_, v_index_139_, v_jp_114_, v___x_124_);
lean_dec(v_index_139_);
v___y_126_ = v___x_141_;
goto v___jp_125_;
}
case 1:
{
lean_object* v_index_142_; 
v_index_142_ = lean_ctor_get(v___x_138_, 0);
lean_inc(v_index_142_);
lean_dec_ref_known(v___x_138_, 1);
v___y_130_ = v___y_137_;
v_i_131_ = v_index_142_;
goto v___jp_129_;
}
default: 
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = lean_unsigned_to_nat(0u);
v___x_144_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_137_, v___x_143_);
if (lean_obj_tag(v___x_144_) == 0)
{
lean_object* v_index_145_; 
v_index_145_ = lean_ctor_get(v___x_144_, 0);
lean_inc(v_index_145_);
lean_dec_ref_known(v___x_144_, 1);
v___y_130_ = v___y_137_;
v_i_131_ = v_index_145_;
goto v___jp_129_;
}
else
{
lean_dec(v_jp_114_);
v___y_126_ = v___y_137_;
goto v___jp_125_;
}
}
}
}
v___jp_146_:
{
lean_object* v_size_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v_size_149_ = lean_ctor_get(v___y_147_, 0);
v___x_150_ = lean_unsigned_to_nat(1u);
v___x_151_ = lean_nat_add(v_size_149_, v___x_150_);
v___x_152_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_147_, v___x_151_, v_i_148_, v_jp_114_, v___x_124_);
lean_dec(v_i_148_);
v___y_126_ = v___x_152_;
goto v___jp_125_;
}
v___jp_153_:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_122_, v___x_123_, v_a_116_);
lean_inc(v_jp_114_);
v___x_155_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_122_, v___x_123_, v___x_154_, v_jp_114_);
switch(lean_obj_tag(v___x_155_))
{
case 0:
{
lean_object* v_index_156_; lean_object* v_size_157_; lean_object* v___x_158_; 
v_index_156_ = lean_ctor_get(v___x_155_, 0);
lean_inc(v_index_156_);
lean_dec_ref_known(v___x_155_, 3);
v_size_157_ = lean_ctor_get(v___x_154_, 0);
lean_inc(v_size_157_);
v___x_158_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_154_, v_size_157_, v_index_156_, v_jp_114_, v___x_124_);
lean_dec(v_index_156_);
v___y_126_ = v___x_158_;
goto v___jp_125_;
}
case 1:
{
lean_object* v_index_159_; 
v_index_159_ = lean_ctor_get(v___x_155_, 0);
lean_inc(v_index_159_);
lean_dec_ref_known(v___x_155_, 1);
v___y_147_ = v___x_154_;
v_i_148_ = v_index_159_;
goto v___jp_146_;
}
default: 
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = lean_unsigned_to_nat(0u);
v___x_161_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_154_, v___x_160_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v_index_162_; 
v_index_162_ = lean_ctor_get(v___x_161_, 0);
lean_inc(v_index_162_);
lean_dec_ref_known(v___x_161_, 1);
v___y_147_ = v___x_154_;
v_i_148_ = v_index_162_;
goto v___jp_146_;
}
else
{
lean_dec(v_jp_114_);
v___y_126_ = v___x_154_;
goto v___jp_125_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___boxed(lean_object* v_jp_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited(v_jp_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_);
lean_dec(v_a_196_);
lean_dec_ref(v_a_195_);
lean_dec(v_a_194_);
lean_dec_ref(v_a_193_);
lean_dec_ref(v_a_191_);
return v_res_198_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3___closed__0(void){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l_instMonadEIO(lean_box(0));
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3(lean_object* v_msg_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v_toApplicative_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_287_; 
v___x_212_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3___closed__0);
v___x_213_ = l_StateRefT_x27_instMonad___redArg(v___x_212_);
v_toApplicative_214_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_287_ == 0)
{
lean_object* v_unused_288_; 
v_unused_288_ = lean_ctor_get(v___x_213_, 1);
lean_dec(v_unused_288_);
v___x_216_ = v___x_213_;
v_isShared_217_ = v_isSharedCheck_287_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_toApplicative_214_);
lean_dec(v___x_213_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_287_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v_toFunctor_218_; lean_object* v_toSeq_219_; lean_object* v_toSeqLeft_220_; lean_object* v_toSeqRight_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_285_; 
v_toFunctor_218_ = lean_ctor_get(v_toApplicative_214_, 0);
v_toSeq_219_ = lean_ctor_get(v_toApplicative_214_, 2);
v_toSeqLeft_220_ = lean_ctor_get(v_toApplicative_214_, 3);
v_toSeqRight_221_ = lean_ctor_get(v_toApplicative_214_, 4);
v_isSharedCheck_285_ = !lean_is_exclusive(v_toApplicative_214_);
if (v_isSharedCheck_285_ == 0)
{
lean_object* v_unused_286_; 
v_unused_286_ = lean_ctor_get(v_toApplicative_214_, 1);
lean_dec(v_unused_286_);
v___x_223_ = v_toApplicative_214_;
v_isShared_224_ = v_isSharedCheck_285_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_toSeqRight_221_);
lean_inc(v_toSeqLeft_220_);
lean_inc(v_toSeq_219_);
lean_inc(v_toFunctor_218_);
lean_dec(v_toApplicative_214_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_285_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___f_225_; lean_object* v___f_226_; lean_object* v___f_227_; lean_object* v___f_228_; lean_object* v___x_229_; lean_object* v___f_230_; lean_object* v___f_231_; lean_object* v___f_232_; lean_object* v___x_234_; 
v___f_225_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3___closed__1));
v___f_226_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3___closed__2));
lean_inc_ref(v_toFunctor_218_);
v___f_227_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_227_, 0, v_toFunctor_218_);
v___f_228_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_228_, 0, v_toFunctor_218_);
v___x_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_229_, 0, v___f_227_);
lean_ctor_set(v___x_229_, 1, v___f_228_);
v___f_230_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_230_, 0, v_toSeqRight_221_);
v___f_231_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_231_, 0, v_toSeqLeft_220_);
v___f_232_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_232_, 0, v_toSeq_219_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 4, v___f_230_);
lean_ctor_set(v___x_223_, 3, v___f_231_);
lean_ctor_set(v___x_223_, 2, v___f_232_);
lean_ctor_set(v___x_223_, 1, v___f_225_);
lean_ctor_set(v___x_223_, 0, v___x_229_);
v___x_234_ = v___x_223_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_229_);
lean_ctor_set(v_reuseFailAlloc_284_, 1, v___f_225_);
lean_ctor_set(v_reuseFailAlloc_284_, 2, v___f_232_);
lean_ctor_set(v_reuseFailAlloc_284_, 3, v___f_231_);
lean_ctor_set(v_reuseFailAlloc_284_, 4, v___f_230_);
v___x_234_ = v_reuseFailAlloc_284_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
lean_object* v___x_236_; 
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 1, v___f_226_);
lean_ctor_set(v___x_216_, 0, v___x_234_);
v___x_236_ = v___x_216_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_234_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v___f_226_);
v___x_236_ = v_reuseFailAlloc_283_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
lean_object* v___x_237_; lean_object* v_toApplicative_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_281_; 
v___x_237_ = l_StateRefT_x27_instMonad___redArg(v___x_236_);
v_toApplicative_238_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_281_ == 0)
{
lean_object* v_unused_282_; 
v_unused_282_ = lean_ctor_get(v___x_237_, 1);
lean_dec(v_unused_282_);
v___x_240_ = v___x_237_;
v_isShared_241_ = v_isSharedCheck_281_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_toApplicative_238_);
lean_dec(v___x_237_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_281_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v_toFunctor_242_; lean_object* v_toSeq_243_; lean_object* v_toSeqLeft_244_; lean_object* v_toSeqRight_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_279_; 
v_toFunctor_242_ = lean_ctor_get(v_toApplicative_238_, 0);
v_toSeq_243_ = lean_ctor_get(v_toApplicative_238_, 2);
v_toSeqLeft_244_ = lean_ctor_get(v_toApplicative_238_, 3);
v_toSeqRight_245_ = lean_ctor_get(v_toApplicative_238_, 4);
v_isSharedCheck_279_ = !lean_is_exclusive(v_toApplicative_238_);
if (v_isSharedCheck_279_ == 0)
{
lean_object* v_unused_280_; 
v_unused_280_ = lean_ctor_get(v_toApplicative_238_, 1);
lean_dec(v_unused_280_);
v___x_247_ = v_toApplicative_238_;
v_isShared_248_ = v_isSharedCheck_279_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_toSeqRight_245_);
lean_inc(v_toSeqLeft_244_);
lean_inc(v_toSeq_243_);
lean_inc(v_toFunctor_242_);
lean_dec(v_toApplicative_238_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_279_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___f_249_; lean_object* v___f_250_; lean_object* v___f_251_; lean_object* v___f_252_; lean_object* v___x_253_; lean_object* v___f_254_; lean_object* v___f_255_; lean_object* v___f_256_; lean_object* v___x_258_; 
v___f_249_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3___closed__3));
v___f_250_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3___closed__4));
lean_inc_ref(v_toFunctor_242_);
v___f_251_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_251_, 0, v_toFunctor_242_);
v___f_252_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_252_, 0, v_toFunctor_242_);
v___x_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_253_, 0, v___f_251_);
lean_ctor_set(v___x_253_, 1, v___f_252_);
v___f_254_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_254_, 0, v_toSeqRight_245_);
v___f_255_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_255_, 0, v_toSeqLeft_244_);
v___f_256_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_256_, 0, v_toSeq_243_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 4, v___f_254_);
lean_ctor_set(v___x_247_, 3, v___f_255_);
lean_ctor_set(v___x_247_, 2, v___f_256_);
lean_ctor_set(v___x_247_, 1, v___f_249_);
lean_ctor_set(v___x_247_, 0, v___x_253_);
v___x_258_ = v___x_247_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_253_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v___f_249_);
lean_ctor_set(v_reuseFailAlloc_278_, 2, v___f_256_);
lean_ctor_set(v_reuseFailAlloc_278_, 3, v___f_255_);
lean_ctor_set(v_reuseFailAlloc_278_, 4, v___f_254_);
v___x_258_ = v_reuseFailAlloc_278_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
lean_object* v___x_260_; 
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 1, v___f_250_);
lean_ctor_set(v___x_240_, 0, v___x_258_);
v___x_260_ = v___x_240_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_258_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v___f_250_);
v___x_260_ = v_reuseFailAlloc_277_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
lean_object* v___f_261_; lean_object* v___f_262_; lean_object* v___f_263_; lean_object* v___f_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; uint8_t v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___f_274_; lean_object* v___x_22740__overap_275_; lean_object* v___x_276_; 
lean_inc_ref_n(v___x_260_, 6);
v___f_261_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_261_, 0, v___x_260_);
v___f_262_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_262_, 0, v___x_260_);
v___f_263_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_263_, 0, v___x_260_);
v___f_264_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_264_, 0, v___x_260_);
v___x_265_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_265_, 0, lean_box(0));
lean_closure_set(v___x_265_, 1, lean_box(0));
lean_closure_set(v___x_265_, 2, v___x_260_);
v___x_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
lean_ctor_set(v___x_266_, 1, v___f_261_);
v___x_267_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_267_, 0, lean_box(0));
lean_closure_set(v___x_267_, 1, lean_box(0));
lean_closure_set(v___x_267_, 2, v___x_260_);
v___x_268_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_268_, 0, v___x_266_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
lean_ctor_set(v___x_268_, 2, v___f_262_);
lean_ctor_set(v___x_268_, 3, v___f_263_);
lean_ctor_set(v___x_268_, 4, v___f_264_);
v___x_269_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_269_, 0, lean_box(0));
lean_closure_set(v___x_269_, 1, lean_box(0));
lean_closure_set(v___x_269_, 2, v___x_260_);
v___x_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_268_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
v___x_271_ = 0;
v___x_272_ = lean_box(v___x_271_);
v___x_273_ = l_instInhabitedOfMonad___redArg(v___x_270_, v___x_272_);
v___f_274_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_274_, 0, v___x_273_);
v___x_22740__overap_275_ = lean_panic_fn_borrowed(v___f_274_, v_msg_204_);
lean_dec_ref(v___f_274_);
lean_inc(v___y_210_);
lean_inc_ref(v___y_209_);
lean_inc(v___y_208_);
lean_inc_ref(v___y_207_);
lean_inc_ref(v___y_205_);
v___x_276_ = lean_apply_7(v___x_22740__overap_275_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, lean_box(0));
return v___x_276_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3___boxed(lean_object* v_msg_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3(v_msg_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
lean_dec_ref(v___y_290_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0___redArg(lean_object* v_m_298_, lean_object* v_query_299_, lean_object* v_x_300_, lean_object* v_x_301_, lean_object* v_x_302_){
_start:
{
lean_object* v_zero_303_; uint8_t v_isZero_304_; 
v_zero_303_ = lean_unsigned_to_nat(0u);
v_isZero_304_ = lean_nat_dec_eq(v_x_301_, v_zero_303_);
if (v_isZero_304_ == 1)
{
lean_dec(v_x_302_);
lean_dec(v_x_301_);
if (lean_obj_tag(v_x_300_) == 0)
{
lean_object* v___x_305_; 
v___x_305_ = lean_box(2);
return v___x_305_;
}
else
{
lean_object* v_val_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_313_; 
v_val_306_ = lean_ctor_get(v_x_300_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v_x_300_);
if (v_isSharedCheck_313_ == 0)
{
v___x_308_ = v_x_300_;
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_val_306_);
lean_dec(v_x_300_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_311_; 
if (v_isShared_309_ == 0)
{
v___x_311_ = v___x_308_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_val_306_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
else
{
lean_object* v_keyArray_314_; lean_object* v_valueArray_315_; lean_object* v___x_316_; uint8_t v_isSome_317_; 
v_keyArray_314_ = lean_ctor_get(v_m_298_, 1);
v_valueArray_315_ = lean_ctor_get(v_m_298_, 2);
v___x_316_ = lean_array_fget_borrowed(v_keyArray_314_, v_x_302_);
v_isSome_317_ = lean_noption_is_some(v___x_316_);
if (v_isSome_317_ == 0)
{
lean_dec(v_x_301_);
if (lean_obj_tag(v_x_300_) == 0)
{
lean_object* v___x_318_; 
v___x_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_318_, 0, v_x_302_);
return v___x_318_;
}
else
{
lean_object* v_val_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_326_; 
lean_dec(v_x_302_);
v_val_319_ = lean_ctor_get(v_x_300_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v_x_300_);
if (v_isSharedCheck_326_ == 0)
{
v___x_321_ = v_x_300_;
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_val_319_);
lean_dec(v_x_300_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_324_; 
if (v_isShared_322_ == 0)
{
v___x_324_ = v___x_321_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_val_319_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
else
{
lean_object* v_one_327_; lean_object* v_n_328_; lean_object* v___y_330_; 
v_one_327_ = lean_unsigned_to_nat(1u);
v_n_328_ = lean_nat_sub(v_x_301_, v_one_327_);
lean_dec(v_x_301_);
if (v_isSome_317_ == 0)
{
goto v___jp_336_;
}
else
{
lean_object* v___x_338_; uint8_t v_isSome_339_; 
v___x_338_ = lean_array_fget_borrowed(v_valueArray_315_, v_x_302_);
v_isSome_339_ = lean_noption_is_some(v___x_338_);
if (v_isSome_339_ == 0)
{
goto v___jp_336_;
}
else
{
lean_object* v_val_340_; uint8_t v___x_341_; 
lean_inc(v___x_316_);
v_val_340_ = lean_noption_get(v___x_316_);
v___x_341_ = l_Lean_instBEqFVarId_beq(v_val_340_, v_query_299_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; 
lean_dec(v_val_340_);
v___x_342_ = lean_array_get_size(v_keyArray_314_);
v___x_343_ = lean_nat_add(v_x_302_, v_one_327_);
lean_dec(v_x_302_);
v___x_344_ = lean_nat_dec_lt(v___x_343_, v___x_342_);
if (v___x_344_ == 0)
{
lean_dec(v___x_343_);
v_x_301_ = v_n_328_;
v_x_302_ = v_zero_303_;
goto _start;
}
else
{
v_x_301_ = v_n_328_;
v_x_302_ = v___x_343_;
goto _start;
}
}
else
{
lean_object* v_val_347_; lean_object* v___x_348_; 
lean_dec(v_n_328_);
lean_dec(v_x_300_);
lean_inc(v___x_338_);
v_val_347_ = lean_noption_get(v___x_338_);
v___x_348_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_348_, 0, v_x_302_);
lean_ctor_set(v___x_348_, 1, v_val_340_);
lean_ctor_set(v___x_348_, 2, v_val_347_);
return v___x_348_;
}
}
}
v___jp_329_:
{
lean_object* v___x_331_; lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_331_ = lean_array_get_size(v_keyArray_314_);
v___x_332_ = lean_nat_add(v_x_302_, v_one_327_);
lean_dec(v_x_302_);
v___x_333_ = lean_nat_dec_lt(v___x_332_, v___x_331_);
if (v___x_333_ == 0)
{
lean_dec(v___x_332_);
v_x_300_ = v___y_330_;
v_x_301_ = v_n_328_;
v_x_302_ = v_zero_303_;
goto _start;
}
else
{
v_x_300_ = v___y_330_;
v_x_301_ = v_n_328_;
v_x_302_ = v___x_332_;
goto _start;
}
}
v___jp_336_:
{
if (lean_obj_tag(v_x_300_) == 0)
{
lean_object* v___x_337_; 
lean_inc(v_x_302_);
v___x_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_337_, 0, v_x_302_);
v___y_330_ = v___x_337_;
goto v___jp_329_;
}
else
{
v___y_330_ = v_x_300_;
goto v___jp_329_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0___redArg___boxed(lean_object* v_m_349_, lean_object* v_query_350_, lean_object* v_x_351_, lean_object* v_x_352_, lean_object* v_x_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0___redArg(v_m_349_, v_query_350_, v_x_351_, v_x_352_, v_x_353_);
lean_dec(v_query_350_);
lean_dec_ref(v_m_349_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0___redArg(lean_object* v_m_355_, lean_object* v_query_356_){
_start:
{
lean_object* v_keyArray_357_; lean_object* v___x_358_; uint64_t v___x_359_; uint64_t v___x_360_; uint64_t v___x_361_; uint64_t v_fold_362_; uint64_t v___x_363_; uint64_t v___x_364_; uint64_t v___x_365_; size_t v___x_366_; size_t v___x_367_; size_t v___x_368_; size_t v___x_369_; size_t v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v_keyArray_357_ = lean_ctor_get(v_m_355_, 1);
v___x_358_ = lean_array_get_size(v_keyArray_357_);
v___x_359_ = l_Lean_instHashableFVarId_hash(v_query_356_);
v___x_360_ = 32ULL;
v___x_361_ = lean_uint64_shift_right(v___x_359_, v___x_360_);
v_fold_362_ = lean_uint64_xor(v___x_359_, v___x_361_);
v___x_363_ = 16ULL;
v___x_364_ = lean_uint64_shift_right(v_fold_362_, v___x_363_);
v___x_365_ = lean_uint64_xor(v_fold_362_, v___x_364_);
v___x_366_ = lean_uint64_to_usize(v___x_365_);
v___x_367_ = lean_usize_of_nat(v___x_358_);
v___x_368_ = ((size_t)1ULL);
v___x_369_ = lean_usize_sub(v___x_367_, v___x_368_);
v___x_370_ = lean_usize_land(v___x_366_, v___x_369_);
v___x_371_ = lean_usize_to_nat(v___x_370_);
v___x_372_ = lean_box(0);
v___x_373_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0___redArg(v_m_355_, v_query_356_, v___x_372_, v___x_358_, v___x_371_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0___redArg___boxed(lean_object* v_m_374_, lean_object* v_query_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0___redArg(v_m_374_, v_query_375_);
lean_dec(v_query_375_);
lean_dec_ref(v_m_374_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2_spec__4___redArg(lean_object* v_m_377_, lean_object* v_query_378_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0___redArg(v_m_377_, v_query_378_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v_index_380_; lean_object* v_key_381_; lean_object* v_value_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_389_; 
v_index_380_ = lean_ctor_get(v___x_379_, 0);
v_key_381_ = lean_ctor_get(v___x_379_, 1);
v_value_382_ = lean_ctor_get(v___x_379_, 2);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_389_ == 0)
{
v___x_384_ = v___x_379_;
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_value_382_);
lean_inc(v_key_381_);
lean_inc(v_index_380_);
lean_dec(v___x_379_);
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
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_index_380_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v_key_381_);
lean_ctor_set(v_reuseFailAlloc_388_, 2, v_value_382_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
else
{
lean_object* v___x_390_; 
lean_dec(v___x_379_);
v___x_390_ = lean_box(1);
return v___x_390_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2_spec__4___redArg___boxed(lean_object* v_m_391_, lean_object* v_query_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2_spec__4___redArg(v_m_391_, v_query_392_);
lean_dec(v_query_392_);
lean_dec_ref(v_m_391_);
return v_res_393_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___redArg(lean_object* v_m_394_, lean_object* v_a_395_){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2_spec__4___redArg(v_m_394_, v_a_395_);
if (lean_obj_tag(v___x_396_) == 0)
{
uint8_t v___x_397_; 
lean_dec_ref_known(v___x_396_, 3);
v___x_397_ = 1;
return v___x_397_;
}
else
{
uint8_t v___x_398_; 
v___x_398_ = 0;
return v___x_398_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___redArg___boxed(lean_object* v_m_399_, lean_object* v_a_400_){
_start:
{
uint8_t v_res_401_; lean_object* v_r_402_; 
v_res_401_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___redArg(v_m_399_, v_a_400_);
lean_dec(v_a_400_);
lean_dec_ref(v_m_399_);
v_r_402_ = lean_box(v_res_401_);
return v_r_402_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__4(lean_object* v_a_403_, lean_object* v_as_404_, size_t v_i_405_, size_t v_stop_406_){
_start:
{
uint8_t v___x_407_; 
v___x_407_ = lean_usize_dec_eq(v_i_405_, v_stop_406_);
if (v___x_407_ == 0)
{
lean_object* v_targetSet_408_; lean_object* v___x_409_; uint8_t v___x_410_; uint8_t v___x_411_; 
v_targetSet_408_ = lean_ctor_get(v_a_403_, 0);
v___x_409_ = lean_array_uget_borrowed(v_as_404_, v_i_405_);
v___x_410_ = 1;
v___x_411_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn(v___x_410_, v___x_409_, v_targetSet_408_);
if (v___x_411_ == 0)
{
size_t v___x_412_; size_t v___x_413_; 
v___x_412_ = ((size_t)1ULL);
v___x_413_ = lean_usize_add(v_i_405_, v___x_412_);
v_i_405_ = v___x_413_;
goto _start;
}
else
{
return v___x_411_;
}
}
else
{
uint8_t v___x_415_; 
v___x_415_ = 0;
return v___x_415_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__4___boxed(lean_object* v_a_416_, lean_object* v_as_417_, lean_object* v_i_418_, lean_object* v_stop_419_){
_start:
{
size_t v_i_boxed_420_; size_t v_stop_boxed_421_; uint8_t v_res_422_; lean_object* v_r_423_; 
v_i_boxed_420_ = lean_unbox_usize(v_i_418_);
lean_dec(v_i_418_);
v_stop_boxed_421_ = lean_unbox_usize(v_stop_419_);
lean_dec(v_stop_419_);
v_res_422_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__4(v_a_416_, v_as_417_, v_i_boxed_420_, v_stop_boxed_421_);
lean_dec_ref(v_as_417_);
lean_dec_ref(v_a_416_);
v_r_423_ = lean_box(v_res_422_);
return v_r_423_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1_spec__2_spec__4___redArg(lean_object* v_b_424_, lean_object* v_acc_425_, lean_object* v_i_426_){
_start:
{
lean_object* v___y_428_; lean_object* v_keyArray_436_; lean_object* v_valueArray_437_; lean_object* v___x_438_; uint8_t v___x_439_; 
v_keyArray_436_ = lean_ctor_get(v_b_424_, 1);
v_valueArray_437_ = lean_ctor_get(v_b_424_, 2);
v___x_438_ = lean_array_get_size(v_keyArray_436_);
v___x_439_ = lean_nat_dec_lt(v_i_426_, v___x_438_);
if (v___x_439_ == 0)
{
lean_dec(v_i_426_);
return v_acc_425_;
}
else
{
lean_object* v___x_440_; uint8_t v_isSome_441_; 
v___x_440_ = lean_array_fget_borrowed(v_keyArray_436_, v_i_426_);
v_isSome_441_ = lean_noption_is_some(v___x_440_);
if (v_isSome_441_ == 0)
{
goto v___jp_432_;
}
else
{
lean_object* v___x_442_; uint8_t v_isSome_443_; 
v___x_442_ = lean_array_fget_borrowed(v_valueArray_437_, v_i_426_);
v_isSome_443_ = lean_noption_is_some(v___x_442_);
if (v_isSome_443_ == 0)
{
goto v___jp_432_;
}
else
{
lean_object* v_val_444_; lean_object* v_val_445_; lean_object* v_i_447_; lean_object* v___x_452_; 
lean_inc(v___x_440_);
v_val_444_ = lean_noption_get(v___x_440_);
lean_inc(v___x_442_);
v_val_445_ = lean_noption_get(v___x_442_);
v___x_452_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0___redArg(v_acc_425_, v_val_444_);
switch(lean_obj_tag(v___x_452_))
{
case 0:
{
lean_object* v_index_453_; lean_object* v_size_454_; lean_object* v___x_455_; 
v_index_453_ = lean_ctor_get(v___x_452_, 0);
lean_inc(v_index_453_);
lean_dec_ref_known(v___x_452_, 3);
v_size_454_ = lean_ctor_get(v_acc_425_, 0);
lean_inc(v_size_454_);
v___x_455_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_425_, v_size_454_, v_index_453_, v_val_444_, v_val_445_);
lean_dec(v_index_453_);
v___y_428_ = v___x_455_;
goto v___jp_427_;
}
case 1:
{
lean_object* v_index_456_; 
v_index_456_ = lean_ctor_get(v___x_452_, 0);
lean_inc(v_index_456_);
lean_dec_ref_known(v___x_452_, 1);
v_i_447_ = v_index_456_;
goto v___jp_446_;
}
default: 
{
lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_457_ = lean_unsigned_to_nat(0u);
v___x_458_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_425_, v___x_457_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v_index_459_; 
v_index_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc(v_index_459_);
lean_dec_ref_known(v___x_458_, 1);
v_i_447_ = v_index_459_;
goto v___jp_446_;
}
else
{
lean_dec(v_val_445_);
lean_dec(v_val_444_);
v___y_428_ = v_acc_425_;
goto v___jp_427_;
}
}
}
v___jp_446_:
{
lean_object* v_size_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v_size_448_ = lean_ctor_get(v_acc_425_, 0);
v___x_449_ = lean_unsigned_to_nat(1u);
v___x_450_ = lean_nat_add(v_size_448_, v___x_449_);
v___x_451_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_425_, v___x_450_, v_i_447_, v_val_444_, v_val_445_);
lean_dec(v_i_447_);
v___y_428_ = v___x_451_;
goto v___jp_427_;
}
}
}
}
v___jp_427_:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = lean_unsigned_to_nat(1u);
v___x_430_ = lean_nat_add(v_i_426_, v___x_429_);
lean_dec(v_i_426_);
v_acc_425_ = v___y_428_;
v_i_426_ = v___x_430_;
goto _start;
}
v___jp_432_:
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = lean_unsigned_to_nat(1u);
v___x_434_ = lean_nat_add(v_i_426_, v___x_433_);
lean_dec(v_i_426_);
v_i_426_ = v___x_434_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_b_460_, lean_object* v_acc_461_, lean_object* v_i_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1_spec__2_spec__4___redArg(v_b_460_, v_acc_461_, v_i_462_);
lean_dec_ref(v_b_460_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1_spec__2___redArg(lean_object* v_init_464_, lean_object* v_b_465_){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = lean_unsigned_to_nat(0u);
v___x_467_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1_spec__2_spec__4___redArg(v_b_465_, v_init_464_, v___x_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1_spec__2___redArg___boxed(lean_object* v_init_468_, lean_object* v_b_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1_spec__2___redArg(v_init_468_, v_b_469_);
lean_dec_ref(v_b_469_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___redArg(lean_object* v_m_471_){
_start:
{
lean_object* v_keyArray_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v_cellCount_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v_target_479_; lean_object* v___x_480_; 
v_keyArray_472_ = lean_ctor_get(v_m_471_, 1);
v___x_473_ = lean_array_get_size(v_keyArray_472_);
v___x_474_ = lean_unsigned_to_nat(2u);
v_cellCount_475_ = lean_nat_mul(v___x_473_, v___x_474_);
v___x_476_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_475_);
v___x_477_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_475_);
v___x_478_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_475_);
v_target_479_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_479_, 0, v___x_476_);
lean_ctor_set(v_target_479_, 1, v___x_477_);
lean_ctor_set(v_target_479_, 2, v___x_478_);
v___x_480_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1_spec__2___redArg(v_target_479_, v_m_471_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___redArg___boxed(lean_object* v_m_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___redArg(v_m_481_);
lean_dec_ref(v_m_481_);
return v_res_482_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__3(void){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_486_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__2));
v___x_487_ = lean_unsigned_to_nat(48u);
v___x_488_ = lean_unsigned_to_nat(76u);
v___x_489_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__1));
v___x_490_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__0));
v___x_491_ = l_mkPanicMessageWithDecl(v___x_490_, v___x_489_, v___x_488_, v___x_487_, v___x_486_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go(lean_object* v_fvarId_492_, lean_object* v_c_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_){
_start:
{
lean_object* v___y_502_; lean_object* v___y_503_; 
switch(lean_obj_tag(v_c_493_))
{
case 0:
{
lean_object* v_decl_506_; lean_object* v_k_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_520_; 
v_decl_506_ = lean_ctor_get(v_c_493_, 0);
v_k_507_ = lean_ctor_get(v_c_493_, 1);
v_isSharedCheck_520_ = !lean_is_exclusive(v_c_493_);
if (v_isSharedCheck_520_ == 0)
{
v___x_509_ = v_c_493_;
v_isShared_510_ = v_isSharedCheck_520_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_k_507_);
lean_inc(v_decl_506_);
lean_dec(v_c_493_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_520_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v_targetSet_511_; uint8_t v___x_512_; uint8_t v___x_513_; 
v_targetSet_511_ = lean_ctor_get(v_a_494_, 0);
v___x_512_ = 1;
v___x_513_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn(v___x_512_, v_decl_506_, v_targetSet_511_);
lean_dec_ref(v_decl_506_);
if (v___x_513_ == 0)
{
lean_del_object(v___x_509_);
v_c_493_ = v_k_507_;
goto _start;
}
else
{
lean_object* v___x_515_; lean_object* v___x_517_; 
lean_dec_ref(v_k_507_);
v___x_515_ = lean_box(v___x_513_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 1, v_a_495_);
lean_ctor_set(v___x_509_, 0, v___x_515_);
v___x_517_ = v___x_509_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_515_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v_a_495_);
v___x_517_ = v_reuseFailAlloc_519_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
lean_object* v___x_518_; 
v___x_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
return v___x_518_;
}
}
}
}
case 2:
{
lean_object* v_decl_521_; lean_object* v_k_522_; lean_object* v_fvarId_523_; lean_object* v_value_524_; lean_object* v___x_525_; 
v_decl_521_ = lean_ctor_get(v_c_493_, 0);
lean_inc_ref(v_decl_521_);
v_k_522_ = lean_ctor_get(v_c_493_, 1);
lean_inc_ref(v_k_522_);
lean_dec_ref_known(v_c_493_, 2);
v_fvarId_523_ = lean_ctor_get(v_decl_521_, 0);
lean_inc(v_fvarId_523_);
v_value_524_ = lean_ctor_get(v_decl_521_, 4);
lean_inc_ref(v_value_524_);
lean_dec_ref(v_decl_521_);
v___x_525_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go(v_fvarId_492_, v_value_524_, v_a_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; lean_object* v_fst_527_; uint8_t v___x_528_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_a_526_);
v_fst_527_ = lean_ctor_get(v_a_526_, 0);
v___x_528_ = lean_unbox(v_fst_527_);
if (v___x_528_ == 0)
{
lean_object* v_snd_529_; lean_object* v___x_530_; lean_object* v___y_532_; lean_object* v_i_533_; lean_object* v___y_540_; lean_object* v___y_552_; lean_object* v_i_553_; lean_object* v___x_571_; 
lean_dec_ref_known(v___x_525_, 1);
v_snd_529_ = lean_ctor_get(v_a_526_, 1);
lean_inc(v_snd_529_);
lean_dec(v_a_526_);
v___x_530_ = lean_box(0);
v___x_571_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0___redArg(v_snd_529_, v_fvarId_523_);
switch(lean_obj_tag(v___x_571_))
{
case 0:
{
lean_dec_ref_known(v___x_571_, 3);
lean_dec(v_fvarId_523_);
v_c_493_ = v_k_522_;
v_a_495_ = v_snd_529_;
goto _start;
}
case 1:
{
lean_object* v_index_573_; lean_object* v_size_574_; lean_object* v_keyArray_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; uint8_t v___x_579_; 
v_index_573_ = lean_ctor_get(v___x_571_, 0);
lean_inc(v_index_573_);
lean_dec_ref_known(v___x_571_, 1);
v_size_574_ = lean_ctor_get(v_snd_529_, 0);
v_keyArray_575_ = lean_ctor_get(v_snd_529_, 1);
v___x_576_ = lean_unsigned_to_nat(1u);
v___x_577_ = lean_nat_add(v_size_574_, v___x_576_);
v___x_578_ = lean_array_get_size(v_keyArray_575_);
v___x_579_ = lean_nat_dec_lt(v___x_577_, v___x_578_);
if (v___x_579_ == 0)
{
lean_dec(v___x_577_);
lean_dec(v_index_573_);
goto v___jp_559_;
}
else
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; uint8_t v___x_584_; 
v___x_580_ = lean_unsigned_to_nat(4u);
v___x_581_ = lean_nat_mul(v___x_577_, v___x_580_);
v___x_582_ = lean_unsigned_to_nat(3u);
v___x_583_ = lean_nat_mul(v___x_578_, v___x_582_);
v___x_584_ = lean_nat_dec_le(v___x_581_, v___x_583_);
lean_dec(v___x_583_);
lean_dec(v___x_581_);
if (v___x_584_ == 0)
{
lean_dec(v___x_577_);
lean_dec(v_index_573_);
goto v___jp_559_;
}
else
{
lean_object* v___x_585_; 
v___x_585_ = l_Std_DHashMap_Raw_setEntry___redArg(v_snd_529_, v___x_577_, v_index_573_, v_fvarId_523_, v___x_530_);
lean_dec(v_index_573_);
v_c_493_ = v_k_522_;
v_a_495_ = v___x_585_;
goto _start;
}
}
}
default: 
{
lean_object* v_size_587_; lean_object* v_keyArray_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; uint8_t v___x_592_; 
v_size_587_ = lean_ctor_get(v_snd_529_, 0);
v_keyArray_588_ = lean_ctor_get(v_snd_529_, 1);
v___x_589_ = lean_unsigned_to_nat(1u);
v___x_590_ = lean_nat_add(v_size_587_, v___x_589_);
v___x_591_ = lean_array_get_size(v_keyArray_588_);
v___x_592_ = lean_nat_dec_lt(v___x_590_, v___x_591_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; 
lean_dec(v___x_590_);
v___x_593_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___redArg(v_snd_529_);
lean_dec(v_snd_529_);
v___y_540_ = v___x_593_;
goto v___jp_539_;
}
else
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; uint8_t v___x_598_; 
v___x_594_ = lean_unsigned_to_nat(4u);
v___x_595_ = lean_nat_mul(v___x_590_, v___x_594_);
lean_dec(v___x_590_);
v___x_596_ = lean_unsigned_to_nat(3u);
v___x_597_ = lean_nat_mul(v___x_591_, v___x_596_);
v___x_598_ = lean_nat_dec_le(v___x_595_, v___x_597_);
lean_dec(v___x_597_);
lean_dec(v___x_595_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; 
v___x_599_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___redArg(v_snd_529_);
lean_dec(v_snd_529_);
v___y_540_ = v___x_599_;
goto v___jp_539_;
}
else
{
v___y_540_ = v_snd_529_;
goto v___jp_539_;
}
}
}
}
v___jp_531_:
{
lean_object* v_size_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v_size_534_ = lean_ctor_get(v___y_532_, 0);
v___x_535_ = lean_unsigned_to_nat(1u);
v___x_536_ = lean_nat_add(v_size_534_, v___x_535_);
v___x_537_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_532_, v___x_536_, v_i_533_, v_fvarId_523_, v___x_530_);
lean_dec(v_i_533_);
v_c_493_ = v_k_522_;
v_a_495_ = v___x_537_;
goto _start;
}
v___jp_539_:
{
lean_object* v___x_541_; 
v___x_541_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0___redArg(v___y_540_, v_fvarId_523_);
switch(lean_obj_tag(v___x_541_))
{
case 0:
{
lean_object* v_index_542_; lean_object* v_size_543_; lean_object* v___x_544_; 
v_index_542_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_index_542_);
lean_dec_ref_known(v___x_541_, 3);
v_size_543_ = lean_ctor_get(v___y_540_, 0);
lean_inc(v_size_543_);
v___x_544_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_540_, v_size_543_, v_index_542_, v_fvarId_523_, v___x_530_);
lean_dec(v_index_542_);
v_c_493_ = v_k_522_;
v_a_495_ = v___x_544_;
goto _start;
}
case 1:
{
lean_object* v_index_546_; 
v_index_546_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_index_546_);
lean_dec_ref_known(v___x_541_, 1);
v___y_532_ = v___y_540_;
v_i_533_ = v_index_546_;
goto v___jp_531_;
}
default: 
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = lean_unsigned_to_nat(0u);
v___x_548_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_540_, v___x_547_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_index_549_; 
v_index_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_index_549_);
lean_dec_ref_known(v___x_548_, 1);
v___y_532_ = v___y_540_;
v_i_533_ = v_index_549_;
goto v___jp_531_;
}
else
{
lean_dec(v_fvarId_523_);
v_c_493_ = v_k_522_;
v_a_495_ = v___y_540_;
goto _start;
}
}
}
}
v___jp_551_:
{
lean_object* v_size_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v_size_554_ = lean_ctor_get(v___y_552_, 0);
v___x_555_ = lean_unsigned_to_nat(1u);
v___x_556_ = lean_nat_add(v_size_554_, v___x_555_);
v___x_557_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_552_, v___x_556_, v_i_553_, v_fvarId_523_, v___x_530_);
lean_dec(v_i_553_);
v_c_493_ = v_k_522_;
v_a_495_ = v___x_557_;
goto _start;
}
v___jp_559_:
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___redArg(v_snd_529_);
lean_dec(v_snd_529_);
v___x_561_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0___redArg(v___x_560_, v_fvarId_523_);
switch(lean_obj_tag(v___x_561_))
{
case 0:
{
lean_object* v_index_562_; lean_object* v_size_563_; lean_object* v___x_564_; 
v_index_562_ = lean_ctor_get(v___x_561_, 0);
lean_inc(v_index_562_);
lean_dec_ref_known(v___x_561_, 3);
v_size_563_ = lean_ctor_get(v___x_560_, 0);
lean_inc(v_size_563_);
v___x_564_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_560_, v_size_563_, v_index_562_, v_fvarId_523_, v___x_530_);
lean_dec(v_index_562_);
v_c_493_ = v_k_522_;
v_a_495_ = v___x_564_;
goto _start;
}
case 1:
{
lean_object* v_index_566_; 
v_index_566_ = lean_ctor_get(v___x_561_, 0);
lean_inc(v_index_566_);
lean_dec_ref_known(v___x_561_, 1);
v___y_552_ = v___x_560_;
v_i_553_ = v_index_566_;
goto v___jp_551_;
}
default: 
{
lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_567_ = lean_unsigned_to_nat(0u);
v___x_568_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_560_, v___x_567_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_index_569_; 
v_index_569_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_index_569_);
lean_dec_ref_known(v___x_568_, 1);
v___y_552_ = v___x_560_;
v_i_553_ = v_index_569_;
goto v___jp_551_;
}
else
{
lean_dec(v_fvarId_523_);
v_c_493_ = v_k_522_;
v_a_495_ = v___x_560_;
goto _start;
}
}
}
}
}
else
{
lean_dec(v_a_526_);
lean_dec(v_fvarId_523_);
lean_dec_ref(v_k_522_);
return v___x_525_;
}
}
else
{
lean_dec(v_fvarId_523_);
lean_dec_ref(v_k_522_);
return v___x_525_;
}
}
case 3:
{
lean_object* v_fvarId_600_; lean_object* v_args_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_706_; 
v_fvarId_600_ = lean_ctor_get(v_c_493_, 0);
v_args_601_ = lean_ctor_get(v_c_493_, 1);
v_isSharedCheck_706_ = !lean_is_exclusive(v_c_493_);
if (v_isSharedCheck_706_ == 0)
{
v___x_603_ = v_c_493_;
v_isShared_604_ = v_isSharedCheck_706_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_args_601_);
lean_inc(v_fvarId_600_);
lean_dec(v_c_493_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_706_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v_i_609_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v_i_630_; lean_object* v___y_636_; lean_object* v___y_637_; uint8_t v___y_648_; lean_object* v___x_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
v___x_697_ = lean_unsigned_to_nat(0u);
v___x_698_ = lean_array_get_size(v_args_601_);
v___x_699_ = lean_nat_dec_lt(v___x_697_, v___x_698_);
if (v___x_699_ == 0)
{
lean_dec_ref(v_args_601_);
v___y_648_ = v___x_699_;
goto v___jp_647_;
}
else
{
if (v___x_699_ == 0)
{
lean_dec_ref(v_args_601_);
v___y_648_ = v___x_699_;
goto v___jp_647_;
}
else
{
size_t v___x_700_; size_t v___x_701_; uint8_t v___x_702_; 
v___x_700_ = ((size_t)0ULL);
v___x_701_ = lean_usize_of_nat(v___x_698_);
v___x_702_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__4(v_a_494_, v_args_601_, v___x_700_, v___x_701_);
lean_dec_ref(v_args_601_);
if (v___x_702_ == 0)
{
v___y_648_ = v___x_702_;
goto v___jp_647_;
}
else
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
lean_del_object(v___x_603_);
lean_dec(v_fvarId_600_);
v___x_703_ = lean_box(v___x_702_);
v___x_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
lean_ctor_set(v___x_704_, 1, v_a_495_);
v___x_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
return v___x_705_;
}
}
}
v___jp_605_:
{
lean_object* v_size_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v_size_610_ = lean_ctor_get(v___y_606_, 0);
v___x_611_ = lean_unsigned_to_nat(1u);
v___x_612_ = lean_nat_add(v_size_610_, v___x_611_);
v___x_613_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_606_, v___x_612_, v_i_609_, v_fvarId_600_, v___y_608_);
lean_dec(v_i_609_);
v___y_502_ = v___y_607_;
v___y_503_ = v___x_613_;
goto v___jp_501_;
}
v___jp_614_:
{
lean_object* v___x_618_; 
v___x_618_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0___redArg(v___y_617_, v_fvarId_600_);
switch(lean_obj_tag(v___x_618_))
{
case 0:
{
lean_object* v_index_619_; lean_object* v_size_620_; lean_object* v___x_621_; 
v_index_619_ = lean_ctor_get(v___x_618_, 0);
lean_inc(v_index_619_);
lean_dec_ref_known(v___x_618_, 3);
v_size_620_ = lean_ctor_get(v___y_617_, 0);
lean_inc(v_size_620_);
v___x_621_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_617_, v_size_620_, v_index_619_, v_fvarId_600_, v___y_616_);
lean_dec(v_index_619_);
v___y_502_ = v___y_615_;
v___y_503_ = v___x_621_;
goto v___jp_501_;
}
case 1:
{
lean_object* v_index_622_; 
v_index_622_ = lean_ctor_get(v___x_618_, 0);
lean_inc(v_index_622_);
lean_dec_ref_known(v___x_618_, 1);
v___y_606_ = v___y_617_;
v___y_607_ = v___y_615_;
v___y_608_ = v___y_616_;
v_i_609_ = v_index_622_;
goto v___jp_605_;
}
default: 
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = lean_unsigned_to_nat(0u);
v___x_624_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_617_, v___x_623_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_index_625_; 
v_index_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_index_625_);
lean_dec_ref_known(v___x_624_, 1);
v___y_606_ = v___y_617_;
v___y_607_ = v___y_615_;
v___y_608_ = v___y_616_;
v_i_609_ = v_index_625_;
goto v___jp_605_;
}
else
{
lean_dec(v_fvarId_600_);
v___y_502_ = v___y_615_;
v___y_503_ = v___y_617_;
goto v___jp_501_;
}
}
}
}
v___jp_626_:
{
lean_object* v_size_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v_size_631_ = lean_ctor_get(v___y_627_, 0);
v___x_632_ = lean_unsigned_to_nat(1u);
v___x_633_ = lean_nat_add(v_size_631_, v___x_632_);
v___x_634_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_627_, v___x_633_, v_i_630_, v_fvarId_600_, v___y_629_);
lean_dec(v_i_630_);
v___y_502_ = v___y_628_;
v___y_503_ = v___x_634_;
goto v___jp_501_;
}
v___jp_635_:
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___redArg(v_a_495_);
lean_dec_ref(v_a_495_);
v___x_639_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0___redArg(v___x_638_, v_fvarId_600_);
switch(lean_obj_tag(v___x_639_))
{
case 0:
{
lean_object* v_index_640_; lean_object* v_size_641_; lean_object* v___x_642_; 
v_index_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_index_640_);
lean_dec_ref_known(v___x_639_, 3);
v_size_641_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_size_641_);
v___x_642_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_638_, v_size_641_, v_index_640_, v_fvarId_600_, v___y_637_);
lean_dec(v_index_640_);
v___y_502_ = v___y_636_;
v___y_503_ = v___x_642_;
goto v___jp_501_;
}
case 1:
{
lean_object* v_index_643_; 
v_index_643_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_index_643_);
lean_dec_ref_known(v___x_639_, 1);
v___y_627_ = v___x_638_;
v___y_628_ = v___y_636_;
v___y_629_ = v___y_637_;
v_i_630_ = v_index_643_;
goto v___jp_626_;
}
default: 
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = lean_unsigned_to_nat(0u);
v___x_645_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_638_, v___x_644_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v_index_646_; 
v_index_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_index_646_);
lean_dec_ref_known(v___x_645_, 1);
v___y_627_ = v___x_638_;
v___y_628_ = v___y_636_;
v___y_629_ = v___y_637_;
v_i_630_ = v_index_646_;
goto v___jp_626_;
}
else
{
lean_dec(v_fvarId_600_);
v___y_502_ = v___y_636_;
v___y_503_ = v___x_638_;
goto v___jp_501_;
}
}
}
}
v___jp_647_:
{
uint8_t v___x_649_; 
v___x_649_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___redArg(v_a_495_, v_fvarId_600_);
if (v___x_649_ == 0)
{
uint8_t v___x_650_; lean_object* v___x_651_; 
lean_del_object(v___x_603_);
v___x_650_ = 1;
v___x_651_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_650_, v_fvarId_600_, v_a_497_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_a_652_);
lean_dec_ref_known(v___x_651_, 1);
if (lean_obj_tag(v_a_652_) == 1)
{
lean_object* v_val_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v_val_653_ = lean_ctor_get(v_a_652_, 0);
lean_inc(v_val_653_);
lean_dec_ref_known(v_a_652_, 1);
v___x_654_ = lean_box(0);
v___x_655_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0___redArg(v_a_495_, v_fvarId_600_);
switch(lean_obj_tag(v___x_655_))
{
case 0:
{
lean_dec_ref_known(v___x_655_, 3);
lean_dec(v_fvarId_600_);
v___y_502_ = v_val_653_;
v___y_503_ = v_a_495_;
goto v___jp_501_;
}
case 1:
{
lean_object* v_index_656_; lean_object* v_size_657_; lean_object* v_keyArray_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; uint8_t v___x_662_; 
v_index_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_index_656_);
lean_dec_ref_known(v___x_655_, 1);
v_size_657_ = lean_ctor_get(v_a_495_, 0);
v_keyArray_658_ = lean_ctor_get(v_a_495_, 1);
v___x_659_ = lean_unsigned_to_nat(1u);
v___x_660_ = lean_nat_add(v_size_657_, v___x_659_);
v___x_661_ = lean_array_get_size(v_keyArray_658_);
v___x_662_ = lean_nat_dec_lt(v___x_660_, v___x_661_);
if (v___x_662_ == 0)
{
lean_dec(v___x_660_);
lean_dec(v_index_656_);
v___y_636_ = v_val_653_;
v___y_637_ = v___x_654_;
goto v___jp_635_;
}
else
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_663_ = lean_unsigned_to_nat(4u);
v___x_664_ = lean_nat_mul(v___x_660_, v___x_663_);
v___x_665_ = lean_unsigned_to_nat(3u);
v___x_666_ = lean_nat_mul(v___x_661_, v___x_665_);
v___x_667_ = lean_nat_dec_le(v___x_664_, v___x_666_);
lean_dec(v___x_666_);
lean_dec(v___x_664_);
if (v___x_667_ == 0)
{
lean_dec(v___x_660_);
lean_dec(v_index_656_);
v___y_636_ = v_val_653_;
v___y_637_ = v___x_654_;
goto v___jp_635_;
}
else
{
lean_object* v___x_668_; 
v___x_668_ = l_Std_DHashMap_Raw_setEntry___redArg(v_a_495_, v___x_660_, v_index_656_, v_fvarId_600_, v___x_654_);
lean_dec(v_index_656_);
v___y_502_ = v_val_653_;
v___y_503_ = v___x_668_;
goto v___jp_501_;
}
}
}
default: 
{
lean_object* v_size_669_; lean_object* v_keyArray_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
v_size_669_ = lean_ctor_get(v_a_495_, 0);
v_keyArray_670_ = lean_ctor_get(v_a_495_, 1);
v___x_671_ = lean_unsigned_to_nat(1u);
v___x_672_ = lean_nat_add(v_size_669_, v___x_671_);
v___x_673_ = lean_array_get_size(v_keyArray_670_);
v___x_674_ = lean_nat_dec_lt(v___x_672_, v___x_673_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; 
lean_dec(v___x_672_);
v___x_675_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___redArg(v_a_495_);
lean_dec_ref(v_a_495_);
v___y_615_ = v_val_653_;
v___y_616_ = v___x_654_;
v___y_617_ = v___x_675_;
goto v___jp_614_;
}
else
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; uint8_t v___x_680_; 
v___x_676_ = lean_unsigned_to_nat(4u);
v___x_677_ = lean_nat_mul(v___x_672_, v___x_676_);
lean_dec(v___x_672_);
v___x_678_ = lean_unsigned_to_nat(3u);
v___x_679_ = lean_nat_mul(v___x_673_, v___x_678_);
v___x_680_ = lean_nat_dec_le(v___x_677_, v___x_679_);
lean_dec(v___x_679_);
lean_dec(v___x_677_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; 
v___x_681_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___redArg(v_a_495_);
lean_dec_ref(v_a_495_);
v___y_615_ = v_val_653_;
v___y_616_ = v___x_654_;
v___y_617_ = v___x_681_;
goto v___jp_614_;
}
else
{
v___y_615_ = v_val_653_;
v___y_616_ = v___x_654_;
v___y_617_ = v_a_495_;
goto v___jp_614_;
}
}
}
}
}
else
{
lean_object* v___x_682_; lean_object* v___x_683_; 
lean_dec(v_a_652_);
lean_dec(v_fvarId_600_);
v___x_682_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__3, &l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__3);
v___x_683_ = l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3(v___x_682_, v_a_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_);
return v___x_683_;
}
}
else
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_691_; 
lean_dec(v_fvarId_600_);
lean_dec_ref(v_a_495_);
v_a_684_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_691_ == 0)
{
v___x_686_ = v___x_651_;
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_651_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_689_; 
if (v_isShared_687_ == 0)
{
v___x_689_ = v___x_686_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_a_684_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
}
else
{
lean_object* v___x_692_; lean_object* v___x_694_; 
lean_dec(v_fvarId_600_);
v___x_692_ = lean_box(v___y_648_);
if (v_isShared_604_ == 0)
{
lean_ctor_set_tag(v___x_603_, 0);
lean_ctor_set(v___x_603_, 1, v_a_495_);
lean_ctor_set(v___x_603_, 0, v___x_692_);
v___x_694_ = v___x_603_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v___x_692_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v_a_495_);
v___x_694_ = v_reuseFailAlloc_696_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
lean_object* v___x_695_; 
v___x_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
return v___x_695_;
}
}
}
}
}
case 4:
{
lean_object* v_cases_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_735_; 
v_cases_707_ = lean_ctor_get(v_c_493_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v_c_493_);
if (v_isSharedCheck_735_ == 0)
{
v___x_709_ = v_c_493_;
v_isShared_710_ = v_isSharedCheck_735_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_cases_707_);
lean_dec(v_c_493_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_735_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v_discr_711_; lean_object* v_alts_712_; uint8_t v___x_713_; 
v_discr_711_ = lean_ctor_get(v_cases_707_, 2);
lean_inc(v_discr_711_);
v_alts_712_ = lean_ctor_get(v_cases_707_, 3);
lean_inc_ref(v_alts_712_);
lean_dec_ref(v_cases_707_);
v___x_713_ = l_Lean_instBEqFVarId_beq(v_discr_711_, v_fvarId_492_);
lean_dec(v_discr_711_);
if (v___x_713_ == 0)
{
lean_object* v___x_714_; lean_object* v___x_715_; uint8_t v___x_716_; 
v___x_714_ = lean_unsigned_to_nat(0u);
v___x_715_ = lean_array_get_size(v_alts_712_);
v___x_716_ = lean_nat_dec_lt(v___x_714_, v___x_715_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_720_; 
lean_dec_ref(v_alts_712_);
v___x_717_ = lean_box(v___x_713_);
v___x_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
lean_ctor_set(v___x_718_, 1, v_a_495_);
if (v_isShared_710_ == 0)
{
lean_ctor_set_tag(v___x_709_, 0);
lean_ctor_set(v___x_709_, 0, v___x_718_);
v___x_720_ = v___x_709_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_718_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
else
{
if (v___x_716_ == 0)
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_725_; 
lean_dec_ref(v_alts_712_);
v___x_722_ = lean_box(v___x_713_);
v___x_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
lean_ctor_set(v___x_723_, 1, v_a_495_);
if (v_isShared_710_ == 0)
{
lean_ctor_set_tag(v___x_709_, 0);
lean_ctor_set(v___x_709_, 0, v___x_723_);
v___x_725_ = v___x_709_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_723_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
else
{
size_t v___x_727_; size_t v___x_728_; lean_object* v___x_729_; 
lean_del_object(v___x_709_);
v___x_727_ = ((size_t)0ULL);
v___x_728_ = lean_usize_of_nat(v___x_715_);
v___x_729_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__5(v_fvarId_492_, v_alts_712_, v___x_727_, v___x_728_, v_a_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_);
lean_dec_ref(v_alts_712_);
return v___x_729_;
}
}
}
else
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_733_; 
lean_dec_ref(v_alts_712_);
v___x_730_ = lean_box(v___x_713_);
v___x_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
lean_ctor_set(v___x_731_, 1, v_a_495_);
if (v_isShared_710_ == 0)
{
lean_ctor_set_tag(v___x_709_, 0);
lean_ctor_set(v___x_709_, 0, v___x_731_);
v___x_733_ = v___x_709_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_731_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_746_; 
v_fvarId_736_ = lean_ctor_get(v_c_493_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v_c_493_);
if (v_isSharedCheck_746_ == 0)
{
v___x_738_ = v_c_493_;
v_isShared_739_ = v_isSharedCheck_746_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_fvarId_736_);
lean_dec(v_c_493_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_746_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
uint8_t v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_744_; 
v___x_740_ = l_Lean_instBEqFVarId_beq(v_fvarId_736_, v_fvarId_492_);
lean_dec(v_fvarId_736_);
v___x_741_ = lean_box(v___x_740_);
v___x_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
lean_ctor_set(v___x_742_, 1, v_a_495_);
if (v_isShared_739_ == 0)
{
lean_ctor_set_tag(v___x_738_, 0);
lean_ctor_set(v___x_738_, 0, v___x_742_);
v___x_744_ = v___x_738_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_742_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
case 6:
{
lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_756_; 
v_isSharedCheck_756_ = !lean_is_exclusive(v_c_493_);
if (v_isSharedCheck_756_ == 0)
{
lean_object* v_unused_757_; 
v_unused_757_ = lean_ctor_get(v_c_493_, 0);
lean_dec(v_unused_757_);
v___x_748_ = v_c_493_;
v_isShared_749_ = v_isSharedCheck_756_;
goto v_resetjp_747_;
}
else
{
lean_dec(v_c_493_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_756_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
uint8_t v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_754_; 
v___x_750_ = 0;
v___x_751_ = lean_box(v___x_750_);
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_751_);
lean_ctor_set(v___x_752_, 1, v_a_495_);
if (v_isShared_749_ == 0)
{
lean_ctor_set_tag(v___x_748_, 0);
lean_ctor_set(v___x_748_, 0, v___x_752_);
v___x_754_ = v___x_748_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_752_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
case 7:
{
lean_object* v_fvarId_758_; lean_object* v_y_759_; lean_object* v_k_760_; uint8_t v___x_761_; 
v_fvarId_758_ = lean_ctor_get(v_c_493_, 0);
lean_inc(v_fvarId_758_);
v_y_759_ = lean_ctor_get(v_c_493_, 2);
lean_inc(v_y_759_);
v_k_760_ = lean_ctor_get(v_c_493_, 3);
lean_inc_ref(v_k_760_);
lean_dec_ref_known(v_c_493_, 4);
v___x_761_ = l_Lean_instBEqFVarId_beq(v_fvarId_758_, v_fvarId_492_);
lean_dec(v_fvarId_758_);
if (v___x_761_ == 0)
{
lean_object* v_targetSet_762_; uint8_t v___x_763_; uint8_t v___x_764_; 
v_targetSet_762_ = lean_ctor_get(v_a_494_, 0);
v___x_763_ = 1;
v___x_764_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn(v___x_763_, v_y_759_, v_targetSet_762_);
lean_dec(v_y_759_);
if (v___x_764_ == 0)
{
v_c_493_ = v_k_760_;
goto _start;
}
else
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
lean_dec_ref(v_k_760_);
v___x_766_ = lean_box(v___x_764_);
v___x_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
lean_ctor_set(v___x_767_, 1, v_a_495_);
v___x_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
return v___x_768_;
}
}
else
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
lean_dec_ref(v_k_760_);
lean_dec(v_y_759_);
v___x_769_ = lean_box(v___x_761_);
v___x_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
lean_ctor_set(v___x_770_, 1, v_a_495_);
v___x_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
return v___x_771_;
}
}
case 8:
{
lean_object* v_fvarId_772_; lean_object* v_y_773_; lean_object* v_k_774_; uint8_t v___x_775_; 
v_fvarId_772_ = lean_ctor_get(v_c_493_, 0);
lean_inc(v_fvarId_772_);
v_y_773_ = lean_ctor_get(v_c_493_, 2);
lean_inc(v_y_773_);
v_k_774_ = lean_ctor_get(v_c_493_, 3);
lean_inc_ref(v_k_774_);
lean_dec_ref_known(v_c_493_, 4);
v___x_775_ = l_Lean_instBEqFVarId_beq(v_fvarId_772_, v_fvarId_492_);
lean_dec(v_fvarId_772_);
if (v___x_775_ == 0)
{
uint8_t v___x_776_; 
v___x_776_ = l_Lean_instBEqFVarId_beq(v_y_773_, v_fvarId_492_);
lean_dec(v_y_773_);
if (v___x_776_ == 0)
{
v_c_493_ = v_k_774_;
goto _start;
}
else
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
lean_dec_ref(v_k_774_);
v___x_778_ = lean_box(v___x_776_);
v___x_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_779_, 0, v___x_778_);
lean_ctor_set(v___x_779_, 1, v_a_495_);
v___x_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
return v___x_780_;
}
}
else
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
lean_dec_ref(v_k_774_);
lean_dec(v_y_773_);
v___x_781_ = lean_box(v___x_775_);
v___x_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
lean_ctor_set(v___x_782_, 1, v_a_495_);
v___x_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
return v___x_783_;
}
}
case 9:
{
lean_object* v_fvarId_784_; lean_object* v_y_785_; lean_object* v_k_786_; uint8_t v___x_787_; 
v_fvarId_784_ = lean_ctor_get(v_c_493_, 0);
lean_inc(v_fvarId_784_);
v_y_785_ = lean_ctor_get(v_c_493_, 3);
lean_inc(v_y_785_);
v_k_786_ = lean_ctor_get(v_c_493_, 5);
lean_inc_ref(v_k_786_);
lean_dec_ref_known(v_c_493_, 6);
v___x_787_ = l_Lean_instBEqFVarId_beq(v_fvarId_784_, v_fvarId_492_);
lean_dec(v_fvarId_784_);
if (v___x_787_ == 0)
{
uint8_t v___x_788_; 
v___x_788_ = l_Lean_instBEqFVarId_beq(v_y_785_, v_fvarId_492_);
lean_dec(v_y_785_);
if (v___x_788_ == 0)
{
v_c_493_ = v_k_786_;
goto _start;
}
else
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
lean_dec_ref(v_k_786_);
v___x_790_ = lean_box(v___x_788_);
v___x_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
lean_ctor_set(v___x_791_, 1, v_a_495_);
v___x_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
return v___x_792_;
}
}
else
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
lean_dec_ref(v_k_786_);
lean_dec(v_y_785_);
v___x_793_ = lean_box(v___x_787_);
v___x_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_794_, 0, v___x_793_);
lean_ctor_set(v___x_794_, 1, v_a_495_);
v___x_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_795_, 0, v___x_794_);
return v___x_795_;
}
}
case 12:
{
lean_object* v_fvarId_796_; lean_object* v_k_797_; uint8_t v___x_798_; 
v_fvarId_796_ = lean_ctor_get(v_c_493_, 0);
lean_inc(v_fvarId_796_);
v_k_797_ = lean_ctor_get(v_c_493_, 3);
lean_inc_ref(v_k_797_);
lean_dec_ref_known(v_c_493_, 4);
v___x_798_ = l_Lean_instBEqFVarId_beq(v_fvarId_796_, v_fvarId_492_);
lean_dec(v_fvarId_796_);
if (v___x_798_ == 0)
{
v_c_493_ = v_k_797_;
goto _start;
}
else
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
lean_dec_ref(v_k_797_);
v___x_800_ = lean_box(v___x_798_);
v___x_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
lean_ctor_set(v___x_801_, 1, v_a_495_);
v___x_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
return v___x_802_;
}
}
case 13:
{
lean_object* v_fvarId_803_; lean_object* v_k_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_815_; 
v_fvarId_803_ = lean_ctor_get(v_c_493_, 0);
v_k_804_ = lean_ctor_get(v_c_493_, 1);
v_isSharedCheck_815_ = !lean_is_exclusive(v_c_493_);
if (v_isSharedCheck_815_ == 0)
{
v___x_806_ = v_c_493_;
v_isShared_807_ = v_isSharedCheck_815_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_k_804_);
lean_inc(v_fvarId_803_);
lean_dec(v_c_493_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_815_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
uint8_t v___x_808_; 
v___x_808_ = l_Lean_instBEqFVarId_beq(v_fvarId_803_, v_fvarId_492_);
lean_dec(v_fvarId_803_);
if (v___x_808_ == 0)
{
lean_del_object(v___x_806_);
v_c_493_ = v_k_804_;
goto _start;
}
else
{
lean_object* v___x_810_; lean_object* v___x_812_; 
lean_dec_ref(v_k_804_);
v___x_810_ = lean_box(v___x_808_);
if (v_isShared_807_ == 0)
{
lean_ctor_set_tag(v___x_806_, 0);
lean_ctor_set(v___x_806_, 1, v_a_495_);
lean_ctor_set(v___x_806_, 0, v___x_810_);
v___x_812_ = v___x_806_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_810_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v_a_495_);
v___x_812_ = v_reuseFailAlloc_814_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
lean_object* v___x_813_; 
v___x_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
return v___x_813_;
}
}
}
}
default: 
{
lean_object* v_fvarId_816_; lean_object* v_k_817_; uint8_t v___x_818_; 
v_fvarId_816_ = lean_ctor_get(v_c_493_, 0);
lean_inc(v_fvarId_816_);
v_k_817_ = lean_ctor_get(v_c_493_, 2);
lean_inc_ref(v_k_817_);
lean_dec_ref(v_c_493_);
v___x_818_ = l_Lean_instBEqFVarId_beq(v_fvarId_816_, v_fvarId_492_);
lean_dec(v_fvarId_816_);
if (v___x_818_ == 0)
{
v_c_493_ = v_k_817_;
goto _start;
}
else
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
lean_dec_ref(v_k_817_);
v___x_820_ = lean_box(v___x_818_);
v___x_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
lean_ctor_set(v___x_821_, 1, v_a_495_);
v___x_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
return v___x_822_;
}
}
}
v___jp_501_:
{
lean_object* v_value_504_; 
v_value_504_ = lean_ctor_get(v___y_502_, 4);
lean_inc_ref(v_value_504_);
lean_dec_ref(v___y_502_);
v_c_493_ = v_value_504_;
v_a_495_ = v___y_503_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__5(lean_object* v_fvarId_823_, lean_object* v_as_824_, size_t v_i_825_, size_t v_stop_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
uint8_t v___x_834_; 
v___x_834_ = lean_usize_dec_eq(v_i_825_, v_stop_826_);
if (v___x_834_ == 0)
{
uint8_t v___x_835_; lean_object* v___y_837_; lean_object* v___x_863_; 
v___x_835_ = 1;
v___x_863_ = lean_array_uget_borrowed(v_as_824_, v_i_825_);
switch(lean_obj_tag(v___x_863_))
{
case 0:
{
lean_object* v_code_864_; 
v_code_864_ = lean_ctor_get(v___x_863_, 2);
lean_inc_ref(v_code_864_);
v___y_837_ = v_code_864_;
goto v___jp_836_;
}
case 1:
{
lean_object* v_code_865_; 
v_code_865_ = lean_ctor_get(v___x_863_, 1);
lean_inc_ref(v_code_865_);
v___y_837_ = v_code_865_;
goto v___jp_836_;
}
default: 
{
lean_object* v_code_866_; 
v_code_866_ = lean_ctor_get(v___x_863_, 0);
lean_inc_ref(v_code_866_);
v___y_837_ = v_code_866_;
goto v___jp_836_;
}
}
v___jp_836_:
{
lean_object* v___x_838_; 
v___x_838_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go(v_fvarId_823_, v___y_837_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_862_; 
v_a_839_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_862_ == 0)
{
v___x_841_ = v___x_838_;
v_isShared_842_ = v_isSharedCheck_862_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_838_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_862_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v_fst_843_; uint8_t v___x_844_; 
v_fst_843_ = lean_ctor_get(v_a_839_, 0);
v___x_844_ = lean_unbox(v_fst_843_);
if (v___x_844_ == 0)
{
lean_object* v_snd_845_; size_t v___x_846_; size_t v___x_847_; 
lean_del_object(v___x_841_);
v_snd_845_ = lean_ctor_get(v_a_839_, 1);
lean_inc(v_snd_845_);
lean_dec(v_a_839_);
v___x_846_ = ((size_t)1ULL);
v___x_847_ = lean_usize_add(v_i_825_, v___x_846_);
v_i_825_ = v___x_847_;
v___y_828_ = v_snd_845_;
goto _start;
}
else
{
lean_object* v_snd_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_860_; 
v_snd_849_ = lean_ctor_get(v_a_839_, 1);
v_isSharedCheck_860_ = !lean_is_exclusive(v_a_839_);
if (v_isSharedCheck_860_ == 0)
{
lean_object* v_unused_861_; 
v_unused_861_ = lean_ctor_get(v_a_839_, 0);
lean_dec(v_unused_861_);
v___x_851_ = v_a_839_;
v_isShared_852_ = v_isSharedCheck_860_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_snd_849_);
lean_dec(v_a_839_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_860_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_853_; lean_object* v___x_855_; 
v___x_853_ = lean_box(v___x_835_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 0, v___x_853_);
v___x_855_ = v___x_851_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_853_);
lean_ctor_set(v_reuseFailAlloc_859_, 1, v_snd_849_);
v___x_855_ = v_reuseFailAlloc_859_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
lean_object* v___x_857_; 
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 0, v___x_855_);
v___x_857_ = v___x_841_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_855_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
}
}
else
{
return v___x_838_;
}
}
}
else
{
uint8_t v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_867_ = 0;
v___x_868_ = lean_box(v___x_867_);
v___x_869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
lean_ctor_set(v___x_869_, 1, v___y_828_);
v___x_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
return v___x_870_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__5___boxed(lean_object* v_fvarId_871_, lean_object* v_as_872_, lean_object* v_i_873_, lean_object* v_stop_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
size_t v_i_boxed_882_; size_t v_stop_boxed_883_; lean_object* v_res_884_; 
v_i_boxed_882_ = lean_unbox_usize(v_i_873_);
lean_dec(v_i_873_);
v_stop_boxed_883_ = lean_unbox_usize(v_stop_874_);
lean_dec(v_stop_874_);
v_res_884_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__5(v_fvarId_871_, v_as_872_, v_i_boxed_882_, v_stop_boxed_883_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec_ref(v___y_875_);
lean_dec_ref(v_as_872_);
lean_dec(v_fvarId_871_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___boxed(lean_object* v_fvarId_885_, lean_object* v_c_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go(v_fvarId_885_, v_c_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
lean_dec(v_a_892_);
lean_dec_ref(v_a_891_);
lean_dec(v_a_890_);
lean_dec_ref(v_a_889_);
lean_dec_ref(v_a_887_);
lean_dec(v_fvarId_885_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0(lean_object* v_00_u03b2_895_, lean_object* v_m_896_, lean_object* v_query_897_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0___redArg(v_m_896_, v_query_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0___boxed(lean_object* v_00_u03b2_899_, lean_object* v_m_900_, lean_object* v_query_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0(v_00_u03b2_899_, v_m_900_, v_query_901_);
lean_dec(v_query_901_);
lean_dec_ref(v_m_900_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1(lean_object* v_00_u03b2_903_, lean_object* v_m_904_){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___redArg(v_m_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___boxed(lean_object* v_00_u03b2_906_, lean_object* v_m_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1(v_00_u03b2_906_, v_m_907_);
lean_dec_ref(v_m_907_);
return v_res_908_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2(lean_object* v_00_u03b2_909_, lean_object* v_m_910_, lean_object* v_a_911_){
_start:
{
uint8_t v___x_912_; 
v___x_912_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___redArg(v_m_910_, v_a_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___boxed(lean_object* v_00_u03b2_913_, lean_object* v_m_914_, lean_object* v_a_915_){
_start:
{
uint8_t v_res_916_; lean_object* v_r_917_; 
v_res_916_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2(v_00_u03b2_913_, v_m_914_, v_a_915_);
lean_dec(v_a_915_);
lean_dec_ref(v_m_914_);
v_r_917_ = lean_box(v_res_916_);
return v_r_917_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0(lean_object* v_00_u03b2_918_, lean_object* v_m_919_, lean_object* v_query_920_, lean_object* v_x_921_, lean_object* v_x_922_, lean_object* v_x_923_, lean_object* v_x_924_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0___redArg(v_m_919_, v_query_920_, v_x_921_, v_x_922_, v_x_923_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_926_, lean_object* v_m_927_, lean_object* v_query_928_, lean_object* v_x_929_, lean_object* v_x_930_, lean_object* v_x_931_, lean_object* v_x_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0(v_00_u03b2_926_, v_m_927_, v_query_928_, v_x_929_, v_x_930_, v_x_931_, v_x_932_);
lean_dec(v_query_928_);
lean_dec_ref(v_m_927_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1_spec__2(lean_object* v_00_u03b2_934_, lean_object* v_init_935_, lean_object* v_b_936_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1_spec__2___redArg(v_init_935_, v_b_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1_spec__2___boxed(lean_object* v_00_u03b2_938_, lean_object* v_init_939_, lean_object* v_b_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1_spec__2(v_00_u03b2_938_, v_init_939_, v_b_940_);
lean_dec_ref(v_b_940_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2_spec__4(lean_object* v_00_u03b2_942_, lean_object* v_m_943_, lean_object* v_query_944_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2_spec__4___redArg(v_m_943_, v_query_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2_spec__4___boxed(lean_object* v_00_u03b2_946_, lean_object* v_m_947_, lean_object* v_query_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2_spec__4(v_00_u03b2_946_, v_m_947_, v_query_948_);
lean_dec(v_query_948_);
lean_dec_ref(v_m_947_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_950_, lean_object* v_b_951_, lean_object* v_acc_952_, lean_object* v_i_953_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1_spec__2_spec__4___redArg(v_b_951_, v_acc_952_, v_i_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_955_, lean_object* v_b_956_, lean_object* v_acc_957_, lean_object* v_i_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1_spec__2_spec__4(v_00_u03b2_955_, v_b_956_, v_acc_957_, v_i_958_);
lean_dec_ref(v_b_956_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_isFVarLiveIn(lean_object* v_c_960_, lean_object* v_fvarId_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_967_ = l_Lean_instEmptyCollectionFVarIdHashSet;
lean_inc_n(v_fvarId_961_, 2);
v___x_968_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_fvarId_961_);
v___x_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
lean_ctor_set(v___x_969_, 1, v_fvarId_961_);
v___x_970_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go(v_fvarId_961_, v_c_960_, v___x_969_, v___x_967_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
lean_dec_ref_known(v___x_969_, 2);
lean_dec(v_fvarId_961_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_979_; 
v_a_971_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_979_ == 0)
{
v___x_973_ = v___x_970_;
v_isShared_974_ = v_isSharedCheck_979_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_970_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_979_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v_fst_975_; lean_object* v___x_977_; 
v_fst_975_ = lean_ctor_get(v_a_971_, 0);
lean_inc(v_fst_975_);
lean_dec(v_a_971_);
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 0, v_fst_975_);
v___x_977_ = v___x_973_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_fst_975_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
else
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
v_a_980_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_970_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_970_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_980_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_isFVarLiveIn___boxed(lean_object* v_c_988_, lean_object* v_fvarId_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_Lean_Compiler_LCNF_Code_isFVarLiveIn(v_c_988_, v_fvarId_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_);
lean_dec(v_a_993_);
lean_dec_ref(v_a_992_);
lean_dec(v_a_991_);
lean_dec_ref(v_a_990_);
return v_res_995_;
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
