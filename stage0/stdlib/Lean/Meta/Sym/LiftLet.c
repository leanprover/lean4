// Lean compiler output
// Module: Lean.Meta.Sym.LiftLet
// Imports: public import Lean.Meta.Sym.SymM import Lean.Meta.Sym.AlphaShareBuilder import Lean.Meta.Sym.ReplaceS
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
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_Expr_looseBVarRange(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_EStateM_instMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_runShareCommonM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg();
uint8_t lean_usize_dec_lt(size_t, size_t);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited___redArg();
lean_object* l_EStateM_instInhabited___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
static const lean_string_object l_Lean_Meta_Sym_LiftLet_instInhabitedDecl_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Meta_Sym_LiftLet_instInhabitedDecl_default___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_LiftLet_instInhabitedDecl_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_LiftLet_instInhabitedDecl_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_LiftLet_instInhabitedDecl_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Meta_Sym_LiftLet_instInhabitedDecl_default___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_LiftLet_instInhabitedDecl_default___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Sym_LiftLet_instInhabitedDecl_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_LiftLet_instInhabitedDecl_default___closed__2;
static lean_once_cell_t l_Lean_Meta_Sym_LiftLet_instInhabitedDecl_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_LiftLet_instInhabitedDecl_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_LiftLet_instInhabitedDecl_default;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_instInhabitedDecl;
LEAN_EXPORT uint64_t l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hashPtrEnv_unsafe__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hashPtrEnv_unsafe__1___boxed(lean_object*);
LEAN_EXPORT uint64_t l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hashPtrEnv(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hashPtrEnv___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_isSameEnv_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_isSameEnv_unsafe__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_isSameEnv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_isSameEnv___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_instHashableEnvPtr___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_instHashableEnvPtr___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_instHashableEnvPtr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_instHashableEnvPtr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_instHashableEnvPtr___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_instHashableEnvPtr___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_instHashableEnvPtr = (const lean_object*)&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_instHashableEnvPtr___closed__0_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_instBEqEnvPtr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_instBEqEnvPtr___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_instBEqEnvPtr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_instBEqEnvPtr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_instBEqEnvPtr___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_instBEqEnvPtr___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_instBEqEnvPtr = (const lean_object*)&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_instBEqEnvPtr___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6_spec__7_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6_spec__7_spec__8(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___redArg___lam__0, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___redArg___lam__1, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___redArg___lam__2, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_map, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_pure, .m_arity = 5, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__4_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_seqRight, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__5 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__5_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_bind, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__6 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "_private.Lean.Meta.Sym.ReplaceS.0.Lean.Meta.Sym.visit"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Meta.Sym.ReplaceS"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Meta.Sym.AlphaShareBuilder"};
static const lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Meta.Sym.Internal.liftBuilderM"};
static const lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10_spec__11_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`Sym.liftLets` internal error, input term is not closed"};
static const lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__3;
static const lean_string_object l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "_private.Lean.Meta.Sym.LiftLet.0.Lean.Meta.Sym.LiftLet.go.visit"};
static const lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Meta.Sym.LiftLet"};
static const lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10_spec__11_spec__12(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "_private.Lean.Meta.Sym.LiftLet.0.Lean.Meta.Sym.LiftLet.mkLets"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "assertion violation: p < i\n          "};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7_spec__12(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1_spec__5_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1_spec__5_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_liftLets___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_liftLets___closed__0;
static lean_once_cell_t l_Lean_Meta_Sym_liftLets___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_liftLets___closed__1;
static const lean_array_object l_Lean_Meta_Sym_liftLets___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Sym_liftLets___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_liftLets___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Sym_liftLets___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_liftLets___closed__3;
static const lean_string_object l_Lean_Meta_Sym_liftLets___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "`Sym.liftLets` internal error, input term has loose bound variables"};
static const lean_object* l_Lean_Meta_Sym_liftLets___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_liftLets___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Sym_liftLets___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_liftLets___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Sym_LiftLet_instInhabitedDecl_default___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_box(0);
v___x_5_ = ((lean_object*)(l_Lean_Meta_Sym_LiftLet_instInhabitedDecl_default___closed__1));
v___x_6_ = l_Lean_Expr_const___override(v___x_5_, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_LiftLet_instInhabitedDecl_default___closed__3(void){
_start:
{
uint8_t v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_7_ = 0;
v___x_8_ = lean_box(0);
v___x_9_ = lean_obj_once(&l_Lean_Meta_Sym_LiftLet_instInhabitedDecl_default___closed__2, &l_Lean_Meta_Sym_LiftLet_instInhabitedDecl_default___closed__2_once, _init_l_Lean_Meta_Sym_LiftLet_instInhabitedDecl_default___closed__2);
v___x_10_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_10_, 0, v___x_9_);
lean_ctor_set(v___x_10_, 1, v___x_8_);
lean_ctor_set(v___x_10_, 2, v___x_9_);
lean_ctor_set(v___x_10_, 3, v___x_9_);
lean_ctor_set_uint8(v___x_10_, sizeof(void*)*4, v___x_7_);
return v___x_10_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_LiftLet_instInhabitedDecl_default(void){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_obj_once(&l_Lean_Meta_Sym_LiftLet_instInhabitedDecl_default___closed__3, &l_Lean_Meta_Sym_LiftLet_instInhabitedDecl_default___closed__3_once, _init_l_Lean_Meta_Sym_LiftLet_instInhabitedDecl_default___closed__3);
return v___x_11_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_instInhabitedDecl(void){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = l_Lean_Meta_Sym_LiftLet_instInhabitedDecl_default;
return v___x_12_;
}
}
uint64_t l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hashPtrEnv_unsafe__1(lean_object* v_xs_13_){
_start:
{
size_t v___x_14_; size_t v___x_15_; size_t v___x_16_; uint64_t v___x_17_; 
v___x_14_ = lean_ptr_addr(v_xs_13_);
v___x_15_ = ((size_t)3ULL);
v___x_16_ = lean_usize_shift_right(v___x_14_, v___x_15_);
v___x_17_ = lean_usize_to_uint64(v___x_16_);
return v___x_17_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hashPtrEnv_unsafe__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_13_ = stack[0].m_obj;
uint64_t v_res_18_;
v_res_18_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hashPtrEnv_unsafe__1(v_xs_13_);
stack->m_num = v_res_18_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hashPtrEnv_unsafe__1___boxed(lean_object* v_xs_19_){
_start:
{
uint64_t v_res_20_; lean_object* v_r_21_; 
v_res_20_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hashPtrEnv_unsafe__1(v_xs_19_);
lean_dec_ref(v_xs_19_);
v_r_21_ = lean_box_uint64(v_res_20_);
return v_r_21_;
}
}
uint64_t l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hashPtrEnv(lean_object* v_xs_22_){
_start:
{
size_t v___x_23_; size_t v___x_24_; size_t v___x_25_; uint64_t v___x_26_; 
v___x_23_ = lean_ptr_addr(v_xs_22_);
v___x_24_ = ((size_t)3ULL);
v___x_25_ = lean_usize_shift_right(v___x_23_, v___x_24_);
v___x_26_ = lean_usize_to_uint64(v___x_25_);
return v___x_26_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hashPtrEnv_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_22_ = stack[0].m_obj;
uint64_t v_res_27_;
v_res_27_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hashPtrEnv(v_xs_22_);
stack->m_num = v_res_27_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hashPtrEnv___boxed(lean_object* v_xs_28_){
_start:
{
uint64_t v_res_29_; lean_object* v_r_30_; 
v_res_29_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hashPtrEnv(v_xs_28_);
lean_dec_ref(v_xs_28_);
v_r_30_ = lean_box_uint64(v_res_29_);
return v_r_30_;
}
}
uint8_t l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_isSameEnv_unsafe__1(lean_object* v_xs_31_, lean_object* v_ys_32_){
_start:
{
size_t v___x_33_; size_t v___x_34_; uint8_t v___x_35_; 
v___x_33_ = lean_ptr_addr(v_xs_31_);
v___x_34_ = lean_ptr_addr(v_ys_32_);
v___x_35_ = lean_usize_dec_eq(v___x_33_, v___x_34_);
return v___x_35_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_isSameEnv_unsafe__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_31_ = stack[0].m_obj;
lean_object* v_ys_32_ = stack[1].m_obj;
uint8_t v_res_36_;
v_res_36_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_isSameEnv_unsafe__1(v_xs_31_, v_ys_32_);
stack->m_num = v_res_36_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_isSameEnv_unsafe__1___boxed(lean_object* v_xs_37_, lean_object* v_ys_38_){
_start:
{
uint8_t v_res_39_; lean_object* v_r_40_; 
v_res_39_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_isSameEnv_unsafe__1(v_xs_37_, v_ys_38_);
lean_dec_ref(v_ys_38_);
lean_dec_ref(v_xs_37_);
v_r_40_ = lean_box(v_res_39_);
return v_r_40_;
}
}
uint8_t l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_isSameEnv(lean_object* v_xs_41_, lean_object* v_ys_42_){
_start:
{
size_t v___x_43_; size_t v___x_44_; uint8_t v___x_45_; 
v___x_43_ = lean_ptr_addr(v_xs_41_);
v___x_44_ = lean_ptr_addr(v_ys_42_);
v___x_45_ = lean_usize_dec_eq(v___x_43_, v___x_44_);
return v___x_45_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_isSameEnv_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_41_ = stack[0].m_obj;
lean_object* v_ys_42_ = stack[1].m_obj;
uint8_t v_res_46_;
v_res_46_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_isSameEnv(v_xs_41_, v_ys_42_);
stack->m_num = v_res_46_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_isSameEnv___boxed(lean_object* v_xs_47_, lean_object* v_ys_48_){
_start:
{
uint8_t v_res_49_; lean_object* v_r_50_; 
v_res_49_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_isSameEnv(v_xs_47_, v_ys_48_);
lean_dec_ref(v_ys_48_);
lean_dec_ref(v_xs_47_);
v_r_50_ = lean_box(v_res_49_);
return v_r_50_;
}
}
uint64_t l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_instHashableEnvPtr___lam__0(lean_object* v_k_51_){
_start:
{
size_t v___x_52_; size_t v___x_53_; size_t v___x_54_; uint64_t v___x_55_; 
v___x_52_ = lean_ptr_addr(v_k_51_);
v___x_53_ = ((size_t)3ULL);
v___x_54_ = lean_usize_shift_right(v___x_52_, v___x_53_);
v___x_55_ = lean_usize_to_uint64(v___x_54_);
return v___x_55_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_instHashableEnvPtr___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_51_ = stack[0].m_obj;
uint64_t v_res_56_;
v_res_56_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_instHashableEnvPtr___lam__0(v_k_51_);
stack->m_num = v_res_56_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_instHashableEnvPtr___lam__0___boxed(lean_object* v_k_57_){
_start:
{
uint64_t v_res_58_; lean_object* v_r_59_; 
v_res_58_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_instHashableEnvPtr___lam__0(v_k_57_);
lean_dec_ref(v_k_57_);
v_r_59_ = lean_box_uint64(v_res_58_);
return v_r_59_;
}
}
uint8_t l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_instBEqEnvPtr___lam__0(lean_object* v_k_u2081_62_, lean_object* v_k_u2082_63_){
_start:
{
size_t v___x_64_; size_t v___x_65_; uint8_t v___x_66_; 
v___x_64_ = lean_ptr_addr(v_k_u2081_62_);
v___x_65_ = lean_ptr_addr(v_k_u2082_63_);
v___x_66_ = lean_usize_dec_eq(v___x_64_, v___x_65_);
return v___x_66_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_instBEqEnvPtr___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_u2081_62_ = stack[0].m_obj;
lean_object* v_k_u2082_63_ = stack[1].m_obj;
uint8_t v_res_67_;
v_res_67_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_instBEqEnvPtr___lam__0(v_k_u2081_62_, v_k_u2082_63_);
stack->m_num = v_res_67_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_instBEqEnvPtr___lam__0___boxed(lean_object* v_k_u2081_68_, lean_object* v_k_u2082_69_){
_start:
{
uint8_t v_res_70_; lean_object* v_r_71_; 
v_res_70_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_instBEqEnvPtr___lam__0(v_k_u2081_68_, v_k_u2082_69_);
lean_dec_ref(v_k_u2082_69_);
lean_dec_ref(v_k_u2081_68_);
v_r_71_ = lean_box(v_res_70_);
return v_r_71_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_74_, lean_object* v_x_75_){
_start:
{
if (lean_obj_tag(v_x_75_) == 0)
{
return v_x_74_;
}
else
{
lean_object* v_key_76_; lean_object* v_value_77_; lean_object* v_tail_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_104_; 
v_key_76_ = lean_ctor_get(v_x_75_, 0);
v_value_77_ = lean_ctor_get(v_x_75_, 1);
v_tail_78_ = lean_ctor_get(v_x_75_, 2);
v_isSharedCheck_104_ = !lean_is_exclusive(v_x_75_);
if (v_isSharedCheck_104_ == 0)
{
v___x_80_ = v_x_75_;
v_isShared_81_ = v_isSharedCheck_104_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_tail_78_);
lean_inc(v_value_77_);
lean_inc(v_key_76_);
lean_dec(v_x_75_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_104_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_82_; size_t v___x_83_; size_t v___x_84_; size_t v___x_85_; uint64_t v___x_86_; uint64_t v___x_87_; uint64_t v___x_88_; uint64_t v_fold_89_; uint64_t v___x_90_; uint64_t v___x_91_; uint64_t v___x_92_; size_t v___x_93_; size_t v___x_94_; size_t v___x_95_; size_t v___x_96_; size_t v___x_97_; lean_object* v___x_98_; lean_object* v___x_100_; 
v___x_82_ = lean_array_get_size(v_x_74_);
v___x_83_ = lean_ptr_addr(v_key_76_);
v___x_84_ = ((size_t)3ULL);
v___x_85_ = lean_usize_shift_right(v___x_83_, v___x_84_);
v___x_86_ = lean_usize_to_uint64(v___x_85_);
v___x_87_ = 32ULL;
v___x_88_ = lean_uint64_shift_right(v___x_86_, v___x_87_);
v_fold_89_ = lean_uint64_xor(v___x_86_, v___x_88_);
v___x_90_ = 16ULL;
v___x_91_ = lean_uint64_shift_right(v_fold_89_, v___x_90_);
v___x_92_ = lean_uint64_xor(v_fold_89_, v___x_91_);
v___x_93_ = lean_uint64_to_usize(v___x_92_);
v___x_94_ = lean_usize_of_nat(v___x_82_);
v___x_95_ = ((size_t)1ULL);
v___x_96_ = lean_usize_sub(v___x_94_, v___x_95_);
v___x_97_ = lean_usize_land(v___x_93_, v___x_96_);
v___x_98_ = lean_array_uget_borrowed(v_x_74_, v___x_97_);
lean_inc(v___x_98_);
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 2, v___x_98_);
v___x_100_ = v___x_80_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_key_76_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v_value_77_);
lean_ctor_set(v_reuseFailAlloc_103_, 2, v___x_98_);
v___x_100_ = v_reuseFailAlloc_103_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
lean_object* v___x_101_; 
v___x_101_ = lean_array_uset(v_x_74_, v___x_97_, v___x_100_);
v_x_74_ = v___x_101_;
v_x_75_ = v_tail_78_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__3_spec__4___redArg(lean_object* v_i_105_, lean_object* v_source_106_, lean_object* v_target_107_){
_start:
{
lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_108_ = lean_array_get_size(v_source_106_);
v___x_109_ = lean_nat_dec_lt(v_i_105_, v___x_108_);
if (v___x_109_ == 0)
{
lean_dec_ref(v_source_106_);
lean_dec(v_i_105_);
return v_target_107_;
}
else
{
lean_object* v_es_110_; lean_object* v___x_111_; lean_object* v_source_112_; lean_object* v_target_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v_es_110_ = lean_array_fget(v_source_106_, v_i_105_);
v___x_111_ = lean_box(0);
v_source_112_ = lean_array_fset(v_source_106_, v_i_105_, v___x_111_);
v_target_113_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__3_spec__4_spec__5___redArg(v_target_107_, v_es_110_);
v___x_114_ = lean_unsigned_to_nat(1u);
v___x_115_ = lean_nat_add(v_i_105_, v___x_114_);
lean_dec(v_i_105_);
v_i_105_ = v___x_115_;
v_source_106_ = v_source_112_;
v_target_107_ = v_target_113_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__3___redArg(lean_object* v_data_117_){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v_nbuckets_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_118_ = lean_array_get_size(v_data_117_);
v___x_119_ = lean_unsigned_to_nat(2u);
v_nbuckets_120_ = lean_nat_mul(v___x_118_, v___x_119_);
v___x_121_ = lean_unsigned_to_nat(0u);
v___x_122_ = lean_box(0);
v___x_123_ = lean_mk_array(v_nbuckets_120_, v___x_122_);
v___x_124_ = lean_array_propagate_mark(v_data_117_, v___x_123_);
v___x_125_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__3_spec__4___redArg(v___x_121_, v_data_117_, v___x_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__4___redArg(lean_object* v_a_126_, lean_object* v_b_127_, lean_object* v_x_128_){
_start:
{
if (lean_obj_tag(v_x_128_) == 0)
{
lean_dec(v_b_127_);
lean_dec_ref(v_a_126_);
return v_x_128_;
}
else
{
lean_object* v_key_129_; lean_object* v_value_130_; lean_object* v_tail_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_145_; 
v_key_129_ = lean_ctor_get(v_x_128_, 0);
v_value_130_ = lean_ctor_get(v_x_128_, 1);
v_tail_131_ = lean_ctor_get(v_x_128_, 2);
v_isSharedCheck_145_ = !lean_is_exclusive(v_x_128_);
if (v_isSharedCheck_145_ == 0)
{
v___x_133_ = v_x_128_;
v_isShared_134_ = v_isSharedCheck_145_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_tail_131_);
lean_inc(v_value_130_);
lean_inc(v_key_129_);
lean_dec(v_x_128_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_145_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
size_t v___x_135_; size_t v___x_136_; uint8_t v___x_137_; 
v___x_135_ = lean_ptr_addr(v_key_129_);
v___x_136_ = lean_ptr_addr(v_a_126_);
v___x_137_ = lean_usize_dec_eq(v___x_135_, v___x_136_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; lean_object* v___x_140_; 
v___x_138_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__4___redArg(v_a_126_, v_b_127_, v_tail_131_);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 2, v___x_138_);
v___x_140_ = v___x_133_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_key_129_);
lean_ctor_set(v_reuseFailAlloc_141_, 1, v_value_130_);
lean_ctor_set(v_reuseFailAlloc_141_, 2, v___x_138_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
else
{
lean_object* v___x_143_; 
lean_dec(v_value_130_);
lean_dec(v_key_129_);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 1, v_b_127_);
lean_ctor_set(v___x_133_, 0, v_a_126_);
v___x_143_ = v___x_133_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_a_126_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v_b_127_);
lean_ctor_set(v_reuseFailAlloc_144_, 2, v_tail_131_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
}
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2___redArg(lean_object* v_a_146_, lean_object* v_x_147_){
_start:
{
if (lean_obj_tag(v_x_147_) == 0)
{
uint8_t v___x_148_; 
v___x_148_ = 0;
return v___x_148_;
}
else
{
lean_object* v_key_149_; lean_object* v_tail_150_; size_t v___x_151_; size_t v___x_152_; uint8_t v___x_153_; 
v_key_149_ = lean_ctor_get(v_x_147_, 0);
v_tail_150_ = lean_ctor_get(v_x_147_, 2);
v___x_151_ = lean_ptr_addr(v_key_149_);
v___x_152_ = lean_ptr_addr(v_a_146_);
v___x_153_ = lean_usize_dec_eq(v___x_151_, v___x_152_);
if (v___x_153_ == 0)
{
v_x_147_ = v_tail_150_;
goto _start;
}
else
{
return v___x_153_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_146_ = stack[0].m_obj;
lean_object* v_x_147_ = stack[1].m_obj;
uint8_t v_res_155_;
v_res_155_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2___redArg(v_a_146_, v_x_147_);
stack->m_num = v_res_155_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2___redArg___boxed(lean_object* v_a_156_, lean_object* v_x_157_){
_start:
{
uint8_t v_res_158_; lean_object* v_r_159_; 
v_res_158_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2___redArg(v_a_156_, v_x_157_);
lean_dec(v_x_157_);
lean_dec_ref(v_a_156_);
v_r_159_ = lean_box(v_res_158_);
return v_r_159_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1___redArg(lean_object* v_m_160_, lean_object* v_a_161_, lean_object* v_b_162_){
_start:
{
lean_object* v_size_163_; lean_object* v_buckets_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_210_; 
v_size_163_ = lean_ctor_get(v_m_160_, 0);
v_buckets_164_ = lean_ctor_get(v_m_160_, 1);
v_isSharedCheck_210_ = !lean_is_exclusive(v_m_160_);
if (v_isSharedCheck_210_ == 0)
{
v___x_166_ = v_m_160_;
v_isShared_167_ = v_isSharedCheck_210_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_buckets_164_);
lean_inc(v_size_163_);
lean_dec(v_m_160_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_210_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_168_; size_t v___x_169_; size_t v___x_170_; size_t v___x_171_; uint64_t v___x_172_; uint64_t v___x_173_; uint64_t v___x_174_; uint64_t v_fold_175_; uint64_t v___x_176_; uint64_t v___x_177_; uint64_t v___x_178_; size_t v___x_179_; size_t v___x_180_; size_t v___x_181_; size_t v___x_182_; size_t v___x_183_; lean_object* v_bkt_184_; uint8_t v___x_185_; 
v___x_168_ = lean_array_get_size(v_buckets_164_);
v___x_169_ = lean_ptr_addr(v_a_161_);
v___x_170_ = ((size_t)3ULL);
v___x_171_ = lean_usize_shift_right(v___x_169_, v___x_170_);
v___x_172_ = lean_usize_to_uint64(v___x_171_);
v___x_173_ = 32ULL;
v___x_174_ = lean_uint64_shift_right(v___x_172_, v___x_173_);
v_fold_175_ = lean_uint64_xor(v___x_172_, v___x_174_);
v___x_176_ = 16ULL;
v___x_177_ = lean_uint64_shift_right(v_fold_175_, v___x_176_);
v___x_178_ = lean_uint64_xor(v_fold_175_, v___x_177_);
v___x_179_ = lean_uint64_to_usize(v___x_178_);
v___x_180_ = lean_usize_of_nat(v___x_168_);
v___x_181_ = ((size_t)1ULL);
v___x_182_ = lean_usize_sub(v___x_180_, v___x_181_);
v___x_183_ = lean_usize_land(v___x_179_, v___x_182_);
v_bkt_184_ = lean_array_uget_borrowed(v_buckets_164_, v___x_183_);
v___x_185_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2___redArg(v_a_161_, v_bkt_184_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; lean_object* v_size_x27_187_; lean_object* v___x_188_; lean_object* v_buckets_x27_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; uint8_t v___x_195_; 
v___x_186_ = lean_unsigned_to_nat(1u);
v_size_x27_187_ = lean_nat_add(v_size_163_, v___x_186_);
lean_dec(v_size_163_);
lean_inc(v_bkt_184_);
v___x_188_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_188_, 0, v_a_161_);
lean_ctor_set(v___x_188_, 1, v_b_162_);
lean_ctor_set(v___x_188_, 2, v_bkt_184_);
v_buckets_x27_189_ = lean_array_uset(v_buckets_164_, v___x_183_, v___x_188_);
v___x_190_ = lean_unsigned_to_nat(4u);
v___x_191_ = lean_nat_mul(v_size_x27_187_, v___x_190_);
v___x_192_ = lean_unsigned_to_nat(3u);
v___x_193_ = lean_nat_div(v___x_191_, v___x_192_);
lean_dec(v___x_191_);
v___x_194_ = lean_array_get_size(v_buckets_x27_189_);
v___x_195_ = lean_nat_dec_le(v___x_193_, v___x_194_);
lean_dec(v___x_193_);
if (v___x_195_ == 0)
{
lean_object* v_val_196_; lean_object* v___x_198_; 
v_val_196_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__3___redArg(v_buckets_x27_189_);
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 1, v_val_196_);
lean_ctor_set(v___x_166_, 0, v_size_x27_187_);
v___x_198_ = v___x_166_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_size_x27_187_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v_val_196_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
else
{
lean_object* v___x_201_; 
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 1, v_buckets_x27_189_);
lean_ctor_set(v___x_166_, 0, v_size_x27_187_);
v___x_201_ = v___x_166_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_size_x27_187_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v_buckets_x27_189_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
else
{
lean_object* v___x_203_; lean_object* v_buckets_x27_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_208_; 
lean_inc(v_bkt_184_);
v___x_203_ = lean_box(0);
v_buckets_x27_204_ = lean_array_uset(v_buckets_164_, v___x_183_, v___x_203_);
v___x_205_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__4___redArg(v_a_161_, v_b_162_, v_bkt_184_);
v___x_206_ = lean_array_uset(v_buckets_x27_204_, v___x_183_, v___x_205_);
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 1, v___x_206_);
v___x_208_ = v___x_166_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_size_163_);
lean_ctor_set(v_reuseFailAlloc_209_, 1, v___x_206_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0_spec__0___redArg(lean_object* v_a_211_, lean_object* v_x_212_){
_start:
{
if (lean_obj_tag(v_x_212_) == 0)
{
lean_object* v___x_213_; 
v___x_213_ = lean_box(0);
return v___x_213_;
}
else
{
lean_object* v_key_214_; lean_object* v_value_215_; lean_object* v_tail_216_; size_t v___x_217_; size_t v___x_218_; uint8_t v___x_219_; 
v_key_214_ = lean_ctor_get(v_x_212_, 0);
v_value_215_ = lean_ctor_get(v_x_212_, 1);
v_tail_216_ = lean_ctor_get(v_x_212_, 2);
v___x_217_ = lean_ptr_addr(v_key_214_);
v___x_218_ = lean_ptr_addr(v_a_211_);
v___x_219_ = lean_usize_dec_eq(v___x_217_, v___x_218_);
if (v___x_219_ == 0)
{
v_x_212_ = v_tail_216_;
goto _start;
}
else
{
lean_object* v___x_221_; 
lean_inc(v_value_215_);
v___x_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_221_, 0, v_value_215_);
return v___x_221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0_spec__0___redArg___boxed(lean_object* v_a_222_, lean_object* v_x_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0_spec__0___redArg(v_a_222_, v_x_223_);
lean_dec(v_x_223_);
lean_dec_ref(v_a_222_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0___redArg(lean_object* v_m_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_buckets_227_; lean_object* v___x_228_; size_t v___x_229_; size_t v___x_230_; size_t v___x_231_; uint64_t v___x_232_; uint64_t v___x_233_; uint64_t v___x_234_; uint64_t v_fold_235_; uint64_t v___x_236_; uint64_t v___x_237_; uint64_t v___x_238_; size_t v___x_239_; size_t v___x_240_; size_t v___x_241_; size_t v___x_242_; size_t v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v_buckets_227_ = lean_ctor_get(v_m_225_, 1);
v___x_228_ = lean_array_get_size(v_buckets_227_);
v___x_229_ = lean_ptr_addr(v_a_226_);
v___x_230_ = ((size_t)3ULL);
v___x_231_ = lean_usize_shift_right(v___x_229_, v___x_230_);
v___x_232_ = lean_usize_to_uint64(v___x_231_);
v___x_233_ = 32ULL;
v___x_234_ = lean_uint64_shift_right(v___x_232_, v___x_233_);
v_fold_235_ = lean_uint64_xor(v___x_232_, v___x_234_);
v___x_236_ = 16ULL;
v___x_237_ = lean_uint64_shift_right(v_fold_235_, v___x_236_);
v___x_238_ = lean_uint64_xor(v_fold_235_, v___x_237_);
v___x_239_ = lean_uint64_to_usize(v___x_238_);
v___x_240_ = lean_usize_of_nat(v___x_228_);
v___x_241_ = ((size_t)1ULL);
v___x_242_ = lean_usize_sub(v___x_240_, v___x_241_);
v___x_243_ = lean_usize_land(v___x_239_, v___x_242_);
v___x_244_ = lean_array_uget_borrowed(v_buckets_227_, v___x_243_);
v___x_245_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0_spec__0___redArg(v_a_226_, v___x_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0___redArg___boxed(lean_object* v_m_246_, lean_object* v_a_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0___redArg(v_m_246_, v_a_247_);
lean_dec_ref(v_a_247_);
lean_dec_ref(v_m_246_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet___lam__0___boxed(lean_object* v_fn_249_, lean_object* v_arg_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet___lam__0(v_fn_249_, v_arg_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
lean_dec(v___y_251_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet___boxed(lean_object* v_e_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet(v_e_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_);
lean_dec(v_a_267_);
lean_dec_ref(v_a_266_);
lean_dec(v_a_265_);
lean_dec_ref(v_a_264_);
lean_dec(v_a_263_);
lean_dec_ref(v_a_262_);
lean_dec(v_a_261_);
return v_res_269_;
}
}
lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet(lean_object* v_e_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_){
_start:
{
lean_object* v_e_280_; lean_object* v_k_281_; lean_object* v___y_282_; lean_object* v___y_283_; lean_object* v___y_284_; lean_object* v___y_285_; lean_object* v___y_286_; lean_object* v___y_287_; lean_object* v___y_288_; 
switch(lean_obj_tag(v_e_270_))
{
case 8:
{
uint8_t v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
lean_dec_ref_known(v_e_270_, 4);
v___x_324_ = 1;
v___x_325_ = lean_box(v___x_324_);
v___x_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
return v___x_326_;
}
case 5:
{
lean_object* v_fn_327_; lean_object* v_arg_328_; lean_object* v___f_329_; 
v_fn_327_ = lean_ctor_get(v_e_270_, 0);
v_arg_328_ = lean_ctor_get(v_e_270_, 1);
lean_inc_ref(v_arg_328_);
lean_inc_ref(v_fn_327_);
v___f_329_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet___lam__0___boxed), 10, 2);
lean_closure_set(v___f_329_, 0, v_fn_327_);
lean_closure_set(v___f_329_, 1, v_arg_328_);
v_e_280_ = v_e_270_;
v_k_281_ = v___f_329_;
v___y_282_ = v_a_271_;
v___y_283_ = v_a_272_;
v___y_284_ = v_a_273_;
v___y_285_ = v_a_274_;
v___y_286_ = v_a_275_;
v___y_287_ = v_a_276_;
v___y_288_ = v_a_277_;
goto v___jp_279_;
}
case 10:
{
lean_object* v_expr_330_; lean_object* v___x_331_; 
v_expr_330_ = lean_ctor_get(v_e_270_, 1);
lean_inc_ref(v_expr_330_);
v___x_331_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet___boxed), 9, 1);
lean_closure_set(v___x_331_, 0, v_expr_330_);
v_e_280_ = v_e_270_;
v_k_281_ = v___x_331_;
v___y_282_ = v_a_271_;
v___y_283_ = v_a_272_;
v___y_284_ = v_a_273_;
v___y_285_ = v_a_274_;
v___y_286_ = v_a_275_;
v___y_287_ = v_a_276_;
v___y_288_ = v_a_277_;
goto v___jp_279_;
}
case 11:
{
lean_object* v_struct_332_; lean_object* v___x_333_; 
v_struct_332_ = lean_ctor_get(v_e_270_, 2);
lean_inc_ref(v_struct_332_);
v___x_333_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet___boxed), 9, 1);
lean_closure_set(v___x_333_, 0, v_struct_332_);
v_e_280_ = v_e_270_;
v_k_281_ = v___x_333_;
v___y_282_ = v_a_271_;
v___y_283_ = v_a_272_;
v___y_284_ = v_a_273_;
v___y_285_ = v_a_274_;
v___y_286_ = v_a_275_;
v___y_287_ = v_a_276_;
v___y_288_ = v_a_277_;
goto v___jp_279_;
}
default: 
{
uint8_t v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
lean_dec_ref(v_e_270_);
v___x_334_ = 0;
v___x_335_ = lean_box(v___x_334_);
v___x_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
return v___x_336_;
}
}
v___jp_279_:
{
lean_object* v___x_289_; lean_object* v_hasLetCache_290_; lean_object* v___x_291_; 
v___x_289_ = lean_st_ref_get(v___y_282_);
v_hasLetCache_290_ = lean_ctor_get(v___x_289_, 2);
lean_inc_ref(v_hasLetCache_290_);
lean_dec(v___x_289_);
v___x_291_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0___redArg(v_hasLetCache_290_, v_e_280_);
lean_dec_ref(v_hasLetCache_290_);
if (lean_obj_tag(v___x_291_) == 1)
{
lean_object* v_val_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_299_; 
lean_dec_ref(v_k_281_);
lean_dec_ref(v_e_280_);
v_val_292_ = lean_ctor_get(v___x_291_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_299_ == 0)
{
v___x_294_ = v___x_291_;
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_val_292_);
lean_dec(v___x_291_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_297_; 
if (v_isShared_295_ == 0)
{
lean_ctor_set_tag(v___x_294_, 0);
v___x_297_ = v___x_294_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_val_292_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
else
{
lean_object* v___x_300_; 
lean_dec(v___x_291_);
lean_inc(v___y_288_);
lean_inc_ref(v___y_287_);
lean_inc(v___y_286_);
lean_inc_ref(v___y_285_);
lean_inc(v___y_284_);
lean_inc_ref(v___y_283_);
lean_inc(v___y_282_);
v___x_300_ = lean_apply_8(v_k_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, lean_box(0));
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v_a_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_323_; 
v_a_301_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_323_ == 0)
{
v___x_303_ = v___x_300_;
v_isShared_304_ = v_isSharedCheck_323_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_a_301_);
lean_dec(v___x_300_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_323_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_305_; lean_object* v_cache_306_; lean_object* v_cacheClosed_307_; lean_object* v_hasLetCache_308_; lean_object* v_decls_309_; lean_object* v_valueMap_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_322_; 
v___x_305_ = lean_st_ref_take(v___y_282_);
v_cache_306_ = lean_ctor_get(v___x_305_, 0);
v_cacheClosed_307_ = lean_ctor_get(v___x_305_, 1);
v_hasLetCache_308_ = lean_ctor_get(v___x_305_, 2);
v_decls_309_ = lean_ctor_get(v___x_305_, 3);
v_valueMap_310_ = lean_ctor_get(v___x_305_, 4);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_322_ == 0)
{
v___x_312_ = v___x_305_;
v_isShared_313_ = v_isSharedCheck_322_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_valueMap_310_);
lean_inc(v_decls_309_);
lean_inc(v_hasLetCache_308_);
lean_inc(v_cacheClosed_307_);
lean_inc(v_cache_306_);
lean_dec(v___x_305_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_322_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_314_; lean_object* v___x_316_; 
lean_inc(v_a_301_);
v___x_314_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1___redArg(v_hasLetCache_308_, v_e_280_, v_a_301_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 2, v___x_314_);
v___x_316_ = v___x_312_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_cache_306_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v_cacheClosed_307_);
lean_ctor_set(v_reuseFailAlloc_321_, 2, v___x_314_);
lean_ctor_set(v_reuseFailAlloc_321_, 3, v_decls_309_);
lean_ctor_set(v_reuseFailAlloc_321_, 4, v_valueMap_310_);
v___x_316_ = v_reuseFailAlloc_321_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
lean_object* v___x_317_; lean_object* v___x_319_; 
v___x_317_ = lean_st_ref_put(v___y_282_, v___x_316_);
if (v_isShared_304_ == 0)
{
v___x_319_ = v___x_303_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_a_301_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_280_);
return v___x_300_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_270_ = stack[0].m_obj;
lean_object* v_a_271_ = stack[1].m_obj;
lean_object* v_a_272_ = stack[2].m_obj;
lean_object* v_a_273_ = stack[3].m_obj;
lean_object* v_a_274_ = stack[4].m_obj;
lean_object* v_a_275_ = stack[5].m_obj;
lean_object* v_a_276_ = stack[6].m_obj;
lean_object* v_a_277_ = stack[7].m_obj;
lean_object* v_res_337_;
v_res_337_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet(v_e_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_);
stack->m_obj
 = v_res_337_;
}
lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet___lam__0(lean_object* v_fn_338_, lean_object* v_arg_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet(v_fn_338_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
if (lean_obj_tag(v___x_348_) == 0)
{
lean_object* v_a_349_; uint8_t v___x_350_; 
v_a_349_ = lean_ctor_get(v___x_348_, 0);
v___x_350_ = lean_unbox(v_a_349_);
if (v___x_350_ == 0)
{
lean_object* v___x_351_; 
lean_dec_ref_known(v___x_348_, 1);
v___x_351_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet(v_arg_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
return v___x_351_;
}
else
{
lean_dec_ref(v_arg_339_);
return v___x_348_;
}
}
else
{
lean_dec_ref(v_arg_339_);
return v___x_348_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fn_338_ = stack[0].m_obj;
lean_object* v_arg_339_ = stack[1].m_obj;
lean_object* v___y_340_ = stack[2].m_obj;
lean_object* v___y_341_ = stack[3].m_obj;
lean_object* v___y_342_ = stack[4].m_obj;
lean_object* v___y_343_ = stack[5].m_obj;
lean_object* v___y_344_ = stack[6].m_obj;
lean_object* v___y_345_ = stack[7].m_obj;
lean_object* v___y_346_ = stack[8].m_obj;
lean_object* v_res_352_;
v_res_352_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet___lam__0(v_fn_338_, v_arg_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
stack->m_obj
 = v_res_352_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0(lean_object* v_00_u03b2_353_, lean_object* v_m_354_, lean_object* v_a_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0___redArg(v_m_354_, v_a_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0___boxed(lean_object* v_00_u03b2_357_, lean_object* v_m_358_, lean_object* v_a_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0(v_00_u03b2_357_, v_m_358_, v_a_359_);
lean_dec_ref(v_a_359_);
lean_dec_ref(v_m_358_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1(lean_object* v_00_u03b2_361_, lean_object* v_m_362_, lean_object* v_a_363_, lean_object* v_b_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1___redArg(v_m_362_, v_a_363_, v_b_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0_spec__0(lean_object* v_00_u03b2_366_, lean_object* v_a_367_, lean_object* v_x_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0_spec__0___redArg(v_a_367_, v_x_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0_spec__0___boxed(lean_object* v_00_u03b2_370_, lean_object* v_a_371_, lean_object* v_x_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0_spec__0(v_00_u03b2_370_, v_a_371_, v_x_372_);
lean_dec(v_x_372_);
lean_dec_ref(v_a_371_);
return v_res_373_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2(lean_object* v_00_u03b2_374_, lean_object* v_a_375_, lean_object* v_x_376_){
_start:
{
uint8_t v___x_377_; 
v___x_377_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2___redArg(v_a_375_, v_x_376_);
return v___x_377_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_375_ = stack[1].m_obj;
lean_object* v_x_376_ = stack[2].m_obj;
uint8_t v_res_378_;
v_res_378_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2(lean_box(0), v_a_375_, v_x_376_);
stack->m_num = v_res_378_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2___boxed(lean_object* v_00_u03b2_379_, lean_object* v_a_380_, lean_object* v_x_381_){
_start:
{
uint8_t v_res_382_; lean_object* v_r_383_; 
v_res_382_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2(v_00_u03b2_379_, v_a_380_, v_x_381_);
lean_dec(v_x_381_);
lean_dec_ref(v_a_380_);
v_r_383_ = lean_box(v_res_382_);
return v_r_383_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__3(lean_object* v_00_u03b2_384_, lean_object* v_data_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__3___redArg(v_data_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__4(lean_object* v_00_u03b2_387_, lean_object* v_a_388_, lean_object* v_b_389_, lean_object* v_x_390_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__4___redArg(v_a_388_, v_b_389_, v_x_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_392_, lean_object* v_i_393_, lean_object* v_source_394_, lean_object* v_target_395_){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__3_spec__4___redArg(v_i_393_, v_source_394_, v_target_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_397_, lean_object* v_x_398_, lean_object* v_x_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__3_spec__4_spec__5___redArg(v_x_398_, v_x_399_);
return v___x_400_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2___redArg(lean_object* v_fvarId_401_, lean_object* v___y_402_){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = l_Lean_Expr_fvar___override(v_fvarId_401_);
v___x_405_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_404_, v___y_402_);
return v___x_405_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_401_ = stack[0].m_obj;
lean_object* v___y_402_ = stack[1].m_obj;
lean_object* v_res_406_;
v_res_406_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2___redArg(v_fvarId_401_, v___y_402_);
stack->m_obj
 = v_res_406_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2___redArg___boxed(lean_object* v_fvarId_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2___redArg(v_fvarId_407_, v___y_408_);
lean_dec(v___y_408_);
return v_res_410_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2(lean_object* v_fvarId_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2___redArg(v_fvarId_411_, v___y_414_);
return v___x_420_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_411_ = stack[0].m_obj;
lean_object* v___y_412_ = stack[1].m_obj;
lean_object* v___y_413_ = stack[2].m_obj;
lean_object* v___y_414_ = stack[3].m_obj;
lean_object* v___y_415_ = stack[4].m_obj;
lean_object* v___y_416_ = stack[5].m_obj;
lean_object* v___y_417_ = stack[6].m_obj;
lean_object* v___y_418_ = stack[7].m_obj;
lean_object* v_res_421_;
v_res_421_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2(v_fvarId_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_);
stack->m_obj
 = v_res_421_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2___boxed(lean_object* v_fvarId_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2(v_fvarId_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec(v___y_423_);
return v_res_431_;
}
}
lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2___redArg(lean_object* v___y_432_){
_start:
{
lean_object* v___x_434_; lean_object* v_ngen_435_; lean_object* v_namePrefix_436_; lean_object* v_idx_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_467_; 
v___x_434_ = lean_st_ref_get(v___y_432_);
v_ngen_435_ = lean_ctor_get(v___x_434_, 2);
lean_inc_ref(v_ngen_435_);
lean_dec(v___x_434_);
v_namePrefix_436_ = lean_ctor_get(v_ngen_435_, 0);
v_idx_437_ = lean_ctor_get(v_ngen_435_, 1);
v_isSharedCheck_467_ = !lean_is_exclusive(v_ngen_435_);
if (v_isSharedCheck_467_ == 0)
{
v___x_439_ = v_ngen_435_;
v_isShared_440_ = v_isSharedCheck_467_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_idx_437_);
lean_inc(v_namePrefix_436_);
lean_dec(v_ngen_435_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_467_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v_r_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_445_; 
lean_inc(v_idx_437_);
lean_inc(v_namePrefix_436_);
v_r_441_ = l_Lean_Name_num___override(v_namePrefix_436_, v_idx_437_);
v___x_442_ = lean_unsigned_to_nat(1u);
v___x_443_ = lean_nat_add(v_idx_437_, v___x_442_);
lean_dec(v_idx_437_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 1, v___x_443_);
v___x_445_ = v___x_439_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_namePrefix_436_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v___x_443_);
v___x_445_ = v_reuseFailAlloc_466_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
lean_object* v___x_446_; lean_object* v_env_447_; lean_object* v_nextMacroScope_448_; lean_object* v_auxDeclNGen_449_; lean_object* v_traceState_450_; lean_object* v_cache_451_; lean_object* v_recordedDeps_452_; lean_object* v_messages_453_; lean_object* v_infoState_454_; lean_object* v_snapshotTasks_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_464_; 
v___x_446_ = lean_st_ref_take(v___y_432_);
v_env_447_ = lean_ctor_get(v___x_446_, 0);
v_nextMacroScope_448_ = lean_ctor_get(v___x_446_, 1);
v_auxDeclNGen_449_ = lean_ctor_get(v___x_446_, 3);
v_traceState_450_ = lean_ctor_get(v___x_446_, 4);
v_cache_451_ = lean_ctor_get(v___x_446_, 5);
v_recordedDeps_452_ = lean_ctor_get(v___x_446_, 6);
v_messages_453_ = lean_ctor_get(v___x_446_, 7);
v_infoState_454_ = lean_ctor_get(v___x_446_, 8);
v_snapshotTasks_455_ = lean_ctor_get(v___x_446_, 9);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_464_ == 0)
{
lean_object* v_unused_465_; 
v_unused_465_ = lean_ctor_get(v___x_446_, 2);
lean_dec(v_unused_465_);
v___x_457_ = v___x_446_;
v_isShared_458_ = v_isSharedCheck_464_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_snapshotTasks_455_);
lean_inc(v_infoState_454_);
lean_inc(v_messages_453_);
lean_inc(v_recordedDeps_452_);
lean_inc(v_cache_451_);
lean_inc(v_traceState_450_);
lean_inc(v_auxDeclNGen_449_);
lean_inc(v_nextMacroScope_448_);
lean_inc(v_env_447_);
lean_dec(v___x_446_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_464_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_460_; 
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 2, v___x_445_);
v___x_460_ = v___x_457_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_env_447_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v_nextMacroScope_448_);
lean_ctor_set(v_reuseFailAlloc_463_, 2, v___x_445_);
lean_ctor_set(v_reuseFailAlloc_463_, 3, v_auxDeclNGen_449_);
lean_ctor_set(v_reuseFailAlloc_463_, 4, v_traceState_450_);
lean_ctor_set(v_reuseFailAlloc_463_, 5, v_cache_451_);
lean_ctor_set(v_reuseFailAlloc_463_, 6, v_recordedDeps_452_);
lean_ctor_set(v_reuseFailAlloc_463_, 7, v_messages_453_);
lean_ctor_set(v_reuseFailAlloc_463_, 8, v_infoState_454_);
lean_ctor_set(v_reuseFailAlloc_463_, 9, v_snapshotTasks_455_);
v___x_460_ = v_reuseFailAlloc_463_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = lean_st_ref_put(v___y_432_, v___x_460_);
v___x_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_462_, 0, v_r_441_);
return v___x_462_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_432_ = stack[0].m_obj;
lean_object* v_res_468_;
v_res_468_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2___redArg(v___y_432_);
stack->m_obj
 = v_res_468_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2___redArg___boxed(lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2___redArg(v___y_469_);
lean_dec(v___y_469_);
return v_res_471_;
}
}
lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1(lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v___x_480_; lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_488_; 
v___x_480_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2___redArg(v___y_478_);
v_a_481_ = lean_ctor_get(v___x_480_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_488_ == 0)
{
v___x_483_ = v___x_480_;
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___x_480_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_486_; 
if (v_isShared_484_ == 0)
{
v___x_486_ = v___x_483_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_a_481_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_472_ = stack[0].m_obj;
lean_object* v___y_473_ = stack[1].m_obj;
lean_object* v___y_474_ = stack[2].m_obj;
lean_object* v___y_475_ = stack[3].m_obj;
lean_object* v___y_476_ = stack[4].m_obj;
lean_object* v___y_477_ = stack[5].m_obj;
lean_object* v___y_478_ = stack[6].m_obj;
lean_object* v_res_489_;
v_res_489_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1(v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
stack->m_obj
 = v_res_489_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1___boxed(lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1(v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
lean_dec(v___y_496_);
lean_dec_ref(v___y_495_);
lean_dec(v___y_494_);
lean_dec_ref(v___y_493_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
lean_dec(v___y_490_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0___redArg(lean_object* v_a_499_, lean_object* v_x_500_){
_start:
{
if (lean_obj_tag(v_x_500_) == 0)
{
lean_object* v___x_501_; 
v___x_501_ = lean_box(0);
return v___x_501_;
}
else
{
lean_object* v_key_502_; lean_object* v_value_503_; lean_object* v_tail_504_; lean_object* v_fst_505_; lean_object* v_snd_506_; lean_object* v_fst_507_; lean_object* v_snd_508_; size_t v___x_509_; size_t v___x_510_; uint8_t v___x_511_; 
v_key_502_ = lean_ctor_get(v_x_500_, 0);
v_value_503_ = lean_ctor_get(v_x_500_, 1);
v_tail_504_ = lean_ctor_get(v_x_500_, 2);
v_fst_505_ = lean_ctor_get(v_key_502_, 0);
v_snd_506_ = lean_ctor_get(v_key_502_, 1);
v_fst_507_ = lean_ctor_get(v_a_499_, 0);
v_snd_508_ = lean_ctor_get(v_a_499_, 1);
v___x_509_ = lean_ptr_addr(v_fst_505_);
v___x_510_ = lean_ptr_addr(v_fst_507_);
v___x_511_ = lean_usize_dec_eq(v___x_509_, v___x_510_);
if (v___x_511_ == 0)
{
v_x_500_ = v_tail_504_;
goto _start;
}
else
{
size_t v___x_513_; size_t v___x_514_; uint8_t v___x_515_; 
v___x_513_ = lean_ptr_addr(v_snd_506_);
v___x_514_ = lean_ptr_addr(v_snd_508_);
v___x_515_ = lean_usize_dec_eq(v___x_513_, v___x_514_);
if (v___x_515_ == 0)
{
v_x_500_ = v_tail_504_;
goto _start;
}
else
{
lean_object* v___x_517_; 
lean_inc(v_value_503_);
v___x_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_517_, 0, v_value_503_);
return v___x_517_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0___redArg___boxed(lean_object* v_a_518_, lean_object* v_x_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0___redArg(v_a_518_, v_x_519_);
lean_dec(v_x_519_);
lean_dec_ref(v_a_518_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0___redArg(lean_object* v_m_521_, lean_object* v_a_522_){
_start:
{
lean_object* v_buckets_523_; lean_object* v_fst_524_; lean_object* v_snd_525_; lean_object* v___x_526_; size_t v___x_527_; size_t v___x_528_; size_t v___x_529_; uint64_t v___x_530_; size_t v___x_531_; size_t v___x_532_; uint64_t v___x_533_; uint64_t v___x_534_; uint64_t v___x_535_; uint64_t v___x_536_; uint64_t v_fold_537_; uint64_t v___x_538_; uint64_t v___x_539_; uint64_t v___x_540_; size_t v___x_541_; size_t v___x_542_; size_t v___x_543_; size_t v___x_544_; size_t v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v_buckets_523_ = lean_ctor_get(v_m_521_, 1);
v_fst_524_ = lean_ctor_get(v_a_522_, 0);
v_snd_525_ = lean_ctor_get(v_a_522_, 1);
v___x_526_ = lean_array_get_size(v_buckets_523_);
v___x_527_ = lean_ptr_addr(v_fst_524_);
v___x_528_ = ((size_t)3ULL);
v___x_529_ = lean_usize_shift_right(v___x_527_, v___x_528_);
v___x_530_ = lean_usize_to_uint64(v___x_529_);
v___x_531_ = lean_ptr_addr(v_snd_525_);
v___x_532_ = lean_usize_shift_right(v___x_531_, v___x_528_);
v___x_533_ = lean_usize_to_uint64(v___x_532_);
v___x_534_ = lean_uint64_mix_hash(v___x_530_, v___x_533_);
v___x_535_ = 32ULL;
v___x_536_ = lean_uint64_shift_right(v___x_534_, v___x_535_);
v_fold_537_ = lean_uint64_xor(v___x_534_, v___x_536_);
v___x_538_ = 16ULL;
v___x_539_ = lean_uint64_shift_right(v_fold_537_, v___x_538_);
v___x_540_ = lean_uint64_xor(v_fold_537_, v___x_539_);
v___x_541_ = lean_uint64_to_usize(v___x_540_);
v___x_542_ = lean_usize_of_nat(v___x_526_);
v___x_543_ = ((size_t)1ULL);
v___x_544_ = lean_usize_sub(v___x_542_, v___x_543_);
v___x_545_ = lean_usize_land(v___x_541_, v___x_544_);
v___x_546_ = lean_array_uget_borrowed(v_buckets_523_, v___x_545_);
v___x_547_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0___redArg(v_a_522_, v___x_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0___redArg___boxed(lean_object* v_m_548_, lean_object* v_a_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0___redArg(v_m_548_, v_a_549_);
lean_dec_ref(v_a_549_);
lean_dec_ref(v_m_548_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__7___redArg(lean_object* v_a_551_, lean_object* v_b_552_, lean_object* v_x_553_){
_start:
{
if (lean_obj_tag(v_x_553_) == 0)
{
lean_dec(v_b_552_);
lean_dec_ref(v_a_551_);
return v_x_553_;
}
else
{
lean_object* v_key_554_; lean_object* v_value_555_; lean_object* v_tail_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_576_; 
v_key_554_ = lean_ctor_get(v_x_553_, 0);
v_value_555_ = lean_ctor_get(v_x_553_, 1);
v_tail_556_ = lean_ctor_get(v_x_553_, 2);
v_isSharedCheck_576_ = !lean_is_exclusive(v_x_553_);
if (v_isSharedCheck_576_ == 0)
{
v___x_558_ = v_x_553_;
v_isShared_559_ = v_isSharedCheck_576_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_tail_556_);
lean_inc(v_value_555_);
lean_inc(v_key_554_);
lean_dec(v_x_553_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_576_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v_fst_565_; lean_object* v_snd_566_; lean_object* v_fst_567_; lean_object* v_snd_568_; size_t v___x_569_; size_t v___x_570_; uint8_t v___x_571_; 
v_fst_565_ = lean_ctor_get(v_key_554_, 0);
v_snd_566_ = lean_ctor_get(v_key_554_, 1);
v_fst_567_ = lean_ctor_get(v_a_551_, 0);
v_snd_568_ = lean_ctor_get(v_a_551_, 1);
v___x_569_ = lean_ptr_addr(v_fst_565_);
v___x_570_ = lean_ptr_addr(v_fst_567_);
v___x_571_ = lean_usize_dec_eq(v___x_569_, v___x_570_);
if (v___x_571_ == 0)
{
goto v___jp_560_;
}
else
{
size_t v___x_572_; size_t v___x_573_; uint8_t v___x_574_; 
v___x_572_ = lean_ptr_addr(v_snd_566_);
v___x_573_ = lean_ptr_addr(v_snd_568_);
v___x_574_ = lean_usize_dec_eq(v___x_572_, v___x_573_);
if (v___x_574_ == 0)
{
goto v___jp_560_;
}
else
{
lean_object* v___x_575_; 
lean_del_object(v___x_558_);
lean_dec(v_value_555_);
lean_dec(v_key_554_);
v___x_575_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_575_, 0, v_a_551_);
lean_ctor_set(v___x_575_, 1, v_b_552_);
lean_ctor_set(v___x_575_, 2, v_tail_556_);
return v___x_575_;
}
}
v___jp_560_:
{
lean_object* v___x_561_; lean_object* v___x_563_; 
v___x_561_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__7___redArg(v_a_551_, v_b_552_, v_tail_556_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 2, v___x_561_);
v___x_563_ = v___x_558_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_key_554_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_value_555_);
lean_ctor_set(v_reuseFailAlloc_564_, 2, v___x_561_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
}
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5___redArg(lean_object* v_a_577_, lean_object* v_x_578_){
_start:
{
if (lean_obj_tag(v_x_578_) == 0)
{
uint8_t v___x_579_; 
v___x_579_ = 0;
return v___x_579_;
}
else
{
lean_object* v_key_580_; lean_object* v_tail_581_; lean_object* v_fst_582_; lean_object* v_snd_583_; lean_object* v_fst_584_; lean_object* v_snd_585_; size_t v___x_586_; size_t v___x_587_; uint8_t v___x_588_; 
v_key_580_ = lean_ctor_get(v_x_578_, 0);
v_tail_581_ = lean_ctor_get(v_x_578_, 2);
v_fst_582_ = lean_ctor_get(v_key_580_, 0);
v_snd_583_ = lean_ctor_get(v_key_580_, 1);
v_fst_584_ = lean_ctor_get(v_a_577_, 0);
v_snd_585_ = lean_ctor_get(v_a_577_, 1);
v___x_586_ = lean_ptr_addr(v_fst_582_);
v___x_587_ = lean_ptr_addr(v_fst_584_);
v___x_588_ = lean_usize_dec_eq(v___x_586_, v___x_587_);
if (v___x_588_ == 0)
{
v_x_578_ = v_tail_581_;
goto _start;
}
else
{
size_t v___x_590_; size_t v___x_591_; uint8_t v___x_592_; 
v___x_590_ = lean_ptr_addr(v_snd_583_);
v___x_591_ = lean_ptr_addr(v_snd_585_);
v___x_592_ = lean_usize_dec_eq(v___x_590_, v___x_591_);
if (v___x_592_ == 0)
{
v_x_578_ = v_tail_581_;
goto _start;
}
else
{
return v___x_592_;
}
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_577_ = stack[0].m_obj;
lean_object* v_x_578_ = stack[1].m_obj;
uint8_t v_res_594_;
v_res_594_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5___redArg(v_a_577_, v_x_578_);
stack->m_num = v_res_594_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5___redArg___boxed(lean_object* v_a_595_, lean_object* v_x_596_){
_start:
{
uint8_t v_res_597_; lean_object* v_r_598_; 
v_res_597_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5___redArg(v_a_595_, v_x_596_);
lean_dec(v_x_596_);
lean_dec_ref(v_a_595_);
v_r_598_ = lean_box(v_res_597_);
return v_r_598_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6_spec__7_spec__8___redArg(lean_object* v_x_599_, lean_object* v_x_600_){
_start:
{
if (lean_obj_tag(v_x_600_) == 0)
{
return v_x_599_;
}
else
{
lean_object* v_key_601_; lean_object* v_value_602_; lean_object* v_tail_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_635_; 
v_key_601_ = lean_ctor_get(v_x_600_, 0);
v_value_602_ = lean_ctor_get(v_x_600_, 1);
v_tail_603_ = lean_ctor_get(v_x_600_, 2);
v_isSharedCheck_635_ = !lean_is_exclusive(v_x_600_);
if (v_isSharedCheck_635_ == 0)
{
v___x_605_ = v_x_600_;
v_isShared_606_ = v_isSharedCheck_635_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_tail_603_);
lean_inc(v_value_602_);
lean_inc(v_key_601_);
lean_dec(v_x_600_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_635_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v_fst_607_; lean_object* v_snd_608_; lean_object* v___x_609_; size_t v___x_610_; size_t v___x_611_; size_t v___x_612_; uint64_t v___x_613_; size_t v___x_614_; size_t v___x_615_; uint64_t v___x_616_; uint64_t v___x_617_; uint64_t v___x_618_; uint64_t v___x_619_; uint64_t v_fold_620_; uint64_t v___x_621_; uint64_t v___x_622_; uint64_t v___x_623_; size_t v___x_624_; size_t v___x_625_; size_t v___x_626_; size_t v___x_627_; size_t v___x_628_; lean_object* v___x_629_; lean_object* v___x_631_; 
v_fst_607_ = lean_ctor_get(v_key_601_, 0);
v_snd_608_ = lean_ctor_get(v_key_601_, 1);
v___x_609_ = lean_array_get_size(v_x_599_);
v___x_610_ = lean_ptr_addr(v_fst_607_);
v___x_611_ = ((size_t)3ULL);
v___x_612_ = lean_usize_shift_right(v___x_610_, v___x_611_);
v___x_613_ = lean_usize_to_uint64(v___x_612_);
v___x_614_ = lean_ptr_addr(v_snd_608_);
v___x_615_ = lean_usize_shift_right(v___x_614_, v___x_611_);
v___x_616_ = lean_usize_to_uint64(v___x_615_);
v___x_617_ = lean_uint64_mix_hash(v___x_613_, v___x_616_);
v___x_618_ = 32ULL;
v___x_619_ = lean_uint64_shift_right(v___x_617_, v___x_618_);
v_fold_620_ = lean_uint64_xor(v___x_617_, v___x_619_);
v___x_621_ = 16ULL;
v___x_622_ = lean_uint64_shift_right(v_fold_620_, v___x_621_);
v___x_623_ = lean_uint64_xor(v_fold_620_, v___x_622_);
v___x_624_ = lean_uint64_to_usize(v___x_623_);
v___x_625_ = lean_usize_of_nat(v___x_609_);
v___x_626_ = ((size_t)1ULL);
v___x_627_ = lean_usize_sub(v___x_625_, v___x_626_);
v___x_628_ = lean_usize_land(v___x_624_, v___x_627_);
v___x_629_ = lean_array_uget_borrowed(v_x_599_, v___x_628_);
lean_inc(v___x_629_);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 2, v___x_629_);
v___x_631_ = v___x_605_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_key_601_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v_value_602_);
lean_ctor_set(v_reuseFailAlloc_634_, 2, v___x_629_);
v___x_631_ = v_reuseFailAlloc_634_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v___x_632_; 
v___x_632_ = lean_array_uset(v_x_599_, v___x_628_, v___x_631_);
v_x_599_ = v___x_632_;
v_x_600_ = v_tail_603_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6_spec__7___redArg(lean_object* v_i_636_, lean_object* v_source_637_, lean_object* v_target_638_){
_start:
{
lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_639_ = lean_array_get_size(v_source_637_);
v___x_640_ = lean_nat_dec_lt(v_i_636_, v___x_639_);
if (v___x_640_ == 0)
{
lean_dec_ref(v_source_637_);
lean_dec(v_i_636_);
return v_target_638_;
}
else
{
lean_object* v_es_641_; lean_object* v___x_642_; lean_object* v_source_643_; lean_object* v_target_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v_es_641_ = lean_array_fget(v_source_637_, v_i_636_);
v___x_642_ = lean_box(0);
v_source_643_ = lean_array_fset(v_source_637_, v_i_636_, v___x_642_);
v_target_644_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6_spec__7_spec__8___redArg(v_target_638_, v_es_641_);
v___x_645_ = lean_unsigned_to_nat(1u);
v___x_646_ = lean_nat_add(v_i_636_, v___x_645_);
lean_dec(v_i_636_);
v_i_636_ = v___x_646_;
v_source_637_ = v_source_643_;
v_target_638_ = v_target_644_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6___redArg(lean_object* v_data_648_){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v_nbuckets_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_649_ = lean_array_get_size(v_data_648_);
v___x_650_ = lean_unsigned_to_nat(2u);
v_nbuckets_651_ = lean_nat_mul(v___x_649_, v___x_650_);
v___x_652_ = lean_unsigned_to_nat(0u);
v___x_653_ = lean_box(0);
v___x_654_ = lean_mk_array(v_nbuckets_651_, v___x_653_);
v___x_655_ = lean_array_propagate_mark(v_data_648_, v___x_654_);
v___x_656_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6_spec__7___redArg(v___x_652_, v_data_648_, v___x_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3___redArg(lean_object* v_m_657_, lean_object* v_a_658_, lean_object* v_b_659_){
_start:
{
lean_object* v_size_660_; lean_object* v_buckets_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_713_; 
v_size_660_ = lean_ctor_get(v_m_657_, 0);
v_buckets_661_ = lean_ctor_get(v_m_657_, 1);
v_isSharedCheck_713_ = !lean_is_exclusive(v_m_657_);
if (v_isSharedCheck_713_ == 0)
{
v___x_663_ = v_m_657_;
v_isShared_664_ = v_isSharedCheck_713_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_buckets_661_);
lean_inc(v_size_660_);
lean_dec(v_m_657_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_713_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v_fst_665_; lean_object* v_snd_666_; lean_object* v___x_667_; size_t v___x_668_; size_t v___x_669_; size_t v___x_670_; uint64_t v___x_671_; size_t v___x_672_; size_t v___x_673_; uint64_t v___x_674_; uint64_t v___x_675_; uint64_t v___x_676_; uint64_t v___x_677_; uint64_t v_fold_678_; uint64_t v___x_679_; uint64_t v___x_680_; uint64_t v___x_681_; size_t v___x_682_; size_t v___x_683_; size_t v___x_684_; size_t v___x_685_; size_t v___x_686_; lean_object* v_bkt_687_; uint8_t v___x_688_; 
v_fst_665_ = lean_ctor_get(v_a_658_, 0);
v_snd_666_ = lean_ctor_get(v_a_658_, 1);
v___x_667_ = lean_array_get_size(v_buckets_661_);
v___x_668_ = lean_ptr_addr(v_fst_665_);
v___x_669_ = ((size_t)3ULL);
v___x_670_ = lean_usize_shift_right(v___x_668_, v___x_669_);
v___x_671_ = lean_usize_to_uint64(v___x_670_);
v___x_672_ = lean_ptr_addr(v_snd_666_);
v___x_673_ = lean_usize_shift_right(v___x_672_, v___x_669_);
v___x_674_ = lean_usize_to_uint64(v___x_673_);
v___x_675_ = lean_uint64_mix_hash(v___x_671_, v___x_674_);
v___x_676_ = 32ULL;
v___x_677_ = lean_uint64_shift_right(v___x_675_, v___x_676_);
v_fold_678_ = lean_uint64_xor(v___x_675_, v___x_677_);
v___x_679_ = 16ULL;
v___x_680_ = lean_uint64_shift_right(v_fold_678_, v___x_679_);
v___x_681_ = lean_uint64_xor(v_fold_678_, v___x_680_);
v___x_682_ = lean_uint64_to_usize(v___x_681_);
v___x_683_ = lean_usize_of_nat(v___x_667_);
v___x_684_ = ((size_t)1ULL);
v___x_685_ = lean_usize_sub(v___x_683_, v___x_684_);
v___x_686_ = lean_usize_land(v___x_682_, v___x_685_);
v_bkt_687_ = lean_array_uget_borrowed(v_buckets_661_, v___x_686_);
v___x_688_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5___redArg(v_a_658_, v_bkt_687_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; lean_object* v_size_x27_690_; lean_object* v___x_691_; lean_object* v_buckets_x27_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; uint8_t v___x_698_; 
v___x_689_ = lean_unsigned_to_nat(1u);
v_size_x27_690_ = lean_nat_add(v_size_660_, v___x_689_);
lean_dec(v_size_660_);
lean_inc(v_bkt_687_);
v___x_691_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_691_, 0, v_a_658_);
lean_ctor_set(v___x_691_, 1, v_b_659_);
lean_ctor_set(v___x_691_, 2, v_bkt_687_);
v_buckets_x27_692_ = lean_array_uset(v_buckets_661_, v___x_686_, v___x_691_);
v___x_693_ = lean_unsigned_to_nat(4u);
v___x_694_ = lean_nat_mul(v_size_x27_690_, v___x_693_);
v___x_695_ = lean_unsigned_to_nat(3u);
v___x_696_ = lean_nat_div(v___x_694_, v___x_695_);
lean_dec(v___x_694_);
v___x_697_ = lean_array_get_size(v_buckets_x27_692_);
v___x_698_ = lean_nat_dec_le(v___x_696_, v___x_697_);
lean_dec(v___x_696_);
if (v___x_698_ == 0)
{
lean_object* v_val_699_; lean_object* v___x_701_; 
v_val_699_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6___redArg(v_buckets_x27_692_);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 1, v_val_699_);
lean_ctor_set(v___x_663_, 0, v_size_x27_690_);
v___x_701_ = v___x_663_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_size_x27_690_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v_val_699_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
else
{
lean_object* v___x_704_; 
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 1, v_buckets_x27_692_);
lean_ctor_set(v___x_663_, 0, v_size_x27_690_);
v___x_704_ = v___x_663_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_size_x27_690_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v_buckets_x27_692_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
else
{
lean_object* v___x_706_; lean_object* v_buckets_x27_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_711_; 
lean_inc(v_bkt_687_);
v___x_706_ = lean_box(0);
v_buckets_x27_707_ = lean_array_uset(v_buckets_661_, v___x_686_, v___x_706_);
v___x_708_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__7___redArg(v_a_658_, v_b_659_, v_bkt_687_);
v___x_709_ = lean_array_uset(v_buckets_x27_707_, v___x_686_, v___x_708_);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 1, v___x_709_);
v___x_711_ = v___x_663_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_size_660_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v___x_709_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl(lean_object* v_userName_714_, lean_object* v_type_715_, lean_object* v_value_716_, uint8_t v_nondep_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_){
_start:
{
lean_object* v___x_726_; lean_object* v_key_727_; lean_object* v___x_728_; lean_object* v_valueMap_729_; lean_object* v___x_730_; 
v___x_726_ = l_Lean_Meta_Sym_LiftLet_instInhabitedDecl_default;
lean_inc_ref(v_value_716_);
lean_inc_ref(v_type_715_);
v_key_727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_727_, 0, v_type_715_);
lean_ctor_set(v_key_727_, 1, v_value_716_);
v___x_728_ = lean_st_ref_get(v_a_718_);
v_valueMap_729_ = lean_ctor_get(v___x_728_, 4);
lean_inc_ref(v_valueMap_729_);
lean_dec(v___x_728_);
v___x_730_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0___redArg(v_valueMap_729_, v_key_727_);
lean_dec_ref(v_valueMap_729_);
if (lean_obj_tag(v___x_730_) == 1)
{
lean_object* v_val_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_777_; 
lean_dec_ref_known(v_key_727_, 2);
lean_dec_ref(v_value_716_);
lean_dec_ref(v_type_715_);
lean_dec(v_userName_714_);
v_val_731_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_777_ == 0)
{
v___x_733_ = v___x_730_;
v_isShared_734_ = v_isSharedCheck_777_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_val_731_);
lean_dec(v___x_730_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_777_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___y_736_; 
if (v_nondep_717_ == 0)
{
lean_object* v___x_744_; lean_object* v_cache_745_; lean_object* v_cacheClosed_746_; lean_object* v_hasLetCache_747_; lean_object* v_decls_748_; lean_object* v_valueMap_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_776_; 
v___x_744_ = lean_st_ref_take(v_a_718_);
v_cache_745_ = lean_ctor_get(v___x_744_, 0);
v_cacheClosed_746_ = lean_ctor_get(v___x_744_, 1);
v_hasLetCache_747_ = lean_ctor_get(v___x_744_, 2);
v_decls_748_ = lean_ctor_get(v___x_744_, 3);
v_valueMap_749_ = lean_ctor_get(v___x_744_, 4);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_776_ == 0)
{
v___x_751_ = v___x_744_;
v_isShared_752_ = v_isSharedCheck_776_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_valueMap_749_);
lean_inc(v_decls_748_);
lean_inc(v_hasLetCache_747_);
lean_inc(v_cacheClosed_746_);
lean_inc(v_cache_745_);
lean_dec(v___x_744_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_776_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___y_754_; lean_object* v___x_759_; uint8_t v___x_760_; 
v___x_759_ = lean_array_get_size(v_decls_748_);
v___x_760_ = lean_nat_dec_lt(v_val_731_, v___x_759_);
if (v___x_760_ == 0)
{
v___y_754_ = v_decls_748_;
goto v___jp_753_;
}
else
{
lean_object* v_v_761_; lean_object* v_fvar_762_; lean_object* v_userName_763_; lean_object* v_type_764_; lean_object* v_value_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_775_; 
v_v_761_ = lean_array_fget(v_decls_748_, v_val_731_);
v_fvar_762_ = lean_ctor_get(v_v_761_, 0);
v_userName_763_ = lean_ctor_get(v_v_761_, 1);
v_type_764_ = lean_ctor_get(v_v_761_, 2);
v_value_765_ = lean_ctor_get(v_v_761_, 3);
v_isSharedCheck_775_ = !lean_is_exclusive(v_v_761_);
if (v_isSharedCheck_775_ == 0)
{
v___x_767_ = v_v_761_;
v_isShared_768_ = v_isSharedCheck_775_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_value_765_);
lean_inc(v_type_764_);
lean_inc(v_userName_763_);
lean_inc(v_fvar_762_);
lean_dec(v_v_761_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_775_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_769_; lean_object* v_xs_x27_770_; lean_object* v___x_772_; 
v___x_769_ = lean_box(0);
v_xs_x27_770_ = lean_array_fset(v_decls_748_, v_val_731_, v___x_769_);
if (v_isShared_768_ == 0)
{
v___x_772_ = v___x_767_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_fvar_762_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_userName_763_);
lean_ctor_set(v_reuseFailAlloc_774_, 2, v_type_764_);
lean_ctor_set(v_reuseFailAlloc_774_, 3, v_value_765_);
v___x_772_ = v_reuseFailAlloc_774_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
lean_object* v___x_773_; 
lean_ctor_set_uint8(v___x_772_, sizeof(void*)*4, v_nondep_717_);
v___x_773_ = lean_array_fset(v_xs_x27_770_, v_val_731_, v___x_772_);
v___y_754_ = v___x_773_;
goto v___jp_753_;
}
}
}
v___jp_753_:
{
lean_object* v___x_756_; 
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 3, v___y_754_);
v___x_756_ = v___x_751_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_cache_745_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v_cacheClosed_746_);
lean_ctor_set(v_reuseFailAlloc_758_, 2, v_hasLetCache_747_);
lean_ctor_set(v_reuseFailAlloc_758_, 3, v___y_754_);
lean_ctor_set(v_reuseFailAlloc_758_, 4, v_valueMap_749_);
v___x_756_ = v_reuseFailAlloc_758_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
lean_object* v___x_757_; 
v___x_757_ = lean_st_ref_put(v_a_718_, v___x_756_);
v___y_736_ = v_a_718_;
goto v___jp_735_;
}
}
}
}
else
{
v___y_736_ = v_a_718_;
goto v___jp_735_;
}
v___jp_735_:
{
lean_object* v___x_737_; lean_object* v_decls_738_; lean_object* v___x_739_; lean_object* v_fvar_740_; lean_object* v___x_742_; 
v___x_737_ = lean_st_ref_get(v___y_736_);
v_decls_738_ = lean_ctor_get(v___x_737_, 3);
lean_inc_ref(v_decls_738_);
lean_dec(v___x_737_);
v___x_739_ = lean_array_get(v___x_726_, v_decls_738_, v_val_731_);
lean_dec(v_val_731_);
lean_dec_ref(v_decls_738_);
v_fvar_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc_ref(v_fvar_740_);
lean_dec(v___x_739_);
if (v_isShared_734_ == 0)
{
lean_ctor_set_tag(v___x_733_, 0);
lean_ctor_set(v___x_733_, 0, v_fvar_740_);
v___x_742_ = v___x_733_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_fvar_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
else
{
lean_object* v___x_778_; 
lean_dec(v___x_730_);
v___x_778_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1(v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v_a_779_; lean_object* v___x_780_; 
v_a_779_ = lean_ctor_get(v___x_778_, 0);
lean_inc(v_a_779_);
lean_dec_ref_known(v___x_778_, 1);
v___x_780_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2___redArg(v_a_779_, v_a_720_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_808_; 
v_a_781_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_808_ == 0)
{
v___x_783_ = v___x_780_;
v_isShared_784_ = v_isSharedCheck_808_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_780_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_808_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_785_; lean_object* v_decls_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v_cache_789_; lean_object* v_cacheClosed_790_; lean_object* v_hasLetCache_791_; lean_object* v_decls_792_; lean_object* v_valueMap_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_807_; 
v___x_785_ = lean_st_ref_get(v_a_718_);
v_decls_786_ = lean_ctor_get(v___x_785_, 3);
lean_inc_ref(v_decls_786_);
lean_dec(v___x_785_);
v___x_787_ = lean_array_get_size(v_decls_786_);
lean_dec_ref(v_decls_786_);
v___x_788_ = lean_st_ref_take(v_a_718_);
v_cache_789_ = lean_ctor_get(v___x_788_, 0);
v_cacheClosed_790_ = lean_ctor_get(v___x_788_, 1);
v_hasLetCache_791_ = lean_ctor_get(v___x_788_, 2);
v_decls_792_ = lean_ctor_get(v___x_788_, 3);
v_valueMap_793_ = lean_ctor_get(v___x_788_, 4);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_807_ == 0)
{
v___x_795_ = v___x_788_;
v_isShared_796_ = v_isSharedCheck_807_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_valueMap_793_);
lean_inc(v_decls_792_);
lean_inc(v_hasLetCache_791_);
lean_inc(v_cacheClosed_790_);
lean_inc(v_cache_789_);
lean_dec(v___x_788_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_807_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_801_; 
lean_inc(v_a_781_);
v___x_797_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_797_, 0, v_a_781_);
lean_ctor_set(v___x_797_, 1, v_userName_714_);
lean_ctor_set(v___x_797_, 2, v_type_715_);
lean_ctor_set(v___x_797_, 3, v_value_716_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*4, v_nondep_717_);
v___x_798_ = lean_array_push(v_decls_792_, v___x_797_);
v___x_799_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3___redArg(v_valueMap_793_, v_key_727_, v___x_787_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 4, v___x_799_);
lean_ctor_set(v___x_795_, 3, v___x_798_);
v___x_801_ = v___x_795_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_cache_789_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v_cacheClosed_790_);
lean_ctor_set(v_reuseFailAlloc_806_, 2, v_hasLetCache_791_);
lean_ctor_set(v_reuseFailAlloc_806_, 3, v___x_798_);
lean_ctor_set(v_reuseFailAlloc_806_, 4, v___x_799_);
v___x_801_ = v_reuseFailAlloc_806_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
lean_object* v___x_802_; lean_object* v___x_804_; 
v___x_802_ = lean_st_ref_put(v_a_718_, v___x_801_);
if (v_isShared_784_ == 0)
{
v___x_804_ = v___x_783_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_781_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_727_, 2);
lean_dec_ref(v_value_716_);
lean_dec_ref(v_type_715_);
lean_dec(v_userName_714_);
return v___x_780_;
}
}
else
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
lean_dec_ref_known(v_key_727_, 2);
lean_dec_ref(v_value_716_);
lean_dec_ref(v_type_715_);
lean_dec(v_userName_714_);
v_a_809_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v___x_778_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_778_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_809_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_userName_714_ = stack[0].m_obj;
lean_object* v_type_715_ = stack[1].m_obj;
lean_object* v_value_716_ = stack[2].m_obj;
uint8_t v_nondep_717_ = stack[3].m_num;
lean_object* v_a_718_ = stack[4].m_obj;
lean_object* v_a_719_ = stack[5].m_obj;
lean_object* v_a_720_ = stack[6].m_obj;
lean_object* v_a_721_ = stack[7].m_obj;
lean_object* v_a_722_ = stack[8].m_obj;
lean_object* v_a_723_ = stack[9].m_obj;
lean_object* v_a_724_ = stack[10].m_obj;
lean_object* v_res_817_;
v_res_817_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl(v_userName_714_, v_type_715_, v_value_716_, v_nondep_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_);
stack->m_obj
 = v_res_817_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl___boxed(lean_object* v_userName_818_, lean_object* v_type_819_, lean_object* v_value_820_, lean_object* v_nondep_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_){
_start:
{
uint8_t v_nondep_boxed_830_; lean_object* v_res_831_; 
v_nondep_boxed_830_ = lean_unbox(v_nondep_821_);
v_res_831_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl(v_userName_818_, v_type_819_, v_value_820_, v_nondep_boxed_830_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
lean_dec(v_a_828_);
lean_dec_ref(v_a_827_);
lean_dec(v_a_826_);
lean_dec_ref(v_a_825_);
lean_dec(v_a_824_);
lean_dec_ref(v_a_823_);
lean_dec(v_a_822_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0(lean_object* v_00_u03b2_832_, lean_object* v_m_833_, lean_object* v_a_834_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0___redArg(v_m_833_, v_a_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0___boxed(lean_object* v_00_u03b2_836_, lean_object* v_m_837_, lean_object* v_a_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0(v_00_u03b2_836_, v_m_837_, v_a_838_);
lean_dec_ref(v_a_838_);
lean_dec_ref(v_m_837_);
return v_res_839_;
}
}
lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2(lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2___redArg(v___y_846_);
return v___x_848_;
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_840_ = stack[0].m_obj;
lean_object* v___y_841_ = stack[1].m_obj;
lean_object* v___y_842_ = stack[2].m_obj;
lean_object* v___y_843_ = stack[3].m_obj;
lean_object* v___y_844_ = stack[4].m_obj;
lean_object* v___y_845_ = stack[5].m_obj;
lean_object* v___y_846_ = stack[6].m_obj;
lean_object* v_res_849_;
v_res_849_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2(v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
stack->m_obj
 = v_res_849_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2___boxed(lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2(v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3(lean_object* v_00_u03b2_859_, lean_object* v_m_860_, lean_object* v_a_861_, lean_object* v_b_862_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3___redArg(v_m_860_, v_a_861_, v_b_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0(lean_object* v_00_u03b2_864_, lean_object* v_a_865_, lean_object* v_x_866_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0___redArg(v_a_865_, v_x_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_868_, lean_object* v_a_869_, lean_object* v_x_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0(v_00_u03b2_868_, v_a_869_, v_x_870_);
lean_dec(v_x_870_);
lean_dec_ref(v_a_869_);
return v_res_871_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5(lean_object* v_00_u03b2_872_, lean_object* v_a_873_, lean_object* v_x_874_){
_start:
{
uint8_t v___x_875_; 
v___x_875_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5___redArg(v_a_873_, v_x_874_);
return v___x_875_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_873_ = stack[1].m_obj;
lean_object* v_x_874_ = stack[2].m_obj;
uint8_t v_res_876_;
v_res_876_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5(lean_box(0), v_a_873_, v_x_874_);
stack->m_num = v_res_876_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5___boxed(lean_object* v_00_u03b2_877_, lean_object* v_a_878_, lean_object* v_x_879_){
_start:
{
uint8_t v_res_880_; lean_object* v_r_881_; 
v_res_880_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5(v_00_u03b2_877_, v_a_878_, v_x_879_);
lean_dec(v_x_879_);
lean_dec_ref(v_a_878_);
v_r_881_ = lean_box(v_res_880_);
return v_r_881_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6(lean_object* v_00_u03b2_882_, lean_object* v_data_883_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6___redArg(v_data_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__7(lean_object* v_00_u03b2_885_, lean_object* v_a_886_, lean_object* v_b_887_, lean_object* v_x_888_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__7___redArg(v_a_886_, v_b_887_, v_x_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6_spec__7(lean_object* v_00_u03b2_890_, lean_object* v_i_891_, lean_object* v_source_892_, lean_object* v_target_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6_spec__7___redArg(v_i_891_, v_source_892_, v_target_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6_spec__7_spec__8(lean_object* v_00_u03b2_895_, lean_object* v_x_896_, lean_object* v_x_897_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6_spec__7_spec__8___redArg(v_x_896_, v_x_897_);
return v___x_898_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1___closed__0(void){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = l_Lean_Meta_Sym_instInhabitedSymM___redArg();
return v___x_899_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1(lean_object* v_msg_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v___x_908_; lean_object* v___x_2263__overap_909_; lean_object* v___x_910_; 
v___x_908_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1___closed__0);
v___x_2263__overap_909_ = lean_panic_fn_borrowed(v___x_908_, v_msg_900_);
lean_inc(v___y_906_);
lean_inc_ref(v___y_905_);
lean_inc(v___y_904_);
lean_inc_ref(v___y_903_);
lean_inc(v___y_902_);
lean_inc_ref(v___y_901_);
v___x_910_ = lean_apply_7(v___x_2263__overap_909_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, lean_box(0));
return v___x_910_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_900_ = stack[0].m_obj;
lean_object* v___y_901_ = stack[1].m_obj;
lean_object* v___y_902_ = stack[2].m_obj;
lean_object* v___y_903_ = stack[3].m_obj;
lean_object* v___y_904_ = stack[4].m_obj;
lean_object* v___y_905_ = stack[5].m_obj;
lean_object* v___y_906_ = stack[6].m_obj;
lean_object* v_res_911_;
v_res_911_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1(v_msg_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
stack->m_obj
 = v_res_911_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1___boxed(lean_object* v_msg_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1(v_msg_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
return v_res_920_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__2(lean_object* v_x_921_, uint8_t v_bi_922_, lean_object* v_t_923_, lean_object* v_b_924_, lean_object* v___y_925_, uint8_t v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v___y_930_; lean_object* v___y_931_; 
if (v___y_926_ == 0)
{
v___y_930_ = v___y_925_;
v___y_931_ = v___y_928_;
goto v___jp_929_;
}
else
{
lean_object* v___x_953_; 
v___x_953_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_923_, v___y_926_, v___y_927_, v___y_928_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; lean_object* v___x_955_; 
v_a_954_ = lean_ctor_get(v___x_953_, 1);
lean_inc(v_a_954_);
lean_dec_ref_known(v___x_953_, 2);
v___x_955_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_924_, v___y_926_, v___y_927_, v_a_954_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v_a_956_; 
v_a_956_ = lean_ctor_get(v___x_955_, 1);
lean_inc(v_a_956_);
lean_dec_ref_known(v___x_955_, 2);
v___y_930_ = v___y_925_;
v___y_931_ = v_a_956_;
goto v___jp_929_;
}
else
{
lean_object* v_a_957_; lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
lean_dec_ref(v___y_925_);
lean_dec_ref(v_b_924_);
lean_dec_ref(v_t_923_);
lean_dec(v_x_921_);
v_a_957_ = lean_ctor_get(v___x_955_, 0);
v_a_958_ = lean_ctor_get(v___x_955_, 1);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_955_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_inc(v_a_957_);
lean_dec(v___x_955_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_957_);
lean_ctor_set(v_reuseFailAlloc_964_, 1, v_a_958_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
else
{
lean_object* v_a_966_; lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
lean_dec_ref(v___y_925_);
lean_dec_ref(v_b_924_);
lean_dec_ref(v_t_923_);
lean_dec(v_x_921_);
v_a_966_ = lean_ctor_get(v___x_953_, 0);
v_a_967_ = lean_ctor_get(v___x_953_, 1);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_953_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_inc(v_a_966_);
lean_dec(v___x_953_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_966_);
lean_ctor_set(v_reuseFailAlloc_973_, 1, v_a_967_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
v___jp_929_:
{
lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_932_ = l_Lean_Expr_lam___override(v_x_921_, v_t_923_, v_b_924_, v_bi_922_);
v___x_933_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_932_, v___y_931_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v_a_934_; lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_943_; 
v_a_934_ = lean_ctor_get(v___x_933_, 0);
v_a_935_ = lean_ctor_get(v___x_933_, 1);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_943_ == 0)
{
v___x_937_ = v___x_933_;
v_isShared_938_ = v_isSharedCheck_943_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_inc(v_a_934_);
lean_dec(v___x_933_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_943_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_939_; lean_object* v___x_941_; 
v___x_939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_939_, 0, v_a_934_);
lean_ctor_set(v___x_939_, 1, v___y_930_);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 0, v___x_939_);
v___x_941_ = v___x_937_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v___x_939_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v_a_935_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
else
{
lean_object* v_a_944_; lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_952_; 
lean_dec_ref(v___y_930_);
v_a_944_ = lean_ctor_get(v___x_933_, 0);
v_a_945_ = lean_ctor_get(v___x_933_, 1);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_952_ == 0)
{
v___x_947_ = v___x_933_;
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_inc(v_a_944_);
lean_dec(v___x_933_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_948_ == 0)
{
v___x_950_ = v___x_947_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_a_944_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_a_945_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_921_ = stack[0].m_obj;
uint8_t v_bi_922_ = stack[1].m_num;
lean_object* v_t_923_ = stack[2].m_obj;
lean_object* v_b_924_ = stack[3].m_obj;
lean_object* v___y_925_ = stack[4].m_obj;
uint8_t v___y_926_ = stack[5].m_num;
lean_object* v___y_927_ = stack[6].m_obj;
lean_object* v___y_928_ = stack[7].m_obj;
lean_object* v_res_975_;
v_res_975_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__2(v_x_921_, v_bi_922_, v_t_923_, v_b_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
stack->m_obj
 = v_res_975_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__2___boxed(lean_object* v_x_976_, lean_object* v_bi_977_, lean_object* v_t_978_, lean_object* v_b_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
uint8_t v_bi_boxed_984_; uint8_t v___y_25292__boxed_985_; lean_object* v_res_986_; 
v_bi_boxed_984_ = lean_unbox(v_bi_977_);
v___y_25292__boxed_985_ = lean_unbox(v___y_981_);
v_res_986_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__2(v_x_976_, v_bi_boxed_984_, v_t_978_, v_b_979_, v___y_980_, v___y_25292__boxed_985_, v___y_982_, v___y_983_);
lean_dec_ref(v___y_982_);
return v_res_986_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__6(lean_object* v_structName_987_, lean_object* v_idx_988_, lean_object* v_struct_989_, lean_object* v___y_990_, uint8_t v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v___y_995_; lean_object* v___y_996_; 
if (v___y_991_ == 0)
{
v___y_995_ = v___y_990_;
v___y_996_ = v___y_993_;
goto v___jp_994_;
}
else
{
lean_object* v___x_1018_; 
v___x_1018_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_struct_989_, v___y_991_, v___y_992_, v___y_993_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 1);
lean_inc(v_a_1019_);
lean_dec_ref_known(v___x_1018_, 2);
v___y_995_ = v___y_990_;
v___y_996_ = v_a_1019_;
goto v___jp_994_;
}
else
{
lean_object* v_a_1020_; lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1028_; 
lean_dec_ref(v___y_990_);
lean_dec_ref(v_struct_989_);
lean_dec(v_idx_988_);
lean_dec(v_structName_987_);
v_a_1020_ = lean_ctor_get(v___x_1018_, 0);
v_a_1021_ = lean_ctor_get(v___x_1018_, 1);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1023_ = v___x_1018_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_inc(v_a_1020_);
lean_dec(v___x_1018_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1020_);
lean_ctor_set(v_reuseFailAlloc_1027_, 1, v_a_1021_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
v___jp_994_:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = l_Lean_Expr_proj___override(v_structName_987_, v_idx_988_, v_struct_989_);
v___x_998_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_997_, v___y_996_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1008_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
v_a_1000_ = lean_ctor_get(v___x_998_, 1);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1002_ = v___x_998_;
v_isShared_1003_ = v_isSharedCheck_1008_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_inc(v_a_999_);
lean_dec(v___x_998_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1008_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1004_; lean_object* v___x_1006_; 
v___x_1004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1004_, 0, v_a_999_);
lean_ctor_set(v___x_1004_, 1, v___y_995_);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 0, v___x_1004_);
v___x_1006_ = v___x_1002_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_1004_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v_a_1000_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
else
{
lean_object* v_a_1009_; lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
lean_dec_ref(v___y_995_);
v_a_1009_ = lean_ctor_get(v___x_998_, 0);
v_a_1010_ = lean_ctor_get(v___x_998_, 1);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_998_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_inc(v_a_1009_);
lean_dec(v___x_998_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1009_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v_a_1010_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_structName_987_ = stack[0].m_obj;
lean_object* v_idx_988_ = stack[1].m_obj;
lean_object* v_struct_989_ = stack[2].m_obj;
lean_object* v___y_990_ = stack[3].m_obj;
uint8_t v___y_991_ = stack[4].m_num;
lean_object* v___y_992_ = stack[5].m_obj;
lean_object* v___y_993_ = stack[6].m_obj;
lean_object* v_res_1029_;
v_res_1029_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__6(v_structName_987_, v_idx_988_, v_struct_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
stack->m_obj
 = v_res_1029_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__6___boxed(lean_object* v_structName_1030_, lean_object* v_idx_1031_, lean_object* v_struct_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
uint8_t v___y_25452__boxed_1037_; lean_object* v_res_1038_; 
v___y_25452__boxed_1037_ = lean_unbox(v___y_1034_);
v_res_1038_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__6(v_structName_1030_, v_idx_1031_, v_struct_1032_, v___y_1033_, v___y_25452__boxed_1037_, v___y_1035_, v___y_1036_);
lean_dec_ref(v___y_1035_);
return v_res_1038_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__1(lean_object* v_f_1039_, lean_object* v_a_1040_, lean_object* v___y_1041_, uint8_t v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v___y_1046_; lean_object* v___y_1047_; 
if (v___y_1042_ == 0)
{
v___y_1046_ = v___y_1041_;
v___y_1047_ = v___y_1044_;
goto v___jp_1045_;
}
else
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_1039_, v___y_1042_, v___y_1043_, v___y_1044_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v___x_1071_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 1);
lean_inc(v_a_1070_);
lean_dec_ref_known(v___x_1069_, 2);
v___x_1071_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_1040_, v___y_1042_, v___y_1043_, v_a_1070_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 1);
lean_inc(v_a_1072_);
lean_dec_ref_known(v___x_1071_, 2);
v___y_1046_ = v___y_1041_;
v___y_1047_ = v_a_1072_;
goto v___jp_1045_;
}
else
{
lean_object* v_a_1073_; lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1081_; 
lean_dec_ref(v___y_1041_);
lean_dec_ref(v_a_1040_);
lean_dec_ref(v_f_1039_);
v_a_1073_ = lean_ctor_get(v___x_1071_, 0);
v_a_1074_ = lean_ctor_get(v___x_1071_, 1);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1076_ = v___x_1071_;
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_inc(v_a_1073_);
lean_dec(v___x_1071_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1077_ == 0)
{
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_a_1073_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v_a_1074_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
}
else
{
lean_object* v_a_1082_; lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
lean_dec_ref(v___y_1041_);
lean_dec_ref(v_a_1040_);
lean_dec_ref(v_f_1039_);
v_a_1082_ = lean_ctor_get(v___x_1069_, 0);
v_a_1083_ = lean_ctor_get(v___x_1069_, 1);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1085_ = v___x_1069_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_inc(v_a_1082_);
lean_dec(v___x_1069_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1082_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v_a_1083_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
v___jp_1045_:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = l_Lean_Expr_app___override(v_f_1039_, v_a_1040_);
v___x_1049_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1048_, v___y_1047_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v_a_1050_; lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1059_; 
v_a_1050_ = lean_ctor_get(v___x_1049_, 0);
v_a_1051_ = lean_ctor_get(v___x_1049_, 1);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1053_ = v___x_1049_;
v_isShared_1054_ = v_isSharedCheck_1059_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_inc(v_a_1050_);
lean_dec(v___x_1049_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1059_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1055_; lean_object* v___x_1057_; 
v___x_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1055_, 0, v_a_1050_);
lean_ctor_set(v___x_1055_, 1, v___y_1046_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 0, v___x_1055_);
v___x_1057_ = v___x_1053_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1055_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v_a_1051_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
else
{
lean_object* v_a_1060_; lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
lean_dec_ref(v___y_1046_);
v_a_1060_ = lean_ctor_get(v___x_1049_, 0);
v_a_1061_ = lean_ctor_get(v___x_1049_, 1);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1063_ = v___x_1049_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_inc(v_a_1060_);
lean_dec(v___x_1049_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1060_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v_a_1061_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1039_ = stack[0].m_obj;
lean_object* v_a_1040_ = stack[1].m_obj;
lean_object* v___y_1041_ = stack[2].m_obj;
uint8_t v___y_1042_ = stack[3].m_num;
lean_object* v___y_1043_ = stack[4].m_obj;
lean_object* v___y_1044_ = stack[5].m_obj;
lean_object* v_res_1091_;
v_res_1091_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__1(v_f_1039_, v_a_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
stack->m_obj
 = v_res_1091_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__1___boxed(lean_object* v_f_1092_, lean_object* v_a_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
uint8_t v___y_25578__boxed_1098_; lean_object* v_res_1099_; 
v___y_25578__boxed_1098_ = lean_unbox(v___y_1095_);
v_res_1099_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__1(v_f_1092_, v_a_1093_, v___y_1094_, v___y_25578__boxed_1098_, v___y_1096_, v___y_1097_);
lean_dec_ref(v___y_1096_);
return v_res_1099_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4(lean_object* v_x_1100_, lean_object* v_t_1101_, lean_object* v_v_1102_, lean_object* v_b_1103_, uint8_t v_nondep_1104_, lean_object* v___y_1105_, uint8_t v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v___y_1110_; lean_object* v___y_1111_; 
if (v___y_1106_ == 0)
{
v___y_1110_ = v___y_1105_;
v___y_1111_ = v___y_1108_;
goto v___jp_1109_;
}
else
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_1101_, v___y_1106_, v___y_1107_, v___y_1108_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v_a_1134_; lean_object* v___x_1135_; 
v_a_1134_ = lean_ctor_get(v___x_1133_, 1);
lean_inc(v_a_1134_);
lean_dec_ref_known(v___x_1133_, 2);
v___x_1135_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_v_1102_, v___y_1106_, v___y_1107_, v_a_1134_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; lean_object* v___x_1137_; 
v_a_1136_ = lean_ctor_get(v___x_1135_, 1);
lean_inc(v_a_1136_);
lean_dec_ref_known(v___x_1135_, 2);
v___x_1137_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_1103_, v___y_1106_, v___y_1107_, v_a_1136_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1138_; 
v_a_1138_ = lean_ctor_get(v___x_1137_, 1);
lean_inc(v_a_1138_);
lean_dec_ref_known(v___x_1137_, 2);
v___y_1110_ = v___y_1105_;
v___y_1111_ = v_a_1138_;
goto v___jp_1109_;
}
else
{
lean_object* v_a_1139_; lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
lean_dec_ref(v___y_1105_);
lean_dec_ref(v_b_1103_);
lean_dec_ref(v_v_1102_);
lean_dec_ref(v_t_1101_);
lean_dec(v_x_1100_);
v_a_1139_ = lean_ctor_get(v___x_1137_, 0);
v_a_1140_ = lean_ctor_get(v___x_1137_, 1);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1142_ = v___x_1137_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_inc(v_a_1139_);
lean_dec(v___x_1137_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1139_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v_a_1140_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
else
{
lean_object* v_a_1148_; lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1156_; 
lean_dec_ref(v___y_1105_);
lean_dec_ref(v_b_1103_);
lean_dec_ref(v_v_1102_);
lean_dec_ref(v_t_1101_);
lean_dec(v_x_1100_);
v_a_1148_ = lean_ctor_get(v___x_1135_, 0);
v_a_1149_ = lean_ctor_get(v___x_1135_, 1);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1151_ = v___x_1135_;
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_inc(v_a_1148_);
lean_dec(v___x_1135_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1154_; 
if (v_isShared_1152_ == 0)
{
v___x_1154_ = v___x_1151_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1148_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v_a_1149_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
else
{
lean_object* v_a_1157_; lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
lean_dec_ref(v___y_1105_);
lean_dec_ref(v_b_1103_);
lean_dec_ref(v_v_1102_);
lean_dec_ref(v_t_1101_);
lean_dec(v_x_1100_);
v_a_1157_ = lean_ctor_get(v___x_1133_, 0);
v_a_1158_ = lean_ctor_get(v___x_1133_, 1);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1133_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_inc(v_a_1157_);
lean_dec(v___x_1133_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1157_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v_a_1158_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
v___jp_1109_:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = l_Lean_Expr_letE___override(v_x_1100_, v_t_1101_, v_v_1102_, v_b_1103_, v_nondep_1104_);
v___x_1113_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1112_, v___y_1111_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_object* v_a_1114_; lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1123_; 
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
v_a_1115_ = lean_ctor_get(v___x_1113_, 1);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1117_ = v___x_1113_;
v_isShared_1118_ = v_isSharedCheck_1123_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_inc(v_a_1114_);
lean_dec(v___x_1113_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1123_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1119_; lean_object* v___x_1121_; 
v___x_1119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1119_, 0, v_a_1114_);
lean_ctor_set(v___x_1119_, 1, v___y_1110_);
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 0, v___x_1119_);
v___x_1121_ = v___x_1117_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1119_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v_a_1115_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
else
{
lean_object* v_a_1124_; lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1132_; 
lean_dec_ref(v___y_1110_);
v_a_1124_ = lean_ctor_get(v___x_1113_, 0);
v_a_1125_ = lean_ctor_get(v___x_1113_, 1);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1127_ = v___x_1113_;
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_inc(v_a_1124_);
lean_dec(v___x_1113_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_a_1124_);
lean_ctor_set(v_reuseFailAlloc_1131_, 1, v_a_1125_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1100_ = stack[0].m_obj;
lean_object* v_t_1101_ = stack[1].m_obj;
lean_object* v_v_1102_ = stack[2].m_obj;
lean_object* v_b_1103_ = stack[3].m_obj;
uint8_t v_nondep_1104_ = stack[4].m_num;
lean_object* v___y_1105_ = stack[5].m_obj;
uint8_t v___y_1106_ = stack[6].m_num;
lean_object* v___y_1107_ = stack[7].m_obj;
lean_object* v___y_1108_ = stack[8].m_obj;
lean_object* v_res_1166_;
v_res_1166_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4(v_x_1100_, v_t_1101_, v_v_1102_, v_b_1103_, v_nondep_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
stack->m_obj
 = v_res_1166_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4___boxed(lean_object* v_x_1167_, lean_object* v_t_1168_, lean_object* v_v_1169_, lean_object* v_b_1170_, lean_object* v_nondep_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
uint8_t v_nondep_boxed_1176_; uint8_t v___y_25738__boxed_1177_; lean_object* v_res_1178_; 
v_nondep_boxed_1176_ = lean_unbox(v_nondep_1171_);
v___y_25738__boxed_1177_ = lean_unbox(v___y_1173_);
v_res_1178_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4(v_x_1167_, v_t_1168_, v_v_1169_, v_b_1170_, v_nondep_boxed_1176_, v___y_1172_, v___y_25738__boxed_1177_, v___y_1174_, v___y_1175_);
lean_dec_ref(v___y_1174_);
return v_res_1178_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7(lean_object* v_msg_1186_, lean_object* v___y_1187_, uint8_t v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v___f_1191_; lean_object* v___f_1192_; lean_object* v___f_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___f_1203_; lean_object* v___f_1204_; lean_object* v___f_1205_; lean_object* v___f_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_24789__overap_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___f_1191_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__0));
v___f_1192_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__1));
v___f_1193_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__2));
v___x_1194_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__3));
v___x_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1194_);
lean_ctor_set(v___x_1195_, 1, v___f_1191_);
v___x_1196_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__4));
v___x_1197_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__5));
v___x_1198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1195_);
lean_ctor_set(v___x_1198_, 1, v___x_1196_);
lean_ctor_set(v___x_1198_, 2, v___f_1192_);
lean_ctor_set(v___x_1198_, 3, v___f_1193_);
lean_ctor_set(v___x_1198_, 4, v___x_1197_);
v___x_1199_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__6));
v___x_1200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1198_);
lean_ctor_set(v___x_1200_, 1, v___x_1199_);
v___x_1201_ = l_ReaderT_instMonad___redArg(v___x_1200_);
v___x_1202_ = l_ReaderT_instMonad___redArg(v___x_1201_);
lean_inc_ref_n(v___x_1202_, 6);
v___f_1203_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1203_, 0, v___x_1202_);
v___f_1204_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1204_, 0, v___x_1202_);
v___f_1205_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_1205_, 0, v___x_1202_);
v___f_1206_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_1206_, 0, v___x_1202_);
v___x_1207_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_1207_, 0, lean_box(0));
lean_closure_set(v___x_1207_, 1, lean_box(0));
lean_closure_set(v___x_1207_, 2, v___x_1202_);
v___x_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
lean_ctor_set(v___x_1208_, 1, v___f_1203_);
v___x_1209_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_1209_, 0, lean_box(0));
lean_closure_set(v___x_1209_, 1, lean_box(0));
lean_closure_set(v___x_1209_, 2, v___x_1202_);
v___x_1210_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1208_);
lean_ctor_set(v___x_1210_, 1, v___x_1209_);
lean_ctor_set(v___x_1210_, 2, v___f_1204_);
lean_ctor_set(v___x_1210_, 3, v___f_1205_);
lean_ctor_set(v___x_1210_, 4, v___f_1206_);
v___x_1211_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_1211_, 0, lean_box(0));
lean_closure_set(v___x_1211_, 1, lean_box(0));
lean_closure_set(v___x_1211_, 2, v___x_1202_);
v___x_1212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1210_);
lean_ctor_set(v___x_1212_, 1, v___x_1211_);
v___x_1213_ = l_Lean_instInhabitedExpr;
v___x_1214_ = l_instInhabitedOfMonad___redArg(v___x_1212_, v___x_1213_);
v___x_24789__overap_1215_ = lean_panic_fn_borrowed(v___x_1214_, v_msg_1186_);
lean_dec(v___x_1214_);
v___x_1216_ = lean_box(v___y_1188_);
lean_inc_ref(v___y_1189_);
v___x_1217_ = lean_apply_4(v___x_24789__overap_1215_, v___y_1187_, v___x_1216_, v___y_1189_, v___y_1190_);
return v___x_1217_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1186_ = stack[0].m_obj;
lean_object* v___y_1187_ = stack[1].m_obj;
uint8_t v___y_1188_ = stack[2].m_num;
lean_object* v___y_1189_ = stack[3].m_obj;
lean_object* v___y_1190_ = stack[4].m_obj;
lean_object* v_res_1218_;
v_res_1218_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7(v_msg_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
stack->m_obj
 = v_res_1218_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___boxed(lean_object* v_msg_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
uint8_t v___y_25946__boxed_1224_; lean_object* v_res_1225_; 
v___y_25946__boxed_1224_ = lean_unbox(v___y_1221_);
v_res_1225_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7(v_msg_1219_, v___y_1220_, v___y_25946__boxed_1224_, v___y_1222_, v___y_1223_);
lean_dec_ref(v___y_1222_);
return v_res_1225_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__5(lean_object* v_d_1226_, lean_object* v_e_1227_, lean_object* v___y_1228_, uint8_t v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v___y_1233_; lean_object* v___y_1234_; 
if (v___y_1229_ == 0)
{
v___y_1233_ = v___y_1228_;
v___y_1234_ = v___y_1231_;
goto v___jp_1232_;
}
else
{
lean_object* v___x_1256_; 
v___x_1256_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_1227_, v___y_1229_, v___y_1230_, v___y_1231_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_a_1257_; 
v_a_1257_ = lean_ctor_get(v___x_1256_, 1);
lean_inc(v_a_1257_);
lean_dec_ref_known(v___x_1256_, 2);
v___y_1233_ = v___y_1228_;
v___y_1234_ = v_a_1257_;
goto v___jp_1232_;
}
else
{
lean_object* v_a_1258_; lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
lean_dec_ref(v___y_1228_);
lean_dec_ref(v_e_1227_);
lean_dec(v_d_1226_);
v_a_1258_ = lean_ctor_get(v___x_1256_, 0);
v_a_1259_ = lean_ctor_get(v___x_1256_, 1);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1261_ = v___x_1256_;
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_inc(v_a_1258_);
lean_dec(v___x_1256_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_a_1258_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v_a_1259_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
}
v___jp_1232_:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = l_Lean_Expr_mdata___override(v_d_1226_, v_e_1227_);
v___x_1236_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1235_, v___y_1234_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v_a_1237_; lean_object* v_a_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1246_; 
v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
v_a_1238_ = lean_ctor_get(v___x_1236_, 1);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1240_ = v___x_1236_;
v_isShared_1241_ = v_isSharedCheck_1246_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_a_1238_);
lean_inc(v_a_1237_);
lean_dec(v___x_1236_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1246_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1242_; lean_object* v___x_1244_; 
v___x_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1242_, 0, v_a_1237_);
lean_ctor_set(v___x_1242_, 1, v___y_1233_);
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 0, v___x_1242_);
v___x_1244_ = v___x_1240_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v___x_1242_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v_a_1238_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
else
{
lean_object* v_a_1247_; lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1255_; 
lean_dec_ref(v___y_1233_);
v_a_1247_ = lean_ctor_get(v___x_1236_, 0);
v_a_1248_ = lean_ctor_get(v___x_1236_, 1);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1250_ = v___x_1236_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_inc(v_a_1247_);
lean_dec(v___x_1236_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1247_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v_a_1248_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_1226_ = stack[0].m_obj;
lean_object* v_e_1227_ = stack[1].m_obj;
lean_object* v___y_1228_ = stack[2].m_obj;
uint8_t v___y_1229_ = stack[3].m_num;
lean_object* v___y_1230_ = stack[4].m_obj;
lean_object* v___y_1231_ = stack[5].m_obj;
lean_object* v_res_1267_;
v_res_1267_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__5(v_d_1226_, v_e_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
stack->m_obj
 = v_res_1267_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__5___boxed(lean_object* v_d_1268_, lean_object* v_e_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
uint8_t v___y_26058__boxed_1274_; lean_object* v_res_1275_; 
v___y_26058__boxed_1274_ = lean_unbox(v___y_1271_);
v_res_1275_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__5(v_d_1268_, v_e_1269_, v___y_1270_, v___y_26058__boxed_1274_, v___y_1272_, v___y_1273_);
lean_dec_ref(v___y_1272_);
return v_res_1275_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__3(lean_object* v_x_1276_, uint8_t v_bi_1277_, lean_object* v_t_1278_, lean_object* v_b_1279_, lean_object* v___y_1280_, uint8_t v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
lean_object* v___y_1285_; lean_object* v___y_1286_; 
if (v___y_1281_ == 0)
{
v___y_1285_ = v___y_1280_;
v___y_1286_ = v___y_1283_;
goto v___jp_1284_;
}
else
{
lean_object* v___x_1308_; 
v___x_1308_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_1278_, v___y_1281_, v___y_1282_, v___y_1283_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v_a_1309_; lean_object* v___x_1310_; 
v_a_1309_ = lean_ctor_get(v___x_1308_, 1);
lean_inc(v_a_1309_);
lean_dec_ref_known(v___x_1308_, 2);
v___x_1310_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_1279_, v___y_1281_, v___y_1282_, v_a_1309_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 1);
lean_inc(v_a_1311_);
lean_dec_ref_known(v___x_1310_, 2);
v___y_1285_ = v___y_1280_;
v___y_1286_ = v_a_1311_;
goto v___jp_1284_;
}
else
{
lean_object* v_a_1312_; lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1320_; 
lean_dec_ref(v___y_1280_);
lean_dec_ref(v_b_1279_);
lean_dec_ref(v_t_1278_);
lean_dec(v_x_1276_);
v_a_1312_ = lean_ctor_get(v___x_1310_, 0);
v_a_1313_ = lean_ctor_get(v___x_1310_, 1);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1315_ = v___x_1310_;
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_inc(v_a_1312_);
lean_dec(v___x_1310_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1312_);
lean_ctor_set(v_reuseFailAlloc_1319_, 1, v_a_1313_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
else
{
lean_object* v_a_1321_; lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1329_; 
lean_dec_ref(v___y_1280_);
lean_dec_ref(v_b_1279_);
lean_dec_ref(v_t_1278_);
lean_dec(v_x_1276_);
v_a_1321_ = lean_ctor_get(v___x_1308_, 0);
v_a_1322_ = lean_ctor_get(v___x_1308_, 1);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1324_ = v___x_1308_;
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_inc(v_a_1321_);
lean_dec(v___x_1308_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1327_; 
if (v_isShared_1325_ == 0)
{
v___x_1327_ = v___x_1324_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_a_1321_);
lean_ctor_set(v_reuseFailAlloc_1328_, 1, v_a_1322_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
}
v___jp_1284_:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = l_Lean_Expr_forallE___override(v_x_1276_, v_t_1278_, v_b_1279_, v_bi_1277_);
v___x_1288_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1287_, v___y_1286_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v_a_1289_; lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1298_; 
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
v_a_1290_ = lean_ctor_get(v___x_1288_, 1);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1292_ = v___x_1288_;
v_isShared_1293_ = v_isSharedCheck_1298_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_inc(v_a_1289_);
lean_dec(v___x_1288_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1298_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1294_; lean_object* v___x_1296_; 
v___x_1294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1294_, 0, v_a_1289_);
lean_ctor_set(v___x_1294_, 1, v___y_1285_);
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 0, v___x_1294_);
v___x_1296_ = v___x_1292_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v___x_1294_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v_a_1290_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
else
{
lean_object* v_a_1299_; lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
lean_dec_ref(v___y_1285_);
v_a_1299_ = lean_ctor_get(v___x_1288_, 0);
v_a_1300_ = lean_ctor_get(v___x_1288_, 1);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v___x_1288_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_inc(v_a_1299_);
lean_dec(v___x_1288_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_a_1299_);
lean_ctor_set(v_reuseFailAlloc_1306_, 1, v_a_1300_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1276_ = stack[0].m_obj;
uint8_t v_bi_1277_ = stack[1].m_num;
lean_object* v_t_1278_ = stack[2].m_obj;
lean_object* v_b_1279_ = stack[3].m_obj;
lean_object* v___y_1280_ = stack[4].m_obj;
uint8_t v___y_1281_ = stack[5].m_num;
lean_object* v___y_1282_ = stack[6].m_obj;
lean_object* v___y_1283_ = stack[7].m_obj;
lean_object* v_res_1330_;
v_res_1330_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__3(v_x_1276_, v_bi_1277_, v_t_1278_, v_b_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
stack->m_obj
 = v_res_1330_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__3___boxed(lean_object* v_x_1331_, lean_object* v_bi_1332_, lean_object* v_t_1333_, lean_object* v_b_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
uint8_t v_bi_boxed_1339_; uint8_t v___y_26184__boxed_1340_; lean_object* v_res_1341_; 
v_bi_boxed_1339_ = lean_unbox(v_bi_1332_);
v___y_26184__boxed_1340_ = lean_unbox(v___y_1336_);
v_res_1341_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__3(v_x_1331_, v_bi_boxed_1339_, v_t_1333_, v_b_1334_, v___y_1335_, v___y_26184__boxed_1340_, v___y_1337_, v___y_1338_);
lean_dec_ref(v___y_1337_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10___redArg(lean_object* v_a_1342_, lean_object* v_x_1343_){
_start:
{
if (lean_obj_tag(v_x_1343_) == 0)
{
lean_object* v___x_1344_; 
v___x_1344_ = lean_box(0);
return v___x_1344_;
}
else
{
lean_object* v_key_1345_; lean_object* v_value_1346_; lean_object* v_tail_1347_; lean_object* v_fst_1348_; lean_object* v_snd_1349_; lean_object* v_fst_1350_; lean_object* v_snd_1351_; size_t v___x_1352_; size_t v___x_1353_; uint8_t v___x_1354_; 
v_key_1345_ = lean_ctor_get(v_x_1343_, 0);
v_value_1346_ = lean_ctor_get(v_x_1343_, 1);
v_tail_1347_ = lean_ctor_get(v_x_1343_, 2);
v_fst_1348_ = lean_ctor_get(v_key_1345_, 0);
v_snd_1349_ = lean_ctor_get(v_key_1345_, 1);
v_fst_1350_ = lean_ctor_get(v_a_1342_, 0);
v_snd_1351_ = lean_ctor_get(v_a_1342_, 1);
v___x_1352_ = lean_ptr_addr(v_fst_1348_);
v___x_1353_ = lean_ptr_addr(v_fst_1350_);
v___x_1354_ = lean_usize_dec_eq(v___x_1352_, v___x_1353_);
if (v___x_1354_ == 0)
{
v_x_1343_ = v_tail_1347_;
goto _start;
}
else
{
uint8_t v___x_1356_; 
v___x_1356_ = lean_nat_dec_eq(v_snd_1349_, v_snd_1351_);
if (v___x_1356_ == 0)
{
v_x_1343_ = v_tail_1347_;
goto _start;
}
else
{
lean_object* v___x_1358_; 
lean_inc(v_value_1346_);
v___x_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1358_, 0, v_value_1346_);
return v___x_1358_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10___redArg___boxed(lean_object* v_a_1359_, lean_object* v_x_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10___redArg(v_a_1359_, v_x_1360_);
lean_dec(v_x_1360_);
lean_dec_ref(v_a_1359_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2___redArg(lean_object* v_m_1362_, lean_object* v_a_1363_){
_start:
{
lean_object* v_buckets_1364_; lean_object* v_fst_1365_; lean_object* v_snd_1366_; lean_object* v___x_1367_; size_t v___x_1368_; size_t v___x_1369_; size_t v___x_1370_; uint64_t v___x_1371_; uint64_t v___x_1372_; uint64_t v___x_1373_; uint64_t v___x_1374_; uint64_t v___x_1375_; uint64_t v_fold_1376_; uint64_t v___x_1377_; uint64_t v___x_1378_; uint64_t v___x_1379_; size_t v___x_1380_; size_t v___x_1381_; size_t v___x_1382_; size_t v___x_1383_; size_t v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v_buckets_1364_ = lean_ctor_get(v_m_1362_, 1);
v_fst_1365_ = lean_ctor_get(v_a_1363_, 0);
v_snd_1366_ = lean_ctor_get(v_a_1363_, 1);
v___x_1367_ = lean_array_get_size(v_buckets_1364_);
v___x_1368_ = lean_ptr_addr(v_fst_1365_);
v___x_1369_ = ((size_t)3ULL);
v___x_1370_ = lean_usize_shift_right(v___x_1368_, v___x_1369_);
v___x_1371_ = lean_usize_to_uint64(v___x_1370_);
v___x_1372_ = lean_uint64_of_nat(v_snd_1366_);
v___x_1373_ = lean_uint64_mix_hash(v___x_1371_, v___x_1372_);
v___x_1374_ = 32ULL;
v___x_1375_ = lean_uint64_shift_right(v___x_1373_, v___x_1374_);
v_fold_1376_ = lean_uint64_xor(v___x_1373_, v___x_1375_);
v___x_1377_ = 16ULL;
v___x_1378_ = lean_uint64_shift_right(v_fold_1376_, v___x_1377_);
v___x_1379_ = lean_uint64_xor(v_fold_1376_, v___x_1378_);
v___x_1380_ = lean_uint64_to_usize(v___x_1379_);
v___x_1381_ = lean_usize_of_nat(v___x_1367_);
v___x_1382_ = ((size_t)1ULL);
v___x_1383_ = lean_usize_sub(v___x_1381_, v___x_1382_);
v___x_1384_ = lean_usize_land(v___x_1380_, v___x_1383_);
v___x_1385_ = lean_array_uget_borrowed(v_buckets_1364_, v___x_1384_);
v___x_1386_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10___redArg(v_a_1363_, v___x_1385_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_m_1387_, lean_object* v_a_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2___redArg(v_m_1387_, v_a_1388_);
lean_dec_ref(v_a_1388_);
lean_dec_ref(v_m_1387_);
return v_res_1389_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1393_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__2));
v___x_1394_ = lean_unsigned_to_nat(67u);
v___x_1395_ = lean_unsigned_to_nat(35u);
v___x_1396_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__1));
v___x_1397_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__0));
v___x_1398_ = l_mkPanicMessageWithDecl(v___x_1397_, v___x_1396_, v___x_1395_, v___x_1394_, v___x_1393_);
return v___x_1398_;
}
}
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0(lean_object* v_n_1399_, lean_object* v_xs_1400_, lean_object* v_e_1401_, lean_object* v_offset_1402_, lean_object* v_a_1403_, uint8_t v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_){
_start:
{
switch(lean_obj_tag(v_e_1401_))
{
case 5:
{
lean_object* v_fn_1407_; lean_object* v_arg_1408_; lean_object* v___x_1409_; 
v_fn_1407_ = lean_ctor_get(v_e_1401_, 0);
v_arg_1408_ = lean_ctor_get(v_e_1401_, 1);
lean_inc(v_offset_1402_);
lean_inc_ref(v_fn_1407_);
v___x_1409_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1399_, v_xs_1400_, v_fn_1407_, v_offset_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v_a_1410_; lean_object* v_a_1411_; lean_object* v_fst_1412_; lean_object* v_snd_1413_; lean_object* v___x_1414_; 
v_a_1410_ = lean_ctor_get(v___x_1409_, 0);
lean_inc(v_a_1410_);
v_a_1411_ = lean_ctor_get(v___x_1409_, 1);
lean_inc(v_a_1411_);
lean_dec_ref_known(v___x_1409_, 2);
v_fst_1412_ = lean_ctor_get(v_a_1410_, 0);
lean_inc(v_fst_1412_);
v_snd_1413_ = lean_ctor_get(v_a_1410_, 1);
lean_inc(v_snd_1413_);
lean_dec(v_a_1410_);
lean_inc_ref(v_arg_1408_);
v___x_1414_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1399_, v_xs_1400_, v_arg_1408_, v_offset_1402_, v_snd_1413_, v_a_1404_, v_a_1405_, v_a_1411_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1415_; lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1440_; 
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
v_a_1416_ = lean_ctor_get(v___x_1414_, 1);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1418_ = v___x_1414_;
v_isShared_1419_ = v_isSharedCheck_1440_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_inc(v_a_1415_);
lean_dec(v___x_1414_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1440_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v_fst_1420_; lean_object* v_snd_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1439_; 
v_fst_1420_ = lean_ctor_get(v_a_1415_, 0);
v_snd_1421_ = lean_ctor_get(v_a_1415_, 1);
v_isSharedCheck_1439_ = !lean_is_exclusive(v_a_1415_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1423_ = v_a_1415_;
v_isShared_1424_ = v_isSharedCheck_1439_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_snd_1421_);
lean_inc(v_fst_1420_);
lean_dec(v_a_1415_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1439_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
size_t v___x_1425_; size_t v___x_1426_; uint8_t v___x_1427_; 
v___x_1425_ = lean_ptr_addr(v_fn_1407_);
v___x_1426_ = lean_ptr_addr(v_fst_1412_);
v___x_1427_ = lean_usize_dec_eq(v___x_1425_, v___x_1426_);
if (v___x_1427_ == 0)
{
lean_object* v___x_1428_; 
lean_del_object(v___x_1423_);
lean_del_object(v___x_1418_);
lean_dec_ref_known(v_e_1401_, 2);
v___x_1428_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__1(v_fst_1412_, v_fst_1420_, v_snd_1421_, v_a_1404_, v_a_1405_, v_a_1416_);
return v___x_1428_;
}
else
{
size_t v___x_1429_; size_t v___x_1430_; uint8_t v___x_1431_; 
v___x_1429_ = lean_ptr_addr(v_arg_1408_);
v___x_1430_ = lean_ptr_addr(v_fst_1420_);
v___x_1431_ = lean_usize_dec_eq(v___x_1429_, v___x_1430_);
if (v___x_1431_ == 0)
{
lean_object* v___x_1432_; 
lean_del_object(v___x_1423_);
lean_del_object(v___x_1418_);
lean_dec_ref_known(v_e_1401_, 2);
v___x_1432_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__1(v_fst_1412_, v_fst_1420_, v_snd_1421_, v_a_1404_, v_a_1405_, v_a_1416_);
return v___x_1432_;
}
else
{
lean_object* v___x_1434_; 
lean_dec(v_fst_1420_);
lean_dec(v_fst_1412_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 0, v_e_1401_);
v___x_1434_ = v___x_1423_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_e_1401_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v_snd_1421_);
v___x_1434_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
lean_object* v___x_1436_; 
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v___x_1434_);
v___x_1436_ = v___x_1418_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1434_);
lean_ctor_set(v_reuseFailAlloc_1437_, 1, v_a_1416_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1412_);
lean_dec_ref_known(v_e_1401_, 2);
return v___x_1414_;
}
}
else
{
lean_dec_ref_known(v_e_1401_, 2);
lean_dec(v_offset_1402_);
return v___x_1409_;
}
}
case 6:
{
lean_object* v_binderName_1441_; lean_object* v_binderType_1442_; lean_object* v_body_1443_; uint8_t v_binderInfo_1444_; lean_object* v___x_1445_; 
v_binderName_1441_ = lean_ctor_get(v_e_1401_, 0);
v_binderType_1442_ = lean_ctor_get(v_e_1401_, 1);
v_body_1443_ = lean_ctor_get(v_e_1401_, 2);
v_binderInfo_1444_ = lean_ctor_get_uint8(v_e_1401_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1402_);
lean_inc_ref(v_binderType_1442_);
v___x_1445_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1399_, v_xs_1400_, v_binderType_1442_, v_offset_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v_a_1446_; lean_object* v_a_1447_; lean_object* v_fst_1448_; lean_object* v_snd_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
v_a_1446_ = lean_ctor_get(v___x_1445_, 0);
lean_inc(v_a_1446_);
v_a_1447_ = lean_ctor_get(v___x_1445_, 1);
lean_inc(v_a_1447_);
lean_dec_ref_known(v___x_1445_, 2);
v_fst_1448_ = lean_ctor_get(v_a_1446_, 0);
lean_inc(v_fst_1448_);
v_snd_1449_ = lean_ctor_get(v_a_1446_, 1);
lean_inc(v_snd_1449_);
lean_dec(v_a_1446_);
v___x_1450_ = lean_unsigned_to_nat(1u);
v___x_1451_ = lean_nat_add(v_offset_1402_, v___x_1450_);
lean_dec(v_offset_1402_);
lean_inc_ref(v_body_1443_);
v___x_1452_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1399_, v_xs_1400_, v_body_1443_, v___x_1451_, v_snd_1449_, v_a_1404_, v_a_1405_, v_a_1447_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v_a_1453_; lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1478_; 
v_a_1453_ = lean_ctor_get(v___x_1452_, 0);
v_a_1454_ = lean_ctor_get(v___x_1452_, 1);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1456_ = v___x_1452_;
v_isShared_1457_ = v_isSharedCheck_1478_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_inc(v_a_1453_);
lean_dec(v___x_1452_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1478_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v_fst_1458_; lean_object* v_snd_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1477_; 
v_fst_1458_ = lean_ctor_get(v_a_1453_, 0);
v_snd_1459_ = lean_ctor_get(v_a_1453_, 1);
v_isSharedCheck_1477_ = !lean_is_exclusive(v_a_1453_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1461_ = v_a_1453_;
v_isShared_1462_ = v_isSharedCheck_1477_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_snd_1459_);
lean_inc(v_fst_1458_);
lean_dec(v_a_1453_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1477_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
size_t v___x_1463_; size_t v___x_1464_; uint8_t v___x_1465_; 
v___x_1463_ = lean_ptr_addr(v_binderType_1442_);
v___x_1464_ = lean_ptr_addr(v_fst_1448_);
v___x_1465_ = lean_usize_dec_eq(v___x_1463_, v___x_1464_);
if (v___x_1465_ == 0)
{
lean_object* v___x_1466_; 
lean_inc(v_binderName_1441_);
lean_del_object(v___x_1461_);
lean_del_object(v___x_1456_);
lean_dec_ref_known(v_e_1401_, 3);
v___x_1466_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__2(v_binderName_1441_, v_binderInfo_1444_, v_fst_1448_, v_fst_1458_, v_snd_1459_, v_a_1404_, v_a_1405_, v_a_1454_);
return v___x_1466_;
}
else
{
size_t v___x_1467_; size_t v___x_1468_; uint8_t v___x_1469_; 
v___x_1467_ = lean_ptr_addr(v_body_1443_);
v___x_1468_ = lean_ptr_addr(v_fst_1458_);
v___x_1469_ = lean_usize_dec_eq(v___x_1467_, v___x_1468_);
if (v___x_1469_ == 0)
{
lean_object* v___x_1470_; 
lean_inc(v_binderName_1441_);
lean_del_object(v___x_1461_);
lean_del_object(v___x_1456_);
lean_dec_ref_known(v_e_1401_, 3);
v___x_1470_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__2(v_binderName_1441_, v_binderInfo_1444_, v_fst_1448_, v_fst_1458_, v_snd_1459_, v_a_1404_, v_a_1405_, v_a_1454_);
return v___x_1470_;
}
else
{
lean_object* v___x_1472_; 
lean_dec(v_fst_1458_);
lean_dec(v_fst_1448_);
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 0, v_e_1401_);
v___x_1472_ = v___x_1461_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_e_1401_);
lean_ctor_set(v_reuseFailAlloc_1476_, 1, v_snd_1459_);
v___x_1472_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
lean_object* v___x_1474_; 
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 0, v___x_1472_);
v___x_1474_ = v___x_1456_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1472_);
lean_ctor_set(v_reuseFailAlloc_1475_, 1, v_a_1454_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1448_);
lean_dec_ref_known(v_e_1401_, 3);
return v___x_1452_;
}
}
else
{
lean_dec_ref_known(v_e_1401_, 3);
lean_dec(v_offset_1402_);
return v___x_1445_;
}
}
case 7:
{
lean_object* v_binderName_1479_; lean_object* v_binderType_1480_; lean_object* v_body_1481_; uint8_t v_binderInfo_1482_; lean_object* v___x_1483_; 
v_binderName_1479_ = lean_ctor_get(v_e_1401_, 0);
v_binderType_1480_ = lean_ctor_get(v_e_1401_, 1);
v_body_1481_ = lean_ctor_get(v_e_1401_, 2);
v_binderInfo_1482_ = lean_ctor_get_uint8(v_e_1401_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1402_);
lean_inc_ref(v_binderType_1480_);
v___x_1483_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1399_, v_xs_1400_, v_binderType_1480_, v_offset_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v_a_1484_; lean_object* v_a_1485_; lean_object* v_fst_1486_; lean_object* v_snd_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_a_1484_);
v_a_1485_ = lean_ctor_get(v___x_1483_, 1);
lean_inc(v_a_1485_);
lean_dec_ref_known(v___x_1483_, 2);
v_fst_1486_ = lean_ctor_get(v_a_1484_, 0);
lean_inc(v_fst_1486_);
v_snd_1487_ = lean_ctor_get(v_a_1484_, 1);
lean_inc(v_snd_1487_);
lean_dec(v_a_1484_);
v___x_1488_ = lean_unsigned_to_nat(1u);
v___x_1489_ = lean_nat_add(v_offset_1402_, v___x_1488_);
lean_dec(v_offset_1402_);
lean_inc_ref(v_body_1481_);
v___x_1490_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1399_, v_xs_1400_, v_body_1481_, v___x_1489_, v_snd_1487_, v_a_1404_, v_a_1405_, v_a_1485_);
if (lean_obj_tag(v___x_1490_) == 0)
{
lean_object* v_a_1491_; lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1516_; 
v_a_1491_ = lean_ctor_get(v___x_1490_, 0);
v_a_1492_ = lean_ctor_get(v___x_1490_, 1);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1494_ = v___x_1490_;
v_isShared_1495_ = v_isSharedCheck_1516_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_inc(v_a_1491_);
lean_dec(v___x_1490_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1516_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v_fst_1496_; lean_object* v_snd_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1515_; 
v_fst_1496_ = lean_ctor_get(v_a_1491_, 0);
v_snd_1497_ = lean_ctor_get(v_a_1491_, 1);
v_isSharedCheck_1515_ = !lean_is_exclusive(v_a_1491_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1499_ = v_a_1491_;
v_isShared_1500_ = v_isSharedCheck_1515_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_snd_1497_);
lean_inc(v_fst_1496_);
lean_dec(v_a_1491_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1515_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
size_t v___x_1501_; size_t v___x_1502_; uint8_t v___x_1503_; 
v___x_1501_ = lean_ptr_addr(v_binderType_1480_);
v___x_1502_ = lean_ptr_addr(v_fst_1486_);
v___x_1503_ = lean_usize_dec_eq(v___x_1501_, v___x_1502_);
if (v___x_1503_ == 0)
{
lean_object* v___x_1504_; 
lean_inc(v_binderName_1479_);
lean_del_object(v___x_1499_);
lean_del_object(v___x_1494_);
lean_dec_ref_known(v_e_1401_, 3);
v___x_1504_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__3(v_binderName_1479_, v_binderInfo_1482_, v_fst_1486_, v_fst_1496_, v_snd_1497_, v_a_1404_, v_a_1405_, v_a_1492_);
return v___x_1504_;
}
else
{
size_t v___x_1505_; size_t v___x_1506_; uint8_t v___x_1507_; 
v___x_1505_ = lean_ptr_addr(v_body_1481_);
v___x_1506_ = lean_ptr_addr(v_fst_1496_);
v___x_1507_ = lean_usize_dec_eq(v___x_1505_, v___x_1506_);
if (v___x_1507_ == 0)
{
lean_object* v___x_1508_; 
lean_inc(v_binderName_1479_);
lean_del_object(v___x_1499_);
lean_del_object(v___x_1494_);
lean_dec_ref_known(v_e_1401_, 3);
v___x_1508_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__3(v_binderName_1479_, v_binderInfo_1482_, v_fst_1486_, v_fst_1496_, v_snd_1497_, v_a_1404_, v_a_1405_, v_a_1492_);
return v___x_1508_;
}
else
{
lean_object* v___x_1510_; 
lean_dec(v_fst_1496_);
lean_dec(v_fst_1486_);
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 0, v_e_1401_);
v___x_1510_ = v___x_1499_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_e_1401_);
lean_ctor_set(v_reuseFailAlloc_1514_, 1, v_snd_1497_);
v___x_1510_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
lean_object* v___x_1512_; 
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 0, v___x_1510_);
v___x_1512_ = v___x_1494_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v___x_1510_);
lean_ctor_set(v_reuseFailAlloc_1513_, 1, v_a_1492_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1486_);
lean_dec_ref_known(v_e_1401_, 3);
return v___x_1490_;
}
}
else
{
lean_dec_ref_known(v_e_1401_, 3);
lean_dec(v_offset_1402_);
return v___x_1483_;
}
}
case 8:
{
lean_object* v_declName_1517_; lean_object* v_type_1518_; lean_object* v_value_1519_; lean_object* v_body_1520_; uint8_t v_nondep_1521_; lean_object* v___x_1522_; 
v_declName_1517_ = lean_ctor_get(v_e_1401_, 0);
v_type_1518_ = lean_ctor_get(v_e_1401_, 1);
v_value_1519_ = lean_ctor_get(v_e_1401_, 2);
v_body_1520_ = lean_ctor_get(v_e_1401_, 3);
v_nondep_1521_ = lean_ctor_get_uint8(v_e_1401_, sizeof(void*)*4 + 8);
lean_inc(v_offset_1402_);
lean_inc_ref(v_type_1518_);
v___x_1522_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1399_, v_xs_1400_, v_type_1518_, v_offset_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; lean_object* v_a_1524_; lean_object* v_fst_1525_; lean_object* v_snd_1526_; lean_object* v___x_1527_; 
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_a_1523_);
v_a_1524_ = lean_ctor_get(v___x_1522_, 1);
lean_inc(v_a_1524_);
lean_dec_ref_known(v___x_1522_, 2);
v_fst_1525_ = lean_ctor_get(v_a_1523_, 0);
lean_inc(v_fst_1525_);
v_snd_1526_ = lean_ctor_get(v_a_1523_, 1);
lean_inc(v_snd_1526_);
lean_dec(v_a_1523_);
lean_inc(v_offset_1402_);
lean_inc_ref(v_value_1519_);
v___x_1527_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1399_, v_xs_1400_, v_value_1519_, v_offset_1402_, v_snd_1526_, v_a_1404_, v_a_1405_, v_a_1524_);
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_object* v_a_1528_; lean_object* v_a_1529_; lean_object* v_fst_1530_; lean_object* v_snd_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v_a_1528_ = lean_ctor_get(v___x_1527_, 0);
lean_inc(v_a_1528_);
v_a_1529_ = lean_ctor_get(v___x_1527_, 1);
lean_inc(v_a_1529_);
lean_dec_ref_known(v___x_1527_, 2);
v_fst_1530_ = lean_ctor_get(v_a_1528_, 0);
lean_inc(v_fst_1530_);
v_snd_1531_ = lean_ctor_get(v_a_1528_, 1);
lean_inc(v_snd_1531_);
lean_dec(v_a_1528_);
v___x_1532_ = lean_unsigned_to_nat(1u);
v___x_1533_ = lean_nat_add(v_offset_1402_, v___x_1532_);
lean_dec(v_offset_1402_);
lean_inc_ref(v_body_1520_);
v___x_1534_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1399_, v_xs_1400_, v_body_1520_, v___x_1533_, v_snd_1531_, v_a_1404_, v_a_1405_, v_a_1529_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v_a_1535_; lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1564_; 
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
v_a_1536_ = lean_ctor_get(v___x_1534_, 1);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1538_ = v___x_1534_;
v_isShared_1539_ = v_isSharedCheck_1564_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_inc(v_a_1535_);
lean_dec(v___x_1534_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1564_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v_fst_1540_; lean_object* v_snd_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1563_; 
v_fst_1540_ = lean_ctor_get(v_a_1535_, 0);
v_snd_1541_ = lean_ctor_get(v_a_1535_, 1);
v_isSharedCheck_1563_ = !lean_is_exclusive(v_a_1535_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1543_ = v_a_1535_;
v_isShared_1544_ = v_isSharedCheck_1563_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_snd_1541_);
lean_inc(v_fst_1540_);
lean_dec(v_a_1535_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1563_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
size_t v___x_1545_; size_t v___x_1546_; uint8_t v___x_1547_; 
v___x_1545_ = lean_ptr_addr(v_type_1518_);
v___x_1546_ = lean_ptr_addr(v_fst_1525_);
v___x_1547_ = lean_usize_dec_eq(v___x_1545_, v___x_1546_);
if (v___x_1547_ == 0)
{
lean_object* v___x_1548_; 
lean_inc(v_declName_1517_);
lean_del_object(v___x_1543_);
lean_del_object(v___x_1538_);
lean_dec_ref_known(v_e_1401_, 4);
v___x_1548_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4(v_declName_1517_, v_fst_1525_, v_fst_1530_, v_fst_1540_, v_nondep_1521_, v_snd_1541_, v_a_1404_, v_a_1405_, v_a_1536_);
return v___x_1548_;
}
else
{
size_t v___x_1549_; size_t v___x_1550_; uint8_t v___x_1551_; 
v___x_1549_ = lean_ptr_addr(v_value_1519_);
v___x_1550_ = lean_ptr_addr(v_fst_1530_);
v___x_1551_ = lean_usize_dec_eq(v___x_1549_, v___x_1550_);
if (v___x_1551_ == 0)
{
lean_object* v___x_1552_; 
lean_inc(v_declName_1517_);
lean_del_object(v___x_1543_);
lean_del_object(v___x_1538_);
lean_dec_ref_known(v_e_1401_, 4);
v___x_1552_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4(v_declName_1517_, v_fst_1525_, v_fst_1530_, v_fst_1540_, v_nondep_1521_, v_snd_1541_, v_a_1404_, v_a_1405_, v_a_1536_);
return v___x_1552_;
}
else
{
size_t v___x_1553_; size_t v___x_1554_; uint8_t v___x_1555_; 
v___x_1553_ = lean_ptr_addr(v_body_1520_);
v___x_1554_ = lean_ptr_addr(v_fst_1540_);
v___x_1555_ = lean_usize_dec_eq(v___x_1553_, v___x_1554_);
if (v___x_1555_ == 0)
{
lean_object* v___x_1556_; 
lean_inc(v_declName_1517_);
lean_del_object(v___x_1543_);
lean_del_object(v___x_1538_);
lean_dec_ref_known(v_e_1401_, 4);
v___x_1556_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4(v_declName_1517_, v_fst_1525_, v_fst_1530_, v_fst_1540_, v_nondep_1521_, v_snd_1541_, v_a_1404_, v_a_1405_, v_a_1536_);
return v___x_1556_;
}
else
{
lean_object* v___x_1558_; 
lean_dec(v_fst_1540_);
lean_dec(v_fst_1530_);
lean_dec(v_fst_1525_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 0, v_e_1401_);
v___x_1558_ = v___x_1543_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_e_1401_);
lean_ctor_set(v_reuseFailAlloc_1562_, 1, v_snd_1541_);
v___x_1558_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
lean_object* v___x_1560_; 
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 0, v___x_1558_);
v___x_1560_ = v___x_1538_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v___x_1558_);
lean_ctor_set(v_reuseFailAlloc_1561_, 1, v_a_1536_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1530_);
lean_dec(v_fst_1525_);
lean_dec_ref_known(v_e_1401_, 4);
return v___x_1534_;
}
}
else
{
lean_dec(v_fst_1525_);
lean_dec_ref_known(v_e_1401_, 4);
lean_dec(v_offset_1402_);
return v___x_1527_;
}
}
else
{
lean_dec_ref_known(v_e_1401_, 4);
lean_dec(v_offset_1402_);
return v___x_1522_;
}
}
case 10:
{
lean_object* v_data_1565_; lean_object* v_expr_1566_; lean_object* v___x_1567_; 
v_data_1565_ = lean_ctor_get(v_e_1401_, 0);
v_expr_1566_ = lean_ctor_get(v_e_1401_, 1);
lean_inc_ref(v_expr_1566_);
v___x_1567_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1399_, v_xs_1400_, v_expr_1566_, v_offset_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1589_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
v_a_1569_ = lean_ctor_get(v___x_1567_, 1);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1571_ = v___x_1567_;
v_isShared_1572_ = v_isSharedCheck_1589_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_inc(v_a_1568_);
lean_dec(v___x_1567_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1589_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v_fst_1573_; lean_object* v_snd_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1588_; 
v_fst_1573_ = lean_ctor_get(v_a_1568_, 0);
v_snd_1574_ = lean_ctor_get(v_a_1568_, 1);
v_isSharedCheck_1588_ = !lean_is_exclusive(v_a_1568_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1576_ = v_a_1568_;
v_isShared_1577_ = v_isSharedCheck_1588_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_snd_1574_);
lean_inc(v_fst_1573_);
lean_dec(v_a_1568_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1588_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
size_t v___x_1578_; size_t v___x_1579_; uint8_t v___x_1580_; 
v___x_1578_ = lean_ptr_addr(v_expr_1566_);
v___x_1579_ = lean_ptr_addr(v_fst_1573_);
v___x_1580_ = lean_usize_dec_eq(v___x_1578_, v___x_1579_);
if (v___x_1580_ == 0)
{
lean_object* v___x_1581_; 
lean_inc(v_data_1565_);
lean_del_object(v___x_1576_);
lean_del_object(v___x_1571_);
lean_dec_ref_known(v_e_1401_, 2);
v___x_1581_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__5(v_data_1565_, v_fst_1573_, v_snd_1574_, v_a_1404_, v_a_1405_, v_a_1569_);
return v___x_1581_;
}
else
{
lean_object* v___x_1583_; 
lean_dec(v_fst_1573_);
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 0, v_e_1401_);
v___x_1583_ = v___x_1576_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_e_1401_);
lean_ctor_set(v_reuseFailAlloc_1587_, 1, v_snd_1574_);
v___x_1583_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
lean_object* v___x_1585_; 
if (v_isShared_1572_ == 0)
{
lean_ctor_set(v___x_1571_, 0, v___x_1583_);
v___x_1585_ = v___x_1571_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1583_);
lean_ctor_set(v_reuseFailAlloc_1586_, 1, v_a_1569_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1401_, 2);
return v___x_1567_;
}
}
case 11:
{
lean_object* v_typeName_1590_; lean_object* v_idx_1591_; lean_object* v_struct_1592_; lean_object* v___x_1593_; 
v_typeName_1590_ = lean_ctor_get(v_e_1401_, 0);
v_idx_1591_ = lean_ctor_get(v_e_1401_, 1);
v_struct_1592_ = lean_ctor_get(v_e_1401_, 2);
lean_inc_ref(v_struct_1592_);
v___x_1593_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1399_, v_xs_1400_, v_struct_1592_, v_offset_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v_a_1594_; lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1615_; 
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
v_a_1595_ = lean_ctor_get(v___x_1593_, 1);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1597_ = v___x_1593_;
v_isShared_1598_ = v_isSharedCheck_1615_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_inc(v_a_1594_);
lean_dec(v___x_1593_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1615_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v_fst_1599_; lean_object* v_snd_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1614_; 
v_fst_1599_ = lean_ctor_get(v_a_1594_, 0);
v_snd_1600_ = lean_ctor_get(v_a_1594_, 1);
v_isSharedCheck_1614_ = !lean_is_exclusive(v_a_1594_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1602_ = v_a_1594_;
v_isShared_1603_ = v_isSharedCheck_1614_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_snd_1600_);
lean_inc(v_fst_1599_);
lean_dec(v_a_1594_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1614_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
size_t v___x_1604_; size_t v___x_1605_; uint8_t v___x_1606_; 
v___x_1604_ = lean_ptr_addr(v_struct_1592_);
v___x_1605_ = lean_ptr_addr(v_fst_1599_);
v___x_1606_ = lean_usize_dec_eq(v___x_1604_, v___x_1605_);
if (v___x_1606_ == 0)
{
lean_object* v___x_1607_; 
lean_inc(v_idx_1591_);
lean_inc(v_typeName_1590_);
lean_del_object(v___x_1602_);
lean_del_object(v___x_1597_);
lean_dec_ref_known(v_e_1401_, 3);
v___x_1607_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__6(v_typeName_1590_, v_idx_1591_, v_fst_1599_, v_snd_1600_, v_a_1404_, v_a_1405_, v_a_1595_);
return v___x_1607_;
}
else
{
lean_object* v___x_1609_; 
lean_dec(v_fst_1599_);
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 0, v_e_1401_);
v___x_1609_ = v___x_1602_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_e_1401_);
lean_ctor_set(v_reuseFailAlloc_1613_, 1, v_snd_1600_);
v___x_1609_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
lean_object* v___x_1611_; 
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 0, v___x_1609_);
v___x_1611_ = v___x_1597_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v___x_1609_);
lean_ctor_set(v_reuseFailAlloc_1612_, 1, v_a_1595_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1401_, 3);
return v___x_1593_;
}
}
default: 
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
lean_dec(v_offset_1402_);
lean_dec_ref(v_e_1401_);
v___x_1616_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__3);
v___x_1617_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7(v___x_1616_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_);
return v___x_1617_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1399_ = stack[0].m_obj;
lean_object* v_xs_1400_ = stack[1].m_obj;
lean_object* v_e_1401_ = stack[2].m_obj;
lean_object* v_offset_1402_ = stack[3].m_obj;
lean_object* v_a_1403_ = stack[4].m_obj;
uint8_t v_a_1404_ = stack[5].m_num;
lean_object* v_a_1405_ = stack[6].m_obj;
lean_object* v_a_1406_ = stack[7].m_obj;
lean_object* v_res_1618_;
v_res_1618_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0(v_n_1399_, v_xs_1400_, v_e_1401_, v_offset_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_);
stack->m_obj
 = v_res_1618_;
}
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(lean_object* v_n_1619_, lean_object* v_xs_1620_, lean_object* v_e_1621_, lean_object* v_offset_1622_, lean_object* v_a_1623_, uint8_t v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_){
_start:
{
lean_object* v_key_1627_; lean_object* v___x_1628_; 
lean_inc(v_offset_1622_);
lean_inc_ref(v_e_1621_);
v_key_1627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1627_, 0, v_e_1621_);
lean_ctor_set(v_key_1627_, 1, v_offset_1622_);
v___x_1628_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2___redArg(v_a_1623_, v_key_1627_);
if (lean_obj_tag(v___x_1628_) == 1)
{
lean_object* v_val_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
lean_dec_ref_known(v_key_1627_, 2);
lean_dec(v_offset_1622_);
lean_dec_ref(v_e_1621_);
v_val_1629_ = lean_ctor_get(v___x_1628_, 0);
lean_inc(v_val_1629_);
lean_dec_ref_known(v___x_1628_, 1);
v___x_1630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1630_, 0, v_val_1629_);
lean_ctor_set(v___x_1630_, 1, v_a_1623_);
v___x_1631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1630_);
lean_ctor_set(v___x_1631_, 1, v_a_1626_);
return v___x_1631_;
}
else
{
lean_dec(v___x_1628_);
switch(lean_obj_tag(v_e_1621_))
{
case 0:
{
lean_object* v_deBruijnIndex_1632_; uint8_t v___x_1633_; 
v_deBruijnIndex_1632_ = lean_ctor_get(v_e_1621_, 0);
v___x_1633_ = lean_nat_dec_le(v_offset_1622_, v_deBruijnIndex_1632_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1634_; 
lean_dec(v_offset_1622_);
v___x_1634_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1627_, v_e_1621_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
return v___x_1634_;
}
else
{
lean_object* v_size_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; uint8_t v___x_1641_; 
lean_inc(v_deBruijnIndex_1632_);
lean_dec_ref_known(v_e_1621_, 1);
v_size_1635_ = lean_ctor_get(v_xs_1620_, 2);
v___x_1636_ = l_Lean_instInhabitedExpr;
v___x_1637_ = lean_nat_sub(v_deBruijnIndex_1632_, v_offset_1622_);
lean_dec(v_offset_1622_);
lean_dec(v_deBruijnIndex_1632_);
v___x_1638_ = lean_nat_sub(v_n_1619_, v___x_1637_);
lean_dec(v___x_1637_);
v___x_1639_ = lean_unsigned_to_nat(1u);
v___x_1640_ = lean_nat_sub(v___x_1638_, v___x_1639_);
lean_dec(v___x_1638_);
v___x_1641_ = lean_nat_dec_lt(v___x_1640_, v_size_1635_);
if (v___x_1641_ == 0)
{
lean_object* v___x_1642_; lean_object* v___x_1643_; 
lean_dec(v___x_1640_);
v___x_1642_ = l_outOfBounds___redArg(v___x_1636_);
v___x_1643_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1627_, v___x_1642_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
return v___x_1643_;
}
else
{
lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1644_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1636_, v_xs_1620_, v___x_1640_);
lean_dec(v___x_1640_);
v___x_1645_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1627_, v___x_1644_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
return v___x_1645_;
}
}
}
case 9:
{
lean_object* v___x_1646_; 
lean_dec(v_offset_1622_);
v___x_1646_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1627_, v_e_1621_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
return v___x_1646_;
}
case 2:
{
lean_object* v___x_1647_; 
lean_dec(v_offset_1622_);
v___x_1647_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1627_, v_e_1621_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
return v___x_1647_;
}
case 1:
{
lean_object* v___x_1648_; 
lean_dec(v_offset_1622_);
v___x_1648_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1627_, v_e_1621_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
return v___x_1648_;
}
case 4:
{
lean_object* v___x_1649_; 
lean_dec(v_offset_1622_);
v___x_1649_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1627_, v_e_1621_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
return v___x_1649_;
}
case 3:
{
lean_object* v___x_1650_; 
lean_dec(v_offset_1622_);
v___x_1650_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1627_, v_e_1621_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
return v___x_1650_;
}
default: 
{
lean_object* v___x_1651_; uint8_t v___x_1652_; 
v___x_1651_ = l_Lean_Expr_looseBVarRange(v_e_1621_);
v___x_1652_ = lean_nat_dec_le(v___x_1651_, v_offset_1622_);
lean_dec(v___x_1651_);
if (v___x_1652_ == 0)
{
switch(lean_obj_tag(v_e_1621_))
{
case 9:
{
lean_object* v___x_1653_; 
lean_dec(v_offset_1622_);
v___x_1653_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1627_, v_e_1621_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
return v___x_1653_;
}
case 2:
{
lean_object* v___x_1654_; 
lean_dec(v_offset_1622_);
v___x_1654_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1627_, v_e_1621_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
return v___x_1654_;
}
case 0:
{
lean_object* v___x_1655_; 
lean_dec(v_offset_1622_);
v___x_1655_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1627_, v_e_1621_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
return v___x_1655_;
}
case 1:
{
lean_object* v___x_1656_; 
lean_dec(v_offset_1622_);
v___x_1656_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1627_, v_e_1621_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
return v___x_1656_;
}
case 4:
{
lean_object* v___x_1657_; 
lean_dec(v_offset_1622_);
v___x_1657_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1627_, v_e_1621_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
return v___x_1657_;
}
case 3:
{
lean_object* v___x_1658_; 
lean_dec(v_offset_1622_);
v___x_1658_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1627_, v_e_1621_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
return v___x_1658_;
}
default: 
{
lean_object* v___x_1659_; 
v___x_1659_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0(v_n_1619_, v_xs_1620_, v_e_1621_, v_offset_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v_a_1660_; lean_object* v_a_1661_; lean_object* v_fst_1662_; lean_object* v_snd_1663_; lean_object* v___x_1664_; 
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
lean_inc(v_a_1660_);
v_a_1661_ = lean_ctor_get(v___x_1659_, 1);
lean_inc(v_a_1661_);
lean_dec_ref_known(v___x_1659_, 2);
v_fst_1662_ = lean_ctor_get(v_a_1660_, 0);
lean_inc(v_fst_1662_);
v_snd_1663_ = lean_ctor_get(v_a_1660_, 1);
lean_inc(v_snd_1663_);
lean_dec(v_a_1660_);
v___x_1664_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1627_, v_fst_1662_, v_snd_1663_, v_a_1624_, v_a_1625_, v_a_1661_);
return v___x_1664_;
}
else
{
lean_dec_ref_known(v_key_1627_, 2);
return v___x_1659_;
}
}
}
}
else
{
lean_object* v___x_1665_; 
lean_dec(v_offset_1622_);
v___x_1665_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1627_, v_e_1621_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
return v___x_1665_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1619_ = stack[0].m_obj;
lean_object* v_xs_1620_ = stack[1].m_obj;
lean_object* v_e_1621_ = stack[2].m_obj;
lean_object* v_offset_1622_ = stack[3].m_obj;
lean_object* v_a_1623_ = stack[4].m_obj;
uint8_t v_a_1624_ = stack[5].m_num;
lean_object* v_a_1625_ = stack[6].m_obj;
lean_object* v_a_1626_ = stack[7].m_obj;
lean_object* v_res_1666_;
v_res_1666_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1619_, v_xs_1620_, v_e_1621_, v_offset_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
stack->m_obj
 = v_res_1666_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0___boxed(lean_object* v_n_1667_, lean_object* v_xs_1668_, lean_object* v_e_1669_, lean_object* v_offset_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_){
_start:
{
uint8_t v_a_boxed_1675_; lean_object* v_res_1676_; 
v_a_boxed_1675_ = lean_unbox(v_a_1672_);
v_res_1676_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1667_, v_xs_1668_, v_e_1669_, v_offset_1670_, v_a_1671_, v_a_boxed_1675_, v_a_1673_, v_a_1674_);
lean_dec_ref(v_a_1673_);
lean_dec_ref(v_xs_1668_);
lean_dec(v_n_1667_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___boxed(lean_object* v_n_1677_, lean_object* v_xs_1678_, lean_object* v_e_1679_, lean_object* v_offset_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_){
_start:
{
uint8_t v_a_boxed_1685_; lean_object* v_res_1686_; 
v_a_boxed_1685_ = lean_unbox(v_a_1682_);
v_res_1686_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0(v_n_1677_, v_xs_1678_, v_e_1679_, v_offset_1680_, v_a_1681_, v_a_boxed_1685_, v_a_1683_, v_a_1684_);
lean_dec_ref(v_a_1683_);
lean_dec_ref(v_xs_1678_);
lean_dec(v_n_1677_);
return v_res_1686_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1687_ = lean_box(0);
v___x_1688_ = lean_unsigned_to_nat(16u);
v___x_1689_ = lean_mk_array(v___x_1688_, v___x_1687_);
return v___x_1689_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1690_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__0, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__0_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__0);
v___x_1691_ = lean_unsigned_to_nat(0u);
v___x_1692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1691_);
lean_ctor_set(v___x_1692_, 1, v___x_1690_);
return v___x_1692_;
}
}
lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0(lean_object* v_e_1693_, lean_object* v_size_1694_, lean_object* v___x_1695_, lean_object* v_xs_1696_, uint8_t v_debug_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
lean_object* v___x_1700_; 
v___x_1700_ = lean_unsigned_to_nat(0u);
switch(lean_obj_tag(v_e_1693_))
{
case 0:
{
lean_object* v_deBruijnIndex_1701_; uint8_t v___x_1702_; 
v_deBruijnIndex_1701_ = lean_ctor_get(v_e_1693_, 0);
v___x_1702_ = lean_nat_dec_le(v___x_1700_, v_deBruijnIndex_1701_);
if (v___x_1702_ == 0)
{
lean_object* v___x_1703_; 
v___x_1703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1703_, 0, v_e_1693_);
lean_ctor_set(v___x_1703_, 1, v___y_1699_);
return v___x_1703_;
}
else
{
lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; uint8_t v___x_1707_; 
lean_inc(v_deBruijnIndex_1701_);
lean_dec_ref_known(v_e_1693_, 1);
v___x_1704_ = lean_nat_sub(v_size_1694_, v_deBruijnIndex_1701_);
lean_dec(v_deBruijnIndex_1701_);
v___x_1705_ = lean_unsigned_to_nat(1u);
v___x_1706_ = lean_nat_sub(v___x_1704_, v___x_1705_);
lean_dec(v___x_1704_);
v___x_1707_ = lean_nat_dec_lt(v___x_1706_, v_size_1694_);
if (v___x_1707_ == 0)
{
lean_object* v___x_1708_; lean_object* v___x_1709_; 
lean_dec(v___x_1706_);
v___x_1708_ = l_outOfBounds___redArg(v___x_1695_);
v___x_1709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1708_);
lean_ctor_set(v___x_1709_, 1, v___y_1699_);
return v___x_1709_;
}
else
{
lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1710_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1695_, v_xs_1696_, v___x_1706_);
lean_dec(v___x_1706_);
v___x_1711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1710_);
lean_ctor_set(v___x_1711_, 1, v___y_1699_);
return v___x_1711_;
}
}
}
case 9:
{
lean_object* v___x_1712_; 
v___x_1712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1712_, 0, v_e_1693_);
lean_ctor_set(v___x_1712_, 1, v___y_1699_);
return v___x_1712_;
}
case 2:
{
lean_object* v___x_1713_; 
v___x_1713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1713_, 0, v_e_1693_);
lean_ctor_set(v___x_1713_, 1, v___y_1699_);
return v___x_1713_;
}
case 1:
{
lean_object* v___x_1714_; 
v___x_1714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1714_, 0, v_e_1693_);
lean_ctor_set(v___x_1714_, 1, v___y_1699_);
return v___x_1714_;
}
case 4:
{
lean_object* v___x_1715_; 
v___x_1715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1715_, 0, v_e_1693_);
lean_ctor_set(v___x_1715_, 1, v___y_1699_);
return v___x_1715_;
}
case 3:
{
lean_object* v___x_1716_; 
v___x_1716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1716_, 0, v_e_1693_);
lean_ctor_set(v___x_1716_, 1, v___y_1699_);
return v___x_1716_;
}
default: 
{
lean_object* v___x_1717_; uint8_t v___x_1718_; 
v___x_1717_ = l_Lean_Expr_looseBVarRange(v_e_1693_);
v___x_1718_ = lean_nat_dec_le(v___x_1717_, v___x_1700_);
lean_dec(v___x_1717_);
if (v___x_1718_ == 0)
{
switch(lean_obj_tag(v_e_1693_))
{
case 9:
{
lean_object* v___x_1719_; 
v___x_1719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1719_, 0, v_e_1693_);
lean_ctor_set(v___x_1719_, 1, v___y_1699_);
return v___x_1719_;
}
case 2:
{
lean_object* v___x_1720_; 
v___x_1720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1720_, 0, v_e_1693_);
lean_ctor_set(v___x_1720_, 1, v___y_1699_);
return v___x_1720_;
}
case 0:
{
lean_object* v___x_1721_; 
v___x_1721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1721_, 0, v_e_1693_);
lean_ctor_set(v___x_1721_, 1, v___y_1699_);
return v___x_1721_;
}
case 1:
{
lean_object* v___x_1722_; 
v___x_1722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1722_, 0, v_e_1693_);
lean_ctor_set(v___x_1722_, 1, v___y_1699_);
return v___x_1722_;
}
case 4:
{
lean_object* v___x_1723_; 
v___x_1723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1723_, 0, v_e_1693_);
lean_ctor_set(v___x_1723_, 1, v___y_1699_);
return v___x_1723_;
}
case 3:
{
lean_object* v___x_1724_; 
v___x_1724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1724_, 0, v_e_1693_);
lean_ctor_set(v___x_1724_, 1, v___y_1699_);
return v___x_1724_;
}
default: 
{
lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1725_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__1, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__1);
v___x_1726_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0(v_size_1694_, v_xs_1696_, v_e_1693_, v___x_1700_, v___x_1725_, v_debug_1697_, v___y_1698_, v___y_1699_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_object* v_a_1727_; lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1736_; 
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
v_a_1728_ = lean_ctor_get(v___x_1726_, 1);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1730_ = v___x_1726_;
v_isShared_1731_ = v_isSharedCheck_1736_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_inc(v_a_1727_);
lean_dec(v___x_1726_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1736_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v_fst_1732_; lean_object* v___x_1734_; 
v_fst_1732_ = lean_ctor_get(v_a_1727_, 0);
lean_inc(v_fst_1732_);
lean_dec(v_a_1727_);
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 0, v_fst_1732_);
v___x_1734_ = v___x_1730_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_fst_1732_);
lean_ctor_set(v_reuseFailAlloc_1735_, 1, v_a_1728_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
else
{
lean_object* v_a_1737_; lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1745_; 
v_a_1737_ = lean_ctor_get(v___x_1726_, 0);
v_a_1738_ = lean_ctor_get(v___x_1726_, 1);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1740_ = v___x_1726_;
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_inc(v_a_1737_);
lean_dec(v___x_1726_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1743_; 
if (v_isShared_1741_ == 0)
{
v___x_1743_ = v___x_1740_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_a_1737_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v_a_1738_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
}
}
}
}
else
{
lean_object* v___x_1746_; 
v___x_1746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1746_, 0, v_e_1693_);
lean_ctor_set(v___x_1746_, 1, v___y_1699_);
return v___x_1746_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1693_ = stack[0].m_obj;
lean_object* v_size_1694_ = stack[1].m_obj;
lean_object* v___x_1695_ = stack[2].m_obj;
lean_object* v_xs_1696_ = stack[3].m_obj;
uint8_t v_debug_1697_ = stack[4].m_num;
lean_object* v___y_1698_ = stack[5].m_obj;
lean_object* v___y_1699_ = stack[6].m_obj;
lean_object* v_res_1747_;
v_res_1747_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0(v_e_1693_, v_size_1694_, v___x_1695_, v_xs_1696_, v_debug_1697_, v___y_1698_, v___y_1699_);
stack->m_obj
 = v_res_1747_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___boxed(lean_object* v_e_1748_, lean_object* v_size_1749_, lean_object* v___x_1750_, lean_object* v_xs_1751_, lean_object* v_debug_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
uint8_t v_debug_boxed_1755_; lean_object* v_res_1756_; 
v_debug_boxed_1755_ = lean_unbox(v_debug_1752_);
v_res_1756_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0(v_e_1748_, v_size_1749_, v___x_1750_, v_xs_1751_, v_debug_boxed_1755_, v___y_1753_, v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec_ref(v_xs_1751_);
lean_dec_ref(v___x_1750_);
lean_dec(v_size_1749_);
return v_res_1756_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2(void){
_start:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1759_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__2));
v___x_1760_ = lean_unsigned_to_nat(16u);
v___x_1761_ = lean_unsigned_to_nat(62u);
v___x_1762_ = ((lean_object*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__1));
v___x_1763_ = ((lean_object*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__0));
v___x_1764_ = l_mkPanicMessageWithDecl(v___x_1763_, v___x_1762_, v___x_1761_, v___x_1760_, v___x_1759_);
return v___x_1764_;
}
}
lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg(lean_object* v_xs_1765_, lean_object* v_e_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_){
_start:
{
lean_object* v_size_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; uint8_t v_debug_1777_; lean_object* v___x_1778_; lean_object* v___f_1779_; lean_object* v___x_1780_; lean_object* v_env_1781_; uint8_t v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v_size_1774_ = lean_ctor_get(v_xs_1765_, 2);
lean_inc(v_size_1774_);
v___x_1775_ = l_Lean_instInhabitedExpr;
v___x_1776_ = lean_st_ref_get(v_a_1768_);
v_debug_1777_ = lean_ctor_get_uint8(v___x_1776_, sizeof(void*)*12);
lean_dec(v___x_1776_);
v___x_1778_ = lean_box(v_debug_1777_);
v___f_1779_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___boxed), 7, 5);
lean_closure_set(v___f_1779_, 0, v_e_1766_);
lean_closure_set(v___f_1779_, 1, v_size_1774_);
lean_closure_set(v___f_1779_, 2, v___x_1775_);
lean_closure_set(v___f_1779_, 3, v_xs_1765_);
lean_closure_set(v___f_1779_, 4, v___x_1778_);
v___x_1780_ = lean_st_ref_get(v_a_1772_);
v_env_1781_ = lean_ctor_get(v___x_1780_, 0);
lean_inc_ref(v_env_1781_);
lean_dec(v___x_1780_);
v___x_1782_ = 0;
v___x_1783_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1783_, 0, v_env_1781_);
lean_ctor_set_uint8(v___x_1783_, sizeof(void*)*1, v___x_1782_);
lean_ctor_set_uint8(v___x_1783_, sizeof(void*)*1 + 1, v___x_1782_);
v___x_1784_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_1779_, v___x_1783_, v_a_1768_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1795_; 
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1787_ = v___x_1784_;
v_isShared_1788_ = v_isSharedCheck_1795_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1784_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1795_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
if (lean_obj_tag(v_a_1785_) == 0)
{
lean_object* v___x_1789_; lean_object* v___x_1790_; 
lean_dec_ref_known(v_a_1785_, 1);
lean_del_object(v___x_1787_);
v___x_1789_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2);
v___x_1790_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1(v___x_1789_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_, v_a_1771_, v_a_1772_);
return v___x_1790_;
}
else
{
lean_object* v_a_1791_; lean_object* v___x_1793_; 
v_a_1791_ = lean_ctor_get(v_a_1785_, 0);
lean_inc(v_a_1791_);
lean_dec_ref_known(v_a_1785_, 1);
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 0, v_a_1791_);
v___x_1793_ = v___x_1787_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1791_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
else
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1803_; 
v_a_1796_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1798_ = v___x_1784_;
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1784_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1801_; 
if (v_isShared_1799_ == 0)
{
v___x_1801_ = v___x_1798_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_a_1796_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_1765_ = stack[0].m_obj;
lean_object* v_e_1766_ = stack[1].m_obj;
lean_object* v_a_1767_ = stack[2].m_obj;
lean_object* v_a_1768_ = stack[3].m_obj;
lean_object* v_a_1769_ = stack[4].m_obj;
lean_object* v_a_1770_ = stack[5].m_obj;
lean_object* v_a_1771_ = stack[6].m_obj;
lean_object* v_a_1772_ = stack[7].m_obj;
lean_object* v_res_1804_;
v_res_1804_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg(v_xs_1765_, v_e_1766_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_, v_a_1771_, v_a_1772_);
stack->m_obj
 = v_res_1804_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___boxed(lean_object* v_xs_1805_, lean_object* v_e_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg(v_xs_1805_, v_e_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_);
lean_dec(v_a_1812_);
lean_dec_ref(v_a_1811_);
lean_dec(v_a_1810_);
lean_dec_ref(v_a_1809_);
lean_dec(v_a_1808_);
lean_dec_ref(v_a_1807_);
return v_res_1814_;
}
}
lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv(lean_object* v_xs_1815_, lean_object* v_e_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg(v_xs_1815_, v_e_1816_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_);
return v___x_1825_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_1815_ = stack[0].m_obj;
lean_object* v_e_1816_ = stack[1].m_obj;
lean_object* v_a_1817_ = stack[2].m_obj;
lean_object* v_a_1818_ = stack[3].m_obj;
lean_object* v_a_1819_ = stack[4].m_obj;
lean_object* v_a_1820_ = stack[5].m_obj;
lean_object* v_a_1821_ = stack[6].m_obj;
lean_object* v_a_1822_ = stack[7].m_obj;
lean_object* v_a_1823_ = stack[8].m_obj;
lean_object* v_res_1826_;
v_res_1826_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv(v_xs_1815_, v_e_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_);
stack->m_obj
 = v_res_1826_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___boxed(lean_object* v_xs_1827_, lean_object* v_e_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv(v_xs_1827_, v_e_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_);
lean_dec(v_a_1835_);
lean_dec_ref(v_a_1834_);
lean_dec(v_a_1833_);
lean_dec_ref(v_a_1832_);
lean_dec(v_a_1831_);
lean_dec_ref(v_a_1830_);
lean_dec(v_a_1829_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1838_, lean_object* v_m_1839_, lean_object* v_a_1840_){
_start:
{
lean_object* v___x_1841_; 
v___x_1841_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2___redArg(v_m_1839_, v_a_1840_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1842_, lean_object* v_m_1843_, lean_object* v_a_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2(v_00_u03b2_1842_, v_m_1843_, v_a_1844_);
lean_dec_ref(v_a_1844_);
lean_dec_ref(v_m_1843_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10(lean_object* v_00_u03b2_1846_, lean_object* v_a_1847_, lean_object* v_x_1848_){
_start:
{
lean_object* v___x_1849_; 
v___x_1849_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10___redArg(v_a_1847_, v_x_1848_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10___boxed(lean_object* v_00_u03b2_1850_, lean_object* v_a_1851_, lean_object* v_x_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10(v_00_u03b2_1850_, v_a_1851_, v_x_1852_);
lean_dec(v_x_1852_);
lean_dec_ref(v_a_1851_);
return v_res_1853_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1854_; 
v___x_1854_ = l_instMonadEIO___redArg();
return v___x_1854_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(lean_object* v_msg_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v_toApplicative_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1934_; 
v___x_1868_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__0);
v___x_1869_ = l_StateRefT_x27_instMonad___redArg(v___x_1868_);
v_toApplicative_1870_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1934_ == 0)
{
lean_object* v_unused_1935_; 
v_unused_1935_ = lean_ctor_get(v___x_1869_, 1);
lean_dec(v_unused_1935_);
v___x_1872_ = v___x_1869_;
v_isShared_1873_ = v_isSharedCheck_1934_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_toApplicative_1870_);
lean_dec(v___x_1869_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1934_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v_toFunctor_1874_; lean_object* v_toSeq_1875_; lean_object* v_toSeqLeft_1876_; lean_object* v_toSeqRight_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1932_; 
v_toFunctor_1874_ = lean_ctor_get(v_toApplicative_1870_, 0);
v_toSeq_1875_ = lean_ctor_get(v_toApplicative_1870_, 2);
v_toSeqLeft_1876_ = lean_ctor_get(v_toApplicative_1870_, 3);
v_toSeqRight_1877_ = lean_ctor_get(v_toApplicative_1870_, 4);
v_isSharedCheck_1932_ = !lean_is_exclusive(v_toApplicative_1870_);
if (v_isSharedCheck_1932_ == 0)
{
lean_object* v_unused_1933_; 
v_unused_1933_ = lean_ctor_get(v_toApplicative_1870_, 1);
lean_dec(v_unused_1933_);
v___x_1879_ = v_toApplicative_1870_;
v_isShared_1880_ = v_isSharedCheck_1932_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_toSeqRight_1877_);
lean_inc(v_toSeqLeft_1876_);
lean_inc(v_toSeq_1875_);
lean_inc(v_toFunctor_1874_);
lean_dec(v_toApplicative_1870_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1932_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___f_1881_; lean_object* v___f_1882_; lean_object* v___f_1883_; lean_object* v___f_1884_; lean_object* v___x_1885_; lean_object* v___f_1886_; lean_object* v___f_1887_; lean_object* v___f_1888_; lean_object* v___x_1890_; 
v___f_1881_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__1));
v___f_1882_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1874_);
v___f_1883_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1883_, 0, v_toFunctor_1874_);
v___f_1884_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1884_, 0, v_toFunctor_1874_);
v___x_1885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1885_, 0, v___f_1883_);
lean_ctor_set(v___x_1885_, 1, v___f_1884_);
v___f_1886_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1886_, 0, v_toSeqRight_1877_);
v___f_1887_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1887_, 0, v_toSeqLeft_1876_);
v___f_1888_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1888_, 0, v_toSeq_1875_);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 4, v___f_1886_);
lean_ctor_set(v___x_1879_, 3, v___f_1887_);
lean_ctor_set(v___x_1879_, 2, v___f_1888_);
lean_ctor_set(v___x_1879_, 1, v___f_1881_);
lean_ctor_set(v___x_1879_, 0, v___x_1885_);
v___x_1890_ = v___x_1879_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1885_);
lean_ctor_set(v_reuseFailAlloc_1931_, 1, v___f_1881_);
lean_ctor_set(v_reuseFailAlloc_1931_, 2, v___f_1888_);
lean_ctor_set(v_reuseFailAlloc_1931_, 3, v___f_1887_);
lean_ctor_set(v_reuseFailAlloc_1931_, 4, v___f_1886_);
v___x_1890_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1892_; 
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 1, v___f_1882_);
lean_ctor_set(v___x_1872_, 0, v___x_1890_);
v___x_1892_ = v___x_1872_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1890_);
lean_ctor_set(v_reuseFailAlloc_1930_, 1, v___f_1882_);
v___x_1892_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
lean_object* v___x_1893_; lean_object* v_toApplicative_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1928_; 
v___x_1893_ = l_StateRefT_x27_instMonad___redArg(v___x_1892_);
v_toApplicative_1894_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1928_ == 0)
{
lean_object* v_unused_1929_; 
v_unused_1929_ = lean_ctor_get(v___x_1893_, 1);
lean_dec(v_unused_1929_);
v___x_1896_ = v___x_1893_;
v_isShared_1897_ = v_isSharedCheck_1928_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_toApplicative_1894_);
lean_dec(v___x_1893_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1928_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v_toFunctor_1898_; lean_object* v_toSeq_1899_; lean_object* v_toSeqLeft_1900_; lean_object* v_toSeqRight_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1926_; 
v_toFunctor_1898_ = lean_ctor_get(v_toApplicative_1894_, 0);
v_toSeq_1899_ = lean_ctor_get(v_toApplicative_1894_, 2);
v_toSeqLeft_1900_ = lean_ctor_get(v_toApplicative_1894_, 3);
v_toSeqRight_1901_ = lean_ctor_get(v_toApplicative_1894_, 4);
v_isSharedCheck_1926_ = !lean_is_exclusive(v_toApplicative_1894_);
if (v_isSharedCheck_1926_ == 0)
{
lean_object* v_unused_1927_; 
v_unused_1927_ = lean_ctor_get(v_toApplicative_1894_, 1);
lean_dec(v_unused_1927_);
v___x_1903_ = v_toApplicative_1894_;
v_isShared_1904_ = v_isSharedCheck_1926_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_toSeqRight_1901_);
lean_inc(v_toSeqLeft_1900_);
lean_inc(v_toSeq_1899_);
lean_inc(v_toFunctor_1898_);
lean_dec(v_toApplicative_1894_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1926_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___f_1905_; lean_object* v___f_1906_; lean_object* v___f_1907_; lean_object* v___f_1908_; lean_object* v___x_1909_; lean_object* v___f_1910_; lean_object* v___f_1911_; lean_object* v___f_1912_; lean_object* v___x_1914_; 
v___f_1905_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__3));
v___f_1906_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1898_);
v___f_1907_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1907_, 0, v_toFunctor_1898_);
v___f_1908_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1908_, 0, v_toFunctor_1898_);
v___x_1909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1909_, 0, v___f_1907_);
lean_ctor_set(v___x_1909_, 1, v___f_1908_);
v___f_1910_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1910_, 0, v_toSeqRight_1901_);
v___f_1911_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1911_, 0, v_toSeqLeft_1900_);
v___f_1912_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1912_, 0, v_toSeq_1899_);
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 4, v___f_1910_);
lean_ctor_set(v___x_1903_, 3, v___f_1911_);
lean_ctor_set(v___x_1903_, 2, v___f_1912_);
lean_ctor_set(v___x_1903_, 1, v___f_1905_);
lean_ctor_set(v___x_1903_, 0, v___x_1909_);
v___x_1914_ = v___x_1903_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v___x_1909_);
lean_ctor_set(v_reuseFailAlloc_1925_, 1, v___f_1905_);
lean_ctor_set(v_reuseFailAlloc_1925_, 2, v___f_1912_);
lean_ctor_set(v_reuseFailAlloc_1925_, 3, v___f_1911_);
lean_ctor_set(v_reuseFailAlloc_1925_, 4, v___f_1910_);
v___x_1914_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
lean_object* v___x_1916_; 
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 1, v___f_1906_);
lean_ctor_set(v___x_1896_, 0, v___x_1914_);
v___x_1916_ = v___x_1896_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1914_);
lean_ctor_set(v_reuseFailAlloc_1924_, 1, v___f_1906_);
v___x_1916_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_14116__overap_1922_; lean_object* v___x_1923_; 
v___x_1917_ = l_StateRefT_x27_instMonad___redArg(v___x_1916_);
v___x_1918_ = l_ReaderT_instMonad___redArg(v___x_1917_);
v___x_1919_ = l_StateRefT_x27_instMonad___redArg(v___x_1918_);
v___x_1920_ = l_Lean_instInhabitedExpr;
v___x_1921_ = l_instInhabitedOfMonad___redArg(v___x_1919_, v___x_1920_);
v___x_14116__overap_1922_ = lean_panic_fn_borrowed(v___x_1921_, v_msg_1859_);
lean_dec(v___x_1921_);
lean_inc(v___y_1866_);
lean_inc_ref(v___y_1865_);
lean_inc(v___y_1864_);
lean_inc_ref(v___y_1863_);
lean_inc(v___y_1862_);
lean_inc_ref(v___y_1861_);
lean_inc(v___y_1860_);
v___x_1923_ = lean_apply_8(v___x_14116__overap_1922_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, lean_box(0));
return v___x_1923_;
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
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1859_ = stack[0].m_obj;
lean_object* v___y_1860_ = stack[1].m_obj;
lean_object* v___y_1861_ = stack[2].m_obj;
lean_object* v___y_1862_ = stack[3].m_obj;
lean_object* v___y_1863_ = stack[4].m_obj;
lean_object* v___y_1864_ = stack[5].m_obj;
lean_object* v___y_1865_ = stack[6].m_obj;
lean_object* v___y_1866_ = stack[7].m_obj;
lean_object* v_res_1936_;
v_res_1936_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(v_msg_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
stack->m_obj
 = v_res_1936_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___boxed(lean_object* v_msg_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_){
_start:
{
lean_object* v_res_1946_; 
v_res_1946_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(v_msg_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
lean_dec(v___y_1940_);
lean_dec_ref(v___y_1939_);
lean_dec(v___y_1938_);
return v_res_1946_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1___redArg(lean_object* v_f_1947_, lean_object* v_a_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v___y_1957_; lean_object* v___x_1960_; uint8_t v_debug_1961_; 
v___x_1960_ = lean_st_ref_get(v___y_1950_);
v_debug_1961_ = lean_ctor_get_uint8(v___x_1960_, sizeof(void*)*12);
lean_dec(v___x_1960_);
if (v_debug_1961_ == 0)
{
v___y_1957_ = v___y_1950_;
goto v___jp_1956_;
}
else
{
lean_object* v___x_1962_; 
v___x_1962_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_1947_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v___x_1963_; 
lean_dec_ref_known(v___x_1962_, 1);
v___x_1963_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
if (lean_obj_tag(v___x_1963_) == 0)
{
lean_dec_ref_known(v___x_1963_, 1);
v___y_1957_ = v___y_1950_;
goto v___jp_1956_;
}
else
{
lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1971_; 
lean_dec_ref(v_a_1948_);
lean_dec_ref(v_f_1947_);
v_a_1964_ = lean_ctor_get(v___x_1963_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1966_ = v___x_1963_;
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_dec(v___x_1963_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1969_; 
if (v_isShared_1967_ == 0)
{
v___x_1969_ = v___x_1966_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_a_1964_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
}
else
{
lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
lean_dec_ref(v_a_1948_);
lean_dec_ref(v_f_1947_);
v_a_1972_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1974_ = v___x_1962_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_dec(v___x_1962_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1977_; 
if (v_isShared_1975_ == 0)
{
v___x_1977_ = v___x_1974_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_a_1972_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
}
v___jp_1956_:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1958_ = l_Lean_Expr_app___override(v_f_1947_, v_a_1948_);
v___x_1959_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1958_, v___y_1957_);
return v___x_1959_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1947_ = stack[0].m_obj;
lean_object* v_a_1948_ = stack[1].m_obj;
lean_object* v___y_1949_ = stack[2].m_obj;
lean_object* v___y_1950_ = stack[3].m_obj;
lean_object* v___y_1951_ = stack[4].m_obj;
lean_object* v___y_1952_ = stack[5].m_obj;
lean_object* v___y_1953_ = stack[6].m_obj;
lean_object* v___y_1954_ = stack[7].m_obj;
lean_object* v_res_1980_;
v_res_1980_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1___redArg(v_f_1947_, v_a_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
stack->m_obj
 = v_res_1980_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1___redArg___boxed(lean_object* v_f_1981_, lean_object* v_a_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1___redArg(v_f_1981_, v_a_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
return v_res_1990_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1(lean_object* v_f_1991_, lean_object* v_a_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_){
_start:
{
lean_object* v___x_2001_; 
v___x_2001_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1___redArg(v_f_1991_, v_a_1992_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
return v___x_2001_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1991_ = stack[0].m_obj;
lean_object* v_a_1992_ = stack[1].m_obj;
lean_object* v___y_1993_ = stack[2].m_obj;
lean_object* v___y_1994_ = stack[3].m_obj;
lean_object* v___y_1995_ = stack[4].m_obj;
lean_object* v___y_1996_ = stack[5].m_obj;
lean_object* v___y_1997_ = stack[6].m_obj;
lean_object* v___y_1998_ = stack[7].m_obj;
lean_object* v___y_1999_ = stack[8].m_obj;
lean_object* v_res_2002_;
v_res_2002_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1(v_f_1991_, v_a_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
stack->m_obj
 = v_res_2002_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1___boxed(lean_object* v_f_2003_, lean_object* v_a_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1(v_f_2003_, v_a_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
lean_dec(v___y_2005_);
return v_res_2013_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2___redArg(lean_object* v_d_2014_, lean_object* v_e_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_){
_start:
{
lean_object* v___y_2024_; lean_object* v___x_2027_; uint8_t v_debug_2028_; 
v___x_2027_ = lean_st_ref_get(v___y_2017_);
v_debug_2028_ = lean_ctor_get_uint8(v___x_2027_, sizeof(void*)*12);
lean_dec(v___x_2027_);
if (v_debug_2028_ == 0)
{
v___y_2024_ = v___y_2017_;
goto v___jp_2023_;
}
else
{
lean_object* v___x_2029_; 
v___x_2029_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_e_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_dec_ref_known(v___x_2029_, 1);
v___y_2024_ = v___y_2017_;
goto v___jp_2023_;
}
else
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2037_; 
lean_dec_ref(v_e_2015_);
lean_dec(v_d_2014_);
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2032_ = v___x_2029_;
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_2029_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2035_; 
if (v_isShared_2033_ == 0)
{
v___x_2035_ = v___x_2032_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_a_2030_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
}
v___jp_2023_:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2025_ = l_Lean_Expr_mdata___override(v_d_2014_, v_e_2015_);
v___x_2026_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2025_, v___y_2024_);
return v___x_2026_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_2014_ = stack[0].m_obj;
lean_object* v_e_2015_ = stack[1].m_obj;
lean_object* v___y_2016_ = stack[2].m_obj;
lean_object* v___y_2017_ = stack[3].m_obj;
lean_object* v___y_2018_ = stack[4].m_obj;
lean_object* v___y_2019_ = stack[5].m_obj;
lean_object* v___y_2020_ = stack[6].m_obj;
lean_object* v___y_2021_ = stack[7].m_obj;
lean_object* v_res_2038_;
v_res_2038_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2___redArg(v_d_2014_, v_e_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
stack->m_obj
 = v_res_2038_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2___redArg___boxed(lean_object* v_d_2039_, lean_object* v_e_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
lean_object* v_res_2048_; 
v_res_2048_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2___redArg(v_d_2039_, v_e_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
return v_res_2048_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2(lean_object* v_d_2049_, lean_object* v_e_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
lean_object* v___x_2059_; 
v___x_2059_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2___redArg(v_d_2049_, v_e_2050_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
return v___x_2059_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_2049_ = stack[0].m_obj;
lean_object* v_e_2050_ = stack[1].m_obj;
lean_object* v___y_2051_ = stack[2].m_obj;
lean_object* v___y_2052_ = stack[3].m_obj;
lean_object* v___y_2053_ = stack[4].m_obj;
lean_object* v___y_2054_ = stack[5].m_obj;
lean_object* v___y_2055_ = stack[6].m_obj;
lean_object* v___y_2056_ = stack[7].m_obj;
lean_object* v___y_2057_ = stack[8].m_obj;
lean_object* v_res_2060_;
v_res_2060_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2(v_d_2049_, v_e_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
stack->m_obj
 = v_res_2060_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2___boxed(lean_object* v_d_2061_, lean_object* v_e_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2(v_d_2061_, v_e_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
return v_res_2071_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3___redArg(lean_object* v_structName_2072_, lean_object* v_idx_2073_, lean_object* v_struct_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_){
_start:
{
lean_object* v___y_2083_; lean_object* v___x_2086_; uint8_t v_debug_2087_; 
v___x_2086_ = lean_st_ref_get(v___y_2076_);
v_debug_2087_ = lean_ctor_get_uint8(v___x_2086_, sizeof(void*)*12);
lean_dec(v___x_2086_);
if (v_debug_2087_ == 0)
{
v___y_2083_ = v___y_2076_;
goto v___jp_2082_;
}
else
{
lean_object* v___x_2088_; 
v___x_2088_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_struct_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_dec_ref_known(v___x_2088_, 1);
v___y_2083_ = v___y_2076_;
goto v___jp_2082_;
}
else
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
lean_dec_ref(v_struct_2074_);
lean_dec(v_idx_2073_);
lean_dec(v_structName_2072_);
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_2088_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2088_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2092_ == 0)
{
v___x_2094_ = v___x_2091_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2089_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
v___jp_2082_:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2084_ = l_Lean_Expr_proj___override(v_structName_2072_, v_idx_2073_, v_struct_2074_);
v___x_2085_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2084_, v___y_2083_);
return v___x_2085_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_structName_2072_ = stack[0].m_obj;
lean_object* v_idx_2073_ = stack[1].m_obj;
lean_object* v_struct_2074_ = stack[2].m_obj;
lean_object* v___y_2075_ = stack[3].m_obj;
lean_object* v___y_2076_ = stack[4].m_obj;
lean_object* v___y_2077_ = stack[5].m_obj;
lean_object* v___y_2078_ = stack[6].m_obj;
lean_object* v___y_2079_ = stack[7].m_obj;
lean_object* v___y_2080_ = stack[8].m_obj;
lean_object* v_res_2097_;
v_res_2097_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3___redArg(v_structName_2072_, v_idx_2073_, v_struct_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
stack->m_obj
 = v_res_2097_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3___redArg___boxed(lean_object* v_structName_2098_, lean_object* v_idx_2099_, lean_object* v_struct_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
lean_object* v_res_2108_; 
v_res_2108_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3___redArg(v_structName_2098_, v_idx_2099_, v_struct_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
return v_res_2108_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3(lean_object* v_structName_2109_, lean_object* v_idx_2110_, lean_object* v_struct_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_){
_start:
{
lean_object* v___x_2120_; 
v___x_2120_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3___redArg(v_structName_2109_, v_idx_2110_, v_struct_2111_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
return v___x_2120_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_structName_2109_ = stack[0].m_obj;
lean_object* v_idx_2110_ = stack[1].m_obj;
lean_object* v_struct_2111_ = stack[2].m_obj;
lean_object* v___y_2112_ = stack[3].m_obj;
lean_object* v___y_2113_ = stack[4].m_obj;
lean_object* v___y_2114_ = stack[5].m_obj;
lean_object* v___y_2115_ = stack[6].m_obj;
lean_object* v___y_2116_ = stack[7].m_obj;
lean_object* v___y_2117_ = stack[8].m_obj;
lean_object* v___y_2118_ = stack[9].m_obj;
lean_object* v_res_2121_;
v_res_2121_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3(v_structName_2109_, v_idx_2110_, v_struct_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
stack->m_obj
 = v_res_2121_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3___boxed(lean_object* v_structName_2122_, lean_object* v_idx_2123_, lean_object* v_struct_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3(v_structName_2122_, v_idx_2123_, v_struct_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
lean_dec(v___y_2125_);
return v_res_2133_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5_spec__5(lean_object* v_msgData_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
lean_object* v___x_2140_; lean_object* v_env_2141_; uint8_t v___x_2142_; lean_object* v_env_2143_; lean_object* v___x_2144_; lean_object* v_toCold_2145_; lean_object* v_mctx_2146_; lean_object* v_lctx_2147_; lean_object* v_options_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2140_ = lean_st_ref_get(v___y_2138_);
v_env_2141_ = lean_ctor_get(v___x_2140_, 0);
lean_inc_ref(v_env_2141_);
lean_dec(v___x_2140_);
v___x_2142_ = 0;
v_env_2143_ = l_Lean_Environment_setRecordingDeps(v_env_2141_, v___x_2142_);
v___x_2144_ = lean_st_ref_get(v___y_2136_);
v_toCold_2145_ = lean_ctor_get(v___y_2137_, 0);
v_mctx_2146_ = lean_ctor_get(v___x_2144_, 0);
lean_inc_ref(v_mctx_2146_);
lean_dec(v___x_2144_);
v_lctx_2147_ = lean_ctor_get(v___y_2135_, 2);
v_options_2148_ = lean_ctor_get(v_toCold_2145_, 2);
lean_inc_ref(v_options_2148_);
lean_inc_ref(v_lctx_2147_);
v___x_2149_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2149_, 0, v_env_2143_);
lean_ctor_set(v___x_2149_, 1, v_mctx_2146_);
lean_ctor_set(v___x_2149_, 2, v_lctx_2147_);
lean_ctor_set(v___x_2149_, 3, v_options_2148_);
v___x_2150_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2149_);
lean_ctor_set(v___x_2150_, 1, v_msgData_2134_);
v___x_2151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2150_);
return v___x_2151_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2134_ = stack[0].m_obj;
lean_object* v___y_2135_ = stack[1].m_obj;
lean_object* v___y_2136_ = stack[2].m_obj;
lean_object* v___y_2137_ = stack[3].m_obj;
lean_object* v___y_2138_ = stack[4].m_obj;
lean_object* v_res_2152_;
v_res_2152_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5_spec__5(v_msgData_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
stack->m_obj
 = v_res_2152_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5_spec__5___boxed(lean_object* v_msgData_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v_res_2159_; 
v_res_2159_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5_spec__5(v_msgData_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
return v_res_2159_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5___redArg(lean_object* v_msg_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
lean_object* v_ref_2166_; lean_object* v___x_2167_; lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2176_; 
v_ref_2166_ = lean_ctor_get(v___y_2163_, 2);
v___x_2167_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5_spec__5(v_msg_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2170_ = v___x_2167_;
v_isShared_2171_ = v_isSharedCheck_2176_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___x_2167_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2176_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2172_; lean_object* v___x_2174_; 
lean_inc(v_ref_2166_);
v___x_2172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2172_, 0, v_ref_2166_);
lean_ctor_set(v___x_2172_, 1, v_a_2168_);
if (v_isShared_2171_ == 0)
{
lean_ctor_set_tag(v___x_2170_, 1);
lean_ctor_set(v___x_2170_, 0, v___x_2172_);
v___x_2174_ = v___x_2170_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v___x_2172_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2160_ = stack[0].m_obj;
lean_object* v___y_2161_ = stack[1].m_obj;
lean_object* v___y_2162_ = stack[2].m_obj;
lean_object* v___y_2163_ = stack[3].m_obj;
lean_object* v___y_2164_ = stack[4].m_obj;
lean_object* v_res_2177_;
v_res_2177_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5___redArg(v_msg_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
stack->m_obj
 = v_res_2177_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5___redArg___boxed(lean_object* v_msg_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5___redArg(v_msg_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
return v_res_2184_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7___redArg(lean_object* v_a_2185_, lean_object* v_x_2186_){
_start:
{
if (lean_obj_tag(v_x_2186_) == 0)
{
lean_object* v___x_2187_; 
v___x_2187_ = lean_box(0);
return v___x_2187_;
}
else
{
lean_object* v_key_2188_; lean_object* v_value_2189_; lean_object* v_tail_2190_; lean_object* v_fst_2191_; lean_object* v_snd_2192_; lean_object* v_fst_2193_; lean_object* v_snd_2194_; size_t v___x_2195_; size_t v___x_2196_; uint8_t v___x_2197_; 
v_key_2188_ = lean_ctor_get(v_x_2186_, 0);
v_value_2189_ = lean_ctor_get(v_x_2186_, 1);
v_tail_2190_ = lean_ctor_get(v_x_2186_, 2);
v_fst_2191_ = lean_ctor_get(v_key_2188_, 0);
v_snd_2192_ = lean_ctor_get(v_key_2188_, 1);
v_fst_2193_ = lean_ctor_get(v_a_2185_, 0);
v_snd_2194_ = lean_ctor_get(v_a_2185_, 1);
v___x_2195_ = lean_ptr_addr(v_fst_2191_);
v___x_2196_ = lean_ptr_addr(v_fst_2193_);
v___x_2197_ = lean_usize_dec_eq(v___x_2195_, v___x_2196_);
if (v___x_2197_ == 0)
{
v_x_2186_ = v_tail_2190_;
goto _start;
}
else
{
size_t v___x_2199_; size_t v___x_2200_; uint8_t v___x_2201_; 
v___x_2199_ = lean_ptr_addr(v_snd_2192_);
v___x_2200_ = lean_ptr_addr(v_snd_2194_);
v___x_2201_ = lean_usize_dec_eq(v___x_2199_, v___x_2200_);
if (v___x_2201_ == 0)
{
v_x_2186_ = v_tail_2190_;
goto _start;
}
else
{
lean_object* v___x_2203_; 
lean_inc(v_value_2189_);
v___x_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2203_, 0, v_value_2189_);
return v___x_2203_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7___redArg___boxed(lean_object* v_a_2204_, lean_object* v_x_2205_){
_start:
{
lean_object* v_res_2206_; 
v_res_2206_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7___redArg(v_a_2204_, v_x_2205_);
lean_dec(v_x_2205_);
lean_dec_ref(v_a_2204_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6___redArg(lean_object* v_m_2207_, lean_object* v_a_2208_){
_start:
{
lean_object* v_buckets_2209_; lean_object* v_fst_2210_; lean_object* v_snd_2211_; lean_object* v___x_2212_; size_t v___x_2213_; size_t v___x_2214_; size_t v___x_2215_; uint64_t v___x_2216_; size_t v___x_2217_; size_t v___x_2218_; uint64_t v___x_2219_; uint64_t v___x_2220_; uint64_t v___x_2221_; uint64_t v___x_2222_; uint64_t v_fold_2223_; uint64_t v___x_2224_; uint64_t v___x_2225_; uint64_t v___x_2226_; size_t v___x_2227_; size_t v___x_2228_; size_t v___x_2229_; size_t v___x_2230_; size_t v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v_buckets_2209_ = lean_ctor_get(v_m_2207_, 1);
v_fst_2210_ = lean_ctor_get(v_a_2208_, 0);
v_snd_2211_ = lean_ctor_get(v_a_2208_, 1);
v___x_2212_ = lean_array_get_size(v_buckets_2209_);
v___x_2213_ = lean_ptr_addr(v_fst_2210_);
v___x_2214_ = ((size_t)3ULL);
v___x_2215_ = lean_usize_shift_right(v___x_2213_, v___x_2214_);
v___x_2216_ = lean_usize_to_uint64(v___x_2215_);
v___x_2217_ = lean_ptr_addr(v_snd_2211_);
v___x_2218_ = lean_usize_shift_right(v___x_2217_, v___x_2214_);
v___x_2219_ = lean_usize_to_uint64(v___x_2218_);
v___x_2220_ = lean_uint64_mix_hash(v___x_2216_, v___x_2219_);
v___x_2221_ = 32ULL;
v___x_2222_ = lean_uint64_shift_right(v___x_2220_, v___x_2221_);
v_fold_2223_ = lean_uint64_xor(v___x_2220_, v___x_2222_);
v___x_2224_ = 16ULL;
v___x_2225_ = lean_uint64_shift_right(v_fold_2223_, v___x_2224_);
v___x_2226_ = lean_uint64_xor(v_fold_2223_, v___x_2225_);
v___x_2227_ = lean_uint64_to_usize(v___x_2226_);
v___x_2228_ = lean_usize_of_nat(v___x_2212_);
v___x_2229_ = ((size_t)1ULL);
v___x_2230_ = lean_usize_sub(v___x_2228_, v___x_2229_);
v___x_2231_ = lean_usize_land(v___x_2227_, v___x_2230_);
v___x_2232_ = lean_array_uget_borrowed(v_buckets_2209_, v___x_2231_);
v___x_2233_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7___redArg(v_a_2208_, v___x_2232_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6___redArg___boxed(lean_object* v_m_2234_, lean_object* v_a_2235_){
_start:
{
lean_object* v_res_2236_; 
v_res_2236_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6___redArg(v_m_2234_, v_a_2235_);
lean_dec_ref(v_a_2235_);
lean_dec_ref(v_m_2234_);
return v_res_2236_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9___redArg(lean_object* v_a_2237_, lean_object* v_x_2238_){
_start:
{
if (lean_obj_tag(v_x_2238_) == 0)
{
uint8_t v___x_2239_; 
v___x_2239_ = 0;
return v___x_2239_;
}
else
{
lean_object* v_key_2240_; lean_object* v_tail_2241_; lean_object* v_fst_2242_; lean_object* v_snd_2243_; lean_object* v_fst_2244_; lean_object* v_snd_2245_; size_t v___x_2246_; size_t v___x_2247_; uint8_t v___x_2248_; 
v_key_2240_ = lean_ctor_get(v_x_2238_, 0);
v_tail_2241_ = lean_ctor_get(v_x_2238_, 2);
v_fst_2242_ = lean_ctor_get(v_key_2240_, 0);
v_snd_2243_ = lean_ctor_get(v_key_2240_, 1);
v_fst_2244_ = lean_ctor_get(v_a_2237_, 0);
v_snd_2245_ = lean_ctor_get(v_a_2237_, 1);
v___x_2246_ = lean_ptr_addr(v_fst_2242_);
v___x_2247_ = lean_ptr_addr(v_fst_2244_);
v___x_2248_ = lean_usize_dec_eq(v___x_2246_, v___x_2247_);
if (v___x_2248_ == 0)
{
v_x_2238_ = v_tail_2241_;
goto _start;
}
else
{
size_t v___x_2250_; size_t v___x_2251_; uint8_t v___x_2252_; 
v___x_2250_ = lean_ptr_addr(v_snd_2243_);
v___x_2251_ = lean_ptr_addr(v_snd_2245_);
v___x_2252_ = lean_usize_dec_eq(v___x_2250_, v___x_2251_);
if (v___x_2252_ == 0)
{
v_x_2238_ = v_tail_2241_;
goto _start;
}
else
{
return v___x_2252_;
}
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2237_ = stack[0].m_obj;
lean_object* v_x_2238_ = stack[1].m_obj;
uint8_t v_res_2254_;
v_res_2254_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9___redArg(v_a_2237_, v_x_2238_);
stack->m_num = v_res_2254_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9___redArg___boxed(lean_object* v_a_2255_, lean_object* v_x_2256_){
_start:
{
uint8_t v_res_2257_; lean_object* v_r_2258_; 
v_res_2257_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9___redArg(v_a_2255_, v_x_2256_);
lean_dec(v_x_2256_);
lean_dec_ref(v_a_2255_);
v_r_2258_ = lean_box(v_res_2257_);
return v_r_2258_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__11___redArg(lean_object* v_a_2259_, lean_object* v_b_2260_, lean_object* v_x_2261_){
_start:
{
if (lean_obj_tag(v_x_2261_) == 0)
{
lean_dec(v_b_2260_);
lean_dec_ref(v_a_2259_);
return v_x_2261_;
}
else
{
lean_object* v_key_2262_; lean_object* v_value_2263_; lean_object* v_tail_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2284_; 
v_key_2262_ = lean_ctor_get(v_x_2261_, 0);
v_value_2263_ = lean_ctor_get(v_x_2261_, 1);
v_tail_2264_ = lean_ctor_get(v_x_2261_, 2);
v_isSharedCheck_2284_ = !lean_is_exclusive(v_x_2261_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2266_ = v_x_2261_;
v_isShared_2267_ = v_isSharedCheck_2284_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_tail_2264_);
lean_inc(v_value_2263_);
lean_inc(v_key_2262_);
lean_dec(v_x_2261_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2284_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v_fst_2273_; lean_object* v_snd_2274_; lean_object* v_fst_2275_; lean_object* v_snd_2276_; size_t v___x_2277_; size_t v___x_2278_; uint8_t v___x_2279_; 
v_fst_2273_ = lean_ctor_get(v_key_2262_, 0);
v_snd_2274_ = lean_ctor_get(v_key_2262_, 1);
v_fst_2275_ = lean_ctor_get(v_a_2259_, 0);
v_snd_2276_ = lean_ctor_get(v_a_2259_, 1);
v___x_2277_ = lean_ptr_addr(v_fst_2273_);
v___x_2278_ = lean_ptr_addr(v_fst_2275_);
v___x_2279_ = lean_usize_dec_eq(v___x_2277_, v___x_2278_);
if (v___x_2279_ == 0)
{
goto v___jp_2268_;
}
else
{
size_t v___x_2280_; size_t v___x_2281_; uint8_t v___x_2282_; 
v___x_2280_ = lean_ptr_addr(v_snd_2274_);
v___x_2281_ = lean_ptr_addr(v_snd_2276_);
v___x_2282_ = lean_usize_dec_eq(v___x_2280_, v___x_2281_);
if (v___x_2282_ == 0)
{
goto v___jp_2268_;
}
else
{
lean_object* v___x_2283_; 
lean_del_object(v___x_2266_);
lean_dec(v_value_2263_);
lean_dec(v_key_2262_);
v___x_2283_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2283_, 0, v_a_2259_);
lean_ctor_set(v___x_2283_, 1, v_b_2260_);
lean_ctor_set(v___x_2283_, 2, v_tail_2264_);
return v___x_2283_;
}
}
v___jp_2268_:
{
lean_object* v___x_2269_; lean_object* v___x_2271_; 
v___x_2269_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__11___redArg(v_a_2259_, v_b_2260_, v_tail_2264_);
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 2, v___x_2269_);
v___x_2271_ = v___x_2266_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_key_2262_);
lean_ctor_set(v_reuseFailAlloc_2272_, 1, v_value_2263_);
lean_ctor_set(v_reuseFailAlloc_2272_, 2, v___x_2269_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10_spec__11_spec__12___redArg(lean_object* v_x_2285_, lean_object* v_x_2286_){
_start:
{
if (lean_obj_tag(v_x_2286_) == 0)
{
return v_x_2285_;
}
else
{
lean_object* v_key_2287_; lean_object* v_value_2288_; lean_object* v_tail_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2321_; 
v_key_2287_ = lean_ctor_get(v_x_2286_, 0);
v_value_2288_ = lean_ctor_get(v_x_2286_, 1);
v_tail_2289_ = lean_ctor_get(v_x_2286_, 2);
v_isSharedCheck_2321_ = !lean_is_exclusive(v_x_2286_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2291_ = v_x_2286_;
v_isShared_2292_ = v_isSharedCheck_2321_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_tail_2289_);
lean_inc(v_value_2288_);
lean_inc(v_key_2287_);
lean_dec(v_x_2286_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2321_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v_fst_2293_; lean_object* v_snd_2294_; lean_object* v___x_2295_; size_t v___x_2296_; size_t v___x_2297_; size_t v___x_2298_; uint64_t v___x_2299_; size_t v___x_2300_; size_t v___x_2301_; uint64_t v___x_2302_; uint64_t v___x_2303_; uint64_t v___x_2304_; uint64_t v___x_2305_; uint64_t v_fold_2306_; uint64_t v___x_2307_; uint64_t v___x_2308_; uint64_t v___x_2309_; size_t v___x_2310_; size_t v___x_2311_; size_t v___x_2312_; size_t v___x_2313_; size_t v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2317_; 
v_fst_2293_ = lean_ctor_get(v_key_2287_, 0);
v_snd_2294_ = lean_ctor_get(v_key_2287_, 1);
v___x_2295_ = lean_array_get_size(v_x_2285_);
v___x_2296_ = lean_ptr_addr(v_fst_2293_);
v___x_2297_ = ((size_t)3ULL);
v___x_2298_ = lean_usize_shift_right(v___x_2296_, v___x_2297_);
v___x_2299_ = lean_usize_to_uint64(v___x_2298_);
v___x_2300_ = lean_ptr_addr(v_snd_2294_);
v___x_2301_ = lean_usize_shift_right(v___x_2300_, v___x_2297_);
v___x_2302_ = lean_usize_to_uint64(v___x_2301_);
v___x_2303_ = lean_uint64_mix_hash(v___x_2299_, v___x_2302_);
v___x_2304_ = 32ULL;
v___x_2305_ = lean_uint64_shift_right(v___x_2303_, v___x_2304_);
v_fold_2306_ = lean_uint64_xor(v___x_2303_, v___x_2305_);
v___x_2307_ = 16ULL;
v___x_2308_ = lean_uint64_shift_right(v_fold_2306_, v___x_2307_);
v___x_2309_ = lean_uint64_xor(v_fold_2306_, v___x_2308_);
v___x_2310_ = lean_uint64_to_usize(v___x_2309_);
v___x_2311_ = lean_usize_of_nat(v___x_2295_);
v___x_2312_ = ((size_t)1ULL);
v___x_2313_ = lean_usize_sub(v___x_2311_, v___x_2312_);
v___x_2314_ = lean_usize_land(v___x_2310_, v___x_2313_);
v___x_2315_ = lean_array_uget_borrowed(v_x_2285_, v___x_2314_);
lean_inc(v___x_2315_);
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 2, v___x_2315_);
v___x_2317_ = v___x_2291_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_key_2287_);
lean_ctor_set(v_reuseFailAlloc_2320_, 1, v_value_2288_);
lean_ctor_set(v_reuseFailAlloc_2320_, 2, v___x_2315_);
v___x_2317_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
lean_object* v___x_2318_; 
v___x_2318_ = lean_array_uset(v_x_2285_, v___x_2314_, v___x_2317_);
v_x_2285_ = v___x_2318_;
v_x_2286_ = v_tail_2289_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10_spec__11___redArg(lean_object* v_i_2322_, lean_object* v_source_2323_, lean_object* v_target_2324_){
_start:
{
lean_object* v___x_2325_; uint8_t v___x_2326_; 
v___x_2325_ = lean_array_get_size(v_source_2323_);
v___x_2326_ = lean_nat_dec_lt(v_i_2322_, v___x_2325_);
if (v___x_2326_ == 0)
{
lean_dec_ref(v_source_2323_);
lean_dec(v_i_2322_);
return v_target_2324_;
}
else
{
lean_object* v_es_2327_; lean_object* v___x_2328_; lean_object* v_source_2329_; lean_object* v_target_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v_es_2327_ = lean_array_fget(v_source_2323_, v_i_2322_);
v___x_2328_ = lean_box(0);
v_source_2329_ = lean_array_fset(v_source_2323_, v_i_2322_, v___x_2328_);
v_target_2330_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10_spec__11_spec__12___redArg(v_target_2324_, v_es_2327_);
v___x_2331_ = lean_unsigned_to_nat(1u);
v___x_2332_ = lean_nat_add(v_i_2322_, v___x_2331_);
lean_dec(v_i_2322_);
v_i_2322_ = v___x_2332_;
v_source_2323_ = v_source_2329_;
v_target_2324_ = v_target_2330_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10___redArg(lean_object* v_data_2334_){
_start:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v_nbuckets_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2335_ = lean_array_get_size(v_data_2334_);
v___x_2336_ = lean_unsigned_to_nat(2u);
v_nbuckets_2337_ = lean_nat_mul(v___x_2335_, v___x_2336_);
v___x_2338_ = lean_unsigned_to_nat(0u);
v___x_2339_ = lean_box(0);
v___x_2340_ = lean_mk_array(v_nbuckets_2337_, v___x_2339_);
v___x_2341_ = lean_array_propagate_mark(v_data_2334_, v___x_2340_);
v___x_2342_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10_spec__11___redArg(v___x_2338_, v_data_2334_, v___x_2341_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7___redArg(lean_object* v_m_2343_, lean_object* v_a_2344_, lean_object* v_b_2345_){
_start:
{
lean_object* v_size_2346_; lean_object* v_buckets_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2399_; 
v_size_2346_ = lean_ctor_get(v_m_2343_, 0);
v_buckets_2347_ = lean_ctor_get(v_m_2343_, 1);
v_isSharedCheck_2399_ = !lean_is_exclusive(v_m_2343_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2349_ = v_m_2343_;
v_isShared_2350_ = v_isSharedCheck_2399_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_buckets_2347_);
lean_inc(v_size_2346_);
lean_dec(v_m_2343_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2399_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v_fst_2351_; lean_object* v_snd_2352_; lean_object* v___x_2353_; size_t v___x_2354_; size_t v___x_2355_; size_t v___x_2356_; uint64_t v___x_2357_; size_t v___x_2358_; size_t v___x_2359_; uint64_t v___x_2360_; uint64_t v___x_2361_; uint64_t v___x_2362_; uint64_t v___x_2363_; uint64_t v_fold_2364_; uint64_t v___x_2365_; uint64_t v___x_2366_; uint64_t v___x_2367_; size_t v___x_2368_; size_t v___x_2369_; size_t v___x_2370_; size_t v___x_2371_; size_t v___x_2372_; lean_object* v_bkt_2373_; uint8_t v___x_2374_; 
v_fst_2351_ = lean_ctor_get(v_a_2344_, 0);
v_snd_2352_ = lean_ctor_get(v_a_2344_, 1);
v___x_2353_ = lean_array_get_size(v_buckets_2347_);
v___x_2354_ = lean_ptr_addr(v_fst_2351_);
v___x_2355_ = ((size_t)3ULL);
v___x_2356_ = lean_usize_shift_right(v___x_2354_, v___x_2355_);
v___x_2357_ = lean_usize_to_uint64(v___x_2356_);
v___x_2358_ = lean_ptr_addr(v_snd_2352_);
v___x_2359_ = lean_usize_shift_right(v___x_2358_, v___x_2355_);
v___x_2360_ = lean_usize_to_uint64(v___x_2359_);
v___x_2361_ = lean_uint64_mix_hash(v___x_2357_, v___x_2360_);
v___x_2362_ = 32ULL;
v___x_2363_ = lean_uint64_shift_right(v___x_2361_, v___x_2362_);
v_fold_2364_ = lean_uint64_xor(v___x_2361_, v___x_2363_);
v___x_2365_ = 16ULL;
v___x_2366_ = lean_uint64_shift_right(v_fold_2364_, v___x_2365_);
v___x_2367_ = lean_uint64_xor(v_fold_2364_, v___x_2366_);
v___x_2368_ = lean_uint64_to_usize(v___x_2367_);
v___x_2369_ = lean_usize_of_nat(v___x_2353_);
v___x_2370_ = ((size_t)1ULL);
v___x_2371_ = lean_usize_sub(v___x_2369_, v___x_2370_);
v___x_2372_ = lean_usize_land(v___x_2368_, v___x_2371_);
v_bkt_2373_ = lean_array_uget_borrowed(v_buckets_2347_, v___x_2372_);
v___x_2374_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9___redArg(v_a_2344_, v_bkt_2373_);
if (v___x_2374_ == 0)
{
lean_object* v___x_2375_; lean_object* v_size_x27_2376_; lean_object* v___x_2377_; lean_object* v_buckets_x27_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; uint8_t v___x_2384_; 
v___x_2375_ = lean_unsigned_to_nat(1u);
v_size_x27_2376_ = lean_nat_add(v_size_2346_, v___x_2375_);
lean_dec(v_size_2346_);
lean_inc(v_bkt_2373_);
v___x_2377_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2377_, 0, v_a_2344_);
lean_ctor_set(v___x_2377_, 1, v_b_2345_);
lean_ctor_set(v___x_2377_, 2, v_bkt_2373_);
v_buckets_x27_2378_ = lean_array_uset(v_buckets_2347_, v___x_2372_, v___x_2377_);
v___x_2379_ = lean_unsigned_to_nat(4u);
v___x_2380_ = lean_nat_mul(v_size_x27_2376_, v___x_2379_);
v___x_2381_ = lean_unsigned_to_nat(3u);
v___x_2382_ = lean_nat_div(v___x_2380_, v___x_2381_);
lean_dec(v___x_2380_);
v___x_2383_ = lean_array_get_size(v_buckets_x27_2378_);
v___x_2384_ = lean_nat_dec_le(v___x_2382_, v___x_2383_);
lean_dec(v___x_2382_);
if (v___x_2384_ == 0)
{
lean_object* v_val_2385_; lean_object* v___x_2387_; 
v_val_2385_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10___redArg(v_buckets_x27_2378_);
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 1, v_val_2385_);
lean_ctor_set(v___x_2349_, 0, v_size_x27_2376_);
v___x_2387_ = v___x_2349_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_size_x27_2376_);
lean_ctor_set(v_reuseFailAlloc_2388_, 1, v_val_2385_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
else
{
lean_object* v___x_2390_; 
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 1, v_buckets_x27_2378_);
lean_ctor_set(v___x_2349_, 0, v_size_x27_2376_);
v___x_2390_ = v___x_2349_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v_size_x27_2376_);
lean_ctor_set(v_reuseFailAlloc_2391_, 1, v_buckets_x27_2378_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
}
else
{
lean_object* v___x_2392_; lean_object* v_buckets_x27_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2397_; 
lean_inc(v_bkt_2373_);
v___x_2392_ = lean_box(0);
v_buckets_x27_2393_ = lean_array_uset(v_buckets_2347_, v___x_2372_, v___x_2392_);
v___x_2394_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__11___redArg(v_a_2344_, v_b_2345_, v_bkt_2373_);
v___x_2395_ = lean_array_uset(v_buckets_x27_2393_, v___x_2372_, v___x_2394_);
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 1, v___x_2395_);
v___x_2397_ = v___x_2349_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_size_2346_);
lean_ctor_set(v_reuseFailAlloc_2398_, 1, v___x_2395_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__1(void){
_start:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2401_ = ((lean_object*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__0));
v___x_2402_ = l_Lean_stringToMessageData(v___x_2401_);
return v___x_2402_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__2(void){
_start:
{
lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2403_ = lean_unsigned_to_nat(32u);
v___x_2404_ = lean_mk_empty_array_with_capacity(v___x_2403_);
v___x_2405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2404_);
return v___x_2405_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__3(void){
_start:
{
size_t v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2406_ = ((size_t)5ULL);
v___x_2407_ = lean_unsigned_to_nat(0u);
v___x_2408_ = lean_unsigned_to_nat(32u);
v___x_2409_ = lean_mk_empty_array_with_capacity(v___x_2408_);
v___x_2410_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__2);
v___x_2411_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2411_, 0, v___x_2410_);
lean_ctor_set(v___x_2411_, 1, v___x_2409_);
lean_ctor_set(v___x_2411_, 2, v___x_2407_);
lean_ctor_set(v___x_2411_, 3, v___x_2407_);
lean_ctor_set_usize(v___x_2411_, 4, v___x_2406_);
return v___x_2411_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2(void){
_start:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2414_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__2));
v___x_2415_ = lean_unsigned_to_nat(73u);
v___x_2416_ = lean_unsigned_to_nat(213u);
v___x_2417_ = ((lean_object*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__1));
v___x_2418_ = ((lean_object*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__0));
v___x_2419_ = l_mkPanicMessageWithDecl(v___x_2418_, v___x_2417_, v___x_2416_, v___x_2415_, v___x_2414_);
return v___x_2419_;
}
}
lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit(lean_object* v_xs_2420_, lean_object* v_e_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_){
_start:
{
switch(lean_obj_tag(v_e_2421_))
{
case 0:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; 
lean_dec_ref_known(v_e_2421_, 1);
lean_dec_ref(v_xs_2420_);
v___x_2430_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2);
v___x_2431_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(v___x_2430_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_);
return v___x_2431_;
}
case 1:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; 
lean_dec_ref_known(v_e_2421_, 1);
lean_dec_ref(v_xs_2420_);
v___x_2432_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2);
v___x_2433_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(v___x_2432_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_);
return v___x_2433_;
}
case 2:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; 
lean_dec_ref_known(v_e_2421_, 1);
lean_dec_ref(v_xs_2420_);
v___x_2434_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2);
v___x_2435_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(v___x_2434_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_);
return v___x_2435_;
}
case 3:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; 
lean_dec_ref_known(v_e_2421_, 1);
lean_dec_ref(v_xs_2420_);
v___x_2436_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2);
v___x_2437_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(v___x_2436_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_);
return v___x_2437_;
}
case 4:
{
lean_object* v___x_2438_; lean_object* v___x_2439_; 
lean_dec_ref_known(v_e_2421_, 2);
lean_dec_ref(v_xs_2420_);
v___x_2438_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2);
v___x_2439_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(v___x_2438_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_);
return v___x_2439_;
}
case 5:
{
lean_object* v_fn_2440_; lean_object* v_arg_2441_; lean_object* v___x_2442_; 
v_fn_2440_ = lean_ctor_get(v_e_2421_, 0);
v_arg_2441_ = lean_ctor_get(v_e_2421_, 1);
lean_inc_ref(v_fn_2440_);
lean_inc_ref(v_xs_2420_);
v___x_2442_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v_xs_2420_, v_fn_2440_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v_a_2443_; lean_object* v___x_2444_; 
v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
lean_inc(v_a_2443_);
lean_dec_ref_known(v___x_2442_, 1);
lean_inc_ref(v_arg_2441_);
v___x_2444_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v_xs_2420_, v_arg_2441_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_);
if (lean_obj_tag(v___x_2444_) == 0)
{
lean_object* v_a_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2460_; 
v_a_2445_ = lean_ctor_get(v___x_2444_, 0);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2447_ = v___x_2444_;
v_isShared_2448_ = v_isSharedCheck_2460_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_a_2445_);
lean_dec(v___x_2444_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2460_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
size_t v___x_2449_; size_t v___x_2450_; uint8_t v___x_2451_; 
v___x_2449_ = lean_ptr_addr(v_fn_2440_);
v___x_2450_ = lean_ptr_addr(v_a_2443_);
v___x_2451_ = lean_usize_dec_eq(v___x_2449_, v___x_2450_);
if (v___x_2451_ == 0)
{
lean_object* v___x_2452_; 
lean_del_object(v___x_2447_);
lean_dec_ref_known(v_e_2421_, 2);
v___x_2452_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1___redArg(v_a_2443_, v_a_2445_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_);
return v___x_2452_;
}
else
{
size_t v___x_2453_; size_t v___x_2454_; uint8_t v___x_2455_; 
v___x_2453_ = lean_ptr_addr(v_arg_2441_);
v___x_2454_ = lean_ptr_addr(v_a_2445_);
v___x_2455_ = lean_usize_dec_eq(v___x_2453_, v___x_2454_);
if (v___x_2455_ == 0)
{
lean_object* v___x_2456_; 
lean_del_object(v___x_2447_);
lean_dec_ref_known(v_e_2421_, 2);
v___x_2456_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1___redArg(v_a_2443_, v_a_2445_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_);
return v___x_2456_;
}
else
{
lean_object* v___x_2458_; 
lean_dec(v_a_2445_);
lean_dec(v_a_2443_);
if (v_isShared_2448_ == 0)
{
lean_ctor_set(v___x_2447_, 0, v_e_2421_);
v___x_2458_ = v___x_2447_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_e_2421_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
return v___x_2458_;
}
}
}
}
}
else
{
lean_dec(v_a_2443_);
lean_dec_ref_known(v_e_2421_, 2);
return v___x_2444_;
}
}
else
{
lean_dec_ref_known(v_e_2421_, 2);
lean_dec_ref(v_xs_2420_);
return v___x_2442_;
}
}
case 8:
{
lean_object* v_declName_2461_; lean_object* v_type_2462_; lean_object* v_value_2463_; lean_object* v_body_2464_; uint8_t v_nondep_2465_; lean_object* v___x_2466_; 
v_declName_2461_ = lean_ctor_get(v_e_2421_, 0);
lean_inc(v_declName_2461_);
v_type_2462_ = lean_ctor_get(v_e_2421_, 1);
lean_inc_ref(v_type_2462_);
v_value_2463_ = lean_ctor_get(v_e_2421_, 2);
lean_inc_ref(v_value_2463_);
v_body_2464_ = lean_ctor_get(v_e_2421_, 3);
lean_inc_ref(v_body_2464_);
v_nondep_2465_ = lean_ctor_get_uint8(v_e_2421_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2421_, 4);
lean_inc_ref(v_xs_2420_);
v___x_2466_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v_xs_2420_, v_type_2462_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_object* v_a_2467_; lean_object* v___x_2468_; 
v_a_2467_ = lean_ctor_get(v___x_2466_, 0);
lean_inc(v_a_2467_);
lean_dec_ref_known(v___x_2466_, 1);
lean_inc_ref(v_xs_2420_);
v___x_2468_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v_xs_2420_, v_value_2463_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_);
if (lean_obj_tag(v___x_2468_) == 0)
{
lean_object* v_a_2469_; lean_object* v___x_2470_; 
v_a_2469_ = lean_ctor_get(v___x_2468_, 0);
lean_inc(v_a_2469_);
lean_dec_ref_known(v___x_2468_, 1);
v___x_2470_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl(v_declName_2461_, v_a_2467_, v_a_2469_, v_nondep_2465_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_);
if (lean_obj_tag(v___x_2470_) == 0)
{
lean_object* v_a_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
v_a_2471_ = lean_ctor_get(v___x_2470_, 0);
lean_inc(v_a_2471_);
lean_dec_ref_known(v___x_2470_, 1);
v___x_2472_ = l_Lean_PersistentArray_push___redArg(v_xs_2420_, v_a_2471_);
v___x_2473_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v___x_2472_, v_body_2464_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_);
return v___x_2473_;
}
else
{
lean_dec_ref(v_body_2464_);
lean_dec_ref(v_xs_2420_);
return v___x_2470_;
}
}
else
{
lean_dec(v_a_2467_);
lean_dec_ref(v_body_2464_);
lean_dec(v_declName_2461_);
lean_dec_ref(v_xs_2420_);
return v___x_2468_;
}
}
else
{
lean_dec_ref(v_body_2464_);
lean_dec_ref(v_value_2463_);
lean_dec(v_declName_2461_);
lean_dec_ref(v_xs_2420_);
return v___x_2466_;
}
}
case 9:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; 
lean_dec_ref_known(v_e_2421_, 1);
lean_dec_ref(v_xs_2420_);
v___x_2474_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2);
v___x_2475_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(v___x_2474_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_);
return v___x_2475_;
}
case 10:
{
lean_object* v_data_2476_; lean_object* v_expr_2477_; lean_object* v___x_2478_; 
v_data_2476_ = lean_ctor_get(v_e_2421_, 0);
v_expr_2477_ = lean_ctor_get(v_e_2421_, 1);
lean_inc_ref(v_expr_2477_);
v___x_2478_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v_xs_2420_, v_expr_2477_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_);
if (lean_obj_tag(v___x_2478_) == 0)
{
lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2490_; 
v_a_2479_ = lean_ctor_get(v___x_2478_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2481_ = v___x_2478_;
v_isShared_2482_ = v_isSharedCheck_2490_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___x_2478_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2490_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
size_t v___x_2483_; size_t v___x_2484_; uint8_t v___x_2485_; 
v___x_2483_ = lean_ptr_addr(v_expr_2477_);
v___x_2484_ = lean_ptr_addr(v_a_2479_);
v___x_2485_ = lean_usize_dec_eq(v___x_2483_, v___x_2484_);
if (v___x_2485_ == 0)
{
lean_object* v___x_2486_; 
lean_inc(v_data_2476_);
lean_del_object(v___x_2481_);
lean_dec_ref_known(v_e_2421_, 2);
v___x_2486_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2___redArg(v_data_2476_, v_a_2479_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_);
return v___x_2486_;
}
else
{
lean_object* v___x_2488_; 
lean_dec(v_a_2479_);
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 0, v_e_2421_);
v___x_2488_ = v___x_2481_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_e_2421_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2421_, 2);
return v___x_2478_;
}
}
case 11:
{
lean_object* v_typeName_2491_; lean_object* v_idx_2492_; lean_object* v_struct_2493_; lean_object* v___x_2494_; 
v_typeName_2491_ = lean_ctor_get(v_e_2421_, 0);
v_idx_2492_ = lean_ctor_get(v_e_2421_, 1);
v_struct_2493_ = lean_ctor_get(v_e_2421_, 2);
lean_inc_ref(v_struct_2493_);
v___x_2494_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v_xs_2420_, v_struct_2493_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_);
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2506_; 
v_a_2495_ = lean_ctor_get(v___x_2494_, 0);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2497_ = v___x_2494_;
v_isShared_2498_ = v_isSharedCheck_2506_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2494_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2506_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
size_t v___x_2499_; size_t v___x_2500_; uint8_t v___x_2501_; 
v___x_2499_ = lean_ptr_addr(v_struct_2493_);
v___x_2500_ = lean_ptr_addr(v_a_2495_);
v___x_2501_ = lean_usize_dec_eq(v___x_2499_, v___x_2500_);
if (v___x_2501_ == 0)
{
lean_object* v___x_2502_; 
lean_inc(v_idx_2492_);
lean_inc(v_typeName_2491_);
lean_del_object(v___x_2497_);
lean_dec_ref_known(v_e_2421_, 3);
v___x_2502_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3___redArg(v_typeName_2491_, v_idx_2492_, v_a_2495_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_);
return v___x_2502_;
}
else
{
lean_object* v___x_2504_; 
lean_dec(v_a_2495_);
if (v_isShared_2498_ == 0)
{
lean_ctor_set(v___x_2497_, 0, v_e_2421_);
v___x_2504_ = v___x_2497_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_e_2421_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2421_, 3);
return v___x_2494_;
}
}
default: 
{
lean_object* v___x_2507_; 
v___x_2507_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg(v_xs_2420_, v_e_2421_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_);
return v___x_2507_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_2420_ = stack[0].m_obj;
lean_object* v_e_2421_ = stack[1].m_obj;
lean_object* v_a_2422_ = stack[2].m_obj;
lean_object* v_a_2423_ = stack[3].m_obj;
lean_object* v_a_2424_ = stack[4].m_obj;
lean_object* v_a_2425_ = stack[5].m_obj;
lean_object* v_a_2426_ = stack[6].m_obj;
lean_object* v_a_2427_ = stack[7].m_obj;
lean_object* v_a_2428_ = stack[8].m_obj;
lean_object* v_res_2508_;
v_res_2508_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit(v_xs_2420_, v_e_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_);
stack->m_obj
 = v_res_2508_;
}
lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(lean_object* v_xs_2509_, lean_object* v_e_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_){
_start:
{
switch(lean_obj_tag(v_e_2510_))
{
case 0:
{
lean_object* v_deBruijnIndex_2519_; lean_object* v_size_2520_; uint8_t v___x_2521_; 
v_deBruijnIndex_2519_ = lean_ctor_get(v_e_2510_, 0);
lean_inc(v_deBruijnIndex_2519_);
lean_dec_ref_known(v_e_2510_, 1);
v_size_2520_ = lean_ctor_get(v_xs_2509_, 2);
v___x_2521_ = lean_nat_dec_lt(v_deBruijnIndex_2519_, v_size_2520_);
if (v___x_2521_ == 0)
{
lean_object* v___x_2522_; lean_object* v___x_2523_; 
lean_dec(v_deBruijnIndex_2519_);
lean_dec_ref(v_xs_2509_);
v___x_2522_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__1, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__1_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__1);
v___x_2523_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5___redArg(v___x_2522_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_);
return v___x_2523_;
}
else
{
lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2524_ = l_Lean_instInhabitedExpr;
v___x_2525_ = lean_nat_sub(v_size_2520_, v_deBruijnIndex_2519_);
lean_dec(v_deBruijnIndex_2519_);
v___x_2526_ = lean_unsigned_to_nat(1u);
v___x_2527_ = lean_nat_sub(v___x_2525_, v___x_2526_);
lean_dec(v___x_2525_);
v___x_2528_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2524_, v_xs_2509_, v___x_2527_);
lean_dec(v___x_2527_);
lean_dec_ref(v_xs_2509_);
v___x_2529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2528_);
return v___x_2529_;
}
}
case 1:
{
lean_object* v___x_2530_; 
lean_dec_ref(v_xs_2509_);
v___x_2530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2530_, 0, v_e_2510_);
return v___x_2530_;
}
case 2:
{
lean_object* v___x_2531_; 
lean_dec_ref(v_xs_2509_);
v___x_2531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2531_, 0, v_e_2510_);
return v___x_2531_;
}
case 3:
{
lean_object* v___x_2532_; 
lean_dec_ref(v_xs_2509_);
v___x_2532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2532_, 0, v_e_2510_);
return v___x_2532_;
}
case 4:
{
lean_object* v___x_2533_; 
lean_dec_ref(v_xs_2509_);
v___x_2533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2533_, 0, v_e_2510_);
return v___x_2533_;
}
case 9:
{
lean_object* v___x_2534_; 
lean_dec_ref(v_xs_2509_);
v___x_2534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2534_, 0, v_e_2510_);
return v___x_2534_;
}
default: 
{
uint8_t v___x_2535_; 
v___x_2535_ = l_Lean_Expr_hasLooseBVars(v_e_2510_);
if (v___x_2535_ == 0)
{
lean_object* v___x_2536_; 
lean_dec_ref(v_xs_2509_);
lean_inc_ref(v_e_2510_);
v___x_2536_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet(v_e_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2577_; 
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2539_ = v___x_2536_;
v_isShared_2540_ = v_isSharedCheck_2577_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2536_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2577_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
uint8_t v___x_2541_; 
v___x_2541_ = lean_unbox(v_a_2537_);
lean_dec(v_a_2537_);
if (v___x_2541_ == 0)
{
lean_object* v___x_2543_; 
if (v_isShared_2540_ == 0)
{
lean_ctor_set(v___x_2539_, 0, v_e_2510_);
v___x_2543_ = v___x_2539_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_e_2510_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
else
{
lean_object* v___x_2545_; lean_object* v_cacheClosed_2546_; lean_object* v___x_2547_; 
v___x_2545_ = lean_st_ref_get(v_a_2511_);
v_cacheClosed_2546_ = lean_ctor_get(v___x_2545_, 1);
lean_inc_ref(v_cacheClosed_2546_);
lean_dec(v___x_2545_);
v___x_2547_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0___redArg(v_cacheClosed_2546_, v_e_2510_);
lean_dec_ref(v_cacheClosed_2546_);
if (lean_obj_tag(v___x_2547_) == 1)
{
lean_object* v_val_2548_; lean_object* v___x_2550_; 
lean_dec_ref(v_e_2510_);
v_val_2548_ = lean_ctor_get(v___x_2547_, 0);
lean_inc(v_val_2548_);
lean_dec_ref_known(v___x_2547_, 1);
if (v_isShared_2540_ == 0)
{
lean_ctor_set(v___x_2539_, 0, v_val_2548_);
v___x_2550_ = v___x_2539_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_val_2548_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
else
{
lean_object* v___x_2552_; lean_object* v___x_2553_; 
lean_dec(v___x_2547_);
lean_del_object(v___x_2539_);
v___x_2552_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__3, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__3_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__3);
lean_inc_ref(v_e_2510_);
v___x_2553_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit(v___x_2552_, v_e_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v_a_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2576_; 
v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2556_ = v___x_2553_;
v_isShared_2557_ = v_isSharedCheck_2576_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_a_2554_);
lean_dec(v___x_2553_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2576_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2558_; lean_object* v_cache_2559_; lean_object* v_cacheClosed_2560_; lean_object* v_hasLetCache_2561_; lean_object* v_decls_2562_; lean_object* v_valueMap_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2575_; 
v___x_2558_ = lean_st_ref_take(v_a_2511_);
v_cache_2559_ = lean_ctor_get(v___x_2558_, 0);
v_cacheClosed_2560_ = lean_ctor_get(v___x_2558_, 1);
v_hasLetCache_2561_ = lean_ctor_get(v___x_2558_, 2);
v_decls_2562_ = lean_ctor_get(v___x_2558_, 3);
v_valueMap_2563_ = lean_ctor_get(v___x_2558_, 4);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2565_ = v___x_2558_;
v_isShared_2566_ = v_isSharedCheck_2575_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_valueMap_2563_);
lean_inc(v_decls_2562_);
lean_inc(v_hasLetCache_2561_);
lean_inc(v_cacheClosed_2560_);
lean_inc(v_cache_2559_);
lean_dec(v___x_2558_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2575_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2567_; lean_object* v___x_2569_; 
lean_inc(v_a_2554_);
v___x_2567_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1___redArg(v_cacheClosed_2560_, v_e_2510_, v_a_2554_);
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 1, v___x_2567_);
v___x_2569_ = v___x_2565_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_cache_2559_);
lean_ctor_set(v_reuseFailAlloc_2574_, 1, v___x_2567_);
lean_ctor_set(v_reuseFailAlloc_2574_, 2, v_hasLetCache_2561_);
lean_ctor_set(v_reuseFailAlloc_2574_, 3, v_decls_2562_);
lean_ctor_set(v_reuseFailAlloc_2574_, 4, v_valueMap_2563_);
v___x_2569_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
lean_object* v___x_2570_; lean_object* v___x_2572_; 
v___x_2570_ = lean_st_ref_put(v_a_2511_, v___x_2569_);
if (v_isShared_2557_ == 0)
{
v___x_2572_ = v___x_2556_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v_a_2554_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_2510_);
return v___x_2553_;
}
}
}
}
}
else
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2585_; 
lean_dec_ref(v_e_2510_);
v_a_2578_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2580_ = v___x_2536_;
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2536_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2583_; 
if (v_isShared_2581_ == 0)
{
v___x_2583_ = v___x_2580_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_a_2578_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
}
else
{
lean_object* v_key_2586_; lean_object* v___x_2587_; lean_object* v_cache_2588_; lean_object* v___x_2589_; 
lean_inc_ref(v_e_2510_);
lean_inc_ref(v_xs_2509_);
v_key_2586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_2586_, 0, v_xs_2509_);
lean_ctor_set(v_key_2586_, 1, v_e_2510_);
v___x_2587_ = lean_st_ref_get(v_a_2511_);
v_cache_2588_ = lean_ctor_get(v___x_2587_, 0);
lean_inc_ref(v_cache_2588_);
lean_dec(v___x_2587_);
v___x_2589_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6___redArg(v_cache_2588_, v_key_2586_);
lean_dec_ref(v_cache_2588_);
if (lean_obj_tag(v___x_2589_) == 1)
{
lean_object* v_val_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2597_; 
lean_dec_ref_known(v_key_2586_, 2);
lean_dec_ref(v_e_2510_);
lean_dec_ref(v_xs_2509_);
v_val_2590_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2592_ = v___x_2589_;
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_val_2590_);
lean_dec(v___x_2589_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2595_; 
if (v_isShared_2593_ == 0)
{
lean_ctor_set_tag(v___x_2592_, 0);
v___x_2595_ = v___x_2592_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_val_2590_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
else
{
lean_object* v___x_2598_; 
lean_dec(v___x_2589_);
v___x_2598_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit(v_xs_2509_, v_e_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v_a_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2621_; 
v_a_2599_ = lean_ctor_get(v___x_2598_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2601_ = v___x_2598_;
v_isShared_2602_ = v_isSharedCheck_2621_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_a_2599_);
lean_dec(v___x_2598_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2621_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2603_; lean_object* v_cache_2604_; lean_object* v_cacheClosed_2605_; lean_object* v_hasLetCache_2606_; lean_object* v_decls_2607_; lean_object* v_valueMap_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2620_; 
v___x_2603_ = lean_st_ref_take(v_a_2511_);
v_cache_2604_ = lean_ctor_get(v___x_2603_, 0);
v_cacheClosed_2605_ = lean_ctor_get(v___x_2603_, 1);
v_hasLetCache_2606_ = lean_ctor_get(v___x_2603_, 2);
v_decls_2607_ = lean_ctor_get(v___x_2603_, 3);
v_valueMap_2608_ = lean_ctor_get(v___x_2603_, 4);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2610_ = v___x_2603_;
v_isShared_2611_ = v_isSharedCheck_2620_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_valueMap_2608_);
lean_inc(v_decls_2607_);
lean_inc(v_hasLetCache_2606_);
lean_inc(v_cacheClosed_2605_);
lean_inc(v_cache_2604_);
lean_dec(v___x_2603_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2620_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2612_; lean_object* v___x_2614_; 
lean_inc(v_a_2599_);
v___x_2612_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7___redArg(v_cache_2604_, v_key_2586_, v_a_2599_);
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 0, v___x_2612_);
v___x_2614_ = v___x_2610_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v___x_2612_);
lean_ctor_set(v_reuseFailAlloc_2619_, 1, v_cacheClosed_2605_);
lean_ctor_set(v_reuseFailAlloc_2619_, 2, v_hasLetCache_2606_);
lean_ctor_set(v_reuseFailAlloc_2619_, 3, v_decls_2607_);
lean_ctor_set(v_reuseFailAlloc_2619_, 4, v_valueMap_2608_);
v___x_2614_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
lean_object* v___x_2615_; lean_object* v___x_2617_; 
v___x_2615_ = lean_st_ref_put(v_a_2511_, v___x_2614_);
if (v_isShared_2602_ == 0)
{
v___x_2617_ = v___x_2601_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_a_2599_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_2586_, 2);
return v___x_2598_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_2509_ = stack[0].m_obj;
lean_object* v_e_2510_ = stack[1].m_obj;
lean_object* v_a_2511_ = stack[2].m_obj;
lean_object* v_a_2512_ = stack[3].m_obj;
lean_object* v_a_2513_ = stack[4].m_obj;
lean_object* v_a_2514_ = stack[5].m_obj;
lean_object* v_a_2515_ = stack[6].m_obj;
lean_object* v_a_2516_ = stack[7].m_obj;
lean_object* v_a_2517_ = stack[8].m_obj;
lean_object* v_res_2622_;
v_res_2622_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v_xs_2509_, v_e_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_);
stack->m_obj
 = v_res_2622_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___boxed(lean_object* v_xs_2623_, lean_object* v_e_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_){
_start:
{
lean_object* v_res_2633_; 
v_res_2633_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v_xs_2623_, v_e_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_);
lean_dec(v_a_2631_);
lean_dec_ref(v_a_2630_);
lean_dec(v_a_2629_);
lean_dec_ref(v_a_2628_);
lean_dec(v_a_2627_);
lean_dec_ref(v_a_2626_);
lean_dec(v_a_2625_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___boxed(lean_object* v_xs_2634_, lean_object* v_e_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_){
_start:
{
lean_object* v_res_2644_; 
v_res_2644_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit(v_xs_2634_, v_e_2635_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_);
lean_dec(v_a_2642_);
lean_dec_ref(v_a_2641_);
lean_dec(v_a_2640_);
lean_dec_ref(v_a_2639_);
lean_dec(v_a_2638_);
lean_dec_ref(v_a_2637_);
lean_dec(v_a_2636_);
return v_res_2644_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5(lean_object* v_00_u03b1_2645_, lean_object* v_msg_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_){
_start:
{
lean_object* v___x_2655_; 
v___x_2655_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5___redArg(v_msg_2646_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_);
return v___x_2655_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2646_ = stack[1].m_obj;
lean_object* v___y_2647_ = stack[2].m_obj;
lean_object* v___y_2648_ = stack[3].m_obj;
lean_object* v___y_2649_ = stack[4].m_obj;
lean_object* v___y_2650_ = stack[5].m_obj;
lean_object* v___y_2651_ = stack[6].m_obj;
lean_object* v___y_2652_ = stack[7].m_obj;
lean_object* v___y_2653_ = stack[8].m_obj;
lean_object* v_res_2656_;
v_res_2656_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5(lean_box(0), v_msg_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_);
stack->m_obj
 = v_res_2656_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5___boxed(lean_object* v_00_u03b1_2657_, lean_object* v_msg_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5(v_00_u03b1_2657_, v_msg_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
lean_dec(v___y_2663_);
lean_dec_ref(v___y_2662_);
lean_dec(v___y_2661_);
lean_dec_ref(v___y_2660_);
lean_dec(v___y_2659_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6(lean_object* v_00_u03b2_2668_, lean_object* v_m_2669_, lean_object* v_a_2670_){
_start:
{
lean_object* v___x_2671_; 
v___x_2671_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6___redArg(v_m_2669_, v_a_2670_);
return v___x_2671_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6___boxed(lean_object* v_00_u03b2_2672_, lean_object* v_m_2673_, lean_object* v_a_2674_){
_start:
{
lean_object* v_res_2675_; 
v_res_2675_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6(v_00_u03b2_2672_, v_m_2673_, v_a_2674_);
lean_dec_ref(v_a_2674_);
lean_dec_ref(v_m_2673_);
return v_res_2675_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7(lean_object* v_00_u03b2_2676_, lean_object* v_m_2677_, lean_object* v_a_2678_, lean_object* v_b_2679_){
_start:
{
lean_object* v___x_2680_; 
v___x_2680_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7___redArg(v_m_2677_, v_a_2678_, v_b_2679_);
return v___x_2680_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7(lean_object* v_00_u03b2_2681_, lean_object* v_a_2682_, lean_object* v_x_2683_){
_start:
{
lean_object* v___x_2684_; 
v___x_2684_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7___redArg(v_a_2682_, v_x_2683_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7___boxed(lean_object* v_00_u03b2_2685_, lean_object* v_a_2686_, lean_object* v_x_2687_){
_start:
{
lean_object* v_res_2688_; 
v_res_2688_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7(v_00_u03b2_2685_, v_a_2686_, v_x_2687_);
lean_dec(v_x_2687_);
lean_dec_ref(v_a_2686_);
return v_res_2688_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9(lean_object* v_00_u03b2_2689_, lean_object* v_a_2690_, lean_object* v_x_2691_){
_start:
{
uint8_t v___x_2692_; 
v___x_2692_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9___redArg(v_a_2690_, v_x_2691_);
return v___x_2692_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2690_ = stack[1].m_obj;
lean_object* v_x_2691_ = stack[2].m_obj;
uint8_t v_res_2693_;
v_res_2693_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9(lean_box(0), v_a_2690_, v_x_2691_);
stack->m_num = v_res_2693_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9___boxed(lean_object* v_00_u03b2_2694_, lean_object* v_a_2695_, lean_object* v_x_2696_){
_start:
{
uint8_t v_res_2697_; lean_object* v_r_2698_; 
v_res_2697_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9(v_00_u03b2_2694_, v_a_2695_, v_x_2696_);
lean_dec(v_x_2696_);
lean_dec_ref(v_a_2695_);
v_r_2698_ = lean_box(v_res_2697_);
return v_r_2698_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10(lean_object* v_00_u03b2_2699_, lean_object* v_data_2700_){
_start:
{
lean_object* v___x_2701_; 
v___x_2701_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10___redArg(v_data_2700_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__11(lean_object* v_00_u03b2_2702_, lean_object* v_a_2703_, lean_object* v_b_2704_, lean_object* v_x_2705_){
_start:
{
lean_object* v___x_2706_; 
v___x_2706_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__11___redArg(v_a_2703_, v_b_2704_, v_x_2705_);
return v___x_2706_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10_spec__11(lean_object* v_00_u03b2_2707_, lean_object* v_i_2708_, lean_object* v_source_2709_, lean_object* v_target_2710_){
_start:
{
lean_object* v___x_2711_; 
v___x_2711_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10_spec__11___redArg(v_i_2708_, v_source_2709_, v_target_2710_);
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10_spec__11_spec__12(lean_object* v_00_u03b2_2712_, lean_object* v_x_2713_, lean_object* v_x_2714_){
_start:
{
lean_object* v___x_2715_; 
v___x_2715_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10_spec__11_spec__12___redArg(v_x_2713_, v_x_2714_);
return v___x_2715_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2716_; 
v___x_2716_ = l_Std_HashMap_instInhabited___redArg();
return v___x_2716_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3(lean_object* v_msg_2717_, uint8_t v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_){
_start:
{
lean_object* v___x_2721_; lean_object* v___f_2722_; lean_object* v___f_2723_; lean_object* v___f_2724_; lean_object* v___x_10671__overap_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2721_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3___closed__0);
v___f_2722_ = lean_alloc_closure((void*)(l_EStateM_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2722_, 0, v___x_2721_);
v___f_2723_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2723_, 0, v___f_2722_);
v___f_2724_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2724_, 0, v___f_2723_);
v___x_10671__overap_2725_ = lean_panic_fn_borrowed(v___f_2724_, v_msg_2717_);
lean_dec_ref(v___f_2724_);
v___x_2726_ = lean_box(v___y_2718_);
lean_inc_ref(v___y_2719_);
v___x_2727_ = lean_apply_3(v___x_10671__overap_2725_, v___x_2726_, v___y_2719_, v___y_2720_);
return v___x_2727_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2717_ = stack[0].m_obj;
uint8_t v___y_2718_ = stack[1].m_num;
lean_object* v___y_2719_ = stack[2].m_obj;
lean_object* v___y_2720_ = stack[3].m_obj;
lean_object* v_res_2728_;
v_res_2728_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3(v_msg_2717_, v___y_2718_, v___y_2719_, v___y_2720_);
stack->m_obj
 = v_res_2728_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3___boxed(lean_object* v_msg_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_){
_start:
{
uint8_t v___y_15640__boxed_2733_; lean_object* v_res_2734_; 
v___y_15640__boxed_2733_ = lean_unbox(v___y_2730_);
v_res_2734_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3(v_msg_2729_, v___y_15640__boxed_2733_, v___y_2731_, v___y_2732_);
lean_dec_ref(v___y_2731_);
return v_res_2734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4___redArg(lean_object* v_idx_2735_, lean_object* v___y_2736_){
_start:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2737_ = l_Lean_Expr_bvar___override(v_idx_2735_);
v___x_2738_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_2737_, v___y_2736_);
return v___x_2738_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4(lean_object* v_idx_2739_, uint8_t v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_){
_start:
{
lean_object* v___x_2743_; 
v___x_2743_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4___redArg(v_idx_2739_, v___y_2742_);
return v___x_2743_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_idx_2739_ = stack[0].m_obj;
uint8_t v___y_2740_ = stack[1].m_num;
lean_object* v___y_2741_ = stack[2].m_obj;
lean_object* v___y_2742_ = stack[3].m_obj;
lean_object* v_res_2744_;
v_res_2744_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4(v_idx_2739_, v___y_2740_, v___y_2741_, v___y_2742_);
stack->m_obj
 = v_res_2744_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4___boxed(lean_object* v_idx_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
uint8_t v___y_15684__boxed_2749_; lean_object* v_res_2750_; 
v___y_15684__boxed_2749_ = lean_unbox(v___y_2746_);
v_res_2750_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4(v_idx_2745_, v___y_15684__boxed_2749_, v___y_2747_, v___y_2748_);
lean_dec_ref(v___y_2747_);
return v_res_2750_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6___redArg(lean_object* v_x_2751_, lean_object* v_t_2752_, lean_object* v_v_2753_, lean_object* v_b_2754_, uint8_t v_nondep_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
lean_object* v___y_2764_; lean_object* v___x_2767_; uint8_t v_debug_2768_; 
v___x_2767_ = lean_st_ref_get(v___y_2757_);
v_debug_2768_ = lean_ctor_get_uint8(v___x_2767_, sizeof(void*)*12);
lean_dec(v___x_2767_);
if (v_debug_2768_ == 0)
{
v___y_2764_ = v___y_2757_;
goto v___jp_2763_;
}
else
{
lean_object* v___x_2769_; 
v___x_2769_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_2752_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
if (lean_obj_tag(v___x_2769_) == 0)
{
lean_object* v___x_2770_; 
lean_dec_ref_known(v___x_2769_, 1);
v___x_2770_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_v_2753_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
if (lean_obj_tag(v___x_2770_) == 0)
{
lean_object* v___x_2771_; 
lean_dec_ref_known(v___x_2770_, 1);
v___x_2771_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_2754_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_dec_ref_known(v___x_2771_, 1);
v___y_2764_ = v___y_2757_;
goto v___jp_2763_;
}
else
{
lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2779_; 
lean_dec_ref(v_b_2754_);
lean_dec_ref(v_v_2753_);
lean_dec_ref(v_t_2752_);
lean_dec(v_x_2751_);
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2774_ = v___x_2771_;
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2771_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2777_; 
if (v_isShared_2775_ == 0)
{
v___x_2777_ = v___x_2774_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_a_2772_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
}
}
else
{
lean_object* v_a_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2787_; 
lean_dec_ref(v_b_2754_);
lean_dec_ref(v_v_2753_);
lean_dec_ref(v_t_2752_);
lean_dec(v_x_2751_);
v_a_2780_ = lean_ctor_get(v___x_2770_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2782_ = v___x_2770_;
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_a_2780_);
lean_dec(v___x_2770_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2785_; 
if (v_isShared_2783_ == 0)
{
v___x_2785_ = v___x_2782_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_a_2780_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
}
}
else
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2795_; 
lean_dec_ref(v_b_2754_);
lean_dec_ref(v_v_2753_);
lean_dec_ref(v_t_2752_);
lean_dec(v_x_2751_);
v_a_2788_ = lean_ctor_get(v___x_2769_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2769_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2790_ = v___x_2769_;
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___x_2769_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2791_ == 0)
{
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_a_2788_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
}
v___jp_2763_:
{
lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2765_ = l_Lean_Expr_letE___override(v_x_2751_, v_t_2752_, v_v_2753_, v_b_2754_, v_nondep_2755_);
v___x_2766_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2765_, v___y_2764_);
return v___x_2766_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2751_ = stack[0].m_obj;
lean_object* v_t_2752_ = stack[1].m_obj;
lean_object* v_v_2753_ = stack[2].m_obj;
lean_object* v_b_2754_ = stack[3].m_obj;
uint8_t v_nondep_2755_ = stack[4].m_num;
lean_object* v___y_2756_ = stack[5].m_obj;
lean_object* v___y_2757_ = stack[6].m_obj;
lean_object* v___y_2758_ = stack[7].m_obj;
lean_object* v___y_2759_ = stack[8].m_obj;
lean_object* v___y_2760_ = stack[9].m_obj;
lean_object* v___y_2761_ = stack[10].m_obj;
lean_object* v_res_2796_;
v_res_2796_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6___redArg(v_x_2751_, v_t_2752_, v_v_2753_, v_b_2754_, v_nondep_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
stack->m_obj
 = v_res_2796_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6___redArg___boxed(lean_object* v_x_2797_, lean_object* v_t_2798_, lean_object* v_v_2799_, lean_object* v_b_2800_, lean_object* v_nondep_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_){
_start:
{
uint8_t v_nondep_boxed_2809_; lean_object* v_res_2810_; 
v_nondep_boxed_2809_ = lean_unbox(v_nondep_2801_);
v_res_2810_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6___redArg(v_x_2797_, v_t_2798_, v_v_2799_, v_b_2800_, v_nondep_boxed_2809_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
lean_dec(v___y_2807_);
lean_dec_ref(v___y_2806_);
lean_dec(v___y_2805_);
lean_dec_ref(v___y_2804_);
lean_dec(v___y_2803_);
lean_dec_ref(v___y_2802_);
return v_res_2810_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6(lean_object* v_x_2811_, lean_object* v_t_2812_, lean_object* v_v_2813_, lean_object* v_b_2814_, uint8_t v_nondep_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_){
_start:
{
lean_object* v___x_2824_; 
v___x_2824_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6___redArg(v_x_2811_, v_t_2812_, v_v_2813_, v_b_2814_, v_nondep_2815_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_);
return v___x_2824_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2811_ = stack[0].m_obj;
lean_object* v_t_2812_ = stack[1].m_obj;
lean_object* v_v_2813_ = stack[2].m_obj;
lean_object* v_b_2814_ = stack[3].m_obj;
uint8_t v_nondep_2815_ = stack[4].m_num;
lean_object* v___y_2816_ = stack[5].m_obj;
lean_object* v___y_2817_ = stack[6].m_obj;
lean_object* v___y_2818_ = stack[7].m_obj;
lean_object* v___y_2819_ = stack[8].m_obj;
lean_object* v___y_2820_ = stack[9].m_obj;
lean_object* v___y_2821_ = stack[10].m_obj;
lean_object* v___y_2822_ = stack[11].m_obj;
lean_object* v_res_2825_;
v_res_2825_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6(v_x_2811_, v_t_2812_, v_v_2813_, v_b_2814_, v_nondep_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_);
stack->m_obj
 = v_res_2825_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6___boxed(lean_object* v_x_2826_, lean_object* v_t_2827_, lean_object* v_v_2828_, lean_object* v_b_2829_, lean_object* v_nondep_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_){
_start:
{
uint8_t v_nondep_boxed_2839_; lean_object* v_res_2840_; 
v_nondep_boxed_2839_ = lean_unbox(v_nondep_2830_);
v_res_2840_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6(v_x_2826_, v_t_2827_, v_v_2828_, v_b_2829_, v_nondep_boxed_2839_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v___y_2831_);
return v_res_2840_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2_spec__5___redArg(lean_object* v_a_2841_, lean_object* v_x_2842_){
_start:
{
if (lean_obj_tag(v_x_2842_) == 0)
{
lean_object* v___x_2843_; 
v___x_2843_ = lean_box(0);
return v___x_2843_;
}
else
{
lean_object* v_key_2844_; lean_object* v_value_2845_; lean_object* v_tail_2846_; uint8_t v___x_2847_; 
v_key_2844_ = lean_ctor_get(v_x_2842_, 0);
v_value_2845_ = lean_ctor_get(v_x_2842_, 1);
v_tail_2846_ = lean_ctor_get(v_x_2842_, 2);
v___x_2847_ = l_Lean_instBEqFVarId_beq(v_key_2844_, v_a_2841_);
if (v___x_2847_ == 0)
{
v_x_2842_ = v_tail_2846_;
goto _start;
}
else
{
lean_object* v___x_2849_; 
lean_inc(v_value_2845_);
v___x_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2849_, 0, v_value_2845_);
return v___x_2849_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2_spec__5___redArg___boxed(lean_object* v_a_2850_, lean_object* v_x_2851_){
_start:
{
lean_object* v_res_2852_; 
v_res_2852_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2_spec__5___redArg(v_a_2850_, v_x_2851_);
lean_dec(v_x_2851_);
lean_dec(v_a_2850_);
return v_res_2852_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___redArg(lean_object* v_m_2853_, lean_object* v_a_2854_){
_start:
{
lean_object* v_buckets_2855_; lean_object* v___x_2856_; uint64_t v___x_2857_; uint64_t v___x_2858_; uint64_t v___x_2859_; uint64_t v_fold_2860_; uint64_t v___x_2861_; uint64_t v___x_2862_; uint64_t v___x_2863_; size_t v___x_2864_; size_t v___x_2865_; size_t v___x_2866_; size_t v___x_2867_; size_t v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; 
v_buckets_2855_ = lean_ctor_get(v_m_2853_, 1);
v___x_2856_ = lean_array_get_size(v_buckets_2855_);
v___x_2857_ = l_Lean_instHashableFVarId_hash(v_a_2854_);
v___x_2858_ = 32ULL;
v___x_2859_ = lean_uint64_shift_right(v___x_2857_, v___x_2858_);
v_fold_2860_ = lean_uint64_xor(v___x_2857_, v___x_2859_);
v___x_2861_ = 16ULL;
v___x_2862_ = lean_uint64_shift_right(v_fold_2860_, v___x_2861_);
v___x_2863_ = lean_uint64_xor(v_fold_2860_, v___x_2862_);
v___x_2864_ = lean_uint64_to_usize(v___x_2863_);
v___x_2865_ = lean_usize_of_nat(v___x_2856_);
v___x_2866_ = ((size_t)1ULL);
v___x_2867_ = lean_usize_sub(v___x_2865_, v___x_2866_);
v___x_2868_ = lean_usize_land(v___x_2864_, v___x_2867_);
v___x_2869_ = lean_array_uget_borrowed(v_buckets_2855_, v___x_2868_);
v___x_2870_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2_spec__5___redArg(v_a_2854_, v___x_2869_);
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___redArg___boxed(lean_object* v_m_2871_, lean_object* v_a_2872_){
_start:
{
lean_object* v_res_2873_; 
v_res_2873_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___redArg(v_m_2871_, v_a_2872_);
lean_dec(v_a_2872_);
lean_dec_ref(v_m_2871_);
return v_res_2873_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2(void){
_start:
{
lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; 
v___x_2876_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__1));
v___x_2877_ = lean_unsigned_to_nat(10u);
v___x_2878_ = lean_unsigned_to_nat(236u);
v___x_2879_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__0));
v___x_2880_ = ((lean_object*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__0));
v___x_2881_ = l_mkPanicMessageWithDecl(v___x_2880_, v___x_2879_, v___x_2878_, v___x_2877_, v___x_2876_);
return v___x_2881_;
}
}
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5(lean_object* v___x_2882_, lean_object* v_i_2883_, lean_object* v_e_2884_, lean_object* v_offset_2885_, lean_object* v_a_2886_, uint8_t v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_){
_start:
{
switch(lean_obj_tag(v_e_2884_))
{
case 5:
{
lean_object* v_fn_2890_; lean_object* v_arg_2891_; lean_object* v___x_2892_; 
v_fn_2890_ = lean_ctor_get(v_e_2884_, 0);
v_arg_2891_ = lean_ctor_get(v_e_2884_, 1);
lean_inc(v_offset_2885_);
lean_inc_ref(v_fn_2890_);
v___x_2892_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2882_, v_i_2883_, v_fn_2890_, v_offset_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v_a_2893_; lean_object* v_a_2894_; lean_object* v_fst_2895_; lean_object* v_snd_2896_; lean_object* v___x_2897_; 
v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
lean_inc(v_a_2893_);
v_a_2894_ = lean_ctor_get(v___x_2892_, 1);
lean_inc(v_a_2894_);
lean_dec_ref_known(v___x_2892_, 2);
v_fst_2895_ = lean_ctor_get(v_a_2893_, 0);
lean_inc(v_fst_2895_);
v_snd_2896_ = lean_ctor_get(v_a_2893_, 1);
lean_inc(v_snd_2896_);
lean_dec(v_a_2893_);
lean_inc_ref(v_arg_2891_);
v___x_2897_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2882_, v_i_2883_, v_arg_2891_, v_offset_2885_, v_snd_2896_, v_a_2887_, v_a_2888_, v_a_2894_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_object* v_a_2898_; lean_object* v_a_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2923_; 
v_a_2898_ = lean_ctor_get(v___x_2897_, 0);
v_a_2899_ = lean_ctor_get(v___x_2897_, 1);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2901_ = v___x_2897_;
v_isShared_2902_ = v_isSharedCheck_2923_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_a_2899_);
lean_inc(v_a_2898_);
lean_dec(v___x_2897_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2923_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v_fst_2903_; lean_object* v_snd_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2922_; 
v_fst_2903_ = lean_ctor_get(v_a_2898_, 0);
v_snd_2904_ = lean_ctor_get(v_a_2898_, 1);
v_isSharedCheck_2922_ = !lean_is_exclusive(v_a_2898_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2906_ = v_a_2898_;
v_isShared_2907_ = v_isSharedCheck_2922_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_snd_2904_);
lean_inc(v_fst_2903_);
lean_dec(v_a_2898_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2922_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
size_t v___x_2908_; size_t v___x_2909_; uint8_t v___x_2910_; 
v___x_2908_ = lean_ptr_addr(v_fn_2890_);
v___x_2909_ = lean_ptr_addr(v_fst_2895_);
v___x_2910_ = lean_usize_dec_eq(v___x_2908_, v___x_2909_);
if (v___x_2910_ == 0)
{
lean_object* v___x_2911_; 
lean_del_object(v___x_2906_);
lean_del_object(v___x_2901_);
lean_dec_ref_known(v_e_2884_, 2);
v___x_2911_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__1(v_fst_2895_, v_fst_2903_, v_snd_2904_, v_a_2887_, v_a_2888_, v_a_2899_);
return v___x_2911_;
}
else
{
size_t v___x_2912_; size_t v___x_2913_; uint8_t v___x_2914_; 
v___x_2912_ = lean_ptr_addr(v_arg_2891_);
v___x_2913_ = lean_ptr_addr(v_fst_2903_);
v___x_2914_ = lean_usize_dec_eq(v___x_2912_, v___x_2913_);
if (v___x_2914_ == 0)
{
lean_object* v___x_2915_; 
lean_del_object(v___x_2906_);
lean_del_object(v___x_2901_);
lean_dec_ref_known(v_e_2884_, 2);
v___x_2915_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__1(v_fst_2895_, v_fst_2903_, v_snd_2904_, v_a_2887_, v_a_2888_, v_a_2899_);
return v___x_2915_;
}
else
{
lean_object* v___x_2917_; 
lean_dec(v_fst_2903_);
lean_dec(v_fst_2895_);
if (v_isShared_2907_ == 0)
{
lean_ctor_set(v___x_2906_, 0, v_e_2884_);
v___x_2917_ = v___x_2906_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_e_2884_);
lean_ctor_set(v_reuseFailAlloc_2921_, 1, v_snd_2904_);
v___x_2917_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
lean_object* v___x_2919_; 
if (v_isShared_2902_ == 0)
{
lean_ctor_set(v___x_2901_, 0, v___x_2917_);
v___x_2919_ = v___x_2901_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v___x_2917_);
lean_ctor_set(v_reuseFailAlloc_2920_, 1, v_a_2899_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
return v___x_2919_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_2895_);
lean_dec_ref_known(v_e_2884_, 2);
return v___x_2897_;
}
}
else
{
lean_dec_ref_known(v_e_2884_, 2);
lean_dec(v_offset_2885_);
return v___x_2892_;
}
}
case 6:
{
lean_object* v_binderName_2924_; lean_object* v_binderType_2925_; lean_object* v_body_2926_; uint8_t v_binderInfo_2927_; lean_object* v___x_2928_; 
v_binderName_2924_ = lean_ctor_get(v_e_2884_, 0);
v_binderType_2925_ = lean_ctor_get(v_e_2884_, 1);
v_body_2926_ = lean_ctor_get(v_e_2884_, 2);
v_binderInfo_2927_ = lean_ctor_get_uint8(v_e_2884_, sizeof(void*)*3 + 8);
lean_inc(v_offset_2885_);
lean_inc_ref(v_binderType_2925_);
v___x_2928_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2882_, v_i_2883_, v_binderType_2925_, v_offset_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_);
if (lean_obj_tag(v___x_2928_) == 0)
{
lean_object* v_a_2929_; lean_object* v_a_2930_; lean_object* v_fst_2931_; lean_object* v_snd_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; 
v_a_2929_ = lean_ctor_get(v___x_2928_, 0);
lean_inc(v_a_2929_);
v_a_2930_ = lean_ctor_get(v___x_2928_, 1);
lean_inc(v_a_2930_);
lean_dec_ref_known(v___x_2928_, 2);
v_fst_2931_ = lean_ctor_get(v_a_2929_, 0);
lean_inc(v_fst_2931_);
v_snd_2932_ = lean_ctor_get(v_a_2929_, 1);
lean_inc(v_snd_2932_);
lean_dec(v_a_2929_);
v___x_2933_ = lean_unsigned_to_nat(1u);
v___x_2934_ = lean_nat_add(v_offset_2885_, v___x_2933_);
lean_dec(v_offset_2885_);
lean_inc_ref(v_body_2926_);
v___x_2935_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2882_, v_i_2883_, v_body_2926_, v___x_2934_, v_snd_2932_, v_a_2887_, v_a_2888_, v_a_2930_);
if (lean_obj_tag(v___x_2935_) == 0)
{
lean_object* v_a_2936_; lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2961_; 
v_a_2936_ = lean_ctor_get(v___x_2935_, 0);
v_a_2937_ = lean_ctor_get(v___x_2935_, 1);
v_isSharedCheck_2961_ = !lean_is_exclusive(v___x_2935_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2939_ = v___x_2935_;
v_isShared_2940_ = v_isSharedCheck_2961_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_inc(v_a_2936_);
lean_dec(v___x_2935_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2961_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v_fst_2941_; lean_object* v_snd_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2960_; 
v_fst_2941_ = lean_ctor_get(v_a_2936_, 0);
v_snd_2942_ = lean_ctor_get(v_a_2936_, 1);
v_isSharedCheck_2960_ = !lean_is_exclusive(v_a_2936_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2944_ = v_a_2936_;
v_isShared_2945_ = v_isSharedCheck_2960_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_snd_2942_);
lean_inc(v_fst_2941_);
lean_dec(v_a_2936_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2960_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
size_t v___x_2946_; size_t v___x_2947_; uint8_t v___x_2948_; 
v___x_2946_ = lean_ptr_addr(v_binderType_2925_);
v___x_2947_ = lean_ptr_addr(v_fst_2931_);
v___x_2948_ = lean_usize_dec_eq(v___x_2946_, v___x_2947_);
if (v___x_2948_ == 0)
{
lean_object* v___x_2949_; 
lean_inc(v_binderName_2924_);
lean_del_object(v___x_2944_);
lean_del_object(v___x_2939_);
lean_dec_ref_known(v_e_2884_, 3);
v___x_2949_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__2(v_binderName_2924_, v_binderInfo_2927_, v_fst_2931_, v_fst_2941_, v_snd_2942_, v_a_2887_, v_a_2888_, v_a_2937_);
return v___x_2949_;
}
else
{
size_t v___x_2950_; size_t v___x_2951_; uint8_t v___x_2952_; 
v___x_2950_ = lean_ptr_addr(v_body_2926_);
v___x_2951_ = lean_ptr_addr(v_fst_2941_);
v___x_2952_ = lean_usize_dec_eq(v___x_2950_, v___x_2951_);
if (v___x_2952_ == 0)
{
lean_object* v___x_2953_; 
lean_inc(v_binderName_2924_);
lean_del_object(v___x_2944_);
lean_del_object(v___x_2939_);
lean_dec_ref_known(v_e_2884_, 3);
v___x_2953_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__2(v_binderName_2924_, v_binderInfo_2927_, v_fst_2931_, v_fst_2941_, v_snd_2942_, v_a_2887_, v_a_2888_, v_a_2937_);
return v___x_2953_;
}
else
{
lean_object* v___x_2955_; 
lean_dec(v_fst_2941_);
lean_dec(v_fst_2931_);
if (v_isShared_2945_ == 0)
{
lean_ctor_set(v___x_2944_, 0, v_e_2884_);
v___x_2955_ = v___x_2944_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_e_2884_);
lean_ctor_set(v_reuseFailAlloc_2959_, 1, v_snd_2942_);
v___x_2955_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
lean_object* v___x_2957_; 
if (v_isShared_2940_ == 0)
{
lean_ctor_set(v___x_2939_, 0, v___x_2955_);
v___x_2957_ = v___x_2939_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v___x_2955_);
lean_ctor_set(v_reuseFailAlloc_2958_, 1, v_a_2937_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_2931_);
lean_dec_ref_known(v_e_2884_, 3);
return v___x_2935_;
}
}
else
{
lean_dec_ref_known(v_e_2884_, 3);
lean_dec(v_offset_2885_);
return v___x_2928_;
}
}
case 7:
{
lean_object* v_binderName_2962_; lean_object* v_binderType_2963_; lean_object* v_body_2964_; uint8_t v_binderInfo_2965_; lean_object* v___x_2966_; 
v_binderName_2962_ = lean_ctor_get(v_e_2884_, 0);
v_binderType_2963_ = lean_ctor_get(v_e_2884_, 1);
v_body_2964_ = lean_ctor_get(v_e_2884_, 2);
v_binderInfo_2965_ = lean_ctor_get_uint8(v_e_2884_, sizeof(void*)*3 + 8);
lean_inc(v_offset_2885_);
lean_inc_ref(v_binderType_2963_);
v___x_2966_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2882_, v_i_2883_, v_binderType_2963_, v_offset_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_object* v_a_2967_; lean_object* v_a_2968_; lean_object* v_fst_2969_; lean_object* v_snd_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
v_a_2967_ = lean_ctor_get(v___x_2966_, 0);
lean_inc(v_a_2967_);
v_a_2968_ = lean_ctor_get(v___x_2966_, 1);
lean_inc(v_a_2968_);
lean_dec_ref_known(v___x_2966_, 2);
v_fst_2969_ = lean_ctor_get(v_a_2967_, 0);
lean_inc(v_fst_2969_);
v_snd_2970_ = lean_ctor_get(v_a_2967_, 1);
lean_inc(v_snd_2970_);
lean_dec(v_a_2967_);
v___x_2971_ = lean_unsigned_to_nat(1u);
v___x_2972_ = lean_nat_add(v_offset_2885_, v___x_2971_);
lean_dec(v_offset_2885_);
lean_inc_ref(v_body_2964_);
v___x_2973_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2882_, v_i_2883_, v_body_2964_, v___x_2972_, v_snd_2970_, v_a_2887_, v_a_2888_, v_a_2968_);
if (lean_obj_tag(v___x_2973_) == 0)
{
lean_object* v_a_2974_; lean_object* v_a_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2999_; 
v_a_2974_ = lean_ctor_get(v___x_2973_, 0);
v_a_2975_ = lean_ctor_get(v___x_2973_, 1);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2977_ = v___x_2973_;
v_isShared_2978_ = v_isSharedCheck_2999_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_a_2975_);
lean_inc(v_a_2974_);
lean_dec(v___x_2973_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2999_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v_fst_2979_; lean_object* v_snd_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_2998_; 
v_fst_2979_ = lean_ctor_get(v_a_2974_, 0);
v_snd_2980_ = lean_ctor_get(v_a_2974_, 1);
v_isSharedCheck_2998_ = !lean_is_exclusive(v_a_2974_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2982_ = v_a_2974_;
v_isShared_2983_ = v_isSharedCheck_2998_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_snd_2980_);
lean_inc(v_fst_2979_);
lean_dec(v_a_2974_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_2998_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
size_t v___x_2984_; size_t v___x_2985_; uint8_t v___x_2986_; 
v___x_2984_ = lean_ptr_addr(v_binderType_2963_);
v___x_2985_ = lean_ptr_addr(v_fst_2969_);
v___x_2986_ = lean_usize_dec_eq(v___x_2984_, v___x_2985_);
if (v___x_2986_ == 0)
{
lean_object* v___x_2987_; 
lean_inc(v_binderName_2962_);
lean_del_object(v___x_2982_);
lean_del_object(v___x_2977_);
lean_dec_ref_known(v_e_2884_, 3);
v___x_2987_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__3(v_binderName_2962_, v_binderInfo_2965_, v_fst_2969_, v_fst_2979_, v_snd_2980_, v_a_2887_, v_a_2888_, v_a_2975_);
return v___x_2987_;
}
else
{
size_t v___x_2988_; size_t v___x_2989_; uint8_t v___x_2990_; 
v___x_2988_ = lean_ptr_addr(v_body_2964_);
v___x_2989_ = lean_ptr_addr(v_fst_2979_);
v___x_2990_ = lean_usize_dec_eq(v___x_2988_, v___x_2989_);
if (v___x_2990_ == 0)
{
lean_object* v___x_2991_; 
lean_inc(v_binderName_2962_);
lean_del_object(v___x_2982_);
lean_del_object(v___x_2977_);
lean_dec_ref_known(v_e_2884_, 3);
v___x_2991_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__3(v_binderName_2962_, v_binderInfo_2965_, v_fst_2969_, v_fst_2979_, v_snd_2980_, v_a_2887_, v_a_2888_, v_a_2975_);
return v___x_2991_;
}
else
{
lean_object* v___x_2993_; 
lean_dec(v_fst_2979_);
lean_dec(v_fst_2969_);
if (v_isShared_2983_ == 0)
{
lean_ctor_set(v___x_2982_, 0, v_e_2884_);
v___x_2993_ = v___x_2982_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_e_2884_);
lean_ctor_set(v_reuseFailAlloc_2997_, 1, v_snd_2980_);
v___x_2993_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
lean_object* v___x_2995_; 
if (v_isShared_2978_ == 0)
{
lean_ctor_set(v___x_2977_, 0, v___x_2993_);
v___x_2995_ = v___x_2977_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v___x_2993_);
lean_ctor_set(v_reuseFailAlloc_2996_, 1, v_a_2975_);
v___x_2995_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
return v___x_2995_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_2969_);
lean_dec_ref_known(v_e_2884_, 3);
return v___x_2973_;
}
}
else
{
lean_dec_ref_known(v_e_2884_, 3);
lean_dec(v_offset_2885_);
return v___x_2966_;
}
}
case 8:
{
lean_object* v_declName_3000_; lean_object* v_type_3001_; lean_object* v_value_3002_; lean_object* v_body_3003_; uint8_t v_nondep_3004_; lean_object* v___x_3005_; 
v_declName_3000_ = lean_ctor_get(v_e_2884_, 0);
v_type_3001_ = lean_ctor_get(v_e_2884_, 1);
v_value_3002_ = lean_ctor_get(v_e_2884_, 2);
v_body_3003_ = lean_ctor_get(v_e_2884_, 3);
v_nondep_3004_ = lean_ctor_get_uint8(v_e_2884_, sizeof(void*)*4 + 8);
lean_inc(v_offset_2885_);
lean_inc_ref(v_type_3001_);
v___x_3005_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2882_, v_i_2883_, v_type_3001_, v_offset_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v_a_3006_; lean_object* v_a_3007_; lean_object* v_fst_3008_; lean_object* v_snd_3009_; lean_object* v___x_3010_; 
v_a_3006_ = lean_ctor_get(v___x_3005_, 0);
lean_inc(v_a_3006_);
v_a_3007_ = lean_ctor_get(v___x_3005_, 1);
lean_inc(v_a_3007_);
lean_dec_ref_known(v___x_3005_, 2);
v_fst_3008_ = lean_ctor_get(v_a_3006_, 0);
lean_inc(v_fst_3008_);
v_snd_3009_ = lean_ctor_get(v_a_3006_, 1);
lean_inc(v_snd_3009_);
lean_dec(v_a_3006_);
lean_inc(v_offset_2885_);
lean_inc_ref(v_value_3002_);
v___x_3010_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2882_, v_i_2883_, v_value_3002_, v_offset_2885_, v_snd_3009_, v_a_2887_, v_a_2888_, v_a_3007_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v_a_3011_; lean_object* v_a_3012_; lean_object* v_fst_3013_; lean_object* v_snd_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_a_3011_);
v_a_3012_ = lean_ctor_get(v___x_3010_, 1);
lean_inc(v_a_3012_);
lean_dec_ref_known(v___x_3010_, 2);
v_fst_3013_ = lean_ctor_get(v_a_3011_, 0);
lean_inc(v_fst_3013_);
v_snd_3014_ = lean_ctor_get(v_a_3011_, 1);
lean_inc(v_snd_3014_);
lean_dec(v_a_3011_);
v___x_3015_ = lean_unsigned_to_nat(1u);
v___x_3016_ = lean_nat_add(v_offset_2885_, v___x_3015_);
lean_dec(v_offset_2885_);
lean_inc_ref(v_body_3003_);
v___x_3017_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2882_, v_i_2883_, v_body_3003_, v___x_3016_, v_snd_3014_, v_a_2887_, v_a_2888_, v_a_3012_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_a_3018_; lean_object* v_a_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3047_; 
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
v_a_3019_ = lean_ctor_get(v___x_3017_, 1);
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_3021_ = v___x_3017_;
v_isShared_3022_ = v_isSharedCheck_3047_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_a_3019_);
lean_inc(v_a_3018_);
lean_dec(v___x_3017_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3047_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v_fst_3023_; lean_object* v_snd_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3046_; 
v_fst_3023_ = lean_ctor_get(v_a_3018_, 0);
v_snd_3024_ = lean_ctor_get(v_a_3018_, 1);
v_isSharedCheck_3046_ = !lean_is_exclusive(v_a_3018_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_3026_ = v_a_3018_;
v_isShared_3027_ = v_isSharedCheck_3046_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_snd_3024_);
lean_inc(v_fst_3023_);
lean_dec(v_a_3018_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3046_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
size_t v___x_3028_; size_t v___x_3029_; uint8_t v___x_3030_; 
v___x_3028_ = lean_ptr_addr(v_type_3001_);
v___x_3029_ = lean_ptr_addr(v_fst_3008_);
v___x_3030_ = lean_usize_dec_eq(v___x_3028_, v___x_3029_);
if (v___x_3030_ == 0)
{
lean_object* v___x_3031_; 
lean_inc(v_declName_3000_);
lean_del_object(v___x_3026_);
lean_del_object(v___x_3021_);
lean_dec_ref_known(v_e_2884_, 4);
v___x_3031_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4(v_declName_3000_, v_fst_3008_, v_fst_3013_, v_fst_3023_, v_nondep_3004_, v_snd_3024_, v_a_2887_, v_a_2888_, v_a_3019_);
return v___x_3031_;
}
else
{
size_t v___x_3032_; size_t v___x_3033_; uint8_t v___x_3034_; 
v___x_3032_ = lean_ptr_addr(v_value_3002_);
v___x_3033_ = lean_ptr_addr(v_fst_3013_);
v___x_3034_ = lean_usize_dec_eq(v___x_3032_, v___x_3033_);
if (v___x_3034_ == 0)
{
lean_object* v___x_3035_; 
lean_inc(v_declName_3000_);
lean_del_object(v___x_3026_);
lean_del_object(v___x_3021_);
lean_dec_ref_known(v_e_2884_, 4);
v___x_3035_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4(v_declName_3000_, v_fst_3008_, v_fst_3013_, v_fst_3023_, v_nondep_3004_, v_snd_3024_, v_a_2887_, v_a_2888_, v_a_3019_);
return v___x_3035_;
}
else
{
size_t v___x_3036_; size_t v___x_3037_; uint8_t v___x_3038_; 
v___x_3036_ = lean_ptr_addr(v_body_3003_);
v___x_3037_ = lean_ptr_addr(v_fst_3023_);
v___x_3038_ = lean_usize_dec_eq(v___x_3036_, v___x_3037_);
if (v___x_3038_ == 0)
{
lean_object* v___x_3039_; 
lean_inc(v_declName_3000_);
lean_del_object(v___x_3026_);
lean_del_object(v___x_3021_);
lean_dec_ref_known(v_e_2884_, 4);
v___x_3039_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4(v_declName_3000_, v_fst_3008_, v_fst_3013_, v_fst_3023_, v_nondep_3004_, v_snd_3024_, v_a_2887_, v_a_2888_, v_a_3019_);
return v___x_3039_;
}
else
{
lean_object* v___x_3041_; 
lean_dec(v_fst_3023_);
lean_dec(v_fst_3013_);
lean_dec(v_fst_3008_);
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 0, v_e_2884_);
v___x_3041_ = v___x_3026_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_e_2884_);
lean_ctor_set(v_reuseFailAlloc_3045_, 1, v_snd_3024_);
v___x_3041_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
lean_object* v___x_3043_; 
if (v_isShared_3022_ == 0)
{
lean_ctor_set(v___x_3021_, 0, v___x_3041_);
v___x_3043_ = v___x_3021_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v___x_3041_);
lean_ctor_set(v_reuseFailAlloc_3044_, 1, v_a_3019_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_3013_);
lean_dec(v_fst_3008_);
lean_dec_ref_known(v_e_2884_, 4);
return v___x_3017_;
}
}
else
{
lean_dec(v_fst_3008_);
lean_dec_ref_known(v_e_2884_, 4);
lean_dec(v_offset_2885_);
return v___x_3010_;
}
}
else
{
lean_dec_ref_known(v_e_2884_, 4);
lean_dec(v_offset_2885_);
return v___x_3005_;
}
}
case 10:
{
lean_object* v_data_3048_; lean_object* v_expr_3049_; lean_object* v___x_3050_; 
v_data_3048_ = lean_ctor_get(v_e_2884_, 0);
v_expr_3049_ = lean_ctor_get(v_e_2884_, 1);
lean_inc_ref(v_expr_3049_);
v___x_3050_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2882_, v_i_2883_, v_expr_3049_, v_offset_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_);
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_object* v_a_3051_; lean_object* v_a_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3072_; 
v_a_3051_ = lean_ctor_get(v___x_3050_, 0);
v_a_3052_ = lean_ctor_get(v___x_3050_, 1);
v_isSharedCheck_3072_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3072_ == 0)
{
v___x_3054_ = v___x_3050_;
v_isShared_3055_ = v_isSharedCheck_3072_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_a_3052_);
lean_inc(v_a_3051_);
lean_dec(v___x_3050_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3072_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v_fst_3056_; lean_object* v_snd_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3071_; 
v_fst_3056_ = lean_ctor_get(v_a_3051_, 0);
v_snd_3057_ = lean_ctor_get(v_a_3051_, 1);
v_isSharedCheck_3071_ = !lean_is_exclusive(v_a_3051_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3059_ = v_a_3051_;
v_isShared_3060_ = v_isSharedCheck_3071_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_snd_3057_);
lean_inc(v_fst_3056_);
lean_dec(v_a_3051_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3071_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
size_t v___x_3061_; size_t v___x_3062_; uint8_t v___x_3063_; 
v___x_3061_ = lean_ptr_addr(v_expr_3049_);
v___x_3062_ = lean_ptr_addr(v_fst_3056_);
v___x_3063_ = lean_usize_dec_eq(v___x_3061_, v___x_3062_);
if (v___x_3063_ == 0)
{
lean_object* v___x_3064_; 
lean_inc(v_data_3048_);
lean_del_object(v___x_3059_);
lean_del_object(v___x_3054_);
lean_dec_ref_known(v_e_2884_, 2);
v___x_3064_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__5(v_data_3048_, v_fst_3056_, v_snd_3057_, v_a_2887_, v_a_2888_, v_a_3052_);
return v___x_3064_;
}
else
{
lean_object* v___x_3066_; 
lean_dec(v_fst_3056_);
if (v_isShared_3060_ == 0)
{
lean_ctor_set(v___x_3059_, 0, v_e_2884_);
v___x_3066_ = v___x_3059_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_e_2884_);
lean_ctor_set(v_reuseFailAlloc_3070_, 1, v_snd_3057_);
v___x_3066_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
lean_object* v___x_3068_; 
if (v_isShared_3055_ == 0)
{
lean_ctor_set(v___x_3054_, 0, v___x_3066_);
v___x_3068_ = v___x_3054_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v___x_3066_);
lean_ctor_set(v_reuseFailAlloc_3069_, 1, v_a_3052_);
v___x_3068_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
return v___x_3068_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2884_, 2);
return v___x_3050_;
}
}
case 11:
{
lean_object* v_typeName_3073_; lean_object* v_idx_3074_; lean_object* v_struct_3075_; lean_object* v___x_3076_; 
v_typeName_3073_ = lean_ctor_get(v_e_2884_, 0);
v_idx_3074_ = lean_ctor_get(v_e_2884_, 1);
v_struct_3075_ = lean_ctor_get(v_e_2884_, 2);
lean_inc_ref(v_struct_3075_);
v___x_3076_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2882_, v_i_2883_, v_struct_3075_, v_offset_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_);
if (lean_obj_tag(v___x_3076_) == 0)
{
lean_object* v_a_3077_; lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3098_; 
v_a_3077_ = lean_ctor_get(v___x_3076_, 0);
v_a_3078_ = lean_ctor_get(v___x_3076_, 1);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3076_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3080_ = v___x_3076_;
v_isShared_3081_ = v_isSharedCheck_3098_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_inc(v_a_3077_);
lean_dec(v___x_3076_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3098_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v_fst_3082_; lean_object* v_snd_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3097_; 
v_fst_3082_ = lean_ctor_get(v_a_3077_, 0);
v_snd_3083_ = lean_ctor_get(v_a_3077_, 1);
v_isSharedCheck_3097_ = !lean_is_exclusive(v_a_3077_);
if (v_isSharedCheck_3097_ == 0)
{
v___x_3085_ = v_a_3077_;
v_isShared_3086_ = v_isSharedCheck_3097_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_snd_3083_);
lean_inc(v_fst_3082_);
lean_dec(v_a_3077_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3097_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
size_t v___x_3087_; size_t v___x_3088_; uint8_t v___x_3089_; 
v___x_3087_ = lean_ptr_addr(v_struct_3075_);
v___x_3088_ = lean_ptr_addr(v_fst_3082_);
v___x_3089_ = lean_usize_dec_eq(v___x_3087_, v___x_3088_);
if (v___x_3089_ == 0)
{
lean_object* v___x_3090_; 
lean_inc(v_idx_3074_);
lean_inc(v_typeName_3073_);
lean_del_object(v___x_3085_);
lean_del_object(v___x_3080_);
lean_dec_ref_known(v_e_2884_, 3);
v___x_3090_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__6(v_typeName_3073_, v_idx_3074_, v_fst_3082_, v_snd_3083_, v_a_2887_, v_a_2888_, v_a_3078_);
return v___x_3090_;
}
else
{
lean_object* v___x_3092_; 
lean_dec(v_fst_3082_);
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 0, v_e_2884_);
v___x_3092_ = v___x_3085_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v_e_2884_);
lean_ctor_set(v_reuseFailAlloc_3096_, 1, v_snd_3083_);
v___x_3092_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
lean_object* v___x_3094_; 
if (v_isShared_3081_ == 0)
{
lean_ctor_set(v___x_3080_, 0, v___x_3092_);
v___x_3094_ = v___x_3080_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v___x_3092_);
lean_ctor_set(v_reuseFailAlloc_3095_, 1, v_a_3078_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2884_, 3);
return v___x_3076_;
}
}
default: 
{
lean_object* v___x_3099_; lean_object* v___x_3100_; 
lean_dec(v_offset_2885_);
lean_dec_ref(v_e_2884_);
v___x_3099_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__3);
v___x_3100_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7(v___x_3099_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_);
return v___x_3100_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2882_ = stack[0].m_obj;
lean_object* v_i_2883_ = stack[1].m_obj;
lean_object* v_e_2884_ = stack[2].m_obj;
lean_object* v_offset_2885_ = stack[3].m_obj;
lean_object* v_a_2886_ = stack[4].m_obj;
uint8_t v_a_2887_ = stack[5].m_num;
lean_object* v_a_2888_ = stack[6].m_obj;
lean_object* v_a_2889_ = stack[7].m_obj;
lean_object* v_res_3101_;
v_res_3101_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5(v___x_2882_, v_i_2883_, v_e_2884_, v_offset_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_);
stack->m_obj
 = v_res_3101_;
}
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(lean_object* v___x_3102_, lean_object* v_i_3103_, lean_object* v_e_3104_, lean_object* v_offset_3105_, lean_object* v_a_3106_, uint8_t v_a_3107_, lean_object* v_a_3108_, lean_object* v_a_3109_){
_start:
{
lean_object* v_key_3110_; lean_object* v_a_3112_; lean_object* v___x_3125_; 
lean_inc(v_offset_3105_);
lean_inc_ref(v_e_3104_);
v_key_3110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_3110_, 0, v_e_3104_);
lean_ctor_set(v_key_3110_, 1, v_offset_3105_);
v___x_3125_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2___redArg(v_a_3106_, v_key_3110_);
if (lean_obj_tag(v___x_3125_) == 1)
{
lean_object* v_val_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; 
lean_dec_ref_known(v_key_3110_, 2);
lean_dec(v_offset_3105_);
lean_dec_ref(v_e_3104_);
v_val_3126_ = lean_ctor_get(v___x_3125_, 0);
lean_inc(v_val_3126_);
lean_dec_ref_known(v___x_3125_, 1);
v___x_3127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3127_, 0, v_val_3126_);
lean_ctor_set(v___x_3127_, 1, v_a_3106_);
v___x_3128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3128_, 0, v___x_3127_);
lean_ctor_set(v___x_3128_, 1, v_a_3109_);
return v___x_3128_;
}
else
{
lean_dec(v___x_3125_);
switch(lean_obj_tag(v_e_3104_))
{
case 1:
{
lean_object* v_fvarId_3129_; lean_object* v___x_3130_; 
v_fvarId_3129_ = lean_ctor_get(v_e_3104_, 0);
v___x_3130_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___redArg(v___x_3102_, v_fvarId_3129_);
if (lean_obj_tag(v___x_3130_) == 1)
{
lean_object* v_val_3131_; uint8_t v___x_3132_; 
v_val_3131_ = lean_ctor_get(v___x_3130_, 0);
lean_inc(v_val_3131_);
lean_dec_ref_known(v___x_3130_, 1);
v___x_3132_ = lean_nat_dec_lt(v_val_3131_, v_i_3103_);
if (v___x_3132_ == 0)
{
lean_object* v___x_3133_; lean_object* v___x_3134_; 
lean_dec(v_val_3131_);
v___x_3133_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2);
v___x_3134_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3(v___x_3133_, v_a_3107_, v_a_3108_, v_a_3109_);
if (lean_obj_tag(v___x_3134_) == 0)
{
lean_object* v_a_3135_; 
v_a_3135_ = lean_ctor_get(v___x_3134_, 0);
if (lean_obj_tag(v_a_3135_) == 1)
{
lean_object* v_a_3136_; lean_object* v_val_3137_; lean_object* v___x_3138_; 
lean_inc_ref(v_a_3135_);
lean_dec_ref_known(v_e_3104_, 1);
lean_dec(v_offset_3105_);
v_a_3136_ = lean_ctor_get(v___x_3134_, 1);
lean_inc(v_a_3136_);
lean_dec_ref_known(v___x_3134_, 2);
v_val_3137_ = lean_ctor_get(v_a_3135_, 0);
lean_inc(v_val_3137_);
lean_dec_ref_known(v_a_3135_, 1);
v___x_3138_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3110_, v_val_3137_, v_a_3106_, v_a_3107_, v_a_3108_, v_a_3136_);
return v___x_3138_;
}
else
{
lean_object* v_a_3139_; 
v_a_3139_ = lean_ctor_get(v___x_3134_, 1);
lean_inc(v_a_3139_);
lean_dec_ref_known(v___x_3134_, 2);
v_a_3112_ = v_a_3139_;
goto v___jp_3111_;
}
}
else
{
lean_object* v_a_3140_; lean_object* v_a_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3148_; 
lean_dec_ref_known(v_e_3104_, 1);
lean_dec_ref_known(v_key_3110_, 2);
lean_dec_ref(v_a_3106_);
lean_dec(v_offset_3105_);
v_a_3140_ = lean_ctor_get(v___x_3134_, 0);
v_a_3141_ = lean_ctor_get(v___x_3134_, 1);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3143_ = v___x_3134_;
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_a_3141_);
lean_inc(v_a_3140_);
lean_dec(v___x_3134_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3146_; 
if (v_isShared_3144_ == 0)
{
v___x_3146_ = v___x_3143_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_a_3140_);
lean_ctor_set(v_reuseFailAlloc_3147_, 1, v_a_3141_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
return v___x_3146_;
}
}
}
}
else
{
lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
lean_dec_ref_known(v_e_3104_, 1);
v___x_3149_ = lean_nat_add(v_offset_3105_, v_i_3103_);
lean_dec(v_offset_3105_);
v___x_3150_ = lean_nat_sub(v___x_3149_, v_val_3131_);
lean_dec(v_val_3131_);
lean_dec(v___x_3149_);
v___x_3151_ = lean_unsigned_to_nat(1u);
v___x_3152_ = lean_nat_sub(v___x_3150_, v___x_3151_);
lean_dec(v___x_3150_);
v___x_3153_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4___redArg(v___x_3152_, v_a_3109_);
if (lean_obj_tag(v___x_3153_) == 0)
{
lean_object* v_a_3154_; lean_object* v_a_3155_; lean_object* v___x_3156_; 
v_a_3154_ = lean_ctor_get(v___x_3153_, 0);
lean_inc(v_a_3154_);
v_a_3155_ = lean_ctor_get(v___x_3153_, 1);
lean_inc(v_a_3155_);
lean_dec_ref_known(v___x_3153_, 2);
v___x_3156_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3110_, v_a_3154_, v_a_3106_, v_a_3107_, v_a_3108_, v_a_3155_);
return v___x_3156_;
}
else
{
lean_object* v_a_3157_; lean_object* v_a_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3165_; 
lean_dec_ref_known(v_key_3110_, 2);
lean_dec_ref(v_a_3106_);
v_a_3157_ = lean_ctor_get(v___x_3153_, 0);
v_a_3158_ = lean_ctor_get(v___x_3153_, 1);
v_isSharedCheck_3165_ = !lean_is_exclusive(v___x_3153_);
if (v_isSharedCheck_3165_ == 0)
{
v___x_3160_ = v___x_3153_;
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_a_3158_);
lean_inc(v_a_3157_);
lean_dec(v___x_3153_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v___x_3163_; 
if (v_isShared_3161_ == 0)
{
v___x_3163_ = v___x_3160_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v_a_3157_);
lean_ctor_set(v_reuseFailAlloc_3164_, 1, v_a_3158_);
v___x_3163_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
return v___x_3163_;
}
}
}
}
}
else
{
lean_object* v___x_3166_; 
lean_dec(v___x_3130_);
lean_dec(v_offset_3105_);
v___x_3166_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3110_, v_e_3104_, v_a_3106_, v_a_3107_, v_a_3108_, v_a_3109_);
return v___x_3166_;
}
}
case 9:
{
lean_object* v___x_3167_; 
lean_dec(v_offset_3105_);
v___x_3167_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3110_, v_e_3104_, v_a_3106_, v_a_3107_, v_a_3108_, v_a_3109_);
return v___x_3167_;
}
case 2:
{
lean_object* v___x_3168_; 
lean_dec(v_offset_3105_);
v___x_3168_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3110_, v_e_3104_, v_a_3106_, v_a_3107_, v_a_3108_, v_a_3109_);
return v___x_3168_;
}
case 0:
{
lean_object* v___x_3169_; 
lean_dec(v_offset_3105_);
v___x_3169_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3110_, v_e_3104_, v_a_3106_, v_a_3107_, v_a_3108_, v_a_3109_);
return v___x_3169_;
}
case 4:
{
lean_object* v___x_3170_; 
lean_dec(v_offset_3105_);
v___x_3170_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3110_, v_e_3104_, v_a_3106_, v_a_3107_, v_a_3108_, v_a_3109_);
return v___x_3170_;
}
case 3:
{
lean_object* v___x_3171_; 
lean_dec(v_offset_3105_);
v___x_3171_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3110_, v_e_3104_, v_a_3106_, v_a_3107_, v_a_3108_, v_a_3109_);
return v___x_3171_;
}
default: 
{
uint8_t v___x_3172_; 
v___x_3172_ = l_Lean_Expr_hasFVar(v_e_3104_);
if (v___x_3172_ == 0)
{
lean_object* v___x_3173_; 
lean_dec(v_offset_3105_);
v___x_3173_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3110_, v_e_3104_, v_a_3106_, v_a_3107_, v_a_3108_, v_a_3109_);
return v___x_3173_;
}
else
{
v_a_3112_ = v_a_3109_;
goto v___jp_3111_;
}
}
}
}
v___jp_3111_:
{
switch(lean_obj_tag(v_e_3104_))
{
case 9:
{
lean_object* v___x_3113_; 
lean_dec(v_offset_3105_);
v___x_3113_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3110_, v_e_3104_, v_a_3106_, v_a_3107_, v_a_3108_, v_a_3112_);
return v___x_3113_;
}
case 2:
{
lean_object* v___x_3114_; 
lean_dec(v_offset_3105_);
v___x_3114_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3110_, v_e_3104_, v_a_3106_, v_a_3107_, v_a_3108_, v_a_3112_);
return v___x_3114_;
}
case 0:
{
lean_object* v___x_3115_; 
lean_dec(v_offset_3105_);
v___x_3115_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3110_, v_e_3104_, v_a_3106_, v_a_3107_, v_a_3108_, v_a_3112_);
return v___x_3115_;
}
case 1:
{
lean_object* v___x_3116_; 
lean_dec(v_offset_3105_);
v___x_3116_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3110_, v_e_3104_, v_a_3106_, v_a_3107_, v_a_3108_, v_a_3112_);
return v___x_3116_;
}
case 4:
{
lean_object* v___x_3117_; 
lean_dec(v_offset_3105_);
v___x_3117_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3110_, v_e_3104_, v_a_3106_, v_a_3107_, v_a_3108_, v_a_3112_);
return v___x_3117_;
}
case 3:
{
lean_object* v___x_3118_; 
lean_dec(v_offset_3105_);
v___x_3118_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3110_, v_e_3104_, v_a_3106_, v_a_3107_, v_a_3108_, v_a_3112_);
return v___x_3118_;
}
default: 
{
lean_object* v___x_3119_; 
v___x_3119_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5(v___x_3102_, v_i_3103_, v_e_3104_, v_offset_3105_, v_a_3106_, v_a_3107_, v_a_3108_, v_a_3112_);
if (lean_obj_tag(v___x_3119_) == 0)
{
lean_object* v_a_3120_; lean_object* v_a_3121_; lean_object* v_fst_3122_; lean_object* v_snd_3123_; lean_object* v___x_3124_; 
v_a_3120_ = lean_ctor_get(v___x_3119_, 0);
lean_inc(v_a_3120_);
v_a_3121_ = lean_ctor_get(v___x_3119_, 1);
lean_inc(v_a_3121_);
lean_dec_ref_known(v___x_3119_, 2);
v_fst_3122_ = lean_ctor_get(v_a_3120_, 0);
lean_inc(v_fst_3122_);
v_snd_3123_ = lean_ctor_get(v_a_3120_, 1);
lean_inc(v_snd_3123_);
lean_dec(v_a_3120_);
v___x_3124_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3110_, v_fst_3122_, v_snd_3123_, v_a_3107_, v_a_3108_, v_a_3121_);
return v___x_3124_;
}
else
{
lean_dec_ref_known(v_key_3110_, 2);
return v___x_3119_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3102_ = stack[0].m_obj;
lean_object* v_i_3103_ = stack[1].m_obj;
lean_object* v_e_3104_ = stack[2].m_obj;
lean_object* v_offset_3105_ = stack[3].m_obj;
lean_object* v_a_3106_ = stack[4].m_obj;
uint8_t v_a_3107_ = stack[5].m_num;
lean_object* v_a_3108_ = stack[6].m_obj;
lean_object* v_a_3109_ = stack[7].m_obj;
lean_object* v_res_3174_;
v_res_3174_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_3102_, v_i_3103_, v_e_3104_, v_offset_3105_, v_a_3106_, v_a_3107_, v_a_3108_, v_a_3109_);
stack->m_obj
 = v_res_3174_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___boxed(lean_object* v___x_3175_, lean_object* v_i_3176_, lean_object* v_e_3177_, lean_object* v_offset_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_){
_start:
{
uint8_t v_a_boxed_3183_; lean_object* v_res_3184_; 
v_a_boxed_3183_ = lean_unbox(v_a_3180_);
v_res_3184_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_3175_, v_i_3176_, v_e_3177_, v_offset_3178_, v_a_3179_, v_a_boxed_3183_, v_a_3181_, v_a_3182_);
lean_dec_ref(v_a_3181_);
lean_dec(v_i_3176_);
lean_dec_ref(v___x_3175_);
return v_res_3184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5___boxed(lean_object* v___x_3185_, lean_object* v_i_3186_, lean_object* v_e_3187_, lean_object* v_offset_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_){
_start:
{
uint8_t v_a_boxed_3193_; lean_object* v_res_3194_; 
v_a_boxed_3193_ = lean_unbox(v_a_3190_);
v_res_3194_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5(v___x_3185_, v_i_3186_, v_e_3187_, v_offset_3188_, v_a_3189_, v_a_boxed_3193_, v_a_3191_, v_a_3192_);
lean_dec_ref(v_a_3191_);
lean_dec(v_i_3186_);
lean_dec_ref(v___x_3185_);
return v_res_3194_;
}
}
lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___lam__0(lean_object* v_e_3195_, lean_object* v___x_3196_, lean_object* v___x_3197_, lean_object* v_fst_3198_, lean_object* v___x_3199_, uint8_t v_debug_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_){
_start:
{
lean_object* v_a_3204_; 
switch(lean_obj_tag(v_e_3195_))
{
case 1:
{
lean_object* v_fvarId_3234_; lean_object* v___x_3235_; 
v_fvarId_3234_ = lean_ctor_get(v_e_3195_, 0);
v___x_3235_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___redArg(v_fst_3198_, v_fvarId_3234_);
if (lean_obj_tag(v___x_3235_) == 1)
{
lean_object* v_val_3236_; uint8_t v___x_3237_; 
v_val_3236_ = lean_ctor_get(v___x_3235_, 0);
lean_inc(v_val_3236_);
lean_dec_ref_known(v___x_3235_, 1);
v___x_3237_ = lean_nat_dec_lt(v_val_3236_, v___x_3199_);
if (v___x_3237_ == 0)
{
lean_object* v___x_3238_; lean_object* v___x_3239_; 
lean_dec(v_val_3236_);
v___x_3238_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2);
v___x_3239_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3(v___x_3238_, v_debug_3200_, v___y_3201_, v___y_3202_);
if (lean_obj_tag(v___x_3239_) == 0)
{
lean_object* v_a_3240_; 
v_a_3240_ = lean_ctor_get(v___x_3239_, 0);
if (lean_obj_tag(v_a_3240_) == 1)
{
lean_object* v_a_3241_; lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3249_; 
lean_inc_ref(v_a_3240_);
lean_dec_ref_known(v_e_3195_, 1);
lean_dec(v___x_3197_);
lean_dec(v___x_3196_);
v_a_3241_ = lean_ctor_get(v___x_3239_, 1);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3239_);
if (v_isSharedCheck_3249_ == 0)
{
lean_object* v_unused_3250_; 
v_unused_3250_ = lean_ctor_get(v___x_3239_, 0);
lean_dec(v_unused_3250_);
v___x_3243_ = v___x_3239_;
v_isShared_3244_ = v_isSharedCheck_3249_;
goto v_resetjp_3242_;
}
else
{
lean_inc(v_a_3241_);
lean_dec(v___x_3239_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3249_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
lean_object* v_val_3245_; lean_object* v___x_3247_; 
v_val_3245_ = lean_ctor_get(v_a_3240_, 0);
lean_inc(v_val_3245_);
lean_dec_ref_known(v_a_3240_, 1);
if (v_isShared_3244_ == 0)
{
lean_ctor_set(v___x_3243_, 0, v_val_3245_);
v___x_3247_ = v___x_3243_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_val_3245_);
lean_ctor_set(v_reuseFailAlloc_3248_, 1, v_a_3241_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
}
else
{
lean_object* v_a_3251_; 
v_a_3251_ = lean_ctor_get(v___x_3239_, 1);
lean_inc(v_a_3251_);
lean_dec_ref_known(v___x_3239_, 2);
v_a_3204_ = v_a_3251_;
goto v___jp_3203_;
}
}
else
{
lean_object* v_a_3252_; lean_object* v_a_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3260_; 
lean_dec_ref_known(v_e_3195_, 1);
lean_dec(v___x_3197_);
lean_dec(v___x_3196_);
v_a_3252_ = lean_ctor_get(v___x_3239_, 0);
v_a_3253_ = lean_ctor_get(v___x_3239_, 1);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___x_3239_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3255_ = v___x_3239_;
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_a_3253_);
lean_inc(v_a_3252_);
lean_dec(v___x_3239_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v___x_3258_; 
if (v_isShared_3256_ == 0)
{
v___x_3258_ = v___x_3255_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_a_3252_);
lean_ctor_set(v_reuseFailAlloc_3259_, 1, v_a_3253_);
v___x_3258_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
return v___x_3258_;
}
}
}
}
else
{
lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; 
lean_dec_ref_known(v_e_3195_, 1);
lean_dec(v___x_3197_);
lean_dec(v___x_3196_);
v___x_3261_ = lean_nat_sub(v___x_3199_, v_val_3236_);
lean_dec(v_val_3236_);
v___x_3262_ = lean_unsigned_to_nat(1u);
v___x_3263_ = lean_nat_sub(v___x_3261_, v___x_3262_);
lean_dec(v___x_3261_);
v___x_3264_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4___redArg(v___x_3263_, v___y_3202_);
return v___x_3264_;
}
}
else
{
lean_object* v___x_3265_; 
lean_dec(v___x_3235_);
lean_dec(v___x_3197_);
lean_dec(v___x_3196_);
v___x_3265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3265_, 0, v_e_3195_);
lean_ctor_set(v___x_3265_, 1, v___y_3202_);
return v___x_3265_;
}
}
case 9:
{
lean_object* v___x_3266_; 
lean_dec(v___x_3197_);
lean_dec(v___x_3196_);
v___x_3266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3266_, 0, v_e_3195_);
lean_ctor_set(v___x_3266_, 1, v___y_3202_);
return v___x_3266_;
}
case 2:
{
lean_object* v___x_3267_; 
lean_dec(v___x_3197_);
lean_dec(v___x_3196_);
v___x_3267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3267_, 0, v_e_3195_);
lean_ctor_set(v___x_3267_, 1, v___y_3202_);
return v___x_3267_;
}
case 0:
{
lean_object* v___x_3268_; 
lean_dec(v___x_3197_);
lean_dec(v___x_3196_);
v___x_3268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3268_, 0, v_e_3195_);
lean_ctor_set(v___x_3268_, 1, v___y_3202_);
return v___x_3268_;
}
case 4:
{
lean_object* v___x_3269_; 
lean_dec(v___x_3197_);
lean_dec(v___x_3196_);
v___x_3269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3269_, 0, v_e_3195_);
lean_ctor_set(v___x_3269_, 1, v___y_3202_);
return v___x_3269_;
}
case 3:
{
lean_object* v___x_3270_; 
lean_dec(v___x_3197_);
lean_dec(v___x_3196_);
v___x_3270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3270_, 0, v_e_3195_);
lean_ctor_set(v___x_3270_, 1, v___y_3202_);
return v___x_3270_;
}
default: 
{
uint8_t v___x_3271_; 
v___x_3271_ = l_Lean_Expr_hasFVar(v_e_3195_);
if (v___x_3271_ == 0)
{
lean_object* v___x_3272_; 
lean_dec(v___x_3197_);
lean_dec(v___x_3196_);
v___x_3272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3272_, 0, v_e_3195_);
lean_ctor_set(v___x_3272_, 1, v___y_3202_);
return v___x_3272_;
}
else
{
v_a_3204_ = v___y_3202_;
goto v___jp_3203_;
}
}
}
v___jp_3203_:
{
switch(lean_obj_tag(v_e_3195_))
{
case 9:
{
lean_object* v___x_3205_; 
lean_dec(v___x_3197_);
lean_dec(v___x_3196_);
v___x_3205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3205_, 0, v_e_3195_);
lean_ctor_set(v___x_3205_, 1, v_a_3204_);
return v___x_3205_;
}
case 2:
{
lean_object* v___x_3206_; 
lean_dec(v___x_3197_);
lean_dec(v___x_3196_);
v___x_3206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3206_, 0, v_e_3195_);
lean_ctor_set(v___x_3206_, 1, v_a_3204_);
return v___x_3206_;
}
case 0:
{
lean_object* v___x_3207_; 
lean_dec(v___x_3197_);
lean_dec(v___x_3196_);
v___x_3207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3207_, 0, v_e_3195_);
lean_ctor_set(v___x_3207_, 1, v_a_3204_);
return v___x_3207_;
}
case 1:
{
lean_object* v___x_3208_; 
lean_dec(v___x_3197_);
lean_dec(v___x_3196_);
v___x_3208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3208_, 0, v_e_3195_);
lean_ctor_set(v___x_3208_, 1, v_a_3204_);
return v___x_3208_;
}
case 4:
{
lean_object* v___x_3209_; 
lean_dec(v___x_3197_);
lean_dec(v___x_3196_);
v___x_3209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3209_, 0, v_e_3195_);
lean_ctor_set(v___x_3209_, 1, v_a_3204_);
return v___x_3209_;
}
case 3:
{
lean_object* v___x_3210_; 
lean_dec(v___x_3197_);
lean_dec(v___x_3196_);
v___x_3210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3210_, 0, v_e_3195_);
lean_ctor_set(v___x_3210_, 1, v_a_3204_);
return v___x_3210_;
}
default: 
{
lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3211_ = lean_box(0);
v___x_3212_ = lean_mk_array(v___x_3196_, v___x_3211_);
lean_inc(v___x_3197_);
v___x_3213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3213_, 0, v___x_3197_);
lean_ctor_set(v___x_3213_, 1, v___x_3212_);
v___x_3214_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5(v_fst_3198_, v___x_3199_, v_e_3195_, v___x_3197_, v___x_3213_, v_debug_3200_, v___y_3201_, v_a_3204_);
if (lean_obj_tag(v___x_3214_) == 0)
{
lean_object* v_a_3215_; lean_object* v_a_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3224_; 
v_a_3215_ = lean_ctor_get(v___x_3214_, 0);
v_a_3216_ = lean_ctor_get(v___x_3214_, 1);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_3214_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3218_ = v___x_3214_;
v_isShared_3219_ = v_isSharedCheck_3224_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_a_3216_);
lean_inc(v_a_3215_);
lean_dec(v___x_3214_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3224_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v_fst_3220_; lean_object* v___x_3222_; 
v_fst_3220_ = lean_ctor_get(v_a_3215_, 0);
lean_inc(v_fst_3220_);
lean_dec(v_a_3215_);
if (v_isShared_3219_ == 0)
{
lean_ctor_set(v___x_3218_, 0, v_fst_3220_);
v___x_3222_ = v___x_3218_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v_fst_3220_);
lean_ctor_set(v_reuseFailAlloc_3223_, 1, v_a_3216_);
v___x_3222_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
return v___x_3222_;
}
}
}
else
{
lean_object* v_a_3225_; lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3233_; 
v_a_3225_ = lean_ctor_get(v___x_3214_, 0);
v_a_3226_ = lean_ctor_get(v___x_3214_, 1);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3214_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3228_ = v___x_3214_;
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_inc(v_a_3225_);
lean_dec(v___x_3214_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3231_; 
if (v_isShared_3229_ == 0)
{
v___x_3231_ = v___x_3228_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v_a_3225_);
lean_ctor_set(v_reuseFailAlloc_3232_, 1, v_a_3226_);
v___x_3231_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
return v___x_3231_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3195_ = stack[0].m_obj;
lean_object* v___x_3196_ = stack[1].m_obj;
lean_object* v___x_3197_ = stack[2].m_obj;
lean_object* v_fst_3198_ = stack[3].m_obj;
lean_object* v___x_3199_ = stack[4].m_obj;
uint8_t v_debug_3200_ = stack[5].m_num;
lean_object* v___y_3201_ = stack[6].m_obj;
lean_object* v___y_3202_ = stack[7].m_obj;
lean_object* v_res_3273_;
v_res_3273_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___lam__0(v_e_3195_, v___x_3196_, v___x_3197_, v_fst_3198_, v___x_3199_, v_debug_3200_, v___y_3201_, v___y_3202_);
stack->m_obj
 = v_res_3273_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___lam__0___boxed(lean_object* v_e_3274_, lean_object* v___x_3275_, lean_object* v___x_3276_, lean_object* v_fst_3277_, lean_object* v___x_3278_, lean_object* v_debug_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_){
_start:
{
uint8_t v_debug_boxed_3282_; lean_object* v_res_3283_; 
v_debug_boxed_3282_ = lean_unbox(v_debug_3279_);
v_res_3283_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___lam__0(v_e_3274_, v___x_3275_, v___x_3276_, v_fst_3277_, v___x_3278_, v_debug_boxed_3282_, v___y_3280_, v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec(v___x_3278_);
lean_dec(v_fst_3277_);
return v_res_3283_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__0(lean_object* v_piece_3284_, lean_object* v___x_3285_, lean_object* v___x_3286_, lean_object* v_i_3287_, uint8_t v_debug_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_){
_start:
{
lean_object* v_a_3292_; 
switch(lean_obj_tag(v_piece_3284_))
{
case 1:
{
lean_object* v_fvarId_3321_; lean_object* v___x_3322_; 
v_fvarId_3321_ = lean_ctor_get(v_piece_3284_, 0);
v___x_3322_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___redArg(v___x_3286_, v_fvarId_3321_);
if (lean_obj_tag(v___x_3322_) == 1)
{
lean_object* v_val_3323_; uint8_t v___x_3324_; 
v_val_3323_ = lean_ctor_get(v___x_3322_, 0);
lean_inc(v_val_3323_);
lean_dec_ref_known(v___x_3322_, 1);
v___x_3324_ = lean_nat_dec_lt(v_val_3323_, v_i_3287_);
if (v___x_3324_ == 0)
{
lean_object* v___x_3325_; lean_object* v___x_3326_; 
lean_dec(v_val_3323_);
v___x_3325_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2);
v___x_3326_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3(v___x_3325_, v_debug_3288_, v___y_3289_, v___y_3290_);
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v_a_3327_; 
v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
if (lean_obj_tag(v_a_3327_) == 1)
{
lean_object* v_a_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3336_; 
lean_inc_ref(v_a_3327_);
lean_dec_ref_known(v_piece_3284_, 1);
lean_dec(v___x_3285_);
v_a_3328_ = lean_ctor_get(v___x_3326_, 1);
v_isSharedCheck_3336_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3336_ == 0)
{
lean_object* v_unused_3337_; 
v_unused_3337_ = lean_ctor_get(v___x_3326_, 0);
lean_dec(v_unused_3337_);
v___x_3330_ = v___x_3326_;
v_isShared_3331_ = v_isSharedCheck_3336_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_a_3328_);
lean_dec(v___x_3326_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3336_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v_val_3332_; lean_object* v___x_3334_; 
v_val_3332_ = lean_ctor_get(v_a_3327_, 0);
lean_inc(v_val_3332_);
lean_dec_ref_known(v_a_3327_, 1);
if (v_isShared_3331_ == 0)
{
lean_ctor_set(v___x_3330_, 0, v_val_3332_);
v___x_3334_ = v___x_3330_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v_val_3332_);
lean_ctor_set(v_reuseFailAlloc_3335_, 1, v_a_3328_);
v___x_3334_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
return v___x_3334_;
}
}
}
else
{
lean_object* v_a_3338_; 
v_a_3338_ = lean_ctor_get(v___x_3326_, 1);
lean_inc(v_a_3338_);
lean_dec_ref_known(v___x_3326_, 2);
v_a_3292_ = v_a_3338_;
goto v___jp_3291_;
}
}
else
{
lean_object* v_a_3339_; lean_object* v_a_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3347_; 
lean_dec_ref_known(v_piece_3284_, 1);
lean_dec(v___x_3285_);
v_a_3339_ = lean_ctor_get(v___x_3326_, 0);
v_a_3340_ = lean_ctor_get(v___x_3326_, 1);
v_isSharedCheck_3347_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3342_ = v___x_3326_;
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_a_3340_);
lean_inc(v_a_3339_);
lean_dec(v___x_3326_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v___x_3345_; 
if (v_isShared_3343_ == 0)
{
v___x_3345_ = v___x_3342_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v_a_3339_);
lean_ctor_set(v_reuseFailAlloc_3346_, 1, v_a_3340_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
return v___x_3345_;
}
}
}
}
else
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; 
lean_dec_ref_known(v_piece_3284_, 1);
lean_dec(v___x_3285_);
v___x_3348_ = lean_nat_sub(v_i_3287_, v_val_3323_);
lean_dec(v_val_3323_);
v___x_3349_ = lean_unsigned_to_nat(1u);
v___x_3350_ = lean_nat_sub(v___x_3348_, v___x_3349_);
lean_dec(v___x_3348_);
v___x_3351_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4___redArg(v___x_3350_, v___y_3290_);
return v___x_3351_;
}
}
else
{
lean_object* v___x_3352_; 
lean_dec(v___x_3322_);
lean_dec(v___x_3285_);
v___x_3352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3352_, 0, v_piece_3284_);
lean_ctor_set(v___x_3352_, 1, v___y_3290_);
return v___x_3352_;
}
}
case 9:
{
lean_object* v___x_3353_; 
lean_dec(v___x_3285_);
v___x_3353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3353_, 0, v_piece_3284_);
lean_ctor_set(v___x_3353_, 1, v___y_3290_);
return v___x_3353_;
}
case 2:
{
lean_object* v___x_3354_; 
lean_dec(v___x_3285_);
v___x_3354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3354_, 0, v_piece_3284_);
lean_ctor_set(v___x_3354_, 1, v___y_3290_);
return v___x_3354_;
}
case 0:
{
lean_object* v___x_3355_; 
lean_dec(v___x_3285_);
v___x_3355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3355_, 0, v_piece_3284_);
lean_ctor_set(v___x_3355_, 1, v___y_3290_);
return v___x_3355_;
}
case 4:
{
lean_object* v___x_3356_; 
lean_dec(v___x_3285_);
v___x_3356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3356_, 0, v_piece_3284_);
lean_ctor_set(v___x_3356_, 1, v___y_3290_);
return v___x_3356_;
}
case 3:
{
lean_object* v___x_3357_; 
lean_dec(v___x_3285_);
v___x_3357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3357_, 0, v_piece_3284_);
lean_ctor_set(v___x_3357_, 1, v___y_3290_);
return v___x_3357_;
}
default: 
{
uint8_t v___x_3358_; 
v___x_3358_ = l_Lean_Expr_hasFVar(v_piece_3284_);
if (v___x_3358_ == 0)
{
lean_object* v___x_3359_; 
lean_dec(v___x_3285_);
v___x_3359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3359_, 0, v_piece_3284_);
lean_ctor_set(v___x_3359_, 1, v___y_3290_);
return v___x_3359_;
}
else
{
v_a_3292_ = v___y_3290_;
goto v___jp_3291_;
}
}
}
v___jp_3291_:
{
switch(lean_obj_tag(v_piece_3284_))
{
case 9:
{
lean_object* v___x_3293_; 
lean_dec(v___x_3285_);
v___x_3293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3293_, 0, v_piece_3284_);
lean_ctor_set(v___x_3293_, 1, v_a_3292_);
return v___x_3293_;
}
case 2:
{
lean_object* v___x_3294_; 
lean_dec(v___x_3285_);
v___x_3294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3294_, 0, v_piece_3284_);
lean_ctor_set(v___x_3294_, 1, v_a_3292_);
return v___x_3294_;
}
case 0:
{
lean_object* v___x_3295_; 
lean_dec(v___x_3285_);
v___x_3295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3295_, 0, v_piece_3284_);
lean_ctor_set(v___x_3295_, 1, v_a_3292_);
return v___x_3295_;
}
case 1:
{
lean_object* v___x_3296_; 
lean_dec(v___x_3285_);
v___x_3296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3296_, 0, v_piece_3284_);
lean_ctor_set(v___x_3296_, 1, v_a_3292_);
return v___x_3296_;
}
case 4:
{
lean_object* v___x_3297_; 
lean_dec(v___x_3285_);
v___x_3297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3297_, 0, v_piece_3284_);
lean_ctor_set(v___x_3297_, 1, v_a_3292_);
return v___x_3297_;
}
case 3:
{
lean_object* v___x_3298_; 
lean_dec(v___x_3285_);
v___x_3298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3298_, 0, v_piece_3284_);
lean_ctor_set(v___x_3298_, 1, v_a_3292_);
return v___x_3298_;
}
default: 
{
lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3299_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__0, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__0_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__0);
lean_inc(v___x_3285_);
v___x_3300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3285_);
lean_ctor_set(v___x_3300_, 1, v___x_3299_);
v___x_3301_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5(v___x_3286_, v_i_3287_, v_piece_3284_, v___x_3285_, v___x_3300_, v_debug_3288_, v___y_3289_, v_a_3292_);
if (lean_obj_tag(v___x_3301_) == 0)
{
lean_object* v_a_3302_; lean_object* v_a_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3311_; 
v_a_3302_ = lean_ctor_get(v___x_3301_, 0);
v_a_3303_ = lean_ctor_get(v___x_3301_, 1);
v_isSharedCheck_3311_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3311_ == 0)
{
v___x_3305_ = v___x_3301_;
v_isShared_3306_ = v_isSharedCheck_3311_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_a_3303_);
lean_inc(v_a_3302_);
lean_dec(v___x_3301_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3311_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v_fst_3307_; lean_object* v___x_3309_; 
v_fst_3307_ = lean_ctor_get(v_a_3302_, 0);
lean_inc(v_fst_3307_);
lean_dec(v_a_3302_);
if (v_isShared_3306_ == 0)
{
lean_ctor_set(v___x_3305_, 0, v_fst_3307_);
v___x_3309_ = v___x_3305_;
goto v_reusejp_3308_;
}
else
{
lean_object* v_reuseFailAlloc_3310_; 
v_reuseFailAlloc_3310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3310_, 0, v_fst_3307_);
lean_ctor_set(v_reuseFailAlloc_3310_, 1, v_a_3303_);
v___x_3309_ = v_reuseFailAlloc_3310_;
goto v_reusejp_3308_;
}
v_reusejp_3308_:
{
return v___x_3309_;
}
}
}
else
{
lean_object* v_a_3312_; lean_object* v_a_3313_; lean_object* v___x_3315_; uint8_t v_isShared_3316_; uint8_t v_isSharedCheck_3320_; 
v_a_3312_ = lean_ctor_get(v___x_3301_, 0);
v_a_3313_ = lean_ctor_get(v___x_3301_, 1);
v_isSharedCheck_3320_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3320_ == 0)
{
v___x_3315_ = v___x_3301_;
v_isShared_3316_ = v_isSharedCheck_3320_;
goto v_resetjp_3314_;
}
else
{
lean_inc(v_a_3313_);
lean_inc(v_a_3312_);
lean_dec(v___x_3301_);
v___x_3315_ = lean_box(0);
v_isShared_3316_ = v_isSharedCheck_3320_;
goto v_resetjp_3314_;
}
v_resetjp_3314_:
{
lean_object* v___x_3318_; 
if (v_isShared_3316_ == 0)
{
v___x_3318_ = v___x_3315_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v_a_3312_);
lean_ctor_set(v_reuseFailAlloc_3319_, 1, v_a_3313_);
v___x_3318_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
return v___x_3318_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_piece_3284_ = stack[0].m_obj;
lean_object* v___x_3285_ = stack[1].m_obj;
lean_object* v___x_3286_ = stack[2].m_obj;
lean_object* v_i_3287_ = stack[3].m_obj;
uint8_t v_debug_3288_ = stack[4].m_num;
lean_object* v___y_3289_ = stack[5].m_obj;
lean_object* v___y_3290_ = stack[6].m_obj;
lean_object* v_res_3360_;
v_res_3360_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__0(v_piece_3284_, v___x_3285_, v___x_3286_, v_i_3287_, v_debug_3288_, v___y_3289_, v___y_3290_);
stack->m_obj
 = v_res_3360_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__0___boxed(lean_object* v_piece_3361_, lean_object* v___x_3362_, lean_object* v___x_3363_, lean_object* v_i_3364_, lean_object* v_debug_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_){
_start:
{
uint8_t v_debug_boxed_3368_; lean_object* v_res_3369_; 
v_debug_boxed_3368_ = lean_unbox(v_debug_3365_);
v_res_3369_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__0(v_piece_3361_, v___x_3362_, v___x_3363_, v_i_3364_, v_debug_boxed_3368_, v___y_3366_, v___y_3367_);
lean_dec_ref(v___y_3366_);
lean_dec(v_i_3364_);
lean_dec_ref(v___x_3363_);
return v_res_3369_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__1(lean_object* v___x_3370_, lean_object* v___x_3371_, uint8_t v___x_3372_, lean_object* v_piece_3373_, lean_object* v_i_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_){
_start:
{
lean_object* v___x_3383_; uint8_t v_debug_3384_; lean_object* v___x_3385_; lean_object* v___f_3386_; lean_object* v___x_3387_; lean_object* v_env_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; 
v___x_3383_ = lean_st_ref_get(v___y_3377_);
v_debug_3384_ = lean_ctor_get_uint8(v___x_3383_, sizeof(void*)*12);
lean_dec(v___x_3383_);
v___x_3385_ = lean_box(v_debug_3384_);
v___f_3386_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__0___boxed), 7, 5);
lean_closure_set(v___f_3386_, 0, v_piece_3373_);
lean_closure_set(v___f_3386_, 1, v___x_3370_);
lean_closure_set(v___f_3386_, 2, v___x_3371_);
lean_closure_set(v___f_3386_, 3, v_i_3374_);
lean_closure_set(v___f_3386_, 4, v___x_3385_);
v___x_3387_ = lean_st_ref_get(v___y_3381_);
v_env_3388_ = lean_ctor_get(v___x_3387_, 0);
lean_inc_ref(v_env_3388_);
lean_dec(v___x_3387_);
v___x_3389_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_3389_, 0, v_env_3388_);
lean_ctor_set_uint8(v___x_3389_, sizeof(void*)*1, v___x_3372_);
lean_ctor_set_uint8(v___x_3389_, sizeof(void*)*1 + 1, v___x_3372_);
v___x_3390_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_3386_, v___x_3389_, v___y_3377_);
if (lean_obj_tag(v___x_3390_) == 0)
{
lean_object* v_a_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3401_; 
v_a_3391_ = lean_ctor_get(v___x_3390_, 0);
v_isSharedCheck_3401_ = !lean_is_exclusive(v___x_3390_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3393_ = v___x_3390_;
v_isShared_3394_ = v_isSharedCheck_3401_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_a_3391_);
lean_dec(v___x_3390_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3401_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
if (lean_obj_tag(v_a_3391_) == 0)
{
lean_object* v___x_3395_; lean_object* v___x_3396_; 
lean_dec_ref_known(v_a_3391_, 1);
lean_del_object(v___x_3393_);
v___x_3395_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2);
v___x_3396_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1(v___x_3395_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
return v___x_3396_;
}
else
{
lean_object* v_a_3397_; lean_object* v___x_3399_; 
v_a_3397_ = lean_ctor_get(v_a_3391_, 0);
lean_inc(v_a_3397_);
lean_dec_ref_known(v_a_3391_, 1);
if (v_isShared_3394_ == 0)
{
lean_ctor_set(v___x_3393_, 0, v_a_3397_);
v___x_3399_ = v___x_3393_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_a_3397_);
v___x_3399_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
return v___x_3399_;
}
}
}
}
else
{
lean_object* v_a_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3409_; 
v_a_3402_ = lean_ctor_get(v___x_3390_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3390_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3404_ = v___x_3390_;
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_a_3402_);
lean_dec(v___x_3390_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___x_3407_; 
if (v_isShared_3405_ == 0)
{
v___x_3407_ = v___x_3404_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_a_3402_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3370_ = stack[0].m_obj;
lean_object* v___x_3371_ = stack[1].m_obj;
uint8_t v___x_3372_ = stack[2].m_num;
lean_object* v_piece_3373_ = stack[3].m_obj;
lean_object* v_i_3374_ = stack[4].m_obj;
lean_object* v___y_3375_ = stack[5].m_obj;
lean_object* v___y_3376_ = stack[6].m_obj;
lean_object* v___y_3377_ = stack[7].m_obj;
lean_object* v___y_3378_ = stack[8].m_obj;
lean_object* v___y_3379_ = stack[9].m_obj;
lean_object* v___y_3380_ = stack[10].m_obj;
lean_object* v___y_3381_ = stack[11].m_obj;
lean_object* v_res_3410_;
v_res_3410_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__1(v___x_3370_, v___x_3371_, v___x_3372_, v_piece_3373_, v_i_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
stack->m_obj
 = v_res_3410_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__1___boxed(lean_object* v___x_3411_, lean_object* v___x_3412_, lean_object* v___x_3413_, lean_object* v_piece_3414_, lean_object* v_i_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_){
_start:
{
uint8_t v___x_17413__boxed_3424_; lean_object* v_res_3425_; 
v___x_17413__boxed_3424_ = lean_unbox(v___x_3413_);
v_res_3425_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__1(v___x_3411_, v___x_3412_, v___x_17413__boxed_3424_, v_piece_3414_, v_i_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_);
lean_dec(v___y_3422_);
lean_dec_ref(v___y_3421_);
lean_dec(v___y_3420_);
lean_dec_ref(v___y_3419_);
lean_dec(v___y_3418_);
lean_dec_ref(v___y_3417_);
lean_dec(v___y_3416_);
return v_res_3425_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7_spec__12(lean_object* v___x_3426_, lean_object* v___x_3427_, lean_object* v_as_3428_, size_t v_sz_3429_, size_t v_i_3430_, lean_object* v_b_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_){
_start:
{
uint8_t v___x_3440_; 
v___x_3440_ = lean_usize_dec_lt(v_i_3430_, v_sz_3429_);
if (v___x_3440_ == 0)
{
lean_object* v___x_3441_; 
lean_dec_ref(v___x_3426_);
v___x_3441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3441_, 0, v_b_3431_);
return v___x_3441_;
}
else
{
lean_object* v_fst_3442_; lean_object* v_snd_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3492_; 
v_fst_3442_ = lean_ctor_get(v_b_3431_, 0);
v_snd_3443_ = lean_ctor_get(v_b_3431_, 1);
v_isSharedCheck_3492_ = !lean_is_exclusive(v_b_3431_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3445_ = v_b_3431_;
v_isShared_3446_ = v_isSharedCheck_3492_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_snd_3443_);
lean_inc(v_fst_3442_);
lean_dec(v_b_3431_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3492_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v_a_3447_; lean_object* v_userName_3448_; lean_object* v_type_3449_; lean_object* v_value_3450_; uint8_t v_nondep_3451_; lean_object* v___x_3452_; uint8_t v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; 
v_a_3447_ = lean_array_uget_borrowed(v_as_3428_, v_i_3430_);
v_userName_3448_ = lean_ctor_get(v_a_3447_, 1);
v_type_3449_ = lean_ctor_get(v_a_3447_, 2);
v_value_3450_ = lean_ctor_get(v_a_3447_, 3);
v_nondep_3451_ = lean_ctor_get_uint8(v_a_3447_, sizeof(void*)*4);
v___x_3452_ = lean_unsigned_to_nat(0u);
v___x_3453_ = lean_nat_dec_eq(v___x_3427_, v___x_3452_);
v___x_3454_ = lean_unsigned_to_nat(1u);
v___x_3455_ = lean_nat_sub(v_snd_3443_, v___x_3454_);
lean_dec(v_snd_3443_);
lean_inc(v___x_3455_);
lean_inc_ref(v_type_3449_);
lean_inc_ref(v___x_3426_);
v___x_3456_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__1(v___x_3452_, v___x_3426_, v___x_3453_, v_type_3449_, v___x_3455_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v_a_3457_; lean_object* v___x_3458_; 
v_a_3457_ = lean_ctor_get(v___x_3456_, 0);
lean_inc(v_a_3457_);
lean_dec_ref_known(v___x_3456_, 1);
lean_inc(v___x_3455_);
lean_inc_ref(v_value_3450_);
lean_inc_ref(v___x_3426_);
v___x_3458_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__1(v___x_3452_, v___x_3426_, v___x_3453_, v_value_3450_, v___x_3455_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_);
if (lean_obj_tag(v___x_3458_) == 0)
{
lean_object* v_a_3459_; lean_object* v___x_3460_; 
v_a_3459_ = lean_ctor_get(v___x_3458_, 0);
lean_inc(v_a_3459_);
lean_dec_ref_known(v___x_3458_, 1);
lean_inc(v_userName_3448_);
v___x_3460_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6___redArg(v_userName_3448_, v_a_3457_, v_a_3459_, v_fst_3442_, v_nondep_3451_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v_a_3461_; lean_object* v___x_3463_; 
v_a_3461_ = lean_ctor_get(v___x_3460_, 0);
lean_inc(v_a_3461_);
lean_dec_ref_known(v___x_3460_, 1);
if (v_isShared_3446_ == 0)
{
lean_ctor_set(v___x_3445_, 1, v___x_3455_);
lean_ctor_set(v___x_3445_, 0, v_a_3461_);
v___x_3463_ = v___x_3445_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_a_3461_);
lean_ctor_set(v_reuseFailAlloc_3467_, 1, v___x_3455_);
v___x_3463_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
size_t v___x_3464_; size_t v___x_3465_; 
v___x_3464_ = ((size_t)1ULL);
v___x_3465_ = lean_usize_add(v_i_3430_, v___x_3464_);
v_i_3430_ = v___x_3465_;
v_b_3431_ = v___x_3463_;
goto _start;
}
}
else
{
lean_object* v_a_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3475_; 
lean_dec(v___x_3455_);
lean_del_object(v___x_3445_);
lean_dec_ref(v___x_3426_);
v_a_3468_ = lean_ctor_get(v___x_3460_, 0);
v_isSharedCheck_3475_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3470_ = v___x_3460_;
v_isShared_3471_ = v_isSharedCheck_3475_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_a_3468_);
lean_dec(v___x_3460_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3475_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v___x_3473_; 
if (v_isShared_3471_ == 0)
{
v___x_3473_ = v___x_3470_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_a_3468_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
return v___x_3473_;
}
}
}
}
else
{
lean_object* v_a_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3483_; 
lean_dec(v_a_3457_);
lean_dec(v___x_3455_);
lean_del_object(v___x_3445_);
lean_dec(v_fst_3442_);
lean_dec_ref(v___x_3426_);
v_a_3476_ = lean_ctor_get(v___x_3458_, 0);
v_isSharedCheck_3483_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3483_ == 0)
{
v___x_3478_ = v___x_3458_;
v_isShared_3479_ = v_isSharedCheck_3483_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_a_3476_);
lean_dec(v___x_3458_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3483_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
lean_object* v___x_3481_; 
if (v_isShared_3479_ == 0)
{
v___x_3481_ = v___x_3478_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_a_3476_);
v___x_3481_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
return v___x_3481_;
}
}
}
}
else
{
lean_object* v_a_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3491_; 
lean_dec(v___x_3455_);
lean_del_object(v___x_3445_);
lean_dec(v_fst_3442_);
lean_dec_ref(v___x_3426_);
v_a_3484_ = lean_ctor_get(v___x_3456_, 0);
v_isSharedCheck_3491_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3491_ == 0)
{
v___x_3486_ = v___x_3456_;
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_a_3484_);
lean_dec(v___x_3456_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___x_3489_; 
if (v_isShared_3487_ == 0)
{
v___x_3489_ = v___x_3486_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v_a_3484_);
v___x_3489_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
return v___x_3489_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3426_ = stack[0].m_obj;
lean_object* v___x_3427_ = stack[1].m_obj;
lean_object* v_as_3428_ = stack[2].m_obj;
size_t v_sz_3429_ = stack[3].m_num;
size_t v_i_3430_ = stack[4].m_num;
lean_object* v_b_3431_ = stack[5].m_obj;
lean_object* v___y_3432_ = stack[6].m_obj;
lean_object* v___y_3433_ = stack[7].m_obj;
lean_object* v___y_3434_ = stack[8].m_obj;
lean_object* v___y_3435_ = stack[9].m_obj;
lean_object* v___y_3436_ = stack[10].m_obj;
lean_object* v___y_3437_ = stack[11].m_obj;
lean_object* v___y_3438_ = stack[12].m_obj;
lean_object* v_res_3493_;
v_res_3493_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7_spec__12(v___x_3426_, v___x_3427_, v_as_3428_, v_sz_3429_, v_i_3430_, v_b_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_);
stack->m_obj
 = v_res_3493_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7_spec__12___boxed(lean_object* v___x_3494_, lean_object* v___x_3495_, lean_object* v_as_3496_, lean_object* v_sz_3497_, lean_object* v_i_3498_, lean_object* v_b_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_){
_start:
{
size_t v_sz_boxed_3508_; size_t v_i_boxed_3509_; lean_object* v_res_3510_; 
v_sz_boxed_3508_ = lean_unbox_usize(v_sz_3497_);
lean_dec(v_sz_3497_);
v_i_boxed_3509_ = lean_unbox_usize(v_i_3498_);
lean_dec(v_i_3498_);
v_res_3510_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7_spec__12(v___x_3494_, v___x_3495_, v_as_3496_, v_sz_boxed_3508_, v_i_boxed_3509_, v_b_3499_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_);
lean_dec(v___y_3506_);
lean_dec_ref(v___y_3505_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
lean_dec(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec(v___y_3500_);
lean_dec_ref(v_as_3496_);
lean_dec(v___x_3495_);
return v_res_3510_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7(lean_object* v___x_3511_, lean_object* v___x_3512_, lean_object* v_as_3513_, size_t v_sz_3514_, size_t v_i_3515_, lean_object* v_b_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_){
_start:
{
uint8_t v___x_3525_; 
v___x_3525_ = lean_usize_dec_lt(v_i_3515_, v_sz_3514_);
if (v___x_3525_ == 0)
{
lean_object* v___x_3526_; 
lean_dec_ref(v___x_3511_);
v___x_3526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3526_, 0, v_b_3516_);
return v___x_3526_;
}
else
{
lean_object* v_fst_3527_; lean_object* v_snd_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3577_; 
v_fst_3527_ = lean_ctor_get(v_b_3516_, 0);
v_snd_3528_ = lean_ctor_get(v_b_3516_, 1);
v_isSharedCheck_3577_ = !lean_is_exclusive(v_b_3516_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3530_ = v_b_3516_;
v_isShared_3531_ = v_isSharedCheck_3577_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_snd_3528_);
lean_inc(v_fst_3527_);
lean_dec(v_b_3516_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3577_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v_a_3532_; lean_object* v_userName_3533_; lean_object* v_type_3534_; lean_object* v_value_3535_; uint8_t v_nondep_3536_; lean_object* v___x_3537_; uint8_t v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; 
v_a_3532_ = lean_array_uget_borrowed(v_as_3513_, v_i_3515_);
v_userName_3533_ = lean_ctor_get(v_a_3532_, 1);
v_type_3534_ = lean_ctor_get(v_a_3532_, 2);
v_value_3535_ = lean_ctor_get(v_a_3532_, 3);
v_nondep_3536_ = lean_ctor_get_uint8(v_a_3532_, sizeof(void*)*4);
v___x_3537_ = lean_unsigned_to_nat(0u);
v___x_3538_ = lean_nat_dec_eq(v___x_3512_, v___x_3537_);
v___x_3539_ = lean_unsigned_to_nat(1u);
v___x_3540_ = lean_nat_sub(v_snd_3528_, v___x_3539_);
lean_dec(v_snd_3528_);
lean_inc(v___x_3540_);
lean_inc_ref(v_type_3534_);
lean_inc_ref(v___x_3511_);
v___x_3541_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__1(v___x_3537_, v___x_3511_, v___x_3538_, v_type_3534_, v___x_3540_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_);
if (lean_obj_tag(v___x_3541_) == 0)
{
lean_object* v_a_3542_; lean_object* v___x_3543_; 
v_a_3542_ = lean_ctor_get(v___x_3541_, 0);
lean_inc(v_a_3542_);
lean_dec_ref_known(v___x_3541_, 1);
lean_inc(v___x_3540_);
lean_inc_ref(v_value_3535_);
lean_inc_ref(v___x_3511_);
v___x_3543_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__1(v___x_3537_, v___x_3511_, v___x_3538_, v_value_3535_, v___x_3540_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_);
if (lean_obj_tag(v___x_3543_) == 0)
{
lean_object* v_a_3544_; lean_object* v___x_3545_; 
v_a_3544_ = lean_ctor_get(v___x_3543_, 0);
lean_inc(v_a_3544_);
lean_dec_ref_known(v___x_3543_, 1);
lean_inc(v_userName_3533_);
v___x_3545_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6___redArg(v_userName_3533_, v_a_3542_, v_a_3544_, v_fst_3527_, v_nondep_3536_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_);
if (lean_obj_tag(v___x_3545_) == 0)
{
lean_object* v_a_3546_; lean_object* v___x_3548_; 
v_a_3546_ = lean_ctor_get(v___x_3545_, 0);
lean_inc(v_a_3546_);
lean_dec_ref_known(v___x_3545_, 1);
if (v_isShared_3531_ == 0)
{
lean_ctor_set(v___x_3530_, 1, v___x_3540_);
lean_ctor_set(v___x_3530_, 0, v_a_3546_);
v___x_3548_ = v___x_3530_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_a_3546_);
lean_ctor_set(v_reuseFailAlloc_3552_, 1, v___x_3540_);
v___x_3548_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
size_t v___x_3549_; size_t v___x_3550_; lean_object* v___x_3551_; 
v___x_3549_ = ((size_t)1ULL);
v___x_3550_ = lean_usize_add(v_i_3515_, v___x_3549_);
v___x_3551_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7_spec__12(v___x_3511_, v___x_3512_, v_as_3513_, v_sz_3514_, v___x_3550_, v___x_3548_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_);
return v___x_3551_;
}
}
else
{
lean_object* v_a_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3560_; 
lean_dec(v___x_3540_);
lean_del_object(v___x_3530_);
lean_dec_ref(v___x_3511_);
v_a_3553_ = lean_ctor_get(v___x_3545_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3545_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3555_ = v___x_3545_;
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_a_3553_);
lean_dec(v___x_3545_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3558_; 
if (v_isShared_3556_ == 0)
{
v___x_3558_ = v___x_3555_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_a_3553_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
}
}
else
{
lean_object* v_a_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3568_; 
lean_dec(v_a_3542_);
lean_dec(v___x_3540_);
lean_del_object(v___x_3530_);
lean_dec(v_fst_3527_);
lean_dec_ref(v___x_3511_);
v_a_3561_ = lean_ctor_get(v___x_3543_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3563_ = v___x_3543_;
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_a_3561_);
lean_dec(v___x_3543_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3566_; 
if (v_isShared_3564_ == 0)
{
v___x_3566_ = v___x_3563_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_a_3561_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
return v___x_3566_;
}
}
}
}
else
{
lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3576_; 
lean_dec(v___x_3540_);
lean_del_object(v___x_3530_);
lean_dec(v_fst_3527_);
lean_dec_ref(v___x_3511_);
v_a_3569_ = lean_ctor_get(v___x_3541_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3541_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3571_ = v___x_3541_;
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_a_3569_);
lean_dec(v___x_3541_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3574_; 
if (v_isShared_3572_ == 0)
{
v___x_3574_ = v___x_3571_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_a_3569_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3511_ = stack[0].m_obj;
lean_object* v___x_3512_ = stack[1].m_obj;
lean_object* v_as_3513_ = stack[2].m_obj;
size_t v_sz_3514_ = stack[3].m_num;
size_t v_i_3515_ = stack[4].m_num;
lean_object* v_b_3516_ = stack[5].m_obj;
lean_object* v___y_3517_ = stack[6].m_obj;
lean_object* v___y_3518_ = stack[7].m_obj;
lean_object* v___y_3519_ = stack[8].m_obj;
lean_object* v___y_3520_ = stack[9].m_obj;
lean_object* v___y_3521_ = stack[10].m_obj;
lean_object* v___y_3522_ = stack[11].m_obj;
lean_object* v___y_3523_ = stack[12].m_obj;
lean_object* v_res_3578_;
v_res_3578_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7(v___x_3511_, v___x_3512_, v_as_3513_, v_sz_3514_, v_i_3515_, v_b_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_);
stack->m_obj
 = v_res_3578_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___boxed(lean_object* v___x_3579_, lean_object* v___x_3580_, lean_object* v_as_3581_, lean_object* v_sz_3582_, lean_object* v_i_3583_, lean_object* v_b_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_){
_start:
{
size_t v_sz_boxed_3593_; size_t v_i_boxed_3594_; lean_object* v_res_3595_; 
v_sz_boxed_3593_ = lean_unbox_usize(v_sz_3582_);
lean_dec(v_sz_3582_);
v_i_boxed_3594_ = lean_unbox_usize(v_i_3583_);
lean_dec(v_i_3583_);
v_res_3595_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7(v___x_3579_, v___x_3580_, v_as_3581_, v_sz_boxed_3593_, v_i_boxed_3594_, v_b_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_);
lean_dec(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec(v___y_3589_);
lean_dec_ref(v___y_3588_);
lean_dec(v___y_3587_);
lean_dec_ref(v___y_3586_);
lean_dec(v___y_3585_);
lean_dec_ref(v_as_3581_);
lean_dec(v___x_3580_);
return v_res_3595_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0___redArg(lean_object* v_a_3596_, lean_object* v_x_3597_){
_start:
{
if (lean_obj_tag(v_x_3597_) == 0)
{
uint8_t v___x_3598_; 
v___x_3598_ = 0;
return v___x_3598_;
}
else
{
lean_object* v_key_3599_; lean_object* v_tail_3600_; uint8_t v___x_3601_; 
v_key_3599_ = lean_ctor_get(v_x_3597_, 0);
v_tail_3600_ = lean_ctor_get(v_x_3597_, 2);
v___x_3601_ = l_Lean_instBEqFVarId_beq(v_key_3599_, v_a_3596_);
if (v___x_3601_ == 0)
{
v_x_3597_ = v_tail_3600_;
goto _start;
}
else
{
return v___x_3601_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3596_ = stack[0].m_obj;
lean_object* v_x_3597_ = stack[1].m_obj;
uint8_t v_res_3603_;
v_res_3603_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0___redArg(v_a_3596_, v_x_3597_);
stack->m_num = v_res_3603_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0___redArg___boxed(lean_object* v_a_3604_, lean_object* v_x_3605_){
_start:
{
uint8_t v_res_3606_; lean_object* v_r_3607_; 
v_res_3606_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0___redArg(v_a_3604_, v_x_3605_);
lean_dec(v_x_3605_);
lean_dec(v_a_3604_);
v_r_3607_ = lean_box(v_res_3606_);
return v_r_3607_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1_spec__5_spec__10___redArg(lean_object* v_x_3608_, lean_object* v_x_3609_){
_start:
{
if (lean_obj_tag(v_x_3609_) == 0)
{
return v_x_3608_;
}
else
{
lean_object* v_key_3610_; lean_object* v_value_3611_; lean_object* v_tail_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3635_; 
v_key_3610_ = lean_ctor_get(v_x_3609_, 0);
v_value_3611_ = lean_ctor_get(v_x_3609_, 1);
v_tail_3612_ = lean_ctor_get(v_x_3609_, 2);
v_isSharedCheck_3635_ = !lean_is_exclusive(v_x_3609_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3614_ = v_x_3609_;
v_isShared_3615_ = v_isSharedCheck_3635_;
goto v_resetjp_3613_;
}
else
{
lean_inc(v_tail_3612_);
lean_inc(v_value_3611_);
lean_inc(v_key_3610_);
lean_dec(v_x_3609_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3635_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v___x_3616_; uint64_t v___x_3617_; uint64_t v___x_3618_; uint64_t v___x_3619_; uint64_t v_fold_3620_; uint64_t v___x_3621_; uint64_t v___x_3622_; uint64_t v___x_3623_; size_t v___x_3624_; size_t v___x_3625_; size_t v___x_3626_; size_t v___x_3627_; size_t v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3631_; 
v___x_3616_ = lean_array_get_size(v_x_3608_);
v___x_3617_ = l_Lean_instHashableFVarId_hash(v_key_3610_);
v___x_3618_ = 32ULL;
v___x_3619_ = lean_uint64_shift_right(v___x_3617_, v___x_3618_);
v_fold_3620_ = lean_uint64_xor(v___x_3617_, v___x_3619_);
v___x_3621_ = 16ULL;
v___x_3622_ = lean_uint64_shift_right(v_fold_3620_, v___x_3621_);
v___x_3623_ = lean_uint64_xor(v_fold_3620_, v___x_3622_);
v___x_3624_ = lean_uint64_to_usize(v___x_3623_);
v___x_3625_ = lean_usize_of_nat(v___x_3616_);
v___x_3626_ = ((size_t)1ULL);
v___x_3627_ = lean_usize_sub(v___x_3625_, v___x_3626_);
v___x_3628_ = lean_usize_land(v___x_3624_, v___x_3627_);
v___x_3629_ = lean_array_uget_borrowed(v_x_3608_, v___x_3628_);
lean_inc(v___x_3629_);
if (v_isShared_3615_ == 0)
{
lean_ctor_set(v___x_3614_, 2, v___x_3629_);
v___x_3631_ = v___x_3614_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v_key_3610_);
lean_ctor_set(v_reuseFailAlloc_3634_, 1, v_value_3611_);
lean_ctor_set(v_reuseFailAlloc_3634_, 2, v___x_3629_);
v___x_3631_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
lean_object* v___x_3632_; 
v___x_3632_ = lean_array_uset(v_x_3608_, v___x_3628_, v___x_3631_);
v_x_3608_ = v___x_3632_;
v_x_3609_ = v_tail_3612_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1_spec__5___redArg(lean_object* v_i_3636_, lean_object* v_source_3637_, lean_object* v_target_3638_){
_start:
{
lean_object* v___x_3639_; uint8_t v___x_3640_; 
v___x_3639_ = lean_array_get_size(v_source_3637_);
v___x_3640_ = lean_nat_dec_lt(v_i_3636_, v___x_3639_);
if (v___x_3640_ == 0)
{
lean_dec_ref(v_source_3637_);
lean_dec(v_i_3636_);
return v_target_3638_;
}
else
{
lean_object* v_es_3641_; lean_object* v___x_3642_; lean_object* v_source_3643_; lean_object* v_target_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
v_es_3641_ = lean_array_fget(v_source_3637_, v_i_3636_);
v___x_3642_ = lean_box(0);
v_source_3643_ = lean_array_fset(v_source_3637_, v_i_3636_, v___x_3642_);
v_target_3644_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1_spec__5_spec__10___redArg(v_target_3638_, v_es_3641_);
v___x_3645_ = lean_unsigned_to_nat(1u);
v___x_3646_ = lean_nat_add(v_i_3636_, v___x_3645_);
lean_dec(v_i_3636_);
v_i_3636_ = v___x_3646_;
v_source_3637_ = v_source_3643_;
v_target_3638_ = v_target_3644_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1___redArg(lean_object* v_data_3648_){
_start:
{
lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v_nbuckets_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; 
v___x_3649_ = lean_array_get_size(v_data_3648_);
v___x_3650_ = lean_unsigned_to_nat(2u);
v_nbuckets_3651_ = lean_nat_mul(v___x_3649_, v___x_3650_);
v___x_3652_ = lean_unsigned_to_nat(0u);
v___x_3653_ = lean_box(0);
v___x_3654_ = lean_mk_array(v_nbuckets_3651_, v___x_3653_);
v___x_3655_ = lean_array_propagate_mark(v_data_3648_, v___x_3654_);
v___x_3656_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1_spec__5___redArg(v___x_3652_, v_data_3648_, v___x_3655_);
return v___x_3656_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__2___redArg(lean_object* v_a_3657_, lean_object* v_b_3658_, lean_object* v_x_3659_){
_start:
{
if (lean_obj_tag(v_x_3659_) == 0)
{
lean_dec(v_b_3658_);
lean_dec(v_a_3657_);
return v_x_3659_;
}
else
{
lean_object* v_key_3660_; lean_object* v_value_3661_; lean_object* v_tail_3662_; lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3674_; 
v_key_3660_ = lean_ctor_get(v_x_3659_, 0);
v_value_3661_ = lean_ctor_get(v_x_3659_, 1);
v_tail_3662_ = lean_ctor_get(v_x_3659_, 2);
v_isSharedCheck_3674_ = !lean_is_exclusive(v_x_3659_);
if (v_isSharedCheck_3674_ == 0)
{
v___x_3664_ = v_x_3659_;
v_isShared_3665_ = v_isSharedCheck_3674_;
goto v_resetjp_3663_;
}
else
{
lean_inc(v_tail_3662_);
lean_inc(v_value_3661_);
lean_inc(v_key_3660_);
lean_dec(v_x_3659_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3674_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
uint8_t v___x_3666_; 
v___x_3666_ = l_Lean_instBEqFVarId_beq(v_key_3660_, v_a_3657_);
if (v___x_3666_ == 0)
{
lean_object* v___x_3667_; lean_object* v___x_3669_; 
v___x_3667_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__2___redArg(v_a_3657_, v_b_3658_, v_tail_3662_);
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 2, v___x_3667_);
v___x_3669_ = v___x_3664_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_key_3660_);
lean_ctor_set(v_reuseFailAlloc_3670_, 1, v_value_3661_);
lean_ctor_set(v_reuseFailAlloc_3670_, 2, v___x_3667_);
v___x_3669_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
return v___x_3669_;
}
}
else
{
lean_object* v___x_3672_; 
lean_dec(v_value_3661_);
lean_dec(v_key_3660_);
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 1, v_b_3658_);
lean_ctor_set(v___x_3664_, 0, v_a_3657_);
v___x_3672_ = v___x_3664_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v_a_3657_);
lean_ctor_set(v_reuseFailAlloc_3673_, 1, v_b_3658_);
lean_ctor_set(v_reuseFailAlloc_3673_, 2, v_tail_3662_);
v___x_3672_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
return v___x_3672_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0___redArg(lean_object* v_m_3675_, lean_object* v_a_3676_, lean_object* v_b_3677_){
_start:
{
lean_object* v_size_3678_; lean_object* v_buckets_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3722_; 
v_size_3678_ = lean_ctor_get(v_m_3675_, 0);
v_buckets_3679_ = lean_ctor_get(v_m_3675_, 1);
v_isSharedCheck_3722_ = !lean_is_exclusive(v_m_3675_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3681_ = v_m_3675_;
v_isShared_3682_ = v_isSharedCheck_3722_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_buckets_3679_);
lean_inc(v_size_3678_);
lean_dec(v_m_3675_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3722_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v___x_3683_; uint64_t v___x_3684_; uint64_t v___x_3685_; uint64_t v___x_3686_; uint64_t v_fold_3687_; uint64_t v___x_3688_; uint64_t v___x_3689_; uint64_t v___x_3690_; size_t v___x_3691_; size_t v___x_3692_; size_t v___x_3693_; size_t v___x_3694_; size_t v___x_3695_; lean_object* v_bkt_3696_; uint8_t v___x_3697_; 
v___x_3683_ = lean_array_get_size(v_buckets_3679_);
v___x_3684_ = l_Lean_instHashableFVarId_hash(v_a_3676_);
v___x_3685_ = 32ULL;
v___x_3686_ = lean_uint64_shift_right(v___x_3684_, v___x_3685_);
v_fold_3687_ = lean_uint64_xor(v___x_3684_, v___x_3686_);
v___x_3688_ = 16ULL;
v___x_3689_ = lean_uint64_shift_right(v_fold_3687_, v___x_3688_);
v___x_3690_ = lean_uint64_xor(v_fold_3687_, v___x_3689_);
v___x_3691_ = lean_uint64_to_usize(v___x_3690_);
v___x_3692_ = lean_usize_of_nat(v___x_3683_);
v___x_3693_ = ((size_t)1ULL);
v___x_3694_ = lean_usize_sub(v___x_3692_, v___x_3693_);
v___x_3695_ = lean_usize_land(v___x_3691_, v___x_3694_);
v_bkt_3696_ = lean_array_uget_borrowed(v_buckets_3679_, v___x_3695_);
v___x_3697_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0___redArg(v_a_3676_, v_bkt_3696_);
if (v___x_3697_ == 0)
{
lean_object* v___x_3698_; lean_object* v_size_x27_3699_; lean_object* v___x_3700_; lean_object* v_buckets_x27_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; uint8_t v___x_3707_; 
v___x_3698_ = lean_unsigned_to_nat(1u);
v_size_x27_3699_ = lean_nat_add(v_size_3678_, v___x_3698_);
lean_dec(v_size_3678_);
lean_inc(v_bkt_3696_);
v___x_3700_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3700_, 0, v_a_3676_);
lean_ctor_set(v___x_3700_, 1, v_b_3677_);
lean_ctor_set(v___x_3700_, 2, v_bkt_3696_);
v_buckets_x27_3701_ = lean_array_uset(v_buckets_3679_, v___x_3695_, v___x_3700_);
v___x_3702_ = lean_unsigned_to_nat(4u);
v___x_3703_ = lean_nat_mul(v_size_x27_3699_, v___x_3702_);
v___x_3704_ = lean_unsigned_to_nat(3u);
v___x_3705_ = lean_nat_div(v___x_3703_, v___x_3704_);
lean_dec(v___x_3703_);
v___x_3706_ = lean_array_get_size(v_buckets_x27_3701_);
v___x_3707_ = lean_nat_dec_le(v___x_3705_, v___x_3706_);
lean_dec(v___x_3705_);
if (v___x_3707_ == 0)
{
lean_object* v_val_3708_; lean_object* v___x_3710_; 
v_val_3708_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1___redArg(v_buckets_x27_3701_);
if (v_isShared_3682_ == 0)
{
lean_ctor_set(v___x_3681_, 1, v_val_3708_);
lean_ctor_set(v___x_3681_, 0, v_size_x27_3699_);
v___x_3710_ = v___x_3681_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v_size_x27_3699_);
lean_ctor_set(v_reuseFailAlloc_3711_, 1, v_val_3708_);
v___x_3710_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
return v___x_3710_;
}
}
else
{
lean_object* v___x_3713_; 
if (v_isShared_3682_ == 0)
{
lean_ctor_set(v___x_3681_, 1, v_buckets_x27_3701_);
lean_ctor_set(v___x_3681_, 0, v_size_x27_3699_);
v___x_3713_ = v___x_3681_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v_size_x27_3699_);
lean_ctor_set(v_reuseFailAlloc_3714_, 1, v_buckets_x27_3701_);
v___x_3713_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
return v___x_3713_;
}
}
}
else
{
lean_object* v___x_3715_; lean_object* v_buckets_x27_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3720_; 
lean_inc(v_bkt_3696_);
v___x_3715_ = lean_box(0);
v_buckets_x27_3716_ = lean_array_uset(v_buckets_3679_, v___x_3695_, v___x_3715_);
v___x_3717_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__2___redArg(v_a_3676_, v_b_3677_, v_bkt_3696_);
v___x_3718_ = lean_array_uset(v_buckets_x27_3716_, v___x_3695_, v___x_3717_);
if (v_isShared_3682_ == 0)
{
lean_ctor_set(v___x_3681_, 1, v___x_3718_);
v___x_3720_ = v___x_3681_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_size_3678_);
lean_ctor_set(v_reuseFailAlloc_3721_, 1, v___x_3718_);
v___x_3720_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
return v___x_3720_;
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1___redArg(lean_object* v_as_3723_, size_t v_sz_3724_, size_t v_i_3725_, lean_object* v_b_3726_){
_start:
{
uint8_t v___x_3728_; 
v___x_3728_ = lean_usize_dec_lt(v_i_3725_, v_sz_3724_);
if (v___x_3728_ == 0)
{
lean_object* v___x_3729_; 
v___x_3729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3729_, 0, v_b_3726_);
return v___x_3729_;
}
else
{
lean_object* v_fst_3730_; lean_object* v_snd_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3747_; 
v_fst_3730_ = lean_ctor_get(v_b_3726_, 0);
v_snd_3731_ = lean_ctor_get(v_b_3726_, 1);
v_isSharedCheck_3747_ = !lean_is_exclusive(v_b_3726_);
if (v_isSharedCheck_3747_ == 0)
{
v___x_3733_ = v_b_3726_;
v_isShared_3734_ = v_isSharedCheck_3747_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_snd_3731_);
lean_inc(v_fst_3730_);
lean_dec(v_b_3726_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3747_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v_a_3735_; lean_object* v_fvar_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3742_; 
v_a_3735_ = lean_array_uget_borrowed(v_as_3723_, v_i_3725_);
v_fvar_3736_ = lean_ctor_get(v_a_3735_, 0);
v___x_3737_ = l_Lean_Expr_fvarId_x21(v_fvar_3736_);
lean_inc(v_snd_3731_);
v___x_3738_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0___redArg(v_fst_3730_, v___x_3737_, v_snd_3731_);
v___x_3739_ = lean_unsigned_to_nat(1u);
v___x_3740_ = lean_nat_add(v_snd_3731_, v___x_3739_);
lean_dec(v_snd_3731_);
if (v_isShared_3734_ == 0)
{
lean_ctor_set(v___x_3733_, 1, v___x_3740_);
lean_ctor_set(v___x_3733_, 0, v___x_3738_);
v___x_3742_ = v___x_3733_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v___x_3738_);
lean_ctor_set(v_reuseFailAlloc_3746_, 1, v___x_3740_);
v___x_3742_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
size_t v___x_3743_; size_t v___x_3744_; 
v___x_3743_ = ((size_t)1ULL);
v___x_3744_ = lean_usize_add(v_i_3725_, v___x_3743_);
v_i_3725_ = v___x_3744_;
v_b_3726_ = v___x_3742_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3723_ = stack[0].m_obj;
size_t v_sz_3724_ = stack[1].m_num;
size_t v_i_3725_ = stack[2].m_num;
lean_object* v_b_3726_ = stack[3].m_obj;
lean_object* v_res_3748_;
v_res_3748_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1___redArg(v_as_3723_, v_sz_3724_, v_i_3725_, v_b_3726_);
stack->m_obj
 = v_res_3748_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1___redArg___boxed(lean_object* v_as_3749_, lean_object* v_sz_3750_, lean_object* v_i_3751_, lean_object* v_b_3752_, lean_object* v___y_3753_){
_start:
{
size_t v_sz_boxed_3754_; size_t v_i_boxed_3755_; lean_object* v_res_3756_; 
v_sz_boxed_3754_ = lean_unbox_usize(v_sz_3750_);
lean_dec(v_sz_3750_);
v_i_boxed_3755_ = lean_unbox_usize(v_i_3751_);
lean_dec(v_i_3751_);
v_res_3756_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1___redArg(v_as_3749_, v_sz_boxed_3754_, v_i_boxed_3755_, v_b_3752_);
lean_dec_ref(v_as_3749_);
return v_res_3756_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__0(void){
_start:
{
lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; 
v___x_3757_ = lean_box(0);
v___x_3758_ = lean_unsigned_to_nat(16u);
v___x_3759_ = lean_mk_array(v___x_3758_, v___x_3757_);
return v___x_3759_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__1(void){
_start:
{
lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; 
v___x_3760_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__0, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__0_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__0);
v___x_3761_ = lean_unsigned_to_nat(0u);
v___x_3762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3762_, 0, v___x_3761_);
lean_ctor_set(v___x_3762_, 1, v___x_3760_);
return v___x_3762_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__2(void){
_start:
{
lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; 
v___x_3763_ = lean_unsigned_to_nat(0u);
v___x_3764_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__1, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__1_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__1);
v___x_3765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3765_, 0, v___x_3764_);
lean_ctor_set(v___x_3765_, 1, v___x_3763_);
return v___x_3765_;
}
}
lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets(lean_object* v_e_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_){
_start:
{
lean_object* v___x_3775_; lean_object* v_decls_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; uint8_t v___x_3779_; 
v___x_3775_ = lean_st_ref_get(v_a_3767_);
v_decls_3776_ = lean_ctor_get(v___x_3775_, 3);
lean_inc_ref(v_decls_3776_);
lean_dec(v___x_3775_);
v___x_3777_ = lean_array_get_size(v_decls_3776_);
v___x_3778_ = lean_unsigned_to_nat(0u);
v___x_3779_ = lean_nat_dec_eq(v___x_3777_, v___x_3778_);
if (v___x_3779_ == 0)
{
lean_object* v___x_3780_; lean_object* v___x_3781_; size_t v_sz_3782_; size_t v___x_3783_; lean_object* v___x_3784_; 
v___x_3780_ = lean_unsigned_to_nat(16u);
v___x_3781_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__2);
v_sz_3782_ = lean_array_size(v_decls_3776_);
v___x_3783_ = ((size_t)0ULL);
v___x_3784_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1___redArg(v_decls_3776_, v_sz_3782_, v___x_3783_, v___x_3781_);
if (lean_obj_tag(v___x_3784_) == 0)
{
lean_object* v_a_3785_; lean_object* v_fst_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3836_; 
v_a_3785_ = lean_ctor_get(v___x_3784_, 0);
lean_inc(v_a_3785_);
lean_dec_ref_known(v___x_3784_, 1);
v_fst_3786_ = lean_ctor_get(v_a_3785_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v_a_3785_);
if (v_isSharedCheck_3836_ == 0)
{
lean_object* v_unused_3837_; 
v_unused_3837_ = lean_ctor_get(v_a_3785_, 1);
lean_dec(v_unused_3837_);
v___x_3788_ = v_a_3785_;
v_isShared_3789_ = v_isSharedCheck_3836_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_fst_3786_);
lean_dec(v_a_3785_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3836_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v_a_3791_; lean_object* v___x_3815_; uint8_t v_debug_3816_; lean_object* v___x_3817_; lean_object* v___f_3818_; lean_object* v___x_3819_; lean_object* v_env_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; 
v___x_3815_ = lean_st_ref_get(v_a_3769_);
v_debug_3816_ = lean_ctor_get_uint8(v___x_3815_, sizeof(void*)*12);
lean_dec(v___x_3815_);
v___x_3817_ = lean_box(v_debug_3816_);
lean_inc(v_fst_3786_);
v___f_3818_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___lam__0___boxed), 8, 6);
lean_closure_set(v___f_3818_, 0, v_e_3766_);
lean_closure_set(v___f_3818_, 1, v___x_3780_);
lean_closure_set(v___f_3818_, 2, v___x_3778_);
lean_closure_set(v___f_3818_, 3, v_fst_3786_);
lean_closure_set(v___f_3818_, 4, v___x_3777_);
lean_closure_set(v___f_3818_, 5, v___x_3817_);
v___x_3819_ = lean_st_ref_get(v_a_3773_);
v_env_3820_ = lean_ctor_get(v___x_3819_, 0);
lean_inc_ref(v_env_3820_);
lean_dec(v___x_3819_);
v___x_3821_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_3821_, 0, v_env_3820_);
lean_ctor_set_uint8(v___x_3821_, sizeof(void*)*1, v___x_3779_);
lean_ctor_set_uint8(v___x_3821_, sizeof(void*)*1 + 1, v___x_3779_);
v___x_3822_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_3818_, v___x_3821_, v_a_3769_);
if (lean_obj_tag(v___x_3822_) == 0)
{
lean_object* v_a_3823_; 
v_a_3823_ = lean_ctor_get(v___x_3822_, 0);
lean_inc(v_a_3823_);
lean_dec_ref_known(v___x_3822_, 1);
if (lean_obj_tag(v_a_3823_) == 0)
{
lean_object* v___x_3824_; lean_object* v___x_3825_; 
lean_dec_ref_known(v_a_3823_, 1);
v___x_3824_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2);
v___x_3825_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1(v___x_3824_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_);
if (lean_obj_tag(v___x_3825_) == 0)
{
lean_object* v_a_3826_; 
v_a_3826_ = lean_ctor_get(v___x_3825_, 0);
lean_inc(v_a_3826_);
lean_dec_ref_known(v___x_3825_, 1);
v_a_3791_ = v_a_3826_;
goto v___jp_3790_;
}
else
{
lean_del_object(v___x_3788_);
lean_dec(v_fst_3786_);
lean_dec_ref(v_decls_3776_);
return v___x_3825_;
}
}
else
{
lean_object* v_a_3827_; 
v_a_3827_ = lean_ctor_get(v_a_3823_, 0);
lean_inc(v_a_3827_);
lean_dec_ref_known(v_a_3823_, 1);
v_a_3791_ = v_a_3827_;
goto v___jp_3790_;
}
}
else
{
lean_object* v_a_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3835_; 
lean_del_object(v___x_3788_);
lean_dec(v_fst_3786_);
lean_dec_ref(v_decls_3776_);
v_a_3828_ = lean_ctor_get(v___x_3822_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v___x_3822_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3830_ = v___x_3822_;
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_a_3828_);
lean_dec(v___x_3822_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___x_3833_; 
if (v_isShared_3831_ == 0)
{
v___x_3833_ = v___x_3830_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v_a_3828_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
return v___x_3833_;
}
}
}
v___jp_3790_:
{
lean_object* v___x_3792_; lean_object* v___x_3794_; 
v___x_3792_ = l_Array_reverse___redArg(v_decls_3776_);
if (v_isShared_3789_ == 0)
{
lean_ctor_set(v___x_3788_, 1, v___x_3777_);
lean_ctor_set(v___x_3788_, 0, v_a_3791_);
v___x_3794_ = v___x_3788_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v_a_3791_);
lean_ctor_set(v_reuseFailAlloc_3814_, 1, v___x_3777_);
v___x_3794_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
size_t v_sz_3795_; lean_object* v___x_3796_; 
v_sz_3795_ = lean_array_size(v___x_3792_);
v___x_3796_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7(v_fst_3786_, v___x_3777_, v___x_3792_, v_sz_3795_, v___x_3783_, v___x_3794_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_);
lean_dec_ref(v___x_3792_);
if (lean_obj_tag(v___x_3796_) == 0)
{
lean_object* v_a_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3805_; 
v_a_3797_ = lean_ctor_get(v___x_3796_, 0);
v_isSharedCheck_3805_ = !lean_is_exclusive(v___x_3796_);
if (v_isSharedCheck_3805_ == 0)
{
v___x_3799_ = v___x_3796_;
v_isShared_3800_ = v_isSharedCheck_3805_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_a_3797_);
lean_dec(v___x_3796_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3805_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v_fst_3801_; lean_object* v___x_3803_; 
v_fst_3801_ = lean_ctor_get(v_a_3797_, 0);
lean_inc(v_fst_3801_);
lean_dec(v_a_3797_);
if (v_isShared_3800_ == 0)
{
lean_ctor_set(v___x_3799_, 0, v_fst_3801_);
v___x_3803_ = v___x_3799_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v_fst_3801_);
v___x_3803_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
return v___x_3803_;
}
}
}
else
{
lean_object* v_a_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3813_; 
v_a_3806_ = lean_ctor_get(v___x_3796_, 0);
v_isSharedCheck_3813_ = !lean_is_exclusive(v___x_3796_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3808_ = v___x_3796_;
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_a_3806_);
lean_dec(v___x_3796_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3811_; 
if (v_isShared_3809_ == 0)
{
v___x_3811_ = v___x_3808_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_a_3806_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3838_; lean_object* v___x_3840_; uint8_t v_isShared_3841_; uint8_t v_isSharedCheck_3845_; 
lean_dec_ref(v_decls_3776_);
lean_dec_ref(v_e_3766_);
v_a_3838_ = lean_ctor_get(v___x_3784_, 0);
v_isSharedCheck_3845_ = !lean_is_exclusive(v___x_3784_);
if (v_isSharedCheck_3845_ == 0)
{
v___x_3840_ = v___x_3784_;
v_isShared_3841_ = v_isSharedCheck_3845_;
goto v_resetjp_3839_;
}
else
{
lean_inc(v_a_3838_);
lean_dec(v___x_3784_);
v___x_3840_ = lean_box(0);
v_isShared_3841_ = v_isSharedCheck_3845_;
goto v_resetjp_3839_;
}
v_resetjp_3839_:
{
lean_object* v___x_3843_; 
if (v_isShared_3841_ == 0)
{
v___x_3843_ = v___x_3840_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3844_; 
v_reuseFailAlloc_3844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3844_, 0, v_a_3838_);
v___x_3843_ = v_reuseFailAlloc_3844_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
return v___x_3843_;
}
}
}
}
else
{
lean_object* v___x_3846_; 
lean_dec_ref(v_decls_3776_);
v___x_3846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3846_, 0, v_e_3766_);
return v___x_3846_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3766_ = stack[0].m_obj;
lean_object* v_a_3767_ = stack[1].m_obj;
lean_object* v_a_3768_ = stack[2].m_obj;
lean_object* v_a_3769_ = stack[3].m_obj;
lean_object* v_a_3770_ = stack[4].m_obj;
lean_object* v_a_3771_ = stack[5].m_obj;
lean_object* v_a_3772_ = stack[6].m_obj;
lean_object* v_a_3773_ = stack[7].m_obj;
lean_object* v_res_3847_;
v_res_3847_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets(v_e_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_);
stack->m_obj
 = v_res_3847_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___boxed(lean_object* v_e_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_){
_start:
{
lean_object* v_res_3857_; 
v_res_3857_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets(v_e_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_);
lean_dec(v_a_3855_);
lean_dec_ref(v_a_3854_);
lean_dec(v_a_3853_);
lean_dec_ref(v_a_3852_);
lean_dec(v_a_3851_);
lean_dec_ref(v_a_3850_);
lean_dec(v_a_3849_);
return v_res_3857_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0(lean_object* v_00_u03b2_3858_, lean_object* v_m_3859_, lean_object* v_a_3860_, lean_object* v_b_3861_){
_start:
{
lean_object* v___x_3862_; 
v___x_3862_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0___redArg(v_m_3859_, v_a_3860_, v_b_3861_);
return v___x_3862_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1(lean_object* v_as_3863_, size_t v_sz_3864_, size_t v_i_3865_, lean_object* v_b_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_){
_start:
{
lean_object* v___x_3875_; 
v___x_3875_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1___redArg(v_as_3863_, v_sz_3864_, v_i_3865_, v_b_3866_);
return v___x_3875_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3863_ = stack[0].m_obj;
size_t v_sz_3864_ = stack[1].m_num;
size_t v_i_3865_ = stack[2].m_num;
lean_object* v_b_3866_ = stack[3].m_obj;
lean_object* v___y_3867_ = stack[4].m_obj;
lean_object* v___y_3868_ = stack[5].m_obj;
lean_object* v___y_3869_ = stack[6].m_obj;
lean_object* v___y_3870_ = stack[7].m_obj;
lean_object* v___y_3871_ = stack[8].m_obj;
lean_object* v___y_3872_ = stack[9].m_obj;
lean_object* v___y_3873_ = stack[10].m_obj;
lean_object* v_res_3876_;
v_res_3876_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1(v_as_3863_, v_sz_3864_, v_i_3865_, v_b_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_);
stack->m_obj
 = v_res_3876_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1___boxed(lean_object* v_as_3877_, lean_object* v_sz_3878_, lean_object* v_i_3879_, lean_object* v_b_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_){
_start:
{
size_t v_sz_boxed_3889_; size_t v_i_boxed_3890_; lean_object* v_res_3891_; 
v_sz_boxed_3889_ = lean_unbox_usize(v_sz_3878_);
lean_dec(v_sz_3878_);
v_i_boxed_3890_ = lean_unbox_usize(v_i_3879_);
lean_dec(v_i_3879_);
v_res_3891_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1(v_as_3877_, v_sz_boxed_3889_, v_i_boxed_3890_, v_b_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_);
lean_dec(v___y_3887_);
lean_dec_ref(v___y_3886_);
lean_dec(v___y_3885_);
lean_dec_ref(v___y_3884_);
lean_dec(v___y_3883_);
lean_dec_ref(v___y_3882_);
lean_dec(v___y_3881_);
lean_dec_ref(v_as_3877_);
return v_res_3891_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2(lean_object* v_00_u03b2_3892_, lean_object* v_m_3893_, lean_object* v_a_3894_){
_start:
{
lean_object* v___x_3895_; 
v___x_3895_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___redArg(v_m_3893_, v_a_3894_);
return v___x_3895_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___boxed(lean_object* v_00_u03b2_3896_, lean_object* v_m_3897_, lean_object* v_a_3898_){
_start:
{
lean_object* v_res_3899_; 
v_res_3899_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2(v_00_u03b2_3896_, v_m_3897_, v_a_3898_);
lean_dec(v_a_3898_);
lean_dec_ref(v_m_3897_);
return v_res_3899_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0(lean_object* v_00_u03b2_3900_, lean_object* v_a_3901_, lean_object* v_x_3902_){
_start:
{
uint8_t v___x_3903_; 
v___x_3903_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0___redArg(v_a_3901_, v_x_3902_);
return v___x_3903_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3901_ = stack[1].m_obj;
lean_object* v_x_3902_ = stack[2].m_obj;
uint8_t v_res_3904_;
v_res_3904_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0(lean_box(0), v_a_3901_, v_x_3902_);
stack->m_num = v_res_3904_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3905_, lean_object* v_a_3906_, lean_object* v_x_3907_){
_start:
{
uint8_t v_res_3908_; lean_object* v_r_3909_; 
v_res_3908_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0(v_00_u03b2_3905_, v_a_3906_, v_x_3907_);
lean_dec(v_x_3907_);
lean_dec(v_a_3906_);
v_r_3909_ = lean_box(v_res_3908_);
return v_r_3909_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1(lean_object* v_00_u03b2_3910_, lean_object* v_data_3911_){
_start:
{
lean_object* v___x_3912_; 
v___x_3912_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1___redArg(v_data_3911_);
return v___x_3912_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__2(lean_object* v_00_u03b2_3913_, lean_object* v_a_3914_, lean_object* v_b_3915_, lean_object* v_x_3916_){
_start:
{
lean_object* v___x_3917_; 
v___x_3917_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__2___redArg(v_a_3914_, v_b_3915_, v_x_3916_);
return v___x_3917_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2_spec__5(lean_object* v_00_u03b2_3918_, lean_object* v_a_3919_, lean_object* v_x_3920_){
_start:
{
lean_object* v___x_3921_; 
v___x_3921_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2_spec__5___redArg(v_a_3919_, v_x_3920_);
return v___x_3921_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3922_, lean_object* v_a_3923_, lean_object* v_x_3924_){
_start:
{
lean_object* v_res_3925_; 
v_res_3925_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2_spec__5(v_00_u03b2_3922_, v_a_3923_, v_x_3924_);
lean_dec(v_x_3924_);
lean_dec(v_a_3923_);
return v_res_3925_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_3926_, lean_object* v_i_3927_, lean_object* v_source_3928_, lean_object* v_target_3929_){
_start:
{
lean_object* v___x_3930_; 
v___x_3930_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1_spec__5___redArg(v_i_3927_, v_source_3928_, v_target_3929_);
return v___x_3930_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1_spec__5_spec__10(lean_object* v_00_u03b2_3931_, lean_object* v_x_3932_, lean_object* v_x_3933_){
_start:
{
lean_object* v___x_3934_; 
v___x_3934_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1_spec__5_spec__10___redArg(v_x_3932_, v_x_3933_);
return v___x_3934_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0___redArg(lean_object* v_msg_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_){
_start:
{
lean_object* v_ref_3941_; lean_object* v___x_3942_; lean_object* v_a_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_3951_; 
v_ref_3941_ = lean_ctor_get(v___y_3938_, 2);
v___x_3942_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5_spec__5(v_msg_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_);
v_a_3943_ = lean_ctor_get(v___x_3942_, 0);
v_isSharedCheck_3951_ = !lean_is_exclusive(v___x_3942_);
if (v_isSharedCheck_3951_ == 0)
{
v___x_3945_ = v___x_3942_;
v_isShared_3946_ = v_isSharedCheck_3951_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_a_3943_);
lean_dec(v___x_3942_);
v___x_3945_ = lean_box(0);
v_isShared_3946_ = v_isSharedCheck_3951_;
goto v_resetjp_3944_;
}
v_resetjp_3944_:
{
lean_object* v___x_3947_; lean_object* v___x_3949_; 
lean_inc(v_ref_3941_);
v___x_3947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3947_, 0, v_ref_3941_);
lean_ctor_set(v___x_3947_, 1, v_a_3943_);
if (v_isShared_3946_ == 0)
{
lean_ctor_set_tag(v___x_3945_, 1);
lean_ctor_set(v___x_3945_, 0, v___x_3947_);
v___x_3949_ = v___x_3945_;
goto v_reusejp_3948_;
}
else
{
lean_object* v_reuseFailAlloc_3950_; 
v_reuseFailAlloc_3950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3950_, 0, v___x_3947_);
v___x_3949_ = v_reuseFailAlloc_3950_;
goto v_reusejp_3948_;
}
v_reusejp_3948_:
{
return v___x_3949_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3935_ = stack[0].m_obj;
lean_object* v___y_3936_ = stack[1].m_obj;
lean_object* v___y_3937_ = stack[2].m_obj;
lean_object* v___y_3938_ = stack[3].m_obj;
lean_object* v___y_3939_ = stack[4].m_obj;
lean_object* v_res_3952_;
v_res_3952_ = l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0___redArg(v_msg_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_);
stack->m_obj
 = v_res_3952_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0___redArg___boxed(lean_object* v_msg_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_){
_start:
{
lean_object* v_res_3959_; 
v_res_3959_ = l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0___redArg(v_msg_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_);
lean_dec(v___y_3957_);
lean_dec_ref(v___y_3956_);
lean_dec(v___y_3955_);
lean_dec_ref(v___y_3954_);
return v_res_3959_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_liftLets___closed__0(void){
_start:
{
lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3960_ = lean_box(0);
v___x_3961_ = lean_unsigned_to_nat(16u);
v___x_3962_ = lean_mk_array(v___x_3961_, v___x_3960_);
return v___x_3962_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_liftLets___closed__1(void){
_start:
{
lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; 
v___x_3963_ = lean_obj_once(&l_Lean_Meta_Sym_liftLets___closed__0, &l_Lean_Meta_Sym_liftLets___closed__0_once, _init_l_Lean_Meta_Sym_liftLets___closed__0);
v___x_3964_ = lean_unsigned_to_nat(0u);
v___x_3965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3965_, 0, v___x_3964_);
lean_ctor_set(v___x_3965_, 1, v___x_3963_);
return v___x_3965_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_liftLets___closed__3(void){
_start:
{
lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; 
v___x_3968_ = ((lean_object*)(l_Lean_Meta_Sym_liftLets___closed__2));
v___x_3969_ = lean_obj_once(&l_Lean_Meta_Sym_liftLets___closed__1, &l_Lean_Meta_Sym_liftLets___closed__1_once, _init_l_Lean_Meta_Sym_liftLets___closed__1);
v___x_3970_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3970_, 0, v___x_3969_);
lean_ctor_set(v___x_3970_, 1, v___x_3969_);
lean_ctor_set(v___x_3970_, 2, v___x_3969_);
lean_ctor_set(v___x_3970_, 3, v___x_3968_);
lean_ctor_set(v___x_3970_, 4, v___x_3969_);
return v___x_3970_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_liftLets___closed__5(void){
_start:
{
lean_object* v___x_3972_; lean_object* v___x_3973_; 
v___x_3972_ = ((lean_object*)(l_Lean_Meta_Sym_liftLets___closed__4));
v___x_3973_ = l_Lean_stringToMessageData(v___x_3972_);
return v___x_3973_;
}
}
lean_object* l_Lean_Meta_Sym_liftLets(lean_object* v_e_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_){
_start:
{
lean_object* v___y_3983_; lean_object* v___y_3984_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; uint8_t v___x_4007_; 
v___x_4007_ = l_Lean_Expr_hasLooseBVars(v_e_3974_);
if (v___x_4007_ == 0)
{
v___y_3995_ = v_a_3975_;
v___y_3996_ = v_a_3976_;
v___y_3997_ = v_a_3977_;
v___y_3998_ = v_a_3978_;
v___y_3999_ = v_a_3979_;
v___y_4000_ = v_a_3980_;
goto v___jp_3994_;
}
else
{
lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v_a_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4017_; 
lean_dec_ref(v_e_3974_);
v___x_4008_ = lean_obj_once(&l_Lean_Meta_Sym_liftLets___closed__5, &l_Lean_Meta_Sym_liftLets___closed__5_once, _init_l_Lean_Meta_Sym_liftLets___closed__5);
v___x_4009_ = l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0___redArg(v___x_4008_, v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_);
v_a_4010_ = lean_ctor_get(v___x_4009_, 0);
v_isSharedCheck_4017_ = !lean_is_exclusive(v___x_4009_);
if (v_isSharedCheck_4017_ == 0)
{
v___x_4012_ = v___x_4009_;
v_isShared_4013_ = v_isSharedCheck_4017_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_a_4010_);
lean_dec(v___x_4009_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4017_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
lean_object* v___x_4015_; 
if (v_isShared_4013_ == 0)
{
v___x_4015_ = v___x_4012_;
goto v_reusejp_4014_;
}
else
{
lean_object* v_reuseFailAlloc_4016_; 
v_reuseFailAlloc_4016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4016_, 0, v_a_4010_);
v___x_4015_ = v_reuseFailAlloc_4016_;
goto v_reusejp_4014_;
}
v_reusejp_4014_:
{
return v___x_4015_;
}
}
}
v___jp_3982_:
{
if (lean_obj_tag(v___y_3984_) == 0)
{
lean_object* v_a_3985_; lean_object* v___x_3987_; uint8_t v_isShared_3988_; uint8_t v_isSharedCheck_3993_; 
v_a_3985_ = lean_ctor_get(v___y_3984_, 0);
v_isSharedCheck_3993_ = !lean_is_exclusive(v___y_3984_);
if (v_isSharedCheck_3993_ == 0)
{
v___x_3987_ = v___y_3984_;
v_isShared_3988_ = v_isSharedCheck_3993_;
goto v_resetjp_3986_;
}
else
{
lean_inc(v_a_3985_);
lean_dec(v___y_3984_);
v___x_3987_ = lean_box(0);
v_isShared_3988_ = v_isSharedCheck_3993_;
goto v_resetjp_3986_;
}
v_resetjp_3986_:
{
lean_object* v___x_3989_; lean_object* v___x_3991_; 
v___x_3989_ = lean_st_ref_get(v___y_3983_);
lean_dec(v___y_3983_);
lean_dec(v___x_3989_);
if (v_isShared_3988_ == 0)
{
v___x_3991_ = v___x_3987_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v_a_3985_);
v___x_3991_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
return v___x_3991_;
}
}
}
else
{
lean_dec(v___y_3983_);
return v___y_3984_;
}
}
v___jp_3994_:
{
lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; 
v___x_4001_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__3, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__3_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__3);
v___x_4002_ = lean_obj_once(&l_Lean_Meta_Sym_liftLets___closed__3, &l_Lean_Meta_Sym_liftLets___closed__3_once, _init_l_Lean_Meta_Sym_liftLets___closed__3);
v___x_4003_ = lean_st_mk_ref(v___x_4002_);
v___x_4004_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v___x_4001_, v_e_3974_, v___x_4003_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_);
if (lean_obj_tag(v___x_4004_) == 0)
{
lean_object* v_a_4005_; lean_object* v___x_4006_; 
v_a_4005_ = lean_ctor_get(v___x_4004_, 0);
lean_inc(v_a_4005_);
lean_dec_ref_known(v___x_4004_, 1);
v___x_4006_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets(v_a_4005_, v___x_4003_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_);
v___y_3983_ = v___x_4003_;
v___y_3984_ = v___x_4006_;
goto v___jp_3982_;
}
else
{
v___y_3983_ = v___x_4003_;
v___y_3984_ = v___x_4004_;
goto v___jp_3982_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_liftLets_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3974_ = stack[0].m_obj;
lean_object* v_a_3975_ = stack[1].m_obj;
lean_object* v_a_3976_ = stack[2].m_obj;
lean_object* v_a_3977_ = stack[3].m_obj;
lean_object* v_a_3978_ = stack[4].m_obj;
lean_object* v_a_3979_ = stack[5].m_obj;
lean_object* v_a_3980_ = stack[6].m_obj;
lean_object* v_res_4018_;
v_res_4018_ = l_Lean_Meta_Sym_liftLets(v_e_3974_, v_a_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_);
stack->m_obj
 = v_res_4018_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLets___boxed(lean_object* v_e_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_){
_start:
{
lean_object* v_res_4027_; 
v_res_4027_ = l_Lean_Meta_Sym_liftLets(v_e_4019_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_);
lean_dec(v_a_4025_);
lean_dec_ref(v_a_4024_);
lean_dec(v_a_4023_);
lean_dec_ref(v_a_4022_);
lean_dec(v_a_4021_);
lean_dec_ref(v_a_4020_);
return v_res_4027_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0(lean_object* v_00_u03b1_4028_, lean_object* v_msg_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_){
_start:
{
lean_object* v___x_4037_; 
v___x_4037_ = l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0___redArg(v_msg_4029_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
return v___x_4037_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_4029_ = stack[1].m_obj;
lean_object* v___y_4030_ = stack[2].m_obj;
lean_object* v___y_4031_ = stack[3].m_obj;
lean_object* v___y_4032_ = stack[4].m_obj;
lean_object* v___y_4033_ = stack[5].m_obj;
lean_object* v___y_4034_ = stack[6].m_obj;
lean_object* v___y_4035_ = stack[7].m_obj;
lean_object* v_res_4038_;
v_res_4038_ = l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0(lean_box(0), v_msg_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
stack->m_obj
 = v_res_4038_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0___boxed(lean_object* v_00_u03b1_4039_, lean_object* v_msg_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_){
_start:
{
lean_object* v_res_4048_; 
v_res_4048_ = l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0(v_00_u03b1_4039_, v_msg_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_);
lean_dec(v___y_4046_);
lean_dec_ref(v___y_4045_);
lean_dec(v___y_4044_);
lean_dec_ref(v___y_4043_);
lean_dec(v___y_4042_);
lean_dec_ref(v___y_4041_);
return v_res_4048_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_ReplaceS(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_LiftLet(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_ReplaceS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Sym_LiftLet_instInhabitedDecl_default = _init_l_Lean_Meta_Sym_LiftLet_instInhabitedDecl_default();
lean_mark_persistent(l_Lean_Meta_Sym_LiftLet_instInhabitedDecl_default);
l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_instInhabitedDecl = _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_instInhabitedDecl();
lean_mark_persistent(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_instInhabitedDecl);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_LiftLet(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_ReplaceS(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_LiftLet(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_ReplaceS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_LiftLet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_LiftLet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_LiftLet(builtin);
}
#ifdef __cplusplus
}
#endif
