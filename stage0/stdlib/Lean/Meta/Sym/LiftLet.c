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
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed(lean_object*);
lean_object* l_instMonadEIO(lean_object*);
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
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_Expr_looseBVarRange(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_EStateM_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Sym_instInhabitedSymM(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instInhabited___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__2_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__4_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__4_spec__7_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__4_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__4___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__4_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__4_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__4_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___lam__0, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___lam__1, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___lam__2, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10_spec__11_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10_spec__11_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10___redArg___boxed(lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10_spec__11_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__8_spec__11_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__8_spec__11_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__8_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__8___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__8___redArg___boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Meta.Sym.LiftLet"};
static const lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "_private.Lean.Meta.Sym.LiftLet.0.Lean.Meta.Sym.LiftLet.go.visit"};
static const lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2;
static const lean_string_object l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`Sym.liftLets` internal error, input term is not closed"};
static const lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__8_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__8_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__8_spec__11_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4___closed__1_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "_private.Lean.Meta.Sym.LiftLet.0.Lean.Meta.Sym.LiftLet.mkLets"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6_spec__9___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6_spec__9___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "assertion violation: p < i\n          "};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6_spec__9___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6_spec__9___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6_spec__9___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6_spec__9___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__8___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__8___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__8___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__8___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__8_spec__12(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__8(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint64_t l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hashPtrEnv_unsafe__1(lean_object* v_xs_13_){
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hashPtrEnv_unsafe__1___boxed(lean_object* v_xs_18_){
_start:
{
uint64_t v_res_19_; lean_object* v_r_20_; 
v_res_19_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hashPtrEnv_unsafe__1(v_xs_18_);
lean_dec_ref(v_xs_18_);
v_r_20_ = lean_box_uint64(v_res_19_);
return v_r_20_;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hashPtrEnv(lean_object* v_xs_21_){
_start:
{
size_t v___x_22_; size_t v___x_23_; size_t v___x_24_; uint64_t v___x_25_; 
v___x_22_ = lean_ptr_addr(v_xs_21_);
v___x_23_ = ((size_t)3ULL);
v___x_24_ = lean_usize_shift_right(v___x_22_, v___x_23_);
v___x_25_ = lean_usize_to_uint64(v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hashPtrEnv___boxed(lean_object* v_xs_26_){
_start:
{
uint64_t v_res_27_; lean_object* v_r_28_; 
v_res_27_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hashPtrEnv(v_xs_26_);
lean_dec_ref(v_xs_26_);
v_r_28_ = lean_box_uint64(v_res_27_);
return v_r_28_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_isSameEnv_unsafe__1(lean_object* v_xs_29_, lean_object* v_ys_30_){
_start:
{
size_t v___x_31_; size_t v___x_32_; uint8_t v___x_33_; 
v___x_31_ = lean_ptr_addr(v_xs_29_);
v___x_32_ = lean_ptr_addr(v_ys_30_);
v___x_33_ = lean_usize_dec_eq(v___x_31_, v___x_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_isSameEnv_unsafe__1___boxed(lean_object* v_xs_34_, lean_object* v_ys_35_){
_start:
{
uint8_t v_res_36_; lean_object* v_r_37_; 
v_res_36_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_isSameEnv_unsafe__1(v_xs_34_, v_ys_35_);
lean_dec_ref(v_ys_35_);
lean_dec_ref(v_xs_34_);
v_r_37_ = lean_box(v_res_36_);
return v_r_37_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_isSameEnv(lean_object* v_xs_38_, lean_object* v_ys_39_){
_start:
{
size_t v___x_40_; size_t v___x_41_; uint8_t v___x_42_; 
v___x_40_ = lean_ptr_addr(v_xs_38_);
v___x_41_ = lean_ptr_addr(v_ys_39_);
v___x_42_ = lean_usize_dec_eq(v___x_40_, v___x_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_isSameEnv___boxed(lean_object* v_xs_43_, lean_object* v_ys_44_){
_start:
{
uint8_t v_res_45_; lean_object* v_r_46_; 
v_res_45_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_isSameEnv(v_xs_43_, v_ys_44_);
lean_dec_ref(v_ys_44_);
lean_dec_ref(v_xs_43_);
v_r_46_ = lean_box(v_res_45_);
return v_r_46_;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_instHashableEnvPtr___lam__0(lean_object* v_k_47_){
_start:
{
size_t v___x_48_; size_t v___x_49_; size_t v___x_50_; uint64_t v___x_51_; 
v___x_48_ = lean_ptr_addr(v_k_47_);
v___x_49_ = ((size_t)3ULL);
v___x_50_ = lean_usize_shift_right(v___x_48_, v___x_49_);
v___x_51_ = lean_usize_to_uint64(v___x_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_instHashableEnvPtr___lam__0___boxed(lean_object* v_k_52_){
_start:
{
uint64_t v_res_53_; lean_object* v_r_54_; 
v_res_53_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_instHashableEnvPtr___lam__0(v_k_52_);
lean_dec_ref(v_k_52_);
v_r_54_ = lean_box_uint64(v_res_53_);
return v_r_54_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_instBEqEnvPtr___lam__0(lean_object* v_k_u2081_57_, lean_object* v_k_u2082_58_){
_start:
{
size_t v___x_59_; size_t v___x_60_; uint8_t v___x_61_; 
v___x_59_ = lean_ptr_addr(v_k_u2081_57_);
v___x_60_ = lean_ptr_addr(v_k_u2082_58_);
v___x_61_ = lean_usize_dec_eq(v___x_59_, v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_instBEqEnvPtr___lam__0___boxed(lean_object* v_k_u2081_62_, lean_object* v_k_u2082_63_){
_start:
{
uint8_t v_res_64_; lean_object* v_r_65_; 
v_res_64_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_instBEqEnvPtr___lam__0(v_k_u2081_62_, v_k_u2082_63_);
lean_dec_ref(v_k_u2082_63_);
lean_dec_ref(v_k_u2081_62_);
v_r_65_ = lean_box(v_res_64_);
return v_r_65_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2___redArg(lean_object* v_m_68_, lean_object* v_query_69_, lean_object* v_x_70_, lean_object* v_x_71_, lean_object* v_x_72_){
_start:
{
lean_object* v_zero_73_; uint8_t v_isZero_74_; 
v_zero_73_ = lean_unsigned_to_nat(0u);
v_isZero_74_ = lean_nat_dec_eq(v_x_71_, v_zero_73_);
if (v_isZero_74_ == 1)
{
lean_dec(v_x_72_);
lean_dec(v_x_71_);
if (lean_obj_tag(v_x_70_) == 0)
{
lean_object* v___x_75_; 
v___x_75_ = lean_box(2);
return v___x_75_;
}
else
{
lean_object* v_val_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_83_; 
v_val_76_ = lean_ctor_get(v_x_70_, 0);
v_isSharedCheck_83_ = !lean_is_exclusive(v_x_70_);
if (v_isSharedCheck_83_ == 0)
{
v___x_78_ = v_x_70_;
v_isShared_79_ = v_isSharedCheck_83_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_val_76_);
lean_dec(v_x_70_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_83_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_81_; 
if (v_isShared_79_ == 0)
{
v___x_81_ = v___x_78_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v_val_76_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
return v___x_81_;
}
}
}
}
else
{
lean_object* v_keyArray_84_; lean_object* v_valueArray_85_; lean_object* v___x_86_; uint8_t v_isSome_87_; 
v_keyArray_84_ = lean_ctor_get(v_m_68_, 1);
v_valueArray_85_ = lean_ctor_get(v_m_68_, 2);
v___x_86_ = lean_array_fget_borrowed(v_keyArray_84_, v_x_72_);
v_isSome_87_ = lean_noption_is_some(v___x_86_);
if (v_isSome_87_ == 0)
{
lean_dec(v_x_71_);
if (lean_obj_tag(v_x_70_) == 0)
{
lean_object* v___x_88_; 
v___x_88_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_88_, 0, v_x_72_);
return v___x_88_;
}
else
{
lean_object* v_val_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_96_; 
lean_dec(v_x_72_);
v_val_89_ = lean_ctor_get(v_x_70_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v_x_70_);
if (v_isSharedCheck_96_ == 0)
{
v___x_91_ = v_x_70_;
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_val_89_);
lean_dec(v_x_70_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_94_; 
if (v_isShared_92_ == 0)
{
v___x_94_ = v___x_91_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_val_89_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
}
else
{
lean_object* v_one_97_; lean_object* v_n_98_; lean_object* v___y_100_; 
v_one_97_ = lean_unsigned_to_nat(1u);
v_n_98_ = lean_nat_sub(v_x_71_, v_one_97_);
lean_dec(v_x_71_);
if (v_isSome_87_ == 0)
{
goto v___jp_106_;
}
else
{
lean_object* v___x_108_; uint8_t v_isSome_109_; 
v___x_108_ = lean_array_fget_borrowed(v_valueArray_85_, v_x_72_);
v_isSome_109_ = lean_noption_is_some(v___x_108_);
if (v_isSome_109_ == 0)
{
goto v___jp_106_;
}
else
{
lean_object* v_val_110_; size_t v___x_111_; size_t v___x_112_; uint8_t v___x_113_; 
lean_inc(v___x_86_);
v_val_110_ = lean_noption_get(v___x_86_);
v___x_111_ = lean_ptr_addr(v_val_110_);
v___x_112_ = lean_ptr_addr(v_query_69_);
v___x_113_ = lean_usize_dec_eq(v___x_111_, v___x_112_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; lean_object* v___x_115_; uint8_t v___x_116_; 
lean_dec(v_val_110_);
v___x_114_ = lean_array_get_size(v_keyArray_84_);
v___x_115_ = lean_nat_add(v_x_72_, v_one_97_);
lean_dec(v_x_72_);
v___x_116_ = lean_nat_dec_lt(v___x_115_, v___x_114_);
if (v___x_116_ == 0)
{
lean_dec(v___x_115_);
v_x_71_ = v_n_98_;
v_x_72_ = v_zero_73_;
goto _start;
}
else
{
v_x_71_ = v_n_98_;
v_x_72_ = v___x_115_;
goto _start;
}
}
else
{
lean_object* v_val_119_; lean_object* v___x_120_; 
lean_dec(v_n_98_);
lean_dec(v_x_70_);
lean_inc(v___x_108_);
v_val_119_ = lean_noption_get(v___x_108_);
v___x_120_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_120_, 0, v_x_72_);
lean_ctor_set(v___x_120_, 1, v_val_110_);
lean_ctor_set(v___x_120_, 2, v_val_119_);
return v___x_120_;
}
}
}
v___jp_99_:
{
lean_object* v___x_101_; lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_101_ = lean_array_get_size(v_keyArray_84_);
v___x_102_ = lean_nat_add(v_x_72_, v_one_97_);
lean_dec(v_x_72_);
v___x_103_ = lean_nat_dec_lt(v___x_102_, v___x_101_);
if (v___x_103_ == 0)
{
lean_dec(v___x_102_);
v_x_70_ = v___y_100_;
v_x_71_ = v_n_98_;
v_x_72_ = v_zero_73_;
goto _start;
}
else
{
v_x_70_ = v___y_100_;
v_x_71_ = v_n_98_;
v_x_72_ = v___x_102_;
goto _start;
}
}
v___jp_106_:
{
if (lean_obj_tag(v_x_70_) == 0)
{
lean_object* v___x_107_; 
lean_inc(v_x_72_);
v___x_107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_107_, 0, v_x_72_);
v___y_100_ = v___x_107_;
goto v___jp_99_;
}
else
{
v___y_100_ = v_x_70_;
goto v___jp_99_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2___redArg___boxed(lean_object* v_m_121_, lean_object* v_query_122_, lean_object* v_x_123_, lean_object* v_x_124_, lean_object* v_x_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2___redArg(v_m_121_, v_query_122_, v_x_123_, v_x_124_, v_x_125_);
lean_dec_ref(v_query_122_);
lean_dec_ref(v_m_121_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1___redArg(lean_object* v_m_127_, lean_object* v_query_128_){
_start:
{
lean_object* v_keyArray_129_; lean_object* v___x_130_; size_t v___x_131_; size_t v___x_132_; size_t v___x_133_; uint64_t v___x_134_; uint64_t v___x_135_; uint64_t v___x_136_; uint64_t v_fold_137_; uint64_t v___x_138_; uint64_t v___x_139_; uint64_t v___x_140_; size_t v___x_141_; size_t v___x_142_; size_t v___x_143_; size_t v___x_144_; size_t v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v_keyArray_129_ = lean_ctor_get(v_m_127_, 1);
v___x_130_ = lean_array_get_size(v_keyArray_129_);
v___x_131_ = lean_ptr_addr(v_query_128_);
v___x_132_ = ((size_t)3ULL);
v___x_133_ = lean_usize_shift_right(v___x_131_, v___x_132_);
v___x_134_ = lean_usize_to_uint64(v___x_133_);
v___x_135_ = 32ULL;
v___x_136_ = lean_uint64_shift_right(v___x_134_, v___x_135_);
v_fold_137_ = lean_uint64_xor(v___x_134_, v___x_136_);
v___x_138_ = 16ULL;
v___x_139_ = lean_uint64_shift_right(v_fold_137_, v___x_138_);
v___x_140_ = lean_uint64_xor(v_fold_137_, v___x_139_);
v___x_141_ = lean_uint64_to_usize(v___x_140_);
v___x_142_ = lean_usize_of_nat(v___x_130_);
v___x_143_ = ((size_t)1ULL);
v___x_144_ = lean_usize_sub(v___x_142_, v___x_143_);
v___x_145_ = lean_usize_land(v___x_141_, v___x_144_);
v___x_146_ = lean_usize_to_nat(v___x_145_);
v___x_147_ = lean_box(0);
v___x_148_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2___redArg(v_m_127_, v_query_128_, v___x_147_, v___x_130_, v___x_146_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1___redArg___boxed(lean_object* v_m_149_, lean_object* v_query_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1___redArg(v_m_149_, v_query_150_);
lean_dec_ref(v_query_150_);
lean_dec_ref(v_m_149_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__2_spec__4_spec__5___redArg(lean_object* v_b_152_, lean_object* v_acc_153_, lean_object* v_i_154_){
_start:
{
lean_object* v___y_156_; lean_object* v_keyArray_164_; lean_object* v_valueArray_165_; lean_object* v___x_166_; uint8_t v___x_167_; 
v_keyArray_164_ = lean_ctor_get(v_b_152_, 1);
v_valueArray_165_ = lean_ctor_get(v_b_152_, 2);
v___x_166_ = lean_array_get_size(v_keyArray_164_);
v___x_167_ = lean_nat_dec_lt(v_i_154_, v___x_166_);
if (v___x_167_ == 0)
{
lean_dec(v_i_154_);
return v_acc_153_;
}
else
{
lean_object* v___x_168_; uint8_t v_isSome_169_; 
v___x_168_ = lean_array_fget_borrowed(v_keyArray_164_, v_i_154_);
v_isSome_169_ = lean_noption_is_some(v___x_168_);
if (v_isSome_169_ == 0)
{
goto v___jp_160_;
}
else
{
lean_object* v___x_170_; uint8_t v_isSome_171_; 
v___x_170_ = lean_array_fget_borrowed(v_valueArray_165_, v_i_154_);
v_isSome_171_ = lean_noption_is_some(v___x_170_);
if (v_isSome_171_ == 0)
{
goto v___jp_160_;
}
else
{
lean_object* v_val_172_; lean_object* v_val_173_; lean_object* v_i_175_; lean_object* v___x_180_; 
lean_inc(v___x_168_);
v_val_172_ = lean_noption_get(v___x_168_);
lean_inc(v___x_170_);
v_val_173_ = lean_noption_get(v___x_170_);
v___x_180_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1___redArg(v_acc_153_, v_val_172_);
switch(lean_obj_tag(v___x_180_))
{
case 0:
{
lean_object* v_index_181_; lean_object* v_size_182_; lean_object* v___x_183_; 
v_index_181_ = lean_ctor_get(v___x_180_, 0);
lean_inc(v_index_181_);
lean_dec_ref_known(v___x_180_, 3);
v_size_182_ = lean_ctor_get(v_acc_153_, 0);
lean_inc(v_size_182_);
v___x_183_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_153_, v_size_182_, v_index_181_, v_val_172_, v_val_173_);
lean_dec(v_index_181_);
v___y_156_ = v___x_183_;
goto v___jp_155_;
}
case 1:
{
lean_object* v_index_184_; 
v_index_184_ = lean_ctor_get(v___x_180_, 0);
lean_inc(v_index_184_);
lean_dec_ref_known(v___x_180_, 1);
v_i_175_ = v_index_184_;
goto v___jp_174_;
}
default: 
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = lean_unsigned_to_nat(0u);
v___x_186_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_153_, v___x_185_);
if (lean_obj_tag(v___x_186_) == 0)
{
lean_object* v_index_187_; 
v_index_187_ = lean_ctor_get(v___x_186_, 0);
lean_inc(v_index_187_);
lean_dec_ref_known(v___x_186_, 1);
v_i_175_ = v_index_187_;
goto v___jp_174_;
}
else
{
lean_dec(v_val_173_);
lean_dec(v_val_172_);
v___y_156_ = v_acc_153_;
goto v___jp_155_;
}
}
}
v___jp_174_:
{
lean_object* v_size_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v_size_176_ = lean_ctor_get(v_acc_153_, 0);
v___x_177_ = lean_unsigned_to_nat(1u);
v___x_178_ = lean_nat_add(v_size_176_, v___x_177_);
v___x_179_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_153_, v___x_178_, v_i_175_, v_val_172_, v_val_173_);
lean_dec(v_i_175_);
v___y_156_ = v___x_179_;
goto v___jp_155_;
}
}
}
}
v___jp_155_:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = lean_unsigned_to_nat(1u);
v___x_158_ = lean_nat_add(v_i_154_, v___x_157_);
lean_dec(v_i_154_);
v_acc_153_ = v___y_156_;
v_i_154_ = v___x_158_;
goto _start;
}
v___jp_160_:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = lean_unsigned_to_nat(1u);
v___x_162_ = lean_nat_add(v_i_154_, v___x_161_);
lean_dec(v_i_154_);
v_i_154_ = v___x_162_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_b_188_, lean_object* v_acc_189_, lean_object* v_i_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__2_spec__4_spec__5___redArg(v_b_188_, v_acc_189_, v_i_190_);
lean_dec_ref(v_b_188_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__2_spec__4___redArg(lean_object* v_init_192_, lean_object* v_b_193_){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = lean_unsigned_to_nat(0u);
v___x_195_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__2_spec__4_spec__5___redArg(v_b_193_, v_init_192_, v___x_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__2_spec__4___redArg___boxed(lean_object* v_init_196_, lean_object* v_b_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__2_spec__4___redArg(v_init_196_, v_b_197_);
lean_dec_ref(v_b_197_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__2___redArg(lean_object* v_m_199_){
_start:
{
lean_object* v_keyArray_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v_cellCount_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v_target_207_; lean_object* v___x_208_; 
v_keyArray_200_ = lean_ctor_get(v_m_199_, 1);
v___x_201_ = lean_array_get_size(v_keyArray_200_);
v___x_202_ = lean_unsigned_to_nat(2u);
v_cellCount_203_ = lean_nat_mul(v___x_201_, v___x_202_);
v___x_204_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_203_);
v___x_205_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_203_);
v___x_206_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_203_);
v_target_207_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_207_, 0, v___x_204_);
lean_ctor_set(v_target_207_, 1, v___x_205_);
lean_ctor_set(v_target_207_, 2, v___x_206_);
v___x_208_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__2_spec__4___redArg(v_target_207_, v_m_199_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__2___redArg___boxed(lean_object* v_m_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__2___redArg(v_m_209_);
lean_dec_ref(v_m_209_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0_spec__0___redArg(lean_object* v_m_211_, lean_object* v_query_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1___redArg(v_m_211_, v_query_212_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v_index_214_; lean_object* v_key_215_; lean_object* v_value_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_223_; 
v_index_214_ = lean_ctor_get(v___x_213_, 0);
v_key_215_ = lean_ctor_get(v___x_213_, 1);
v_value_216_ = lean_ctor_get(v___x_213_, 2);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_223_ == 0)
{
v___x_218_ = v___x_213_;
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_value_216_);
lean_inc(v_key_215_);
lean_inc(v_index_214_);
lean_dec(v___x_213_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_221_; 
if (v_isShared_219_ == 0)
{
v___x_221_ = v___x_218_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_index_214_);
lean_ctor_set(v_reuseFailAlloc_222_, 1, v_key_215_);
lean_ctor_set(v_reuseFailAlloc_222_, 2, v_value_216_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
else
{
lean_object* v___x_224_; 
lean_dec(v___x_213_);
v___x_224_ = lean_box(1);
return v___x_224_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0_spec__0___redArg___boxed(lean_object* v_m_225_, lean_object* v_query_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0_spec__0___redArg(v_m_225_, v_query_226_);
lean_dec_ref(v_query_226_);
lean_dec_ref(v_m_225_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0___redArg(lean_object* v_m_228_, lean_object* v_a_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0_spec__0___redArg(v_m_228_, v_a_229_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_value_231_; lean_object* v___x_232_; 
v_value_231_ = lean_ctor_get(v___x_230_, 2);
lean_inc(v_value_231_);
lean_dec_ref_known(v___x_230_, 3);
v___x_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_232_, 0, v_value_231_);
return v___x_232_;
}
else
{
lean_object* v___x_233_; 
v___x_233_ = lean_box(0);
return v___x_233_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0___redArg___boxed(lean_object* v_m_234_, lean_object* v_a_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0___redArg(v_m_234_, v_a_235_);
lean_dec_ref(v_a_235_);
lean_dec_ref(v_m_234_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet___lam__0___boxed(lean_object* v_fn_237_, lean_object* v_arg_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet___lam__0(v_fn_237_, v_arg_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v___y_239_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet___boxed(lean_object* v_e_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet(v_e_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_);
lean_dec(v_a_255_);
lean_dec_ref(v_a_254_);
lean_dec(v_a_253_);
lean_dec_ref(v_a_252_);
lean_dec(v_a_251_);
lean_dec_ref(v_a_250_);
lean_dec(v_a_249_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet(lean_object* v_e_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
lean_object* v___y_268_; lean_object* v___y_269_; lean_object* v___y_270_; lean_object* v___y_271_; uint8_t v___y_272_; lean_object* v___y_273_; lean_object* v___y_274_; lean_object* v___y_280_; lean_object* v___y_281_; lean_object* v___y_282_; lean_object* v___y_283_; uint8_t v___y_284_; lean_object* v___y_285_; lean_object* v___y_286_; lean_object* v___y_287_; lean_object* v_i_288_; lean_object* v___y_295_; lean_object* v___y_296_; lean_object* v___y_297_; lean_object* v___y_298_; uint8_t v___y_299_; lean_object* v___y_300_; lean_object* v___y_301_; lean_object* v___y_302_; lean_object* v___y_314_; lean_object* v___y_315_; lean_object* v___y_316_; lean_object* v___y_317_; lean_object* v___y_318_; uint8_t v___y_319_; lean_object* v___y_320_; lean_object* v___y_321_; lean_object* v_i_322_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v___y_331_; lean_object* v___y_332_; uint8_t v___y_333_; lean_object* v___y_334_; lean_object* v___y_335_; lean_object* v___y_336_; lean_object* v_e_347_; lean_object* v_k_348_; lean_object* v___y_349_; lean_object* v___y_350_; lean_object* v___y_351_; lean_object* v___y_352_; lean_object* v___y_353_; lean_object* v___y_354_; lean_object* v___y_355_; 
switch(lean_obj_tag(v_e_258_))
{
case 8:
{
uint8_t v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
lean_dec_ref_known(v_e_258_, 4);
v___x_412_ = 1;
v___x_413_ = lean_box(v___x_412_);
v___x_414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
return v___x_414_;
}
case 5:
{
lean_object* v_fn_415_; lean_object* v_arg_416_; lean_object* v___f_417_; 
v_fn_415_ = lean_ctor_get(v_e_258_, 0);
v_arg_416_ = lean_ctor_get(v_e_258_, 1);
lean_inc_ref(v_arg_416_);
lean_inc_ref(v_fn_415_);
v___f_417_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet___lam__0___boxed), 10, 2);
lean_closure_set(v___f_417_, 0, v_fn_415_);
lean_closure_set(v___f_417_, 1, v_arg_416_);
v_e_347_ = v_e_258_;
v_k_348_ = v___f_417_;
v___y_349_ = v_a_259_;
v___y_350_ = v_a_260_;
v___y_351_ = v_a_261_;
v___y_352_ = v_a_262_;
v___y_353_ = v_a_263_;
v___y_354_ = v_a_264_;
v___y_355_ = v_a_265_;
goto v___jp_346_;
}
case 10:
{
lean_object* v_expr_418_; lean_object* v___x_419_; 
v_expr_418_ = lean_ctor_get(v_e_258_, 1);
lean_inc_ref(v_expr_418_);
v___x_419_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet___boxed), 9, 1);
lean_closure_set(v___x_419_, 0, v_expr_418_);
v_e_347_ = v_e_258_;
v_k_348_ = v___x_419_;
v___y_349_ = v_a_259_;
v___y_350_ = v_a_260_;
v___y_351_ = v_a_261_;
v___y_352_ = v_a_262_;
v___y_353_ = v_a_263_;
v___y_354_ = v_a_264_;
v___y_355_ = v_a_265_;
goto v___jp_346_;
}
case 11:
{
lean_object* v_struct_420_; lean_object* v___x_421_; 
v_struct_420_ = lean_ctor_get(v_e_258_, 2);
lean_inc_ref(v_struct_420_);
v___x_421_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet___boxed), 9, 1);
lean_closure_set(v___x_421_, 0, v_struct_420_);
v_e_347_ = v_e_258_;
v_k_348_ = v___x_421_;
v___y_349_ = v_a_259_;
v___y_350_ = v_a_260_;
v___y_351_ = v_a_261_;
v___y_352_ = v_a_262_;
v___y_353_ = v_a_263_;
v___y_354_ = v_a_264_;
v___y_355_ = v_a_265_;
goto v___jp_346_;
}
default: 
{
uint8_t v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
lean_dec_ref(v_e_258_);
v___x_422_ = 0;
v___x_423_ = lean_box(v___x_422_);
v___x_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
return v___x_424_;
}
}
v___jp_267_:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_275_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_275_, 0, v___y_268_);
lean_ctor_set(v___x_275_, 1, v___y_269_);
lean_ctor_set(v___x_275_, 2, v___y_274_);
lean_ctor_set(v___x_275_, 3, v___y_270_);
lean_ctor_set(v___x_275_, 4, v___y_273_);
v___x_276_ = lean_st_ref_put(v___y_271_, v___x_275_);
v___x_277_ = lean_box(v___y_272_);
v___x_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
return v___x_278_;
}
v___jp_279_:
{
lean_object* v_size_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v_size_289_ = lean_ctor_get(v___y_286_, 0);
v___x_290_ = lean_unsigned_to_nat(1u);
v___x_291_ = lean_nat_add(v_size_289_, v___x_290_);
v___x_292_ = lean_box(v___y_284_);
v___x_293_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_286_, v___x_291_, v_i_288_, v___y_283_, v___x_292_);
lean_dec(v_i_288_);
v___y_268_ = v___y_280_;
v___y_269_ = v___y_281_;
v___y_270_ = v___y_282_;
v___y_271_ = v___y_285_;
v___y_272_ = v___y_284_;
v___y_273_ = v___y_287_;
v___y_274_ = v___x_293_;
goto v___jp_267_;
}
v___jp_294_:
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__2___redArg(v___y_302_);
lean_dec_ref(v___y_302_);
v___x_304_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1___redArg(v___x_303_, v___y_298_);
switch(lean_obj_tag(v___x_304_))
{
case 0:
{
lean_object* v_index_305_; lean_object* v_size_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v_index_305_ = lean_ctor_get(v___x_304_, 0);
lean_inc(v_index_305_);
lean_dec_ref_known(v___x_304_, 3);
v_size_306_ = lean_ctor_get(v___x_303_, 0);
lean_inc(v_size_306_);
v___x_307_ = lean_box(v___y_299_);
v___x_308_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_303_, v_size_306_, v_index_305_, v___y_298_, v___x_307_);
lean_dec(v_index_305_);
v___y_268_ = v___y_295_;
v___y_269_ = v___y_296_;
v___y_270_ = v___y_297_;
v___y_271_ = v___y_300_;
v___y_272_ = v___y_299_;
v___y_273_ = v___y_301_;
v___y_274_ = v___x_308_;
goto v___jp_267_;
}
case 1:
{
lean_object* v_index_309_; 
v_index_309_ = lean_ctor_get(v___x_304_, 0);
lean_inc(v_index_309_);
lean_dec_ref_known(v___x_304_, 1);
v___y_280_ = v___y_295_;
v___y_281_ = v___y_296_;
v___y_282_ = v___y_297_;
v___y_283_ = v___y_298_;
v___y_284_ = v___y_299_;
v___y_285_ = v___y_300_;
v___y_286_ = v___x_303_;
v___y_287_ = v___y_301_;
v_i_288_ = v_index_309_;
goto v___jp_279_;
}
default: 
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = lean_unsigned_to_nat(0u);
v___x_311_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_303_, v___x_310_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_index_312_; 
v_index_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_index_312_);
lean_dec_ref_known(v___x_311_, 1);
v___y_280_ = v___y_295_;
v___y_281_ = v___y_296_;
v___y_282_ = v___y_297_;
v___y_283_ = v___y_298_;
v___y_284_ = v___y_299_;
v___y_285_ = v___y_300_;
v___y_286_ = v___x_303_;
v___y_287_ = v___y_301_;
v_i_288_ = v_index_312_;
goto v___jp_279_;
}
else
{
lean_dec_ref(v___y_298_);
v___y_268_ = v___y_295_;
v___y_269_ = v___y_296_;
v___y_270_ = v___y_297_;
v___y_271_ = v___y_300_;
v___y_272_ = v___y_299_;
v___y_273_ = v___y_301_;
v___y_274_ = v___x_303_;
goto v___jp_267_;
}
}
}
}
v___jp_313_:
{
lean_object* v_size_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v_size_323_ = lean_ctor_get(v___y_315_, 0);
v___x_324_ = lean_unsigned_to_nat(1u);
v___x_325_ = lean_nat_add(v_size_323_, v___x_324_);
v___x_326_ = lean_box(v___y_319_);
v___x_327_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_315_, v___x_325_, v_i_322_, v___y_318_, v___x_326_);
lean_dec(v_i_322_);
v___y_268_ = v___y_314_;
v___y_269_ = v___y_316_;
v___y_270_ = v___y_317_;
v___y_271_ = v___y_320_;
v___y_272_ = v___y_319_;
v___y_273_ = v___y_321_;
v___y_274_ = v___x_327_;
goto v___jp_267_;
}
v___jp_328_:
{
lean_object* v___x_337_; 
v___x_337_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1___redArg(v___y_336_, v___y_332_);
switch(lean_obj_tag(v___x_337_))
{
case 0:
{
lean_object* v_index_338_; lean_object* v_size_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v_index_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc(v_index_338_);
lean_dec_ref_known(v___x_337_, 3);
v_size_339_ = lean_ctor_get(v___y_336_, 0);
lean_inc(v_size_339_);
v___x_340_ = lean_box(v___y_333_);
v___x_341_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_336_, v_size_339_, v_index_338_, v___y_332_, v___x_340_);
lean_dec(v_index_338_);
v___y_268_ = v___y_329_;
v___y_269_ = v___y_330_;
v___y_270_ = v___y_331_;
v___y_271_ = v___y_334_;
v___y_272_ = v___y_333_;
v___y_273_ = v___y_335_;
v___y_274_ = v___x_341_;
goto v___jp_267_;
}
case 1:
{
lean_object* v_index_342_; 
v_index_342_ = lean_ctor_get(v___x_337_, 0);
lean_inc(v_index_342_);
lean_dec_ref_known(v___x_337_, 1);
v___y_314_ = v___y_329_;
v___y_315_ = v___y_336_;
v___y_316_ = v___y_330_;
v___y_317_ = v___y_331_;
v___y_318_ = v___y_332_;
v___y_319_ = v___y_333_;
v___y_320_ = v___y_334_;
v___y_321_ = v___y_335_;
v_i_322_ = v_index_342_;
goto v___jp_313_;
}
default: 
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = lean_unsigned_to_nat(0u);
v___x_344_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_336_, v___x_343_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v_index_345_; 
v_index_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_index_345_);
lean_dec_ref_known(v___x_344_, 1);
v___y_314_ = v___y_329_;
v___y_315_ = v___y_336_;
v___y_316_ = v___y_330_;
v___y_317_ = v___y_331_;
v___y_318_ = v___y_332_;
v___y_319_ = v___y_333_;
v___y_320_ = v___y_334_;
v___y_321_ = v___y_335_;
v_i_322_ = v_index_345_;
goto v___jp_313_;
}
else
{
lean_dec_ref(v___y_332_);
v___y_268_ = v___y_329_;
v___y_269_ = v___y_330_;
v___y_270_ = v___y_331_;
v___y_271_ = v___y_334_;
v___y_272_ = v___y_333_;
v___y_273_ = v___y_335_;
v___y_274_ = v___y_336_;
goto v___jp_267_;
}
}
}
}
v___jp_346_:
{
lean_object* v___x_356_; lean_object* v_hasLetCache_357_; lean_object* v___x_358_; 
v___x_356_ = lean_st_ref_get(v___y_349_);
v_hasLetCache_357_ = lean_ctor_get(v___x_356_, 2);
lean_inc_ref(v_hasLetCache_357_);
lean_dec(v___x_356_);
v___x_358_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0___redArg(v_hasLetCache_357_, v_e_347_);
lean_dec_ref(v_hasLetCache_357_);
if (lean_obj_tag(v___x_358_) == 1)
{
lean_object* v_val_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
lean_dec_ref(v_k_348_);
lean_dec_ref(v_e_347_);
v_val_359_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_358_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_val_359_);
lean_dec(v___x_358_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
lean_ctor_set_tag(v___x_361_, 0);
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_val_359_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
else
{
lean_object* v___x_367_; 
lean_dec(v___x_358_);
lean_inc(v___y_355_);
lean_inc_ref(v___y_354_);
lean_inc(v___y_353_);
lean_inc_ref(v___y_352_);
lean_inc(v___y_351_);
lean_inc_ref(v___y_350_);
lean_inc(v___y_349_);
v___x_367_ = lean_apply_8(v_k_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, lean_box(0));
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v_a_368_; lean_object* v___x_369_; lean_object* v_cache_370_; lean_object* v_cacheClosed_371_; lean_object* v_hasLetCache_372_; lean_object* v_decls_373_; lean_object* v_valueMap_374_; lean_object* v___x_375_; 
v_a_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_a_368_);
lean_dec_ref_known(v___x_367_, 1);
v___x_369_ = lean_st_ref_take(v___y_349_);
v_cache_370_ = lean_ctor_get(v___x_369_, 0);
lean_inc_ref(v_cache_370_);
v_cacheClosed_371_ = lean_ctor_get(v___x_369_, 1);
lean_inc_ref(v_cacheClosed_371_);
v_hasLetCache_372_ = lean_ctor_get(v___x_369_, 2);
lean_inc_ref(v_hasLetCache_372_);
v_decls_373_ = lean_ctor_get(v___x_369_, 3);
lean_inc_ref(v_decls_373_);
v_valueMap_374_ = lean_ctor_get(v___x_369_, 4);
lean_inc_ref(v_valueMap_374_);
lean_dec(v___x_369_);
v___x_375_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1___redArg(v_hasLetCache_372_, v_e_347_);
switch(lean_obj_tag(v___x_375_))
{
case 0:
{
lean_object* v_index_376_; lean_object* v_size_377_; lean_object* v___x_378_; uint8_t v___x_379_; 
v_index_376_ = lean_ctor_get(v___x_375_, 0);
lean_inc(v_index_376_);
lean_dec_ref_known(v___x_375_, 3);
v_size_377_ = lean_ctor_get(v_hasLetCache_372_, 0);
lean_inc(v_size_377_);
lean_inc(v_a_368_);
v___x_378_ = l_Std_DHashMap_Raw_setEntry___redArg(v_hasLetCache_372_, v_size_377_, v_index_376_, v_e_347_, v_a_368_);
lean_dec(v_index_376_);
v___x_379_ = lean_unbox(v_a_368_);
lean_dec(v_a_368_);
v___y_268_ = v_cache_370_;
v___y_269_ = v_cacheClosed_371_;
v___y_270_ = v_decls_373_;
v___y_271_ = v___y_349_;
v___y_272_ = v___x_379_;
v___y_273_ = v_valueMap_374_;
v___y_274_ = v___x_378_;
goto v___jp_267_;
}
case 1:
{
lean_object* v_index_380_; lean_object* v_size_381_; lean_object* v_keyArray_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; uint8_t v___x_386_; 
v_index_380_ = lean_ctor_get(v___x_375_, 0);
lean_inc(v_index_380_);
lean_dec_ref_known(v___x_375_, 1);
v_size_381_ = lean_ctor_get(v_hasLetCache_372_, 0);
v_keyArray_382_ = lean_ctor_get(v_hasLetCache_372_, 1);
v___x_383_ = lean_unsigned_to_nat(1u);
v___x_384_ = lean_nat_add(v_size_381_, v___x_383_);
v___x_385_ = lean_array_get_size(v_keyArray_382_);
v___x_386_ = lean_nat_dec_lt(v___x_384_, v___x_385_);
if (v___x_386_ == 0)
{
uint8_t v___x_387_; 
lean_dec(v___x_384_);
lean_dec(v_index_380_);
v___x_387_ = lean_unbox(v_a_368_);
lean_dec(v_a_368_);
v___y_295_ = v_cache_370_;
v___y_296_ = v_cacheClosed_371_;
v___y_297_ = v_decls_373_;
v___y_298_ = v_e_347_;
v___y_299_ = v___x_387_;
v___y_300_ = v___y_349_;
v___y_301_ = v_valueMap_374_;
v___y_302_ = v_hasLetCache_372_;
goto v___jp_294_;
}
else
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; uint8_t v___x_392_; 
v___x_388_ = lean_unsigned_to_nat(4u);
v___x_389_ = lean_nat_mul(v___x_384_, v___x_388_);
v___x_390_ = lean_unsigned_to_nat(3u);
v___x_391_ = lean_nat_mul(v___x_385_, v___x_390_);
v___x_392_ = lean_nat_dec_le(v___x_389_, v___x_391_);
lean_dec(v___x_391_);
lean_dec(v___x_389_);
if (v___x_392_ == 0)
{
uint8_t v___x_393_; 
lean_dec(v___x_384_);
lean_dec(v_index_380_);
v___x_393_ = lean_unbox(v_a_368_);
lean_dec(v_a_368_);
v___y_295_ = v_cache_370_;
v___y_296_ = v_cacheClosed_371_;
v___y_297_ = v_decls_373_;
v___y_298_ = v_e_347_;
v___y_299_ = v___x_393_;
v___y_300_ = v___y_349_;
v___y_301_ = v_valueMap_374_;
v___y_302_ = v_hasLetCache_372_;
goto v___jp_294_;
}
else
{
lean_object* v___x_394_; uint8_t v___x_395_; 
lean_inc(v_a_368_);
v___x_394_ = l_Std_DHashMap_Raw_setEntry___redArg(v_hasLetCache_372_, v___x_384_, v_index_380_, v_e_347_, v_a_368_);
lean_dec(v_index_380_);
v___x_395_ = lean_unbox(v_a_368_);
lean_dec(v_a_368_);
v___y_268_ = v_cache_370_;
v___y_269_ = v_cacheClosed_371_;
v___y_270_ = v_decls_373_;
v___y_271_ = v___y_349_;
v___y_272_ = v___x_395_;
v___y_273_ = v_valueMap_374_;
v___y_274_ = v___x_394_;
goto v___jp_267_;
}
}
}
default: 
{
lean_object* v_size_396_; lean_object* v_keyArray_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; uint8_t v___x_401_; 
v_size_396_ = lean_ctor_get(v_hasLetCache_372_, 0);
v_keyArray_397_ = lean_ctor_get(v_hasLetCache_372_, 1);
v___x_398_ = lean_unsigned_to_nat(1u);
v___x_399_ = lean_nat_add(v_size_396_, v___x_398_);
v___x_400_ = lean_array_get_size(v_keyArray_397_);
v___x_401_ = lean_nat_dec_lt(v___x_399_, v___x_400_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; uint8_t v___x_403_; 
lean_dec(v___x_399_);
v___x_402_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__2___redArg(v_hasLetCache_372_);
lean_dec_ref(v_hasLetCache_372_);
v___x_403_ = lean_unbox(v_a_368_);
lean_dec(v_a_368_);
v___y_329_ = v_cache_370_;
v___y_330_ = v_cacheClosed_371_;
v___y_331_ = v_decls_373_;
v___y_332_ = v_e_347_;
v___y_333_ = v___x_403_;
v___y_334_ = v___y_349_;
v___y_335_ = v_valueMap_374_;
v___y_336_ = v___x_402_;
goto v___jp_328_;
}
else
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; uint8_t v___x_408_; 
v___x_404_ = lean_unsigned_to_nat(4u);
v___x_405_ = lean_nat_mul(v___x_399_, v___x_404_);
lean_dec(v___x_399_);
v___x_406_ = lean_unsigned_to_nat(3u);
v___x_407_ = lean_nat_mul(v___x_400_, v___x_406_);
v___x_408_ = lean_nat_dec_le(v___x_405_, v___x_407_);
lean_dec(v___x_407_);
lean_dec(v___x_405_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; uint8_t v___x_410_; 
v___x_409_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__2___redArg(v_hasLetCache_372_);
lean_dec_ref(v_hasLetCache_372_);
v___x_410_ = lean_unbox(v_a_368_);
lean_dec(v_a_368_);
v___y_329_ = v_cache_370_;
v___y_330_ = v_cacheClosed_371_;
v___y_331_ = v_decls_373_;
v___y_332_ = v_e_347_;
v___y_333_ = v___x_410_;
v___y_334_ = v___y_349_;
v___y_335_ = v_valueMap_374_;
v___y_336_ = v___x_409_;
goto v___jp_328_;
}
else
{
uint8_t v___x_411_; 
v___x_411_ = lean_unbox(v_a_368_);
lean_dec(v_a_368_);
v___y_329_ = v_cache_370_;
v___y_330_ = v_cacheClosed_371_;
v___y_331_ = v_decls_373_;
v___y_332_ = v_e_347_;
v___y_333_ = v___x_411_;
v___y_334_ = v___y_349_;
v___y_335_ = v_valueMap_374_;
v___y_336_ = v_hasLetCache_372_;
goto v___jp_328_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_347_);
return v___x_367_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet___lam__0(lean_object* v_fn_425_, lean_object* v_arg_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet(v_fn_425_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; uint8_t v___x_437_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_a_436_);
v___x_437_ = lean_unbox(v_a_436_);
lean_dec(v_a_436_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; 
lean_dec_ref_known(v___x_435_, 1);
v___x_438_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet(v_arg_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
return v___x_438_;
}
else
{
lean_dec_ref(v_arg_426_);
return v___x_435_;
}
}
else
{
lean_dec_ref(v_arg_426_);
return v___x_435_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0(lean_object* v_00_u03b2_439_, lean_object* v_m_440_, lean_object* v_a_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0___redArg(v_m_440_, v_a_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0___boxed(lean_object* v_00_u03b2_443_, lean_object* v_m_444_, lean_object* v_a_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0(v_00_u03b2_443_, v_m_444_, v_a_445_);
lean_dec_ref(v_a_445_);
lean_dec_ref(v_m_444_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1(lean_object* v_00_u03b2_447_, lean_object* v_m_448_, lean_object* v_query_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1___redArg(v_m_448_, v_query_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1___boxed(lean_object* v_00_u03b2_451_, lean_object* v_m_452_, lean_object* v_query_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1(v_00_u03b2_451_, v_m_452_, v_query_453_);
lean_dec_ref(v_query_453_);
lean_dec_ref(v_m_452_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__2(lean_object* v_00_u03b2_455_, lean_object* v_m_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__2___redArg(v_m_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__2___boxed(lean_object* v_00_u03b2_458_, lean_object* v_m_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__2(v_00_u03b2_458_, v_m_459_);
lean_dec_ref(v_m_459_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0_spec__0(lean_object* v_00_u03b2_461_, lean_object* v_m_462_, lean_object* v_query_463_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0_spec__0___redArg(v_m_462_, v_query_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0_spec__0___boxed(lean_object* v_00_u03b2_465_, lean_object* v_m_466_, lean_object* v_query_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0_spec__0(v_00_u03b2_465_, v_m_466_, v_query_467_);
lean_dec_ref(v_query_467_);
lean_dec_ref(v_m_466_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2(lean_object* v_00_u03b2_469_, lean_object* v_m_470_, lean_object* v_query_471_, lean_object* v_x_472_, lean_object* v_x_473_, lean_object* v_x_474_, lean_object* v_x_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2___redArg(v_m_470_, v_query_471_, v_x_472_, v_x_473_, v_x_474_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2___boxed(lean_object* v_00_u03b2_477_, lean_object* v_m_478_, lean_object* v_query_479_, lean_object* v_x_480_, lean_object* v_x_481_, lean_object* v_x_482_, lean_object* v_x_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2(v_00_u03b2_477_, v_m_478_, v_query_479_, v_x_480_, v_x_481_, v_x_482_, v_x_483_);
lean_dec_ref(v_query_479_);
lean_dec_ref(v_m_478_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__2_spec__4(lean_object* v_00_u03b2_485_, lean_object* v_init_486_, lean_object* v_b_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__2_spec__4___redArg(v_init_486_, v_b_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__2_spec__4___boxed(lean_object* v_00_u03b2_489_, lean_object* v_init_490_, lean_object* v_b_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__2_spec__4(v_00_u03b2_489_, v_init_490_, v_b_491_);
lean_dec_ref(v_b_491_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_493_, lean_object* v_b_494_, lean_object* v_acc_495_, lean_object* v_i_496_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__2_spec__4_spec__5___redArg(v_b_494_, v_acc_495_, v_i_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b2_498_, lean_object* v_b_499_, lean_object* v_acc_500_, lean_object* v_i_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__2_spec__4_spec__5(v_00_u03b2_498_, v_b_499_, v_acc_500_, v_i_501_);
lean_dec_ref(v_b_499_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2___redArg(lean_object* v_fvarId_503_, lean_object* v___y_504_){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = l_Lean_Expr_fvar___override(v_fvarId_503_);
v___x_507_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_506_, v___y_504_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2___redArg___boxed(lean_object* v_fvarId_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2___redArg(v_fvarId_508_, v___y_509_);
lean_dec(v___y_509_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2(lean_object* v_fvarId_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2___redArg(v_fvarId_512_, v___y_515_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2___boxed(lean_object* v_fvarId_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2(v_fvarId_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2___redArg(lean_object* v___y_532_){
_start:
{
lean_object* v___x_534_; lean_object* v_ngen_535_; lean_object* v_namePrefix_536_; lean_object* v_idx_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_566_; 
v___x_534_ = lean_st_ref_get(v___y_532_);
v_ngen_535_ = lean_ctor_get(v___x_534_, 2);
lean_inc_ref(v_ngen_535_);
lean_dec(v___x_534_);
v_namePrefix_536_ = lean_ctor_get(v_ngen_535_, 0);
v_idx_537_ = lean_ctor_get(v_ngen_535_, 1);
v_isSharedCheck_566_ = !lean_is_exclusive(v_ngen_535_);
if (v_isSharedCheck_566_ == 0)
{
v___x_539_ = v_ngen_535_;
v_isShared_540_ = v_isSharedCheck_566_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_idx_537_);
lean_inc(v_namePrefix_536_);
lean_dec(v_ngen_535_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_566_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_541_; lean_object* v_env_542_; lean_object* v_nextMacroScope_543_; lean_object* v_auxDeclNGen_544_; lean_object* v_traceState_545_; lean_object* v_cache_546_; lean_object* v_messages_547_; lean_object* v_infoState_548_; lean_object* v_snapshotTasks_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_564_; 
v___x_541_ = lean_st_ref_take(v___y_532_);
v_env_542_ = lean_ctor_get(v___x_541_, 0);
v_nextMacroScope_543_ = lean_ctor_get(v___x_541_, 1);
v_auxDeclNGen_544_ = lean_ctor_get(v___x_541_, 3);
v_traceState_545_ = lean_ctor_get(v___x_541_, 4);
v_cache_546_ = lean_ctor_get(v___x_541_, 5);
v_messages_547_ = lean_ctor_get(v___x_541_, 6);
v_infoState_548_ = lean_ctor_get(v___x_541_, 7);
v_snapshotTasks_549_ = lean_ctor_get(v___x_541_, 8);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_564_ == 0)
{
lean_object* v_unused_565_; 
v_unused_565_ = lean_ctor_get(v___x_541_, 2);
lean_dec(v_unused_565_);
v___x_551_ = v___x_541_;
v_isShared_552_ = v_isSharedCheck_564_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_snapshotTasks_549_);
lean_inc(v_infoState_548_);
lean_inc(v_messages_547_);
lean_inc(v_cache_546_);
lean_inc(v_traceState_545_);
lean_inc(v_auxDeclNGen_544_);
lean_inc(v_nextMacroScope_543_);
lean_inc(v_env_542_);
lean_dec(v___x_541_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_564_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v_r_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_557_; 
lean_inc(v_idx_537_);
lean_inc(v_namePrefix_536_);
v_r_553_ = l_Lean_Name_num___override(v_namePrefix_536_, v_idx_537_);
v___x_554_ = lean_unsigned_to_nat(1u);
v___x_555_ = lean_nat_add(v_idx_537_, v___x_554_);
lean_dec(v_idx_537_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 1, v___x_555_);
v___x_557_ = v___x_539_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_namePrefix_536_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v___x_555_);
v___x_557_ = v_reuseFailAlloc_563_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_object* v___x_559_; 
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 2, v___x_557_);
v___x_559_ = v___x_551_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_env_542_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v_nextMacroScope_543_);
lean_ctor_set(v_reuseFailAlloc_562_, 2, v___x_557_);
lean_ctor_set(v_reuseFailAlloc_562_, 3, v_auxDeclNGen_544_);
lean_ctor_set(v_reuseFailAlloc_562_, 4, v_traceState_545_);
lean_ctor_set(v_reuseFailAlloc_562_, 5, v_cache_546_);
lean_ctor_set(v_reuseFailAlloc_562_, 6, v_messages_547_);
lean_ctor_set(v_reuseFailAlloc_562_, 7, v_infoState_548_);
lean_ctor_set(v_reuseFailAlloc_562_, 8, v_snapshotTasks_549_);
v___x_559_ = v_reuseFailAlloc_562_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = lean_st_ref_put(v___y_532_, v___x_559_);
v___x_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_561_, 0, v_r_553_);
return v___x_561_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2___redArg___boxed(lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2___redArg(v___y_567_);
lean_dec(v___y_567_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1(lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
lean_object* v___x_578_; lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_586_; 
v___x_578_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2___redArg(v___y_576_);
v_a_579_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_586_ == 0)
{
v___x_581_ = v___x_578_;
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v___x_578_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_584_; 
if (v_isShared_582_ == 0)
{
v___x_584_ = v___x_581_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_a_579_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1___boxed(lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1(v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5___redArg(lean_object* v_m_596_, lean_object* v_query_597_, lean_object* v_x_598_, lean_object* v_x_599_, lean_object* v_x_600_){
_start:
{
lean_object* v_zero_601_; uint8_t v_isZero_602_; 
v_zero_601_ = lean_unsigned_to_nat(0u);
v_isZero_602_ = lean_nat_dec_eq(v_x_599_, v_zero_601_);
if (v_isZero_602_ == 1)
{
lean_dec(v_x_600_);
lean_dec(v_x_599_);
if (lean_obj_tag(v_x_598_) == 0)
{
lean_object* v___x_603_; 
v___x_603_ = lean_box(2);
return v___x_603_;
}
else
{
lean_object* v_val_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
v_val_604_ = lean_ctor_get(v_x_598_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v_x_598_);
if (v_isSharedCheck_611_ == 0)
{
v___x_606_ = v_x_598_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_val_604_);
lean_dec(v_x_598_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_val_604_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
else
{
lean_object* v_keyArray_612_; lean_object* v_valueArray_613_; lean_object* v___x_614_; uint8_t v_isSome_615_; 
v_keyArray_612_ = lean_ctor_get(v_m_596_, 1);
v_valueArray_613_ = lean_ctor_get(v_m_596_, 2);
v___x_614_ = lean_array_fget_borrowed(v_keyArray_612_, v_x_600_);
v_isSome_615_ = lean_noption_is_some(v___x_614_);
if (v_isSome_615_ == 0)
{
lean_dec(v_x_599_);
if (lean_obj_tag(v_x_598_) == 0)
{
lean_object* v___x_616_; 
v___x_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_616_, 0, v_x_600_);
return v___x_616_;
}
else
{
lean_object* v_val_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_624_; 
lean_dec(v_x_600_);
v_val_617_ = lean_ctor_get(v_x_598_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v_x_598_);
if (v_isSharedCheck_624_ == 0)
{
v___x_619_ = v_x_598_;
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_val_617_);
lean_dec(v_x_598_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_622_; 
if (v_isShared_620_ == 0)
{
v___x_622_ = v___x_619_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_val_617_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
}
else
{
lean_object* v_one_625_; lean_object* v_n_626_; lean_object* v___y_628_; 
v_one_625_ = lean_unsigned_to_nat(1u);
v_n_626_ = lean_nat_sub(v_x_599_, v_one_625_);
lean_dec(v_x_599_);
if (v_isSome_615_ == 0)
{
goto v___jp_634_;
}
else
{
lean_object* v___x_636_; uint8_t v_isSome_637_; 
v___x_636_ = lean_array_fget_borrowed(v_valueArray_613_, v_x_600_);
v_isSome_637_ = lean_noption_is_some(v___x_636_);
if (v_isSome_637_ == 0)
{
goto v___jp_634_;
}
else
{
lean_object* v_val_638_; lean_object* v_fst_639_; lean_object* v_snd_640_; lean_object* v_fst_641_; lean_object* v_snd_642_; lean_object* v_val_643_; uint8_t v___y_645_; size_t v___x_652_; size_t v___x_653_; uint8_t v___x_654_; 
lean_inc(v___x_614_);
v_val_638_ = lean_noption_get(v___x_614_);
v_fst_639_ = lean_ctor_get(v_val_638_, 0);
lean_inc(v_fst_639_);
v_snd_640_ = lean_ctor_get(v_val_638_, 1);
lean_inc(v_snd_640_);
v_fst_641_ = lean_ctor_get(v_query_597_, 0);
v_snd_642_ = lean_ctor_get(v_query_597_, 1);
lean_inc(v___x_636_);
v_val_643_ = lean_noption_get(v___x_636_);
v___x_652_ = lean_ptr_addr(v_fst_639_);
lean_dec(v_fst_639_);
v___x_653_ = lean_ptr_addr(v_fst_641_);
v___x_654_ = lean_usize_dec_eq(v___x_652_, v___x_653_);
if (v___x_654_ == 0)
{
lean_dec(v_snd_640_);
v___y_645_ = v___x_654_;
goto v___jp_644_;
}
else
{
size_t v___x_655_; size_t v___x_656_; uint8_t v___x_657_; 
v___x_655_ = lean_ptr_addr(v_snd_640_);
lean_dec(v_snd_640_);
v___x_656_ = lean_ptr_addr(v_snd_642_);
v___x_657_ = lean_usize_dec_eq(v___x_655_, v___x_656_);
v___y_645_ = v___x_657_;
goto v___jp_644_;
}
v___jp_644_:
{
if (v___y_645_ == 0)
{
lean_object* v___x_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
lean_dec(v_val_643_);
lean_dec(v_val_638_);
v___x_646_ = lean_array_get_size(v_keyArray_612_);
v___x_647_ = lean_nat_add(v_x_600_, v_one_625_);
lean_dec(v_x_600_);
v___x_648_ = lean_nat_dec_lt(v___x_647_, v___x_646_);
if (v___x_648_ == 0)
{
lean_dec(v___x_647_);
v_x_599_ = v_n_626_;
v_x_600_ = v_zero_601_;
goto _start;
}
else
{
v_x_599_ = v_n_626_;
v_x_600_ = v___x_647_;
goto _start;
}
}
else
{
lean_object* v___x_651_; 
lean_dec(v_n_626_);
lean_dec(v_x_598_);
v___x_651_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_651_, 0, v_x_600_);
lean_ctor_set(v___x_651_, 1, v_val_638_);
lean_ctor_set(v___x_651_, 2, v_val_643_);
return v___x_651_;
}
}
}
}
v___jp_627_:
{
lean_object* v___x_629_; lean_object* v___x_630_; uint8_t v___x_631_; 
v___x_629_ = lean_array_get_size(v_keyArray_612_);
v___x_630_ = lean_nat_add(v_x_600_, v_one_625_);
lean_dec(v_x_600_);
v___x_631_ = lean_nat_dec_lt(v___x_630_, v___x_629_);
if (v___x_631_ == 0)
{
lean_dec(v___x_630_);
v_x_598_ = v___y_628_;
v_x_599_ = v_n_626_;
v_x_600_ = v_zero_601_;
goto _start;
}
else
{
v_x_598_ = v___y_628_;
v_x_599_ = v_n_626_;
v_x_600_ = v___x_630_;
goto _start;
}
}
v___jp_634_:
{
if (lean_obj_tag(v_x_598_) == 0)
{
lean_object* v___x_635_; 
lean_inc(v_x_600_);
v___x_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_635_, 0, v_x_600_);
v___y_628_ = v___x_635_;
goto v___jp_627_;
}
else
{
v___y_628_ = v_x_598_;
goto v___jp_627_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5___redArg___boxed(lean_object* v_m_658_, lean_object* v_query_659_, lean_object* v_x_660_, lean_object* v_x_661_, lean_object* v_x_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5___redArg(v_m_658_, v_query_659_, v_x_660_, v_x_661_, v_x_662_);
lean_dec_ref(v_query_659_);
lean_dec_ref(v_m_658_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3___redArg(lean_object* v_m_664_, lean_object* v_query_665_){
_start:
{
lean_object* v_keyArray_666_; lean_object* v_fst_667_; lean_object* v_snd_668_; lean_object* v___x_669_; size_t v___x_670_; size_t v___x_671_; size_t v___x_672_; uint64_t v___x_673_; size_t v___x_674_; size_t v___x_675_; uint64_t v___x_676_; uint64_t v___x_677_; uint64_t v___x_678_; uint64_t v___x_679_; uint64_t v_fold_680_; uint64_t v___x_681_; uint64_t v___x_682_; uint64_t v___x_683_; size_t v___x_684_; size_t v___x_685_; size_t v___x_686_; size_t v___x_687_; size_t v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v_keyArray_666_ = lean_ctor_get(v_m_664_, 1);
v_fst_667_ = lean_ctor_get(v_query_665_, 0);
v_snd_668_ = lean_ctor_get(v_query_665_, 1);
v___x_669_ = lean_array_get_size(v_keyArray_666_);
v___x_670_ = lean_ptr_addr(v_fst_667_);
v___x_671_ = ((size_t)3ULL);
v___x_672_ = lean_usize_shift_right(v___x_670_, v___x_671_);
v___x_673_ = lean_usize_to_uint64(v___x_672_);
v___x_674_ = lean_ptr_addr(v_snd_668_);
v___x_675_ = lean_usize_shift_right(v___x_674_, v___x_671_);
v___x_676_ = lean_usize_to_uint64(v___x_675_);
v___x_677_ = lean_uint64_mix_hash(v___x_673_, v___x_676_);
v___x_678_ = 32ULL;
v___x_679_ = lean_uint64_shift_right(v___x_677_, v___x_678_);
v_fold_680_ = lean_uint64_xor(v___x_677_, v___x_679_);
v___x_681_ = 16ULL;
v___x_682_ = lean_uint64_shift_right(v_fold_680_, v___x_681_);
v___x_683_ = lean_uint64_xor(v_fold_680_, v___x_682_);
v___x_684_ = lean_uint64_to_usize(v___x_683_);
v___x_685_ = lean_usize_of_nat(v___x_669_);
v___x_686_ = ((size_t)1ULL);
v___x_687_ = lean_usize_sub(v___x_685_, v___x_686_);
v___x_688_ = lean_usize_land(v___x_684_, v___x_687_);
v___x_689_ = lean_usize_to_nat(v___x_688_);
v___x_690_ = lean_box(0);
v___x_691_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5___redArg(v_m_664_, v_query_665_, v___x_690_, v___x_669_, v___x_689_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3___redArg___boxed(lean_object* v_m_692_, lean_object* v_query_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3___redArg(v_m_692_, v_query_693_);
lean_dec_ref(v_query_693_);
lean_dec_ref(v_m_692_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0___redArg(lean_object* v_m_695_, lean_object* v_query_696_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3___redArg(v_m_695_, v_query_696_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v_index_698_; lean_object* v_key_699_; lean_object* v_value_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
v_index_698_ = lean_ctor_get(v___x_697_, 0);
v_key_699_ = lean_ctor_get(v___x_697_, 1);
v_value_700_ = lean_ctor_get(v___x_697_, 2);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_697_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_value_700_);
lean_inc(v_key_699_);
lean_inc(v_index_698_);
lean_dec(v___x_697_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_index_698_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v_key_699_);
lean_ctor_set(v_reuseFailAlloc_706_, 2, v_value_700_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
else
{
lean_object* v___x_708_; 
lean_dec(v___x_697_);
v___x_708_ = lean_box(1);
return v___x_708_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0___redArg___boxed(lean_object* v_m_709_, lean_object* v_query_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0___redArg(v_m_709_, v_query_710_);
lean_dec_ref(v_query_710_);
lean_dec_ref(v_m_709_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0___redArg(lean_object* v_m_712_, lean_object* v_a_713_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0___redArg(v_m_712_, v_a_713_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_value_715_; lean_object* v___x_716_; 
v_value_715_ = lean_ctor_get(v___x_714_, 2);
lean_inc(v_value_715_);
lean_dec_ref_known(v___x_714_, 3);
v___x_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_716_, 0, v_value_715_);
return v___x_716_;
}
else
{
lean_object* v___x_717_; 
v___x_717_ = lean_box(0);
return v___x_717_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0___redArg___boxed(lean_object* v_m_718_, lean_object* v_a_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0___redArg(v_m_718_, v_a_719_);
lean_dec_ref(v_a_719_);
lean_dec_ref(v_m_718_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__4_spec__7_spec__8___redArg(lean_object* v_b_721_, lean_object* v_acc_722_, lean_object* v_i_723_){
_start:
{
lean_object* v___y_725_; lean_object* v_keyArray_733_; lean_object* v_valueArray_734_; lean_object* v___x_735_; uint8_t v___x_736_; 
v_keyArray_733_ = lean_ctor_get(v_b_721_, 1);
v_valueArray_734_ = lean_ctor_get(v_b_721_, 2);
v___x_735_ = lean_array_get_size(v_keyArray_733_);
v___x_736_ = lean_nat_dec_lt(v_i_723_, v___x_735_);
if (v___x_736_ == 0)
{
lean_dec(v_i_723_);
return v_acc_722_;
}
else
{
lean_object* v___x_737_; uint8_t v_isSome_738_; 
v___x_737_ = lean_array_fget_borrowed(v_keyArray_733_, v_i_723_);
v_isSome_738_ = lean_noption_is_some(v___x_737_);
if (v_isSome_738_ == 0)
{
goto v___jp_729_;
}
else
{
lean_object* v___x_739_; uint8_t v_isSome_740_; 
v___x_739_ = lean_array_fget_borrowed(v_valueArray_734_, v_i_723_);
v_isSome_740_ = lean_noption_is_some(v___x_739_);
if (v_isSome_740_ == 0)
{
goto v___jp_729_;
}
else
{
lean_object* v_val_741_; lean_object* v_val_742_; lean_object* v_i_744_; lean_object* v___x_749_; 
lean_inc(v___x_737_);
v_val_741_ = lean_noption_get(v___x_737_);
lean_inc(v___x_739_);
v_val_742_ = lean_noption_get(v___x_739_);
v___x_749_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3___redArg(v_acc_722_, v_val_741_);
switch(lean_obj_tag(v___x_749_))
{
case 0:
{
lean_object* v_index_750_; lean_object* v_size_751_; lean_object* v___x_752_; 
v_index_750_ = lean_ctor_get(v___x_749_, 0);
lean_inc(v_index_750_);
lean_dec_ref_known(v___x_749_, 3);
v_size_751_ = lean_ctor_get(v_acc_722_, 0);
lean_inc(v_size_751_);
v___x_752_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_722_, v_size_751_, v_index_750_, v_val_741_, v_val_742_);
lean_dec(v_index_750_);
v___y_725_ = v___x_752_;
goto v___jp_724_;
}
case 1:
{
lean_object* v_index_753_; 
v_index_753_ = lean_ctor_get(v___x_749_, 0);
lean_inc(v_index_753_);
lean_dec_ref_known(v___x_749_, 1);
v_i_744_ = v_index_753_;
goto v___jp_743_;
}
default: 
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = lean_unsigned_to_nat(0u);
v___x_755_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_722_, v___x_754_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_index_756_; 
v_index_756_ = lean_ctor_get(v___x_755_, 0);
lean_inc(v_index_756_);
lean_dec_ref_known(v___x_755_, 1);
v_i_744_ = v_index_756_;
goto v___jp_743_;
}
else
{
lean_dec(v_val_742_);
lean_dec(v_val_741_);
v___y_725_ = v_acc_722_;
goto v___jp_724_;
}
}
}
v___jp_743_:
{
lean_object* v_size_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v_size_745_ = lean_ctor_get(v_acc_722_, 0);
v___x_746_ = lean_unsigned_to_nat(1u);
v___x_747_ = lean_nat_add(v_size_745_, v___x_746_);
v___x_748_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_722_, v___x_747_, v_i_744_, v_val_741_, v_val_742_);
lean_dec(v_i_744_);
v___y_725_ = v___x_748_;
goto v___jp_724_;
}
}
}
}
v___jp_724_:
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = lean_unsigned_to_nat(1u);
v___x_727_ = lean_nat_add(v_i_723_, v___x_726_);
lean_dec(v_i_723_);
v_acc_722_ = v___y_725_;
v_i_723_ = v___x_727_;
goto _start;
}
v___jp_729_:
{
lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_730_ = lean_unsigned_to_nat(1u);
v___x_731_ = lean_nat_add(v_i_723_, v___x_730_);
lean_dec(v_i_723_);
v_i_723_ = v___x_731_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__4_spec__7_spec__8___redArg___boxed(lean_object* v_b_757_, lean_object* v_acc_758_, lean_object* v_i_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__4_spec__7_spec__8___redArg(v_b_757_, v_acc_758_, v_i_759_);
lean_dec_ref(v_b_757_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__4_spec__7___redArg(lean_object* v_init_761_, lean_object* v_b_762_){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = lean_unsigned_to_nat(0u);
v___x_764_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__4_spec__7_spec__8___redArg(v_b_762_, v_init_761_, v___x_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__4_spec__7___redArg___boxed(lean_object* v_init_765_, lean_object* v_b_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__4_spec__7___redArg(v_init_765_, v_b_766_);
lean_dec_ref(v_b_766_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__4___redArg(lean_object* v_m_768_){
_start:
{
lean_object* v_keyArray_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v_cellCount_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v_target_776_; lean_object* v___x_777_; 
v_keyArray_769_ = lean_ctor_get(v_m_768_, 1);
v___x_770_ = lean_array_get_size(v_keyArray_769_);
v___x_771_ = lean_unsigned_to_nat(2u);
v_cellCount_772_ = lean_nat_mul(v___x_770_, v___x_771_);
v___x_773_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_772_);
v___x_774_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_772_);
v___x_775_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_772_);
v_target_776_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_776_, 0, v___x_773_);
lean_ctor_set(v_target_776_, 1, v___x_774_);
lean_ctor_set(v_target_776_, 2, v___x_775_);
v___x_777_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__4_spec__7___redArg(v_target_776_, v_m_768_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__4___redArg___boxed(lean_object* v_m_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__4___redArg(v_m_778_);
lean_dec_ref(v_m_778_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl(lean_object* v_userName_780_, lean_object* v_type_781_, lean_object* v_value_782_, uint8_t v_nondep_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_){
_start:
{
lean_object* v___x_792_; lean_object* v_valueMap_793_; lean_object* v_key_794_; lean_object* v___x_795_; 
v___x_792_ = lean_st_ref_get(v_a_784_);
v_valueMap_793_ = lean_ctor_get(v___x_792_, 4);
lean_inc_ref(v_valueMap_793_);
lean_dec(v___x_792_);
lean_inc_ref(v_value_782_);
lean_inc_ref(v_type_781_);
v_key_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_794_, 0, v_type_781_);
lean_ctor_set(v_key_794_, 1, v_value_782_);
v___x_795_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0___redArg(v_valueMap_793_, v_key_794_);
lean_dec_ref(v_valueMap_793_);
if (lean_obj_tag(v___x_795_) == 1)
{
lean_object* v_val_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_843_; 
lean_dec_ref_known(v_key_794_, 2);
lean_dec_ref(v_value_782_);
lean_dec_ref(v_type_781_);
lean_dec(v_userName_780_);
v_val_796_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_843_ == 0)
{
v___x_798_ = v___x_795_;
v_isShared_799_ = v_isSharedCheck_843_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_val_796_);
lean_dec(v___x_795_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_843_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_800_; lean_object* v___y_802_; 
v___x_800_ = l_Lean_Meta_Sym_LiftLet_instInhabitedDecl_default;
if (v_nondep_783_ == 0)
{
lean_object* v___x_810_; lean_object* v_cache_811_; lean_object* v_cacheClosed_812_; lean_object* v_hasLetCache_813_; lean_object* v_decls_814_; lean_object* v_valueMap_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_842_; 
v___x_810_ = lean_st_ref_take(v_a_784_);
v_cache_811_ = lean_ctor_get(v___x_810_, 0);
v_cacheClosed_812_ = lean_ctor_get(v___x_810_, 1);
v_hasLetCache_813_ = lean_ctor_get(v___x_810_, 2);
v_decls_814_ = lean_ctor_get(v___x_810_, 3);
v_valueMap_815_ = lean_ctor_get(v___x_810_, 4);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_842_ == 0)
{
v___x_817_ = v___x_810_;
v_isShared_818_ = v_isSharedCheck_842_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_valueMap_815_);
lean_inc(v_decls_814_);
lean_inc(v_hasLetCache_813_);
lean_inc(v_cacheClosed_812_);
lean_inc(v_cache_811_);
lean_dec(v___x_810_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_842_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___y_820_; lean_object* v___x_825_; uint8_t v___x_826_; 
v___x_825_ = lean_array_get_size(v_decls_814_);
v___x_826_ = lean_nat_dec_lt(v_val_796_, v___x_825_);
if (v___x_826_ == 0)
{
v___y_820_ = v_decls_814_;
goto v___jp_819_;
}
else
{
lean_object* v_v_827_; lean_object* v_fvar_828_; lean_object* v_userName_829_; lean_object* v_type_830_; lean_object* v_value_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_841_; 
v_v_827_ = lean_array_fget(v_decls_814_, v_val_796_);
v_fvar_828_ = lean_ctor_get(v_v_827_, 0);
v_userName_829_ = lean_ctor_get(v_v_827_, 1);
v_type_830_ = lean_ctor_get(v_v_827_, 2);
v_value_831_ = lean_ctor_get(v_v_827_, 3);
v_isSharedCheck_841_ = !lean_is_exclusive(v_v_827_);
if (v_isSharedCheck_841_ == 0)
{
v___x_833_ = v_v_827_;
v_isShared_834_ = v_isSharedCheck_841_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_value_831_);
lean_inc(v_type_830_);
lean_inc(v_userName_829_);
lean_inc(v_fvar_828_);
lean_dec(v_v_827_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_841_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_835_; lean_object* v_xs_x27_836_; lean_object* v___x_838_; 
v___x_835_ = lean_box(0);
v_xs_x27_836_ = lean_array_fset(v_decls_814_, v_val_796_, v___x_835_);
if (v_isShared_834_ == 0)
{
v___x_838_ = v___x_833_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_fvar_828_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_userName_829_);
lean_ctor_set(v_reuseFailAlloc_840_, 2, v_type_830_);
lean_ctor_set(v_reuseFailAlloc_840_, 3, v_value_831_);
v___x_838_ = v_reuseFailAlloc_840_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
lean_object* v___x_839_; 
lean_ctor_set_uint8(v___x_838_, sizeof(void*)*4, v_nondep_783_);
v___x_839_ = lean_array_fset(v_xs_x27_836_, v_val_796_, v___x_838_);
v___y_820_ = v___x_839_;
goto v___jp_819_;
}
}
}
v___jp_819_:
{
lean_object* v___x_822_; 
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 3, v___y_820_);
v___x_822_ = v___x_817_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_cache_811_);
lean_ctor_set(v_reuseFailAlloc_824_, 1, v_cacheClosed_812_);
lean_ctor_set(v_reuseFailAlloc_824_, 2, v_hasLetCache_813_);
lean_ctor_set(v_reuseFailAlloc_824_, 3, v___y_820_);
lean_ctor_set(v_reuseFailAlloc_824_, 4, v_valueMap_815_);
v___x_822_ = v_reuseFailAlloc_824_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
lean_object* v___x_823_; 
v___x_823_ = lean_st_ref_put(v_a_784_, v___x_822_);
v___y_802_ = v_a_784_;
goto v___jp_801_;
}
}
}
}
else
{
v___y_802_ = v_a_784_;
goto v___jp_801_;
}
v___jp_801_:
{
lean_object* v___x_803_; lean_object* v_decls_804_; lean_object* v___x_805_; lean_object* v_fvar_806_; lean_object* v___x_808_; 
v___x_803_ = lean_st_ref_get(v___y_802_);
v_decls_804_ = lean_ctor_get(v___x_803_, 3);
lean_inc_ref(v_decls_804_);
lean_dec(v___x_803_);
v___x_805_ = lean_array_get(v___x_800_, v_decls_804_, v_val_796_);
lean_dec(v_val_796_);
lean_dec_ref(v_decls_804_);
v_fvar_806_ = lean_ctor_get(v___x_805_, 0);
lean_inc_ref(v_fvar_806_);
lean_dec(v___x_805_);
if (v_isShared_799_ == 0)
{
lean_ctor_set_tag(v___x_798_, 0);
lean_ctor_set(v___x_798_, 0, v_fvar_806_);
v___x_808_ = v___x_798_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_fvar_806_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
else
{
lean_object* v___x_844_; 
lean_dec(v___x_795_);
v___x_844_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1(v_a_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; lean_object* v___x_846_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_a_845_);
lean_dec_ref_known(v___x_844_, 1);
v___x_846_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2___redArg(v_a_845_, v_a_786_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_939_; 
v_a_847_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_939_ == 0)
{
v___x_849_ = v___x_846_;
v_isShared_850_ = v_isSharedCheck_939_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_846_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_939_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v_decls_853_; lean_object* v_cache_854_; lean_object* v_cacheClosed_855_; lean_object* v_hasLetCache_856_; lean_object* v_decls_857_; lean_object* v_valueMap_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_938_; 
v___x_851_ = lean_st_ref_get(v_a_784_);
v___x_852_ = lean_st_ref_take(v_a_784_);
v_decls_853_ = lean_ctor_get(v___x_851_, 3);
lean_inc_ref(v_decls_853_);
lean_dec(v___x_851_);
v_cache_854_ = lean_ctor_get(v___x_852_, 0);
v_cacheClosed_855_ = lean_ctor_get(v___x_852_, 1);
v_hasLetCache_856_ = lean_ctor_get(v___x_852_, 2);
v_decls_857_ = lean_ctor_get(v___x_852_, 3);
v_valueMap_858_ = lean_ctor_get(v___x_852_, 4);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_938_ == 0)
{
v___x_860_ = v___x_852_;
v_isShared_861_ = v_isSharedCheck_938_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_valueMap_858_);
lean_inc(v_decls_857_);
lean_inc(v_hasLetCache_856_);
lean_inc(v_cacheClosed_855_);
lean_inc(v_cache_854_);
lean_dec(v___x_852_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_938_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___y_866_; lean_object* v___y_875_; lean_object* v_i_876_; lean_object* v___y_892_; lean_object* v_i_893_; lean_object* v___y_899_; lean_object* v___x_908_; 
v___x_862_ = lean_array_get_size(v_decls_853_);
lean_dec_ref(v_decls_853_);
lean_inc(v_a_847_);
v___x_863_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_863_, 0, v_a_847_);
lean_ctor_set(v___x_863_, 1, v_userName_780_);
lean_ctor_set(v___x_863_, 2, v_type_781_);
lean_ctor_set(v___x_863_, 3, v_value_782_);
lean_ctor_set_uint8(v___x_863_, sizeof(void*)*4, v_nondep_783_);
v___x_864_ = lean_array_push(v_decls_857_, v___x_863_);
v___x_908_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3___redArg(v_valueMap_858_, v_key_794_);
switch(lean_obj_tag(v___x_908_))
{
case 0:
{
lean_object* v_index_909_; lean_object* v_size_910_; lean_object* v___x_911_; 
v_index_909_ = lean_ctor_get(v___x_908_, 0);
lean_inc(v_index_909_);
lean_dec_ref_known(v___x_908_, 3);
v_size_910_ = lean_ctor_get(v_valueMap_858_, 0);
lean_inc(v_size_910_);
v___x_911_ = l_Std_DHashMap_Raw_setEntry___redArg(v_valueMap_858_, v_size_910_, v_index_909_, v_key_794_, v___x_862_);
lean_dec(v_index_909_);
v___y_866_ = v___x_911_;
goto v___jp_865_;
}
case 1:
{
lean_object* v_index_912_; lean_object* v_size_913_; lean_object* v_keyArray_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; uint8_t v___x_918_; 
v_index_912_ = lean_ctor_get(v___x_908_, 0);
lean_inc(v_index_912_);
lean_dec_ref_known(v___x_908_, 1);
v_size_913_ = lean_ctor_get(v_valueMap_858_, 0);
v_keyArray_914_ = lean_ctor_get(v_valueMap_858_, 1);
v___x_915_ = lean_unsigned_to_nat(1u);
v___x_916_ = lean_nat_add(v_size_913_, v___x_915_);
v___x_917_ = lean_array_get_size(v_keyArray_914_);
v___x_918_ = lean_nat_dec_lt(v___x_916_, v___x_917_);
if (v___x_918_ == 0)
{
lean_dec(v___x_916_);
lean_dec(v_index_912_);
goto v___jp_881_;
}
else
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; uint8_t v___x_923_; 
v___x_919_ = lean_unsigned_to_nat(4u);
v___x_920_ = lean_nat_mul(v___x_916_, v___x_919_);
v___x_921_ = lean_unsigned_to_nat(3u);
v___x_922_ = lean_nat_mul(v___x_917_, v___x_921_);
v___x_923_ = lean_nat_dec_le(v___x_920_, v___x_922_);
lean_dec(v___x_922_);
lean_dec(v___x_920_);
if (v___x_923_ == 0)
{
lean_dec(v___x_916_);
lean_dec(v_index_912_);
goto v___jp_881_;
}
else
{
lean_object* v___x_924_; 
v___x_924_ = l_Std_DHashMap_Raw_setEntry___redArg(v_valueMap_858_, v___x_916_, v_index_912_, v_key_794_, v___x_862_);
lean_dec(v_index_912_);
v___y_866_ = v___x_924_;
goto v___jp_865_;
}
}
}
default: 
{
lean_object* v_size_925_; lean_object* v_keyArray_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; uint8_t v___x_930_; 
v_size_925_ = lean_ctor_get(v_valueMap_858_, 0);
v_keyArray_926_ = lean_ctor_get(v_valueMap_858_, 1);
v___x_927_ = lean_unsigned_to_nat(1u);
v___x_928_ = lean_nat_add(v_size_925_, v___x_927_);
v___x_929_ = lean_array_get_size(v_keyArray_926_);
v___x_930_ = lean_nat_dec_lt(v___x_928_, v___x_929_);
if (v___x_930_ == 0)
{
lean_object* v___x_931_; 
lean_dec(v___x_928_);
v___x_931_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__4___redArg(v_valueMap_858_);
lean_dec_ref(v_valueMap_858_);
v___y_899_ = v___x_931_;
goto v___jp_898_;
}
else
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; uint8_t v___x_936_; 
v___x_932_ = lean_unsigned_to_nat(4u);
v___x_933_ = lean_nat_mul(v___x_928_, v___x_932_);
lean_dec(v___x_928_);
v___x_934_ = lean_unsigned_to_nat(3u);
v___x_935_ = lean_nat_mul(v___x_929_, v___x_934_);
v___x_936_ = lean_nat_dec_le(v___x_933_, v___x_935_);
lean_dec(v___x_935_);
lean_dec(v___x_933_);
if (v___x_936_ == 0)
{
lean_object* v___x_937_; 
v___x_937_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__4___redArg(v_valueMap_858_);
lean_dec_ref(v_valueMap_858_);
v___y_899_ = v___x_937_;
goto v___jp_898_;
}
else
{
v___y_899_ = v_valueMap_858_;
goto v___jp_898_;
}
}
}
}
v___jp_865_:
{
lean_object* v___x_868_; 
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 4, v___y_866_);
lean_ctor_set(v___x_860_, 3, v___x_864_);
v___x_868_ = v___x_860_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_cache_854_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v_cacheClosed_855_);
lean_ctor_set(v_reuseFailAlloc_873_, 2, v_hasLetCache_856_);
lean_ctor_set(v_reuseFailAlloc_873_, 3, v___x_864_);
lean_ctor_set(v_reuseFailAlloc_873_, 4, v___y_866_);
v___x_868_ = v_reuseFailAlloc_873_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
lean_object* v___x_869_; lean_object* v___x_871_; 
v___x_869_ = lean_st_ref_put(v_a_784_, v___x_868_);
if (v_isShared_850_ == 0)
{
v___x_871_ = v___x_849_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_847_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
v___jp_874_:
{
lean_object* v_size_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v_size_877_ = lean_ctor_get(v___y_875_, 0);
v___x_878_ = lean_unsigned_to_nat(1u);
v___x_879_ = lean_nat_add(v_size_877_, v___x_878_);
v___x_880_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_875_, v___x_879_, v_i_876_, v_key_794_, v___x_862_);
lean_dec(v_i_876_);
v___y_866_ = v___x_880_;
goto v___jp_865_;
}
v___jp_881_:
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__4___redArg(v_valueMap_858_);
lean_dec_ref(v_valueMap_858_);
v___x_883_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3___redArg(v___x_882_, v_key_794_);
switch(lean_obj_tag(v___x_883_))
{
case 0:
{
lean_object* v_index_884_; lean_object* v_size_885_; lean_object* v___x_886_; 
v_index_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_index_884_);
lean_dec_ref_known(v___x_883_, 3);
v_size_885_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_size_885_);
v___x_886_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_882_, v_size_885_, v_index_884_, v_key_794_, v___x_862_);
lean_dec(v_index_884_);
v___y_866_ = v___x_886_;
goto v___jp_865_;
}
case 1:
{
lean_object* v_index_887_; 
v_index_887_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_index_887_);
lean_dec_ref_known(v___x_883_, 1);
v___y_875_ = v___x_882_;
v_i_876_ = v_index_887_;
goto v___jp_874_;
}
default: 
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = lean_unsigned_to_nat(0u);
v___x_889_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_882_, v___x_888_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v_index_890_; 
v_index_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_index_890_);
lean_dec_ref_known(v___x_889_, 1);
v___y_875_ = v___x_882_;
v_i_876_ = v_index_890_;
goto v___jp_874_;
}
else
{
lean_dec_ref_known(v_key_794_, 2);
v___y_866_ = v___x_882_;
goto v___jp_865_;
}
}
}
}
v___jp_891_:
{
lean_object* v_size_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v_size_894_ = lean_ctor_get(v___y_892_, 0);
v___x_895_ = lean_unsigned_to_nat(1u);
v___x_896_ = lean_nat_add(v_size_894_, v___x_895_);
v___x_897_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_892_, v___x_896_, v_i_893_, v_key_794_, v___x_862_);
lean_dec(v_i_893_);
v___y_866_ = v___x_897_;
goto v___jp_865_;
}
v___jp_898_:
{
lean_object* v___x_900_; 
v___x_900_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3___redArg(v___y_899_, v_key_794_);
switch(lean_obj_tag(v___x_900_))
{
case 0:
{
lean_object* v_index_901_; lean_object* v_size_902_; lean_object* v___x_903_; 
v_index_901_ = lean_ctor_get(v___x_900_, 0);
lean_inc(v_index_901_);
lean_dec_ref_known(v___x_900_, 3);
v_size_902_ = lean_ctor_get(v___y_899_, 0);
lean_inc(v_size_902_);
v___x_903_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_899_, v_size_902_, v_index_901_, v_key_794_, v___x_862_);
lean_dec(v_index_901_);
v___y_866_ = v___x_903_;
goto v___jp_865_;
}
case 1:
{
lean_object* v_index_904_; 
v_index_904_ = lean_ctor_get(v___x_900_, 0);
lean_inc(v_index_904_);
lean_dec_ref_known(v___x_900_, 1);
v___y_892_ = v___y_899_;
v_i_893_ = v_index_904_;
goto v___jp_891_;
}
default: 
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = lean_unsigned_to_nat(0u);
v___x_906_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_899_, v___x_905_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v_index_907_; 
v_index_907_ = lean_ctor_get(v___x_906_, 0);
lean_inc(v_index_907_);
lean_dec_ref_known(v___x_906_, 1);
v___y_892_ = v___y_899_;
v_i_893_ = v_index_907_;
goto v___jp_891_;
}
else
{
lean_dec_ref_known(v_key_794_, 2);
v___y_866_ = v___y_899_;
goto v___jp_865_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_794_, 2);
lean_dec_ref(v_value_782_);
lean_dec_ref(v_type_781_);
lean_dec(v_userName_780_);
return v___x_846_;
}
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec_ref_known(v_key_794_, 2);
lean_dec_ref(v_value_782_);
lean_dec_ref(v_type_781_);
lean_dec(v_userName_780_);
v_a_940_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_844_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_844_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl___boxed(lean_object* v_userName_948_, lean_object* v_type_949_, lean_object* v_value_950_, lean_object* v_nondep_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_){
_start:
{
uint8_t v_nondep_boxed_960_; lean_object* v_res_961_; 
v_nondep_boxed_960_ = lean_unbox(v_nondep_951_);
v_res_961_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl(v_userName_948_, v_type_949_, v_value_950_, v_nondep_boxed_960_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
lean_dec(v_a_952_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0(lean_object* v_00_u03b2_962_, lean_object* v_m_963_, lean_object* v_a_964_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0___redArg(v_m_963_, v_a_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0___boxed(lean_object* v_00_u03b2_966_, lean_object* v_m_967_, lean_object* v_a_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0(v_00_u03b2_966_, v_m_967_, v_a_968_);
lean_dec_ref(v_a_968_);
lean_dec_ref(v_m_967_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2(lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2___redArg(v___y_976_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2___boxed(lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2(v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v___y_979_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3(lean_object* v_00_u03b2_988_, lean_object* v_m_989_, lean_object* v_query_990_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3___redArg(v_m_989_, v_query_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3___boxed(lean_object* v_00_u03b2_992_, lean_object* v_m_993_, lean_object* v_query_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3(v_00_u03b2_992_, v_m_993_, v_query_994_);
lean_dec_ref(v_query_994_);
lean_dec_ref(v_m_993_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__4(lean_object* v_00_u03b2_996_, lean_object* v_m_997_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__4___redArg(v_m_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__4___boxed(lean_object* v_00_u03b2_999_, lean_object* v_m_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__4(v_00_u03b2_999_, v_m_1000_);
lean_dec_ref(v_m_1000_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0(lean_object* v_00_u03b2_1002_, lean_object* v_m_1003_, lean_object* v_query_1004_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0___redArg(v_m_1003_, v_query_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1006_, lean_object* v_m_1007_, lean_object* v_query_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0(v_00_u03b2_1006_, v_m_1007_, v_query_1008_);
lean_dec_ref(v_query_1008_);
lean_dec_ref(v_m_1007_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5(lean_object* v_00_u03b2_1010_, lean_object* v_m_1011_, lean_object* v_query_1012_, lean_object* v_x_1013_, lean_object* v_x_1014_, lean_object* v_x_1015_, lean_object* v_x_1016_){
_start:
{
lean_object* v___x_1017_; 
v___x_1017_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5___redArg(v_m_1011_, v_query_1012_, v_x_1013_, v_x_1014_, v_x_1015_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5___boxed(lean_object* v_00_u03b2_1018_, lean_object* v_m_1019_, lean_object* v_query_1020_, lean_object* v_x_1021_, lean_object* v_x_1022_, lean_object* v_x_1023_, lean_object* v_x_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5(v_00_u03b2_1018_, v_m_1019_, v_query_1020_, v_x_1021_, v_x_1022_, v_x_1023_, v_x_1024_);
lean_dec_ref(v_query_1020_);
lean_dec_ref(v_m_1019_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__4_spec__7(lean_object* v_00_u03b2_1026_, lean_object* v_init_1027_, lean_object* v_b_1028_){
_start:
{
lean_object* v___x_1029_; 
v___x_1029_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__4_spec__7___redArg(v_init_1027_, v_b_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__4_spec__7___boxed(lean_object* v_00_u03b2_1030_, lean_object* v_init_1031_, lean_object* v_b_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__4_spec__7(v_00_u03b2_1030_, v_init_1031_, v_b_1032_);
lean_dec_ref(v_b_1032_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__4_spec__7_spec__8(lean_object* v_00_u03b2_1034_, lean_object* v_b_1035_, lean_object* v_acc_1036_, lean_object* v_i_1037_){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__4_spec__7_spec__8___redArg(v_b_1035_, v_acc_1036_, v_i_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__4_spec__7_spec__8___boxed(lean_object* v_00_u03b2_1039_, lean_object* v_b_1040_, lean_object* v_acc_1041_, lean_object* v_i_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__4_spec__7_spec__8(v_00_u03b2_1039_, v_b_1040_, v_acc_1041_, v_i_1042_);
lean_dec_ref(v_b_1040_);
return v_res_1043_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1(lean_object* v_msg_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_2251__overap_1054_; lean_object* v___x_1055_; 
v___x_1053_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1___closed__0);
v___x_2251__overap_1054_ = lean_panic_fn_borrowed(v___x_1053_, v_msg_1045_);
lean_inc(v___y_1051_);
lean_inc_ref(v___y_1050_);
lean_inc(v___y_1049_);
lean_inc_ref(v___y_1048_);
lean_inc(v___y_1047_);
lean_inc_ref(v___y_1046_);
v___x_1055_ = lean_apply_7(v___x_2251__overap_1054_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, lean_box(0));
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1___boxed(lean_object* v_msg_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1(v_msg_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__2(lean_object* v_x_1065_, uint8_t v_bi_1066_, lean_object* v_t_1067_, lean_object* v_b_1068_, lean_object* v___y_1069_, uint8_t v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v___y_1074_; lean_object* v___y_1075_; 
if (v___y_1070_ == 0)
{
v___y_1074_ = v___y_1069_;
v___y_1075_ = v___y_1072_;
goto v___jp_1073_;
}
else
{
lean_object* v___x_1097_; 
v___x_1097_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_1067_, v___y_1070_, v___y_1071_, v___y_1072_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_a_1098_; lean_object* v___x_1099_; 
v_a_1098_ = lean_ctor_get(v___x_1097_, 1);
lean_inc(v_a_1098_);
lean_dec_ref_known(v___x_1097_, 2);
v___x_1099_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_1068_, v___y_1070_, v___y_1071_, v_a_1098_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v_a_1100_; 
v_a_1100_ = lean_ctor_get(v___x_1099_, 1);
lean_inc(v_a_1100_);
lean_dec_ref_known(v___x_1099_, 2);
v___y_1074_ = v___y_1069_;
v___y_1075_ = v_a_1100_;
goto v___jp_1073_;
}
else
{
lean_object* v_a_1101_; lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
lean_dec_ref(v___y_1069_);
lean_dec_ref(v_b_1068_);
lean_dec_ref(v_t_1067_);
lean_dec(v_x_1065_);
v_a_1101_ = lean_ctor_get(v___x_1099_, 0);
v_a_1102_ = lean_ctor_get(v___x_1099_, 1);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1104_ = v___x_1099_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_inc(v_a_1101_);
lean_dec(v___x_1099_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_a_1101_);
lean_ctor_set(v_reuseFailAlloc_1108_, 1, v_a_1102_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
else
{
lean_object* v_a_1110_; lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
lean_dec_ref(v___y_1069_);
lean_dec_ref(v_b_1068_);
lean_dec_ref(v_t_1067_);
lean_dec(v_x_1065_);
v_a_1110_ = lean_ctor_get(v___x_1097_, 0);
v_a_1111_ = lean_ctor_get(v___x_1097_, 1);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1097_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_inc(v_a_1110_);
lean_dec(v___x_1097_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1110_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
v___jp_1073_:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = l_Lean_Expr_lam___override(v_x_1065_, v_t_1067_, v_b_1068_, v_bi_1066_);
v___x_1077_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1076_, v___y_1075_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1087_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
v_a_1079_ = lean_ctor_get(v___x_1077_, 1);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1081_ = v___x_1077_;
v_isShared_1082_ = v_isSharedCheck_1087_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_inc(v_a_1078_);
lean_dec(v___x_1077_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1087_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1083_; lean_object* v___x_1085_; 
v___x_1083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1083_, 0, v_a_1078_);
lean_ctor_set(v___x_1083_, 1, v___y_1074_);
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 0, v___x_1083_);
v___x_1085_ = v___x_1081_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1083_);
lean_ctor_set(v_reuseFailAlloc_1086_, 1, v_a_1079_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
else
{
lean_object* v_a_1088_; lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
lean_dec_ref(v___y_1074_);
v_a_1088_ = lean_ctor_get(v___x_1077_, 0);
v_a_1089_ = lean_ctor_get(v___x_1077_, 1);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1091_ = v___x_1077_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_inc(v_a_1088_);
lean_dec(v___x_1077_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1088_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v_a_1089_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__2___boxed(lean_object* v_x_1119_, lean_object* v_bi_1120_, lean_object* v_t_1121_, lean_object* v_b_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
uint8_t v_bi_boxed_1127_; uint8_t v___y_25375__boxed_1128_; lean_object* v_res_1129_; 
v_bi_boxed_1127_ = lean_unbox(v_bi_1120_);
v___y_25375__boxed_1128_ = lean_unbox(v___y_1124_);
v_res_1129_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__2(v_x_1119_, v_bi_boxed_1127_, v_t_1121_, v_b_1122_, v___y_1123_, v___y_25375__boxed_1128_, v___y_1125_, v___y_1126_);
lean_dec_ref(v___y_1125_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__6(lean_object* v_structName_1130_, lean_object* v_idx_1131_, lean_object* v_struct_1132_, lean_object* v___y_1133_, uint8_t v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v___y_1138_; lean_object* v___y_1139_; 
if (v___y_1134_ == 0)
{
v___y_1138_ = v___y_1133_;
v___y_1139_ = v___y_1136_;
goto v___jp_1137_;
}
else
{
lean_object* v___x_1161_; 
v___x_1161_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_struct_1132_, v___y_1134_, v___y_1135_, v___y_1136_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_a_1162_; 
v_a_1162_ = lean_ctor_get(v___x_1161_, 1);
lean_inc(v_a_1162_);
lean_dec_ref_known(v___x_1161_, 2);
v___y_1138_ = v___y_1133_;
v___y_1139_ = v_a_1162_;
goto v___jp_1137_;
}
else
{
lean_object* v_a_1163_; lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1171_; 
lean_dec_ref(v___y_1133_);
lean_dec_ref(v_struct_1132_);
lean_dec(v_idx_1131_);
lean_dec(v_structName_1130_);
v_a_1163_ = lean_ctor_get(v___x_1161_, 0);
v_a_1164_ = lean_ctor_get(v___x_1161_, 1);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1166_ = v___x_1161_;
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_inc(v_a_1163_);
lean_dec(v___x_1161_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1169_; 
if (v_isShared_1167_ == 0)
{
v___x_1169_ = v___x_1166_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1163_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v_a_1164_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
v___jp_1137_:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = l_Lean_Expr_proj___override(v_structName_1130_, v_idx_1131_, v_struct_1132_);
v___x_1141_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1140_, v___y_1139_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_a_1142_; lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1151_; 
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
v_a_1143_ = lean_ctor_get(v___x_1141_, 1);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1145_ = v___x_1141_;
v_isShared_1146_ = v_isSharedCheck_1151_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_inc(v_a_1142_);
lean_dec(v___x_1141_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1151_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; lean_object* v___x_1149_; 
v___x_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1147_, 0, v_a_1142_);
lean_ctor_set(v___x_1147_, 1, v___y_1138_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v___x_1147_);
v___x_1149_ = v___x_1145_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v___x_1147_);
lean_ctor_set(v_reuseFailAlloc_1150_, 1, v_a_1143_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
else
{
lean_object* v_a_1152_; lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
lean_dec_ref(v___y_1138_);
v_a_1152_ = lean_ctor_get(v___x_1141_, 0);
v_a_1153_ = lean_ctor_get(v___x_1141_, 1);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v___x_1141_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_inc(v_a_1152_);
lean_dec(v___x_1141_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1156_ == 0)
{
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1152_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v_a_1153_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__6___boxed(lean_object* v_structName_1172_, lean_object* v_idx_1173_, lean_object* v_struct_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
uint8_t v___y_25481__boxed_1179_; lean_object* v_res_1180_; 
v___y_25481__boxed_1179_ = lean_unbox(v___y_1176_);
v_res_1180_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__6(v_structName_1172_, v_idx_1173_, v_struct_1174_, v___y_1175_, v___y_25481__boxed_1179_, v___y_1177_, v___y_1178_);
lean_dec_ref(v___y_1177_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__1(lean_object* v_f_1181_, lean_object* v_a_1182_, lean_object* v___y_1183_, uint8_t v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
lean_object* v___y_1188_; lean_object* v___y_1189_; 
if (v___y_1184_ == 0)
{
v___y_1188_ = v___y_1183_;
v___y_1189_ = v___y_1186_;
goto v___jp_1187_;
}
else
{
lean_object* v___x_1211_; 
v___x_1211_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_1181_, v___y_1184_, v___y_1185_, v___y_1186_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v_a_1212_; lean_object* v___x_1213_; 
v_a_1212_ = lean_ctor_get(v___x_1211_, 1);
lean_inc(v_a_1212_);
lean_dec_ref_known(v___x_1211_, 2);
v___x_1213_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_1182_, v___y_1184_, v___y_1185_, v_a_1212_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v_a_1214_; 
v_a_1214_ = lean_ctor_get(v___x_1213_, 1);
lean_inc(v_a_1214_);
lean_dec_ref_known(v___x_1213_, 2);
v___y_1188_ = v___y_1183_;
v___y_1189_ = v_a_1214_;
goto v___jp_1187_;
}
else
{
lean_object* v_a_1215_; lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1223_; 
lean_dec_ref(v___y_1183_);
lean_dec_ref(v_a_1182_);
lean_dec_ref(v_f_1181_);
v_a_1215_ = lean_ctor_get(v___x_1213_, 0);
v_a_1216_ = lean_ctor_get(v___x_1213_, 1);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1218_ = v___x_1213_;
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_inc(v_a_1215_);
lean_dec(v___x_1213_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_a_1215_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v_a_1216_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
}
else
{
lean_object* v_a_1224_; lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1232_; 
lean_dec_ref(v___y_1183_);
lean_dec_ref(v_a_1182_);
lean_dec_ref(v_f_1181_);
v_a_1224_ = lean_ctor_get(v___x_1211_, 0);
v_a_1225_ = lean_ctor_get(v___x_1211_, 1);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1227_ = v___x_1211_;
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_inc(v_a_1224_);
lean_dec(v___x_1211_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1230_; 
if (v_isShared_1228_ == 0)
{
v___x_1230_ = v___x_1227_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_a_1224_);
lean_ctor_set(v_reuseFailAlloc_1231_, 1, v_a_1225_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
}
v___jp_1187_:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1190_ = l_Lean_Expr_app___override(v_f_1181_, v_a_1182_);
v___x_1191_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1190_, v___y_1189_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1201_; 
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
v_a_1193_ = lean_ctor_get(v___x_1191_, 1);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1195_ = v___x_1191_;
v_isShared_1196_ = v_isSharedCheck_1201_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_inc(v_a_1192_);
lean_dec(v___x_1191_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1201_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1197_; lean_object* v___x_1199_; 
v___x_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1197_, 0, v_a_1192_);
lean_ctor_set(v___x_1197_, 1, v___y_1188_);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 0, v___x_1197_);
v___x_1199_ = v___x_1195_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1197_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v_a_1193_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
else
{
lean_object* v_a_1202_; lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
lean_dec_ref(v___y_1188_);
v_a_1202_ = lean_ctor_get(v___x_1191_, 0);
v_a_1203_ = lean_ctor_get(v___x_1191_, 1);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1205_ = v___x_1191_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_inc(v_a_1202_);
lean_dec(v___x_1191_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1202_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_a_1203_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__1___boxed(lean_object* v_f_1233_, lean_object* v_a_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
uint8_t v___y_25564__boxed_1239_; lean_object* v_res_1240_; 
v___y_25564__boxed_1239_ = lean_unbox(v___y_1236_);
v_res_1240_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__1(v_f_1233_, v_a_1234_, v___y_1235_, v___y_25564__boxed_1239_, v___y_1237_, v___y_1238_);
lean_dec_ref(v___y_1237_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4(lean_object* v_x_1241_, lean_object* v_t_1242_, lean_object* v_v_1243_, lean_object* v_b_1244_, uint8_t v_nondep_1245_, lean_object* v___y_1246_, uint8_t v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v___y_1251_; lean_object* v___y_1252_; 
if (v___y_1247_ == 0)
{
v___y_1251_ = v___y_1246_;
v___y_1252_ = v___y_1249_;
goto v___jp_1250_;
}
else
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_1242_, v___y_1247_, v___y_1248_, v___y_1249_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; lean_object* v___x_1276_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 1);
lean_inc(v_a_1275_);
lean_dec_ref_known(v___x_1274_, 2);
v___x_1276_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_v_1243_, v___y_1247_, v___y_1248_, v_a_1275_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; lean_object* v___x_1278_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 1);
lean_inc(v_a_1277_);
lean_dec_ref_known(v___x_1276_, 2);
v___x_1278_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_1244_, v___y_1247_, v___y_1248_, v_a_1277_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 1);
lean_inc(v_a_1279_);
lean_dec_ref_known(v___x_1278_, 2);
v___y_1251_ = v___y_1246_;
v___y_1252_ = v_a_1279_;
goto v___jp_1250_;
}
else
{
lean_object* v_a_1280_; lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
lean_dec_ref(v___y_1246_);
lean_dec_ref(v_b_1244_);
lean_dec_ref(v_v_1243_);
lean_dec_ref(v_t_1242_);
lean_dec(v_x_1241_);
v_a_1280_ = lean_ctor_get(v___x_1278_, 0);
v_a_1281_ = lean_ctor_get(v___x_1278_, 1);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v___x_1278_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_inc(v_a_1280_);
lean_dec(v___x_1278_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1280_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v_a_1281_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
else
{
lean_object* v_a_1289_; lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
lean_dec_ref(v___y_1246_);
lean_dec_ref(v_b_1244_);
lean_dec_ref(v_v_1243_);
lean_dec_ref(v_t_1242_);
lean_dec(v_x_1241_);
v_a_1289_ = lean_ctor_get(v___x_1276_, 0);
v_a_1290_ = lean_ctor_get(v___x_1276_, 1);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1276_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_inc(v_a_1289_);
lean_dec(v___x_1276_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1289_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v_a_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
else
{
lean_object* v_a_1298_; lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1306_; 
lean_dec_ref(v___y_1246_);
lean_dec_ref(v_b_1244_);
lean_dec_ref(v_v_1243_);
lean_dec_ref(v_t_1242_);
lean_dec(v_x_1241_);
v_a_1298_ = lean_ctor_get(v___x_1274_, 0);
v_a_1299_ = lean_ctor_get(v___x_1274_, 1);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1301_ = v___x_1274_;
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_inc(v_a_1298_);
lean_dec(v___x_1274_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1304_; 
if (v_isShared_1302_ == 0)
{
v___x_1304_ = v___x_1301_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_a_1298_);
lean_ctor_set(v_reuseFailAlloc_1305_, 1, v_a_1299_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
v___jp_1250_:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1253_ = l_Lean_Expr_letE___override(v_x_1241_, v_t_1242_, v_v_1243_, v_b_1244_, v_nondep_1245_);
v___x_1254_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1253_, v___y_1252_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1255_; lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1264_; 
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
v_a_1256_ = lean_ctor_get(v___x_1254_, 1);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1258_ = v___x_1254_;
v_isShared_1259_ = v_isSharedCheck_1264_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_inc(v_a_1255_);
lean_dec(v___x_1254_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1264_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1260_; lean_object* v___x_1262_; 
v___x_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1260_, 0, v_a_1255_);
lean_ctor_set(v___x_1260_, 1, v___y_1251_);
if (v_isShared_1259_ == 0)
{
lean_ctor_set(v___x_1258_, 0, v___x_1260_);
v___x_1262_ = v___x_1258_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1260_);
lean_ctor_set(v_reuseFailAlloc_1263_, 1, v_a_1256_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
else
{
lean_object* v_a_1265_; lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec_ref(v___y_1251_);
v_a_1265_ = lean_ctor_get(v___x_1254_, 0);
v_a_1266_ = lean_ctor_get(v___x_1254_, 1);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1254_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_inc(v_a_1265_);
lean_dec(v___x_1254_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1265_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4___boxed(lean_object* v_x_1307_, lean_object* v_t_1308_, lean_object* v_v_1309_, lean_object* v_b_1310_, lean_object* v_nondep_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
uint8_t v_nondep_boxed_1316_; uint8_t v___y_25670__boxed_1317_; lean_object* v_res_1318_; 
v_nondep_boxed_1316_ = lean_unbox(v_nondep_1311_);
v___y_25670__boxed_1317_ = lean_unbox(v___y_1313_);
v_res_1318_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4(v_x_1307_, v_t_1308_, v_v_1309_, v_b_1310_, v_nondep_boxed_1316_, v___y_1312_, v___y_25670__boxed_1317_, v___y_1314_, v___y_1315_);
lean_dec_ref(v___y_1314_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7(lean_object* v_msg_1326_, lean_object* v___y_1327_, uint8_t v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v___f_1331_; lean_object* v___f_1332_; lean_object* v___f_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___f_1343_; lean_object* v___f_1344_; lean_object* v___f_1345_; lean_object* v___f_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_24777__overap_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___f_1331_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__0));
v___f_1332_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__1));
v___f_1333_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__2));
v___x_1334_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__3));
v___x_1335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
lean_ctor_set(v___x_1335_, 1, v___f_1331_);
v___x_1336_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__4));
v___x_1337_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__5));
v___x_1338_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1335_);
lean_ctor_set(v___x_1338_, 1, v___x_1336_);
lean_ctor_set(v___x_1338_, 2, v___f_1332_);
lean_ctor_set(v___x_1338_, 3, v___f_1333_);
lean_ctor_set(v___x_1338_, 4, v___x_1337_);
v___x_1339_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__6));
v___x_1340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1338_);
lean_ctor_set(v___x_1340_, 1, v___x_1339_);
v___x_1341_ = l_ReaderT_instMonad___redArg(v___x_1340_);
v___x_1342_ = l_ReaderT_instMonad___redArg(v___x_1341_);
lean_inc_ref_n(v___x_1342_, 6);
v___f_1343_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1343_, 0, v___x_1342_);
v___f_1344_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1344_, 0, v___x_1342_);
v___f_1345_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_1345_, 0, v___x_1342_);
v___f_1346_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_1346_, 0, v___x_1342_);
v___x_1347_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_1347_, 0, lean_box(0));
lean_closure_set(v___x_1347_, 1, lean_box(0));
lean_closure_set(v___x_1347_, 2, v___x_1342_);
v___x_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1347_);
lean_ctor_set(v___x_1348_, 1, v___f_1343_);
v___x_1349_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_1349_, 0, lean_box(0));
lean_closure_set(v___x_1349_, 1, lean_box(0));
lean_closure_set(v___x_1349_, 2, v___x_1342_);
v___x_1350_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1348_);
lean_ctor_set(v___x_1350_, 1, v___x_1349_);
lean_ctor_set(v___x_1350_, 2, v___f_1344_);
lean_ctor_set(v___x_1350_, 3, v___f_1345_);
lean_ctor_set(v___x_1350_, 4, v___f_1346_);
v___x_1351_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_1351_, 0, lean_box(0));
lean_closure_set(v___x_1351_, 1, lean_box(0));
lean_closure_set(v___x_1351_, 2, v___x_1342_);
v___x_1352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1350_);
lean_ctor_set(v___x_1352_, 1, v___x_1351_);
v___x_1353_ = l_Lean_instInhabitedExpr;
v___x_1354_ = l_instInhabitedOfMonad___redArg(v___x_1352_, v___x_1353_);
v___x_24777__overap_1355_ = lean_panic_fn_borrowed(v___x_1354_, v_msg_1326_);
lean_dec(v___x_1354_);
v___x_1356_ = lean_box(v___y_1328_);
lean_inc_ref(v___y_1329_);
v___x_1357_ = lean_apply_4(v___x_24777__overap_1355_, v___y_1327_, v___x_1356_, v___y_1329_, v___y_1330_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___boxed(lean_object* v_msg_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
uint8_t v___y_25813__boxed_1363_; lean_object* v_res_1364_; 
v___y_25813__boxed_1363_ = lean_unbox(v___y_1360_);
v_res_1364_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7(v_msg_1358_, v___y_1359_, v___y_25813__boxed_1363_, v___y_1361_, v___y_1362_);
lean_dec_ref(v___y_1361_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__5(lean_object* v_d_1365_, lean_object* v_e_1366_, lean_object* v___y_1367_, uint8_t v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v___y_1372_; lean_object* v___y_1373_; 
if (v___y_1368_ == 0)
{
v___y_1372_ = v___y_1367_;
v___y_1373_ = v___y_1370_;
goto v___jp_1371_;
}
else
{
lean_object* v___x_1395_; 
v___x_1395_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_1366_, v___y_1368_, v___y_1369_, v___y_1370_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v_a_1396_; 
v_a_1396_ = lean_ctor_get(v___x_1395_, 1);
lean_inc(v_a_1396_);
lean_dec_ref_known(v___x_1395_, 2);
v___y_1372_ = v___y_1367_;
v___y_1373_ = v_a_1396_;
goto v___jp_1371_;
}
else
{
lean_object* v_a_1397_; lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1405_; 
lean_dec_ref(v___y_1367_);
lean_dec_ref(v_e_1366_);
lean_dec(v_d_1365_);
v_a_1397_ = lean_ctor_get(v___x_1395_, 0);
v_a_1398_ = lean_ctor_get(v___x_1395_, 1);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1400_ = v___x_1395_;
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_inc(v_a_1397_);
lean_dec(v___x_1395_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1403_; 
if (v_isShared_1401_ == 0)
{
v___x_1403_ = v___x_1400_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_a_1397_);
lean_ctor_set(v_reuseFailAlloc_1404_, 1, v_a_1398_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
}
v___jp_1371_:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1374_ = l_Lean_Expr_mdata___override(v_d_1365_, v_e_1366_);
v___x_1375_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1374_, v___y_1373_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1385_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
v_a_1377_ = lean_ctor_get(v___x_1375_, 1);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1379_ = v___x_1375_;
v_isShared_1380_ = v_isSharedCheck_1385_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_inc(v_a_1376_);
lean_dec(v___x_1375_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1385_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1381_; lean_object* v___x_1383_; 
v___x_1381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1381_, 0, v_a_1376_);
lean_ctor_set(v___x_1381_, 1, v___y_1372_);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 0, v___x_1381_);
v___x_1383_ = v___x_1379_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1381_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v_a_1377_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
else
{
lean_object* v_a_1386_; lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
lean_dec_ref(v___y_1372_);
v_a_1386_ = lean_ctor_get(v___x_1375_, 0);
v_a_1387_ = lean_ctor_get(v___x_1375_, 1);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1389_ = v___x_1375_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_inc(v_a_1386_);
lean_dec(v___x_1375_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_a_1386_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v_a_1387_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__5___boxed(lean_object* v_d_1406_, lean_object* v_e_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
uint8_t v___y_25884__boxed_1412_; lean_object* v_res_1413_; 
v___y_25884__boxed_1412_ = lean_unbox(v___y_1409_);
v_res_1413_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__5(v_d_1406_, v_e_1407_, v___y_1408_, v___y_25884__boxed_1412_, v___y_1410_, v___y_1411_);
lean_dec_ref(v___y_1410_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__3(lean_object* v_x_1414_, uint8_t v_bi_1415_, lean_object* v_t_1416_, lean_object* v_b_1417_, lean_object* v___y_1418_, uint8_t v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v___y_1423_; lean_object* v___y_1424_; 
if (v___y_1419_ == 0)
{
v___y_1423_ = v___y_1418_;
v___y_1424_ = v___y_1421_;
goto v___jp_1422_;
}
else
{
lean_object* v___x_1446_; 
v___x_1446_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_1416_, v___y_1419_, v___y_1420_, v___y_1421_);
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_object* v_a_1447_; lean_object* v___x_1448_; 
v_a_1447_ = lean_ctor_get(v___x_1446_, 1);
lean_inc(v_a_1447_);
lean_dec_ref_known(v___x_1446_, 2);
v___x_1448_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_1417_, v___y_1419_, v___y_1420_, v_a_1447_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_a_1449_; 
v_a_1449_ = lean_ctor_get(v___x_1448_, 1);
lean_inc(v_a_1449_);
lean_dec_ref_known(v___x_1448_, 2);
v___y_1423_ = v___y_1418_;
v___y_1424_ = v_a_1449_;
goto v___jp_1422_;
}
else
{
lean_object* v_a_1450_; lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
lean_dec_ref(v___y_1418_);
lean_dec_ref(v_b_1417_);
lean_dec_ref(v_t_1416_);
lean_dec(v_x_1414_);
v_a_1450_ = lean_ctor_get(v___x_1448_, 0);
v_a_1451_ = lean_ctor_get(v___x_1448_, 1);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1453_ = v___x_1448_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_inc(v_a_1450_);
lean_dec(v___x_1448_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_a_1450_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_a_1451_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
else
{
lean_object* v_a_1459_; lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
lean_dec_ref(v___y_1418_);
lean_dec_ref(v_b_1417_);
lean_dec_ref(v_t_1416_);
lean_dec(v_x_1414_);
v_a_1459_ = lean_ctor_get(v___x_1446_, 0);
v_a_1460_ = lean_ctor_get(v___x_1446_, 1);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1446_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_inc(v_a_1459_);
lean_dec(v___x_1446_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1459_);
lean_ctor_set(v_reuseFailAlloc_1466_, 1, v_a_1460_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
v___jp_1422_:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1425_ = l_Lean_Expr_forallE___override(v_x_1414_, v_t_1416_, v_b_1417_, v_bi_1415_);
v___x_1426_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1425_, v___y_1424_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1436_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
v_a_1428_ = lean_ctor_get(v___x_1426_, 1);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1430_ = v___x_1426_;
v_isShared_1431_ = v_isSharedCheck_1436_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_inc(v_a_1427_);
lean_dec(v___x_1426_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1436_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; lean_object* v___x_1434_; 
v___x_1432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1432_, 0, v_a_1427_);
lean_ctor_set(v___x_1432_, 1, v___y_1423_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v___x_1432_);
v___x_1434_ = v___x_1430_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1432_);
lean_ctor_set(v_reuseFailAlloc_1435_, 1, v_a_1428_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
else
{
lean_object* v_a_1437_; lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
lean_dec_ref(v___y_1423_);
v_a_1437_ = lean_ctor_get(v___x_1426_, 0);
v_a_1438_ = lean_ctor_get(v___x_1426_, 1);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___x_1426_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_inc(v_a_1437_);
lean_dec(v___x_1426_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1437_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v_a_1438_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__3___boxed(lean_object* v_x_1468_, lean_object* v_bi_1469_, lean_object* v_t_1470_, lean_object* v_b_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
uint8_t v_bi_boxed_1476_; uint8_t v___y_25967__boxed_1477_; lean_object* v_res_1478_; 
v_bi_boxed_1476_ = lean_unbox(v_bi_1469_);
v___y_25967__boxed_1477_ = lean_unbox(v___y_1473_);
v_res_1478_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__3(v_x_1468_, v_bi_boxed_1476_, v_t_1470_, v_b_1471_, v___y_1472_, v___y_25967__boxed_1477_, v___y_1474_, v___y_1475_);
lean_dec_ref(v___y_1474_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10_spec__11_spec__12___redArg(lean_object* v_m_1479_, lean_object* v_query_1480_, lean_object* v_x_1481_, lean_object* v_x_1482_, lean_object* v_x_1483_){
_start:
{
lean_object* v_zero_1484_; uint8_t v_isZero_1485_; 
v_zero_1484_ = lean_unsigned_to_nat(0u);
v_isZero_1485_ = lean_nat_dec_eq(v_x_1482_, v_zero_1484_);
if (v_isZero_1485_ == 1)
{
lean_dec(v_x_1483_);
lean_dec(v_x_1482_);
if (lean_obj_tag(v_x_1481_) == 0)
{
lean_object* v___x_1486_; 
v___x_1486_ = lean_box(2);
return v___x_1486_;
}
else
{
lean_object* v_val_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
v_val_1487_ = lean_ctor_get(v_x_1481_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v_x_1481_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v_x_1481_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_val_1487_);
lean_dec(v_x_1481_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_val_1487_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
else
{
lean_object* v_keyArray_1495_; lean_object* v_valueArray_1496_; lean_object* v___x_1497_; uint8_t v_isSome_1498_; 
v_keyArray_1495_ = lean_ctor_get(v_m_1479_, 1);
v_valueArray_1496_ = lean_ctor_get(v_m_1479_, 2);
v___x_1497_ = lean_array_fget_borrowed(v_keyArray_1495_, v_x_1483_);
v_isSome_1498_ = lean_noption_is_some(v___x_1497_);
if (v_isSome_1498_ == 0)
{
lean_dec(v_x_1482_);
if (lean_obj_tag(v_x_1481_) == 0)
{
lean_object* v___x_1499_; 
v___x_1499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1499_, 0, v_x_1483_);
return v___x_1499_;
}
else
{
lean_object* v_val_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
lean_dec(v_x_1483_);
v_val_1500_ = lean_ctor_get(v_x_1481_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v_x_1481_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v_x_1481_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_val_1500_);
lean_dec(v_x_1481_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_val_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
else
{
lean_object* v_one_1508_; lean_object* v_n_1509_; lean_object* v___y_1511_; 
v_one_1508_ = lean_unsigned_to_nat(1u);
v_n_1509_ = lean_nat_sub(v_x_1482_, v_one_1508_);
lean_dec(v_x_1482_);
if (v_isSome_1498_ == 0)
{
goto v___jp_1517_;
}
else
{
lean_object* v___x_1519_; uint8_t v_isSome_1520_; 
v___x_1519_ = lean_array_fget_borrowed(v_valueArray_1496_, v_x_1483_);
v_isSome_1520_ = lean_noption_is_some(v___x_1519_);
if (v_isSome_1520_ == 0)
{
goto v___jp_1517_;
}
else
{
lean_object* v_val_1521_; lean_object* v_fst_1522_; lean_object* v_snd_1523_; lean_object* v_fst_1524_; lean_object* v_snd_1525_; lean_object* v_val_1526_; uint8_t v___y_1528_; size_t v___x_1535_; size_t v___x_1536_; uint8_t v___x_1537_; 
lean_inc(v___x_1497_);
v_val_1521_ = lean_noption_get(v___x_1497_);
v_fst_1522_ = lean_ctor_get(v_val_1521_, 0);
lean_inc(v_fst_1522_);
v_snd_1523_ = lean_ctor_get(v_val_1521_, 1);
lean_inc(v_snd_1523_);
v_fst_1524_ = lean_ctor_get(v_query_1480_, 0);
v_snd_1525_ = lean_ctor_get(v_query_1480_, 1);
lean_inc(v___x_1519_);
v_val_1526_ = lean_noption_get(v___x_1519_);
v___x_1535_ = lean_ptr_addr(v_fst_1522_);
lean_dec(v_fst_1522_);
v___x_1536_ = lean_ptr_addr(v_fst_1524_);
v___x_1537_ = lean_usize_dec_eq(v___x_1535_, v___x_1536_);
if (v___x_1537_ == 0)
{
lean_dec(v_snd_1523_);
v___y_1528_ = v___x_1537_;
goto v___jp_1527_;
}
else
{
uint8_t v___x_1538_; 
v___x_1538_ = lean_nat_dec_eq(v_snd_1523_, v_snd_1525_);
lean_dec(v_snd_1523_);
v___y_1528_ = v___x_1538_;
goto v___jp_1527_;
}
v___jp_1527_:
{
if (v___y_1528_ == 0)
{
lean_object* v___x_1529_; lean_object* v___x_1530_; uint8_t v___x_1531_; 
lean_dec(v_val_1526_);
lean_dec(v_val_1521_);
v___x_1529_ = lean_array_get_size(v_keyArray_1495_);
v___x_1530_ = lean_nat_add(v_x_1483_, v_one_1508_);
lean_dec(v_x_1483_);
v___x_1531_ = lean_nat_dec_lt(v___x_1530_, v___x_1529_);
if (v___x_1531_ == 0)
{
lean_dec(v___x_1530_);
v_x_1482_ = v_n_1509_;
v_x_1483_ = v_zero_1484_;
goto _start;
}
else
{
v_x_1482_ = v_n_1509_;
v_x_1483_ = v___x_1530_;
goto _start;
}
}
else
{
lean_object* v___x_1534_; 
lean_dec(v_n_1509_);
lean_dec(v_x_1481_);
v___x_1534_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1534_, 0, v_x_1483_);
lean_ctor_set(v___x_1534_, 1, v_val_1521_);
lean_ctor_set(v___x_1534_, 2, v_val_1526_);
return v___x_1534_;
}
}
}
}
v___jp_1510_:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; uint8_t v___x_1514_; 
v___x_1512_ = lean_array_get_size(v_keyArray_1495_);
v___x_1513_ = lean_nat_add(v_x_1483_, v_one_1508_);
lean_dec(v_x_1483_);
v___x_1514_ = lean_nat_dec_lt(v___x_1513_, v___x_1512_);
if (v___x_1514_ == 0)
{
lean_dec(v___x_1513_);
v_x_1481_ = v___y_1511_;
v_x_1482_ = v_n_1509_;
v_x_1483_ = v_zero_1484_;
goto _start;
}
else
{
v_x_1481_ = v___y_1511_;
v_x_1482_ = v_n_1509_;
v_x_1483_ = v___x_1513_;
goto _start;
}
}
v___jp_1517_:
{
if (lean_obj_tag(v_x_1481_) == 0)
{
lean_object* v___x_1518_; 
lean_inc(v_x_1483_);
v___x_1518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1518_, 0, v_x_1483_);
v___y_1511_ = v___x_1518_;
goto v___jp_1510_;
}
else
{
v___y_1511_ = v_x_1481_;
goto v___jp_1510_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10_spec__11_spec__12___redArg___boxed(lean_object* v_m_1539_, lean_object* v_query_1540_, lean_object* v_x_1541_, lean_object* v_x_1542_, lean_object* v_x_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10_spec__11_spec__12___redArg(v_m_1539_, v_query_1540_, v_x_1541_, v_x_1542_, v_x_1543_);
lean_dec_ref(v_query_1540_);
lean_dec_ref(v_m_1539_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10_spec__11___redArg(lean_object* v_m_1545_, lean_object* v_query_1546_){
_start:
{
lean_object* v_keyArray_1547_; lean_object* v_fst_1548_; lean_object* v_snd_1549_; lean_object* v___x_1550_; size_t v___x_1551_; size_t v___x_1552_; size_t v___x_1553_; uint64_t v___x_1554_; uint64_t v___x_1555_; uint64_t v___x_1556_; uint64_t v___x_1557_; uint64_t v___x_1558_; uint64_t v_fold_1559_; uint64_t v___x_1560_; uint64_t v___x_1561_; uint64_t v___x_1562_; size_t v___x_1563_; size_t v___x_1564_; size_t v___x_1565_; size_t v___x_1566_; size_t v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v_keyArray_1547_ = lean_ctor_get(v_m_1545_, 1);
v_fst_1548_ = lean_ctor_get(v_query_1546_, 0);
v_snd_1549_ = lean_ctor_get(v_query_1546_, 1);
v___x_1550_ = lean_array_get_size(v_keyArray_1547_);
v___x_1551_ = lean_ptr_addr(v_fst_1548_);
v___x_1552_ = ((size_t)3ULL);
v___x_1553_ = lean_usize_shift_right(v___x_1551_, v___x_1552_);
v___x_1554_ = lean_usize_to_uint64(v___x_1553_);
v___x_1555_ = lean_uint64_of_nat(v_snd_1549_);
v___x_1556_ = lean_uint64_mix_hash(v___x_1554_, v___x_1555_);
v___x_1557_ = 32ULL;
v___x_1558_ = lean_uint64_shift_right(v___x_1556_, v___x_1557_);
v_fold_1559_ = lean_uint64_xor(v___x_1556_, v___x_1558_);
v___x_1560_ = 16ULL;
v___x_1561_ = lean_uint64_shift_right(v_fold_1559_, v___x_1560_);
v___x_1562_ = lean_uint64_xor(v_fold_1559_, v___x_1561_);
v___x_1563_ = lean_uint64_to_usize(v___x_1562_);
v___x_1564_ = lean_usize_of_nat(v___x_1550_);
v___x_1565_ = ((size_t)1ULL);
v___x_1566_ = lean_usize_sub(v___x_1564_, v___x_1565_);
v___x_1567_ = lean_usize_land(v___x_1563_, v___x_1566_);
v___x_1568_ = lean_usize_to_nat(v___x_1567_);
v___x_1569_ = lean_box(0);
v___x_1570_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10_spec__11_spec__12___redArg(v_m_1545_, v_query_1546_, v___x_1569_, v___x_1550_, v___x_1568_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10_spec__11___redArg___boxed(lean_object* v_m_1571_, lean_object* v_query_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10_spec__11___redArg(v_m_1571_, v_query_1572_);
lean_dec_ref(v_query_1572_);
lean_dec_ref(v_m_1571_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10___redArg(lean_object* v_m_1574_, lean_object* v_query_1575_){
_start:
{
lean_object* v___x_1576_; 
v___x_1576_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10_spec__11___redArg(v_m_1574_, v_query_1575_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v_index_1577_; lean_object* v_key_1578_; lean_object* v_value_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
v_index_1577_ = lean_ctor_get(v___x_1576_, 0);
v_key_1578_ = lean_ctor_get(v___x_1576_, 1);
v_value_1579_ = lean_ctor_get(v___x_1576_, 2);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1581_ = v___x_1576_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_value_1579_);
lean_inc(v_key_1578_);
lean_inc(v_index_1577_);
lean_dec(v___x_1576_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1584_; 
if (v_isShared_1582_ == 0)
{
v___x_1584_ = v___x_1581_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_index_1577_);
lean_ctor_set(v_reuseFailAlloc_1585_, 1, v_key_1578_);
lean_ctor_set(v_reuseFailAlloc_1585_, 2, v_value_1579_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
else
{
lean_object* v___x_1587_; 
lean_dec(v___x_1576_);
v___x_1587_ = lean_box(1);
return v___x_1587_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10___redArg___boxed(lean_object* v_m_1588_, lean_object* v_query_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10___redArg(v_m_1588_, v_query_1589_);
lean_dec_ref(v_query_1589_);
lean_dec_ref(v_m_1588_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2___redArg(lean_object* v_m_1591_, lean_object* v_a_1592_){
_start:
{
lean_object* v___x_1593_; 
v___x_1593_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10___redArg(v_m_1591_, v_a_1592_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v_value_1594_; lean_object* v___x_1595_; 
v_value_1594_ = lean_ctor_get(v___x_1593_, 2);
lean_inc(v_value_1594_);
lean_dec_ref_known(v___x_1593_, 3);
v___x_1595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1595_, 0, v_value_1594_);
return v___x_1595_;
}
else
{
lean_object* v___x_1596_; 
v___x_1596_ = lean_box(0);
return v___x_1596_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_m_1597_, lean_object* v_a_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2___redArg(v_m_1597_, v_a_1598_);
lean_dec_ref(v_a_1598_);
lean_dec_ref(v_m_1597_);
return v_res_1599_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1603_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__2));
v___x_1604_ = lean_unsigned_to_nat(67u);
v___x_1605_ = lean_unsigned_to_nat(35u);
v___x_1606_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__1));
v___x_1607_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__0));
v___x_1608_ = l_mkPanicMessageWithDecl(v___x_1607_, v___x_1606_, v___x_1605_, v___x_1604_, v___x_1603_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0(lean_object* v_n_1609_, lean_object* v_xs_1610_, lean_object* v_e_1611_, lean_object* v_offset_1612_, lean_object* v_a_1613_, uint8_t v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_){
_start:
{
switch(lean_obj_tag(v_e_1611_))
{
case 5:
{
lean_object* v_fn_1617_; lean_object* v_arg_1618_; lean_object* v___x_1619_; 
v_fn_1617_ = lean_ctor_get(v_e_1611_, 0);
v_arg_1618_ = lean_ctor_get(v_e_1611_, 1);
lean_inc(v_offset_1612_);
lean_inc_ref(v_fn_1617_);
v___x_1619_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1609_, v_xs_1610_, v_fn_1617_, v_offset_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_a_1620_; lean_object* v_a_1621_; lean_object* v_fst_1622_; lean_object* v_snd_1623_; lean_object* v___x_1624_; 
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
lean_inc(v_a_1620_);
v_a_1621_ = lean_ctor_get(v___x_1619_, 1);
lean_inc(v_a_1621_);
lean_dec_ref_known(v___x_1619_, 2);
v_fst_1622_ = lean_ctor_get(v_a_1620_, 0);
lean_inc(v_fst_1622_);
v_snd_1623_ = lean_ctor_get(v_a_1620_, 1);
lean_inc(v_snd_1623_);
lean_dec(v_a_1620_);
lean_inc_ref(v_arg_1618_);
v___x_1624_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1609_, v_xs_1610_, v_arg_1618_, v_offset_1612_, v_snd_1623_, v_a_1614_, v_a_1615_, v_a_1621_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_a_1625_; lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1651_; 
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
v_a_1626_ = lean_ctor_get(v___x_1624_, 1);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1628_ = v___x_1624_;
v_isShared_1629_ = v_isSharedCheck_1651_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_inc(v_a_1625_);
lean_dec(v___x_1624_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1651_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v_fst_1630_; lean_object* v_snd_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1650_; 
v_fst_1630_ = lean_ctor_get(v_a_1625_, 0);
v_snd_1631_ = lean_ctor_get(v_a_1625_, 1);
v_isSharedCheck_1650_ = !lean_is_exclusive(v_a_1625_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1633_ = v_a_1625_;
v_isShared_1634_ = v_isSharedCheck_1650_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_snd_1631_);
lean_inc(v_fst_1630_);
lean_dec(v_a_1625_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1650_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
uint8_t v___y_1636_; size_t v___x_1644_; size_t v___x_1645_; uint8_t v___x_1646_; 
v___x_1644_ = lean_ptr_addr(v_fn_1617_);
v___x_1645_ = lean_ptr_addr(v_fst_1622_);
v___x_1646_ = lean_usize_dec_eq(v___x_1644_, v___x_1645_);
if (v___x_1646_ == 0)
{
v___y_1636_ = v___x_1646_;
goto v___jp_1635_;
}
else
{
size_t v___x_1647_; size_t v___x_1648_; uint8_t v___x_1649_; 
v___x_1647_ = lean_ptr_addr(v_arg_1618_);
v___x_1648_ = lean_ptr_addr(v_fst_1630_);
v___x_1649_ = lean_usize_dec_eq(v___x_1647_, v___x_1648_);
v___y_1636_ = v___x_1649_;
goto v___jp_1635_;
}
v___jp_1635_:
{
if (v___y_1636_ == 0)
{
lean_object* v___x_1637_; 
lean_del_object(v___x_1633_);
lean_del_object(v___x_1628_);
lean_dec_ref_known(v_e_1611_, 2);
v___x_1637_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__1(v_fst_1622_, v_fst_1630_, v_snd_1631_, v_a_1614_, v_a_1615_, v_a_1626_);
return v___x_1637_;
}
else
{
lean_object* v___x_1639_; 
lean_dec(v_fst_1630_);
lean_dec(v_fst_1622_);
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 0, v_e_1611_);
v___x_1639_ = v___x_1633_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_e_1611_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v_snd_1631_);
v___x_1639_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
lean_object* v___x_1641_; 
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 0, v___x_1639_);
v___x_1641_ = v___x_1628_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1639_);
lean_ctor_set(v_reuseFailAlloc_1642_, 1, v_a_1626_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1622_);
lean_dec_ref_known(v_e_1611_, 2);
return v___x_1624_;
}
}
else
{
lean_dec_ref_known(v_e_1611_, 2);
lean_dec(v_offset_1612_);
return v___x_1619_;
}
}
case 6:
{
lean_object* v_binderName_1652_; lean_object* v_binderType_1653_; lean_object* v_body_1654_; uint8_t v_binderInfo_1655_; lean_object* v___x_1656_; 
v_binderName_1652_ = lean_ctor_get(v_e_1611_, 0);
v_binderType_1653_ = lean_ctor_get(v_e_1611_, 1);
v_body_1654_ = lean_ctor_get(v_e_1611_, 2);
v_binderInfo_1655_ = lean_ctor_get_uint8(v_e_1611_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1612_);
lean_inc_ref(v_binderType_1653_);
v___x_1656_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1609_, v_xs_1610_, v_binderType_1653_, v_offset_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_a_1657_; lean_object* v_a_1658_; lean_object* v_fst_1659_; lean_object* v_snd_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_a_1657_);
v_a_1658_ = lean_ctor_get(v___x_1656_, 1);
lean_inc(v_a_1658_);
lean_dec_ref_known(v___x_1656_, 2);
v_fst_1659_ = lean_ctor_get(v_a_1657_, 0);
lean_inc(v_fst_1659_);
v_snd_1660_ = lean_ctor_get(v_a_1657_, 1);
lean_inc(v_snd_1660_);
lean_dec(v_a_1657_);
v___x_1661_ = lean_unsigned_to_nat(1u);
v___x_1662_ = lean_nat_add(v_offset_1612_, v___x_1661_);
lean_dec(v_offset_1612_);
lean_inc_ref(v_body_1654_);
v___x_1663_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1609_, v_xs_1610_, v_body_1654_, v___x_1662_, v_snd_1660_, v_a_1614_, v_a_1615_, v_a_1658_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v_a_1664_; lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1690_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
v_a_1665_ = lean_ctor_get(v___x_1663_, 1);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1667_ = v___x_1663_;
v_isShared_1668_ = v_isSharedCheck_1690_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_inc(v_a_1664_);
lean_dec(v___x_1663_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1690_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v_fst_1669_; lean_object* v_snd_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1689_; 
v_fst_1669_ = lean_ctor_get(v_a_1664_, 0);
v_snd_1670_ = lean_ctor_get(v_a_1664_, 1);
v_isSharedCheck_1689_ = !lean_is_exclusive(v_a_1664_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1672_ = v_a_1664_;
v_isShared_1673_ = v_isSharedCheck_1689_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_snd_1670_);
lean_inc(v_fst_1669_);
lean_dec(v_a_1664_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1689_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
uint8_t v___y_1675_; size_t v___x_1683_; size_t v___x_1684_; uint8_t v___x_1685_; 
v___x_1683_ = lean_ptr_addr(v_binderType_1653_);
v___x_1684_ = lean_ptr_addr(v_fst_1659_);
v___x_1685_ = lean_usize_dec_eq(v___x_1683_, v___x_1684_);
if (v___x_1685_ == 0)
{
v___y_1675_ = v___x_1685_;
goto v___jp_1674_;
}
else
{
size_t v___x_1686_; size_t v___x_1687_; uint8_t v___x_1688_; 
v___x_1686_ = lean_ptr_addr(v_body_1654_);
v___x_1687_ = lean_ptr_addr(v_fst_1669_);
v___x_1688_ = lean_usize_dec_eq(v___x_1686_, v___x_1687_);
v___y_1675_ = v___x_1688_;
goto v___jp_1674_;
}
v___jp_1674_:
{
if (v___y_1675_ == 0)
{
lean_object* v___x_1676_; 
lean_inc(v_binderName_1652_);
lean_del_object(v___x_1672_);
lean_del_object(v___x_1667_);
lean_dec_ref_known(v_e_1611_, 3);
v___x_1676_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__2(v_binderName_1652_, v_binderInfo_1655_, v_fst_1659_, v_fst_1669_, v_snd_1670_, v_a_1614_, v_a_1615_, v_a_1665_);
return v___x_1676_;
}
else
{
lean_object* v___x_1678_; 
lean_dec(v_fst_1669_);
lean_dec(v_fst_1659_);
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 0, v_e_1611_);
v___x_1678_ = v___x_1672_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_e_1611_);
lean_ctor_set(v_reuseFailAlloc_1682_, 1, v_snd_1670_);
v___x_1678_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
lean_object* v___x_1680_; 
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 0, v___x_1678_);
v___x_1680_ = v___x_1667_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v___x_1678_);
lean_ctor_set(v_reuseFailAlloc_1681_, 1, v_a_1665_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1659_);
lean_dec_ref_known(v_e_1611_, 3);
return v___x_1663_;
}
}
else
{
lean_dec_ref_known(v_e_1611_, 3);
lean_dec(v_offset_1612_);
return v___x_1656_;
}
}
case 7:
{
lean_object* v_binderName_1691_; lean_object* v_binderType_1692_; lean_object* v_body_1693_; uint8_t v_binderInfo_1694_; lean_object* v___x_1695_; 
v_binderName_1691_ = lean_ctor_get(v_e_1611_, 0);
v_binderType_1692_ = lean_ctor_get(v_e_1611_, 1);
v_body_1693_ = lean_ctor_get(v_e_1611_, 2);
v_binderInfo_1694_ = lean_ctor_get_uint8(v_e_1611_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1612_);
lean_inc_ref(v_binderType_1692_);
v___x_1695_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1609_, v_xs_1610_, v_binderType_1692_, v_offset_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_);
if (lean_obj_tag(v___x_1695_) == 0)
{
lean_object* v_a_1696_; lean_object* v_a_1697_; lean_object* v_fst_1698_; lean_object* v_snd_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
v_a_1696_ = lean_ctor_get(v___x_1695_, 0);
lean_inc(v_a_1696_);
v_a_1697_ = lean_ctor_get(v___x_1695_, 1);
lean_inc(v_a_1697_);
lean_dec_ref_known(v___x_1695_, 2);
v_fst_1698_ = lean_ctor_get(v_a_1696_, 0);
lean_inc(v_fst_1698_);
v_snd_1699_ = lean_ctor_get(v_a_1696_, 1);
lean_inc(v_snd_1699_);
lean_dec(v_a_1696_);
v___x_1700_ = lean_unsigned_to_nat(1u);
v___x_1701_ = lean_nat_add(v_offset_1612_, v___x_1700_);
lean_dec(v_offset_1612_);
lean_inc_ref(v_body_1693_);
v___x_1702_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1609_, v_xs_1610_, v_body_1693_, v___x_1701_, v_snd_1699_, v_a_1614_, v_a_1615_, v_a_1697_);
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_object* v_a_1703_; lean_object* v_a_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1729_; 
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
v_a_1704_ = lean_ctor_get(v___x_1702_, 1);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1702_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1706_ = v___x_1702_;
v_isShared_1707_ = v_isSharedCheck_1729_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_a_1704_);
lean_inc(v_a_1703_);
lean_dec(v___x_1702_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1729_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v_fst_1708_; lean_object* v_snd_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1728_; 
v_fst_1708_ = lean_ctor_get(v_a_1703_, 0);
v_snd_1709_ = lean_ctor_get(v_a_1703_, 1);
v_isSharedCheck_1728_ = !lean_is_exclusive(v_a_1703_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1711_ = v_a_1703_;
v_isShared_1712_ = v_isSharedCheck_1728_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_snd_1709_);
lean_inc(v_fst_1708_);
lean_dec(v_a_1703_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1728_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
uint8_t v___y_1714_; size_t v___x_1722_; size_t v___x_1723_; uint8_t v___x_1724_; 
v___x_1722_ = lean_ptr_addr(v_binderType_1692_);
v___x_1723_ = lean_ptr_addr(v_fst_1698_);
v___x_1724_ = lean_usize_dec_eq(v___x_1722_, v___x_1723_);
if (v___x_1724_ == 0)
{
v___y_1714_ = v___x_1724_;
goto v___jp_1713_;
}
else
{
size_t v___x_1725_; size_t v___x_1726_; uint8_t v___x_1727_; 
v___x_1725_ = lean_ptr_addr(v_body_1693_);
v___x_1726_ = lean_ptr_addr(v_fst_1708_);
v___x_1727_ = lean_usize_dec_eq(v___x_1725_, v___x_1726_);
v___y_1714_ = v___x_1727_;
goto v___jp_1713_;
}
v___jp_1713_:
{
if (v___y_1714_ == 0)
{
lean_object* v___x_1715_; 
lean_inc(v_binderName_1691_);
lean_del_object(v___x_1711_);
lean_del_object(v___x_1706_);
lean_dec_ref_known(v_e_1611_, 3);
v___x_1715_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__3(v_binderName_1691_, v_binderInfo_1694_, v_fst_1698_, v_fst_1708_, v_snd_1709_, v_a_1614_, v_a_1615_, v_a_1704_);
return v___x_1715_;
}
else
{
lean_object* v___x_1717_; 
lean_dec(v_fst_1708_);
lean_dec(v_fst_1698_);
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 0, v_e_1611_);
v___x_1717_ = v___x_1711_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_e_1611_);
lean_ctor_set(v_reuseFailAlloc_1721_, 1, v_snd_1709_);
v___x_1717_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
lean_object* v___x_1719_; 
if (v_isShared_1707_ == 0)
{
lean_ctor_set(v___x_1706_, 0, v___x_1717_);
v___x_1719_ = v___x_1706_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v___x_1717_);
lean_ctor_set(v_reuseFailAlloc_1720_, 1, v_a_1704_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1698_);
lean_dec_ref_known(v_e_1611_, 3);
return v___x_1702_;
}
}
else
{
lean_dec_ref_known(v_e_1611_, 3);
lean_dec(v_offset_1612_);
return v___x_1695_;
}
}
case 8:
{
lean_object* v_declName_1730_; lean_object* v_type_1731_; lean_object* v_value_1732_; lean_object* v_body_1733_; uint8_t v_nondep_1734_; lean_object* v___x_1735_; 
v_declName_1730_ = lean_ctor_get(v_e_1611_, 0);
v_type_1731_ = lean_ctor_get(v_e_1611_, 1);
v_value_1732_ = lean_ctor_get(v_e_1611_, 2);
v_body_1733_ = lean_ctor_get(v_e_1611_, 3);
v_nondep_1734_ = lean_ctor_get_uint8(v_e_1611_, sizeof(void*)*4 + 8);
lean_inc(v_offset_1612_);
lean_inc_ref(v_type_1731_);
v___x_1735_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1609_, v_xs_1610_, v_type_1731_, v_offset_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_a_1736_; lean_object* v_a_1737_; lean_object* v_fst_1738_; lean_object* v_snd_1739_; lean_object* v___x_1740_; 
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_a_1736_);
v_a_1737_ = lean_ctor_get(v___x_1735_, 1);
lean_inc(v_a_1737_);
lean_dec_ref_known(v___x_1735_, 2);
v_fst_1738_ = lean_ctor_get(v_a_1736_, 0);
lean_inc(v_fst_1738_);
v_snd_1739_ = lean_ctor_get(v_a_1736_, 1);
lean_inc(v_snd_1739_);
lean_dec(v_a_1736_);
lean_inc(v_offset_1612_);
lean_inc_ref(v_value_1732_);
v___x_1740_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1609_, v_xs_1610_, v_value_1732_, v_offset_1612_, v_snd_1739_, v_a_1614_, v_a_1615_, v_a_1737_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_a_1741_; lean_object* v_a_1742_; lean_object* v_fst_1743_; lean_object* v_snd_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_a_1741_);
v_a_1742_ = lean_ctor_get(v___x_1740_, 1);
lean_inc(v_a_1742_);
lean_dec_ref_known(v___x_1740_, 2);
v_fst_1743_ = lean_ctor_get(v_a_1741_, 0);
lean_inc(v_fst_1743_);
v_snd_1744_ = lean_ctor_get(v_a_1741_, 1);
lean_inc(v_snd_1744_);
lean_dec(v_a_1741_);
v___x_1745_ = lean_unsigned_to_nat(1u);
v___x_1746_ = lean_nat_add(v_offset_1612_, v___x_1745_);
lean_dec(v_offset_1612_);
lean_inc_ref(v_body_1733_);
v___x_1747_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1609_, v_xs_1610_, v_body_1733_, v___x_1746_, v_snd_1744_, v_a_1614_, v_a_1615_, v_a_1742_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v_a_1748_; lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1778_; 
v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
v_a_1749_ = lean_ctor_get(v___x_1747_, 1);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1751_ = v___x_1747_;
v_isShared_1752_ = v_isSharedCheck_1778_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_inc(v_a_1748_);
lean_dec(v___x_1747_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1778_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v_fst_1753_; lean_object* v_snd_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1777_; 
v_fst_1753_ = lean_ctor_get(v_a_1748_, 0);
v_snd_1754_ = lean_ctor_get(v_a_1748_, 1);
v_isSharedCheck_1777_ = !lean_is_exclusive(v_a_1748_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1756_ = v_a_1748_;
v_isShared_1757_ = v_isSharedCheck_1777_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_snd_1754_);
lean_inc(v_fst_1753_);
lean_dec(v_a_1748_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1777_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
uint8_t v___y_1759_; size_t v___x_1771_; size_t v___x_1772_; uint8_t v___x_1773_; 
v___x_1771_ = lean_ptr_addr(v_type_1731_);
v___x_1772_ = lean_ptr_addr(v_fst_1738_);
v___x_1773_ = lean_usize_dec_eq(v___x_1771_, v___x_1772_);
if (v___x_1773_ == 0)
{
v___y_1759_ = v___x_1773_;
goto v___jp_1758_;
}
else
{
size_t v___x_1774_; size_t v___x_1775_; uint8_t v___x_1776_; 
v___x_1774_ = lean_ptr_addr(v_value_1732_);
v___x_1775_ = lean_ptr_addr(v_fst_1743_);
v___x_1776_ = lean_usize_dec_eq(v___x_1774_, v___x_1775_);
v___y_1759_ = v___x_1776_;
goto v___jp_1758_;
}
v___jp_1758_:
{
if (v___y_1759_ == 0)
{
lean_object* v___x_1760_; 
lean_inc(v_declName_1730_);
lean_del_object(v___x_1756_);
lean_del_object(v___x_1751_);
lean_dec_ref_known(v_e_1611_, 4);
v___x_1760_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4(v_declName_1730_, v_fst_1738_, v_fst_1743_, v_fst_1753_, v_nondep_1734_, v_snd_1754_, v_a_1614_, v_a_1615_, v_a_1749_);
return v___x_1760_;
}
else
{
size_t v___x_1761_; size_t v___x_1762_; uint8_t v___x_1763_; 
v___x_1761_ = lean_ptr_addr(v_body_1733_);
v___x_1762_ = lean_ptr_addr(v_fst_1753_);
v___x_1763_ = lean_usize_dec_eq(v___x_1761_, v___x_1762_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1764_; 
lean_inc(v_declName_1730_);
lean_del_object(v___x_1756_);
lean_del_object(v___x_1751_);
lean_dec_ref_known(v_e_1611_, 4);
v___x_1764_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4(v_declName_1730_, v_fst_1738_, v_fst_1743_, v_fst_1753_, v_nondep_1734_, v_snd_1754_, v_a_1614_, v_a_1615_, v_a_1749_);
return v___x_1764_;
}
else
{
lean_object* v___x_1766_; 
lean_dec(v_fst_1753_);
lean_dec(v_fst_1743_);
lean_dec(v_fst_1738_);
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 0, v_e_1611_);
v___x_1766_ = v___x_1756_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_e_1611_);
lean_ctor_set(v_reuseFailAlloc_1770_, 1, v_snd_1754_);
v___x_1766_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
lean_object* v___x_1768_; 
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 0, v___x_1766_);
v___x_1768_ = v___x_1751_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v___x_1766_);
lean_ctor_set(v_reuseFailAlloc_1769_, 1, v_a_1749_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
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
lean_dec(v_fst_1743_);
lean_dec(v_fst_1738_);
lean_dec_ref_known(v_e_1611_, 4);
return v___x_1747_;
}
}
else
{
lean_dec(v_fst_1738_);
lean_dec_ref_known(v_e_1611_, 4);
lean_dec(v_offset_1612_);
return v___x_1740_;
}
}
else
{
lean_dec_ref_known(v_e_1611_, 4);
lean_dec(v_offset_1612_);
return v___x_1735_;
}
}
case 10:
{
lean_object* v_data_1779_; lean_object* v_expr_1780_; lean_object* v___x_1781_; 
v_data_1779_ = lean_ctor_get(v_e_1611_, 0);
v_expr_1780_ = lean_ctor_get(v_e_1611_, 1);
lean_inc_ref(v_expr_1780_);
v___x_1781_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1609_, v_xs_1610_, v_expr_1780_, v_offset_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v_a_1782_; lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1803_; 
v_a_1782_ = lean_ctor_get(v___x_1781_, 0);
v_a_1783_ = lean_ctor_get(v___x_1781_, 1);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1785_ = v___x_1781_;
v_isShared_1786_ = v_isSharedCheck_1803_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_inc(v_a_1782_);
lean_dec(v___x_1781_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1803_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v_fst_1787_; lean_object* v_snd_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1802_; 
v_fst_1787_ = lean_ctor_get(v_a_1782_, 0);
v_snd_1788_ = lean_ctor_get(v_a_1782_, 1);
v_isSharedCheck_1802_ = !lean_is_exclusive(v_a_1782_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1790_ = v_a_1782_;
v_isShared_1791_ = v_isSharedCheck_1802_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_snd_1788_);
lean_inc(v_fst_1787_);
lean_dec(v_a_1782_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1802_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
size_t v___x_1792_; size_t v___x_1793_; uint8_t v___x_1794_; 
v___x_1792_ = lean_ptr_addr(v_expr_1780_);
v___x_1793_ = lean_ptr_addr(v_fst_1787_);
v___x_1794_ = lean_usize_dec_eq(v___x_1792_, v___x_1793_);
if (v___x_1794_ == 0)
{
lean_object* v___x_1795_; 
lean_inc(v_data_1779_);
lean_del_object(v___x_1790_);
lean_del_object(v___x_1785_);
lean_dec_ref_known(v_e_1611_, 2);
v___x_1795_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__5(v_data_1779_, v_fst_1787_, v_snd_1788_, v_a_1614_, v_a_1615_, v_a_1783_);
return v___x_1795_;
}
else
{
lean_object* v___x_1797_; 
lean_dec(v_fst_1787_);
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 0, v_e_1611_);
v___x_1797_ = v___x_1790_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_e_1611_);
lean_ctor_set(v_reuseFailAlloc_1801_, 1, v_snd_1788_);
v___x_1797_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
lean_object* v___x_1799_; 
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 0, v___x_1797_);
v___x_1799_ = v___x_1785_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v___x_1797_);
lean_ctor_set(v_reuseFailAlloc_1800_, 1, v_a_1783_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1611_, 2);
return v___x_1781_;
}
}
case 11:
{
lean_object* v_typeName_1804_; lean_object* v_idx_1805_; lean_object* v_struct_1806_; lean_object* v___x_1807_; 
v_typeName_1804_ = lean_ctor_get(v_e_1611_, 0);
v_idx_1805_ = lean_ctor_get(v_e_1611_, 1);
v_struct_1806_ = lean_ctor_get(v_e_1611_, 2);
lean_inc_ref(v_struct_1806_);
v___x_1807_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1609_, v_xs_1610_, v_struct_1806_, v_offset_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_a_1808_; lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1829_; 
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
v_a_1809_ = lean_ctor_get(v___x_1807_, 1);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1811_ = v___x_1807_;
v_isShared_1812_ = v_isSharedCheck_1829_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_inc(v_a_1808_);
lean_dec(v___x_1807_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1829_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v_fst_1813_; lean_object* v_snd_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1828_; 
v_fst_1813_ = lean_ctor_get(v_a_1808_, 0);
v_snd_1814_ = lean_ctor_get(v_a_1808_, 1);
v_isSharedCheck_1828_ = !lean_is_exclusive(v_a_1808_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1816_ = v_a_1808_;
v_isShared_1817_ = v_isSharedCheck_1828_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_snd_1814_);
lean_inc(v_fst_1813_);
lean_dec(v_a_1808_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1828_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
size_t v___x_1818_; size_t v___x_1819_; uint8_t v___x_1820_; 
v___x_1818_ = lean_ptr_addr(v_struct_1806_);
v___x_1819_ = lean_ptr_addr(v_fst_1813_);
v___x_1820_ = lean_usize_dec_eq(v___x_1818_, v___x_1819_);
if (v___x_1820_ == 0)
{
lean_object* v___x_1821_; 
lean_inc(v_idx_1805_);
lean_inc(v_typeName_1804_);
lean_del_object(v___x_1816_);
lean_del_object(v___x_1811_);
lean_dec_ref_known(v_e_1611_, 3);
v___x_1821_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__6(v_typeName_1804_, v_idx_1805_, v_fst_1813_, v_snd_1814_, v_a_1614_, v_a_1615_, v_a_1809_);
return v___x_1821_;
}
else
{
lean_object* v___x_1823_; 
lean_dec(v_fst_1813_);
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 0, v_e_1611_);
v___x_1823_ = v___x_1816_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_e_1611_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v_snd_1814_);
v___x_1823_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
lean_object* v___x_1825_; 
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 0, v___x_1823_);
v___x_1825_ = v___x_1811_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1823_);
lean_ctor_set(v_reuseFailAlloc_1826_, 1, v_a_1809_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1611_, 3);
return v___x_1807_;
}
}
default: 
{
lean_object* v___x_1830_; lean_object* v___x_1831_; 
lean_dec(v_offset_1612_);
lean_dec_ref(v_e_1611_);
v___x_1830_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__3);
v___x_1831_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7(v___x_1830_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_);
return v___x_1831_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(lean_object* v_n_1832_, lean_object* v_xs_1833_, lean_object* v_e_1834_, lean_object* v_offset_1835_, lean_object* v_a_1836_, uint8_t v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_){
_start:
{
lean_object* v_key_1840_; lean_object* v___x_1841_; 
lean_inc(v_offset_1835_);
lean_inc_ref(v_e_1834_);
v_key_1840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1840_, 0, v_e_1834_);
lean_ctor_set(v_key_1840_, 1, v_offset_1835_);
v___x_1841_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2___redArg(v_a_1836_, v_key_1840_);
if (lean_obj_tag(v___x_1841_) == 1)
{
lean_object* v_val_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
lean_dec_ref_known(v_key_1840_, 2);
lean_dec(v_offset_1835_);
lean_dec_ref(v_e_1834_);
v_val_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_val_1842_);
lean_dec_ref_known(v___x_1841_, 1);
v___x_1843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1843_, 0, v_val_1842_);
lean_ctor_set(v___x_1843_, 1, v_a_1836_);
v___x_1844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1843_);
lean_ctor_set(v___x_1844_, 1, v_a_1839_);
return v___x_1844_;
}
else
{
lean_dec(v___x_1841_);
switch(lean_obj_tag(v_e_1834_))
{
case 0:
{
lean_object* v_deBruijnIndex_1845_; uint8_t v___x_1846_; 
v_deBruijnIndex_1845_ = lean_ctor_get(v_e_1834_, 0);
v___x_1846_ = lean_nat_dec_le(v_offset_1835_, v_deBruijnIndex_1845_);
if (v___x_1846_ == 0)
{
lean_object* v___x_1847_; 
lean_dec(v_offset_1835_);
v___x_1847_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1840_, v_e_1834_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
return v___x_1847_;
}
else
{
lean_object* v_size_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; uint8_t v___x_1854_; 
lean_inc(v_deBruijnIndex_1845_);
lean_dec_ref_known(v_e_1834_, 1);
v_size_1848_ = lean_ctor_get(v_xs_1833_, 2);
v___x_1849_ = l_Lean_instInhabitedExpr;
v___x_1850_ = lean_nat_sub(v_deBruijnIndex_1845_, v_offset_1835_);
lean_dec(v_offset_1835_);
lean_dec(v_deBruijnIndex_1845_);
v___x_1851_ = lean_nat_sub(v_n_1832_, v___x_1850_);
lean_dec(v___x_1850_);
v___x_1852_ = lean_unsigned_to_nat(1u);
v___x_1853_ = lean_nat_sub(v___x_1851_, v___x_1852_);
lean_dec(v___x_1851_);
v___x_1854_ = lean_nat_dec_lt(v___x_1853_, v_size_1848_);
if (v___x_1854_ == 0)
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
lean_dec(v___x_1853_);
v___x_1855_ = l_outOfBounds___redArg(v___x_1849_);
v___x_1856_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1840_, v___x_1855_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
return v___x_1856_;
}
else
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1857_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1849_, v_xs_1833_, v___x_1853_);
lean_dec(v___x_1853_);
v___x_1858_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1840_, v___x_1857_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
return v___x_1858_;
}
}
}
case 9:
{
lean_object* v___x_1859_; 
lean_dec(v_offset_1835_);
v___x_1859_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1840_, v_e_1834_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
return v___x_1859_;
}
case 2:
{
lean_object* v___x_1860_; 
lean_dec(v_offset_1835_);
v___x_1860_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1840_, v_e_1834_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
return v___x_1860_;
}
case 1:
{
lean_object* v___x_1861_; 
lean_dec(v_offset_1835_);
v___x_1861_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1840_, v_e_1834_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
return v___x_1861_;
}
case 4:
{
lean_object* v___x_1862_; 
lean_dec(v_offset_1835_);
v___x_1862_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1840_, v_e_1834_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
return v___x_1862_;
}
case 3:
{
lean_object* v___x_1863_; 
lean_dec(v_offset_1835_);
v___x_1863_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1840_, v_e_1834_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
return v___x_1863_;
}
default: 
{
lean_object* v___x_1864_; uint8_t v___x_1865_; 
v___x_1864_ = l_Lean_Expr_looseBVarRange(v_e_1834_);
v___x_1865_ = lean_nat_dec_le(v___x_1864_, v_offset_1835_);
lean_dec(v___x_1864_);
if (v___x_1865_ == 0)
{
switch(lean_obj_tag(v_e_1834_))
{
case 9:
{
lean_object* v___x_1866_; 
lean_dec(v_offset_1835_);
v___x_1866_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1840_, v_e_1834_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
return v___x_1866_;
}
case 2:
{
lean_object* v___x_1867_; 
lean_dec(v_offset_1835_);
v___x_1867_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1840_, v_e_1834_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
return v___x_1867_;
}
case 0:
{
lean_object* v___x_1868_; 
lean_dec(v_offset_1835_);
v___x_1868_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1840_, v_e_1834_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
return v___x_1868_;
}
case 1:
{
lean_object* v___x_1869_; 
lean_dec(v_offset_1835_);
v___x_1869_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1840_, v_e_1834_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
return v___x_1869_;
}
case 4:
{
lean_object* v___x_1870_; 
lean_dec(v_offset_1835_);
v___x_1870_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1840_, v_e_1834_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
return v___x_1870_;
}
case 3:
{
lean_object* v___x_1871_; 
lean_dec(v_offset_1835_);
v___x_1871_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1840_, v_e_1834_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
return v___x_1871_;
}
default: 
{
lean_object* v___x_1872_; 
v___x_1872_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0(v_n_1832_, v_xs_1833_, v_e_1834_, v_offset_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; lean_object* v_a_1874_; lean_object* v_fst_1875_; lean_object* v_snd_1876_; lean_object* v___x_1877_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_a_1873_);
v_a_1874_ = lean_ctor_get(v___x_1872_, 1);
lean_inc(v_a_1874_);
lean_dec_ref_known(v___x_1872_, 2);
v_fst_1875_ = lean_ctor_get(v_a_1873_, 0);
lean_inc(v_fst_1875_);
v_snd_1876_ = lean_ctor_get(v_a_1873_, 1);
lean_inc(v_snd_1876_);
lean_dec(v_a_1873_);
v___x_1877_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1840_, v_fst_1875_, v_snd_1876_, v_a_1837_, v_a_1838_, v_a_1874_);
return v___x_1877_;
}
else
{
lean_dec_ref_known(v_key_1840_, 2);
return v___x_1872_;
}
}
}
}
else
{
lean_object* v___x_1878_; 
lean_dec(v_offset_1835_);
v___x_1878_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1840_, v_e_1834_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
return v___x_1878_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0___boxed(lean_object* v_n_1879_, lean_object* v_xs_1880_, lean_object* v_e_1881_, lean_object* v_offset_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_){
_start:
{
uint8_t v_a_boxed_1887_; lean_object* v_res_1888_; 
v_a_boxed_1887_ = lean_unbox(v_a_1884_);
v_res_1888_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1879_, v_xs_1880_, v_e_1881_, v_offset_1882_, v_a_1883_, v_a_boxed_1887_, v_a_1885_, v_a_1886_);
lean_dec_ref(v_a_1885_);
lean_dec_ref(v_xs_1880_);
lean_dec(v_n_1879_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___boxed(lean_object* v_n_1889_, lean_object* v_xs_1890_, lean_object* v_e_1891_, lean_object* v_offset_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_){
_start:
{
uint8_t v_a_boxed_1897_; lean_object* v_res_1898_; 
v_a_boxed_1897_ = lean_unbox(v_a_1894_);
v_res_1898_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0(v_n_1889_, v_xs_1890_, v_e_1891_, v_offset_1892_, v_a_1893_, v_a_boxed_1897_, v_a_1895_, v_a_1896_);
lean_dec_ref(v_a_1895_);
lean_dec_ref(v_xs_1890_);
lean_dec(v_n_1889_);
return v_res_1898_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v_cellCount_1899_; lean_object* v___x_1900_; 
v_cellCount_1899_ = lean_unsigned_to_nat(16u);
v___x_1900_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1899_);
return v___x_1900_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v_cellCount_1901_; lean_object* v___x_1902_; 
v_cellCount_1901_ = lean_unsigned_to_nat(16u);
v___x_1902_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1901_);
return v___x_1902_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1903_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__1, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__1);
v___x_1904_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__0, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__0_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__0);
v___x_1905_ = lean_unsigned_to_nat(0u);
v___x_1906_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1905_);
lean_ctor_set(v___x_1906_, 1, v___x_1904_);
lean_ctor_set(v___x_1906_, 2, v___x_1903_);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0(lean_object* v_e_1907_, lean_object* v_size_1908_, lean_object* v_xs_1909_, uint8_t v_debug_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v___x_1913_; 
v___x_1913_ = lean_unsigned_to_nat(0u);
switch(lean_obj_tag(v_e_1907_))
{
case 0:
{
lean_object* v_deBruijnIndex_1914_; uint8_t v___x_1915_; 
v_deBruijnIndex_1914_ = lean_ctor_get(v_e_1907_, 0);
v___x_1915_ = lean_nat_dec_le(v___x_1913_, v_deBruijnIndex_1914_);
if (v___x_1915_ == 0)
{
lean_object* v___x_1916_; 
v___x_1916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1916_, 0, v_e_1907_);
lean_ctor_set(v___x_1916_, 1, v___y_1912_);
return v___x_1916_;
}
else
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; uint8_t v___x_1921_; 
lean_inc(v_deBruijnIndex_1914_);
lean_dec_ref_known(v_e_1907_, 1);
v___x_1917_ = l_Lean_instInhabitedExpr;
v___x_1918_ = lean_nat_sub(v_size_1908_, v_deBruijnIndex_1914_);
lean_dec(v_deBruijnIndex_1914_);
v___x_1919_ = lean_unsigned_to_nat(1u);
v___x_1920_ = lean_nat_sub(v___x_1918_, v___x_1919_);
lean_dec(v___x_1918_);
v___x_1921_ = lean_nat_dec_lt(v___x_1920_, v_size_1908_);
if (v___x_1921_ == 0)
{
lean_object* v___x_1922_; lean_object* v___x_1923_; 
lean_dec(v___x_1920_);
v___x_1922_ = l_outOfBounds___redArg(v___x_1917_);
v___x_1923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1922_);
lean_ctor_set(v___x_1923_, 1, v___y_1912_);
return v___x_1923_;
}
else
{
lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1924_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1917_, v_xs_1909_, v___x_1920_);
lean_dec(v___x_1920_);
v___x_1925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1924_);
lean_ctor_set(v___x_1925_, 1, v___y_1912_);
return v___x_1925_;
}
}
}
case 9:
{
lean_object* v___x_1926_; 
v___x_1926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1926_, 0, v_e_1907_);
lean_ctor_set(v___x_1926_, 1, v___y_1912_);
return v___x_1926_;
}
case 2:
{
lean_object* v___x_1927_; 
v___x_1927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1927_, 0, v_e_1907_);
lean_ctor_set(v___x_1927_, 1, v___y_1912_);
return v___x_1927_;
}
case 1:
{
lean_object* v___x_1928_; 
v___x_1928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1928_, 0, v_e_1907_);
lean_ctor_set(v___x_1928_, 1, v___y_1912_);
return v___x_1928_;
}
case 4:
{
lean_object* v___x_1929_; 
v___x_1929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1929_, 0, v_e_1907_);
lean_ctor_set(v___x_1929_, 1, v___y_1912_);
return v___x_1929_;
}
case 3:
{
lean_object* v___x_1930_; 
v___x_1930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1930_, 0, v_e_1907_);
lean_ctor_set(v___x_1930_, 1, v___y_1912_);
return v___x_1930_;
}
default: 
{
lean_object* v___x_1931_; uint8_t v___x_1932_; 
v___x_1931_ = l_Lean_Expr_looseBVarRange(v_e_1907_);
v___x_1932_ = lean_nat_dec_le(v___x_1931_, v___x_1913_);
lean_dec(v___x_1931_);
if (v___x_1932_ == 0)
{
switch(lean_obj_tag(v_e_1907_))
{
case 9:
{
lean_object* v___x_1933_; 
v___x_1933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1933_, 0, v_e_1907_);
lean_ctor_set(v___x_1933_, 1, v___y_1912_);
return v___x_1933_;
}
case 2:
{
lean_object* v___x_1934_; 
v___x_1934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1934_, 0, v_e_1907_);
lean_ctor_set(v___x_1934_, 1, v___y_1912_);
return v___x_1934_;
}
case 0:
{
lean_object* v___x_1935_; 
v___x_1935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1935_, 0, v_e_1907_);
lean_ctor_set(v___x_1935_, 1, v___y_1912_);
return v___x_1935_;
}
case 1:
{
lean_object* v___x_1936_; 
v___x_1936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1936_, 0, v_e_1907_);
lean_ctor_set(v___x_1936_, 1, v___y_1912_);
return v___x_1936_;
}
case 4:
{
lean_object* v___x_1937_; 
v___x_1937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1937_, 0, v_e_1907_);
lean_ctor_set(v___x_1937_, 1, v___y_1912_);
return v___x_1937_;
}
case 3:
{
lean_object* v___x_1938_; 
v___x_1938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1938_, 0, v_e_1907_);
lean_ctor_set(v___x_1938_, 1, v___y_1912_);
return v___x_1938_;
}
default: 
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1939_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__2);
v___x_1940_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0(v_size_1908_, v_xs_1909_, v_e_1907_, v___x_1913_, v___x_1939_, v_debug_1910_, v___y_1911_, v___y_1912_);
if (lean_obj_tag(v___x_1940_) == 0)
{
lean_object* v_a_1941_; lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1950_; 
v_a_1941_ = lean_ctor_get(v___x_1940_, 0);
v_a_1942_ = lean_ctor_get(v___x_1940_, 1);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1944_ = v___x_1940_;
v_isShared_1945_ = v_isSharedCheck_1950_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_inc(v_a_1941_);
lean_dec(v___x_1940_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1950_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v_fst_1946_; lean_object* v___x_1948_; 
v_fst_1946_ = lean_ctor_get(v_a_1941_, 0);
lean_inc(v_fst_1946_);
lean_dec(v_a_1941_);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 0, v_fst_1946_);
v___x_1948_ = v___x_1944_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_fst_1946_);
lean_ctor_set(v_reuseFailAlloc_1949_, 1, v_a_1942_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
else
{
lean_object* v_a_1951_; lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
v_a_1951_ = lean_ctor_get(v___x_1940_, 0);
v_a_1952_ = lean_ctor_get(v___x_1940_, 1);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___x_1940_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_inc(v_a_1951_);
lean_dec(v___x_1940_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1951_);
lean_ctor_set(v_reuseFailAlloc_1958_, 1, v_a_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
}
}
else
{
lean_object* v___x_1960_; 
v___x_1960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1960_, 0, v_e_1907_);
lean_ctor_set(v___x_1960_, 1, v___y_1912_);
return v___x_1960_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___boxed(lean_object* v_e_1961_, lean_object* v_size_1962_, lean_object* v_xs_1963_, lean_object* v_debug_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
uint8_t v_debug_boxed_1967_; lean_object* v_res_1968_; 
v_debug_boxed_1967_ = lean_unbox(v_debug_1964_);
v_res_1968_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0(v_e_1961_, v_size_1962_, v_xs_1963_, v_debug_boxed_1967_, v___y_1965_, v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec_ref(v_xs_1963_);
lean_dec(v_size_1962_);
return v_res_1968_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2(void){
_start:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1971_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__2));
v___x_1972_ = lean_unsigned_to_nat(16u);
v___x_1973_ = lean_unsigned_to_nat(62u);
v___x_1974_ = ((lean_object*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__1));
v___x_1975_ = ((lean_object*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__0));
v___x_1976_ = l_mkPanicMessageWithDecl(v___x_1975_, v___x_1974_, v___x_1973_, v___x_1972_, v___x_1971_);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg(lean_object* v_xs_1977_, lean_object* v_e_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_){
_start:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v_size_1988_; uint8_t v_debug_1989_; lean_object* v_env_1990_; lean_object* v___x_1991_; lean_object* v___f_1992_; uint8_t v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1986_ = lean_st_ref_get(v_a_1980_);
v___x_1987_ = lean_st_ref_get(v_a_1984_);
v_size_1988_ = lean_ctor_get(v_xs_1977_, 2);
lean_inc(v_size_1988_);
v_debug_1989_ = lean_ctor_get_uint8(v___x_1986_, sizeof(void*)*11);
lean_dec(v___x_1986_);
v_env_1990_ = lean_ctor_get(v___x_1987_, 0);
lean_inc_ref(v_env_1990_);
lean_dec(v___x_1987_);
v___x_1991_ = lean_box(v_debug_1989_);
v___f_1992_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1992_, 0, v_e_1978_);
lean_closure_set(v___f_1992_, 1, v_size_1988_);
lean_closure_set(v___f_1992_, 2, v_xs_1977_);
lean_closure_set(v___f_1992_, 3, v___x_1991_);
v___x_1993_ = 0;
v___x_1994_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1994_, 0, v_env_1990_);
lean_ctor_set_uint8(v___x_1994_, sizeof(void*)*1, v___x_1993_);
lean_ctor_set_uint8(v___x_1994_, sizeof(void*)*1 + 1, v___x_1993_);
v___x_1995_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_1992_, v___x_1994_, v_a_1980_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2006_; 
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_1998_ = v___x_1995_;
v_isShared_1999_ = v_isSharedCheck_2006_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1995_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2006_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
if (lean_obj_tag(v_a_1996_) == 0)
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
lean_dec_ref_known(v_a_1996_, 1);
lean_del_object(v___x_1998_);
v___x_2000_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2);
v___x_2001_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1(v___x_2000_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_);
return v___x_2001_;
}
else
{
lean_object* v_a_2002_; lean_object* v___x_2004_; 
v_a_2002_ = lean_ctor_get(v_a_1996_, 0);
lean_inc(v_a_2002_);
lean_dec_ref_known(v_a_1996_, 1);
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 0, v_a_2002_);
v___x_2004_ = v___x_1998_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_a_2002_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
}
else
{
lean_object* v_a_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2014_; 
v_a_2007_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_2009_ = v___x_1995_;
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_a_2007_);
lean_dec(v___x_1995_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2012_; 
if (v_isShared_2010_ == 0)
{
v___x_2012_ = v___x_2009_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_a_2007_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___boxed(lean_object* v_xs_2015_, lean_object* v_e_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_){
_start:
{
lean_object* v_res_2024_; 
v_res_2024_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg(v_xs_2015_, v_e_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_);
lean_dec(v_a_2022_);
lean_dec_ref(v_a_2021_);
lean_dec(v_a_2020_);
lean_dec_ref(v_a_2019_);
lean_dec(v_a_2018_);
lean_dec_ref(v_a_2017_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv(lean_object* v_xs_2025_, lean_object* v_e_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_){
_start:
{
lean_object* v___x_2035_; 
v___x_2035_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg(v_xs_2025_, v_e_2026_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_);
return v___x_2035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___boxed(lean_object* v_xs_2036_, lean_object* v_e_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv(v_xs_2036_, v_e_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_);
lean_dec(v_a_2044_);
lean_dec_ref(v_a_2043_);
lean_dec(v_a_2042_);
lean_dec_ref(v_a_2041_);
lean_dec(v_a_2040_);
lean_dec_ref(v_a_2039_);
lean_dec(v_a_2038_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2047_, lean_object* v_m_2048_, lean_object* v_a_2049_){
_start:
{
lean_object* v___x_2050_; 
v___x_2050_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2___redArg(v_m_2048_, v_a_2049_);
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2051_, lean_object* v_m_2052_, lean_object* v_a_2053_){
_start:
{
lean_object* v_res_2054_; 
v_res_2054_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2(v_00_u03b2_2051_, v_m_2052_, v_a_2053_);
lean_dec_ref(v_a_2053_);
lean_dec_ref(v_m_2052_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10(lean_object* v_00_u03b2_2055_, lean_object* v_m_2056_, lean_object* v_query_2057_){
_start:
{
lean_object* v___x_2058_; 
v___x_2058_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10___redArg(v_m_2056_, v_query_2057_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10___boxed(lean_object* v_00_u03b2_2059_, lean_object* v_m_2060_, lean_object* v_query_2061_){
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10(v_00_u03b2_2059_, v_m_2060_, v_query_2061_);
lean_dec_ref(v_query_2061_);
lean_dec_ref(v_m_2060_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10_spec__11(lean_object* v_00_u03b2_2063_, lean_object* v_m_2064_, lean_object* v_query_2065_){
_start:
{
lean_object* v___x_2066_; 
v___x_2066_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10_spec__11___redArg(v_m_2064_, v_query_2065_);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10_spec__11___boxed(lean_object* v_00_u03b2_2067_, lean_object* v_m_2068_, lean_object* v_query_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10_spec__11(v_00_u03b2_2067_, v_m_2068_, v_query_2069_);
lean_dec_ref(v_query_2069_);
lean_dec_ref(v_m_2068_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10_spec__11_spec__12(lean_object* v_00_u03b2_2071_, lean_object* v_m_2072_, lean_object* v_query_2073_, lean_object* v_x_2074_, lean_object* v_x_2075_, lean_object* v_x_2076_, lean_object* v_x_2077_){
_start:
{
lean_object* v___x_2078_; 
v___x_2078_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10_spec__11_spec__12___redArg(v_m_2072_, v_query_2073_, v_x_2074_, v_x_2075_, v_x_2076_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10_spec__11_spec__12___boxed(lean_object* v_00_u03b2_2079_, lean_object* v_m_2080_, lean_object* v_query_2081_, lean_object* v_x_2082_, lean_object* v_x_2083_, lean_object* v_x_2084_, lean_object* v_x_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10_spec__11_spec__12(v_00_u03b2_2079_, v_m_2080_, v_query_2081_, v_x_2082_, v_x_2083_, v_x_2084_, v_x_2085_);
lean_dec_ref(v_query_2081_);
lean_dec_ref(v_m_2080_);
return v_res_2086_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2087_; 
v___x_2087_ = l_instMonadEIO(lean_box(0));
return v___x_2087_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(lean_object* v_msg_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v_toApplicative_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2167_; 
v___x_2101_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__0);
v___x_2102_ = l_StateRefT_x27_instMonad___redArg(v___x_2101_);
v_toApplicative_2103_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2167_ == 0)
{
lean_object* v_unused_2168_; 
v_unused_2168_ = lean_ctor_get(v___x_2102_, 1);
lean_dec(v_unused_2168_);
v___x_2105_ = v___x_2102_;
v_isShared_2106_ = v_isSharedCheck_2167_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_toApplicative_2103_);
lean_dec(v___x_2102_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2167_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v_toFunctor_2107_; lean_object* v_toSeq_2108_; lean_object* v_toSeqLeft_2109_; lean_object* v_toSeqRight_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2165_; 
v_toFunctor_2107_ = lean_ctor_get(v_toApplicative_2103_, 0);
v_toSeq_2108_ = lean_ctor_get(v_toApplicative_2103_, 2);
v_toSeqLeft_2109_ = lean_ctor_get(v_toApplicative_2103_, 3);
v_toSeqRight_2110_ = lean_ctor_get(v_toApplicative_2103_, 4);
v_isSharedCheck_2165_ = !lean_is_exclusive(v_toApplicative_2103_);
if (v_isSharedCheck_2165_ == 0)
{
lean_object* v_unused_2166_; 
v_unused_2166_ = lean_ctor_get(v_toApplicative_2103_, 1);
lean_dec(v_unused_2166_);
v___x_2112_ = v_toApplicative_2103_;
v_isShared_2113_ = v_isSharedCheck_2165_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_toSeqRight_2110_);
lean_inc(v_toSeqLeft_2109_);
lean_inc(v_toSeq_2108_);
lean_inc(v_toFunctor_2107_);
lean_dec(v_toApplicative_2103_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2165_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___f_2114_; lean_object* v___f_2115_; lean_object* v___f_2116_; lean_object* v___f_2117_; lean_object* v___x_2118_; lean_object* v___f_2119_; lean_object* v___f_2120_; lean_object* v___f_2121_; lean_object* v___x_2123_; 
v___f_2114_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__1));
v___f_2115_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__2));
lean_inc_ref(v_toFunctor_2107_);
v___f_2116_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2116_, 0, v_toFunctor_2107_);
v___f_2117_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2117_, 0, v_toFunctor_2107_);
v___x_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___f_2116_);
lean_ctor_set(v___x_2118_, 1, v___f_2117_);
v___f_2119_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2119_, 0, v_toSeqRight_2110_);
v___f_2120_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2120_, 0, v_toSeqLeft_2109_);
v___f_2121_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2121_, 0, v_toSeq_2108_);
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 4, v___f_2119_);
lean_ctor_set(v___x_2112_, 3, v___f_2120_);
lean_ctor_set(v___x_2112_, 2, v___f_2121_);
lean_ctor_set(v___x_2112_, 1, v___f_2114_);
lean_ctor_set(v___x_2112_, 0, v___x_2118_);
v___x_2123_ = v___x_2112_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2118_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v___f_2114_);
lean_ctor_set(v_reuseFailAlloc_2164_, 2, v___f_2121_);
lean_ctor_set(v_reuseFailAlloc_2164_, 3, v___f_2120_);
lean_ctor_set(v_reuseFailAlloc_2164_, 4, v___f_2119_);
v___x_2123_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
lean_object* v___x_2125_; 
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 1, v___f_2115_);
lean_ctor_set(v___x_2105_, 0, v___x_2123_);
v___x_2125_ = v___x_2105_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2123_);
lean_ctor_set(v_reuseFailAlloc_2163_, 1, v___f_2115_);
v___x_2125_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
lean_object* v___x_2126_; lean_object* v_toApplicative_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2161_; 
v___x_2126_ = l_StateRefT_x27_instMonad___redArg(v___x_2125_);
v_toApplicative_2127_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2161_ == 0)
{
lean_object* v_unused_2162_; 
v_unused_2162_ = lean_ctor_get(v___x_2126_, 1);
lean_dec(v_unused_2162_);
v___x_2129_ = v___x_2126_;
v_isShared_2130_ = v_isSharedCheck_2161_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_toApplicative_2127_);
lean_dec(v___x_2126_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2161_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v_toFunctor_2131_; lean_object* v_toSeq_2132_; lean_object* v_toSeqLeft_2133_; lean_object* v_toSeqRight_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2159_; 
v_toFunctor_2131_ = lean_ctor_get(v_toApplicative_2127_, 0);
v_toSeq_2132_ = lean_ctor_get(v_toApplicative_2127_, 2);
v_toSeqLeft_2133_ = lean_ctor_get(v_toApplicative_2127_, 3);
v_toSeqRight_2134_ = lean_ctor_get(v_toApplicative_2127_, 4);
v_isSharedCheck_2159_ = !lean_is_exclusive(v_toApplicative_2127_);
if (v_isSharedCheck_2159_ == 0)
{
lean_object* v_unused_2160_; 
v_unused_2160_ = lean_ctor_get(v_toApplicative_2127_, 1);
lean_dec(v_unused_2160_);
v___x_2136_ = v_toApplicative_2127_;
v_isShared_2137_ = v_isSharedCheck_2159_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_toSeqRight_2134_);
lean_inc(v_toSeqLeft_2133_);
lean_inc(v_toSeq_2132_);
lean_inc(v_toFunctor_2131_);
lean_dec(v_toApplicative_2127_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2159_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___f_2138_; lean_object* v___f_2139_; lean_object* v___f_2140_; lean_object* v___f_2141_; lean_object* v___x_2142_; lean_object* v___f_2143_; lean_object* v___f_2144_; lean_object* v___f_2145_; lean_object* v___x_2147_; 
v___f_2138_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__3));
v___f_2139_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__4));
lean_inc_ref(v_toFunctor_2131_);
v___f_2140_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2140_, 0, v_toFunctor_2131_);
v___f_2141_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2141_, 0, v_toFunctor_2131_);
v___x_2142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2142_, 0, v___f_2140_);
lean_ctor_set(v___x_2142_, 1, v___f_2141_);
v___f_2143_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2143_, 0, v_toSeqRight_2134_);
v___f_2144_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2144_, 0, v_toSeqLeft_2133_);
v___f_2145_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2145_, 0, v_toSeq_2132_);
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 4, v___f_2143_);
lean_ctor_set(v___x_2136_, 3, v___f_2144_);
lean_ctor_set(v___x_2136_, 2, v___f_2145_);
lean_ctor_set(v___x_2136_, 1, v___f_2138_);
lean_ctor_set(v___x_2136_, 0, v___x_2142_);
v___x_2147_ = v___x_2136_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v___x_2142_);
lean_ctor_set(v_reuseFailAlloc_2158_, 1, v___f_2138_);
lean_ctor_set(v_reuseFailAlloc_2158_, 2, v___f_2145_);
lean_ctor_set(v_reuseFailAlloc_2158_, 3, v___f_2144_);
lean_ctor_set(v_reuseFailAlloc_2158_, 4, v___f_2143_);
v___x_2147_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
lean_object* v___x_2149_; 
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 1, v___f_2139_);
lean_ctor_set(v___x_2129_, 0, v___x_2147_);
v___x_2149_ = v___x_2129_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v___x_2147_);
lean_ctor_set(v_reuseFailAlloc_2157_, 1, v___f_2139_);
v___x_2149_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_24612__overap_2155_; lean_object* v___x_2156_; 
v___x_2150_ = l_StateRefT_x27_instMonad___redArg(v___x_2149_);
v___x_2151_ = l_ReaderT_instMonad___redArg(v___x_2150_);
v___x_2152_ = l_StateRefT_x27_instMonad___redArg(v___x_2151_);
v___x_2153_ = l_Lean_instInhabitedExpr;
v___x_2154_ = l_instInhabitedOfMonad___redArg(v___x_2152_, v___x_2153_);
v___x_24612__overap_2155_ = lean_panic_fn_borrowed(v___x_2154_, v_msg_2092_);
lean_dec(v___x_2154_);
lean_inc(v___y_2099_);
lean_inc_ref(v___y_2098_);
lean_inc(v___y_2097_);
lean_inc_ref(v___y_2096_);
lean_inc(v___y_2095_);
lean_inc_ref(v___y_2094_);
lean_inc(v___y_2093_);
v___x_2156_ = lean_apply_8(v___x_24612__overap_2155_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, lean_box(0));
return v___x_2156_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___boxed(lean_object* v_msg_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(v_msg_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
lean_dec(v___y_2170_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1___redArg(lean_object* v_f_2179_, lean_object* v_a_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
lean_object* v___y_2189_; lean_object* v___x_2192_; uint8_t v_debug_2193_; 
v___x_2192_ = lean_st_ref_get(v___y_2182_);
v_debug_2193_ = lean_ctor_get_uint8(v___x_2192_, sizeof(void*)*11);
lean_dec(v___x_2192_);
if (v_debug_2193_ == 0)
{
v___y_2189_ = v___y_2182_;
goto v___jp_2188_;
}
else
{
lean_object* v___x_2194_; 
v___x_2194_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_2179_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v___x_2195_; 
lean_dec_ref_known(v___x_2194_, 1);
v___x_2195_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_dec_ref_known(v___x_2195_, 1);
v___y_2189_ = v___y_2182_;
goto v___jp_2188_;
}
else
{
lean_object* v_a_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2203_; 
lean_dec_ref(v_a_2180_);
lean_dec_ref(v_f_2179_);
v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2198_ = v___x_2195_;
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_a_2196_);
lean_dec(v___x_2195_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2201_; 
if (v_isShared_2199_ == 0)
{
v___x_2201_ = v___x_2198_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_a_2196_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
}
}
else
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2211_; 
lean_dec_ref(v_a_2180_);
lean_dec_ref(v_f_2179_);
v_a_2204_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2206_ = v___x_2194_;
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2194_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2209_; 
if (v_isShared_2207_ == 0)
{
v___x_2209_ = v___x_2206_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_a_2204_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
v___jp_2188_:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2190_ = l_Lean_Expr_app___override(v_f_2179_, v_a_2180_);
v___x_2191_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2190_, v___y_2189_);
return v___x_2191_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1___redArg___boxed(lean_object* v_f_2212_, lean_object* v_a_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
lean_object* v_res_2221_; 
v_res_2221_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1___redArg(v_f_2212_, v_a_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
return v_res_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1(lean_object* v_f_2222_, lean_object* v_a_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
lean_object* v___x_2232_; 
v___x_2232_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1___redArg(v_f_2222_, v_a_2223_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1___boxed(lean_object* v_f_2233_, lean_object* v_a_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1(v_f_2233_, v_a_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec(v___y_2235_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2___redArg(lean_object* v_d_2244_, lean_object* v_e_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
lean_object* v___y_2254_; lean_object* v___x_2257_; uint8_t v_debug_2258_; 
v___x_2257_ = lean_st_ref_get(v___y_2247_);
v_debug_2258_ = lean_ctor_get_uint8(v___x_2257_, sizeof(void*)*11);
lean_dec(v___x_2257_);
if (v_debug_2258_ == 0)
{
v___y_2254_ = v___y_2247_;
goto v___jp_2253_;
}
else
{
lean_object* v___x_2259_; 
v___x_2259_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_e_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
if (lean_obj_tag(v___x_2259_) == 0)
{
lean_dec_ref_known(v___x_2259_, 1);
v___y_2254_ = v___y_2247_;
goto v___jp_2253_;
}
else
{
lean_object* v_a_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2267_; 
lean_dec_ref(v_e_2245_);
lean_dec(v_d_2244_);
v_a_2260_ = lean_ctor_get(v___x_2259_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2259_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2262_ = v___x_2259_;
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_a_2260_);
lean_dec(v___x_2259_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v___x_2265_; 
if (v_isShared_2263_ == 0)
{
v___x_2265_ = v___x_2262_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_a_2260_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
}
}
v___jp_2253_:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = l_Lean_Expr_mdata___override(v_d_2244_, v_e_2245_);
v___x_2256_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2255_, v___y_2254_);
return v___x_2256_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2___redArg___boxed(lean_object* v_d_2268_, lean_object* v_e_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2___redArg(v_d_2268_, v_e_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2(lean_object* v_d_2278_, lean_object* v_e_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
lean_object* v___x_2288_; 
v___x_2288_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2___redArg(v_d_2278_, v_e_2279_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2___boxed(lean_object* v_d_2289_, lean_object* v_e_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
lean_object* v_res_2299_; 
v_res_2299_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2(v_d_2289_, v_e_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
lean_dec(v___y_2291_);
return v_res_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3___redArg(lean_object* v_structName_2300_, lean_object* v_idx_2301_, lean_object* v_struct_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
lean_object* v___y_2311_; lean_object* v___x_2314_; uint8_t v_debug_2315_; 
v___x_2314_ = lean_st_ref_get(v___y_2304_);
v_debug_2315_ = lean_ctor_get_uint8(v___x_2314_, sizeof(void*)*11);
lean_dec(v___x_2314_);
if (v_debug_2315_ == 0)
{
v___y_2311_ = v___y_2304_;
goto v___jp_2310_;
}
else
{
lean_object* v___x_2316_; 
v___x_2316_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_struct_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_dec_ref_known(v___x_2316_, 1);
v___y_2311_ = v___y_2304_;
goto v___jp_2310_;
}
else
{
lean_object* v_a_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2324_; 
lean_dec_ref(v_struct_2302_);
lean_dec(v_idx_2301_);
lean_dec(v_structName_2300_);
v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2319_ = v___x_2316_;
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_a_2317_);
lean_dec(v___x_2316_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2322_; 
if (v_isShared_2320_ == 0)
{
v___x_2322_ = v___x_2319_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_a_2317_);
v___x_2322_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
return v___x_2322_;
}
}
}
}
v___jp_2310_:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2312_ = l_Lean_Expr_proj___override(v_structName_2300_, v_idx_2301_, v_struct_2302_);
v___x_2313_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2312_, v___y_2311_);
return v___x_2313_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3___redArg___boxed(lean_object* v_structName_2325_, lean_object* v_idx_2326_, lean_object* v_struct_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_){
_start:
{
lean_object* v_res_2335_; 
v_res_2335_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3___redArg(v_structName_2325_, v_idx_2326_, v_struct_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3(lean_object* v_structName_2336_, lean_object* v_idx_2337_, lean_object* v_struct_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v___x_2347_; 
v___x_2347_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3___redArg(v_structName_2336_, v_idx_2337_, v_struct_2338_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3___boxed(lean_object* v_structName_2348_, lean_object* v_idx_2349_, lean_object* v_struct_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3(v_structName_2348_, v_idx_2349_, v_struct_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
lean_dec(v___y_2357_);
lean_dec_ref(v___y_2356_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v___y_2351_);
return v_res_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5_spec__5(lean_object* v_msgData_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
lean_object* v___x_2366_; lean_object* v_env_2367_; lean_object* v___x_2368_; lean_object* v_mctx_2369_; lean_object* v_lctx_2370_; lean_object* v_options_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2366_ = lean_st_ref_get(v___y_2364_);
v_env_2367_ = lean_ctor_get(v___x_2366_, 0);
lean_inc_ref(v_env_2367_);
lean_dec(v___x_2366_);
v___x_2368_ = lean_st_ref_get(v___y_2362_);
v_mctx_2369_ = lean_ctor_get(v___x_2368_, 0);
lean_inc_ref(v_mctx_2369_);
lean_dec(v___x_2368_);
v_lctx_2370_ = lean_ctor_get(v___y_2361_, 2);
v_options_2371_ = lean_ctor_get(v___y_2363_, 2);
lean_inc_ref(v_options_2371_);
lean_inc_ref(v_lctx_2370_);
v___x_2372_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2372_, 0, v_env_2367_);
lean_ctor_set(v___x_2372_, 1, v_mctx_2369_);
lean_ctor_set(v___x_2372_, 2, v_lctx_2370_);
lean_ctor_set(v___x_2372_, 3, v_options_2371_);
v___x_2373_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2372_);
lean_ctor_set(v___x_2373_, 1, v_msgData_2360_);
v___x_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2373_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5_spec__5___boxed(lean_object* v_msgData_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_){
_start:
{
lean_object* v_res_2381_; 
v_res_2381_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5_spec__5(v_msgData_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5___redArg(lean_object* v_msg_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
lean_object* v_ref_2388_; lean_object* v___x_2389_; lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2398_; 
v_ref_2388_ = lean_ctor_get(v___y_2385_, 5);
v___x_2389_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5_spec__5(v_msg_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
v_a_2390_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2392_ = v___x_2389_;
v_isShared_2393_ = v_isSharedCheck_2398_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_dec(v___x_2389_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2398_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2394_; lean_object* v___x_2396_; 
lean_inc(v_ref_2388_);
v___x_2394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2394_, 0, v_ref_2388_);
lean_ctor_set(v___x_2394_, 1, v_a_2390_);
if (v_isShared_2393_ == 0)
{
lean_ctor_set_tag(v___x_2392_, 1);
lean_ctor_set(v___x_2392_, 0, v___x_2394_);
v___x_2396_ = v___x_2392_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v___x_2394_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5___redArg___boxed(lean_object* v_msg_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5___redArg(v_msg_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
return v_res_2405_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9___redArg(lean_object* v_m_2406_, lean_object* v_query_2407_, lean_object* v_x_2408_, lean_object* v_x_2409_, lean_object* v_x_2410_){
_start:
{
lean_object* v_zero_2411_; uint8_t v_isZero_2412_; 
v_zero_2411_ = lean_unsigned_to_nat(0u);
v_isZero_2412_ = lean_nat_dec_eq(v_x_2409_, v_zero_2411_);
if (v_isZero_2412_ == 1)
{
lean_dec(v_x_2410_);
lean_dec(v_x_2409_);
if (lean_obj_tag(v_x_2408_) == 0)
{
lean_object* v___x_2413_; 
v___x_2413_ = lean_box(2);
return v___x_2413_;
}
else
{
lean_object* v_val_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2421_; 
v_val_2414_ = lean_ctor_get(v_x_2408_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v_x_2408_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2416_ = v_x_2408_;
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_val_2414_);
lean_dec(v_x_2408_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2419_; 
if (v_isShared_2417_ == 0)
{
v___x_2419_ = v___x_2416_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_val_2414_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
}
else
{
lean_object* v_keyArray_2422_; lean_object* v_valueArray_2423_; lean_object* v___x_2424_; uint8_t v_isSome_2425_; 
v_keyArray_2422_ = lean_ctor_get(v_m_2406_, 1);
v_valueArray_2423_ = lean_ctor_get(v_m_2406_, 2);
v___x_2424_ = lean_array_fget_borrowed(v_keyArray_2422_, v_x_2410_);
v_isSome_2425_ = lean_noption_is_some(v___x_2424_);
if (v_isSome_2425_ == 0)
{
lean_dec(v_x_2409_);
if (lean_obj_tag(v_x_2408_) == 0)
{
lean_object* v___x_2426_; 
v___x_2426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2426_, 0, v_x_2410_);
return v___x_2426_;
}
else
{
lean_object* v_val_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2434_; 
lean_dec(v_x_2410_);
v_val_2427_ = lean_ctor_get(v_x_2408_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v_x_2408_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2429_ = v_x_2408_;
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_val_2427_);
lean_dec(v_x_2408_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2432_; 
if (v_isShared_2430_ == 0)
{
v___x_2432_ = v___x_2429_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_val_2427_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
}
else
{
lean_object* v_one_2435_; lean_object* v_n_2436_; lean_object* v___y_2438_; 
v_one_2435_ = lean_unsigned_to_nat(1u);
v_n_2436_ = lean_nat_sub(v_x_2409_, v_one_2435_);
lean_dec(v_x_2409_);
if (v_isSome_2425_ == 0)
{
goto v___jp_2444_;
}
else
{
lean_object* v___x_2446_; uint8_t v_isSome_2447_; 
v___x_2446_ = lean_array_fget_borrowed(v_valueArray_2423_, v_x_2410_);
v_isSome_2447_ = lean_noption_is_some(v___x_2446_);
if (v_isSome_2447_ == 0)
{
goto v___jp_2444_;
}
else
{
lean_object* v_val_2448_; lean_object* v_fst_2449_; lean_object* v_snd_2450_; lean_object* v_fst_2451_; lean_object* v_snd_2452_; lean_object* v_val_2453_; uint8_t v___y_2455_; size_t v___x_2462_; size_t v___x_2463_; uint8_t v___x_2464_; 
lean_inc(v___x_2424_);
v_val_2448_ = lean_noption_get(v___x_2424_);
v_fst_2449_ = lean_ctor_get(v_val_2448_, 0);
lean_inc(v_fst_2449_);
v_snd_2450_ = lean_ctor_get(v_val_2448_, 1);
lean_inc(v_snd_2450_);
v_fst_2451_ = lean_ctor_get(v_query_2407_, 0);
v_snd_2452_ = lean_ctor_get(v_query_2407_, 1);
lean_inc(v___x_2446_);
v_val_2453_ = lean_noption_get(v___x_2446_);
v___x_2462_ = lean_ptr_addr(v_fst_2449_);
lean_dec(v_fst_2449_);
v___x_2463_ = lean_ptr_addr(v_fst_2451_);
v___x_2464_ = lean_usize_dec_eq(v___x_2462_, v___x_2463_);
if (v___x_2464_ == 0)
{
lean_dec(v_snd_2450_);
v___y_2455_ = v___x_2464_;
goto v___jp_2454_;
}
else
{
size_t v___x_2465_; size_t v___x_2466_; uint8_t v___x_2467_; 
v___x_2465_ = lean_ptr_addr(v_snd_2450_);
lean_dec(v_snd_2450_);
v___x_2466_ = lean_ptr_addr(v_snd_2452_);
v___x_2467_ = lean_usize_dec_eq(v___x_2465_, v___x_2466_);
v___y_2455_ = v___x_2467_;
goto v___jp_2454_;
}
v___jp_2454_:
{
if (v___y_2455_ == 0)
{
lean_object* v___x_2456_; lean_object* v___x_2457_; uint8_t v___x_2458_; 
lean_dec(v_val_2453_);
lean_dec(v_val_2448_);
v___x_2456_ = lean_array_get_size(v_keyArray_2422_);
v___x_2457_ = lean_nat_add(v_x_2410_, v_one_2435_);
lean_dec(v_x_2410_);
v___x_2458_ = lean_nat_dec_lt(v___x_2457_, v___x_2456_);
if (v___x_2458_ == 0)
{
lean_dec(v___x_2457_);
v_x_2409_ = v_n_2436_;
v_x_2410_ = v_zero_2411_;
goto _start;
}
else
{
v_x_2409_ = v_n_2436_;
v_x_2410_ = v___x_2457_;
goto _start;
}
}
else
{
lean_object* v___x_2461_; 
lean_dec(v_n_2436_);
lean_dec(v_x_2408_);
v___x_2461_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2461_, 0, v_x_2410_);
lean_ctor_set(v___x_2461_, 1, v_val_2448_);
lean_ctor_set(v___x_2461_, 2, v_val_2453_);
return v___x_2461_;
}
}
}
}
v___jp_2437_:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; uint8_t v___x_2441_; 
v___x_2439_ = lean_array_get_size(v_keyArray_2422_);
v___x_2440_ = lean_nat_add(v_x_2410_, v_one_2435_);
lean_dec(v_x_2410_);
v___x_2441_ = lean_nat_dec_lt(v___x_2440_, v___x_2439_);
if (v___x_2441_ == 0)
{
lean_dec(v___x_2440_);
v_x_2408_ = v___y_2438_;
v_x_2409_ = v_n_2436_;
v_x_2410_ = v_zero_2411_;
goto _start;
}
else
{
v_x_2408_ = v___y_2438_;
v_x_2409_ = v_n_2436_;
v_x_2410_ = v___x_2440_;
goto _start;
}
}
v___jp_2444_:
{
if (lean_obj_tag(v_x_2408_) == 0)
{
lean_object* v___x_2445_; 
lean_inc(v_x_2410_);
v___x_2445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2445_, 0, v_x_2410_);
v___y_2438_ = v___x_2445_;
goto v___jp_2437_;
}
else
{
v___y_2438_ = v_x_2408_;
goto v___jp_2437_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9___redArg___boxed(lean_object* v_m_2468_, lean_object* v_query_2469_, lean_object* v_x_2470_, lean_object* v_x_2471_, lean_object* v_x_2472_){
_start:
{
lean_object* v_res_2473_; 
v_res_2473_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9___redArg(v_m_2468_, v_query_2469_, v_x_2470_, v_x_2471_, v_x_2472_);
lean_dec_ref(v_query_2469_);
lean_dec_ref(v_m_2468_);
return v_res_2473_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7___redArg(lean_object* v_m_2474_, lean_object* v_query_2475_){
_start:
{
lean_object* v_keyArray_2476_; lean_object* v_fst_2477_; lean_object* v_snd_2478_; lean_object* v___x_2479_; size_t v___x_2480_; size_t v___x_2481_; size_t v___x_2482_; uint64_t v___x_2483_; size_t v___x_2484_; size_t v___x_2485_; uint64_t v___x_2486_; uint64_t v___x_2487_; uint64_t v___x_2488_; uint64_t v___x_2489_; uint64_t v_fold_2490_; uint64_t v___x_2491_; uint64_t v___x_2492_; uint64_t v___x_2493_; size_t v___x_2494_; size_t v___x_2495_; size_t v___x_2496_; size_t v___x_2497_; size_t v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; 
v_keyArray_2476_ = lean_ctor_get(v_m_2474_, 1);
v_fst_2477_ = lean_ctor_get(v_query_2475_, 0);
v_snd_2478_ = lean_ctor_get(v_query_2475_, 1);
v___x_2479_ = lean_array_get_size(v_keyArray_2476_);
v___x_2480_ = lean_ptr_addr(v_fst_2477_);
v___x_2481_ = ((size_t)3ULL);
v___x_2482_ = lean_usize_shift_right(v___x_2480_, v___x_2481_);
v___x_2483_ = lean_usize_to_uint64(v___x_2482_);
v___x_2484_ = lean_ptr_addr(v_snd_2478_);
v___x_2485_ = lean_usize_shift_right(v___x_2484_, v___x_2481_);
v___x_2486_ = lean_usize_to_uint64(v___x_2485_);
v___x_2487_ = lean_uint64_mix_hash(v___x_2483_, v___x_2486_);
v___x_2488_ = 32ULL;
v___x_2489_ = lean_uint64_shift_right(v___x_2487_, v___x_2488_);
v_fold_2490_ = lean_uint64_xor(v___x_2487_, v___x_2489_);
v___x_2491_ = 16ULL;
v___x_2492_ = lean_uint64_shift_right(v_fold_2490_, v___x_2491_);
v___x_2493_ = lean_uint64_xor(v_fold_2490_, v___x_2492_);
v___x_2494_ = lean_uint64_to_usize(v___x_2493_);
v___x_2495_ = lean_usize_of_nat(v___x_2479_);
v___x_2496_ = ((size_t)1ULL);
v___x_2497_ = lean_usize_sub(v___x_2495_, v___x_2496_);
v___x_2498_ = lean_usize_land(v___x_2494_, v___x_2497_);
v___x_2499_ = lean_usize_to_nat(v___x_2498_);
v___x_2500_ = lean_box(0);
v___x_2501_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9___redArg(v_m_2474_, v_query_2475_, v___x_2500_, v___x_2479_, v___x_2499_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7___redArg___boxed(lean_object* v_m_2502_, lean_object* v_query_2503_){
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7___redArg(v_m_2502_, v_query_2503_);
lean_dec_ref(v_query_2503_);
lean_dec_ref(v_m_2502_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7___redArg(lean_object* v_m_2505_, lean_object* v_query_2506_){
_start:
{
lean_object* v___x_2507_; 
v___x_2507_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7___redArg(v_m_2505_, v_query_2506_);
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_object* v_index_2508_; lean_object* v_key_2509_; lean_object* v_value_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2517_; 
v_index_2508_ = lean_ctor_get(v___x_2507_, 0);
v_key_2509_ = lean_ctor_get(v___x_2507_, 1);
v_value_2510_ = lean_ctor_get(v___x_2507_, 2);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2512_ = v___x_2507_;
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_value_2510_);
lean_inc(v_key_2509_);
lean_inc(v_index_2508_);
lean_dec(v___x_2507_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___x_2515_; 
if (v_isShared_2513_ == 0)
{
v___x_2515_ = v___x_2512_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_index_2508_);
lean_ctor_set(v_reuseFailAlloc_2516_, 1, v_key_2509_);
lean_ctor_set(v_reuseFailAlloc_2516_, 2, v_value_2510_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
}
else
{
lean_object* v___x_2518_; 
lean_dec(v___x_2507_);
v___x_2518_ = lean_box(1);
return v___x_2518_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7___redArg___boxed(lean_object* v_m_2519_, lean_object* v_query_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7___redArg(v_m_2519_, v_query_2520_);
lean_dec_ref(v_query_2520_);
lean_dec_ref(v_m_2519_);
return v_res_2521_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6___redArg(lean_object* v_m_2522_, lean_object* v_a_2523_){
_start:
{
lean_object* v___x_2524_; 
v___x_2524_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7___redArg(v_m_2522_, v_a_2523_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_object* v_value_2525_; lean_object* v___x_2526_; 
v_value_2525_ = lean_ctor_get(v___x_2524_, 2);
lean_inc(v_value_2525_);
lean_dec_ref_known(v___x_2524_, 3);
v___x_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2526_, 0, v_value_2525_);
return v___x_2526_;
}
else
{
lean_object* v___x_2527_; 
v___x_2527_ = lean_box(0);
return v___x_2527_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6___redArg___boxed(lean_object* v_m_2528_, lean_object* v_a_2529_){
_start:
{
lean_object* v_res_2530_; 
v_res_2530_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6___redArg(v_m_2528_, v_a_2529_);
lean_dec_ref(v_a_2529_);
lean_dec_ref(v_m_2528_);
return v_res_2530_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__8_spec__11_spec__12___redArg(lean_object* v_b_2531_, lean_object* v_acc_2532_, lean_object* v_i_2533_){
_start:
{
lean_object* v___y_2535_; lean_object* v_keyArray_2543_; lean_object* v_valueArray_2544_; lean_object* v___x_2545_; uint8_t v___x_2546_; 
v_keyArray_2543_ = lean_ctor_get(v_b_2531_, 1);
v_valueArray_2544_ = lean_ctor_get(v_b_2531_, 2);
v___x_2545_ = lean_array_get_size(v_keyArray_2543_);
v___x_2546_ = lean_nat_dec_lt(v_i_2533_, v___x_2545_);
if (v___x_2546_ == 0)
{
lean_dec(v_i_2533_);
return v_acc_2532_;
}
else
{
lean_object* v___x_2547_; uint8_t v_isSome_2548_; 
v___x_2547_ = lean_array_fget_borrowed(v_keyArray_2543_, v_i_2533_);
v_isSome_2548_ = lean_noption_is_some(v___x_2547_);
if (v_isSome_2548_ == 0)
{
goto v___jp_2539_;
}
else
{
lean_object* v___x_2549_; uint8_t v_isSome_2550_; 
v___x_2549_ = lean_array_fget_borrowed(v_valueArray_2544_, v_i_2533_);
v_isSome_2550_ = lean_noption_is_some(v___x_2549_);
if (v_isSome_2550_ == 0)
{
goto v___jp_2539_;
}
else
{
lean_object* v_val_2551_; lean_object* v_val_2552_; lean_object* v_i_2554_; lean_object* v___x_2559_; 
lean_inc(v___x_2547_);
v_val_2551_ = lean_noption_get(v___x_2547_);
lean_inc(v___x_2549_);
v_val_2552_ = lean_noption_get(v___x_2549_);
v___x_2559_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7___redArg(v_acc_2532_, v_val_2551_);
switch(lean_obj_tag(v___x_2559_))
{
case 0:
{
lean_object* v_index_2560_; lean_object* v_size_2561_; lean_object* v___x_2562_; 
v_index_2560_ = lean_ctor_get(v___x_2559_, 0);
lean_inc(v_index_2560_);
lean_dec_ref_known(v___x_2559_, 3);
v_size_2561_ = lean_ctor_get(v_acc_2532_, 0);
lean_inc(v_size_2561_);
v___x_2562_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_2532_, v_size_2561_, v_index_2560_, v_val_2551_, v_val_2552_);
lean_dec(v_index_2560_);
v___y_2535_ = v___x_2562_;
goto v___jp_2534_;
}
case 1:
{
lean_object* v_index_2563_; 
v_index_2563_ = lean_ctor_get(v___x_2559_, 0);
lean_inc(v_index_2563_);
lean_dec_ref_known(v___x_2559_, 1);
v_i_2554_ = v_index_2563_;
goto v___jp_2553_;
}
default: 
{
lean_object* v___x_2564_; lean_object* v___x_2565_; 
v___x_2564_ = lean_unsigned_to_nat(0u);
v___x_2565_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_2532_, v___x_2564_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_index_2566_; 
v_index_2566_ = lean_ctor_get(v___x_2565_, 0);
lean_inc(v_index_2566_);
lean_dec_ref_known(v___x_2565_, 1);
v_i_2554_ = v_index_2566_;
goto v___jp_2553_;
}
else
{
lean_dec(v_val_2552_);
lean_dec(v_val_2551_);
v___y_2535_ = v_acc_2532_;
goto v___jp_2534_;
}
}
}
v___jp_2553_:
{
lean_object* v_size_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
v_size_2555_ = lean_ctor_get(v_acc_2532_, 0);
v___x_2556_ = lean_unsigned_to_nat(1u);
v___x_2557_ = lean_nat_add(v_size_2555_, v___x_2556_);
v___x_2558_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_2532_, v___x_2557_, v_i_2554_, v_val_2551_, v_val_2552_);
lean_dec(v_i_2554_);
v___y_2535_ = v___x_2558_;
goto v___jp_2534_;
}
}
}
}
v___jp_2534_:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2536_ = lean_unsigned_to_nat(1u);
v___x_2537_ = lean_nat_add(v_i_2533_, v___x_2536_);
lean_dec(v_i_2533_);
v_acc_2532_ = v___y_2535_;
v_i_2533_ = v___x_2537_;
goto _start;
}
v___jp_2539_:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2540_ = lean_unsigned_to_nat(1u);
v___x_2541_ = lean_nat_add(v_i_2533_, v___x_2540_);
lean_dec(v_i_2533_);
v_i_2533_ = v___x_2541_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__8_spec__11_spec__12___redArg___boxed(lean_object* v_b_2567_, lean_object* v_acc_2568_, lean_object* v_i_2569_){
_start:
{
lean_object* v_res_2570_; 
v_res_2570_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__8_spec__11_spec__12___redArg(v_b_2567_, v_acc_2568_, v_i_2569_);
lean_dec_ref(v_b_2567_);
return v_res_2570_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__8_spec__11___redArg(lean_object* v_init_2571_, lean_object* v_b_2572_){
_start:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2573_ = lean_unsigned_to_nat(0u);
v___x_2574_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__8_spec__11_spec__12___redArg(v_b_2572_, v_init_2571_, v___x_2573_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__8_spec__11___redArg___boxed(lean_object* v_init_2575_, lean_object* v_b_2576_){
_start:
{
lean_object* v_res_2577_; 
v_res_2577_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__8_spec__11___redArg(v_init_2575_, v_b_2576_);
lean_dec_ref(v_b_2576_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__8___redArg(lean_object* v_m_2578_){
_start:
{
lean_object* v_keyArray_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v_cellCount_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v_target_2586_; lean_object* v___x_2587_; 
v_keyArray_2579_ = lean_ctor_get(v_m_2578_, 1);
v___x_2580_ = lean_array_get_size(v_keyArray_2579_);
v___x_2581_ = lean_unsigned_to_nat(2u);
v_cellCount_2582_ = lean_nat_mul(v___x_2580_, v___x_2581_);
v___x_2583_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_2582_);
v___x_2584_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_2582_);
v___x_2585_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_2582_);
v_target_2586_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_2586_, 0, v___x_2583_);
lean_ctor_set(v_target_2586_, 1, v___x_2584_);
lean_ctor_set(v_target_2586_, 2, v___x_2585_);
v___x_2587_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__8_spec__11___redArg(v_target_2586_, v_m_2578_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__8___redArg___boxed(lean_object* v_m_2588_){
_start:
{
lean_object* v_res_2589_; 
v_res_2589_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__8___redArg(v_m_2588_);
lean_dec_ref(v_m_2588_);
return v_res_2589_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2(void){
_start:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2592_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__2));
v___x_2593_ = lean_unsigned_to_nat(73u);
v___x_2594_ = lean_unsigned_to_nat(213u);
v___x_2595_ = ((lean_object*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__1));
v___x_2596_ = ((lean_object*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__0));
v___x_2597_ = l_mkPanicMessageWithDecl(v___x_2596_, v___x_2595_, v___x_2594_, v___x_2593_, v___x_2592_);
return v___x_2597_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__1(void){
_start:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2599_ = ((lean_object*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__0));
v___x_2600_ = l_Lean_stringToMessageData(v___x_2599_);
return v___x_2600_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__2(void){
_start:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2601_ = lean_unsigned_to_nat(32u);
v___x_2602_ = lean_mk_empty_array_with_capacity(v___x_2601_);
v___x_2603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2603_, 0, v___x_2602_);
return v___x_2603_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__3(void){
_start:
{
size_t v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2604_ = ((size_t)5ULL);
v___x_2605_ = lean_unsigned_to_nat(0u);
v___x_2606_ = lean_unsigned_to_nat(32u);
v___x_2607_ = lean_mk_empty_array_with_capacity(v___x_2606_);
v___x_2608_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__2);
v___x_2609_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2609_, 0, v___x_2608_);
lean_ctor_set(v___x_2609_, 1, v___x_2607_);
lean_ctor_set(v___x_2609_, 2, v___x_2605_);
lean_ctor_set(v___x_2609_, 3, v___x_2605_);
lean_ctor_set_usize(v___x_2609_, 4, v___x_2604_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(lean_object* v_xs_2610_, lean_object* v_e_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_){
_start:
{
switch(lean_obj_tag(v_e_2611_))
{
case 0:
{
lean_object* v_deBruijnIndex_2620_; lean_object* v_size_2621_; uint8_t v___x_2622_; 
v_deBruijnIndex_2620_ = lean_ctor_get(v_e_2611_, 0);
lean_inc(v_deBruijnIndex_2620_);
lean_dec_ref_known(v_e_2611_, 1);
v_size_2621_ = lean_ctor_get(v_xs_2610_, 2);
v___x_2622_ = lean_nat_dec_lt(v_deBruijnIndex_2620_, v_size_2621_);
if (v___x_2622_ == 0)
{
lean_object* v___x_2623_; lean_object* v___x_2624_; 
lean_dec(v_deBruijnIndex_2620_);
lean_dec_ref(v_xs_2610_);
v___x_2623_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__1, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__1_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__1);
v___x_2624_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5___redArg(v___x_2623_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_);
return v___x_2624_;
}
else
{
lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2625_ = l_Lean_instInhabitedExpr;
v___x_2626_ = lean_nat_sub(v_size_2621_, v_deBruijnIndex_2620_);
lean_dec(v_deBruijnIndex_2620_);
v___x_2627_ = lean_unsigned_to_nat(1u);
v___x_2628_ = lean_nat_sub(v___x_2626_, v___x_2627_);
lean_dec(v___x_2626_);
v___x_2629_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2625_, v_xs_2610_, v___x_2628_);
lean_dec(v___x_2628_);
lean_dec_ref(v_xs_2610_);
v___x_2630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2630_, 0, v___x_2629_);
return v___x_2630_;
}
}
case 1:
{
lean_object* v___x_2631_; 
lean_dec_ref(v_xs_2610_);
v___x_2631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2631_, 0, v_e_2611_);
return v___x_2631_;
}
case 2:
{
lean_object* v___x_2632_; 
lean_dec_ref(v_xs_2610_);
v___x_2632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2632_, 0, v_e_2611_);
return v___x_2632_;
}
case 3:
{
lean_object* v___x_2633_; 
lean_dec_ref(v_xs_2610_);
v___x_2633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2633_, 0, v_e_2611_);
return v___x_2633_;
}
case 4:
{
lean_object* v___x_2634_; 
lean_dec_ref(v_xs_2610_);
v___x_2634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2634_, 0, v_e_2611_);
return v___x_2634_;
}
case 9:
{
lean_object* v___x_2635_; 
lean_dec_ref(v_xs_2610_);
v___x_2635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2635_, 0, v_e_2611_);
return v___x_2635_;
}
default: 
{
uint8_t v___x_2636_; 
v___x_2636_ = l_Lean_Expr_hasLooseBVars(v_e_2611_);
if (v___x_2636_ == 0)
{
lean_object* v___x_2637_; 
lean_dec_ref(v_xs_2610_);
lean_inc_ref(v_e_2611_);
v___x_2637_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet(v_e_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_);
if (lean_obj_tag(v___x_2637_) == 0)
{
lean_object* v_a_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2742_; 
v_a_2638_ = lean_ctor_get(v___x_2637_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2637_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2640_ = v___x_2637_;
v_isShared_2641_ = v_isSharedCheck_2742_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_a_2638_);
lean_dec(v___x_2637_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2742_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
uint8_t v___x_2642_; 
v___x_2642_ = lean_unbox(v_a_2638_);
lean_dec(v_a_2638_);
if (v___x_2642_ == 0)
{
lean_object* v___x_2644_; 
if (v_isShared_2641_ == 0)
{
lean_ctor_set(v___x_2640_, 0, v_e_2611_);
v___x_2644_ = v___x_2640_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_e_2611_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
else
{
lean_object* v___x_2646_; lean_object* v_cacheClosed_2647_; lean_object* v___x_2648_; 
v___x_2646_ = lean_st_ref_get(v_a_2612_);
v_cacheClosed_2647_ = lean_ctor_get(v___x_2646_, 1);
lean_inc_ref(v_cacheClosed_2647_);
lean_dec(v___x_2646_);
v___x_2648_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0___redArg(v_cacheClosed_2647_, v_e_2611_);
lean_dec_ref(v_cacheClosed_2647_);
if (lean_obj_tag(v___x_2648_) == 1)
{
lean_object* v_val_2649_; lean_object* v___x_2651_; 
lean_dec_ref(v_e_2611_);
v_val_2649_ = lean_ctor_get(v___x_2648_, 0);
lean_inc(v_val_2649_);
lean_dec_ref_known(v___x_2648_, 1);
if (v_isShared_2641_ == 0)
{
lean_ctor_set(v___x_2640_, 0, v_val_2649_);
v___x_2651_ = v___x_2640_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_val_2649_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
else
{
lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; 
lean_dec(v___x_2648_);
lean_del_object(v___x_2640_);
v___x_2653_ = lean_unsigned_to_nat(0u);
v___x_2654_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__3, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__3_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__3);
lean_inc_ref(v_e_2611_);
v___x_2655_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit(v___x_2654_, v_e_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v_a_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2741_; 
v_a_2656_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2658_ = v___x_2655_;
v_isShared_2659_ = v_isSharedCheck_2741_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_a_2656_);
lean_dec(v___x_2655_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2741_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___x_2660_; lean_object* v_cache_2661_; lean_object* v_cacheClosed_2662_; lean_object* v_hasLetCache_2663_; lean_object* v_decls_2664_; lean_object* v_valueMap_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2740_; 
v___x_2660_ = lean_st_ref_take(v_a_2612_);
v_cache_2661_ = lean_ctor_get(v___x_2660_, 0);
v_cacheClosed_2662_ = lean_ctor_get(v___x_2660_, 1);
v_hasLetCache_2663_ = lean_ctor_get(v___x_2660_, 2);
v_decls_2664_ = lean_ctor_get(v___x_2660_, 3);
v_valueMap_2665_ = lean_ctor_get(v___x_2660_, 4);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___x_2660_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2667_ = v___x_2660_;
v_isShared_2668_ = v_isSharedCheck_2740_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_valueMap_2665_);
lean_inc(v_decls_2664_);
lean_inc(v_hasLetCache_2663_);
lean_inc(v_cacheClosed_2662_);
lean_inc(v_cache_2661_);
lean_dec(v___x_2660_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2740_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___y_2670_; lean_object* v___y_2679_; lean_object* v_i_2680_; lean_object* v___y_2695_; lean_object* v_i_2696_; lean_object* v___y_2702_; lean_object* v___x_2710_; 
v___x_2710_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1___redArg(v_cacheClosed_2662_, v_e_2611_);
switch(lean_obj_tag(v___x_2710_))
{
case 0:
{
lean_object* v_index_2711_; lean_object* v_size_2712_; lean_object* v___x_2713_; 
v_index_2711_ = lean_ctor_get(v___x_2710_, 0);
lean_inc(v_index_2711_);
lean_dec_ref_known(v___x_2710_, 3);
v_size_2712_ = lean_ctor_get(v_cacheClosed_2662_, 0);
lean_inc(v_size_2712_);
lean_inc(v_a_2656_);
v___x_2713_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cacheClosed_2662_, v_size_2712_, v_index_2711_, v_e_2611_, v_a_2656_);
lean_dec(v_index_2711_);
v___y_2670_ = v___x_2713_;
goto v___jp_2669_;
}
case 1:
{
lean_object* v_index_2714_; lean_object* v_size_2715_; lean_object* v_keyArray_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; uint8_t v___x_2720_; 
v_index_2714_ = lean_ctor_get(v___x_2710_, 0);
lean_inc(v_index_2714_);
lean_dec_ref_known(v___x_2710_, 1);
v_size_2715_ = lean_ctor_get(v_cacheClosed_2662_, 0);
v_keyArray_2716_ = lean_ctor_get(v_cacheClosed_2662_, 1);
v___x_2717_ = lean_unsigned_to_nat(1u);
v___x_2718_ = lean_nat_add(v_size_2715_, v___x_2717_);
v___x_2719_ = lean_array_get_size(v_keyArray_2716_);
v___x_2720_ = lean_nat_dec_lt(v___x_2718_, v___x_2719_);
if (v___x_2720_ == 0)
{
lean_dec(v___x_2718_);
lean_dec(v_index_2714_);
goto v___jp_2685_;
}
else
{
lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; uint8_t v___x_2725_; 
v___x_2721_ = lean_unsigned_to_nat(4u);
v___x_2722_ = lean_nat_mul(v___x_2718_, v___x_2721_);
v___x_2723_ = lean_unsigned_to_nat(3u);
v___x_2724_ = lean_nat_mul(v___x_2719_, v___x_2723_);
v___x_2725_ = lean_nat_dec_le(v___x_2722_, v___x_2724_);
lean_dec(v___x_2724_);
lean_dec(v___x_2722_);
if (v___x_2725_ == 0)
{
lean_dec(v___x_2718_);
lean_dec(v_index_2714_);
goto v___jp_2685_;
}
else
{
lean_object* v___x_2726_; 
lean_inc(v_a_2656_);
v___x_2726_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cacheClosed_2662_, v___x_2718_, v_index_2714_, v_e_2611_, v_a_2656_);
lean_dec(v_index_2714_);
v___y_2670_ = v___x_2726_;
goto v___jp_2669_;
}
}
}
default: 
{
lean_object* v_size_2727_; lean_object* v_keyArray_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; uint8_t v___x_2732_; 
v_size_2727_ = lean_ctor_get(v_cacheClosed_2662_, 0);
v_keyArray_2728_ = lean_ctor_get(v_cacheClosed_2662_, 1);
v___x_2729_ = lean_unsigned_to_nat(1u);
v___x_2730_ = lean_nat_add(v_size_2727_, v___x_2729_);
v___x_2731_ = lean_array_get_size(v_keyArray_2728_);
v___x_2732_ = lean_nat_dec_lt(v___x_2730_, v___x_2731_);
if (v___x_2732_ == 0)
{
lean_object* v___x_2733_; 
lean_dec(v___x_2730_);
v___x_2733_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__2___redArg(v_cacheClosed_2662_);
lean_dec_ref(v_cacheClosed_2662_);
v___y_2702_ = v___x_2733_;
goto v___jp_2701_;
}
else
{
lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; uint8_t v___x_2738_; 
v___x_2734_ = lean_unsigned_to_nat(4u);
v___x_2735_ = lean_nat_mul(v___x_2730_, v___x_2734_);
lean_dec(v___x_2730_);
v___x_2736_ = lean_unsigned_to_nat(3u);
v___x_2737_ = lean_nat_mul(v___x_2731_, v___x_2736_);
v___x_2738_ = lean_nat_dec_le(v___x_2735_, v___x_2737_);
lean_dec(v___x_2737_);
lean_dec(v___x_2735_);
if (v___x_2738_ == 0)
{
lean_object* v___x_2739_; 
v___x_2739_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__2___redArg(v_cacheClosed_2662_);
lean_dec_ref(v_cacheClosed_2662_);
v___y_2702_ = v___x_2739_;
goto v___jp_2701_;
}
else
{
v___y_2702_ = v_cacheClosed_2662_;
goto v___jp_2701_;
}
}
}
}
v___jp_2669_:
{
lean_object* v___x_2672_; 
if (v_isShared_2668_ == 0)
{
lean_ctor_set(v___x_2667_, 1, v___y_2670_);
v___x_2672_ = v___x_2667_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_cache_2661_);
lean_ctor_set(v_reuseFailAlloc_2677_, 1, v___y_2670_);
lean_ctor_set(v_reuseFailAlloc_2677_, 2, v_hasLetCache_2663_);
lean_ctor_set(v_reuseFailAlloc_2677_, 3, v_decls_2664_);
lean_ctor_set(v_reuseFailAlloc_2677_, 4, v_valueMap_2665_);
v___x_2672_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
lean_object* v___x_2673_; lean_object* v___x_2675_; 
v___x_2673_ = lean_st_ref_put(v_a_2612_, v___x_2672_);
if (v_isShared_2659_ == 0)
{
v___x_2675_ = v___x_2658_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_a_2656_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
v___jp_2678_:
{
lean_object* v_size_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
v_size_2681_ = lean_ctor_get(v___y_2679_, 0);
v___x_2682_ = lean_unsigned_to_nat(1u);
v___x_2683_ = lean_nat_add(v_size_2681_, v___x_2682_);
lean_inc(v_a_2656_);
v___x_2684_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2679_, v___x_2683_, v_i_2680_, v_e_2611_, v_a_2656_);
lean_dec(v_i_2680_);
v___y_2670_ = v___x_2684_;
goto v___jp_2669_;
}
v___jp_2685_:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; 
v___x_2686_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__2___redArg(v_cacheClosed_2662_);
lean_dec_ref(v_cacheClosed_2662_);
v___x_2687_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1___redArg(v___x_2686_, v_e_2611_);
switch(lean_obj_tag(v___x_2687_))
{
case 0:
{
lean_object* v_index_2688_; lean_object* v_size_2689_; lean_object* v___x_2690_; 
v_index_2688_ = lean_ctor_get(v___x_2687_, 0);
lean_inc(v_index_2688_);
lean_dec_ref_known(v___x_2687_, 3);
v_size_2689_ = lean_ctor_get(v___x_2686_, 0);
lean_inc(v_size_2689_);
lean_inc(v_a_2656_);
v___x_2690_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2686_, v_size_2689_, v_index_2688_, v_e_2611_, v_a_2656_);
lean_dec(v_index_2688_);
v___y_2670_ = v___x_2690_;
goto v___jp_2669_;
}
case 1:
{
lean_object* v_index_2691_; 
v_index_2691_ = lean_ctor_get(v___x_2687_, 0);
lean_inc(v_index_2691_);
lean_dec_ref_known(v___x_2687_, 1);
v___y_2679_ = v___x_2686_;
v_i_2680_ = v_index_2691_;
goto v___jp_2678_;
}
default: 
{
lean_object* v___x_2692_; 
v___x_2692_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2686_, v___x_2653_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v_index_2693_; 
v_index_2693_ = lean_ctor_get(v___x_2692_, 0);
lean_inc(v_index_2693_);
lean_dec_ref_known(v___x_2692_, 1);
v___y_2679_ = v___x_2686_;
v_i_2680_ = v_index_2693_;
goto v___jp_2678_;
}
else
{
lean_dec_ref(v_e_2611_);
v___y_2670_ = v___x_2686_;
goto v___jp_2669_;
}
}
}
}
v___jp_2694_:
{
lean_object* v_size_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
v_size_2697_ = lean_ctor_get(v___y_2695_, 0);
v___x_2698_ = lean_unsigned_to_nat(1u);
v___x_2699_ = lean_nat_add(v_size_2697_, v___x_2698_);
lean_inc(v_a_2656_);
v___x_2700_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2695_, v___x_2699_, v_i_2696_, v_e_2611_, v_a_2656_);
lean_dec(v_i_2696_);
v___y_2670_ = v___x_2700_;
goto v___jp_2669_;
}
v___jp_2701_:
{
lean_object* v___x_2703_; 
v___x_2703_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1___redArg(v___y_2702_, v_e_2611_);
switch(lean_obj_tag(v___x_2703_))
{
case 0:
{
lean_object* v_index_2704_; lean_object* v_size_2705_; lean_object* v___x_2706_; 
v_index_2704_ = lean_ctor_get(v___x_2703_, 0);
lean_inc(v_index_2704_);
lean_dec_ref_known(v___x_2703_, 3);
v_size_2705_ = lean_ctor_get(v___y_2702_, 0);
lean_inc(v_size_2705_);
lean_inc(v_a_2656_);
v___x_2706_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2702_, v_size_2705_, v_index_2704_, v_e_2611_, v_a_2656_);
lean_dec(v_index_2704_);
v___y_2670_ = v___x_2706_;
goto v___jp_2669_;
}
case 1:
{
lean_object* v_index_2707_; 
v_index_2707_ = lean_ctor_get(v___x_2703_, 0);
lean_inc(v_index_2707_);
lean_dec_ref_known(v___x_2703_, 1);
v___y_2695_ = v___y_2702_;
v_i_2696_ = v_index_2707_;
goto v___jp_2694_;
}
default: 
{
lean_object* v___x_2708_; 
v___x_2708_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2702_, v___x_2653_);
if (lean_obj_tag(v___x_2708_) == 0)
{
lean_object* v_index_2709_; 
v_index_2709_ = lean_ctor_get(v___x_2708_, 0);
lean_inc(v_index_2709_);
lean_dec_ref_known(v___x_2708_, 1);
v___y_2695_ = v___y_2702_;
v_i_2696_ = v_index_2709_;
goto v___jp_2694_;
}
else
{
lean_dec_ref(v_e_2611_);
v___y_2670_ = v___y_2702_;
goto v___jp_2669_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2611_);
return v___x_2655_;
}
}
}
}
}
else
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2750_; 
lean_dec_ref(v_e_2611_);
v_a_2743_ = lean_ctor_get(v___x_2637_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2637_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2745_ = v___x_2637_;
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2637_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2748_; 
if (v_isShared_2746_ == 0)
{
v___x_2748_ = v___x_2745_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_a_2743_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
else
{
lean_object* v___x_2751_; lean_object* v_cache_2752_; lean_object* v_key_2753_; lean_object* v___x_2754_; 
v___x_2751_ = lean_st_ref_get(v_a_2612_);
v_cache_2752_ = lean_ctor_get(v___x_2751_, 0);
lean_inc_ref(v_cache_2752_);
lean_dec(v___x_2751_);
lean_inc_ref(v_e_2611_);
lean_inc_ref(v_xs_2610_);
v_key_2753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_2753_, 0, v_xs_2610_);
lean_ctor_set(v_key_2753_, 1, v_e_2611_);
v___x_2754_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6___redArg(v_cache_2752_, v_key_2753_);
lean_dec_ref(v_cache_2752_);
if (lean_obj_tag(v___x_2754_) == 1)
{
lean_object* v_val_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
lean_dec_ref_known(v_key_2753_, 2);
lean_dec_ref(v_e_2611_);
lean_dec_ref(v_xs_2610_);
v_val_2755_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2757_ = v___x_2754_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_val_2755_);
lean_dec(v___x_2754_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2760_; 
if (v_isShared_2758_ == 0)
{
lean_ctor_set_tag(v___x_2757_, 0);
v___x_2760_ = v___x_2757_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_val_2755_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
else
{
lean_object* v___x_2763_; 
lean_dec(v___x_2754_);
v___x_2763_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit(v_xs_2610_, v_e_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_);
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2851_; 
v_a_2764_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2766_ = v___x_2763_;
v_isShared_2767_ = v_isSharedCheck_2851_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2763_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2851_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2768_; lean_object* v_cache_2769_; lean_object* v_cacheClosed_2770_; lean_object* v_hasLetCache_2771_; lean_object* v_decls_2772_; lean_object* v_valueMap_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2850_; 
v___x_2768_ = lean_st_ref_take(v_a_2612_);
v_cache_2769_ = lean_ctor_get(v___x_2768_, 0);
v_cacheClosed_2770_ = lean_ctor_get(v___x_2768_, 1);
v_hasLetCache_2771_ = lean_ctor_get(v___x_2768_, 2);
v_decls_2772_ = lean_ctor_get(v___x_2768_, 3);
v_valueMap_2773_ = lean_ctor_get(v___x_2768_, 4);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2768_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2775_ = v___x_2768_;
v_isShared_2776_ = v_isSharedCheck_2850_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_valueMap_2773_);
lean_inc(v_decls_2772_);
lean_inc(v_hasLetCache_2771_);
lean_inc(v_cacheClosed_2770_);
lean_inc(v_cache_2769_);
lean_dec(v___x_2768_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2850_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v___y_2778_; lean_object* v___y_2787_; lean_object* v_i_2788_; lean_object* v___y_2794_; lean_object* v___y_2804_; lean_object* v_i_2805_; lean_object* v___x_2820_; 
v___x_2820_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7___redArg(v_cache_2769_, v_key_2753_);
switch(lean_obj_tag(v___x_2820_))
{
case 0:
{
lean_object* v_index_2821_; lean_object* v_size_2822_; lean_object* v___x_2823_; 
v_index_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_index_2821_);
lean_dec_ref_known(v___x_2820_, 3);
v_size_2822_ = lean_ctor_get(v_cache_2769_, 0);
lean_inc(v_size_2822_);
lean_inc(v_a_2764_);
v___x_2823_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cache_2769_, v_size_2822_, v_index_2821_, v_key_2753_, v_a_2764_);
lean_dec(v_index_2821_);
v___y_2778_ = v___x_2823_;
goto v___jp_2777_;
}
case 1:
{
lean_object* v_index_2824_; lean_object* v_size_2825_; lean_object* v_keyArray_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; uint8_t v___x_2830_; 
v_index_2824_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_index_2824_);
lean_dec_ref_known(v___x_2820_, 1);
v_size_2825_ = lean_ctor_get(v_cache_2769_, 0);
v_keyArray_2826_ = lean_ctor_get(v_cache_2769_, 1);
v___x_2827_ = lean_unsigned_to_nat(1u);
v___x_2828_ = lean_nat_add(v_size_2825_, v___x_2827_);
v___x_2829_ = lean_array_get_size(v_keyArray_2826_);
v___x_2830_ = lean_nat_dec_lt(v___x_2828_, v___x_2829_);
if (v___x_2830_ == 0)
{
lean_dec(v___x_2828_);
lean_dec(v_index_2824_);
goto v___jp_2810_;
}
else
{
lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; uint8_t v___x_2835_; 
v___x_2831_ = lean_unsigned_to_nat(4u);
v___x_2832_ = lean_nat_mul(v___x_2828_, v___x_2831_);
v___x_2833_ = lean_unsigned_to_nat(3u);
v___x_2834_ = lean_nat_mul(v___x_2829_, v___x_2833_);
v___x_2835_ = lean_nat_dec_le(v___x_2832_, v___x_2834_);
lean_dec(v___x_2834_);
lean_dec(v___x_2832_);
if (v___x_2835_ == 0)
{
lean_dec(v___x_2828_);
lean_dec(v_index_2824_);
goto v___jp_2810_;
}
else
{
lean_object* v___x_2836_; 
lean_inc(v_a_2764_);
v___x_2836_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cache_2769_, v___x_2828_, v_index_2824_, v_key_2753_, v_a_2764_);
lean_dec(v_index_2824_);
v___y_2778_ = v___x_2836_;
goto v___jp_2777_;
}
}
}
default: 
{
lean_object* v_size_2837_; lean_object* v_keyArray_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; uint8_t v___x_2842_; 
v_size_2837_ = lean_ctor_get(v_cache_2769_, 0);
v_keyArray_2838_ = lean_ctor_get(v_cache_2769_, 1);
v___x_2839_ = lean_unsigned_to_nat(1u);
v___x_2840_ = lean_nat_add(v_size_2837_, v___x_2839_);
v___x_2841_ = lean_array_get_size(v_keyArray_2838_);
v___x_2842_ = lean_nat_dec_lt(v___x_2840_, v___x_2841_);
if (v___x_2842_ == 0)
{
lean_object* v___x_2843_; 
lean_dec(v___x_2840_);
v___x_2843_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__8___redArg(v_cache_2769_);
lean_dec_ref(v_cache_2769_);
v___y_2794_ = v___x_2843_;
goto v___jp_2793_;
}
else
{
lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; uint8_t v___x_2848_; 
v___x_2844_ = lean_unsigned_to_nat(4u);
v___x_2845_ = lean_nat_mul(v___x_2840_, v___x_2844_);
lean_dec(v___x_2840_);
v___x_2846_ = lean_unsigned_to_nat(3u);
v___x_2847_ = lean_nat_mul(v___x_2841_, v___x_2846_);
v___x_2848_ = lean_nat_dec_le(v___x_2845_, v___x_2847_);
lean_dec(v___x_2847_);
lean_dec(v___x_2845_);
if (v___x_2848_ == 0)
{
lean_object* v___x_2849_; 
v___x_2849_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__8___redArg(v_cache_2769_);
lean_dec_ref(v_cache_2769_);
v___y_2794_ = v___x_2849_;
goto v___jp_2793_;
}
else
{
v___y_2794_ = v_cache_2769_;
goto v___jp_2793_;
}
}
}
}
v___jp_2777_:
{
lean_object* v___x_2780_; 
if (v_isShared_2776_ == 0)
{
lean_ctor_set(v___x_2775_, 0, v___y_2778_);
v___x_2780_ = v___x_2775_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v___y_2778_);
lean_ctor_set(v_reuseFailAlloc_2785_, 1, v_cacheClosed_2770_);
lean_ctor_set(v_reuseFailAlloc_2785_, 2, v_hasLetCache_2771_);
lean_ctor_set(v_reuseFailAlloc_2785_, 3, v_decls_2772_);
lean_ctor_set(v_reuseFailAlloc_2785_, 4, v_valueMap_2773_);
v___x_2780_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
lean_object* v___x_2781_; lean_object* v___x_2783_; 
v___x_2781_ = lean_st_ref_put(v_a_2612_, v___x_2780_);
if (v_isShared_2767_ == 0)
{
v___x_2783_ = v___x_2766_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_a_2764_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
}
v___jp_2786_:
{
lean_object* v_size_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; 
v_size_2789_ = lean_ctor_get(v___y_2787_, 0);
v___x_2790_ = lean_unsigned_to_nat(1u);
v___x_2791_ = lean_nat_add(v_size_2789_, v___x_2790_);
lean_inc(v_a_2764_);
v___x_2792_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2787_, v___x_2791_, v_i_2788_, v_key_2753_, v_a_2764_);
lean_dec(v_i_2788_);
v___y_2778_ = v___x_2792_;
goto v___jp_2777_;
}
v___jp_2793_:
{
lean_object* v___x_2795_; 
v___x_2795_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7___redArg(v___y_2794_, v_key_2753_);
switch(lean_obj_tag(v___x_2795_))
{
case 0:
{
lean_object* v_index_2796_; lean_object* v_size_2797_; lean_object* v___x_2798_; 
v_index_2796_ = lean_ctor_get(v___x_2795_, 0);
lean_inc(v_index_2796_);
lean_dec_ref_known(v___x_2795_, 3);
v_size_2797_ = lean_ctor_get(v___y_2794_, 0);
lean_inc(v_size_2797_);
lean_inc(v_a_2764_);
v___x_2798_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2794_, v_size_2797_, v_index_2796_, v_key_2753_, v_a_2764_);
lean_dec(v_index_2796_);
v___y_2778_ = v___x_2798_;
goto v___jp_2777_;
}
case 1:
{
lean_object* v_index_2799_; 
v_index_2799_ = lean_ctor_get(v___x_2795_, 0);
lean_inc(v_index_2799_);
lean_dec_ref_known(v___x_2795_, 1);
v___y_2787_ = v___y_2794_;
v_i_2788_ = v_index_2799_;
goto v___jp_2786_;
}
default: 
{
lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2800_ = lean_unsigned_to_nat(0u);
v___x_2801_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2794_, v___x_2800_);
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_object* v_index_2802_; 
v_index_2802_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_index_2802_);
lean_dec_ref_known(v___x_2801_, 1);
v___y_2787_ = v___y_2794_;
v_i_2788_ = v_index_2802_;
goto v___jp_2786_;
}
else
{
lean_dec_ref_known(v_key_2753_, 2);
v___y_2778_ = v___y_2794_;
goto v___jp_2777_;
}
}
}
}
v___jp_2803_:
{
lean_object* v_size_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; 
v_size_2806_ = lean_ctor_get(v___y_2804_, 0);
v___x_2807_ = lean_unsigned_to_nat(1u);
v___x_2808_ = lean_nat_add(v_size_2806_, v___x_2807_);
lean_inc(v_a_2764_);
v___x_2809_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2804_, v___x_2808_, v_i_2805_, v_key_2753_, v_a_2764_);
lean_dec(v_i_2805_);
v___y_2778_ = v___x_2809_;
goto v___jp_2777_;
}
v___jp_2810_:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2811_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__8___redArg(v_cache_2769_);
lean_dec_ref(v_cache_2769_);
v___x_2812_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7___redArg(v___x_2811_, v_key_2753_);
switch(lean_obj_tag(v___x_2812_))
{
case 0:
{
lean_object* v_index_2813_; lean_object* v_size_2814_; lean_object* v___x_2815_; 
v_index_2813_ = lean_ctor_get(v___x_2812_, 0);
lean_inc(v_index_2813_);
lean_dec_ref_known(v___x_2812_, 3);
v_size_2814_ = lean_ctor_get(v___x_2811_, 0);
lean_inc(v_size_2814_);
lean_inc(v_a_2764_);
v___x_2815_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2811_, v_size_2814_, v_index_2813_, v_key_2753_, v_a_2764_);
lean_dec(v_index_2813_);
v___y_2778_ = v___x_2815_;
goto v___jp_2777_;
}
case 1:
{
lean_object* v_index_2816_; 
v_index_2816_ = lean_ctor_get(v___x_2812_, 0);
lean_inc(v_index_2816_);
lean_dec_ref_known(v___x_2812_, 1);
v___y_2804_ = v___x_2811_;
v_i_2805_ = v_index_2816_;
goto v___jp_2803_;
}
default: 
{
lean_object* v___x_2817_; lean_object* v___x_2818_; 
v___x_2817_ = lean_unsigned_to_nat(0u);
v___x_2818_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2811_, v___x_2817_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v_index_2819_; 
v_index_2819_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_index_2819_);
lean_dec_ref_known(v___x_2818_, 1);
v___y_2804_ = v___x_2811_;
v_i_2805_ = v_index_2819_;
goto v___jp_2803_;
}
else
{
lean_dec_ref_known(v_key_2753_, 2);
v___y_2778_ = v___x_2811_;
goto v___jp_2777_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_2753_, 2);
return v___x_2763_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit(lean_object* v_xs_2852_, lean_object* v_e_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_){
_start:
{
switch(lean_obj_tag(v_e_2853_))
{
case 0:
{
lean_object* v___x_2862_; lean_object* v___x_2863_; 
lean_dec_ref_known(v_e_2853_, 1);
lean_dec_ref(v_xs_2852_);
v___x_2862_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2);
v___x_2863_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(v___x_2862_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_);
return v___x_2863_;
}
case 1:
{
lean_object* v___x_2864_; lean_object* v___x_2865_; 
lean_dec_ref_known(v_e_2853_, 1);
lean_dec_ref(v_xs_2852_);
v___x_2864_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2);
v___x_2865_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(v___x_2864_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_);
return v___x_2865_;
}
case 2:
{
lean_object* v___x_2866_; lean_object* v___x_2867_; 
lean_dec_ref_known(v_e_2853_, 1);
lean_dec_ref(v_xs_2852_);
v___x_2866_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2);
v___x_2867_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(v___x_2866_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_);
return v___x_2867_;
}
case 3:
{
lean_object* v___x_2868_; lean_object* v___x_2869_; 
lean_dec_ref_known(v_e_2853_, 1);
lean_dec_ref(v_xs_2852_);
v___x_2868_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2);
v___x_2869_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(v___x_2868_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_);
return v___x_2869_;
}
case 4:
{
lean_object* v___x_2870_; lean_object* v___x_2871_; 
lean_dec_ref_known(v_e_2853_, 2);
lean_dec_ref(v_xs_2852_);
v___x_2870_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2);
v___x_2871_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(v___x_2870_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_);
return v___x_2871_;
}
case 5:
{
lean_object* v_fn_2872_; lean_object* v_arg_2873_; lean_object* v___x_2874_; 
v_fn_2872_ = lean_ctor_get(v_e_2853_, 0);
v_arg_2873_ = lean_ctor_get(v_e_2853_, 1);
lean_inc_ref(v_fn_2872_);
lean_inc_ref(v_xs_2852_);
v___x_2874_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v_xs_2852_, v_fn_2872_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_);
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_object* v_a_2875_; lean_object* v___x_2876_; 
v_a_2875_ = lean_ctor_get(v___x_2874_, 0);
lean_inc(v_a_2875_);
lean_dec_ref_known(v___x_2874_, 1);
lean_inc_ref(v_arg_2873_);
v___x_2876_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v_xs_2852_, v_arg_2873_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_);
if (lean_obj_tag(v___x_2876_) == 0)
{
lean_object* v_a_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2893_; 
v_a_2877_ = lean_ctor_get(v___x_2876_, 0);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2879_ = v___x_2876_;
v_isShared_2880_ = v_isSharedCheck_2893_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_a_2877_);
lean_dec(v___x_2876_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2893_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
uint8_t v___y_2882_; size_t v___x_2887_; size_t v___x_2888_; uint8_t v___x_2889_; 
v___x_2887_ = lean_ptr_addr(v_fn_2872_);
v___x_2888_ = lean_ptr_addr(v_a_2875_);
v___x_2889_ = lean_usize_dec_eq(v___x_2887_, v___x_2888_);
if (v___x_2889_ == 0)
{
v___y_2882_ = v___x_2889_;
goto v___jp_2881_;
}
else
{
size_t v___x_2890_; size_t v___x_2891_; uint8_t v___x_2892_; 
v___x_2890_ = lean_ptr_addr(v_arg_2873_);
v___x_2891_ = lean_ptr_addr(v_a_2877_);
v___x_2892_ = lean_usize_dec_eq(v___x_2890_, v___x_2891_);
v___y_2882_ = v___x_2892_;
goto v___jp_2881_;
}
v___jp_2881_:
{
if (v___y_2882_ == 0)
{
lean_object* v___x_2883_; 
lean_del_object(v___x_2879_);
lean_dec_ref_known(v_e_2853_, 2);
v___x_2883_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1___redArg(v_a_2875_, v_a_2877_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_);
return v___x_2883_;
}
else
{
lean_object* v___x_2885_; 
lean_dec(v_a_2877_);
lean_dec(v_a_2875_);
if (v_isShared_2880_ == 0)
{
lean_ctor_set(v___x_2879_, 0, v_e_2853_);
v___x_2885_ = v___x_2879_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_e_2853_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
}
}
else
{
lean_dec(v_a_2875_);
lean_dec_ref_known(v_e_2853_, 2);
return v___x_2876_;
}
}
else
{
lean_dec_ref_known(v_e_2853_, 2);
lean_dec_ref(v_xs_2852_);
return v___x_2874_;
}
}
case 8:
{
lean_object* v_declName_2894_; lean_object* v_type_2895_; lean_object* v_value_2896_; lean_object* v_body_2897_; uint8_t v_nondep_2898_; lean_object* v___x_2899_; 
v_declName_2894_ = lean_ctor_get(v_e_2853_, 0);
lean_inc(v_declName_2894_);
v_type_2895_ = lean_ctor_get(v_e_2853_, 1);
lean_inc_ref(v_type_2895_);
v_value_2896_ = lean_ctor_get(v_e_2853_, 2);
lean_inc_ref(v_value_2896_);
v_body_2897_ = lean_ctor_get(v_e_2853_, 3);
lean_inc_ref(v_body_2897_);
v_nondep_2898_ = lean_ctor_get_uint8(v_e_2853_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2853_, 4);
lean_inc_ref(v_xs_2852_);
v___x_2899_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v_xs_2852_, v_type_2895_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_object* v_a_2900_; lean_object* v___x_2901_; 
v_a_2900_ = lean_ctor_get(v___x_2899_, 0);
lean_inc(v_a_2900_);
lean_dec_ref_known(v___x_2899_, 1);
lean_inc_ref(v_xs_2852_);
v___x_2901_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v_xs_2852_, v_value_2896_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_);
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_object* v_a_2902_; lean_object* v___x_2903_; 
v_a_2902_ = lean_ctor_get(v___x_2901_, 0);
lean_inc(v_a_2902_);
lean_dec_ref_known(v___x_2901_, 1);
v___x_2903_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl(v_declName_2894_, v_a_2900_, v_a_2902_, v_nondep_2898_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
lean_inc(v_a_2904_);
lean_dec_ref_known(v___x_2903_, 1);
v___x_2905_ = l_Lean_PersistentArray_push___redArg(v_xs_2852_, v_a_2904_);
v___x_2906_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v___x_2905_, v_body_2897_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_);
return v___x_2906_;
}
else
{
lean_dec_ref(v_body_2897_);
lean_dec_ref(v_xs_2852_);
return v___x_2903_;
}
}
else
{
lean_dec(v_a_2900_);
lean_dec_ref(v_body_2897_);
lean_dec(v_declName_2894_);
lean_dec_ref(v_xs_2852_);
return v___x_2901_;
}
}
else
{
lean_dec_ref(v_body_2897_);
lean_dec_ref(v_value_2896_);
lean_dec(v_declName_2894_);
lean_dec_ref(v_xs_2852_);
return v___x_2899_;
}
}
case 9:
{
lean_object* v___x_2907_; lean_object* v___x_2908_; 
lean_dec_ref_known(v_e_2853_, 1);
lean_dec_ref(v_xs_2852_);
v___x_2907_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2);
v___x_2908_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(v___x_2907_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_);
return v___x_2908_;
}
case 10:
{
lean_object* v_data_2909_; lean_object* v_expr_2910_; lean_object* v___x_2911_; 
v_data_2909_ = lean_ctor_get(v_e_2853_, 0);
v_expr_2910_ = lean_ctor_get(v_e_2853_, 1);
lean_inc_ref(v_expr_2910_);
v___x_2911_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v_xs_2852_, v_expr_2910_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_);
if (lean_obj_tag(v___x_2911_) == 0)
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2923_; 
v_a_2912_ = lean_ctor_get(v___x_2911_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2914_ = v___x_2911_;
v_isShared_2915_ = v_isSharedCheck_2923_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2911_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2923_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
size_t v___x_2916_; size_t v___x_2917_; uint8_t v___x_2918_; 
v___x_2916_ = lean_ptr_addr(v_expr_2910_);
v___x_2917_ = lean_ptr_addr(v_a_2912_);
v___x_2918_ = lean_usize_dec_eq(v___x_2916_, v___x_2917_);
if (v___x_2918_ == 0)
{
lean_object* v___x_2919_; 
lean_inc(v_data_2909_);
lean_del_object(v___x_2914_);
lean_dec_ref_known(v_e_2853_, 2);
v___x_2919_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2___redArg(v_data_2909_, v_a_2912_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_);
return v___x_2919_;
}
else
{
lean_object* v___x_2921_; 
lean_dec(v_a_2912_);
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 0, v_e_2853_);
v___x_2921_ = v___x_2914_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_e_2853_);
v___x_2921_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
return v___x_2921_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2853_, 2);
return v___x_2911_;
}
}
case 11:
{
lean_object* v_typeName_2924_; lean_object* v_idx_2925_; lean_object* v_struct_2926_; lean_object* v___x_2927_; 
v_typeName_2924_ = lean_ctor_get(v_e_2853_, 0);
v_idx_2925_ = lean_ctor_get(v_e_2853_, 1);
v_struct_2926_ = lean_ctor_get(v_e_2853_, 2);
lean_inc_ref(v_struct_2926_);
v___x_2927_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v_xs_2852_, v_struct_2926_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_);
if (lean_obj_tag(v___x_2927_) == 0)
{
lean_object* v_a_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2939_; 
v_a_2928_ = lean_ctor_get(v___x_2927_, 0);
v_isSharedCheck_2939_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_2939_ == 0)
{
v___x_2930_ = v___x_2927_;
v_isShared_2931_ = v_isSharedCheck_2939_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_a_2928_);
lean_dec(v___x_2927_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2939_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
size_t v___x_2932_; size_t v___x_2933_; uint8_t v___x_2934_; 
v___x_2932_ = lean_ptr_addr(v_struct_2926_);
v___x_2933_ = lean_ptr_addr(v_a_2928_);
v___x_2934_ = lean_usize_dec_eq(v___x_2932_, v___x_2933_);
if (v___x_2934_ == 0)
{
lean_object* v___x_2935_; 
lean_inc(v_idx_2925_);
lean_inc(v_typeName_2924_);
lean_del_object(v___x_2930_);
lean_dec_ref_known(v_e_2853_, 3);
v___x_2935_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3___redArg(v_typeName_2924_, v_idx_2925_, v_a_2928_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_);
return v___x_2935_;
}
else
{
lean_object* v___x_2937_; 
lean_dec(v_a_2928_);
if (v_isShared_2931_ == 0)
{
lean_ctor_set(v___x_2930_, 0, v_e_2853_);
v___x_2937_ = v___x_2930_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v_e_2853_);
v___x_2937_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
return v___x_2937_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2853_, 3);
return v___x_2927_;
}
}
default: 
{
lean_object* v___x_2940_; 
v___x_2940_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg(v_xs_2852_, v_e_2853_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_);
return v___x_2940_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___boxed(lean_object* v_xs_2941_, lean_object* v_e_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit(v_xs_2941_, v_e_2942_, v_a_2943_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_, v_a_2948_, v_a_2949_);
lean_dec(v_a_2949_);
lean_dec_ref(v_a_2948_);
lean_dec(v_a_2947_);
lean_dec_ref(v_a_2946_);
lean_dec(v_a_2945_);
lean_dec_ref(v_a_2944_);
lean_dec(v_a_2943_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___boxed(lean_object* v_xs_2952_, lean_object* v_e_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_){
_start:
{
lean_object* v_res_2962_; 
v_res_2962_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v_xs_2952_, v_e_2953_, v_a_2954_, v_a_2955_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_);
lean_dec(v_a_2960_);
lean_dec_ref(v_a_2959_);
lean_dec(v_a_2958_);
lean_dec_ref(v_a_2957_);
lean_dec(v_a_2956_);
lean_dec_ref(v_a_2955_);
lean_dec(v_a_2954_);
return v_res_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5(lean_object* v_00_u03b1_2963_, lean_object* v_msg_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_){
_start:
{
lean_object* v___x_2973_; 
v___x_2973_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5___redArg(v_msg_2964_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5___boxed(lean_object* v_00_u03b1_2974_, lean_object* v_msg_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_){
_start:
{
lean_object* v_res_2984_; 
v_res_2984_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5(v_00_u03b1_2974_, v_msg_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2981_);
lean_dec(v___y_2980_);
lean_dec_ref(v___y_2979_);
lean_dec(v___y_2978_);
lean_dec_ref(v___y_2977_);
lean_dec(v___y_2976_);
return v_res_2984_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6(lean_object* v_00_u03b2_2985_, lean_object* v_m_2986_, lean_object* v_a_2987_){
_start:
{
lean_object* v___x_2988_; 
v___x_2988_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6___redArg(v_m_2986_, v_a_2987_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6___boxed(lean_object* v_00_u03b2_2989_, lean_object* v_m_2990_, lean_object* v_a_2991_){
_start:
{
lean_object* v_res_2992_; 
v_res_2992_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6(v_00_u03b2_2989_, v_m_2990_, v_a_2991_);
lean_dec_ref(v_a_2991_);
lean_dec_ref(v_m_2990_);
return v_res_2992_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7(lean_object* v_00_u03b2_2993_, lean_object* v_m_2994_, lean_object* v_query_2995_){
_start:
{
lean_object* v___x_2996_; 
v___x_2996_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7___redArg(v_m_2994_, v_query_2995_);
return v___x_2996_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7___boxed(lean_object* v_00_u03b2_2997_, lean_object* v_m_2998_, lean_object* v_query_2999_){
_start:
{
lean_object* v_res_3000_; 
v_res_3000_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7(v_00_u03b2_2997_, v_m_2998_, v_query_2999_);
lean_dec_ref(v_query_2999_);
lean_dec_ref(v_m_2998_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__8(lean_object* v_00_u03b2_3001_, lean_object* v_m_3002_){
_start:
{
lean_object* v___x_3003_; 
v___x_3003_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__8___redArg(v_m_3002_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__8___boxed(lean_object* v_00_u03b2_3004_, lean_object* v_m_3005_){
_start:
{
lean_object* v_res_3006_; 
v_res_3006_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__8(v_00_u03b2_3004_, v_m_3005_);
lean_dec_ref(v_m_3005_);
return v_res_3006_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7(lean_object* v_00_u03b2_3007_, lean_object* v_m_3008_, lean_object* v_query_3009_){
_start:
{
lean_object* v___x_3010_; 
v___x_3010_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7___redArg(v_m_3008_, v_query_3009_);
return v___x_3010_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7___boxed(lean_object* v_00_u03b2_3011_, lean_object* v_m_3012_, lean_object* v_query_3013_){
_start:
{
lean_object* v_res_3014_; 
v_res_3014_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7(v_00_u03b2_3011_, v_m_3012_, v_query_3013_);
lean_dec_ref(v_query_3013_);
lean_dec_ref(v_m_3012_);
return v_res_3014_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9(lean_object* v_00_u03b2_3015_, lean_object* v_m_3016_, lean_object* v_query_3017_, lean_object* v_x_3018_, lean_object* v_x_3019_, lean_object* v_x_3020_, lean_object* v_x_3021_){
_start:
{
lean_object* v___x_3022_; 
v___x_3022_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9___redArg(v_m_3016_, v_query_3017_, v_x_3018_, v_x_3019_, v_x_3020_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9___boxed(lean_object* v_00_u03b2_3023_, lean_object* v_m_3024_, lean_object* v_query_3025_, lean_object* v_x_3026_, lean_object* v_x_3027_, lean_object* v_x_3028_, lean_object* v_x_3029_){
_start:
{
lean_object* v_res_3030_; 
v_res_3030_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9(v_00_u03b2_3023_, v_m_3024_, v_query_3025_, v_x_3026_, v_x_3027_, v_x_3028_, v_x_3029_);
lean_dec_ref(v_query_3025_);
lean_dec_ref(v_m_3024_);
return v_res_3030_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__8_spec__11(lean_object* v_00_u03b2_3031_, lean_object* v_init_3032_, lean_object* v_b_3033_){
_start:
{
lean_object* v___x_3034_; 
v___x_3034_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__8_spec__11___redArg(v_init_3032_, v_b_3033_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__8_spec__11___boxed(lean_object* v_00_u03b2_3035_, lean_object* v_init_3036_, lean_object* v_b_3037_){
_start:
{
lean_object* v_res_3038_; 
v_res_3038_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__8_spec__11(v_00_u03b2_3035_, v_init_3036_, v_b_3037_);
lean_dec_ref(v_b_3037_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__8_spec__11_spec__12(lean_object* v_00_u03b2_3039_, lean_object* v_b_3040_, lean_object* v_acc_3041_, lean_object* v_i_3042_){
_start:
{
lean_object* v___x_3043_; 
v___x_3043_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__8_spec__11_spec__12___redArg(v_b_3040_, v_acc_3041_, v_i_3042_);
return v___x_3043_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__8_spec__11_spec__12___boxed(lean_object* v_00_u03b2_3044_, lean_object* v_b_3045_, lean_object* v_acc_3046_, lean_object* v_i_3047_){
_start:
{
lean_object* v_res_3048_; 
v_res_3048_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__8_spec__11_spec__12(v_00_u03b2_3044_, v_b_3045_, v_acc_3046_, v_i_3047_);
lean_dec_ref(v_b_3045_);
return v_res_3048_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4(lean_object* v_msg_3051_, uint8_t v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_){
_start:
{
lean_object* v___f_3055_; lean_object* v___f_3056_; lean_object* v___x_3057_; lean_object* v___f_3058_; lean_object* v___f_3059_; lean_object* v___f_3060_; lean_object* v___x_13994__overap_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___f_3055_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4___closed__0));
v___f_3056_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4___closed__1));
v___x_3057_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___f_3055_, v___f_3056_);
v___f_3058_ = lean_alloc_closure((void*)(l_EStateM_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3058_, 0, v___x_3057_);
v___f_3059_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3059_, 0, v___f_3058_);
v___f_3060_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3060_, 0, v___f_3059_);
v___x_13994__overap_3061_ = lean_panic_fn_borrowed(v___f_3060_, v_msg_3051_);
lean_dec_ref(v___f_3060_);
v___x_3062_ = lean_box(v___y_3052_);
lean_inc_ref(v___y_3053_);
v___x_3063_ = lean_apply_3(v___x_13994__overap_3061_, v___x_3062_, v___y_3053_, v___y_3054_);
return v___x_3063_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4___boxed(lean_object* v_msg_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_){
_start:
{
uint8_t v___y_19165__boxed_3068_; lean_object* v_res_3069_; 
v___y_19165__boxed_3068_ = lean_unbox(v___y_3065_);
v_res_3069_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4(v_msg_3064_, v___y_19165__boxed_3068_, v___y_3066_, v___y_3067_);
lean_dec_ref(v___y_3066_);
return v_res_3069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5___redArg(lean_object* v_idx_3070_, lean_object* v___y_3071_){
_start:
{
lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3072_ = l_Lean_Expr_bvar___override(v_idx_3070_);
v___x_3073_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_3072_, v___y_3071_);
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5(lean_object* v_idx_3074_, uint8_t v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_){
_start:
{
lean_object* v___x_3078_; 
v___x_3078_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5___redArg(v_idx_3074_, v___y_3077_);
return v___x_3078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5___boxed(lean_object* v_idx_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_){
_start:
{
uint8_t v___y_19198__boxed_3083_; lean_object* v_res_3084_; 
v___y_19198__boxed_3083_ = lean_unbox(v___y_3080_);
v_res_3084_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5(v_idx_3079_, v___y_19198__boxed_3083_, v___y_3081_, v___y_3082_);
lean_dec_ref(v___y_3081_);
return v_res_3084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___redArg(lean_object* v_x_3085_, lean_object* v_t_3086_, lean_object* v_v_3087_, lean_object* v_b_3088_, uint8_t v_nondep_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_){
_start:
{
lean_object* v___y_3098_; lean_object* v___x_3101_; uint8_t v_debug_3102_; 
v___x_3101_ = lean_st_ref_get(v___y_3091_);
v_debug_3102_ = lean_ctor_get_uint8(v___x_3101_, sizeof(void*)*11);
lean_dec(v___x_3101_);
if (v_debug_3102_ == 0)
{
v___y_3098_ = v___y_3091_;
goto v___jp_3097_;
}
else
{
lean_object* v___x_3103_; 
v___x_3103_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_3086_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_object* v___x_3104_; 
lean_dec_ref_known(v___x_3103_, 1);
v___x_3104_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_v_3087_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_);
if (lean_obj_tag(v___x_3104_) == 0)
{
lean_object* v___x_3105_; 
lean_dec_ref_known(v___x_3104_, 1);
v___x_3105_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_3088_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_);
if (lean_obj_tag(v___x_3105_) == 0)
{
lean_dec_ref_known(v___x_3105_, 1);
v___y_3098_ = v___y_3091_;
goto v___jp_3097_;
}
else
{
lean_object* v_a_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3113_; 
lean_dec_ref(v_b_3088_);
lean_dec_ref(v_v_3087_);
lean_dec_ref(v_t_3086_);
lean_dec(v_x_3085_);
v_a_3106_ = lean_ctor_get(v___x_3105_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v___x_3105_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3108_ = v___x_3105_;
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_a_3106_);
lean_dec(v___x_3105_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v___x_3111_; 
if (v_isShared_3109_ == 0)
{
v___x_3111_ = v___x_3108_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_a_3106_);
v___x_3111_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
return v___x_3111_;
}
}
}
}
else
{
lean_object* v_a_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3121_; 
lean_dec_ref(v_b_3088_);
lean_dec_ref(v_v_3087_);
lean_dec_ref(v_t_3086_);
lean_dec(v_x_3085_);
v_a_3114_ = lean_ctor_get(v___x_3104_, 0);
v_isSharedCheck_3121_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3121_ == 0)
{
v___x_3116_ = v___x_3104_;
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_a_3114_);
lean_dec(v___x_3104_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3119_; 
if (v_isShared_3117_ == 0)
{
v___x_3119_ = v___x_3116_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_a_3114_);
v___x_3119_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
return v___x_3119_;
}
}
}
}
else
{
lean_object* v_a_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3129_; 
lean_dec_ref(v_b_3088_);
lean_dec_ref(v_v_3087_);
lean_dec_ref(v_t_3086_);
lean_dec(v_x_3085_);
v_a_3122_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3129_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3124_ = v___x_3103_;
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_a_3122_);
lean_dec(v___x_3103_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
lean_object* v___x_3127_; 
if (v_isShared_3125_ == 0)
{
v___x_3127_ = v___x_3124_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_a_3122_);
v___x_3127_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
return v___x_3127_;
}
}
}
}
v___jp_3097_:
{
lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3099_ = l_Lean_Expr_letE___override(v_x_3085_, v_t_3086_, v_v_3087_, v_b_3088_, v_nondep_3089_);
v___x_3100_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_3099_, v___y_3098_);
return v___x_3100_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___redArg___boxed(lean_object* v_x_3130_, lean_object* v_t_3131_, lean_object* v_v_3132_, lean_object* v_b_3133_, lean_object* v_nondep_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_){
_start:
{
uint8_t v_nondep_boxed_3142_; lean_object* v_res_3143_; 
v_nondep_boxed_3142_ = lean_unbox(v_nondep_3134_);
v_res_3143_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___redArg(v_x_3130_, v_t_3131_, v_v_3132_, v_b_3133_, v_nondep_boxed_3142_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7(lean_object* v_x_3144_, lean_object* v_t_3145_, lean_object* v_v_3146_, lean_object* v_b_3147_, uint8_t v_nondep_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_){
_start:
{
lean_object* v___x_3157_; 
v___x_3157_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___redArg(v_x_3144_, v_t_3145_, v_v_3146_, v_b_3147_, v_nondep_3148_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_);
return v___x_3157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___boxed(lean_object* v_x_3158_, lean_object* v_t_3159_, lean_object* v_v_3160_, lean_object* v_b_3161_, lean_object* v_nondep_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_){
_start:
{
uint8_t v_nondep_boxed_3171_; lean_object* v_res_3172_; 
v_nondep_boxed_3171_ = lean_unbox(v_nondep_3162_);
v_res_3172_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7(v_x_3158_, v_t_3159_, v_v_3160_, v_b_3161_, v_nondep_boxed_3171_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec(v___y_3163_);
return v_res_3172_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0___redArg(lean_object* v_m_3173_, lean_object* v_query_3174_, lean_object* v_x_3175_, lean_object* v_x_3176_, lean_object* v_x_3177_){
_start:
{
lean_object* v_zero_3178_; uint8_t v_isZero_3179_; 
v_zero_3178_ = lean_unsigned_to_nat(0u);
v_isZero_3179_ = lean_nat_dec_eq(v_x_3176_, v_zero_3178_);
if (v_isZero_3179_ == 1)
{
lean_dec(v_x_3177_);
lean_dec(v_x_3176_);
if (lean_obj_tag(v_x_3175_) == 0)
{
lean_object* v___x_3180_; 
v___x_3180_ = lean_box(2);
return v___x_3180_;
}
else
{
lean_object* v_val_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3188_; 
v_val_3181_ = lean_ctor_get(v_x_3175_, 0);
v_isSharedCheck_3188_ = !lean_is_exclusive(v_x_3175_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3183_ = v_x_3175_;
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_val_3181_);
lean_dec(v_x_3175_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v___x_3186_; 
if (v_isShared_3184_ == 0)
{
v___x_3186_ = v___x_3183_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_val_3181_);
v___x_3186_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
return v___x_3186_;
}
}
}
}
else
{
lean_object* v_keyArray_3189_; lean_object* v_valueArray_3190_; lean_object* v___x_3191_; uint8_t v_isSome_3192_; 
v_keyArray_3189_ = lean_ctor_get(v_m_3173_, 1);
v_valueArray_3190_ = lean_ctor_get(v_m_3173_, 2);
v___x_3191_ = lean_array_fget_borrowed(v_keyArray_3189_, v_x_3177_);
v_isSome_3192_ = lean_noption_is_some(v___x_3191_);
if (v_isSome_3192_ == 0)
{
lean_dec(v_x_3176_);
if (lean_obj_tag(v_x_3175_) == 0)
{
lean_object* v___x_3193_; 
v___x_3193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3193_, 0, v_x_3177_);
return v___x_3193_;
}
else
{
lean_object* v_val_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3201_; 
lean_dec(v_x_3177_);
v_val_3194_ = lean_ctor_get(v_x_3175_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v_x_3175_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3196_ = v_x_3175_;
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_val_3194_);
lean_dec(v_x_3175_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3199_; 
if (v_isShared_3197_ == 0)
{
v___x_3199_ = v___x_3196_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v_val_3194_);
v___x_3199_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
return v___x_3199_;
}
}
}
}
else
{
lean_object* v_one_3202_; lean_object* v_n_3203_; lean_object* v___y_3205_; 
v_one_3202_ = lean_unsigned_to_nat(1u);
v_n_3203_ = lean_nat_sub(v_x_3176_, v_one_3202_);
lean_dec(v_x_3176_);
if (v_isSome_3192_ == 0)
{
goto v___jp_3211_;
}
else
{
lean_object* v___x_3213_; uint8_t v_isSome_3214_; 
v___x_3213_ = lean_array_fget_borrowed(v_valueArray_3190_, v_x_3177_);
v_isSome_3214_ = lean_noption_is_some(v___x_3213_);
if (v_isSome_3214_ == 0)
{
goto v___jp_3211_;
}
else
{
lean_object* v_val_3215_; uint8_t v___x_3216_; 
lean_inc(v___x_3191_);
v_val_3215_ = lean_noption_get(v___x_3191_);
v___x_3216_ = l_Lean_instBEqFVarId_beq(v_val_3215_, v_query_3174_);
if (v___x_3216_ == 0)
{
lean_object* v___x_3217_; lean_object* v___x_3218_; uint8_t v___x_3219_; 
lean_dec(v_val_3215_);
v___x_3217_ = lean_array_get_size(v_keyArray_3189_);
v___x_3218_ = lean_nat_add(v_x_3177_, v_one_3202_);
lean_dec(v_x_3177_);
v___x_3219_ = lean_nat_dec_lt(v___x_3218_, v___x_3217_);
if (v___x_3219_ == 0)
{
lean_dec(v___x_3218_);
v_x_3176_ = v_n_3203_;
v_x_3177_ = v_zero_3178_;
goto _start;
}
else
{
v_x_3176_ = v_n_3203_;
v_x_3177_ = v___x_3218_;
goto _start;
}
}
else
{
lean_object* v_val_3222_; lean_object* v___x_3223_; 
lean_dec(v_n_3203_);
lean_dec(v_x_3175_);
lean_inc(v___x_3213_);
v_val_3222_ = lean_noption_get(v___x_3213_);
v___x_3223_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3223_, 0, v_x_3177_);
lean_ctor_set(v___x_3223_, 1, v_val_3215_);
lean_ctor_set(v___x_3223_, 2, v_val_3222_);
return v___x_3223_;
}
}
}
v___jp_3204_:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; uint8_t v___x_3208_; 
v___x_3206_ = lean_array_get_size(v_keyArray_3189_);
v___x_3207_ = lean_nat_add(v_x_3177_, v_one_3202_);
lean_dec(v_x_3177_);
v___x_3208_ = lean_nat_dec_lt(v___x_3207_, v___x_3206_);
if (v___x_3208_ == 0)
{
lean_dec(v___x_3207_);
v_x_3175_ = v___y_3205_;
v_x_3176_ = v_n_3203_;
v_x_3177_ = v_zero_3178_;
goto _start;
}
else
{
v_x_3175_ = v___y_3205_;
v_x_3176_ = v_n_3203_;
v_x_3177_ = v___x_3207_;
goto _start;
}
}
v___jp_3211_:
{
if (lean_obj_tag(v_x_3175_) == 0)
{
lean_object* v___x_3212_; 
lean_inc(v_x_3177_);
v___x_3212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3212_, 0, v_x_3177_);
v___y_3205_ = v___x_3212_;
goto v___jp_3204_;
}
else
{
v___y_3205_ = v_x_3175_;
goto v___jp_3204_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0___redArg___boxed(lean_object* v_m_3224_, lean_object* v_query_3225_, lean_object* v_x_3226_, lean_object* v_x_3227_, lean_object* v_x_3228_){
_start:
{
lean_object* v_res_3229_; 
v_res_3229_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0___redArg(v_m_3224_, v_query_3225_, v_x_3226_, v_x_3227_, v_x_3228_);
lean_dec(v_query_3225_);
lean_dec_ref(v_m_3224_);
return v_res_3229_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0___redArg(lean_object* v_m_3230_, lean_object* v_query_3231_){
_start:
{
lean_object* v_keyArray_3232_; lean_object* v___x_3233_; uint64_t v___x_3234_; uint64_t v___x_3235_; uint64_t v___x_3236_; uint64_t v_fold_3237_; uint64_t v___x_3238_; uint64_t v___x_3239_; uint64_t v___x_3240_; size_t v___x_3241_; size_t v___x_3242_; size_t v___x_3243_; size_t v___x_3244_; size_t v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; 
v_keyArray_3232_ = lean_ctor_get(v_m_3230_, 1);
v___x_3233_ = lean_array_get_size(v_keyArray_3232_);
v___x_3234_ = l_Lean_instHashableFVarId_hash(v_query_3231_);
v___x_3235_ = 32ULL;
v___x_3236_ = lean_uint64_shift_right(v___x_3234_, v___x_3235_);
v_fold_3237_ = lean_uint64_xor(v___x_3234_, v___x_3236_);
v___x_3238_ = 16ULL;
v___x_3239_ = lean_uint64_shift_right(v_fold_3237_, v___x_3238_);
v___x_3240_ = lean_uint64_xor(v_fold_3237_, v___x_3239_);
v___x_3241_ = lean_uint64_to_usize(v___x_3240_);
v___x_3242_ = lean_usize_of_nat(v___x_3233_);
v___x_3243_ = ((size_t)1ULL);
v___x_3244_ = lean_usize_sub(v___x_3242_, v___x_3243_);
v___x_3245_ = lean_usize_land(v___x_3241_, v___x_3244_);
v___x_3246_ = lean_usize_to_nat(v___x_3245_);
v___x_3247_ = lean_box(0);
v___x_3248_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0___redArg(v_m_3230_, v_query_3231_, v___x_3247_, v___x_3233_, v___x_3246_);
return v___x_3248_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0___redArg___boxed(lean_object* v_m_3249_, lean_object* v_query_3250_){
_start:
{
lean_object* v_res_3251_; 
v_res_3251_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0___redArg(v_m_3249_, v_query_3250_);
lean_dec(v_query_3250_);
lean_dec_ref(v_m_3249_);
return v_res_3251_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3_spec__5___redArg(lean_object* v_m_3252_, lean_object* v_query_3253_){
_start:
{
lean_object* v___x_3254_; 
v___x_3254_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0___redArg(v_m_3252_, v_query_3253_);
if (lean_obj_tag(v___x_3254_) == 0)
{
lean_object* v_index_3255_; lean_object* v_key_3256_; lean_object* v_value_3257_; lean_object* v___x_3259_; uint8_t v_isShared_3260_; uint8_t v_isSharedCheck_3264_; 
v_index_3255_ = lean_ctor_get(v___x_3254_, 0);
v_key_3256_ = lean_ctor_get(v___x_3254_, 1);
v_value_3257_ = lean_ctor_get(v___x_3254_, 2);
v_isSharedCheck_3264_ = !lean_is_exclusive(v___x_3254_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3259_ = v___x_3254_;
v_isShared_3260_ = v_isSharedCheck_3264_;
goto v_resetjp_3258_;
}
else
{
lean_inc(v_value_3257_);
lean_inc(v_key_3256_);
lean_inc(v_index_3255_);
lean_dec(v___x_3254_);
v___x_3259_ = lean_box(0);
v_isShared_3260_ = v_isSharedCheck_3264_;
goto v_resetjp_3258_;
}
v_resetjp_3258_:
{
lean_object* v___x_3262_; 
if (v_isShared_3260_ == 0)
{
v___x_3262_ = v___x_3259_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v_index_3255_);
lean_ctor_set(v_reuseFailAlloc_3263_, 1, v_key_3256_);
lean_ctor_set(v_reuseFailAlloc_3263_, 2, v_value_3257_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
}
else
{
lean_object* v___x_3265_; 
lean_dec(v___x_3254_);
v___x_3265_ = lean_box(1);
return v___x_3265_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3_spec__5___redArg___boxed(lean_object* v_m_3266_, lean_object* v_query_3267_){
_start:
{
lean_object* v_res_3268_; 
v_res_3268_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3_spec__5___redArg(v_m_3266_, v_query_3267_);
lean_dec(v_query_3267_);
lean_dec_ref(v_m_3266_);
return v_res_3268_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3___redArg(lean_object* v_m_3269_, lean_object* v_a_3270_){
_start:
{
lean_object* v___x_3271_; 
v___x_3271_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3_spec__5___redArg(v_m_3269_, v_a_3270_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v_value_3272_; lean_object* v___x_3273_; 
v_value_3272_ = lean_ctor_get(v___x_3271_, 2);
lean_inc(v_value_3272_);
lean_dec_ref_known(v___x_3271_, 3);
v___x_3273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3273_, 0, v_value_3272_);
return v___x_3273_;
}
else
{
lean_object* v___x_3274_; 
v___x_3274_ = lean_box(0);
return v___x_3274_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3___redArg___boxed(lean_object* v_m_3275_, lean_object* v_a_3276_){
_start:
{
lean_object* v_res_3277_; 
v_res_3277_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3___redArg(v_m_3275_, v_a_3276_);
lean_dec(v_a_3276_);
lean_dec_ref(v_m_3275_);
return v_res_3277_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6_spec__9___closed__2(void){
_start:
{
lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
v___x_3280_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6_spec__9___closed__1));
v___x_3281_ = lean_unsigned_to_nat(10u);
v___x_3282_ = lean_unsigned_to_nat(236u);
v___x_3283_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6_spec__9___closed__0));
v___x_3284_ = ((lean_object*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__0));
v___x_3285_ = l_mkPanicMessageWithDecl(v___x_3284_, v___x_3283_, v___x_3282_, v___x_3281_, v___x_3280_);
return v___x_3285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6(lean_object* v___x_3286_, lean_object* v_i_3287_, lean_object* v___x_3288_, lean_object* v_e_3289_, lean_object* v_offset_3290_, lean_object* v_a_3291_, uint8_t v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_){
_start:
{
switch(lean_obj_tag(v_e_3289_))
{
case 5:
{
lean_object* v_fn_3295_; lean_object* v_arg_3296_; lean_object* v___x_3297_; 
v_fn_3295_ = lean_ctor_get(v_e_3289_, 0);
v_arg_3296_ = lean_ctor_get(v_e_3289_, 1);
lean_inc(v_offset_3290_);
lean_inc_ref(v_fn_3295_);
v___x_3297_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6_spec__9(v___x_3286_, v_i_3287_, v___x_3288_, v_fn_3295_, v_offset_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_);
if (lean_obj_tag(v___x_3297_) == 0)
{
lean_object* v_a_3298_; lean_object* v_a_3299_; lean_object* v_fst_3300_; lean_object* v_snd_3301_; lean_object* v___x_3302_; 
v_a_3298_ = lean_ctor_get(v___x_3297_, 0);
lean_inc(v_a_3298_);
v_a_3299_ = lean_ctor_get(v___x_3297_, 1);
lean_inc(v_a_3299_);
lean_dec_ref_known(v___x_3297_, 2);
v_fst_3300_ = lean_ctor_get(v_a_3298_, 0);
lean_inc(v_fst_3300_);
v_snd_3301_ = lean_ctor_get(v_a_3298_, 1);
lean_inc(v_snd_3301_);
lean_dec(v_a_3298_);
lean_inc_ref(v_arg_3296_);
v___x_3302_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6_spec__9(v___x_3286_, v_i_3287_, v___x_3288_, v_arg_3296_, v_offset_3290_, v_snd_3301_, v_a_3292_, v_a_3293_, v_a_3299_);
if (lean_obj_tag(v___x_3302_) == 0)
{
lean_object* v_a_3303_; lean_object* v_a_3304_; lean_object* v___x_3306_; uint8_t v_isShared_3307_; uint8_t v_isSharedCheck_3329_; 
v_a_3303_ = lean_ctor_get(v___x_3302_, 0);
v_a_3304_ = lean_ctor_get(v___x_3302_, 1);
v_isSharedCheck_3329_ = !lean_is_exclusive(v___x_3302_);
if (v_isSharedCheck_3329_ == 0)
{
v___x_3306_ = v___x_3302_;
v_isShared_3307_ = v_isSharedCheck_3329_;
goto v_resetjp_3305_;
}
else
{
lean_inc(v_a_3304_);
lean_inc(v_a_3303_);
lean_dec(v___x_3302_);
v___x_3306_ = lean_box(0);
v_isShared_3307_ = v_isSharedCheck_3329_;
goto v_resetjp_3305_;
}
v_resetjp_3305_:
{
lean_object* v_fst_3308_; lean_object* v_snd_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3328_; 
v_fst_3308_ = lean_ctor_get(v_a_3303_, 0);
v_snd_3309_ = lean_ctor_get(v_a_3303_, 1);
v_isSharedCheck_3328_ = !lean_is_exclusive(v_a_3303_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3311_ = v_a_3303_;
v_isShared_3312_ = v_isSharedCheck_3328_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_snd_3309_);
lean_inc(v_fst_3308_);
lean_dec(v_a_3303_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3328_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
uint8_t v___y_3314_; size_t v___x_3322_; size_t v___x_3323_; uint8_t v___x_3324_; 
v___x_3322_ = lean_ptr_addr(v_fn_3295_);
v___x_3323_ = lean_ptr_addr(v_fst_3300_);
v___x_3324_ = lean_usize_dec_eq(v___x_3322_, v___x_3323_);
if (v___x_3324_ == 0)
{
v___y_3314_ = v___x_3324_;
goto v___jp_3313_;
}
else
{
size_t v___x_3325_; size_t v___x_3326_; uint8_t v___x_3327_; 
v___x_3325_ = lean_ptr_addr(v_arg_3296_);
v___x_3326_ = lean_ptr_addr(v_fst_3308_);
v___x_3327_ = lean_usize_dec_eq(v___x_3325_, v___x_3326_);
v___y_3314_ = v___x_3327_;
goto v___jp_3313_;
}
v___jp_3313_:
{
if (v___y_3314_ == 0)
{
lean_object* v___x_3315_; 
lean_del_object(v___x_3311_);
lean_del_object(v___x_3306_);
lean_dec_ref_known(v_e_3289_, 2);
v___x_3315_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__1(v_fst_3300_, v_fst_3308_, v_snd_3309_, v_a_3292_, v_a_3293_, v_a_3304_);
return v___x_3315_;
}
else
{
lean_object* v___x_3317_; 
lean_dec(v_fst_3308_);
lean_dec(v_fst_3300_);
if (v_isShared_3312_ == 0)
{
lean_ctor_set(v___x_3311_, 0, v_e_3289_);
v___x_3317_ = v___x_3311_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v_e_3289_);
lean_ctor_set(v_reuseFailAlloc_3321_, 1, v_snd_3309_);
v___x_3317_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
lean_object* v___x_3319_; 
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 0, v___x_3317_);
v___x_3319_ = v___x_3306_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v___x_3317_);
lean_ctor_set(v_reuseFailAlloc_3320_, 1, v_a_3304_);
v___x_3319_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
return v___x_3319_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_3300_);
lean_dec_ref_known(v_e_3289_, 2);
return v___x_3302_;
}
}
else
{
lean_dec_ref_known(v_e_3289_, 2);
lean_dec(v_offset_3290_);
return v___x_3297_;
}
}
case 6:
{
lean_object* v_binderName_3330_; lean_object* v_binderType_3331_; lean_object* v_body_3332_; uint8_t v_binderInfo_3333_; lean_object* v___x_3334_; 
v_binderName_3330_ = lean_ctor_get(v_e_3289_, 0);
v_binderType_3331_ = lean_ctor_get(v_e_3289_, 1);
v_body_3332_ = lean_ctor_get(v_e_3289_, 2);
v_binderInfo_3333_ = lean_ctor_get_uint8(v_e_3289_, sizeof(void*)*3 + 8);
lean_inc(v_offset_3290_);
lean_inc_ref(v_binderType_3331_);
v___x_3334_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6_spec__9(v___x_3286_, v_i_3287_, v___x_3288_, v_binderType_3331_, v_offset_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_);
if (lean_obj_tag(v___x_3334_) == 0)
{
lean_object* v_a_3335_; lean_object* v_a_3336_; lean_object* v_fst_3337_; lean_object* v_snd_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; 
v_a_3335_ = lean_ctor_get(v___x_3334_, 0);
lean_inc(v_a_3335_);
v_a_3336_ = lean_ctor_get(v___x_3334_, 1);
lean_inc(v_a_3336_);
lean_dec_ref_known(v___x_3334_, 2);
v_fst_3337_ = lean_ctor_get(v_a_3335_, 0);
lean_inc(v_fst_3337_);
v_snd_3338_ = lean_ctor_get(v_a_3335_, 1);
lean_inc(v_snd_3338_);
lean_dec(v_a_3335_);
v___x_3339_ = lean_unsigned_to_nat(1u);
v___x_3340_ = lean_nat_add(v_offset_3290_, v___x_3339_);
lean_dec(v_offset_3290_);
lean_inc_ref(v_body_3332_);
v___x_3341_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6_spec__9(v___x_3286_, v_i_3287_, v___x_3288_, v_body_3332_, v___x_3340_, v_snd_3338_, v_a_3292_, v_a_3293_, v_a_3336_);
if (lean_obj_tag(v___x_3341_) == 0)
{
lean_object* v_a_3342_; lean_object* v_a_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3368_; 
v_a_3342_ = lean_ctor_get(v___x_3341_, 0);
v_a_3343_ = lean_ctor_get(v___x_3341_, 1);
v_isSharedCheck_3368_ = !lean_is_exclusive(v___x_3341_);
if (v_isSharedCheck_3368_ == 0)
{
v___x_3345_ = v___x_3341_;
v_isShared_3346_ = v_isSharedCheck_3368_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_a_3343_);
lean_inc(v_a_3342_);
lean_dec(v___x_3341_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3368_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v_fst_3347_; lean_object* v_snd_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3367_; 
v_fst_3347_ = lean_ctor_get(v_a_3342_, 0);
v_snd_3348_ = lean_ctor_get(v_a_3342_, 1);
v_isSharedCheck_3367_ = !lean_is_exclusive(v_a_3342_);
if (v_isSharedCheck_3367_ == 0)
{
v___x_3350_ = v_a_3342_;
v_isShared_3351_ = v_isSharedCheck_3367_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_snd_3348_);
lean_inc(v_fst_3347_);
lean_dec(v_a_3342_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3367_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
uint8_t v___y_3353_; size_t v___x_3361_; size_t v___x_3362_; uint8_t v___x_3363_; 
v___x_3361_ = lean_ptr_addr(v_binderType_3331_);
v___x_3362_ = lean_ptr_addr(v_fst_3337_);
v___x_3363_ = lean_usize_dec_eq(v___x_3361_, v___x_3362_);
if (v___x_3363_ == 0)
{
v___y_3353_ = v___x_3363_;
goto v___jp_3352_;
}
else
{
size_t v___x_3364_; size_t v___x_3365_; uint8_t v___x_3366_; 
v___x_3364_ = lean_ptr_addr(v_body_3332_);
v___x_3365_ = lean_ptr_addr(v_fst_3347_);
v___x_3366_ = lean_usize_dec_eq(v___x_3364_, v___x_3365_);
v___y_3353_ = v___x_3366_;
goto v___jp_3352_;
}
v___jp_3352_:
{
if (v___y_3353_ == 0)
{
lean_object* v___x_3354_; 
lean_inc(v_binderName_3330_);
lean_del_object(v___x_3350_);
lean_del_object(v___x_3345_);
lean_dec_ref_known(v_e_3289_, 3);
v___x_3354_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__2(v_binderName_3330_, v_binderInfo_3333_, v_fst_3337_, v_fst_3347_, v_snd_3348_, v_a_3292_, v_a_3293_, v_a_3343_);
return v___x_3354_;
}
else
{
lean_object* v___x_3356_; 
lean_dec(v_fst_3347_);
lean_dec(v_fst_3337_);
if (v_isShared_3351_ == 0)
{
lean_ctor_set(v___x_3350_, 0, v_e_3289_);
v___x_3356_ = v___x_3350_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v_e_3289_);
lean_ctor_set(v_reuseFailAlloc_3360_, 1, v_snd_3348_);
v___x_3356_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
lean_object* v___x_3358_; 
if (v_isShared_3346_ == 0)
{
lean_ctor_set(v___x_3345_, 0, v___x_3356_);
v___x_3358_ = v___x_3345_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v___x_3356_);
lean_ctor_set(v_reuseFailAlloc_3359_, 1, v_a_3343_);
v___x_3358_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
return v___x_3358_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_3337_);
lean_dec_ref_known(v_e_3289_, 3);
return v___x_3341_;
}
}
else
{
lean_dec_ref_known(v_e_3289_, 3);
lean_dec(v_offset_3290_);
return v___x_3334_;
}
}
case 7:
{
lean_object* v_binderName_3369_; lean_object* v_binderType_3370_; lean_object* v_body_3371_; uint8_t v_binderInfo_3372_; lean_object* v___x_3373_; 
v_binderName_3369_ = lean_ctor_get(v_e_3289_, 0);
v_binderType_3370_ = lean_ctor_get(v_e_3289_, 1);
v_body_3371_ = lean_ctor_get(v_e_3289_, 2);
v_binderInfo_3372_ = lean_ctor_get_uint8(v_e_3289_, sizeof(void*)*3 + 8);
lean_inc(v_offset_3290_);
lean_inc_ref(v_binderType_3370_);
v___x_3373_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6_spec__9(v___x_3286_, v_i_3287_, v___x_3288_, v_binderType_3370_, v_offset_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_);
if (lean_obj_tag(v___x_3373_) == 0)
{
lean_object* v_a_3374_; lean_object* v_a_3375_; lean_object* v_fst_3376_; lean_object* v_snd_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; 
v_a_3374_ = lean_ctor_get(v___x_3373_, 0);
lean_inc(v_a_3374_);
v_a_3375_ = lean_ctor_get(v___x_3373_, 1);
lean_inc(v_a_3375_);
lean_dec_ref_known(v___x_3373_, 2);
v_fst_3376_ = lean_ctor_get(v_a_3374_, 0);
lean_inc(v_fst_3376_);
v_snd_3377_ = lean_ctor_get(v_a_3374_, 1);
lean_inc(v_snd_3377_);
lean_dec(v_a_3374_);
v___x_3378_ = lean_unsigned_to_nat(1u);
v___x_3379_ = lean_nat_add(v_offset_3290_, v___x_3378_);
lean_dec(v_offset_3290_);
lean_inc_ref(v_body_3371_);
v___x_3380_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6_spec__9(v___x_3286_, v_i_3287_, v___x_3288_, v_body_3371_, v___x_3379_, v_snd_3377_, v_a_3292_, v_a_3293_, v_a_3375_);
if (lean_obj_tag(v___x_3380_) == 0)
{
lean_object* v_a_3381_; lean_object* v_a_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3407_; 
v_a_3381_ = lean_ctor_get(v___x_3380_, 0);
v_a_3382_ = lean_ctor_get(v___x_3380_, 1);
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3384_ = v___x_3380_;
v_isShared_3385_ = v_isSharedCheck_3407_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_a_3382_);
lean_inc(v_a_3381_);
lean_dec(v___x_3380_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3407_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v_fst_3386_; lean_object* v_snd_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3406_; 
v_fst_3386_ = lean_ctor_get(v_a_3381_, 0);
v_snd_3387_ = lean_ctor_get(v_a_3381_, 1);
v_isSharedCheck_3406_ = !lean_is_exclusive(v_a_3381_);
if (v_isSharedCheck_3406_ == 0)
{
v___x_3389_ = v_a_3381_;
v_isShared_3390_ = v_isSharedCheck_3406_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_snd_3387_);
lean_inc(v_fst_3386_);
lean_dec(v_a_3381_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3406_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
uint8_t v___y_3392_; size_t v___x_3400_; size_t v___x_3401_; uint8_t v___x_3402_; 
v___x_3400_ = lean_ptr_addr(v_binderType_3370_);
v___x_3401_ = lean_ptr_addr(v_fst_3376_);
v___x_3402_ = lean_usize_dec_eq(v___x_3400_, v___x_3401_);
if (v___x_3402_ == 0)
{
v___y_3392_ = v___x_3402_;
goto v___jp_3391_;
}
else
{
size_t v___x_3403_; size_t v___x_3404_; uint8_t v___x_3405_; 
v___x_3403_ = lean_ptr_addr(v_body_3371_);
v___x_3404_ = lean_ptr_addr(v_fst_3386_);
v___x_3405_ = lean_usize_dec_eq(v___x_3403_, v___x_3404_);
v___y_3392_ = v___x_3405_;
goto v___jp_3391_;
}
v___jp_3391_:
{
if (v___y_3392_ == 0)
{
lean_object* v___x_3393_; 
lean_inc(v_binderName_3369_);
lean_del_object(v___x_3389_);
lean_del_object(v___x_3384_);
lean_dec_ref_known(v_e_3289_, 3);
v___x_3393_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__3(v_binderName_3369_, v_binderInfo_3372_, v_fst_3376_, v_fst_3386_, v_snd_3387_, v_a_3292_, v_a_3293_, v_a_3382_);
return v___x_3393_;
}
else
{
lean_object* v___x_3395_; 
lean_dec(v_fst_3386_);
lean_dec(v_fst_3376_);
if (v_isShared_3390_ == 0)
{
lean_ctor_set(v___x_3389_, 0, v_e_3289_);
v___x_3395_ = v___x_3389_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v_e_3289_);
lean_ctor_set(v_reuseFailAlloc_3399_, 1, v_snd_3387_);
v___x_3395_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
lean_object* v___x_3397_; 
if (v_isShared_3385_ == 0)
{
lean_ctor_set(v___x_3384_, 0, v___x_3395_);
v___x_3397_ = v___x_3384_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v___x_3395_);
lean_ctor_set(v_reuseFailAlloc_3398_, 1, v_a_3382_);
v___x_3397_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
return v___x_3397_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_3376_);
lean_dec_ref_known(v_e_3289_, 3);
return v___x_3380_;
}
}
else
{
lean_dec_ref_known(v_e_3289_, 3);
lean_dec(v_offset_3290_);
return v___x_3373_;
}
}
case 8:
{
lean_object* v_declName_3408_; lean_object* v_type_3409_; lean_object* v_value_3410_; lean_object* v_body_3411_; uint8_t v_nondep_3412_; lean_object* v___x_3413_; 
v_declName_3408_ = lean_ctor_get(v_e_3289_, 0);
v_type_3409_ = lean_ctor_get(v_e_3289_, 1);
v_value_3410_ = lean_ctor_get(v_e_3289_, 2);
v_body_3411_ = lean_ctor_get(v_e_3289_, 3);
v_nondep_3412_ = lean_ctor_get_uint8(v_e_3289_, sizeof(void*)*4 + 8);
lean_inc(v_offset_3290_);
lean_inc_ref(v_type_3409_);
v___x_3413_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6_spec__9(v___x_3286_, v_i_3287_, v___x_3288_, v_type_3409_, v_offset_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_);
if (lean_obj_tag(v___x_3413_) == 0)
{
lean_object* v_a_3414_; lean_object* v_a_3415_; lean_object* v_fst_3416_; lean_object* v_snd_3417_; lean_object* v___x_3418_; 
v_a_3414_ = lean_ctor_get(v___x_3413_, 0);
lean_inc(v_a_3414_);
v_a_3415_ = lean_ctor_get(v___x_3413_, 1);
lean_inc(v_a_3415_);
lean_dec_ref_known(v___x_3413_, 2);
v_fst_3416_ = lean_ctor_get(v_a_3414_, 0);
lean_inc(v_fst_3416_);
v_snd_3417_ = lean_ctor_get(v_a_3414_, 1);
lean_inc(v_snd_3417_);
lean_dec(v_a_3414_);
lean_inc(v_offset_3290_);
lean_inc_ref(v_value_3410_);
v___x_3418_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6_spec__9(v___x_3286_, v_i_3287_, v___x_3288_, v_value_3410_, v_offset_3290_, v_snd_3417_, v_a_3292_, v_a_3293_, v_a_3415_);
if (lean_obj_tag(v___x_3418_) == 0)
{
lean_object* v_a_3419_; lean_object* v_a_3420_; lean_object* v_fst_3421_; lean_object* v_snd_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; 
v_a_3419_ = lean_ctor_get(v___x_3418_, 0);
lean_inc(v_a_3419_);
v_a_3420_ = lean_ctor_get(v___x_3418_, 1);
lean_inc(v_a_3420_);
lean_dec_ref_known(v___x_3418_, 2);
v_fst_3421_ = lean_ctor_get(v_a_3419_, 0);
lean_inc(v_fst_3421_);
v_snd_3422_ = lean_ctor_get(v_a_3419_, 1);
lean_inc(v_snd_3422_);
lean_dec(v_a_3419_);
v___x_3423_ = lean_unsigned_to_nat(1u);
v___x_3424_ = lean_nat_add(v_offset_3290_, v___x_3423_);
lean_dec(v_offset_3290_);
lean_inc_ref(v_body_3411_);
v___x_3425_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6_spec__9(v___x_3286_, v_i_3287_, v___x_3288_, v_body_3411_, v___x_3424_, v_snd_3422_, v_a_3292_, v_a_3293_, v_a_3420_);
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_object* v_a_3426_; lean_object* v_a_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3456_; 
v_a_3426_ = lean_ctor_get(v___x_3425_, 0);
v_a_3427_ = lean_ctor_get(v___x_3425_, 1);
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3425_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3429_ = v___x_3425_;
v_isShared_3430_ = v_isSharedCheck_3456_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_a_3427_);
lean_inc(v_a_3426_);
lean_dec(v___x_3425_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3456_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v_fst_3431_; lean_object* v_snd_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3455_; 
v_fst_3431_ = lean_ctor_get(v_a_3426_, 0);
v_snd_3432_ = lean_ctor_get(v_a_3426_, 1);
v_isSharedCheck_3455_ = !lean_is_exclusive(v_a_3426_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3434_ = v_a_3426_;
v_isShared_3435_ = v_isSharedCheck_3455_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_snd_3432_);
lean_inc(v_fst_3431_);
lean_dec(v_a_3426_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3455_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
uint8_t v___y_3437_; size_t v___x_3449_; size_t v___x_3450_; uint8_t v___x_3451_; 
v___x_3449_ = lean_ptr_addr(v_type_3409_);
v___x_3450_ = lean_ptr_addr(v_fst_3416_);
v___x_3451_ = lean_usize_dec_eq(v___x_3449_, v___x_3450_);
if (v___x_3451_ == 0)
{
v___y_3437_ = v___x_3451_;
goto v___jp_3436_;
}
else
{
size_t v___x_3452_; size_t v___x_3453_; uint8_t v___x_3454_; 
v___x_3452_ = lean_ptr_addr(v_value_3410_);
v___x_3453_ = lean_ptr_addr(v_fst_3421_);
v___x_3454_ = lean_usize_dec_eq(v___x_3452_, v___x_3453_);
v___y_3437_ = v___x_3454_;
goto v___jp_3436_;
}
v___jp_3436_:
{
if (v___y_3437_ == 0)
{
lean_object* v___x_3438_; 
lean_inc(v_declName_3408_);
lean_del_object(v___x_3434_);
lean_del_object(v___x_3429_);
lean_dec_ref_known(v_e_3289_, 4);
v___x_3438_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4(v_declName_3408_, v_fst_3416_, v_fst_3421_, v_fst_3431_, v_nondep_3412_, v_snd_3432_, v_a_3292_, v_a_3293_, v_a_3427_);
return v___x_3438_;
}
else
{
size_t v___x_3439_; size_t v___x_3440_; uint8_t v___x_3441_; 
v___x_3439_ = lean_ptr_addr(v_body_3411_);
v___x_3440_ = lean_ptr_addr(v_fst_3431_);
v___x_3441_ = lean_usize_dec_eq(v___x_3439_, v___x_3440_);
if (v___x_3441_ == 0)
{
lean_object* v___x_3442_; 
lean_inc(v_declName_3408_);
lean_del_object(v___x_3434_);
lean_del_object(v___x_3429_);
lean_dec_ref_known(v_e_3289_, 4);
v___x_3442_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4(v_declName_3408_, v_fst_3416_, v_fst_3421_, v_fst_3431_, v_nondep_3412_, v_snd_3432_, v_a_3292_, v_a_3293_, v_a_3427_);
return v___x_3442_;
}
else
{
lean_object* v___x_3444_; 
lean_dec(v_fst_3431_);
lean_dec(v_fst_3421_);
lean_dec(v_fst_3416_);
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 0, v_e_3289_);
v___x_3444_ = v___x_3434_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_e_3289_);
lean_ctor_set(v_reuseFailAlloc_3448_, 1, v_snd_3432_);
v___x_3444_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
lean_object* v___x_3446_; 
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 0, v___x_3444_);
v___x_3446_ = v___x_3429_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v___x_3444_);
lean_ctor_set(v_reuseFailAlloc_3447_, 1, v_a_3427_);
v___x_3446_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
return v___x_3446_;
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
lean_dec(v_fst_3421_);
lean_dec(v_fst_3416_);
lean_dec_ref_known(v_e_3289_, 4);
return v___x_3425_;
}
}
else
{
lean_dec(v_fst_3416_);
lean_dec_ref_known(v_e_3289_, 4);
lean_dec(v_offset_3290_);
return v___x_3418_;
}
}
else
{
lean_dec_ref_known(v_e_3289_, 4);
lean_dec(v_offset_3290_);
return v___x_3413_;
}
}
case 10:
{
lean_object* v_data_3457_; lean_object* v_expr_3458_; lean_object* v___x_3459_; 
v_data_3457_ = lean_ctor_get(v_e_3289_, 0);
v_expr_3458_ = lean_ctor_get(v_e_3289_, 1);
lean_inc_ref(v_expr_3458_);
v___x_3459_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6_spec__9(v___x_3286_, v_i_3287_, v___x_3288_, v_expr_3458_, v_offset_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v_a_3460_; lean_object* v_a_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3481_; 
v_a_3460_ = lean_ctor_get(v___x_3459_, 0);
v_a_3461_ = lean_ctor_get(v___x_3459_, 1);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3463_ = v___x_3459_;
v_isShared_3464_ = v_isSharedCheck_3481_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_a_3461_);
lean_inc(v_a_3460_);
lean_dec(v___x_3459_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3481_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v_fst_3465_; lean_object* v_snd_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3480_; 
v_fst_3465_ = lean_ctor_get(v_a_3460_, 0);
v_snd_3466_ = lean_ctor_get(v_a_3460_, 1);
v_isSharedCheck_3480_ = !lean_is_exclusive(v_a_3460_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3468_ = v_a_3460_;
v_isShared_3469_ = v_isSharedCheck_3480_;
goto v_resetjp_3467_;
}
else
{
lean_inc(v_snd_3466_);
lean_inc(v_fst_3465_);
lean_dec(v_a_3460_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3480_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
size_t v___x_3470_; size_t v___x_3471_; uint8_t v___x_3472_; 
v___x_3470_ = lean_ptr_addr(v_expr_3458_);
v___x_3471_ = lean_ptr_addr(v_fst_3465_);
v___x_3472_ = lean_usize_dec_eq(v___x_3470_, v___x_3471_);
if (v___x_3472_ == 0)
{
lean_object* v___x_3473_; 
lean_inc(v_data_3457_);
lean_del_object(v___x_3468_);
lean_del_object(v___x_3463_);
lean_dec_ref_known(v_e_3289_, 2);
v___x_3473_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__5(v_data_3457_, v_fst_3465_, v_snd_3466_, v_a_3292_, v_a_3293_, v_a_3461_);
return v___x_3473_;
}
else
{
lean_object* v___x_3475_; 
lean_dec(v_fst_3465_);
if (v_isShared_3469_ == 0)
{
lean_ctor_set(v___x_3468_, 0, v_e_3289_);
v___x_3475_ = v___x_3468_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_e_3289_);
lean_ctor_set(v_reuseFailAlloc_3479_, 1, v_snd_3466_);
v___x_3475_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
lean_object* v___x_3477_; 
if (v_isShared_3464_ == 0)
{
lean_ctor_set(v___x_3463_, 0, v___x_3475_);
v___x_3477_ = v___x_3463_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v___x_3475_);
lean_ctor_set(v_reuseFailAlloc_3478_, 1, v_a_3461_);
v___x_3477_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
return v___x_3477_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3289_, 2);
return v___x_3459_;
}
}
case 11:
{
lean_object* v_typeName_3482_; lean_object* v_idx_3483_; lean_object* v_struct_3484_; lean_object* v___x_3485_; 
v_typeName_3482_ = lean_ctor_get(v_e_3289_, 0);
v_idx_3483_ = lean_ctor_get(v_e_3289_, 1);
v_struct_3484_ = lean_ctor_get(v_e_3289_, 2);
lean_inc_ref(v_struct_3484_);
v___x_3485_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6_spec__9(v___x_3286_, v_i_3287_, v___x_3288_, v_struct_3484_, v_offset_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_);
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_object* v_a_3486_; lean_object* v_a_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3507_; 
v_a_3486_ = lean_ctor_get(v___x_3485_, 0);
v_a_3487_ = lean_ctor_get(v___x_3485_, 1);
v_isSharedCheck_3507_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3489_ = v___x_3485_;
v_isShared_3490_ = v_isSharedCheck_3507_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_a_3487_);
lean_inc(v_a_3486_);
lean_dec(v___x_3485_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3507_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v_fst_3491_; lean_object* v_snd_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3506_; 
v_fst_3491_ = lean_ctor_get(v_a_3486_, 0);
v_snd_3492_ = lean_ctor_get(v_a_3486_, 1);
v_isSharedCheck_3506_ = !lean_is_exclusive(v_a_3486_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3494_ = v_a_3486_;
v_isShared_3495_ = v_isSharedCheck_3506_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_snd_3492_);
lean_inc(v_fst_3491_);
lean_dec(v_a_3486_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3506_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
size_t v___x_3496_; size_t v___x_3497_; uint8_t v___x_3498_; 
v___x_3496_ = lean_ptr_addr(v_struct_3484_);
v___x_3497_ = lean_ptr_addr(v_fst_3491_);
v___x_3498_ = lean_usize_dec_eq(v___x_3496_, v___x_3497_);
if (v___x_3498_ == 0)
{
lean_object* v___x_3499_; 
lean_inc(v_idx_3483_);
lean_inc(v_typeName_3482_);
lean_del_object(v___x_3494_);
lean_del_object(v___x_3489_);
lean_dec_ref_known(v_e_3289_, 3);
v___x_3499_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__6(v_typeName_3482_, v_idx_3483_, v_fst_3491_, v_snd_3492_, v_a_3292_, v_a_3293_, v_a_3487_);
return v___x_3499_;
}
else
{
lean_object* v___x_3501_; 
lean_dec(v_fst_3491_);
if (v_isShared_3495_ == 0)
{
lean_ctor_set(v___x_3494_, 0, v_e_3289_);
v___x_3501_ = v___x_3494_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v_e_3289_);
lean_ctor_set(v_reuseFailAlloc_3505_, 1, v_snd_3492_);
v___x_3501_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
lean_object* v___x_3503_; 
if (v_isShared_3490_ == 0)
{
lean_ctor_set(v___x_3489_, 0, v___x_3501_);
v___x_3503_ = v___x_3489_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v___x_3501_);
lean_ctor_set(v_reuseFailAlloc_3504_, 1, v_a_3487_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
return v___x_3503_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3289_, 3);
return v___x_3485_;
}
}
default: 
{
lean_object* v___x_3508_; lean_object* v___x_3509_; 
lean_dec(v_offset_3290_);
lean_dec_ref(v_e_3289_);
v___x_3508_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__3);
v___x_3509_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7(v___x_3508_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_);
return v___x_3509_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6_spec__9(lean_object* v___x_3510_, lean_object* v_i_3511_, lean_object* v___x_3512_, lean_object* v_e_3513_, lean_object* v_offset_3514_, lean_object* v_a_3515_, uint8_t v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_){
_start:
{
lean_object* v_key_3519_; lean_object* v_a_3521_; lean_object* v___x_3534_; 
lean_inc(v_offset_3514_);
lean_inc_ref(v_e_3513_);
v_key_3519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_3519_, 0, v_e_3513_);
lean_ctor_set(v_key_3519_, 1, v_offset_3514_);
v___x_3534_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2___redArg(v_a_3515_, v_key_3519_);
if (lean_obj_tag(v___x_3534_) == 1)
{
lean_object* v_val_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; 
lean_dec_ref_known(v_key_3519_, 2);
lean_dec(v_offset_3514_);
lean_dec_ref(v_e_3513_);
v_val_3535_ = lean_ctor_get(v___x_3534_, 0);
lean_inc(v_val_3535_);
lean_dec_ref_known(v___x_3534_, 1);
v___x_3536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3536_, 0, v_val_3535_);
lean_ctor_set(v___x_3536_, 1, v_a_3515_);
v___x_3537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3537_, 0, v___x_3536_);
lean_ctor_set(v___x_3537_, 1, v_a_3518_);
return v___x_3537_;
}
else
{
lean_dec(v___x_3534_);
switch(lean_obj_tag(v_e_3513_))
{
case 1:
{
lean_object* v_fvarId_3538_; lean_object* v___x_3539_; 
v_fvarId_3538_ = lean_ctor_get(v_e_3513_, 0);
v___x_3539_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3___redArg(v___x_3510_, v_fvarId_3538_);
if (lean_obj_tag(v___x_3539_) == 1)
{
lean_object* v_val_3540_; uint8_t v___x_3541_; 
v_val_3540_ = lean_ctor_get(v___x_3539_, 0);
lean_inc(v_val_3540_);
lean_dec_ref_known(v___x_3539_, 1);
v___x_3541_ = lean_nat_dec_lt(v_val_3540_, v_i_3511_);
if (v___x_3541_ == 0)
{
lean_object* v___x_3542_; lean_object* v___x_3543_; 
lean_dec(v_val_3540_);
v___x_3542_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6_spec__9___closed__2, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6_spec__9___closed__2_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6_spec__9___closed__2);
v___x_3543_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4(v___x_3542_, v_a_3516_, v_a_3517_, v_a_3518_);
if (lean_obj_tag(v___x_3543_) == 0)
{
lean_object* v_a_3544_; 
v_a_3544_ = lean_ctor_get(v___x_3543_, 0);
lean_inc(v_a_3544_);
if (lean_obj_tag(v_a_3544_) == 1)
{
lean_object* v_a_3545_; lean_object* v_val_3546_; lean_object* v___x_3547_; 
lean_dec_ref_known(v_e_3513_, 1);
lean_dec(v_offset_3514_);
v_a_3545_ = lean_ctor_get(v___x_3543_, 1);
lean_inc(v_a_3545_);
lean_dec_ref_known(v___x_3543_, 2);
v_val_3546_ = lean_ctor_get(v_a_3544_, 0);
lean_inc(v_val_3546_);
lean_dec_ref_known(v_a_3544_, 1);
v___x_3547_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3519_, v_val_3546_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3545_);
return v___x_3547_;
}
else
{
lean_object* v_a_3548_; 
lean_dec(v_a_3544_);
v_a_3548_ = lean_ctor_get(v___x_3543_, 1);
lean_inc(v_a_3548_);
lean_dec_ref_known(v___x_3543_, 2);
v_a_3521_ = v_a_3548_;
goto v___jp_3520_;
}
}
else
{
lean_object* v_a_3549_; lean_object* v_a_3550_; lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3557_; 
lean_dec_ref_known(v_e_3513_, 1);
lean_dec_ref_known(v_key_3519_, 2);
lean_dec_ref(v_a_3515_);
lean_dec(v_offset_3514_);
v_a_3549_ = lean_ctor_get(v___x_3543_, 0);
v_a_3550_ = lean_ctor_get(v___x_3543_, 1);
v_isSharedCheck_3557_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3557_ == 0)
{
v___x_3552_ = v___x_3543_;
v_isShared_3553_ = v_isSharedCheck_3557_;
goto v_resetjp_3551_;
}
else
{
lean_inc(v_a_3550_);
lean_inc(v_a_3549_);
lean_dec(v___x_3543_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3557_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
lean_object* v___x_3555_; 
if (v_isShared_3553_ == 0)
{
v___x_3555_ = v___x_3552_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v_a_3549_);
lean_ctor_set(v_reuseFailAlloc_3556_, 1, v_a_3550_);
v___x_3555_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3554_;
}
v_reusejp_3554_:
{
return v___x_3555_;
}
}
}
}
else
{
lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
lean_dec_ref_known(v_e_3513_, 1);
v___x_3558_ = lean_nat_add(v_offset_3514_, v_i_3511_);
lean_dec(v_offset_3514_);
v___x_3559_ = lean_nat_sub(v___x_3558_, v_val_3540_);
lean_dec(v_val_3540_);
lean_dec(v___x_3558_);
v___x_3560_ = lean_unsigned_to_nat(1u);
v___x_3561_ = lean_nat_sub(v___x_3559_, v___x_3560_);
lean_dec(v___x_3559_);
v___x_3562_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5___redArg(v___x_3561_, v_a_3518_);
if (lean_obj_tag(v___x_3562_) == 0)
{
lean_object* v_a_3563_; lean_object* v_a_3564_; lean_object* v___x_3565_; 
v_a_3563_ = lean_ctor_get(v___x_3562_, 0);
lean_inc(v_a_3563_);
v_a_3564_ = lean_ctor_get(v___x_3562_, 1);
lean_inc(v_a_3564_);
lean_dec_ref_known(v___x_3562_, 2);
v___x_3565_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3519_, v_a_3563_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3564_);
return v___x_3565_;
}
else
{
lean_object* v_a_3566_; lean_object* v_a_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3574_; 
lean_dec_ref_known(v_key_3519_, 2);
lean_dec_ref(v_a_3515_);
v_a_3566_ = lean_ctor_get(v___x_3562_, 0);
v_a_3567_ = lean_ctor_get(v___x_3562_, 1);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3562_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3569_ = v___x_3562_;
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_a_3567_);
lean_inc(v_a_3566_);
lean_dec(v___x_3562_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3572_; 
if (v_isShared_3570_ == 0)
{
v___x_3572_ = v___x_3569_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v_a_3566_);
lean_ctor_set(v_reuseFailAlloc_3573_, 1, v_a_3567_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
return v___x_3572_;
}
}
}
}
}
else
{
lean_object* v___x_3575_; 
lean_dec(v___x_3539_);
lean_dec(v_offset_3514_);
v___x_3575_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3519_, v_e_3513_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_);
return v___x_3575_;
}
}
case 9:
{
lean_object* v___x_3576_; 
lean_dec(v_offset_3514_);
v___x_3576_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3519_, v_e_3513_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_);
return v___x_3576_;
}
case 2:
{
lean_object* v___x_3577_; 
lean_dec(v_offset_3514_);
v___x_3577_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3519_, v_e_3513_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_);
return v___x_3577_;
}
case 0:
{
lean_object* v___x_3578_; 
lean_dec(v_offset_3514_);
v___x_3578_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3519_, v_e_3513_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_);
return v___x_3578_;
}
case 4:
{
lean_object* v___x_3579_; 
lean_dec(v_offset_3514_);
v___x_3579_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3519_, v_e_3513_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_);
return v___x_3579_;
}
case 3:
{
lean_object* v___x_3580_; 
lean_dec(v_offset_3514_);
v___x_3580_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3519_, v_e_3513_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_);
return v___x_3580_;
}
default: 
{
uint8_t v___x_3581_; 
v___x_3581_ = l_Lean_Expr_hasFVar(v_e_3513_);
if (v___x_3581_ == 0)
{
lean_object* v___x_3582_; 
lean_dec(v_offset_3514_);
v___x_3582_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3519_, v_e_3513_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_);
return v___x_3582_;
}
else
{
lean_object* v___x_3583_; uint8_t v___x_3584_; 
v___x_3583_ = lean_unsigned_to_nat(0u);
v___x_3584_ = lean_nat_dec_eq(v___x_3512_, v___x_3583_);
if (v___x_3584_ == 0)
{
v_a_3521_ = v_a_3518_;
goto v___jp_3520_;
}
else
{
lean_object* v___x_3585_; 
lean_dec(v_offset_3514_);
v___x_3585_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3519_, v_e_3513_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_);
return v___x_3585_;
}
}
}
}
}
v___jp_3520_:
{
switch(lean_obj_tag(v_e_3513_))
{
case 9:
{
lean_object* v___x_3522_; 
lean_dec(v_offset_3514_);
v___x_3522_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3519_, v_e_3513_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3521_);
return v___x_3522_;
}
case 2:
{
lean_object* v___x_3523_; 
lean_dec(v_offset_3514_);
v___x_3523_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3519_, v_e_3513_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3521_);
return v___x_3523_;
}
case 0:
{
lean_object* v___x_3524_; 
lean_dec(v_offset_3514_);
v___x_3524_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3519_, v_e_3513_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3521_);
return v___x_3524_;
}
case 1:
{
lean_object* v___x_3525_; 
lean_dec(v_offset_3514_);
v___x_3525_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3519_, v_e_3513_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3521_);
return v___x_3525_;
}
case 4:
{
lean_object* v___x_3526_; 
lean_dec(v_offset_3514_);
v___x_3526_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3519_, v_e_3513_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3521_);
return v___x_3526_;
}
case 3:
{
lean_object* v___x_3527_; 
lean_dec(v_offset_3514_);
v___x_3527_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3519_, v_e_3513_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3521_);
return v___x_3527_;
}
default: 
{
lean_object* v___x_3528_; 
v___x_3528_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6(v___x_3510_, v_i_3511_, v___x_3512_, v_e_3513_, v_offset_3514_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3521_);
if (lean_obj_tag(v___x_3528_) == 0)
{
lean_object* v_a_3529_; lean_object* v_a_3530_; lean_object* v_fst_3531_; lean_object* v_snd_3532_; lean_object* v___x_3533_; 
v_a_3529_ = lean_ctor_get(v___x_3528_, 0);
lean_inc(v_a_3529_);
v_a_3530_ = lean_ctor_get(v___x_3528_, 1);
lean_inc(v_a_3530_);
lean_dec_ref_known(v___x_3528_, 2);
v_fst_3531_ = lean_ctor_get(v_a_3529_, 0);
lean_inc(v_fst_3531_);
v_snd_3532_ = lean_ctor_get(v_a_3529_, 1);
lean_inc(v_snd_3532_);
lean_dec(v_a_3529_);
v___x_3533_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3519_, v_fst_3531_, v_snd_3532_, v_a_3516_, v_a_3517_, v_a_3530_);
return v___x_3533_;
}
else
{
lean_dec_ref_known(v_key_3519_, 2);
return v___x_3528_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6_spec__9___boxed(lean_object* v___x_3586_, lean_object* v_i_3587_, lean_object* v___x_3588_, lean_object* v_e_3589_, lean_object* v_offset_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_){
_start:
{
uint8_t v_a_boxed_3595_; lean_object* v_res_3596_; 
v_a_boxed_3595_ = lean_unbox(v_a_3592_);
v_res_3596_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6_spec__9(v___x_3586_, v_i_3587_, v___x_3588_, v_e_3589_, v_offset_3590_, v_a_3591_, v_a_boxed_3595_, v_a_3593_, v_a_3594_);
lean_dec_ref(v_a_3593_);
lean_dec(v___x_3588_);
lean_dec(v_i_3587_);
lean_dec_ref(v___x_3586_);
return v_res_3596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6___boxed(lean_object* v___x_3597_, lean_object* v_i_3598_, lean_object* v___x_3599_, lean_object* v_e_3600_, lean_object* v_offset_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_){
_start:
{
uint8_t v_a_boxed_3606_; lean_object* v_res_3607_; 
v_a_boxed_3606_ = lean_unbox(v_a_3603_);
v_res_3607_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6(v___x_3597_, v_i_3598_, v___x_3599_, v_e_3600_, v_offset_3601_, v_a_3602_, v_a_boxed_3606_, v_a_3604_, v_a_3605_);
lean_dec_ref(v_a_3604_);
lean_dec(v___x_3599_);
lean_dec(v_i_3598_);
lean_dec_ref(v___x_3597_);
return v_res_3607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___lam__0(lean_object* v_e_3608_, lean_object* v_cellCount_3609_, lean_object* v___x_3610_, lean_object* v_fst_3611_, lean_object* v___x_3612_, uint8_t v_debug_3613_, uint8_t v___x_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_){
_start:
{
lean_object* v_a_3618_; 
switch(lean_obj_tag(v_e_3608_))
{
case 1:
{
lean_object* v_fvarId_3648_; lean_object* v___x_3649_; 
v_fvarId_3648_ = lean_ctor_get(v_e_3608_, 0);
v___x_3649_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3___redArg(v_fst_3611_, v_fvarId_3648_);
if (lean_obj_tag(v___x_3649_) == 1)
{
lean_object* v_val_3650_; uint8_t v___x_3651_; 
v_val_3650_ = lean_ctor_get(v___x_3649_, 0);
lean_inc(v_val_3650_);
lean_dec_ref_known(v___x_3649_, 1);
v___x_3651_ = lean_nat_dec_lt(v_val_3650_, v___x_3612_);
if (v___x_3651_ == 0)
{
lean_object* v___x_3652_; lean_object* v___x_3653_; 
lean_dec(v_val_3650_);
v___x_3652_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6_spec__9___closed__2, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6_spec__9___closed__2_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6_spec__9___closed__2);
v___x_3653_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4(v___x_3652_, v_debug_3613_, v___y_3615_, v___y_3616_);
if (lean_obj_tag(v___x_3653_) == 0)
{
lean_object* v_a_3654_; 
v_a_3654_ = lean_ctor_get(v___x_3653_, 0);
lean_inc(v_a_3654_);
if (lean_obj_tag(v_a_3654_) == 1)
{
lean_object* v_a_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3663_; 
lean_dec_ref_known(v_e_3608_, 1);
lean_dec(v___x_3610_);
lean_dec(v_cellCount_3609_);
v_a_3655_ = lean_ctor_get(v___x_3653_, 1);
v_isSharedCheck_3663_ = !lean_is_exclusive(v___x_3653_);
if (v_isSharedCheck_3663_ == 0)
{
lean_object* v_unused_3664_; 
v_unused_3664_ = lean_ctor_get(v___x_3653_, 0);
lean_dec(v_unused_3664_);
v___x_3657_ = v___x_3653_;
v_isShared_3658_ = v_isSharedCheck_3663_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_a_3655_);
lean_dec(v___x_3653_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3663_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v_val_3659_; lean_object* v___x_3661_; 
v_val_3659_ = lean_ctor_get(v_a_3654_, 0);
lean_inc(v_val_3659_);
lean_dec_ref_known(v_a_3654_, 1);
if (v_isShared_3658_ == 0)
{
lean_ctor_set(v___x_3657_, 0, v_val_3659_);
v___x_3661_ = v___x_3657_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_val_3659_);
lean_ctor_set(v_reuseFailAlloc_3662_, 1, v_a_3655_);
v___x_3661_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
return v___x_3661_;
}
}
}
else
{
lean_object* v_a_3665_; 
lean_dec(v_a_3654_);
v_a_3665_ = lean_ctor_get(v___x_3653_, 1);
lean_inc(v_a_3665_);
lean_dec_ref_known(v___x_3653_, 2);
v_a_3618_ = v_a_3665_;
goto v___jp_3617_;
}
}
else
{
lean_object* v_a_3666_; lean_object* v_a_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3674_; 
lean_dec_ref_known(v_e_3608_, 1);
lean_dec(v___x_3610_);
lean_dec(v_cellCount_3609_);
v_a_3666_ = lean_ctor_get(v___x_3653_, 0);
v_a_3667_ = lean_ctor_get(v___x_3653_, 1);
v_isSharedCheck_3674_ = !lean_is_exclusive(v___x_3653_);
if (v_isSharedCheck_3674_ == 0)
{
v___x_3669_ = v___x_3653_;
v_isShared_3670_ = v_isSharedCheck_3674_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_a_3667_);
lean_inc(v_a_3666_);
lean_dec(v___x_3653_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3674_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v___x_3672_; 
if (v_isShared_3670_ == 0)
{
v___x_3672_ = v___x_3669_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v_a_3666_);
lean_ctor_set(v_reuseFailAlloc_3673_, 1, v_a_3667_);
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
else
{
lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; 
lean_dec_ref_known(v_e_3608_, 1);
lean_dec(v___x_3610_);
lean_dec(v_cellCount_3609_);
v___x_3675_ = lean_nat_sub(v___x_3612_, v_val_3650_);
lean_dec(v_val_3650_);
v___x_3676_ = lean_unsigned_to_nat(1u);
v___x_3677_ = lean_nat_sub(v___x_3675_, v___x_3676_);
lean_dec(v___x_3675_);
v___x_3678_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5___redArg(v___x_3677_, v___y_3616_);
return v___x_3678_;
}
}
else
{
lean_object* v___x_3679_; 
lean_dec(v___x_3649_);
lean_dec(v___x_3610_);
lean_dec(v_cellCount_3609_);
v___x_3679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3679_, 0, v_e_3608_);
lean_ctor_set(v___x_3679_, 1, v___y_3616_);
return v___x_3679_;
}
}
case 9:
{
lean_object* v___x_3680_; 
lean_dec(v___x_3610_);
lean_dec(v_cellCount_3609_);
v___x_3680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3680_, 0, v_e_3608_);
lean_ctor_set(v___x_3680_, 1, v___y_3616_);
return v___x_3680_;
}
case 2:
{
lean_object* v___x_3681_; 
lean_dec(v___x_3610_);
lean_dec(v_cellCount_3609_);
v___x_3681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3681_, 0, v_e_3608_);
lean_ctor_set(v___x_3681_, 1, v___y_3616_);
return v___x_3681_;
}
case 0:
{
lean_object* v___x_3682_; 
lean_dec(v___x_3610_);
lean_dec(v_cellCount_3609_);
v___x_3682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3682_, 0, v_e_3608_);
lean_ctor_set(v___x_3682_, 1, v___y_3616_);
return v___x_3682_;
}
case 4:
{
lean_object* v___x_3683_; 
lean_dec(v___x_3610_);
lean_dec(v_cellCount_3609_);
v___x_3683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3683_, 0, v_e_3608_);
lean_ctor_set(v___x_3683_, 1, v___y_3616_);
return v___x_3683_;
}
case 3:
{
lean_object* v___x_3684_; 
lean_dec(v___x_3610_);
lean_dec(v_cellCount_3609_);
v___x_3684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3684_, 0, v_e_3608_);
lean_ctor_set(v___x_3684_, 1, v___y_3616_);
return v___x_3684_;
}
default: 
{
uint8_t v___x_3685_; 
v___x_3685_ = l_Lean_Expr_hasFVar(v_e_3608_);
if (v___x_3685_ == 0)
{
lean_object* v___x_3686_; 
lean_dec(v___x_3610_);
lean_dec(v_cellCount_3609_);
v___x_3686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3686_, 0, v_e_3608_);
lean_ctor_set(v___x_3686_, 1, v___y_3616_);
return v___x_3686_;
}
else
{
if (v___x_3614_ == 0)
{
v_a_3618_ = v___y_3616_;
goto v___jp_3617_;
}
else
{
lean_object* v___x_3687_; 
lean_dec(v___x_3610_);
lean_dec(v_cellCount_3609_);
v___x_3687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3687_, 0, v_e_3608_);
lean_ctor_set(v___x_3687_, 1, v___y_3616_);
return v___x_3687_;
}
}
}
}
v___jp_3617_:
{
switch(lean_obj_tag(v_e_3608_))
{
case 9:
{
lean_object* v___x_3619_; 
lean_dec(v___x_3610_);
lean_dec(v_cellCount_3609_);
v___x_3619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3619_, 0, v_e_3608_);
lean_ctor_set(v___x_3619_, 1, v_a_3618_);
return v___x_3619_;
}
case 2:
{
lean_object* v___x_3620_; 
lean_dec(v___x_3610_);
lean_dec(v_cellCount_3609_);
v___x_3620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3620_, 0, v_e_3608_);
lean_ctor_set(v___x_3620_, 1, v_a_3618_);
return v___x_3620_;
}
case 0:
{
lean_object* v___x_3621_; 
lean_dec(v___x_3610_);
lean_dec(v_cellCount_3609_);
v___x_3621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3621_, 0, v_e_3608_);
lean_ctor_set(v___x_3621_, 1, v_a_3618_);
return v___x_3621_;
}
case 1:
{
lean_object* v___x_3622_; 
lean_dec(v___x_3610_);
lean_dec(v_cellCount_3609_);
v___x_3622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3622_, 0, v_e_3608_);
lean_ctor_set(v___x_3622_, 1, v_a_3618_);
return v___x_3622_;
}
case 4:
{
lean_object* v___x_3623_; 
lean_dec(v___x_3610_);
lean_dec(v_cellCount_3609_);
v___x_3623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3623_, 0, v_e_3608_);
lean_ctor_set(v___x_3623_, 1, v_a_3618_);
return v___x_3623_;
}
case 3:
{
lean_object* v___x_3624_; 
lean_dec(v___x_3610_);
lean_dec(v_cellCount_3609_);
v___x_3624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3624_, 0, v_e_3608_);
lean_ctor_set(v___x_3624_, 1, v_a_3618_);
return v___x_3624_;
}
default: 
{
lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; 
lean_inc(v_cellCount_3609_);
v___x_3625_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_3609_);
v___x_3626_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_3609_);
lean_inc(v___x_3610_);
v___x_3627_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3627_, 0, v___x_3610_);
lean_ctor_set(v___x_3627_, 1, v___x_3625_);
lean_ctor_set(v___x_3627_, 2, v___x_3626_);
v___x_3628_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6(v_fst_3611_, v___x_3612_, v___x_3612_, v_e_3608_, v___x_3610_, v___x_3627_, v_debug_3613_, v___y_3615_, v_a_3618_);
if (lean_obj_tag(v___x_3628_) == 0)
{
lean_object* v_a_3629_; lean_object* v_a_3630_; lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3638_; 
v_a_3629_ = lean_ctor_get(v___x_3628_, 0);
v_a_3630_ = lean_ctor_get(v___x_3628_, 1);
v_isSharedCheck_3638_ = !lean_is_exclusive(v___x_3628_);
if (v_isSharedCheck_3638_ == 0)
{
v___x_3632_ = v___x_3628_;
v_isShared_3633_ = v_isSharedCheck_3638_;
goto v_resetjp_3631_;
}
else
{
lean_inc(v_a_3630_);
lean_inc(v_a_3629_);
lean_dec(v___x_3628_);
v___x_3632_ = lean_box(0);
v_isShared_3633_ = v_isSharedCheck_3638_;
goto v_resetjp_3631_;
}
v_resetjp_3631_:
{
lean_object* v_fst_3634_; lean_object* v___x_3636_; 
v_fst_3634_ = lean_ctor_get(v_a_3629_, 0);
lean_inc(v_fst_3634_);
lean_dec(v_a_3629_);
if (v_isShared_3633_ == 0)
{
lean_ctor_set(v___x_3632_, 0, v_fst_3634_);
v___x_3636_ = v___x_3632_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_fst_3634_);
lean_ctor_set(v_reuseFailAlloc_3637_, 1, v_a_3630_);
v___x_3636_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
return v___x_3636_;
}
}
}
else
{
lean_object* v_a_3639_; lean_object* v_a_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3647_; 
v_a_3639_ = lean_ctor_get(v___x_3628_, 0);
v_a_3640_ = lean_ctor_get(v___x_3628_, 1);
v_isSharedCheck_3647_ = !lean_is_exclusive(v___x_3628_);
if (v_isSharedCheck_3647_ == 0)
{
v___x_3642_ = v___x_3628_;
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_a_3640_);
lean_inc(v_a_3639_);
lean_dec(v___x_3628_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v___x_3645_; 
if (v_isShared_3643_ == 0)
{
v___x_3645_ = v___x_3642_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v_a_3639_);
lean_ctor_set(v_reuseFailAlloc_3646_, 1, v_a_3640_);
v___x_3645_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
return v___x_3645_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___lam__0___boxed(lean_object* v_e_3688_, lean_object* v_cellCount_3689_, lean_object* v___x_3690_, lean_object* v_fst_3691_, lean_object* v___x_3692_, lean_object* v_debug_3693_, lean_object* v___x_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_){
_start:
{
uint8_t v_debug_boxed_3697_; uint8_t v___x_20148__boxed_3698_; lean_object* v_res_3699_; 
v_debug_boxed_3697_ = lean_unbox(v_debug_3693_);
v___x_20148__boxed_3698_ = lean_unbox(v___x_3694_);
v_res_3699_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___lam__0(v_e_3688_, v_cellCount_3689_, v___x_3690_, v_fst_3691_, v___x_3692_, v_debug_boxed_3697_, v___x_20148__boxed_3698_, v___y_3695_, v___y_3696_);
lean_dec_ref(v___y_3695_);
lean_dec(v___x_3692_);
lean_dec(v_fst_3691_);
return v_res_3699_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__8___lam__0(lean_object* v_piece_3700_, lean_object* v___x_3701_, lean_object* v___x_3702_, lean_object* v_i_3703_, lean_object* v___x_3704_, uint8_t v_debug_3705_, uint8_t v___x_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_){
_start:
{
lean_object* v_a_3710_; 
switch(lean_obj_tag(v_piece_3700_))
{
case 1:
{
lean_object* v_fvarId_3740_; lean_object* v___x_3741_; 
v_fvarId_3740_ = lean_ctor_get(v_piece_3700_, 0);
v___x_3741_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3___redArg(v___x_3702_, v_fvarId_3740_);
if (lean_obj_tag(v___x_3741_) == 1)
{
lean_object* v_val_3742_; uint8_t v___x_3743_; 
v_val_3742_ = lean_ctor_get(v___x_3741_, 0);
lean_inc(v_val_3742_);
lean_dec_ref_known(v___x_3741_, 1);
v___x_3743_ = lean_nat_dec_lt(v_val_3742_, v_i_3703_);
if (v___x_3743_ == 0)
{
lean_object* v___x_3744_; lean_object* v___x_3745_; 
lean_dec(v_val_3742_);
v___x_3744_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6_spec__9___closed__2, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6_spec__9___closed__2_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6_spec__9___closed__2);
v___x_3745_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4(v___x_3744_, v_debug_3705_, v___y_3707_, v___y_3708_);
if (lean_obj_tag(v___x_3745_) == 0)
{
lean_object* v_a_3746_; 
v_a_3746_ = lean_ctor_get(v___x_3745_, 0);
lean_inc(v_a_3746_);
if (lean_obj_tag(v_a_3746_) == 1)
{
lean_object* v_a_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3755_; 
lean_dec_ref_known(v_piece_3700_, 1);
lean_dec(v___x_3701_);
v_a_3747_ = lean_ctor_get(v___x_3745_, 1);
v_isSharedCheck_3755_ = !lean_is_exclusive(v___x_3745_);
if (v_isSharedCheck_3755_ == 0)
{
lean_object* v_unused_3756_; 
v_unused_3756_ = lean_ctor_get(v___x_3745_, 0);
lean_dec(v_unused_3756_);
v___x_3749_ = v___x_3745_;
v_isShared_3750_ = v_isSharedCheck_3755_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_a_3747_);
lean_dec(v___x_3745_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3755_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v_val_3751_; lean_object* v___x_3753_; 
v_val_3751_ = lean_ctor_get(v_a_3746_, 0);
lean_inc(v_val_3751_);
lean_dec_ref_known(v_a_3746_, 1);
if (v_isShared_3750_ == 0)
{
lean_ctor_set(v___x_3749_, 0, v_val_3751_);
v___x_3753_ = v___x_3749_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_val_3751_);
lean_ctor_set(v_reuseFailAlloc_3754_, 1, v_a_3747_);
v___x_3753_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
return v___x_3753_;
}
}
}
else
{
lean_object* v_a_3757_; 
lean_dec(v_a_3746_);
v_a_3757_ = lean_ctor_get(v___x_3745_, 1);
lean_inc(v_a_3757_);
lean_dec_ref_known(v___x_3745_, 2);
v_a_3710_ = v_a_3757_;
goto v___jp_3709_;
}
}
else
{
lean_object* v_a_3758_; lean_object* v_a_3759_; lean_object* v___x_3761_; uint8_t v_isShared_3762_; uint8_t v_isSharedCheck_3766_; 
lean_dec_ref_known(v_piece_3700_, 1);
lean_dec(v___x_3701_);
v_a_3758_ = lean_ctor_get(v___x_3745_, 0);
v_a_3759_ = lean_ctor_get(v___x_3745_, 1);
v_isSharedCheck_3766_ = !lean_is_exclusive(v___x_3745_);
if (v_isSharedCheck_3766_ == 0)
{
v___x_3761_ = v___x_3745_;
v_isShared_3762_ = v_isSharedCheck_3766_;
goto v_resetjp_3760_;
}
else
{
lean_inc(v_a_3759_);
lean_inc(v_a_3758_);
lean_dec(v___x_3745_);
v___x_3761_ = lean_box(0);
v_isShared_3762_ = v_isSharedCheck_3766_;
goto v_resetjp_3760_;
}
v_resetjp_3760_:
{
lean_object* v___x_3764_; 
if (v_isShared_3762_ == 0)
{
v___x_3764_ = v___x_3761_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v_a_3758_);
lean_ctor_set(v_reuseFailAlloc_3765_, 1, v_a_3759_);
v___x_3764_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
return v___x_3764_;
}
}
}
}
else
{
lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; 
lean_dec_ref_known(v_piece_3700_, 1);
lean_dec(v___x_3701_);
v___x_3767_ = lean_nat_sub(v_i_3703_, v_val_3742_);
lean_dec(v_val_3742_);
v___x_3768_ = lean_unsigned_to_nat(1u);
v___x_3769_ = lean_nat_sub(v___x_3767_, v___x_3768_);
lean_dec(v___x_3767_);
v___x_3770_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5___redArg(v___x_3769_, v___y_3708_);
return v___x_3770_;
}
}
else
{
lean_object* v___x_3771_; 
lean_dec(v___x_3741_);
lean_dec(v___x_3701_);
v___x_3771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3771_, 0, v_piece_3700_);
lean_ctor_set(v___x_3771_, 1, v___y_3708_);
return v___x_3771_;
}
}
case 9:
{
lean_object* v___x_3772_; 
lean_dec(v___x_3701_);
v___x_3772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3772_, 0, v_piece_3700_);
lean_ctor_set(v___x_3772_, 1, v___y_3708_);
return v___x_3772_;
}
case 2:
{
lean_object* v___x_3773_; 
lean_dec(v___x_3701_);
v___x_3773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3773_, 0, v_piece_3700_);
lean_ctor_set(v___x_3773_, 1, v___y_3708_);
return v___x_3773_;
}
case 0:
{
lean_object* v___x_3774_; 
lean_dec(v___x_3701_);
v___x_3774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3774_, 0, v_piece_3700_);
lean_ctor_set(v___x_3774_, 1, v___y_3708_);
return v___x_3774_;
}
case 4:
{
lean_object* v___x_3775_; 
lean_dec(v___x_3701_);
v___x_3775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3775_, 0, v_piece_3700_);
lean_ctor_set(v___x_3775_, 1, v___y_3708_);
return v___x_3775_;
}
case 3:
{
lean_object* v___x_3776_; 
lean_dec(v___x_3701_);
v___x_3776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3776_, 0, v_piece_3700_);
lean_ctor_set(v___x_3776_, 1, v___y_3708_);
return v___x_3776_;
}
default: 
{
uint8_t v___x_3777_; 
v___x_3777_ = l_Lean_Expr_hasFVar(v_piece_3700_);
if (v___x_3777_ == 0)
{
lean_object* v___x_3778_; 
lean_dec(v___x_3701_);
v___x_3778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3778_, 0, v_piece_3700_);
lean_ctor_set(v___x_3778_, 1, v___y_3708_);
return v___x_3778_;
}
else
{
if (v___x_3706_ == 0)
{
v_a_3710_ = v___y_3708_;
goto v___jp_3709_;
}
else
{
lean_object* v___x_3779_; 
lean_dec(v___x_3701_);
v___x_3779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3779_, 0, v_piece_3700_);
lean_ctor_set(v___x_3779_, 1, v___y_3708_);
return v___x_3779_;
}
}
}
}
v___jp_3709_:
{
switch(lean_obj_tag(v_piece_3700_))
{
case 9:
{
lean_object* v___x_3711_; 
lean_dec(v___x_3701_);
v___x_3711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3711_, 0, v_piece_3700_);
lean_ctor_set(v___x_3711_, 1, v_a_3710_);
return v___x_3711_;
}
case 2:
{
lean_object* v___x_3712_; 
lean_dec(v___x_3701_);
v___x_3712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3712_, 0, v_piece_3700_);
lean_ctor_set(v___x_3712_, 1, v_a_3710_);
return v___x_3712_;
}
case 0:
{
lean_object* v___x_3713_; 
lean_dec(v___x_3701_);
v___x_3713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3713_, 0, v_piece_3700_);
lean_ctor_set(v___x_3713_, 1, v_a_3710_);
return v___x_3713_;
}
case 1:
{
lean_object* v___x_3714_; 
lean_dec(v___x_3701_);
v___x_3714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3714_, 0, v_piece_3700_);
lean_ctor_set(v___x_3714_, 1, v_a_3710_);
return v___x_3714_;
}
case 4:
{
lean_object* v___x_3715_; 
lean_dec(v___x_3701_);
v___x_3715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3715_, 0, v_piece_3700_);
lean_ctor_set(v___x_3715_, 1, v_a_3710_);
return v___x_3715_;
}
case 3:
{
lean_object* v___x_3716_; 
lean_dec(v___x_3701_);
v___x_3716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3716_, 0, v_piece_3700_);
lean_ctor_set(v___x_3716_, 1, v_a_3710_);
return v___x_3716_;
}
default: 
{
lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; 
v___x_3717_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__0, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__0_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__0);
v___x_3718_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__1, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__1);
lean_inc(v___x_3701_);
v___x_3719_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3719_, 0, v___x_3701_);
lean_ctor_set(v___x_3719_, 1, v___x_3717_);
lean_ctor_set(v___x_3719_, 2, v___x_3718_);
v___x_3720_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6(v___x_3702_, v_i_3703_, v___x_3704_, v_piece_3700_, v___x_3701_, v___x_3719_, v_debug_3705_, v___y_3707_, v_a_3710_);
if (lean_obj_tag(v___x_3720_) == 0)
{
lean_object* v_a_3721_; lean_object* v_a_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3730_; 
v_a_3721_ = lean_ctor_get(v___x_3720_, 0);
v_a_3722_ = lean_ctor_get(v___x_3720_, 1);
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3724_ = v___x_3720_;
v_isShared_3725_ = v_isSharedCheck_3730_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_a_3722_);
lean_inc(v_a_3721_);
lean_dec(v___x_3720_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3730_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v_fst_3726_; lean_object* v___x_3728_; 
v_fst_3726_ = lean_ctor_get(v_a_3721_, 0);
lean_inc(v_fst_3726_);
lean_dec(v_a_3721_);
if (v_isShared_3725_ == 0)
{
lean_ctor_set(v___x_3724_, 0, v_fst_3726_);
v___x_3728_ = v___x_3724_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v_fst_3726_);
lean_ctor_set(v_reuseFailAlloc_3729_, 1, v_a_3722_);
v___x_3728_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
return v___x_3728_;
}
}
}
else
{
lean_object* v_a_3731_; lean_object* v_a_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3739_; 
v_a_3731_ = lean_ctor_get(v___x_3720_, 0);
v_a_3732_ = lean_ctor_get(v___x_3720_, 1);
v_isSharedCheck_3739_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3739_ == 0)
{
v___x_3734_ = v___x_3720_;
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_a_3732_);
lean_inc(v_a_3731_);
lean_dec(v___x_3720_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v___x_3737_; 
if (v_isShared_3735_ == 0)
{
v___x_3737_ = v___x_3734_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_a_3731_);
lean_ctor_set(v_reuseFailAlloc_3738_, 1, v_a_3732_);
v___x_3737_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
return v___x_3737_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__8___lam__0___boxed(lean_object* v_piece_3780_, lean_object* v___x_3781_, lean_object* v___x_3782_, lean_object* v_i_3783_, lean_object* v___x_3784_, lean_object* v_debug_3785_, lean_object* v___x_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_){
_start:
{
uint8_t v_debug_boxed_3789_; uint8_t v___x_20333__boxed_3790_; lean_object* v_res_3791_; 
v_debug_boxed_3789_ = lean_unbox(v_debug_3785_);
v___x_20333__boxed_3790_ = lean_unbox(v___x_3786_);
v_res_3791_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__8___lam__0(v_piece_3780_, v___x_3781_, v___x_3782_, v_i_3783_, v___x_3784_, v_debug_boxed_3789_, v___x_20333__boxed_3790_, v___y_3787_, v___y_3788_);
lean_dec_ref(v___y_3787_);
lean_dec(v___x_3784_);
lean_dec(v_i_3783_);
lean_dec_ref(v___x_3782_);
return v_res_3791_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__8___lam__1(lean_object* v___x_3792_, lean_object* v___x_3793_, lean_object* v___x_3794_, uint8_t v___x_3795_, lean_object* v_piece_3796_, lean_object* v_i_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_){
_start:
{
lean_object* v___x_3806_; lean_object* v___x_3807_; uint8_t v_debug_3808_; lean_object* v_env_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___f_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; 
v___x_3806_ = lean_st_ref_get(v___y_3800_);
v___x_3807_ = lean_st_ref_get(v___y_3804_);
v_debug_3808_ = lean_ctor_get_uint8(v___x_3806_, sizeof(void*)*11);
lean_dec(v___x_3806_);
v_env_3809_ = lean_ctor_get(v___x_3807_, 0);
lean_inc_ref(v_env_3809_);
lean_dec(v___x_3807_);
v___x_3810_ = lean_box(v_debug_3808_);
v___x_3811_ = lean_box(v___x_3795_);
v___f_3812_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__8___lam__0___boxed), 9, 7);
lean_closure_set(v___f_3812_, 0, v_piece_3796_);
lean_closure_set(v___f_3812_, 1, v___x_3792_);
lean_closure_set(v___f_3812_, 2, v___x_3793_);
lean_closure_set(v___f_3812_, 3, v_i_3797_);
lean_closure_set(v___f_3812_, 4, v___x_3794_);
lean_closure_set(v___f_3812_, 5, v___x_3810_);
lean_closure_set(v___f_3812_, 6, v___x_3811_);
v___x_3813_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_3813_, 0, v_env_3809_);
lean_ctor_set_uint8(v___x_3813_, sizeof(void*)*1, v___x_3795_);
lean_ctor_set_uint8(v___x_3813_, sizeof(void*)*1 + 1, v___x_3795_);
v___x_3814_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_3812_, v___x_3813_, v___y_3800_);
if (lean_obj_tag(v___x_3814_) == 0)
{
lean_object* v_a_3815_; lean_object* v___x_3817_; uint8_t v_isShared_3818_; uint8_t v_isSharedCheck_3825_; 
v_a_3815_ = lean_ctor_get(v___x_3814_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3814_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3817_ = v___x_3814_;
v_isShared_3818_ = v_isSharedCheck_3825_;
goto v_resetjp_3816_;
}
else
{
lean_inc(v_a_3815_);
lean_dec(v___x_3814_);
v___x_3817_ = lean_box(0);
v_isShared_3818_ = v_isSharedCheck_3825_;
goto v_resetjp_3816_;
}
v_resetjp_3816_:
{
if (lean_obj_tag(v_a_3815_) == 0)
{
lean_object* v___x_3819_; lean_object* v___x_3820_; 
lean_dec_ref_known(v_a_3815_, 1);
lean_del_object(v___x_3817_);
v___x_3819_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2);
v___x_3820_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1(v___x_3819_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_);
return v___x_3820_;
}
else
{
lean_object* v_a_3821_; lean_object* v___x_3823_; 
v_a_3821_ = lean_ctor_get(v_a_3815_, 0);
lean_inc(v_a_3821_);
lean_dec_ref_known(v_a_3815_, 1);
if (v_isShared_3818_ == 0)
{
lean_ctor_set(v___x_3817_, 0, v_a_3821_);
v___x_3823_ = v___x_3817_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v_a_3821_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
return v___x_3823_;
}
}
}
}
else
{
lean_object* v_a_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3833_; 
v_a_3826_ = lean_ctor_get(v___x_3814_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3814_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3828_ = v___x_3814_;
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_a_3826_);
lean_dec(v___x_3814_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v___x_3831_; 
if (v_isShared_3829_ == 0)
{
v___x_3831_ = v___x_3828_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_a_3826_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__8___lam__1___boxed(lean_object* v___x_3834_, lean_object* v___x_3835_, lean_object* v___x_3836_, lean_object* v___x_3837_, lean_object* v_piece_3838_, lean_object* v_i_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_){
_start:
{
uint8_t v___x_20518__boxed_3848_; lean_object* v_res_3849_; 
v___x_20518__boxed_3848_ = lean_unbox(v___x_3837_);
v_res_3849_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__8___lam__1(v___x_3834_, v___x_3835_, v___x_3836_, v___x_20518__boxed_3848_, v_piece_3838_, v_i_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_);
lean_dec(v___y_3846_);
lean_dec_ref(v___y_3845_);
lean_dec(v___y_3844_);
lean_dec_ref(v___y_3843_);
lean_dec(v___y_3842_);
lean_dec_ref(v___y_3841_);
lean_dec(v___y_3840_);
return v_res_3849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__8_spec__12(lean_object* v___x_3850_, lean_object* v___x_3851_, lean_object* v_as_3852_, size_t v_sz_3853_, size_t v_i_3854_, lean_object* v_b_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_){
_start:
{
uint8_t v___x_3864_; 
v___x_3864_ = lean_usize_dec_lt(v_i_3854_, v_sz_3853_);
if (v___x_3864_ == 0)
{
lean_object* v___x_3865_; 
lean_dec(v___x_3851_);
lean_dec_ref(v___x_3850_);
v___x_3865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3865_, 0, v_b_3855_);
return v___x_3865_;
}
else
{
lean_object* v_fst_3866_; lean_object* v_snd_3867_; lean_object* v___x_3869_; uint8_t v_isShared_3870_; uint8_t v_isSharedCheck_3916_; 
v_fst_3866_ = lean_ctor_get(v_b_3855_, 0);
v_snd_3867_ = lean_ctor_get(v_b_3855_, 1);
v_isSharedCheck_3916_ = !lean_is_exclusive(v_b_3855_);
if (v_isSharedCheck_3916_ == 0)
{
v___x_3869_ = v_b_3855_;
v_isShared_3870_ = v_isSharedCheck_3916_;
goto v_resetjp_3868_;
}
else
{
lean_inc(v_snd_3867_);
lean_inc(v_fst_3866_);
lean_dec(v_b_3855_);
v___x_3869_ = lean_box(0);
v_isShared_3870_ = v_isSharedCheck_3916_;
goto v_resetjp_3868_;
}
v_resetjp_3868_:
{
lean_object* v_a_3871_; lean_object* v_userName_3872_; lean_object* v_type_3873_; lean_object* v_value_3874_; uint8_t v_nondep_3875_; lean_object* v___x_3876_; uint8_t v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; 
v_a_3871_ = lean_array_uget_borrowed(v_as_3852_, v_i_3854_);
v_userName_3872_ = lean_ctor_get(v_a_3871_, 1);
v_type_3873_ = lean_ctor_get(v_a_3871_, 2);
v_value_3874_ = lean_ctor_get(v_a_3871_, 3);
v_nondep_3875_ = lean_ctor_get_uint8(v_a_3871_, sizeof(void*)*4);
v___x_3876_ = lean_unsigned_to_nat(0u);
v___x_3877_ = lean_nat_dec_eq(v___x_3851_, v___x_3876_);
v___x_3878_ = lean_unsigned_to_nat(1u);
v___x_3879_ = lean_nat_sub(v_snd_3867_, v___x_3878_);
lean_dec(v_snd_3867_);
lean_inc(v___x_3879_);
lean_inc_ref(v_type_3873_);
lean_inc(v___x_3851_);
lean_inc_ref(v___x_3850_);
v___x_3880_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__8___lam__1(v___x_3876_, v___x_3850_, v___x_3851_, v___x_3877_, v_type_3873_, v___x_3879_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_);
if (lean_obj_tag(v___x_3880_) == 0)
{
lean_object* v_a_3881_; lean_object* v___x_3882_; 
v_a_3881_ = lean_ctor_get(v___x_3880_, 0);
lean_inc(v_a_3881_);
lean_dec_ref_known(v___x_3880_, 1);
lean_inc(v___x_3879_);
lean_inc_ref(v_value_3874_);
lean_inc(v___x_3851_);
lean_inc_ref(v___x_3850_);
v___x_3882_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__8___lam__1(v___x_3876_, v___x_3850_, v___x_3851_, v___x_3877_, v_value_3874_, v___x_3879_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_);
if (lean_obj_tag(v___x_3882_) == 0)
{
lean_object* v_a_3883_; lean_object* v___x_3884_; 
v_a_3883_ = lean_ctor_get(v___x_3882_, 0);
lean_inc(v_a_3883_);
lean_dec_ref_known(v___x_3882_, 1);
lean_inc(v_userName_3872_);
v___x_3884_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___redArg(v_userName_3872_, v_a_3881_, v_a_3883_, v_fst_3866_, v_nondep_3875_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_);
if (lean_obj_tag(v___x_3884_) == 0)
{
lean_object* v_a_3885_; lean_object* v___x_3887_; 
v_a_3885_ = lean_ctor_get(v___x_3884_, 0);
lean_inc(v_a_3885_);
lean_dec_ref_known(v___x_3884_, 1);
if (v_isShared_3870_ == 0)
{
lean_ctor_set(v___x_3869_, 1, v___x_3879_);
lean_ctor_set(v___x_3869_, 0, v_a_3885_);
v___x_3887_ = v___x_3869_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v_a_3885_);
lean_ctor_set(v_reuseFailAlloc_3891_, 1, v___x_3879_);
v___x_3887_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
size_t v___x_3888_; size_t v___x_3889_; 
v___x_3888_ = ((size_t)1ULL);
v___x_3889_ = lean_usize_add(v_i_3854_, v___x_3888_);
v_i_3854_ = v___x_3889_;
v_b_3855_ = v___x_3887_;
goto _start;
}
}
else
{
lean_object* v_a_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3899_; 
lean_dec(v___x_3879_);
lean_del_object(v___x_3869_);
lean_dec(v___x_3851_);
lean_dec_ref(v___x_3850_);
v_a_3892_ = lean_ctor_get(v___x_3884_, 0);
v_isSharedCheck_3899_ = !lean_is_exclusive(v___x_3884_);
if (v_isSharedCheck_3899_ == 0)
{
v___x_3894_ = v___x_3884_;
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_a_3892_);
lean_dec(v___x_3884_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
lean_object* v___x_3897_; 
if (v_isShared_3895_ == 0)
{
v___x_3897_ = v___x_3894_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v_a_3892_);
v___x_3897_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
return v___x_3897_;
}
}
}
}
else
{
lean_object* v_a_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3907_; 
lean_dec(v_a_3881_);
lean_dec(v___x_3879_);
lean_del_object(v___x_3869_);
lean_dec(v_fst_3866_);
lean_dec(v___x_3851_);
lean_dec_ref(v___x_3850_);
v_a_3900_ = lean_ctor_get(v___x_3882_, 0);
v_isSharedCheck_3907_ = !lean_is_exclusive(v___x_3882_);
if (v_isSharedCheck_3907_ == 0)
{
v___x_3902_ = v___x_3882_;
v_isShared_3903_ = v_isSharedCheck_3907_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_a_3900_);
lean_dec(v___x_3882_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3907_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
lean_object* v___x_3905_; 
if (v_isShared_3903_ == 0)
{
v___x_3905_ = v___x_3902_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v_a_3900_);
v___x_3905_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
return v___x_3905_;
}
}
}
}
else
{
lean_object* v_a_3908_; lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3915_; 
lean_dec(v___x_3879_);
lean_del_object(v___x_3869_);
lean_dec(v_fst_3866_);
lean_dec(v___x_3851_);
lean_dec_ref(v___x_3850_);
v_a_3908_ = lean_ctor_get(v___x_3880_, 0);
v_isSharedCheck_3915_ = !lean_is_exclusive(v___x_3880_);
if (v_isSharedCheck_3915_ == 0)
{
v___x_3910_ = v___x_3880_;
v_isShared_3911_ = v_isSharedCheck_3915_;
goto v_resetjp_3909_;
}
else
{
lean_inc(v_a_3908_);
lean_dec(v___x_3880_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3915_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
lean_object* v___x_3913_; 
if (v_isShared_3911_ == 0)
{
v___x_3913_ = v___x_3910_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v_a_3908_);
v___x_3913_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
return v___x_3913_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__8_spec__12___boxed(lean_object* v___x_3917_, lean_object* v___x_3918_, lean_object* v_as_3919_, lean_object* v_sz_3920_, lean_object* v_i_3921_, lean_object* v_b_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_){
_start:
{
size_t v_sz_boxed_3931_; size_t v_i_boxed_3932_; lean_object* v_res_3933_; 
v_sz_boxed_3931_ = lean_unbox_usize(v_sz_3920_);
lean_dec(v_sz_3920_);
v_i_boxed_3932_ = lean_unbox_usize(v_i_3921_);
lean_dec(v_i_3921_);
v_res_3933_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__8_spec__12(v___x_3917_, v___x_3918_, v_as_3919_, v_sz_boxed_3931_, v_i_boxed_3932_, v_b_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_);
lean_dec(v___y_3929_);
lean_dec_ref(v___y_3928_);
lean_dec(v___y_3927_);
lean_dec_ref(v___y_3926_);
lean_dec(v___y_3925_);
lean_dec_ref(v___y_3924_);
lean_dec(v___y_3923_);
lean_dec_ref(v_as_3919_);
return v_res_3933_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__8(lean_object* v___x_3934_, lean_object* v___x_3935_, lean_object* v_as_3936_, size_t v_sz_3937_, size_t v_i_3938_, lean_object* v_b_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_){
_start:
{
uint8_t v___x_3948_; 
v___x_3948_ = lean_usize_dec_lt(v_i_3938_, v_sz_3937_);
if (v___x_3948_ == 0)
{
lean_object* v___x_3949_; 
lean_dec(v___x_3935_);
lean_dec_ref(v___x_3934_);
v___x_3949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3949_, 0, v_b_3939_);
return v___x_3949_;
}
else
{
lean_object* v_fst_3950_; lean_object* v_snd_3951_; lean_object* v___x_3953_; uint8_t v_isShared_3954_; uint8_t v_isSharedCheck_4000_; 
v_fst_3950_ = lean_ctor_get(v_b_3939_, 0);
v_snd_3951_ = lean_ctor_get(v_b_3939_, 1);
v_isSharedCheck_4000_ = !lean_is_exclusive(v_b_3939_);
if (v_isSharedCheck_4000_ == 0)
{
v___x_3953_ = v_b_3939_;
v_isShared_3954_ = v_isSharedCheck_4000_;
goto v_resetjp_3952_;
}
else
{
lean_inc(v_snd_3951_);
lean_inc(v_fst_3950_);
lean_dec(v_b_3939_);
v___x_3953_ = lean_box(0);
v_isShared_3954_ = v_isSharedCheck_4000_;
goto v_resetjp_3952_;
}
v_resetjp_3952_:
{
lean_object* v_a_3955_; lean_object* v_userName_3956_; lean_object* v_type_3957_; lean_object* v_value_3958_; uint8_t v_nondep_3959_; lean_object* v___x_3960_; uint8_t v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; 
v_a_3955_ = lean_array_uget_borrowed(v_as_3936_, v_i_3938_);
v_userName_3956_ = lean_ctor_get(v_a_3955_, 1);
v_type_3957_ = lean_ctor_get(v_a_3955_, 2);
v_value_3958_ = lean_ctor_get(v_a_3955_, 3);
v_nondep_3959_ = lean_ctor_get_uint8(v_a_3955_, sizeof(void*)*4);
v___x_3960_ = lean_unsigned_to_nat(0u);
v___x_3961_ = lean_nat_dec_eq(v___x_3935_, v___x_3960_);
v___x_3962_ = lean_unsigned_to_nat(1u);
v___x_3963_ = lean_nat_sub(v_snd_3951_, v___x_3962_);
lean_dec(v_snd_3951_);
lean_inc(v___x_3963_);
lean_inc_ref(v_type_3957_);
lean_inc(v___x_3935_);
lean_inc_ref(v___x_3934_);
v___x_3964_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__8___lam__1(v___x_3960_, v___x_3934_, v___x_3935_, v___x_3961_, v_type_3957_, v___x_3963_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_);
if (lean_obj_tag(v___x_3964_) == 0)
{
lean_object* v_a_3965_; lean_object* v___x_3966_; 
v_a_3965_ = lean_ctor_get(v___x_3964_, 0);
lean_inc(v_a_3965_);
lean_dec_ref_known(v___x_3964_, 1);
lean_inc(v___x_3963_);
lean_inc_ref(v_value_3958_);
lean_inc(v___x_3935_);
lean_inc_ref(v___x_3934_);
v___x_3966_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__8___lam__1(v___x_3960_, v___x_3934_, v___x_3935_, v___x_3961_, v_value_3958_, v___x_3963_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_);
if (lean_obj_tag(v___x_3966_) == 0)
{
lean_object* v_a_3967_; lean_object* v___x_3968_; 
v_a_3967_ = lean_ctor_get(v___x_3966_, 0);
lean_inc(v_a_3967_);
lean_dec_ref_known(v___x_3966_, 1);
lean_inc(v_userName_3956_);
v___x_3968_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___redArg(v_userName_3956_, v_a_3965_, v_a_3967_, v_fst_3950_, v_nondep_3959_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_);
if (lean_obj_tag(v___x_3968_) == 0)
{
lean_object* v_a_3969_; lean_object* v___x_3971_; 
v_a_3969_ = lean_ctor_get(v___x_3968_, 0);
lean_inc(v_a_3969_);
lean_dec_ref_known(v___x_3968_, 1);
if (v_isShared_3954_ == 0)
{
lean_ctor_set(v___x_3953_, 1, v___x_3963_);
lean_ctor_set(v___x_3953_, 0, v_a_3969_);
v___x_3971_ = v___x_3953_;
goto v_reusejp_3970_;
}
else
{
lean_object* v_reuseFailAlloc_3975_; 
v_reuseFailAlloc_3975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3975_, 0, v_a_3969_);
lean_ctor_set(v_reuseFailAlloc_3975_, 1, v___x_3963_);
v___x_3971_ = v_reuseFailAlloc_3975_;
goto v_reusejp_3970_;
}
v_reusejp_3970_:
{
size_t v___x_3972_; size_t v___x_3973_; lean_object* v___x_3974_; 
v___x_3972_ = ((size_t)1ULL);
v___x_3973_ = lean_usize_add(v_i_3938_, v___x_3972_);
v___x_3974_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__8_spec__12(v___x_3934_, v___x_3935_, v_as_3936_, v_sz_3937_, v___x_3973_, v___x_3971_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_);
return v___x_3974_;
}
}
else
{
lean_object* v_a_3976_; lean_object* v___x_3978_; uint8_t v_isShared_3979_; uint8_t v_isSharedCheck_3983_; 
lean_dec(v___x_3963_);
lean_del_object(v___x_3953_);
lean_dec(v___x_3935_);
lean_dec_ref(v___x_3934_);
v_a_3976_ = lean_ctor_get(v___x_3968_, 0);
v_isSharedCheck_3983_ = !lean_is_exclusive(v___x_3968_);
if (v_isSharedCheck_3983_ == 0)
{
v___x_3978_ = v___x_3968_;
v_isShared_3979_ = v_isSharedCheck_3983_;
goto v_resetjp_3977_;
}
else
{
lean_inc(v_a_3976_);
lean_dec(v___x_3968_);
v___x_3978_ = lean_box(0);
v_isShared_3979_ = v_isSharedCheck_3983_;
goto v_resetjp_3977_;
}
v_resetjp_3977_:
{
lean_object* v___x_3981_; 
if (v_isShared_3979_ == 0)
{
v___x_3981_ = v___x_3978_;
goto v_reusejp_3980_;
}
else
{
lean_object* v_reuseFailAlloc_3982_; 
v_reuseFailAlloc_3982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3982_, 0, v_a_3976_);
v___x_3981_ = v_reuseFailAlloc_3982_;
goto v_reusejp_3980_;
}
v_reusejp_3980_:
{
return v___x_3981_;
}
}
}
}
else
{
lean_object* v_a_3984_; lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_3991_; 
lean_dec(v_a_3965_);
lean_dec(v___x_3963_);
lean_del_object(v___x_3953_);
lean_dec(v_fst_3950_);
lean_dec(v___x_3935_);
lean_dec_ref(v___x_3934_);
v_a_3984_ = lean_ctor_get(v___x_3966_, 0);
v_isSharedCheck_3991_ = !lean_is_exclusive(v___x_3966_);
if (v_isSharedCheck_3991_ == 0)
{
v___x_3986_ = v___x_3966_;
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
else
{
lean_inc(v_a_3984_);
lean_dec(v___x_3966_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
lean_object* v___x_3989_; 
if (v_isShared_3987_ == 0)
{
v___x_3989_ = v___x_3986_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v_a_3984_);
v___x_3989_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
return v___x_3989_;
}
}
}
}
else
{
lean_object* v_a_3992_; lean_object* v___x_3994_; uint8_t v_isShared_3995_; uint8_t v_isSharedCheck_3999_; 
lean_dec(v___x_3963_);
lean_del_object(v___x_3953_);
lean_dec(v_fst_3950_);
lean_dec(v___x_3935_);
lean_dec_ref(v___x_3934_);
v_a_3992_ = lean_ctor_get(v___x_3964_, 0);
v_isSharedCheck_3999_ = !lean_is_exclusive(v___x_3964_);
if (v_isSharedCheck_3999_ == 0)
{
v___x_3994_ = v___x_3964_;
v_isShared_3995_ = v_isSharedCheck_3999_;
goto v_resetjp_3993_;
}
else
{
lean_inc(v_a_3992_);
lean_dec(v___x_3964_);
v___x_3994_ = lean_box(0);
v_isShared_3995_ = v_isSharedCheck_3999_;
goto v_resetjp_3993_;
}
v_resetjp_3993_:
{
lean_object* v___x_3997_; 
if (v_isShared_3995_ == 0)
{
v___x_3997_ = v___x_3994_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v_a_3992_);
v___x_3997_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
return v___x_3997_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__8___boxed(lean_object* v___x_4001_, lean_object* v___x_4002_, lean_object* v_as_4003_, lean_object* v_sz_4004_, lean_object* v_i_4005_, lean_object* v_b_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_){
_start:
{
size_t v_sz_boxed_4015_; size_t v_i_boxed_4016_; lean_object* v_res_4017_; 
v_sz_boxed_4015_ = lean_unbox_usize(v_sz_4004_);
lean_dec(v_sz_4004_);
v_i_boxed_4016_ = lean_unbox_usize(v_i_4005_);
lean_dec(v_i_4005_);
v_res_4017_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__8(v___x_4001_, v___x_4002_, v_as_4003_, v_sz_boxed_4015_, v_i_boxed_4016_, v_b_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_);
lean_dec(v___y_4013_);
lean_dec_ref(v___y_4012_);
lean_dec(v___y_4011_);
lean_dec_ref(v___y_4010_);
lean_dec(v___y_4009_);
lean_dec_ref(v___y_4008_);
lean_dec(v___y_4007_);
lean_dec_ref(v_as_4003_);
return v_res_4017_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1_spec__2_spec__6___redArg(lean_object* v_b_4018_, lean_object* v_acc_4019_, lean_object* v_i_4020_){
_start:
{
lean_object* v___y_4022_; lean_object* v_keyArray_4030_; lean_object* v_valueArray_4031_; lean_object* v___x_4032_; uint8_t v___x_4033_; 
v_keyArray_4030_ = lean_ctor_get(v_b_4018_, 1);
v_valueArray_4031_ = lean_ctor_get(v_b_4018_, 2);
v___x_4032_ = lean_array_get_size(v_keyArray_4030_);
v___x_4033_ = lean_nat_dec_lt(v_i_4020_, v___x_4032_);
if (v___x_4033_ == 0)
{
lean_dec(v_i_4020_);
return v_acc_4019_;
}
else
{
lean_object* v___x_4034_; uint8_t v_isSome_4035_; 
v___x_4034_ = lean_array_fget_borrowed(v_keyArray_4030_, v_i_4020_);
v_isSome_4035_ = lean_noption_is_some(v___x_4034_);
if (v_isSome_4035_ == 0)
{
goto v___jp_4026_;
}
else
{
lean_object* v___x_4036_; uint8_t v_isSome_4037_; 
v___x_4036_ = lean_array_fget_borrowed(v_valueArray_4031_, v_i_4020_);
v_isSome_4037_ = lean_noption_is_some(v___x_4036_);
if (v_isSome_4037_ == 0)
{
goto v___jp_4026_;
}
else
{
lean_object* v_val_4038_; lean_object* v_val_4039_; lean_object* v_i_4041_; lean_object* v___x_4046_; 
lean_inc(v___x_4034_);
v_val_4038_ = lean_noption_get(v___x_4034_);
lean_inc(v___x_4036_);
v_val_4039_ = lean_noption_get(v___x_4036_);
v___x_4046_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0___redArg(v_acc_4019_, v_val_4038_);
switch(lean_obj_tag(v___x_4046_))
{
case 0:
{
lean_object* v_index_4047_; lean_object* v_size_4048_; lean_object* v___x_4049_; 
v_index_4047_ = lean_ctor_get(v___x_4046_, 0);
lean_inc(v_index_4047_);
lean_dec_ref_known(v___x_4046_, 3);
v_size_4048_ = lean_ctor_get(v_acc_4019_, 0);
lean_inc(v_size_4048_);
v___x_4049_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_4019_, v_size_4048_, v_index_4047_, v_val_4038_, v_val_4039_);
lean_dec(v_index_4047_);
v___y_4022_ = v___x_4049_;
goto v___jp_4021_;
}
case 1:
{
lean_object* v_index_4050_; 
v_index_4050_ = lean_ctor_get(v___x_4046_, 0);
lean_inc(v_index_4050_);
lean_dec_ref_known(v___x_4046_, 1);
v_i_4041_ = v_index_4050_;
goto v___jp_4040_;
}
default: 
{
lean_object* v___x_4051_; lean_object* v___x_4052_; 
v___x_4051_ = lean_unsigned_to_nat(0u);
v___x_4052_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_4019_, v___x_4051_);
if (lean_obj_tag(v___x_4052_) == 0)
{
lean_object* v_index_4053_; 
v_index_4053_ = lean_ctor_get(v___x_4052_, 0);
lean_inc(v_index_4053_);
lean_dec_ref_known(v___x_4052_, 1);
v_i_4041_ = v_index_4053_;
goto v___jp_4040_;
}
else
{
lean_dec(v_val_4039_);
lean_dec(v_val_4038_);
v___y_4022_ = v_acc_4019_;
goto v___jp_4021_;
}
}
}
v___jp_4040_:
{
lean_object* v_size_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; 
v_size_4042_ = lean_ctor_get(v_acc_4019_, 0);
v___x_4043_ = lean_unsigned_to_nat(1u);
v___x_4044_ = lean_nat_add(v_size_4042_, v___x_4043_);
v___x_4045_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_4019_, v___x_4044_, v_i_4041_, v_val_4038_, v_val_4039_);
lean_dec(v_i_4041_);
v___y_4022_ = v___x_4045_;
goto v___jp_4021_;
}
}
}
}
v___jp_4021_:
{
lean_object* v___x_4023_; lean_object* v___x_4024_; 
v___x_4023_ = lean_unsigned_to_nat(1u);
v___x_4024_ = lean_nat_add(v_i_4020_, v___x_4023_);
lean_dec(v_i_4020_);
v_acc_4019_ = v___y_4022_;
v_i_4020_ = v___x_4024_;
goto _start;
}
v___jp_4026_:
{
lean_object* v___x_4027_; lean_object* v___x_4028_; 
v___x_4027_ = lean_unsigned_to_nat(1u);
v___x_4028_ = lean_nat_add(v_i_4020_, v___x_4027_);
lean_dec(v_i_4020_);
v_i_4020_ = v___x_4028_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_b_4054_, lean_object* v_acc_4055_, lean_object* v_i_4056_){
_start:
{
lean_object* v_res_4057_; 
v_res_4057_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1_spec__2_spec__6___redArg(v_b_4054_, v_acc_4055_, v_i_4056_);
lean_dec_ref(v_b_4054_);
return v_res_4057_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1_spec__2___redArg(lean_object* v_init_4058_, lean_object* v_b_4059_){
_start:
{
lean_object* v___x_4060_; lean_object* v___x_4061_; 
v___x_4060_ = lean_unsigned_to_nat(0u);
v___x_4061_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1_spec__2_spec__6___redArg(v_b_4059_, v_init_4058_, v___x_4060_);
return v___x_4061_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1_spec__2___redArg___boxed(lean_object* v_init_4062_, lean_object* v_b_4063_){
_start:
{
lean_object* v_res_4064_; 
v_res_4064_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1_spec__2___redArg(v_init_4062_, v_b_4063_);
lean_dec_ref(v_b_4063_);
return v_res_4064_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1___redArg(lean_object* v_m_4065_){
_start:
{
lean_object* v_keyArray_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v_cellCount_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v_target_4073_; lean_object* v___x_4074_; 
v_keyArray_4066_ = lean_ctor_get(v_m_4065_, 1);
v___x_4067_ = lean_array_get_size(v_keyArray_4066_);
v___x_4068_ = lean_unsigned_to_nat(2u);
v_cellCount_4069_ = lean_nat_mul(v___x_4067_, v___x_4068_);
v___x_4070_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_4069_);
v___x_4071_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_4069_);
v___x_4072_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_4069_);
v_target_4073_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_4073_, 0, v___x_4070_);
lean_ctor_set(v_target_4073_, 1, v___x_4071_);
lean_ctor_set(v_target_4073_, 2, v___x_4072_);
v___x_4074_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1_spec__2___redArg(v_target_4073_, v_m_4065_);
return v___x_4074_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1___redArg___boxed(lean_object* v_m_4075_){
_start:
{
lean_object* v_res_4076_; 
v_res_4076_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1___redArg(v_m_4075_);
lean_dec_ref(v_m_4075_);
return v_res_4076_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___redArg(lean_object* v_as_4077_, size_t v_sz_4078_, size_t v_i_4079_, lean_object* v_b_4080_){
_start:
{
uint8_t v___x_4082_; 
v___x_4082_ = lean_usize_dec_lt(v_i_4079_, v_sz_4078_);
if (v___x_4082_ == 0)
{
lean_object* v___x_4083_; 
v___x_4083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4083_, 0, v_b_4080_);
return v___x_4083_;
}
else
{
lean_object* v_fst_4084_; lean_object* v_snd_4085_; lean_object* v___x_4087_; uint8_t v_isShared_4088_; uint8_t v_isSharedCheck_4166_; 
v_fst_4084_ = lean_ctor_get(v_b_4080_, 0);
v_snd_4085_ = lean_ctor_get(v_b_4080_, 1);
v_isSharedCheck_4166_ = !lean_is_exclusive(v_b_4080_);
if (v_isSharedCheck_4166_ == 0)
{
v___x_4087_ = v_b_4080_;
v_isShared_4088_ = v_isSharedCheck_4166_;
goto v_resetjp_4086_;
}
else
{
lean_inc(v_snd_4085_);
lean_inc(v_fst_4084_);
lean_dec(v_b_4080_);
v___x_4087_ = lean_box(0);
v_isShared_4088_ = v_isSharedCheck_4166_;
goto v_resetjp_4086_;
}
v_resetjp_4086_:
{
lean_object* v___y_4090_; lean_object* v_a_4099_; lean_object* v_fvar_4100_; lean_object* v___x_4101_; lean_object* v___y_4103_; lean_object* v_i_4104_; lean_object* v___y_4110_; lean_object* v___y_4120_; lean_object* v_i_4121_; lean_object* v___x_4136_; 
v_a_4099_ = lean_array_uget_borrowed(v_as_4077_, v_i_4079_);
v_fvar_4100_ = lean_ctor_get(v_a_4099_, 0);
v___x_4101_ = l_Lean_Expr_fvarId_x21(v_fvar_4100_);
v___x_4136_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0___redArg(v_fst_4084_, v___x_4101_);
switch(lean_obj_tag(v___x_4136_))
{
case 0:
{
lean_object* v_index_4137_; lean_object* v_size_4138_; lean_object* v___x_4139_; 
v_index_4137_ = lean_ctor_get(v___x_4136_, 0);
lean_inc(v_index_4137_);
lean_dec_ref_known(v___x_4136_, 3);
v_size_4138_ = lean_ctor_get(v_fst_4084_, 0);
lean_inc(v_size_4138_);
lean_inc(v_snd_4085_);
v___x_4139_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_4084_, v_size_4138_, v_index_4137_, v___x_4101_, v_snd_4085_);
lean_dec(v_index_4137_);
v___y_4090_ = v___x_4139_;
goto v___jp_4089_;
}
case 1:
{
lean_object* v_index_4140_; lean_object* v_size_4141_; lean_object* v_keyArray_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; uint8_t v___x_4146_; 
v_index_4140_ = lean_ctor_get(v___x_4136_, 0);
lean_inc(v_index_4140_);
lean_dec_ref_known(v___x_4136_, 1);
v_size_4141_ = lean_ctor_get(v_fst_4084_, 0);
v_keyArray_4142_ = lean_ctor_get(v_fst_4084_, 1);
v___x_4143_ = lean_unsigned_to_nat(1u);
v___x_4144_ = lean_nat_add(v_size_4141_, v___x_4143_);
v___x_4145_ = lean_array_get_size(v_keyArray_4142_);
v___x_4146_ = lean_nat_dec_lt(v___x_4144_, v___x_4145_);
if (v___x_4146_ == 0)
{
lean_dec(v___x_4144_);
lean_dec(v_index_4140_);
goto v___jp_4126_;
}
else
{
lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; uint8_t v___x_4151_; 
v___x_4147_ = lean_unsigned_to_nat(4u);
v___x_4148_ = lean_nat_mul(v___x_4144_, v___x_4147_);
v___x_4149_ = lean_unsigned_to_nat(3u);
v___x_4150_ = lean_nat_mul(v___x_4145_, v___x_4149_);
v___x_4151_ = lean_nat_dec_le(v___x_4148_, v___x_4150_);
lean_dec(v___x_4150_);
lean_dec(v___x_4148_);
if (v___x_4151_ == 0)
{
lean_dec(v___x_4144_);
lean_dec(v_index_4140_);
goto v___jp_4126_;
}
else
{
lean_object* v___x_4152_; 
lean_inc(v_snd_4085_);
v___x_4152_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_4084_, v___x_4144_, v_index_4140_, v___x_4101_, v_snd_4085_);
lean_dec(v_index_4140_);
v___y_4090_ = v___x_4152_;
goto v___jp_4089_;
}
}
}
default: 
{
lean_object* v_size_4153_; lean_object* v_keyArray_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; uint8_t v___x_4158_; 
v_size_4153_ = lean_ctor_get(v_fst_4084_, 0);
v_keyArray_4154_ = lean_ctor_get(v_fst_4084_, 1);
v___x_4155_ = lean_unsigned_to_nat(1u);
v___x_4156_ = lean_nat_add(v_size_4153_, v___x_4155_);
v___x_4157_ = lean_array_get_size(v_keyArray_4154_);
v___x_4158_ = lean_nat_dec_lt(v___x_4156_, v___x_4157_);
if (v___x_4158_ == 0)
{
lean_object* v___x_4159_; 
lean_dec(v___x_4156_);
v___x_4159_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1___redArg(v_fst_4084_);
lean_dec(v_fst_4084_);
v___y_4110_ = v___x_4159_;
goto v___jp_4109_;
}
else
{
lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; uint8_t v___x_4164_; 
v___x_4160_ = lean_unsigned_to_nat(4u);
v___x_4161_ = lean_nat_mul(v___x_4156_, v___x_4160_);
lean_dec(v___x_4156_);
v___x_4162_ = lean_unsigned_to_nat(3u);
v___x_4163_ = lean_nat_mul(v___x_4157_, v___x_4162_);
v___x_4164_ = lean_nat_dec_le(v___x_4161_, v___x_4163_);
lean_dec(v___x_4163_);
lean_dec(v___x_4161_);
if (v___x_4164_ == 0)
{
lean_object* v___x_4165_; 
v___x_4165_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1___redArg(v_fst_4084_);
lean_dec(v_fst_4084_);
v___y_4110_ = v___x_4165_;
goto v___jp_4109_;
}
else
{
v___y_4110_ = v_fst_4084_;
goto v___jp_4109_;
}
}
}
}
v___jp_4089_:
{
lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4094_; 
v___x_4091_ = lean_unsigned_to_nat(1u);
v___x_4092_ = lean_nat_add(v_snd_4085_, v___x_4091_);
lean_dec(v_snd_4085_);
if (v_isShared_4088_ == 0)
{
lean_ctor_set(v___x_4087_, 1, v___x_4092_);
lean_ctor_set(v___x_4087_, 0, v___y_4090_);
v___x_4094_ = v___x_4087_;
goto v_reusejp_4093_;
}
else
{
lean_object* v_reuseFailAlloc_4098_; 
v_reuseFailAlloc_4098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4098_, 0, v___y_4090_);
lean_ctor_set(v_reuseFailAlloc_4098_, 1, v___x_4092_);
v___x_4094_ = v_reuseFailAlloc_4098_;
goto v_reusejp_4093_;
}
v_reusejp_4093_:
{
size_t v___x_4095_; size_t v___x_4096_; 
v___x_4095_ = ((size_t)1ULL);
v___x_4096_ = lean_usize_add(v_i_4079_, v___x_4095_);
v_i_4079_ = v___x_4096_;
v_b_4080_ = v___x_4094_;
goto _start;
}
}
v___jp_4102_:
{
lean_object* v_size_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; 
v_size_4105_ = lean_ctor_get(v___y_4103_, 0);
v___x_4106_ = lean_unsigned_to_nat(1u);
v___x_4107_ = lean_nat_add(v_size_4105_, v___x_4106_);
lean_inc(v_snd_4085_);
v___x_4108_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4103_, v___x_4107_, v_i_4104_, v___x_4101_, v_snd_4085_);
lean_dec(v_i_4104_);
v___y_4090_ = v___x_4108_;
goto v___jp_4089_;
}
v___jp_4109_:
{
lean_object* v___x_4111_; 
v___x_4111_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0___redArg(v___y_4110_, v___x_4101_);
switch(lean_obj_tag(v___x_4111_))
{
case 0:
{
lean_object* v_index_4112_; lean_object* v_size_4113_; lean_object* v___x_4114_; 
v_index_4112_ = lean_ctor_get(v___x_4111_, 0);
lean_inc(v_index_4112_);
lean_dec_ref_known(v___x_4111_, 3);
v_size_4113_ = lean_ctor_get(v___y_4110_, 0);
lean_inc(v_size_4113_);
lean_inc(v_snd_4085_);
v___x_4114_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4110_, v_size_4113_, v_index_4112_, v___x_4101_, v_snd_4085_);
lean_dec(v_index_4112_);
v___y_4090_ = v___x_4114_;
goto v___jp_4089_;
}
case 1:
{
lean_object* v_index_4115_; 
v_index_4115_ = lean_ctor_get(v___x_4111_, 0);
lean_inc(v_index_4115_);
lean_dec_ref_known(v___x_4111_, 1);
v___y_4103_ = v___y_4110_;
v_i_4104_ = v_index_4115_;
goto v___jp_4102_;
}
default: 
{
lean_object* v___x_4116_; lean_object* v___x_4117_; 
v___x_4116_ = lean_unsigned_to_nat(0u);
v___x_4117_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_4110_, v___x_4116_);
if (lean_obj_tag(v___x_4117_) == 0)
{
lean_object* v_index_4118_; 
v_index_4118_ = lean_ctor_get(v___x_4117_, 0);
lean_inc(v_index_4118_);
lean_dec_ref_known(v___x_4117_, 1);
v___y_4103_ = v___y_4110_;
v_i_4104_ = v_index_4118_;
goto v___jp_4102_;
}
else
{
lean_dec(v___x_4101_);
v___y_4090_ = v___y_4110_;
goto v___jp_4089_;
}
}
}
}
v___jp_4119_:
{
lean_object* v_size_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; 
v_size_4122_ = lean_ctor_get(v___y_4120_, 0);
v___x_4123_ = lean_unsigned_to_nat(1u);
v___x_4124_ = lean_nat_add(v_size_4122_, v___x_4123_);
lean_inc(v_snd_4085_);
v___x_4125_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4120_, v___x_4124_, v_i_4121_, v___x_4101_, v_snd_4085_);
lean_dec(v_i_4121_);
v___y_4090_ = v___x_4125_;
goto v___jp_4089_;
}
v___jp_4126_:
{
lean_object* v___x_4127_; lean_object* v___x_4128_; 
v___x_4127_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1___redArg(v_fst_4084_);
lean_dec(v_fst_4084_);
v___x_4128_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0___redArg(v___x_4127_, v___x_4101_);
switch(lean_obj_tag(v___x_4128_))
{
case 0:
{
lean_object* v_index_4129_; lean_object* v_size_4130_; lean_object* v___x_4131_; 
v_index_4129_ = lean_ctor_get(v___x_4128_, 0);
lean_inc(v_index_4129_);
lean_dec_ref_known(v___x_4128_, 3);
v_size_4130_ = lean_ctor_get(v___x_4127_, 0);
lean_inc(v_size_4130_);
lean_inc(v_snd_4085_);
v___x_4131_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_4127_, v_size_4130_, v_index_4129_, v___x_4101_, v_snd_4085_);
lean_dec(v_index_4129_);
v___y_4090_ = v___x_4131_;
goto v___jp_4089_;
}
case 1:
{
lean_object* v_index_4132_; 
v_index_4132_ = lean_ctor_get(v___x_4128_, 0);
lean_inc(v_index_4132_);
lean_dec_ref_known(v___x_4128_, 1);
v___y_4120_ = v___x_4127_;
v_i_4121_ = v_index_4132_;
goto v___jp_4119_;
}
default: 
{
lean_object* v___x_4133_; lean_object* v___x_4134_; 
v___x_4133_ = lean_unsigned_to_nat(0u);
v___x_4134_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_4127_, v___x_4133_);
if (lean_obj_tag(v___x_4134_) == 0)
{
lean_object* v_index_4135_; 
v_index_4135_ = lean_ctor_get(v___x_4134_, 0);
lean_inc(v_index_4135_);
lean_dec_ref_known(v___x_4134_, 1);
v___y_4120_ = v___x_4127_;
v_i_4121_ = v_index_4135_;
goto v___jp_4119_;
}
else
{
lean_dec(v___x_4101_);
v___y_4090_ = v___x_4127_;
goto v___jp_4089_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___redArg___boxed(lean_object* v_as_4167_, lean_object* v_sz_4168_, lean_object* v_i_4169_, lean_object* v_b_4170_, lean_object* v___y_4171_){
_start:
{
size_t v_sz_boxed_4172_; size_t v_i_boxed_4173_; lean_object* v_res_4174_; 
v_sz_boxed_4172_ = lean_unbox_usize(v_sz_4168_);
lean_dec(v_sz_4168_);
v_i_boxed_4173_ = lean_unbox_usize(v_i_4169_);
lean_dec(v_i_4169_);
v_res_4174_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___redArg(v_as_4167_, v_sz_boxed_4172_, v_i_boxed_4173_, v_b_4170_);
lean_dec_ref(v_as_4167_);
return v_res_4174_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__0(void){
_start:
{
lean_object* v_cellCount_4175_; lean_object* v___x_4176_; 
v_cellCount_4175_ = lean_unsigned_to_nat(16u);
v___x_4176_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_4175_);
return v___x_4176_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__1(void){
_start:
{
lean_object* v_cellCount_4177_; lean_object* v___x_4178_; 
v_cellCount_4177_ = lean_unsigned_to_nat(16u);
v___x_4178_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_4177_);
return v___x_4178_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__2(void){
_start:
{
lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; 
v___x_4179_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__1, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__1_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__1);
v___x_4180_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__0, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__0_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__0);
v___x_4181_ = lean_unsigned_to_nat(0u);
v___x_4182_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4182_, 0, v___x_4181_);
lean_ctor_set(v___x_4182_, 1, v___x_4180_);
lean_ctor_set(v___x_4182_, 2, v___x_4179_);
return v___x_4182_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__3(void){
_start:
{
lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; 
v___x_4183_ = lean_unsigned_to_nat(0u);
v___x_4184_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__2);
v___x_4185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4185_, 0, v___x_4184_);
lean_ctor_set(v___x_4185_, 1, v___x_4183_);
return v___x_4185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets(lean_object* v_e_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_){
_start:
{
lean_object* v___x_4195_; lean_object* v_decls_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; uint8_t v___x_4199_; 
v___x_4195_ = lean_st_ref_get(v_a_4187_);
v_decls_4196_ = lean_ctor_get(v___x_4195_, 3);
lean_inc_ref(v_decls_4196_);
lean_dec(v___x_4195_);
v___x_4197_ = lean_array_get_size(v_decls_4196_);
v___x_4198_ = lean_unsigned_to_nat(0u);
v___x_4199_ = lean_nat_dec_eq(v___x_4197_, v___x_4198_);
if (v___x_4199_ == 0)
{
lean_object* v_cellCount_4200_; lean_object* v___x_4201_; size_t v_sz_4202_; size_t v___x_4203_; lean_object* v___x_4204_; 
v_cellCount_4200_ = lean_unsigned_to_nat(16u);
v___x_4201_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__3, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__3_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__3);
v_sz_4202_ = lean_array_size(v_decls_4196_);
v___x_4203_ = ((size_t)0ULL);
v___x_4204_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___redArg(v_decls_4196_, v_sz_4202_, v___x_4203_, v___x_4201_);
if (lean_obj_tag(v___x_4204_) == 0)
{
lean_object* v_a_4205_; lean_object* v_fst_4206_; lean_object* v___x_4208_; uint8_t v_isShared_4209_; uint8_t v_isSharedCheck_4257_; 
v_a_4205_ = lean_ctor_get(v___x_4204_, 0);
lean_inc(v_a_4205_);
lean_dec_ref_known(v___x_4204_, 1);
v_fst_4206_ = lean_ctor_get(v_a_4205_, 0);
v_isSharedCheck_4257_ = !lean_is_exclusive(v_a_4205_);
if (v_isSharedCheck_4257_ == 0)
{
lean_object* v_unused_4258_; 
v_unused_4258_ = lean_ctor_get(v_a_4205_, 1);
lean_dec(v_unused_4258_);
v___x_4208_ = v_a_4205_;
v_isShared_4209_ = v_isSharedCheck_4257_;
goto v_resetjp_4207_;
}
else
{
lean_inc(v_fst_4206_);
lean_dec(v_a_4205_);
v___x_4208_ = lean_box(0);
v_isShared_4209_ = v_isSharedCheck_4257_;
goto v_resetjp_4207_;
}
v_resetjp_4207_:
{
lean_object* v_a_4211_; lean_object* v___x_4235_; lean_object* v___x_4236_; uint8_t v_debug_4237_; lean_object* v_env_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___f_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; 
v___x_4235_ = lean_st_ref_get(v_a_4189_);
v___x_4236_ = lean_st_ref_get(v_a_4193_);
v_debug_4237_ = lean_ctor_get_uint8(v___x_4235_, sizeof(void*)*11);
lean_dec(v___x_4235_);
v_env_4238_ = lean_ctor_get(v___x_4236_, 0);
lean_inc_ref(v_env_4238_);
lean_dec(v___x_4236_);
v___x_4239_ = lean_box(v_debug_4237_);
v___x_4240_ = lean_box(v___x_4199_);
lean_inc(v_fst_4206_);
v___f_4241_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___lam__0___boxed), 9, 7);
lean_closure_set(v___f_4241_, 0, v_e_4186_);
lean_closure_set(v___f_4241_, 1, v_cellCount_4200_);
lean_closure_set(v___f_4241_, 2, v___x_4198_);
lean_closure_set(v___f_4241_, 3, v_fst_4206_);
lean_closure_set(v___f_4241_, 4, v___x_4197_);
lean_closure_set(v___f_4241_, 5, v___x_4239_);
lean_closure_set(v___f_4241_, 6, v___x_4240_);
v___x_4242_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_4242_, 0, v_env_4238_);
lean_ctor_set_uint8(v___x_4242_, sizeof(void*)*1, v___x_4199_);
lean_ctor_set_uint8(v___x_4242_, sizeof(void*)*1 + 1, v___x_4199_);
v___x_4243_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_4241_, v___x_4242_, v_a_4189_);
if (lean_obj_tag(v___x_4243_) == 0)
{
lean_object* v_a_4244_; 
v_a_4244_ = lean_ctor_get(v___x_4243_, 0);
lean_inc(v_a_4244_);
lean_dec_ref_known(v___x_4243_, 1);
if (lean_obj_tag(v_a_4244_) == 0)
{
lean_object* v___x_4245_; lean_object* v___x_4246_; 
lean_dec_ref_known(v_a_4244_, 1);
v___x_4245_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2);
v___x_4246_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1(v___x_4245_, v_a_4188_, v_a_4189_, v_a_4190_, v_a_4191_, v_a_4192_, v_a_4193_);
if (lean_obj_tag(v___x_4246_) == 0)
{
lean_object* v_a_4247_; 
v_a_4247_ = lean_ctor_get(v___x_4246_, 0);
lean_inc(v_a_4247_);
lean_dec_ref_known(v___x_4246_, 1);
v_a_4211_ = v_a_4247_;
goto v___jp_4210_;
}
else
{
lean_del_object(v___x_4208_);
lean_dec(v_fst_4206_);
lean_dec_ref(v_decls_4196_);
return v___x_4246_;
}
}
else
{
lean_object* v_a_4248_; 
v_a_4248_ = lean_ctor_get(v_a_4244_, 0);
lean_inc(v_a_4248_);
lean_dec_ref_known(v_a_4244_, 1);
v_a_4211_ = v_a_4248_;
goto v___jp_4210_;
}
}
else
{
lean_object* v_a_4249_; lean_object* v___x_4251_; uint8_t v_isShared_4252_; uint8_t v_isSharedCheck_4256_; 
lean_del_object(v___x_4208_);
lean_dec(v_fst_4206_);
lean_dec_ref(v_decls_4196_);
v_a_4249_ = lean_ctor_get(v___x_4243_, 0);
v_isSharedCheck_4256_ = !lean_is_exclusive(v___x_4243_);
if (v_isSharedCheck_4256_ == 0)
{
v___x_4251_ = v___x_4243_;
v_isShared_4252_ = v_isSharedCheck_4256_;
goto v_resetjp_4250_;
}
else
{
lean_inc(v_a_4249_);
lean_dec(v___x_4243_);
v___x_4251_ = lean_box(0);
v_isShared_4252_ = v_isSharedCheck_4256_;
goto v_resetjp_4250_;
}
v_resetjp_4250_:
{
lean_object* v___x_4254_; 
if (v_isShared_4252_ == 0)
{
v___x_4254_ = v___x_4251_;
goto v_reusejp_4253_;
}
else
{
lean_object* v_reuseFailAlloc_4255_; 
v_reuseFailAlloc_4255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4255_, 0, v_a_4249_);
v___x_4254_ = v_reuseFailAlloc_4255_;
goto v_reusejp_4253_;
}
v_reusejp_4253_:
{
return v___x_4254_;
}
}
}
v___jp_4210_:
{
lean_object* v___x_4212_; lean_object* v___x_4214_; 
v___x_4212_ = l_Array_reverse___redArg(v_decls_4196_);
if (v_isShared_4209_ == 0)
{
lean_ctor_set(v___x_4208_, 1, v___x_4197_);
lean_ctor_set(v___x_4208_, 0, v_a_4211_);
v___x_4214_ = v___x_4208_;
goto v_reusejp_4213_;
}
else
{
lean_object* v_reuseFailAlloc_4234_; 
v_reuseFailAlloc_4234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4234_, 0, v_a_4211_);
lean_ctor_set(v_reuseFailAlloc_4234_, 1, v___x_4197_);
v___x_4214_ = v_reuseFailAlloc_4234_;
goto v_reusejp_4213_;
}
v_reusejp_4213_:
{
size_t v_sz_4215_; lean_object* v___x_4216_; 
v_sz_4215_ = lean_array_size(v___x_4212_);
v___x_4216_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__8(v_fst_4206_, v___x_4197_, v___x_4212_, v_sz_4215_, v___x_4203_, v___x_4214_, v_a_4187_, v_a_4188_, v_a_4189_, v_a_4190_, v_a_4191_, v_a_4192_, v_a_4193_);
lean_dec_ref(v___x_4212_);
if (lean_obj_tag(v___x_4216_) == 0)
{
lean_object* v_a_4217_; lean_object* v___x_4219_; uint8_t v_isShared_4220_; uint8_t v_isSharedCheck_4225_; 
v_a_4217_ = lean_ctor_get(v___x_4216_, 0);
v_isSharedCheck_4225_ = !lean_is_exclusive(v___x_4216_);
if (v_isSharedCheck_4225_ == 0)
{
v___x_4219_ = v___x_4216_;
v_isShared_4220_ = v_isSharedCheck_4225_;
goto v_resetjp_4218_;
}
else
{
lean_inc(v_a_4217_);
lean_dec(v___x_4216_);
v___x_4219_ = lean_box(0);
v_isShared_4220_ = v_isSharedCheck_4225_;
goto v_resetjp_4218_;
}
v_resetjp_4218_:
{
lean_object* v_fst_4221_; lean_object* v___x_4223_; 
v_fst_4221_ = lean_ctor_get(v_a_4217_, 0);
lean_inc(v_fst_4221_);
lean_dec(v_a_4217_);
if (v_isShared_4220_ == 0)
{
lean_ctor_set(v___x_4219_, 0, v_fst_4221_);
v___x_4223_ = v___x_4219_;
goto v_reusejp_4222_;
}
else
{
lean_object* v_reuseFailAlloc_4224_; 
v_reuseFailAlloc_4224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4224_, 0, v_fst_4221_);
v___x_4223_ = v_reuseFailAlloc_4224_;
goto v_reusejp_4222_;
}
v_reusejp_4222_:
{
return v___x_4223_;
}
}
}
else
{
lean_object* v_a_4226_; lean_object* v___x_4228_; uint8_t v_isShared_4229_; uint8_t v_isSharedCheck_4233_; 
v_a_4226_ = lean_ctor_get(v___x_4216_, 0);
v_isSharedCheck_4233_ = !lean_is_exclusive(v___x_4216_);
if (v_isSharedCheck_4233_ == 0)
{
v___x_4228_ = v___x_4216_;
v_isShared_4229_ = v_isSharedCheck_4233_;
goto v_resetjp_4227_;
}
else
{
lean_inc(v_a_4226_);
lean_dec(v___x_4216_);
v___x_4228_ = lean_box(0);
v_isShared_4229_ = v_isSharedCheck_4233_;
goto v_resetjp_4227_;
}
v_resetjp_4227_:
{
lean_object* v___x_4231_; 
if (v_isShared_4229_ == 0)
{
v___x_4231_ = v___x_4228_;
goto v_reusejp_4230_;
}
else
{
lean_object* v_reuseFailAlloc_4232_; 
v_reuseFailAlloc_4232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4232_, 0, v_a_4226_);
v___x_4231_ = v_reuseFailAlloc_4232_;
goto v_reusejp_4230_;
}
v_reusejp_4230_:
{
return v___x_4231_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4259_; lean_object* v___x_4261_; uint8_t v_isShared_4262_; uint8_t v_isSharedCheck_4266_; 
lean_dec_ref(v_decls_4196_);
lean_dec_ref(v_e_4186_);
v_a_4259_ = lean_ctor_get(v___x_4204_, 0);
v_isSharedCheck_4266_ = !lean_is_exclusive(v___x_4204_);
if (v_isSharedCheck_4266_ == 0)
{
v___x_4261_ = v___x_4204_;
v_isShared_4262_ = v_isSharedCheck_4266_;
goto v_resetjp_4260_;
}
else
{
lean_inc(v_a_4259_);
lean_dec(v___x_4204_);
v___x_4261_ = lean_box(0);
v_isShared_4262_ = v_isSharedCheck_4266_;
goto v_resetjp_4260_;
}
v_resetjp_4260_:
{
lean_object* v___x_4264_; 
if (v_isShared_4262_ == 0)
{
v___x_4264_ = v___x_4261_;
goto v_reusejp_4263_;
}
else
{
lean_object* v_reuseFailAlloc_4265_; 
v_reuseFailAlloc_4265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4265_, 0, v_a_4259_);
v___x_4264_ = v_reuseFailAlloc_4265_;
goto v_reusejp_4263_;
}
v_reusejp_4263_:
{
return v___x_4264_;
}
}
}
}
else
{
lean_object* v___x_4267_; 
lean_dec_ref(v_decls_4196_);
v___x_4267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4267_, 0, v_e_4186_);
return v___x_4267_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___boxed(lean_object* v_e_4268_, lean_object* v_a_4269_, lean_object* v_a_4270_, lean_object* v_a_4271_, lean_object* v_a_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_, lean_object* v_a_4275_, lean_object* v_a_4276_){
_start:
{
lean_object* v_res_4277_; 
v_res_4277_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets(v_e_4268_, v_a_4269_, v_a_4270_, v_a_4271_, v_a_4272_, v_a_4273_, v_a_4274_, v_a_4275_);
lean_dec(v_a_4275_);
lean_dec_ref(v_a_4274_);
lean_dec(v_a_4273_);
lean_dec_ref(v_a_4272_);
lean_dec(v_a_4271_);
lean_dec_ref(v_a_4270_);
lean_dec(v_a_4269_);
return v_res_4277_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0(lean_object* v_00_u03b2_4278_, lean_object* v_m_4279_, lean_object* v_query_4280_){
_start:
{
lean_object* v___x_4281_; 
v___x_4281_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0___redArg(v_m_4279_, v_query_4280_);
return v___x_4281_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0___boxed(lean_object* v_00_u03b2_4282_, lean_object* v_m_4283_, lean_object* v_query_4284_){
_start:
{
lean_object* v_res_4285_; 
v_res_4285_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0(v_00_u03b2_4282_, v_m_4283_, v_query_4284_);
lean_dec(v_query_4284_);
lean_dec_ref(v_m_4283_);
return v_res_4285_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1(lean_object* v_00_u03b2_4286_, lean_object* v_m_4287_){
_start:
{
lean_object* v___x_4288_; 
v___x_4288_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1___redArg(v_m_4287_);
return v___x_4288_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1___boxed(lean_object* v_00_u03b2_4289_, lean_object* v_m_4290_){
_start:
{
lean_object* v_res_4291_; 
v_res_4291_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1(v_00_u03b2_4289_, v_m_4290_);
lean_dec_ref(v_m_4290_);
return v_res_4291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2(lean_object* v_as_4292_, size_t v_sz_4293_, size_t v_i_4294_, lean_object* v_b_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_){
_start:
{
lean_object* v___x_4304_; 
v___x_4304_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___redArg(v_as_4292_, v_sz_4293_, v_i_4294_, v_b_4295_);
return v___x_4304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___boxed(lean_object* v_as_4305_, lean_object* v_sz_4306_, lean_object* v_i_4307_, lean_object* v_b_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_){
_start:
{
size_t v_sz_boxed_4317_; size_t v_i_boxed_4318_; lean_object* v_res_4319_; 
v_sz_boxed_4317_ = lean_unbox_usize(v_sz_4306_);
lean_dec(v_sz_4306_);
v_i_boxed_4318_ = lean_unbox_usize(v_i_4307_);
lean_dec(v_i_4307_);
v_res_4319_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2(v_as_4305_, v_sz_boxed_4317_, v_i_boxed_4318_, v_b_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_, v___y_4313_, v___y_4314_, v___y_4315_);
lean_dec(v___y_4315_);
lean_dec_ref(v___y_4314_);
lean_dec(v___y_4313_);
lean_dec_ref(v___y_4312_);
lean_dec(v___y_4311_);
lean_dec_ref(v___y_4310_);
lean_dec(v___y_4309_);
lean_dec_ref(v_as_4305_);
return v_res_4319_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3(lean_object* v_00_u03b2_4320_, lean_object* v_m_4321_, lean_object* v_a_4322_){
_start:
{
lean_object* v___x_4323_; 
v___x_4323_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3___redArg(v_m_4321_, v_a_4322_);
return v___x_4323_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3___boxed(lean_object* v_00_u03b2_4324_, lean_object* v_m_4325_, lean_object* v_a_4326_){
_start:
{
lean_object* v_res_4327_; 
v_res_4327_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3(v_00_u03b2_4324_, v_m_4325_, v_a_4326_);
lean_dec(v_a_4326_);
lean_dec_ref(v_m_4325_);
return v_res_4327_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0(lean_object* v_00_u03b2_4328_, lean_object* v_m_4329_, lean_object* v_query_4330_, lean_object* v_x_4331_, lean_object* v_x_4332_, lean_object* v_x_4333_, lean_object* v_x_4334_){
_start:
{
lean_object* v___x_4335_; 
v___x_4335_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0___redArg(v_m_4329_, v_query_4330_, v_x_4331_, v_x_4332_, v_x_4333_);
return v___x_4335_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4336_, lean_object* v_m_4337_, lean_object* v_query_4338_, lean_object* v_x_4339_, lean_object* v_x_4340_, lean_object* v_x_4341_, lean_object* v_x_4342_){
_start:
{
lean_object* v_res_4343_; 
v_res_4343_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0(v_00_u03b2_4336_, v_m_4337_, v_query_4338_, v_x_4339_, v_x_4340_, v_x_4341_, v_x_4342_);
lean_dec(v_query_4338_);
lean_dec_ref(v_m_4337_);
return v_res_4343_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1_spec__2(lean_object* v_00_u03b2_4344_, lean_object* v_init_4345_, lean_object* v_b_4346_){
_start:
{
lean_object* v___x_4347_; 
v___x_4347_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1_spec__2___redArg(v_init_4345_, v_b_4346_);
return v___x_4347_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4348_, lean_object* v_init_4349_, lean_object* v_b_4350_){
_start:
{
lean_object* v_res_4351_; 
v_res_4351_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1_spec__2(v_00_u03b2_4348_, v_init_4349_, v_b_4350_);
lean_dec_ref(v_b_4350_);
return v_res_4351_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3_spec__5(lean_object* v_00_u03b2_4352_, lean_object* v_m_4353_, lean_object* v_query_4354_){
_start:
{
lean_object* v___x_4355_; 
v___x_4355_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3_spec__5___redArg(v_m_4353_, v_query_4354_);
return v___x_4355_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3_spec__5___boxed(lean_object* v_00_u03b2_4356_, lean_object* v_m_4357_, lean_object* v_query_4358_){
_start:
{
lean_object* v_res_4359_; 
v_res_4359_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3_spec__5(v_00_u03b2_4356_, v_m_4357_, v_query_4358_);
lean_dec(v_query_4358_);
lean_dec_ref(v_m_4357_);
return v_res_4359_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_4360_, lean_object* v_b_4361_, lean_object* v_acc_4362_, lean_object* v_i_4363_){
_start:
{
lean_object* v___x_4364_; 
v___x_4364_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1_spec__2_spec__6___redArg(v_b_4361_, v_acc_4362_, v_i_4363_);
return v___x_4364_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_4365_, lean_object* v_b_4366_, lean_object* v_acc_4367_, lean_object* v_i_4368_){
_start:
{
lean_object* v_res_4369_; 
v_res_4369_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1_spec__2_spec__6(v_00_u03b2_4365_, v_b_4366_, v_acc_4367_, v_i_4368_);
lean_dec_ref(v_b_4366_);
return v_res_4369_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0___redArg(lean_object* v_msg_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_){
_start:
{
lean_object* v_ref_4376_; lean_object* v___x_4377_; lean_object* v_a_4378_; lean_object* v___x_4380_; uint8_t v_isShared_4381_; uint8_t v_isSharedCheck_4386_; 
v_ref_4376_ = lean_ctor_get(v___y_4373_, 5);
v___x_4377_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5_spec__5(v_msg_4370_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_);
v_a_4378_ = lean_ctor_get(v___x_4377_, 0);
v_isSharedCheck_4386_ = !lean_is_exclusive(v___x_4377_);
if (v_isSharedCheck_4386_ == 0)
{
v___x_4380_ = v___x_4377_;
v_isShared_4381_ = v_isSharedCheck_4386_;
goto v_resetjp_4379_;
}
else
{
lean_inc(v_a_4378_);
lean_dec(v___x_4377_);
v___x_4380_ = lean_box(0);
v_isShared_4381_ = v_isSharedCheck_4386_;
goto v_resetjp_4379_;
}
v_resetjp_4379_:
{
lean_object* v___x_4382_; lean_object* v___x_4384_; 
lean_inc(v_ref_4376_);
v___x_4382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4382_, 0, v_ref_4376_);
lean_ctor_set(v___x_4382_, 1, v_a_4378_);
if (v_isShared_4381_ == 0)
{
lean_ctor_set_tag(v___x_4380_, 1);
lean_ctor_set(v___x_4380_, 0, v___x_4382_);
v___x_4384_ = v___x_4380_;
goto v_reusejp_4383_;
}
else
{
lean_object* v_reuseFailAlloc_4385_; 
v_reuseFailAlloc_4385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4385_, 0, v___x_4382_);
v___x_4384_ = v_reuseFailAlloc_4385_;
goto v_reusejp_4383_;
}
v_reusejp_4383_:
{
return v___x_4384_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0___redArg___boxed(lean_object* v_msg_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_){
_start:
{
lean_object* v_res_4393_; 
v_res_4393_ = l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0___redArg(v_msg_4387_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_);
lean_dec(v___y_4391_);
lean_dec_ref(v___y_4390_);
lean_dec(v___y_4389_);
lean_dec_ref(v___y_4388_);
return v_res_4393_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_liftLets___closed__0(void){
_start:
{
lean_object* v_cellCount_4394_; lean_object* v___x_4395_; 
v_cellCount_4394_ = lean_unsigned_to_nat(16u);
v___x_4395_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_4394_);
return v___x_4395_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_liftLets___closed__1(void){
_start:
{
lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; 
v___x_4396_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__1, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__1);
v___x_4397_ = lean_obj_once(&l_Lean_Meta_Sym_liftLets___closed__0, &l_Lean_Meta_Sym_liftLets___closed__0_once, _init_l_Lean_Meta_Sym_liftLets___closed__0);
v___x_4398_ = lean_unsigned_to_nat(0u);
v___x_4399_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4399_, 0, v___x_4398_);
lean_ctor_set(v___x_4399_, 1, v___x_4397_);
lean_ctor_set(v___x_4399_, 2, v___x_4396_);
return v___x_4399_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_liftLets___closed__3(void){
_start:
{
lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; 
v___x_4402_ = ((lean_object*)(l_Lean_Meta_Sym_liftLets___closed__2));
v___x_4403_ = lean_obj_once(&l_Lean_Meta_Sym_liftLets___closed__1, &l_Lean_Meta_Sym_liftLets___closed__1_once, _init_l_Lean_Meta_Sym_liftLets___closed__1);
v___x_4404_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4404_, 0, v___x_4403_);
lean_ctor_set(v___x_4404_, 1, v___x_4403_);
lean_ctor_set(v___x_4404_, 2, v___x_4403_);
lean_ctor_set(v___x_4404_, 3, v___x_4402_);
lean_ctor_set(v___x_4404_, 4, v___x_4403_);
return v___x_4404_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_liftLets___closed__5(void){
_start:
{
lean_object* v___x_4406_; lean_object* v___x_4407_; 
v___x_4406_ = ((lean_object*)(l_Lean_Meta_Sym_liftLets___closed__4));
v___x_4407_ = l_Lean_stringToMessageData(v___x_4406_);
return v___x_4407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLets(lean_object* v_e_4408_, lean_object* v_a_4409_, lean_object* v_a_4410_, lean_object* v_a_4411_, lean_object* v_a_4412_, lean_object* v_a_4413_, lean_object* v_a_4414_){
_start:
{
lean_object* v___y_4417_; lean_object* v___y_4418_; lean_object* v___y_4429_; lean_object* v___y_4430_; lean_object* v___y_4431_; lean_object* v___y_4432_; lean_object* v___y_4433_; lean_object* v___y_4434_; uint8_t v___x_4441_; 
v___x_4441_ = l_Lean_Expr_hasLooseBVars(v_e_4408_);
if (v___x_4441_ == 0)
{
v___y_4429_ = v_a_4409_;
v___y_4430_ = v_a_4410_;
v___y_4431_ = v_a_4411_;
v___y_4432_ = v_a_4412_;
v___y_4433_ = v_a_4413_;
v___y_4434_ = v_a_4414_;
goto v___jp_4428_;
}
else
{
lean_object* v___x_4442_; lean_object* v___x_4443_; lean_object* v_a_4444_; lean_object* v___x_4446_; uint8_t v_isShared_4447_; uint8_t v_isSharedCheck_4451_; 
lean_dec_ref(v_e_4408_);
v___x_4442_ = lean_obj_once(&l_Lean_Meta_Sym_liftLets___closed__5, &l_Lean_Meta_Sym_liftLets___closed__5_once, _init_l_Lean_Meta_Sym_liftLets___closed__5);
v___x_4443_ = l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0___redArg(v___x_4442_, v_a_4411_, v_a_4412_, v_a_4413_, v_a_4414_);
v_a_4444_ = lean_ctor_get(v___x_4443_, 0);
v_isSharedCheck_4451_ = !lean_is_exclusive(v___x_4443_);
if (v_isSharedCheck_4451_ == 0)
{
v___x_4446_ = v___x_4443_;
v_isShared_4447_ = v_isSharedCheck_4451_;
goto v_resetjp_4445_;
}
else
{
lean_inc(v_a_4444_);
lean_dec(v___x_4443_);
v___x_4446_ = lean_box(0);
v_isShared_4447_ = v_isSharedCheck_4451_;
goto v_resetjp_4445_;
}
v_resetjp_4445_:
{
lean_object* v___x_4449_; 
if (v_isShared_4447_ == 0)
{
v___x_4449_ = v___x_4446_;
goto v_reusejp_4448_;
}
else
{
lean_object* v_reuseFailAlloc_4450_; 
v_reuseFailAlloc_4450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4450_, 0, v_a_4444_);
v___x_4449_ = v_reuseFailAlloc_4450_;
goto v_reusejp_4448_;
}
v_reusejp_4448_:
{
return v___x_4449_;
}
}
}
v___jp_4416_:
{
if (lean_obj_tag(v___y_4418_) == 0)
{
lean_object* v_a_4419_; lean_object* v___x_4421_; uint8_t v_isShared_4422_; uint8_t v_isSharedCheck_4427_; 
v_a_4419_ = lean_ctor_get(v___y_4418_, 0);
v_isSharedCheck_4427_ = !lean_is_exclusive(v___y_4418_);
if (v_isSharedCheck_4427_ == 0)
{
v___x_4421_ = v___y_4418_;
v_isShared_4422_ = v_isSharedCheck_4427_;
goto v_resetjp_4420_;
}
else
{
lean_inc(v_a_4419_);
lean_dec(v___y_4418_);
v___x_4421_ = lean_box(0);
v_isShared_4422_ = v_isSharedCheck_4427_;
goto v_resetjp_4420_;
}
v_resetjp_4420_:
{
lean_object* v___x_4423_; lean_object* v___x_4425_; 
v___x_4423_ = lean_st_ref_get(v___y_4417_);
lean_dec(v___y_4417_);
lean_dec(v___x_4423_);
if (v_isShared_4422_ == 0)
{
v___x_4425_ = v___x_4421_;
goto v_reusejp_4424_;
}
else
{
lean_object* v_reuseFailAlloc_4426_; 
v_reuseFailAlloc_4426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4426_, 0, v_a_4419_);
v___x_4425_ = v_reuseFailAlloc_4426_;
goto v_reusejp_4424_;
}
v_reusejp_4424_:
{
return v___x_4425_;
}
}
}
else
{
lean_dec(v___y_4417_);
return v___y_4418_;
}
}
v___jp_4428_:
{
lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; 
v___x_4435_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__3, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__3_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__3);
v___x_4436_ = lean_obj_once(&l_Lean_Meta_Sym_liftLets___closed__3, &l_Lean_Meta_Sym_liftLets___closed__3_once, _init_l_Lean_Meta_Sym_liftLets___closed__3);
v___x_4437_ = lean_st_mk_ref(v___x_4436_);
v___x_4438_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v___x_4435_, v_e_4408_, v___x_4437_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_);
if (lean_obj_tag(v___x_4438_) == 0)
{
lean_object* v_a_4439_; lean_object* v___x_4440_; 
v_a_4439_ = lean_ctor_get(v___x_4438_, 0);
lean_inc(v_a_4439_);
lean_dec_ref_known(v___x_4438_, 1);
v___x_4440_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets(v_a_4439_, v___x_4437_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_);
v___y_4417_ = v___x_4437_;
v___y_4418_ = v___x_4440_;
goto v___jp_4416_;
}
else
{
v___y_4417_ = v___x_4437_;
v___y_4418_ = v___x_4438_;
goto v___jp_4416_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLets___boxed(lean_object* v_e_4452_, lean_object* v_a_4453_, lean_object* v_a_4454_, lean_object* v_a_4455_, lean_object* v_a_4456_, lean_object* v_a_4457_, lean_object* v_a_4458_, lean_object* v_a_4459_){
_start:
{
lean_object* v_res_4460_; 
v_res_4460_ = l_Lean_Meta_Sym_liftLets(v_e_4452_, v_a_4453_, v_a_4454_, v_a_4455_, v_a_4456_, v_a_4457_, v_a_4458_);
lean_dec(v_a_4458_);
lean_dec_ref(v_a_4457_);
lean_dec(v_a_4456_);
lean_dec_ref(v_a_4455_);
lean_dec(v_a_4454_);
lean_dec_ref(v_a_4453_);
return v_res_4460_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0(lean_object* v_00_u03b1_4461_, lean_object* v_msg_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_){
_start:
{
lean_object* v___x_4470_; 
v___x_4470_ = l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0___redArg(v_msg_4462_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_);
return v___x_4470_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0___boxed(lean_object* v_00_u03b1_4471_, lean_object* v_msg_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_){
_start:
{
lean_object* v_res_4480_; 
v_res_4480_ = l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0(v_00_u03b1_4471_, v_msg_4472_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_);
lean_dec(v___y_4478_);
lean_dec_ref(v___y_4477_);
lean_dec(v___y_4476_);
lean_dec_ref(v___y_4475_);
lean_dec(v___y_4474_);
lean_dec_ref(v___y_4473_);
return v_res_4480_;
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
