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
uint8_t lean_usize_dec_lt(size_t, size_t);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed(lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3___closed__1_value;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_68_, lean_object* v_x_69_){
_start:
{
if (lean_obj_tag(v_x_69_) == 0)
{
return v_x_68_;
}
else
{
lean_object* v_key_70_; lean_object* v_value_71_; lean_object* v_tail_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_98_; 
v_key_70_ = lean_ctor_get(v_x_69_, 0);
v_value_71_ = lean_ctor_get(v_x_69_, 1);
v_tail_72_ = lean_ctor_get(v_x_69_, 2);
v_isSharedCheck_98_ = !lean_is_exclusive(v_x_69_);
if (v_isSharedCheck_98_ == 0)
{
v___x_74_ = v_x_69_;
v_isShared_75_ = v_isSharedCheck_98_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_tail_72_);
lean_inc(v_value_71_);
lean_inc(v_key_70_);
lean_dec(v_x_69_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_98_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
lean_object* v___x_76_; size_t v___x_77_; size_t v___x_78_; size_t v___x_79_; uint64_t v___x_80_; uint64_t v___x_81_; uint64_t v___x_82_; uint64_t v_fold_83_; uint64_t v___x_84_; uint64_t v___x_85_; uint64_t v___x_86_; size_t v___x_87_; size_t v___x_88_; size_t v___x_89_; size_t v___x_90_; size_t v___x_91_; lean_object* v___x_92_; lean_object* v___x_94_; 
v___x_76_ = lean_array_get_size(v_x_68_);
v___x_77_ = lean_ptr_addr(v_key_70_);
v___x_78_ = ((size_t)3ULL);
v___x_79_ = lean_usize_shift_right(v___x_77_, v___x_78_);
v___x_80_ = lean_usize_to_uint64(v___x_79_);
v___x_81_ = 32ULL;
v___x_82_ = lean_uint64_shift_right(v___x_80_, v___x_81_);
v_fold_83_ = lean_uint64_xor(v___x_80_, v___x_82_);
v___x_84_ = 16ULL;
v___x_85_ = lean_uint64_shift_right(v_fold_83_, v___x_84_);
v___x_86_ = lean_uint64_xor(v_fold_83_, v___x_85_);
v___x_87_ = lean_uint64_to_usize(v___x_86_);
v___x_88_ = lean_usize_of_nat(v___x_76_);
v___x_89_ = ((size_t)1ULL);
v___x_90_ = lean_usize_sub(v___x_88_, v___x_89_);
v___x_91_ = lean_usize_land(v___x_87_, v___x_90_);
v___x_92_ = lean_array_uget_borrowed(v_x_68_, v___x_91_);
lean_inc(v___x_92_);
if (v_isShared_75_ == 0)
{
lean_ctor_set(v___x_74_, 2, v___x_92_);
v___x_94_ = v___x_74_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v_key_70_);
lean_ctor_set(v_reuseFailAlloc_97_, 1, v_value_71_);
lean_ctor_set(v_reuseFailAlloc_97_, 2, v___x_92_);
v___x_94_ = v_reuseFailAlloc_97_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
lean_object* v___x_95_; 
v___x_95_ = lean_array_uset(v_x_68_, v___x_91_, v___x_94_);
v_x_68_ = v___x_95_;
v_x_69_ = v_tail_72_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__3_spec__4___redArg(lean_object* v_i_99_, lean_object* v_source_100_, lean_object* v_target_101_){
_start:
{
lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_102_ = lean_array_get_size(v_source_100_);
v___x_103_ = lean_nat_dec_lt(v_i_99_, v___x_102_);
if (v___x_103_ == 0)
{
lean_dec_ref(v_source_100_);
lean_dec(v_i_99_);
return v_target_101_;
}
else
{
lean_object* v_es_104_; lean_object* v___x_105_; lean_object* v_source_106_; lean_object* v_target_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v_es_104_ = lean_array_fget(v_source_100_, v_i_99_);
v___x_105_ = lean_box(0);
v_source_106_ = lean_array_fset(v_source_100_, v_i_99_, v___x_105_);
v_target_107_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__3_spec__4_spec__5___redArg(v_target_101_, v_es_104_);
v___x_108_ = lean_unsigned_to_nat(1u);
v___x_109_ = lean_nat_add(v_i_99_, v___x_108_);
lean_dec(v_i_99_);
v_i_99_ = v___x_109_;
v_source_100_ = v_source_106_;
v_target_101_ = v_target_107_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__3___redArg(lean_object* v_data_111_){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v_nbuckets_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_112_ = lean_array_get_size(v_data_111_);
v___x_113_ = lean_unsigned_to_nat(2u);
v_nbuckets_114_ = lean_nat_mul(v___x_112_, v___x_113_);
v___x_115_ = lean_unsigned_to_nat(0u);
v___x_116_ = lean_box(0);
v___x_117_ = lean_mk_array(v_nbuckets_114_, v___x_116_);
v___x_118_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__3_spec__4___redArg(v___x_115_, v_data_111_, v___x_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__4___redArg(lean_object* v_a_119_, lean_object* v_b_120_, lean_object* v_x_121_){
_start:
{
if (lean_obj_tag(v_x_121_) == 0)
{
lean_dec(v_b_120_);
lean_dec_ref(v_a_119_);
return v_x_121_;
}
else
{
lean_object* v_key_122_; lean_object* v_value_123_; lean_object* v_tail_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_138_; 
v_key_122_ = lean_ctor_get(v_x_121_, 0);
v_value_123_ = lean_ctor_get(v_x_121_, 1);
v_tail_124_ = lean_ctor_get(v_x_121_, 2);
v_isSharedCheck_138_ = !lean_is_exclusive(v_x_121_);
if (v_isSharedCheck_138_ == 0)
{
v___x_126_ = v_x_121_;
v_isShared_127_ = v_isSharedCheck_138_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_tail_124_);
lean_inc(v_value_123_);
lean_inc(v_key_122_);
lean_dec(v_x_121_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_138_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
size_t v___x_128_; size_t v___x_129_; uint8_t v___x_130_; 
v___x_128_ = lean_ptr_addr(v_key_122_);
v___x_129_ = lean_ptr_addr(v_a_119_);
v___x_130_ = lean_usize_dec_eq(v___x_128_, v___x_129_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; lean_object* v___x_133_; 
v___x_131_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__4___redArg(v_a_119_, v_b_120_, v_tail_124_);
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 2, v___x_131_);
v___x_133_ = v___x_126_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_key_122_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v_value_123_);
lean_ctor_set(v_reuseFailAlloc_134_, 2, v___x_131_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
else
{
lean_object* v___x_136_; 
lean_dec(v_value_123_);
lean_dec(v_key_122_);
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 1, v_b_120_);
lean_ctor_set(v___x_126_, 0, v_a_119_);
v___x_136_ = v___x_126_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_a_119_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v_b_120_);
lean_ctor_set(v_reuseFailAlloc_137_, 2, v_tail_124_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2___redArg(lean_object* v_a_139_, lean_object* v_x_140_){
_start:
{
if (lean_obj_tag(v_x_140_) == 0)
{
uint8_t v___x_141_; 
v___x_141_ = 0;
return v___x_141_;
}
else
{
lean_object* v_key_142_; lean_object* v_tail_143_; size_t v___x_144_; size_t v___x_145_; uint8_t v___x_146_; 
v_key_142_ = lean_ctor_get(v_x_140_, 0);
v_tail_143_ = lean_ctor_get(v_x_140_, 2);
v___x_144_ = lean_ptr_addr(v_key_142_);
v___x_145_ = lean_ptr_addr(v_a_139_);
v___x_146_ = lean_usize_dec_eq(v___x_144_, v___x_145_);
if (v___x_146_ == 0)
{
v_x_140_ = v_tail_143_;
goto _start;
}
else
{
return v___x_146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2___redArg___boxed(lean_object* v_a_148_, lean_object* v_x_149_){
_start:
{
uint8_t v_res_150_; lean_object* v_r_151_; 
v_res_150_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2___redArg(v_a_148_, v_x_149_);
lean_dec(v_x_149_);
lean_dec_ref(v_a_148_);
v_r_151_ = lean_box(v_res_150_);
return v_r_151_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1___redArg(lean_object* v_m_152_, lean_object* v_a_153_, lean_object* v_b_154_){
_start:
{
lean_object* v_size_155_; lean_object* v_buckets_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_202_; 
v_size_155_ = lean_ctor_get(v_m_152_, 0);
v_buckets_156_ = lean_ctor_get(v_m_152_, 1);
v_isSharedCheck_202_ = !lean_is_exclusive(v_m_152_);
if (v_isSharedCheck_202_ == 0)
{
v___x_158_ = v_m_152_;
v_isShared_159_ = v_isSharedCheck_202_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_buckets_156_);
lean_inc(v_size_155_);
lean_dec(v_m_152_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_202_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_160_; size_t v___x_161_; size_t v___x_162_; size_t v___x_163_; uint64_t v___x_164_; uint64_t v___x_165_; uint64_t v___x_166_; uint64_t v_fold_167_; uint64_t v___x_168_; uint64_t v___x_169_; uint64_t v___x_170_; size_t v___x_171_; size_t v___x_172_; size_t v___x_173_; size_t v___x_174_; size_t v___x_175_; lean_object* v_bkt_176_; uint8_t v___x_177_; 
v___x_160_ = lean_array_get_size(v_buckets_156_);
v___x_161_ = lean_ptr_addr(v_a_153_);
v___x_162_ = ((size_t)3ULL);
v___x_163_ = lean_usize_shift_right(v___x_161_, v___x_162_);
v___x_164_ = lean_usize_to_uint64(v___x_163_);
v___x_165_ = 32ULL;
v___x_166_ = lean_uint64_shift_right(v___x_164_, v___x_165_);
v_fold_167_ = lean_uint64_xor(v___x_164_, v___x_166_);
v___x_168_ = 16ULL;
v___x_169_ = lean_uint64_shift_right(v_fold_167_, v___x_168_);
v___x_170_ = lean_uint64_xor(v_fold_167_, v___x_169_);
v___x_171_ = lean_uint64_to_usize(v___x_170_);
v___x_172_ = lean_usize_of_nat(v___x_160_);
v___x_173_ = ((size_t)1ULL);
v___x_174_ = lean_usize_sub(v___x_172_, v___x_173_);
v___x_175_ = lean_usize_land(v___x_171_, v___x_174_);
v_bkt_176_ = lean_array_uget_borrowed(v_buckets_156_, v___x_175_);
v___x_177_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2___redArg(v_a_153_, v_bkt_176_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; lean_object* v_size_x27_179_; lean_object* v___x_180_; lean_object* v_buckets_x27_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_178_ = lean_unsigned_to_nat(1u);
v_size_x27_179_ = lean_nat_add(v_size_155_, v___x_178_);
lean_dec(v_size_155_);
lean_inc(v_bkt_176_);
v___x_180_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_180_, 0, v_a_153_);
lean_ctor_set(v___x_180_, 1, v_b_154_);
lean_ctor_set(v___x_180_, 2, v_bkt_176_);
v_buckets_x27_181_ = lean_array_uset(v_buckets_156_, v___x_175_, v___x_180_);
v___x_182_ = lean_unsigned_to_nat(4u);
v___x_183_ = lean_nat_mul(v_size_x27_179_, v___x_182_);
v___x_184_ = lean_unsigned_to_nat(3u);
v___x_185_ = lean_nat_div(v___x_183_, v___x_184_);
lean_dec(v___x_183_);
v___x_186_ = lean_array_get_size(v_buckets_x27_181_);
v___x_187_ = lean_nat_dec_le(v___x_185_, v___x_186_);
lean_dec(v___x_185_);
if (v___x_187_ == 0)
{
lean_object* v_val_188_; lean_object* v___x_190_; 
v_val_188_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__3___redArg(v_buckets_x27_181_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 1, v_val_188_);
lean_ctor_set(v___x_158_, 0, v_size_x27_179_);
v___x_190_ = v___x_158_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_size_x27_179_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v_val_188_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
else
{
lean_object* v___x_193_; 
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 1, v_buckets_x27_181_);
lean_ctor_set(v___x_158_, 0, v_size_x27_179_);
v___x_193_ = v___x_158_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_size_x27_179_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v_buckets_x27_181_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
else
{
lean_object* v___x_195_; lean_object* v_buckets_x27_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_200_; 
lean_inc(v_bkt_176_);
v___x_195_ = lean_box(0);
v_buckets_x27_196_ = lean_array_uset(v_buckets_156_, v___x_175_, v___x_195_);
v___x_197_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__4___redArg(v_a_153_, v_b_154_, v_bkt_176_);
v___x_198_ = lean_array_uset(v_buckets_x27_196_, v___x_175_, v___x_197_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 1, v___x_198_);
v___x_200_ = v___x_158_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_size_155_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v___x_198_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0_spec__0___redArg(lean_object* v_a_203_, lean_object* v_x_204_){
_start:
{
if (lean_obj_tag(v_x_204_) == 0)
{
lean_object* v___x_205_; 
v___x_205_ = lean_box(0);
return v___x_205_;
}
else
{
lean_object* v_key_206_; lean_object* v_value_207_; lean_object* v_tail_208_; size_t v___x_209_; size_t v___x_210_; uint8_t v___x_211_; 
v_key_206_ = lean_ctor_get(v_x_204_, 0);
v_value_207_ = lean_ctor_get(v_x_204_, 1);
v_tail_208_ = lean_ctor_get(v_x_204_, 2);
v___x_209_ = lean_ptr_addr(v_key_206_);
v___x_210_ = lean_ptr_addr(v_a_203_);
v___x_211_ = lean_usize_dec_eq(v___x_209_, v___x_210_);
if (v___x_211_ == 0)
{
v_x_204_ = v_tail_208_;
goto _start;
}
else
{
lean_object* v___x_213_; 
lean_inc(v_value_207_);
v___x_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_213_, 0, v_value_207_);
return v___x_213_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0_spec__0___redArg___boxed(lean_object* v_a_214_, lean_object* v_x_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0_spec__0___redArg(v_a_214_, v_x_215_);
lean_dec(v_x_215_);
lean_dec_ref(v_a_214_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0___redArg(lean_object* v_m_217_, lean_object* v_a_218_){
_start:
{
lean_object* v_buckets_219_; lean_object* v___x_220_; size_t v___x_221_; size_t v___x_222_; size_t v___x_223_; uint64_t v___x_224_; uint64_t v___x_225_; uint64_t v___x_226_; uint64_t v_fold_227_; uint64_t v___x_228_; uint64_t v___x_229_; uint64_t v___x_230_; size_t v___x_231_; size_t v___x_232_; size_t v___x_233_; size_t v___x_234_; size_t v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v_buckets_219_ = lean_ctor_get(v_m_217_, 1);
v___x_220_ = lean_array_get_size(v_buckets_219_);
v___x_221_ = lean_ptr_addr(v_a_218_);
v___x_222_ = ((size_t)3ULL);
v___x_223_ = lean_usize_shift_right(v___x_221_, v___x_222_);
v___x_224_ = lean_usize_to_uint64(v___x_223_);
v___x_225_ = 32ULL;
v___x_226_ = lean_uint64_shift_right(v___x_224_, v___x_225_);
v_fold_227_ = lean_uint64_xor(v___x_224_, v___x_226_);
v___x_228_ = 16ULL;
v___x_229_ = lean_uint64_shift_right(v_fold_227_, v___x_228_);
v___x_230_ = lean_uint64_xor(v_fold_227_, v___x_229_);
v___x_231_ = lean_uint64_to_usize(v___x_230_);
v___x_232_ = lean_usize_of_nat(v___x_220_);
v___x_233_ = ((size_t)1ULL);
v___x_234_ = lean_usize_sub(v___x_232_, v___x_233_);
v___x_235_ = lean_usize_land(v___x_231_, v___x_234_);
v___x_236_ = lean_array_uget_borrowed(v_buckets_219_, v___x_235_);
v___x_237_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0_spec__0___redArg(v_a_218_, v___x_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0___redArg___boxed(lean_object* v_m_238_, lean_object* v_a_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0___redArg(v_m_238_, v_a_239_);
lean_dec_ref(v_a_239_);
lean_dec_ref(v_m_238_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet___lam__0___boxed(lean_object* v_fn_241_, lean_object* v_arg_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet___lam__0(v_fn_241_, v_arg_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
lean_dec(v___y_249_);
lean_dec_ref(v___y_248_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
lean_dec(v___y_243_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet___boxed(lean_object* v_e_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet(v_e_252_, v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_);
lean_dec(v_a_259_);
lean_dec_ref(v_a_258_);
lean_dec(v_a_257_);
lean_dec_ref(v_a_256_);
lean_dec(v_a_255_);
lean_dec_ref(v_a_254_);
lean_dec(v_a_253_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet(lean_object* v_e_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_){
_start:
{
lean_object* v_e_272_; lean_object* v_k_273_; lean_object* v___y_274_; lean_object* v___y_275_; lean_object* v___y_276_; lean_object* v___y_277_; lean_object* v___y_278_; lean_object* v___y_279_; lean_object* v___y_280_; 
switch(lean_obj_tag(v_e_262_))
{
case 8:
{
uint8_t v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
lean_dec_ref_known(v_e_262_, 4);
v___x_316_ = 1;
v___x_317_ = lean_box(v___x_316_);
v___x_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
return v___x_318_;
}
case 5:
{
lean_object* v_fn_319_; lean_object* v_arg_320_; lean_object* v___f_321_; 
v_fn_319_ = lean_ctor_get(v_e_262_, 0);
v_arg_320_ = lean_ctor_get(v_e_262_, 1);
lean_inc_ref(v_arg_320_);
lean_inc_ref(v_fn_319_);
v___f_321_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet___lam__0___boxed), 10, 2);
lean_closure_set(v___f_321_, 0, v_fn_319_);
lean_closure_set(v___f_321_, 1, v_arg_320_);
v_e_272_ = v_e_262_;
v_k_273_ = v___f_321_;
v___y_274_ = v_a_263_;
v___y_275_ = v_a_264_;
v___y_276_ = v_a_265_;
v___y_277_ = v_a_266_;
v___y_278_ = v_a_267_;
v___y_279_ = v_a_268_;
v___y_280_ = v_a_269_;
goto v___jp_271_;
}
case 10:
{
lean_object* v_expr_322_; lean_object* v___x_323_; 
v_expr_322_ = lean_ctor_get(v_e_262_, 1);
lean_inc_ref(v_expr_322_);
v___x_323_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet___boxed), 9, 1);
lean_closure_set(v___x_323_, 0, v_expr_322_);
v_e_272_ = v_e_262_;
v_k_273_ = v___x_323_;
v___y_274_ = v_a_263_;
v___y_275_ = v_a_264_;
v___y_276_ = v_a_265_;
v___y_277_ = v_a_266_;
v___y_278_ = v_a_267_;
v___y_279_ = v_a_268_;
v___y_280_ = v_a_269_;
goto v___jp_271_;
}
case 11:
{
lean_object* v_struct_324_; lean_object* v___x_325_; 
v_struct_324_ = lean_ctor_get(v_e_262_, 2);
lean_inc_ref(v_struct_324_);
v___x_325_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet___boxed), 9, 1);
lean_closure_set(v___x_325_, 0, v_struct_324_);
v_e_272_ = v_e_262_;
v_k_273_ = v___x_325_;
v___y_274_ = v_a_263_;
v___y_275_ = v_a_264_;
v___y_276_ = v_a_265_;
v___y_277_ = v_a_266_;
v___y_278_ = v_a_267_;
v___y_279_ = v_a_268_;
v___y_280_ = v_a_269_;
goto v___jp_271_;
}
default: 
{
uint8_t v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
lean_dec_ref(v_e_262_);
v___x_326_ = 0;
v___x_327_ = lean_box(v___x_326_);
v___x_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
return v___x_328_;
}
}
v___jp_271_:
{
lean_object* v___x_281_; lean_object* v_hasLetCache_282_; lean_object* v___x_283_; 
v___x_281_ = lean_st_ref_get(v___y_274_);
v_hasLetCache_282_ = lean_ctor_get(v___x_281_, 2);
lean_inc_ref(v_hasLetCache_282_);
lean_dec(v___x_281_);
v___x_283_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0___redArg(v_hasLetCache_282_, v_e_272_);
lean_dec_ref(v_hasLetCache_282_);
if (lean_obj_tag(v___x_283_) == 1)
{
lean_object* v_val_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_291_; 
lean_dec_ref(v_k_273_);
lean_dec_ref(v_e_272_);
v_val_284_ = lean_ctor_get(v___x_283_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_291_ == 0)
{
v___x_286_ = v___x_283_;
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_val_284_);
lean_dec(v___x_283_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_289_; 
if (v_isShared_287_ == 0)
{
lean_ctor_set_tag(v___x_286_, 0);
v___x_289_ = v___x_286_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_val_284_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
else
{
lean_object* v___x_292_; 
lean_dec(v___x_283_);
lean_inc(v___y_280_);
lean_inc_ref(v___y_279_);
lean_inc(v___y_278_);
lean_inc_ref(v___y_277_);
lean_inc(v___y_276_);
lean_inc_ref(v___y_275_);
lean_inc(v___y_274_);
v___x_292_ = lean_apply_8(v_k_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, lean_box(0));
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v_a_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_315_; 
v_a_293_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_315_ == 0)
{
v___x_295_ = v___x_292_;
v_isShared_296_ = v_isSharedCheck_315_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_a_293_);
lean_dec(v___x_292_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_315_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_297_; lean_object* v_cache_298_; lean_object* v_cacheClosed_299_; lean_object* v_hasLetCache_300_; lean_object* v_decls_301_; lean_object* v_valueMap_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_314_; 
v___x_297_ = lean_st_ref_take(v___y_274_);
v_cache_298_ = lean_ctor_get(v___x_297_, 0);
v_cacheClosed_299_ = lean_ctor_get(v___x_297_, 1);
v_hasLetCache_300_ = lean_ctor_get(v___x_297_, 2);
v_decls_301_ = lean_ctor_get(v___x_297_, 3);
v_valueMap_302_ = lean_ctor_get(v___x_297_, 4);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_314_ == 0)
{
v___x_304_ = v___x_297_;
v_isShared_305_ = v_isSharedCheck_314_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_valueMap_302_);
lean_inc(v_decls_301_);
lean_inc(v_hasLetCache_300_);
lean_inc(v_cacheClosed_299_);
lean_inc(v_cache_298_);
lean_dec(v___x_297_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_314_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_306_; lean_object* v___x_308_; 
lean_inc(v_a_293_);
v___x_306_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1___redArg(v_hasLetCache_300_, v_e_272_, v_a_293_);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 2, v___x_306_);
v___x_308_ = v___x_304_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_cache_298_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v_cacheClosed_299_);
lean_ctor_set(v_reuseFailAlloc_313_, 2, v___x_306_);
lean_ctor_set(v_reuseFailAlloc_313_, 3, v_decls_301_);
lean_ctor_set(v_reuseFailAlloc_313_, 4, v_valueMap_302_);
v___x_308_ = v_reuseFailAlloc_313_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
lean_object* v___x_309_; lean_object* v___x_311_; 
v___x_309_ = lean_st_ref_put(v___y_274_, v___x_308_);
if (v_isShared_296_ == 0)
{
v___x_311_ = v___x_295_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_a_293_);
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
}
else
{
lean_dec_ref(v_e_272_);
return v___x_292_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet___lam__0(lean_object* v_fn_329_, lean_object* v_arg_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet(v_fn_329_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v_a_340_; uint8_t v___x_341_; 
v_a_340_ = lean_ctor_get(v___x_339_, 0);
lean_inc(v_a_340_);
v___x_341_ = lean_unbox(v_a_340_);
lean_dec(v_a_340_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; 
lean_dec_ref_known(v___x_339_, 1);
v___x_342_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet(v_arg_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
return v___x_342_;
}
else
{
lean_dec_ref(v_arg_330_);
return v___x_339_;
}
}
else
{
lean_dec_ref(v_arg_330_);
return v___x_339_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0(lean_object* v_00_u03b2_343_, lean_object* v_m_344_, lean_object* v_a_345_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0___redArg(v_m_344_, v_a_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0___boxed(lean_object* v_00_u03b2_347_, lean_object* v_m_348_, lean_object* v_a_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0(v_00_u03b2_347_, v_m_348_, v_a_349_);
lean_dec_ref(v_a_349_);
lean_dec_ref(v_m_348_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1(lean_object* v_00_u03b2_351_, lean_object* v_m_352_, lean_object* v_a_353_, lean_object* v_b_354_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1___redArg(v_m_352_, v_a_353_, v_b_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0_spec__0(lean_object* v_00_u03b2_356_, lean_object* v_a_357_, lean_object* v_x_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0_spec__0___redArg(v_a_357_, v_x_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0_spec__0___boxed(lean_object* v_00_u03b2_360_, lean_object* v_a_361_, lean_object* v_x_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0_spec__0(v_00_u03b2_360_, v_a_361_, v_x_362_);
lean_dec(v_x_362_);
lean_dec_ref(v_a_361_);
return v_res_363_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2(lean_object* v_00_u03b2_364_, lean_object* v_a_365_, lean_object* v_x_366_){
_start:
{
uint8_t v___x_367_; 
v___x_367_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2___redArg(v_a_365_, v_x_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2___boxed(lean_object* v_00_u03b2_368_, lean_object* v_a_369_, lean_object* v_x_370_){
_start:
{
uint8_t v_res_371_; lean_object* v_r_372_; 
v_res_371_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2(v_00_u03b2_368_, v_a_369_, v_x_370_);
lean_dec(v_x_370_);
lean_dec_ref(v_a_369_);
v_r_372_ = lean_box(v_res_371_);
return v_r_372_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__3(lean_object* v_00_u03b2_373_, lean_object* v_data_374_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__3___redArg(v_data_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__4(lean_object* v_00_u03b2_376_, lean_object* v_a_377_, lean_object* v_b_378_, lean_object* v_x_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__4___redArg(v_a_377_, v_b_378_, v_x_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_381_, lean_object* v_i_382_, lean_object* v_source_383_, lean_object* v_target_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__3_spec__4___redArg(v_i_382_, v_source_383_, v_target_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_386_, lean_object* v_x_387_, lean_object* v_x_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__3_spec__4_spec__5___redArg(v_x_387_, v_x_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2___redArg(lean_object* v_fvarId_390_, lean_object* v___y_391_){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = l_Lean_Expr_fvar___override(v_fvarId_390_);
v___x_394_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_393_, v___y_391_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2___redArg___boxed(lean_object* v_fvarId_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2___redArg(v_fvarId_395_, v___y_396_);
lean_dec(v___y_396_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2(lean_object* v_fvarId_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2___redArg(v_fvarId_399_, v___y_402_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2___boxed(lean_object* v_fvarId_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2(v_fvarId_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
lean_dec(v___y_410_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2___redArg(lean_object* v___y_419_){
_start:
{
lean_object* v___x_421_; lean_object* v_ngen_422_; lean_object* v_namePrefix_423_; lean_object* v_idx_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_453_; 
v___x_421_ = lean_st_ref_get(v___y_419_);
v_ngen_422_ = lean_ctor_get(v___x_421_, 2);
lean_inc_ref(v_ngen_422_);
lean_dec(v___x_421_);
v_namePrefix_423_ = lean_ctor_get(v_ngen_422_, 0);
v_idx_424_ = lean_ctor_get(v_ngen_422_, 1);
v_isSharedCheck_453_ = !lean_is_exclusive(v_ngen_422_);
if (v_isSharedCheck_453_ == 0)
{
v___x_426_ = v_ngen_422_;
v_isShared_427_ = v_isSharedCheck_453_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_idx_424_);
lean_inc(v_namePrefix_423_);
lean_dec(v_ngen_422_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_453_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_428_; lean_object* v_env_429_; lean_object* v_nextMacroScope_430_; lean_object* v_auxDeclNGen_431_; lean_object* v_traceState_432_; lean_object* v_cache_433_; lean_object* v_messages_434_; lean_object* v_infoState_435_; lean_object* v_snapshotTasks_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_451_; 
v___x_428_ = lean_st_ref_take(v___y_419_);
v_env_429_ = lean_ctor_get(v___x_428_, 0);
v_nextMacroScope_430_ = lean_ctor_get(v___x_428_, 1);
v_auxDeclNGen_431_ = lean_ctor_get(v___x_428_, 3);
v_traceState_432_ = lean_ctor_get(v___x_428_, 4);
v_cache_433_ = lean_ctor_get(v___x_428_, 5);
v_messages_434_ = lean_ctor_get(v___x_428_, 6);
v_infoState_435_ = lean_ctor_get(v___x_428_, 7);
v_snapshotTasks_436_ = lean_ctor_get(v___x_428_, 8);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_451_ == 0)
{
lean_object* v_unused_452_; 
v_unused_452_ = lean_ctor_get(v___x_428_, 2);
lean_dec(v_unused_452_);
v___x_438_ = v___x_428_;
v_isShared_439_ = v_isSharedCheck_451_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_snapshotTasks_436_);
lean_inc(v_infoState_435_);
lean_inc(v_messages_434_);
lean_inc(v_cache_433_);
lean_inc(v_traceState_432_);
lean_inc(v_auxDeclNGen_431_);
lean_inc(v_nextMacroScope_430_);
lean_inc(v_env_429_);
lean_dec(v___x_428_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_451_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v_r_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_444_; 
lean_inc(v_idx_424_);
lean_inc(v_namePrefix_423_);
v_r_440_ = l_Lean_Name_num___override(v_namePrefix_423_, v_idx_424_);
v___x_441_ = lean_unsigned_to_nat(1u);
v___x_442_ = lean_nat_add(v_idx_424_, v___x_441_);
lean_dec(v_idx_424_);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 1, v___x_442_);
v___x_444_ = v___x_426_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_namePrefix_423_);
lean_ctor_set(v_reuseFailAlloc_450_, 1, v___x_442_);
v___x_444_ = v_reuseFailAlloc_450_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
lean_object* v___x_446_; 
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 2, v___x_444_);
v___x_446_ = v___x_438_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_env_429_);
lean_ctor_set(v_reuseFailAlloc_449_, 1, v_nextMacroScope_430_);
lean_ctor_set(v_reuseFailAlloc_449_, 2, v___x_444_);
lean_ctor_set(v_reuseFailAlloc_449_, 3, v_auxDeclNGen_431_);
lean_ctor_set(v_reuseFailAlloc_449_, 4, v_traceState_432_);
lean_ctor_set(v_reuseFailAlloc_449_, 5, v_cache_433_);
lean_ctor_set(v_reuseFailAlloc_449_, 6, v_messages_434_);
lean_ctor_set(v_reuseFailAlloc_449_, 7, v_infoState_435_);
lean_ctor_set(v_reuseFailAlloc_449_, 8, v_snapshotTasks_436_);
v___x_446_ = v_reuseFailAlloc_449_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = lean_st_ref_put(v___y_419_, v___x_446_);
v___x_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_448_, 0, v_r_440_);
return v___x_448_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2___redArg___boxed(lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2___redArg(v___y_454_);
lean_dec(v___y_454_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1(lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
lean_object* v___x_465_; lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_473_; 
v___x_465_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2___redArg(v___y_463_);
v_a_466_ = lean_ctor_get(v___x_465_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_473_ == 0)
{
v___x_468_ = v___x_465_;
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___x_465_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_471_; 
if (v_isShared_469_ == 0)
{
v___x_471_ = v___x_468_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_a_466_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1___boxed(lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1(v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
lean_dec(v___y_474_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0___redArg(lean_object* v_a_483_, lean_object* v_x_484_){
_start:
{
if (lean_obj_tag(v_x_484_) == 0)
{
lean_object* v___x_485_; 
v___x_485_ = lean_box(0);
return v___x_485_;
}
else
{
lean_object* v_key_486_; lean_object* v_value_487_; lean_object* v_tail_488_; lean_object* v_fst_489_; lean_object* v_snd_490_; lean_object* v_fst_491_; lean_object* v_snd_492_; size_t v___x_493_; size_t v___x_494_; uint8_t v___x_495_; 
v_key_486_ = lean_ctor_get(v_x_484_, 0);
v_value_487_ = lean_ctor_get(v_x_484_, 1);
v_tail_488_ = lean_ctor_get(v_x_484_, 2);
v_fst_489_ = lean_ctor_get(v_key_486_, 0);
v_snd_490_ = lean_ctor_get(v_key_486_, 1);
v_fst_491_ = lean_ctor_get(v_a_483_, 0);
v_snd_492_ = lean_ctor_get(v_a_483_, 1);
v___x_493_ = lean_ptr_addr(v_fst_489_);
v___x_494_ = lean_ptr_addr(v_fst_491_);
v___x_495_ = lean_usize_dec_eq(v___x_493_, v___x_494_);
if (v___x_495_ == 0)
{
v_x_484_ = v_tail_488_;
goto _start;
}
else
{
size_t v___x_497_; size_t v___x_498_; uint8_t v___x_499_; 
v___x_497_ = lean_ptr_addr(v_snd_490_);
v___x_498_ = lean_ptr_addr(v_snd_492_);
v___x_499_ = lean_usize_dec_eq(v___x_497_, v___x_498_);
if (v___x_499_ == 0)
{
v_x_484_ = v_tail_488_;
goto _start;
}
else
{
lean_object* v___x_501_; 
lean_inc(v_value_487_);
v___x_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_501_, 0, v_value_487_);
return v___x_501_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0___redArg___boxed(lean_object* v_a_502_, lean_object* v_x_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0___redArg(v_a_502_, v_x_503_);
lean_dec(v_x_503_);
lean_dec_ref(v_a_502_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0___redArg(lean_object* v_m_505_, lean_object* v_a_506_){
_start:
{
lean_object* v_buckets_507_; lean_object* v_fst_508_; lean_object* v_snd_509_; lean_object* v___x_510_; size_t v___x_511_; size_t v___x_512_; size_t v___x_513_; uint64_t v___x_514_; size_t v___x_515_; size_t v___x_516_; uint64_t v___x_517_; uint64_t v___x_518_; uint64_t v___x_519_; uint64_t v___x_520_; uint64_t v_fold_521_; uint64_t v___x_522_; uint64_t v___x_523_; uint64_t v___x_524_; size_t v___x_525_; size_t v___x_526_; size_t v___x_527_; size_t v___x_528_; size_t v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v_buckets_507_ = lean_ctor_get(v_m_505_, 1);
v_fst_508_ = lean_ctor_get(v_a_506_, 0);
v_snd_509_ = lean_ctor_get(v_a_506_, 1);
v___x_510_ = lean_array_get_size(v_buckets_507_);
v___x_511_ = lean_ptr_addr(v_fst_508_);
v___x_512_ = ((size_t)3ULL);
v___x_513_ = lean_usize_shift_right(v___x_511_, v___x_512_);
v___x_514_ = lean_usize_to_uint64(v___x_513_);
v___x_515_ = lean_ptr_addr(v_snd_509_);
v___x_516_ = lean_usize_shift_right(v___x_515_, v___x_512_);
v___x_517_ = lean_usize_to_uint64(v___x_516_);
v___x_518_ = lean_uint64_mix_hash(v___x_514_, v___x_517_);
v___x_519_ = 32ULL;
v___x_520_ = lean_uint64_shift_right(v___x_518_, v___x_519_);
v_fold_521_ = lean_uint64_xor(v___x_518_, v___x_520_);
v___x_522_ = 16ULL;
v___x_523_ = lean_uint64_shift_right(v_fold_521_, v___x_522_);
v___x_524_ = lean_uint64_xor(v_fold_521_, v___x_523_);
v___x_525_ = lean_uint64_to_usize(v___x_524_);
v___x_526_ = lean_usize_of_nat(v___x_510_);
v___x_527_ = ((size_t)1ULL);
v___x_528_ = lean_usize_sub(v___x_526_, v___x_527_);
v___x_529_ = lean_usize_land(v___x_525_, v___x_528_);
v___x_530_ = lean_array_uget_borrowed(v_buckets_507_, v___x_529_);
v___x_531_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0___redArg(v_a_506_, v___x_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0___redArg___boxed(lean_object* v_m_532_, lean_object* v_a_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0___redArg(v_m_532_, v_a_533_);
lean_dec_ref(v_a_533_);
lean_dec_ref(v_m_532_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__7___redArg(lean_object* v_a_535_, lean_object* v_b_536_, lean_object* v_x_537_){
_start:
{
if (lean_obj_tag(v_x_537_) == 0)
{
lean_dec(v_b_536_);
lean_dec_ref(v_a_535_);
return v_x_537_;
}
else
{
lean_object* v_key_538_; lean_object* v_value_539_; lean_object* v_tail_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_560_; 
v_key_538_ = lean_ctor_get(v_x_537_, 0);
v_value_539_ = lean_ctor_get(v_x_537_, 1);
v_tail_540_ = lean_ctor_get(v_x_537_, 2);
v_isSharedCheck_560_ = !lean_is_exclusive(v_x_537_);
if (v_isSharedCheck_560_ == 0)
{
v___x_542_ = v_x_537_;
v_isShared_543_ = v_isSharedCheck_560_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_tail_540_);
lean_inc(v_value_539_);
lean_inc(v_key_538_);
lean_dec(v_x_537_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_560_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v_fst_549_; lean_object* v_snd_550_; lean_object* v_fst_551_; lean_object* v_snd_552_; size_t v___x_553_; size_t v___x_554_; uint8_t v___x_555_; 
v_fst_549_ = lean_ctor_get(v_key_538_, 0);
v_snd_550_ = lean_ctor_get(v_key_538_, 1);
v_fst_551_ = lean_ctor_get(v_a_535_, 0);
v_snd_552_ = lean_ctor_get(v_a_535_, 1);
v___x_553_ = lean_ptr_addr(v_fst_549_);
v___x_554_ = lean_ptr_addr(v_fst_551_);
v___x_555_ = lean_usize_dec_eq(v___x_553_, v___x_554_);
if (v___x_555_ == 0)
{
goto v___jp_544_;
}
else
{
size_t v___x_556_; size_t v___x_557_; uint8_t v___x_558_; 
v___x_556_ = lean_ptr_addr(v_snd_550_);
v___x_557_ = lean_ptr_addr(v_snd_552_);
v___x_558_ = lean_usize_dec_eq(v___x_556_, v___x_557_);
if (v___x_558_ == 0)
{
goto v___jp_544_;
}
else
{
lean_object* v___x_559_; 
lean_del_object(v___x_542_);
lean_dec(v_value_539_);
lean_dec(v_key_538_);
v___x_559_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_559_, 0, v_a_535_);
lean_ctor_set(v___x_559_, 1, v_b_536_);
lean_ctor_set(v___x_559_, 2, v_tail_540_);
return v___x_559_;
}
}
v___jp_544_:
{
lean_object* v___x_545_; lean_object* v___x_547_; 
v___x_545_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__7___redArg(v_a_535_, v_b_536_, v_tail_540_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 2, v___x_545_);
v___x_547_ = v___x_542_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_key_538_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v_value_539_);
lean_ctor_set(v_reuseFailAlloc_548_, 2, v___x_545_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5___redArg(lean_object* v_a_561_, lean_object* v_x_562_){
_start:
{
if (lean_obj_tag(v_x_562_) == 0)
{
uint8_t v___x_563_; 
v___x_563_ = 0;
return v___x_563_;
}
else
{
lean_object* v_key_564_; lean_object* v_tail_565_; lean_object* v_fst_566_; lean_object* v_snd_567_; lean_object* v_fst_568_; lean_object* v_snd_569_; size_t v___x_570_; size_t v___x_571_; uint8_t v___x_572_; 
v_key_564_ = lean_ctor_get(v_x_562_, 0);
v_tail_565_ = lean_ctor_get(v_x_562_, 2);
v_fst_566_ = lean_ctor_get(v_key_564_, 0);
v_snd_567_ = lean_ctor_get(v_key_564_, 1);
v_fst_568_ = lean_ctor_get(v_a_561_, 0);
v_snd_569_ = lean_ctor_get(v_a_561_, 1);
v___x_570_ = lean_ptr_addr(v_fst_566_);
v___x_571_ = lean_ptr_addr(v_fst_568_);
v___x_572_ = lean_usize_dec_eq(v___x_570_, v___x_571_);
if (v___x_572_ == 0)
{
v_x_562_ = v_tail_565_;
goto _start;
}
else
{
size_t v___x_574_; size_t v___x_575_; uint8_t v___x_576_; 
v___x_574_ = lean_ptr_addr(v_snd_567_);
v___x_575_ = lean_ptr_addr(v_snd_569_);
v___x_576_ = lean_usize_dec_eq(v___x_574_, v___x_575_);
if (v___x_576_ == 0)
{
v_x_562_ = v_tail_565_;
goto _start;
}
else
{
return v___x_576_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5___redArg___boxed(lean_object* v_a_578_, lean_object* v_x_579_){
_start:
{
uint8_t v_res_580_; lean_object* v_r_581_; 
v_res_580_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5___redArg(v_a_578_, v_x_579_);
lean_dec(v_x_579_);
lean_dec_ref(v_a_578_);
v_r_581_ = lean_box(v_res_580_);
return v_r_581_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6_spec__7_spec__8___redArg(lean_object* v_x_582_, lean_object* v_x_583_){
_start:
{
if (lean_obj_tag(v_x_583_) == 0)
{
return v_x_582_;
}
else
{
lean_object* v_key_584_; lean_object* v_value_585_; lean_object* v_tail_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_618_; 
v_key_584_ = lean_ctor_get(v_x_583_, 0);
v_value_585_ = lean_ctor_get(v_x_583_, 1);
v_tail_586_ = lean_ctor_get(v_x_583_, 2);
v_isSharedCheck_618_ = !lean_is_exclusive(v_x_583_);
if (v_isSharedCheck_618_ == 0)
{
v___x_588_ = v_x_583_;
v_isShared_589_ = v_isSharedCheck_618_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_tail_586_);
lean_inc(v_value_585_);
lean_inc(v_key_584_);
lean_dec(v_x_583_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_618_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v_fst_590_; lean_object* v_snd_591_; lean_object* v___x_592_; size_t v___x_593_; size_t v___x_594_; size_t v___x_595_; uint64_t v___x_596_; size_t v___x_597_; size_t v___x_598_; uint64_t v___x_599_; uint64_t v___x_600_; uint64_t v___x_601_; uint64_t v___x_602_; uint64_t v_fold_603_; uint64_t v___x_604_; uint64_t v___x_605_; uint64_t v___x_606_; size_t v___x_607_; size_t v___x_608_; size_t v___x_609_; size_t v___x_610_; size_t v___x_611_; lean_object* v___x_612_; lean_object* v___x_614_; 
v_fst_590_ = lean_ctor_get(v_key_584_, 0);
v_snd_591_ = lean_ctor_get(v_key_584_, 1);
v___x_592_ = lean_array_get_size(v_x_582_);
v___x_593_ = lean_ptr_addr(v_fst_590_);
v___x_594_ = ((size_t)3ULL);
v___x_595_ = lean_usize_shift_right(v___x_593_, v___x_594_);
v___x_596_ = lean_usize_to_uint64(v___x_595_);
v___x_597_ = lean_ptr_addr(v_snd_591_);
v___x_598_ = lean_usize_shift_right(v___x_597_, v___x_594_);
v___x_599_ = lean_usize_to_uint64(v___x_598_);
v___x_600_ = lean_uint64_mix_hash(v___x_596_, v___x_599_);
v___x_601_ = 32ULL;
v___x_602_ = lean_uint64_shift_right(v___x_600_, v___x_601_);
v_fold_603_ = lean_uint64_xor(v___x_600_, v___x_602_);
v___x_604_ = 16ULL;
v___x_605_ = lean_uint64_shift_right(v_fold_603_, v___x_604_);
v___x_606_ = lean_uint64_xor(v_fold_603_, v___x_605_);
v___x_607_ = lean_uint64_to_usize(v___x_606_);
v___x_608_ = lean_usize_of_nat(v___x_592_);
v___x_609_ = ((size_t)1ULL);
v___x_610_ = lean_usize_sub(v___x_608_, v___x_609_);
v___x_611_ = lean_usize_land(v___x_607_, v___x_610_);
v___x_612_ = lean_array_uget_borrowed(v_x_582_, v___x_611_);
lean_inc(v___x_612_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 2, v___x_612_);
v___x_614_ = v___x_588_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_key_584_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v_value_585_);
lean_ctor_set(v_reuseFailAlloc_617_, 2, v___x_612_);
v___x_614_ = v_reuseFailAlloc_617_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_615_; 
v___x_615_ = lean_array_uset(v_x_582_, v___x_611_, v___x_614_);
v_x_582_ = v___x_615_;
v_x_583_ = v_tail_586_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6_spec__7___redArg(lean_object* v_i_619_, lean_object* v_source_620_, lean_object* v_target_621_){
_start:
{
lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_622_ = lean_array_get_size(v_source_620_);
v___x_623_ = lean_nat_dec_lt(v_i_619_, v___x_622_);
if (v___x_623_ == 0)
{
lean_dec_ref(v_source_620_);
lean_dec(v_i_619_);
return v_target_621_;
}
else
{
lean_object* v_es_624_; lean_object* v___x_625_; lean_object* v_source_626_; lean_object* v_target_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v_es_624_ = lean_array_fget(v_source_620_, v_i_619_);
v___x_625_ = lean_box(0);
v_source_626_ = lean_array_fset(v_source_620_, v_i_619_, v___x_625_);
v_target_627_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6_spec__7_spec__8___redArg(v_target_621_, v_es_624_);
v___x_628_ = lean_unsigned_to_nat(1u);
v___x_629_ = lean_nat_add(v_i_619_, v___x_628_);
lean_dec(v_i_619_);
v_i_619_ = v___x_629_;
v_source_620_ = v_source_626_;
v_target_621_ = v_target_627_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6___redArg(lean_object* v_data_631_){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v_nbuckets_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_632_ = lean_array_get_size(v_data_631_);
v___x_633_ = lean_unsigned_to_nat(2u);
v_nbuckets_634_ = lean_nat_mul(v___x_632_, v___x_633_);
v___x_635_ = lean_unsigned_to_nat(0u);
v___x_636_ = lean_box(0);
v___x_637_ = lean_mk_array(v_nbuckets_634_, v___x_636_);
v___x_638_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6_spec__7___redArg(v___x_635_, v_data_631_, v___x_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3___redArg(lean_object* v_m_639_, lean_object* v_a_640_, lean_object* v_b_641_){
_start:
{
lean_object* v_size_642_; lean_object* v_buckets_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_695_; 
v_size_642_ = lean_ctor_get(v_m_639_, 0);
v_buckets_643_ = lean_ctor_get(v_m_639_, 1);
v_isSharedCheck_695_ = !lean_is_exclusive(v_m_639_);
if (v_isSharedCheck_695_ == 0)
{
v___x_645_ = v_m_639_;
v_isShared_646_ = v_isSharedCheck_695_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_buckets_643_);
lean_inc(v_size_642_);
lean_dec(v_m_639_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_695_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v_fst_647_; lean_object* v_snd_648_; lean_object* v___x_649_; size_t v___x_650_; size_t v___x_651_; size_t v___x_652_; uint64_t v___x_653_; size_t v___x_654_; size_t v___x_655_; uint64_t v___x_656_; uint64_t v___x_657_; uint64_t v___x_658_; uint64_t v___x_659_; uint64_t v_fold_660_; uint64_t v___x_661_; uint64_t v___x_662_; uint64_t v___x_663_; size_t v___x_664_; size_t v___x_665_; size_t v___x_666_; size_t v___x_667_; size_t v___x_668_; lean_object* v_bkt_669_; uint8_t v___x_670_; 
v_fst_647_ = lean_ctor_get(v_a_640_, 0);
v_snd_648_ = lean_ctor_get(v_a_640_, 1);
v___x_649_ = lean_array_get_size(v_buckets_643_);
v___x_650_ = lean_ptr_addr(v_fst_647_);
v___x_651_ = ((size_t)3ULL);
v___x_652_ = lean_usize_shift_right(v___x_650_, v___x_651_);
v___x_653_ = lean_usize_to_uint64(v___x_652_);
v___x_654_ = lean_ptr_addr(v_snd_648_);
v___x_655_ = lean_usize_shift_right(v___x_654_, v___x_651_);
v___x_656_ = lean_usize_to_uint64(v___x_655_);
v___x_657_ = lean_uint64_mix_hash(v___x_653_, v___x_656_);
v___x_658_ = 32ULL;
v___x_659_ = lean_uint64_shift_right(v___x_657_, v___x_658_);
v_fold_660_ = lean_uint64_xor(v___x_657_, v___x_659_);
v___x_661_ = 16ULL;
v___x_662_ = lean_uint64_shift_right(v_fold_660_, v___x_661_);
v___x_663_ = lean_uint64_xor(v_fold_660_, v___x_662_);
v___x_664_ = lean_uint64_to_usize(v___x_663_);
v___x_665_ = lean_usize_of_nat(v___x_649_);
v___x_666_ = ((size_t)1ULL);
v___x_667_ = lean_usize_sub(v___x_665_, v___x_666_);
v___x_668_ = lean_usize_land(v___x_664_, v___x_667_);
v_bkt_669_ = lean_array_uget_borrowed(v_buckets_643_, v___x_668_);
v___x_670_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5___redArg(v_a_640_, v_bkt_669_);
if (v___x_670_ == 0)
{
lean_object* v___x_671_; lean_object* v_size_x27_672_; lean_object* v___x_673_; lean_object* v_buckets_x27_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; uint8_t v___x_680_; 
v___x_671_ = lean_unsigned_to_nat(1u);
v_size_x27_672_ = lean_nat_add(v_size_642_, v___x_671_);
lean_dec(v_size_642_);
lean_inc(v_bkt_669_);
v___x_673_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_673_, 0, v_a_640_);
lean_ctor_set(v___x_673_, 1, v_b_641_);
lean_ctor_set(v___x_673_, 2, v_bkt_669_);
v_buckets_x27_674_ = lean_array_uset(v_buckets_643_, v___x_668_, v___x_673_);
v___x_675_ = lean_unsigned_to_nat(4u);
v___x_676_ = lean_nat_mul(v_size_x27_672_, v___x_675_);
v___x_677_ = lean_unsigned_to_nat(3u);
v___x_678_ = lean_nat_div(v___x_676_, v___x_677_);
lean_dec(v___x_676_);
v___x_679_ = lean_array_get_size(v_buckets_x27_674_);
v___x_680_ = lean_nat_dec_le(v___x_678_, v___x_679_);
lean_dec(v___x_678_);
if (v___x_680_ == 0)
{
lean_object* v_val_681_; lean_object* v___x_683_; 
v_val_681_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6___redArg(v_buckets_x27_674_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 1, v_val_681_);
lean_ctor_set(v___x_645_, 0, v_size_x27_672_);
v___x_683_ = v___x_645_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_size_x27_672_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v_val_681_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
else
{
lean_object* v___x_686_; 
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 1, v_buckets_x27_674_);
lean_ctor_set(v___x_645_, 0, v_size_x27_672_);
v___x_686_ = v___x_645_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_size_x27_672_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v_buckets_x27_674_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
else
{
lean_object* v___x_688_; lean_object* v_buckets_x27_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_693_; 
lean_inc(v_bkt_669_);
v___x_688_ = lean_box(0);
v_buckets_x27_689_ = lean_array_uset(v_buckets_643_, v___x_668_, v___x_688_);
v___x_690_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__7___redArg(v_a_640_, v_b_641_, v_bkt_669_);
v___x_691_ = lean_array_uset(v_buckets_x27_689_, v___x_668_, v___x_690_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 1, v___x_691_);
v___x_693_ = v___x_645_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_size_642_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v___x_691_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl(lean_object* v_userName_696_, lean_object* v_type_697_, lean_object* v_value_698_, uint8_t v_nondep_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_){
_start:
{
lean_object* v___x_708_; lean_object* v_valueMap_709_; lean_object* v_key_710_; lean_object* v___x_711_; 
v___x_708_ = lean_st_ref_get(v_a_700_);
v_valueMap_709_ = lean_ctor_get(v___x_708_, 4);
lean_inc_ref(v_valueMap_709_);
lean_dec(v___x_708_);
lean_inc_ref(v_value_698_);
lean_inc_ref(v_type_697_);
v_key_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_710_, 0, v_type_697_);
lean_ctor_set(v_key_710_, 1, v_value_698_);
v___x_711_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0___redArg(v_valueMap_709_, v_key_710_);
lean_dec_ref(v_valueMap_709_);
if (lean_obj_tag(v___x_711_) == 1)
{
lean_object* v_val_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_759_; 
lean_dec_ref_known(v_key_710_, 2);
lean_dec_ref(v_value_698_);
lean_dec_ref(v_type_697_);
lean_dec(v_userName_696_);
v_val_712_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_759_ == 0)
{
v___x_714_ = v___x_711_;
v_isShared_715_ = v_isSharedCheck_759_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_val_712_);
lean_dec(v___x_711_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_759_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_716_; lean_object* v___y_718_; 
v___x_716_ = l_Lean_Meta_Sym_LiftLet_instInhabitedDecl_default;
if (v_nondep_699_ == 0)
{
lean_object* v___x_726_; lean_object* v_cache_727_; lean_object* v_cacheClosed_728_; lean_object* v_hasLetCache_729_; lean_object* v_decls_730_; lean_object* v_valueMap_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_758_; 
v___x_726_ = lean_st_ref_take(v_a_700_);
v_cache_727_ = lean_ctor_get(v___x_726_, 0);
v_cacheClosed_728_ = lean_ctor_get(v___x_726_, 1);
v_hasLetCache_729_ = lean_ctor_get(v___x_726_, 2);
v_decls_730_ = lean_ctor_get(v___x_726_, 3);
v_valueMap_731_ = lean_ctor_get(v___x_726_, 4);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_758_ == 0)
{
v___x_733_ = v___x_726_;
v_isShared_734_ = v_isSharedCheck_758_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_valueMap_731_);
lean_inc(v_decls_730_);
lean_inc(v_hasLetCache_729_);
lean_inc(v_cacheClosed_728_);
lean_inc(v_cache_727_);
lean_dec(v___x_726_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_758_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___y_736_; lean_object* v___x_741_; uint8_t v___x_742_; 
v___x_741_ = lean_array_get_size(v_decls_730_);
v___x_742_ = lean_nat_dec_lt(v_val_712_, v___x_741_);
if (v___x_742_ == 0)
{
v___y_736_ = v_decls_730_;
goto v___jp_735_;
}
else
{
lean_object* v_v_743_; lean_object* v_fvar_744_; lean_object* v_userName_745_; lean_object* v_type_746_; lean_object* v_value_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_757_; 
v_v_743_ = lean_array_fget(v_decls_730_, v_val_712_);
v_fvar_744_ = lean_ctor_get(v_v_743_, 0);
v_userName_745_ = lean_ctor_get(v_v_743_, 1);
v_type_746_ = lean_ctor_get(v_v_743_, 2);
v_value_747_ = lean_ctor_get(v_v_743_, 3);
v_isSharedCheck_757_ = !lean_is_exclusive(v_v_743_);
if (v_isSharedCheck_757_ == 0)
{
v___x_749_ = v_v_743_;
v_isShared_750_ = v_isSharedCheck_757_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_value_747_);
lean_inc(v_type_746_);
lean_inc(v_userName_745_);
lean_inc(v_fvar_744_);
lean_dec(v_v_743_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_757_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_751_; lean_object* v_xs_x27_752_; lean_object* v___x_754_; 
v___x_751_ = lean_box(0);
v_xs_x27_752_ = lean_array_fset(v_decls_730_, v_val_712_, v___x_751_);
if (v_isShared_750_ == 0)
{
v___x_754_ = v___x_749_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_fvar_744_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v_userName_745_);
lean_ctor_set(v_reuseFailAlloc_756_, 2, v_type_746_);
lean_ctor_set(v_reuseFailAlloc_756_, 3, v_value_747_);
v___x_754_ = v_reuseFailAlloc_756_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
lean_object* v___x_755_; 
lean_ctor_set_uint8(v___x_754_, sizeof(void*)*4, v_nondep_699_);
v___x_755_ = lean_array_fset(v_xs_x27_752_, v_val_712_, v___x_754_);
v___y_736_ = v___x_755_;
goto v___jp_735_;
}
}
}
v___jp_735_:
{
lean_object* v___x_738_; 
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 3, v___y_736_);
v___x_738_ = v___x_733_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_cache_727_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v_cacheClosed_728_);
lean_ctor_set(v_reuseFailAlloc_740_, 2, v_hasLetCache_729_);
lean_ctor_set(v_reuseFailAlloc_740_, 3, v___y_736_);
lean_ctor_set(v_reuseFailAlloc_740_, 4, v_valueMap_731_);
v___x_738_ = v_reuseFailAlloc_740_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
lean_object* v___x_739_; 
v___x_739_ = lean_st_ref_put(v_a_700_, v___x_738_);
v___y_718_ = v_a_700_;
goto v___jp_717_;
}
}
}
}
else
{
v___y_718_ = v_a_700_;
goto v___jp_717_;
}
v___jp_717_:
{
lean_object* v___x_719_; lean_object* v_decls_720_; lean_object* v___x_721_; lean_object* v_fvar_722_; lean_object* v___x_724_; 
v___x_719_ = lean_st_ref_get(v___y_718_);
v_decls_720_ = lean_ctor_get(v___x_719_, 3);
lean_inc_ref(v_decls_720_);
lean_dec(v___x_719_);
v___x_721_ = lean_array_get(v___x_716_, v_decls_720_, v_val_712_);
lean_dec(v_val_712_);
lean_dec_ref(v_decls_720_);
v_fvar_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc_ref(v_fvar_722_);
lean_dec(v___x_721_);
if (v_isShared_715_ == 0)
{
lean_ctor_set_tag(v___x_714_, 0);
lean_ctor_set(v___x_714_, 0, v_fvar_722_);
v___x_724_ = v___x_714_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_fvar_722_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
else
{
lean_object* v___x_760_; 
lean_dec(v___x_711_);
v___x_760_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1(v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v_a_761_; lean_object* v___x_762_; 
v_a_761_ = lean_ctor_get(v___x_760_, 0);
lean_inc(v_a_761_);
lean_dec_ref_known(v___x_760_, 1);
v___x_762_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2___redArg(v_a_761_, v_a_702_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_790_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_790_ == 0)
{
v___x_765_ = v___x_762_;
v_isShared_766_ = v_isSharedCheck_790_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_762_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_790_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v_decls_769_; lean_object* v_cache_770_; lean_object* v_cacheClosed_771_; lean_object* v_hasLetCache_772_; lean_object* v_decls_773_; lean_object* v_valueMap_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_789_; 
v___x_767_ = lean_st_ref_get(v_a_700_);
v___x_768_ = lean_st_ref_take(v_a_700_);
v_decls_769_ = lean_ctor_get(v___x_767_, 3);
lean_inc_ref(v_decls_769_);
lean_dec(v___x_767_);
v_cache_770_ = lean_ctor_get(v___x_768_, 0);
v_cacheClosed_771_ = lean_ctor_get(v___x_768_, 1);
v_hasLetCache_772_ = lean_ctor_get(v___x_768_, 2);
v_decls_773_ = lean_ctor_get(v___x_768_, 3);
v_valueMap_774_ = lean_ctor_get(v___x_768_, 4);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_789_ == 0)
{
v___x_776_ = v___x_768_;
v_isShared_777_ = v_isSharedCheck_789_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_valueMap_774_);
lean_inc(v_decls_773_);
lean_inc(v_hasLetCache_772_);
lean_inc(v_cacheClosed_771_);
lean_inc(v_cache_770_);
lean_dec(v___x_768_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_789_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_783_; 
v___x_778_ = lean_array_get_size(v_decls_769_);
lean_dec_ref(v_decls_769_);
lean_inc(v_a_763_);
v___x_779_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_779_, 0, v_a_763_);
lean_ctor_set(v___x_779_, 1, v_userName_696_);
lean_ctor_set(v___x_779_, 2, v_type_697_);
lean_ctor_set(v___x_779_, 3, v_value_698_);
lean_ctor_set_uint8(v___x_779_, sizeof(void*)*4, v_nondep_699_);
v___x_780_ = lean_array_push(v_decls_773_, v___x_779_);
v___x_781_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3___redArg(v_valueMap_774_, v_key_710_, v___x_778_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 4, v___x_781_);
lean_ctor_set(v___x_776_, 3, v___x_780_);
v___x_783_ = v___x_776_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_cache_770_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v_cacheClosed_771_);
lean_ctor_set(v_reuseFailAlloc_788_, 2, v_hasLetCache_772_);
lean_ctor_set(v_reuseFailAlloc_788_, 3, v___x_780_);
lean_ctor_set(v_reuseFailAlloc_788_, 4, v___x_781_);
v___x_783_ = v_reuseFailAlloc_788_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
lean_object* v___x_784_; lean_object* v___x_786_; 
v___x_784_ = lean_st_ref_put(v_a_700_, v___x_783_);
if (v_isShared_766_ == 0)
{
v___x_786_ = v___x_765_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_a_763_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_710_, 2);
lean_dec_ref(v_value_698_);
lean_dec_ref(v_type_697_);
lean_dec(v_userName_696_);
return v___x_762_;
}
}
else
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
lean_dec_ref_known(v_key_710_, 2);
lean_dec_ref(v_value_698_);
lean_dec_ref(v_type_697_);
lean_dec(v_userName_696_);
v_a_791_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_760_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_760_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl___boxed(lean_object* v_userName_799_, lean_object* v_type_800_, lean_object* v_value_801_, lean_object* v_nondep_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_){
_start:
{
uint8_t v_nondep_boxed_811_; lean_object* v_res_812_; 
v_nondep_boxed_811_ = lean_unbox(v_nondep_802_);
v_res_812_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl(v_userName_799_, v_type_800_, v_value_801_, v_nondep_boxed_811_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0(lean_object* v_00_u03b2_813_, lean_object* v_m_814_, lean_object* v_a_815_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0___redArg(v_m_814_, v_a_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0___boxed(lean_object* v_00_u03b2_817_, lean_object* v_m_818_, lean_object* v_a_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0(v_00_u03b2_817_, v_m_818_, v_a_819_);
lean_dec_ref(v_a_819_);
lean_dec_ref(v_m_818_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2(lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2___redArg(v___y_827_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2___boxed(lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2(v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3(lean_object* v_00_u03b2_839_, lean_object* v_m_840_, lean_object* v_a_841_, lean_object* v_b_842_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3___redArg(v_m_840_, v_a_841_, v_b_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0(lean_object* v_00_u03b2_844_, lean_object* v_a_845_, lean_object* v_x_846_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0___redArg(v_a_845_, v_x_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_848_, lean_object* v_a_849_, lean_object* v_x_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0(v_00_u03b2_848_, v_a_849_, v_x_850_);
lean_dec(v_x_850_);
lean_dec_ref(v_a_849_);
return v_res_851_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5(lean_object* v_00_u03b2_852_, lean_object* v_a_853_, lean_object* v_x_854_){
_start:
{
uint8_t v___x_855_; 
v___x_855_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5___redArg(v_a_853_, v_x_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5___boxed(lean_object* v_00_u03b2_856_, lean_object* v_a_857_, lean_object* v_x_858_){
_start:
{
uint8_t v_res_859_; lean_object* v_r_860_; 
v_res_859_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5(v_00_u03b2_856_, v_a_857_, v_x_858_);
lean_dec(v_x_858_);
lean_dec_ref(v_a_857_);
v_r_860_ = lean_box(v_res_859_);
return v_r_860_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6(lean_object* v_00_u03b2_861_, lean_object* v_data_862_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6___redArg(v_data_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__7(lean_object* v_00_u03b2_864_, lean_object* v_a_865_, lean_object* v_b_866_, lean_object* v_x_867_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__7___redArg(v_a_865_, v_b_866_, v_x_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6_spec__7(lean_object* v_00_u03b2_869_, lean_object* v_i_870_, lean_object* v_source_871_, lean_object* v_target_872_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6_spec__7___redArg(v_i_870_, v_source_871_, v_target_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6_spec__7_spec__8(lean_object* v_00_u03b2_874_, lean_object* v_x_875_, lean_object* v_x_876_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6_spec__7_spec__8___redArg(v_x_875_, v_x_876_);
return v___x_877_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1___closed__0(void){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1(lean_object* v_msg_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
lean_object* v___x_887_; lean_object* v___x_2263__overap_888_; lean_object* v___x_889_; 
v___x_887_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1___closed__0);
v___x_2263__overap_888_ = lean_panic_fn_borrowed(v___x_887_, v_msg_879_);
lean_inc(v___y_885_);
lean_inc_ref(v___y_884_);
lean_inc(v___y_883_);
lean_inc_ref(v___y_882_);
lean_inc(v___y_881_);
lean_inc_ref(v___y_880_);
v___x_889_ = lean_apply_7(v___x_2263__overap_888_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, lean_box(0));
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1___boxed(lean_object* v_msg_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1(v_msg_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__2(lean_object* v_x_899_, uint8_t v_bi_900_, lean_object* v_t_901_, lean_object* v_b_902_, lean_object* v___y_903_, uint8_t v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v___y_908_; lean_object* v___y_909_; 
if (v___y_904_ == 0)
{
v___y_908_ = v___y_903_;
v___y_909_ = v___y_906_;
goto v___jp_907_;
}
else
{
lean_object* v___x_931_; 
v___x_931_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_901_, v___y_904_, v___y_905_, v___y_906_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v_a_932_; lean_object* v___x_933_; 
v_a_932_ = lean_ctor_get(v___x_931_, 1);
lean_inc(v_a_932_);
lean_dec_ref_known(v___x_931_, 2);
v___x_933_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_902_, v___y_904_, v___y_905_, v_a_932_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v_a_934_; 
v_a_934_ = lean_ctor_get(v___x_933_, 1);
lean_inc(v_a_934_);
lean_dec_ref_known(v___x_933_, 2);
v___y_908_ = v___y_903_;
v___y_909_ = v_a_934_;
goto v___jp_907_;
}
else
{
lean_object* v_a_935_; lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_943_; 
lean_dec_ref(v___y_903_);
lean_dec_ref(v_b_902_);
lean_dec_ref(v_t_901_);
lean_dec(v_x_899_);
v_a_935_ = lean_ctor_get(v___x_933_, 0);
v_a_936_ = lean_ctor_get(v___x_933_, 1);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_943_ == 0)
{
v___x_938_ = v___x_933_;
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_inc(v_a_935_);
lean_dec(v___x_933_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_941_; 
if (v_isShared_939_ == 0)
{
v___x_941_ = v___x_938_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_a_935_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v_a_936_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
}
else
{
lean_object* v_a_944_; lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_952_; 
lean_dec_ref(v___y_903_);
lean_dec_ref(v_b_902_);
lean_dec_ref(v_t_901_);
lean_dec(v_x_899_);
v_a_944_ = lean_ctor_get(v___x_931_, 0);
v_a_945_ = lean_ctor_get(v___x_931_, 1);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_952_ == 0)
{
v___x_947_ = v___x_931_;
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_inc(v_a_944_);
lean_dec(v___x_931_);
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
v___jp_907_:
{
lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_910_ = l_Lean_Expr_lam___override(v_x_899_, v_t_901_, v_b_902_, v_bi_900_);
v___x_911_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_910_, v___y_909_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_921_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
v_a_913_ = lean_ctor_get(v___x_911_, 1);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_921_ == 0)
{
v___x_915_ = v___x_911_;
v_isShared_916_ = v_isSharedCheck_921_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_inc(v_a_912_);
lean_dec(v___x_911_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_921_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_917_; lean_object* v___x_919_; 
v___x_917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_917_, 0, v_a_912_);
lean_ctor_set(v___x_917_, 1, v___y_908_);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 0, v___x_917_);
v___x_919_ = v___x_915_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_917_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v_a_913_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
else
{
lean_object* v_a_922_; lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
lean_dec_ref(v___y_908_);
v_a_922_ = lean_ctor_get(v___x_911_, 0);
v_a_923_ = lean_ctor_get(v___x_911_, 1);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_930_ == 0)
{
v___x_925_ = v___x_911_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_inc(v_a_922_);
lean_dec(v___x_911_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_922_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v_a_923_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__2___boxed(lean_object* v_x_953_, lean_object* v_bi_954_, lean_object* v_t_955_, lean_object* v_b_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
uint8_t v_bi_boxed_961_; uint8_t v___y_25260__boxed_962_; lean_object* v_res_963_; 
v_bi_boxed_961_ = lean_unbox(v_bi_954_);
v___y_25260__boxed_962_ = lean_unbox(v___y_958_);
v_res_963_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__2(v_x_953_, v_bi_boxed_961_, v_t_955_, v_b_956_, v___y_957_, v___y_25260__boxed_962_, v___y_959_, v___y_960_);
lean_dec_ref(v___y_959_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__6(lean_object* v_structName_964_, lean_object* v_idx_965_, lean_object* v_struct_966_, lean_object* v___y_967_, uint8_t v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v___y_972_; lean_object* v___y_973_; 
if (v___y_968_ == 0)
{
v___y_972_ = v___y_967_;
v___y_973_ = v___y_970_;
goto v___jp_971_;
}
else
{
lean_object* v___x_995_; 
v___x_995_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_struct_966_, v___y_968_, v___y_969_, v___y_970_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_object* v_a_996_; 
v_a_996_ = lean_ctor_get(v___x_995_, 1);
lean_inc(v_a_996_);
lean_dec_ref_known(v___x_995_, 2);
v___y_972_ = v___y_967_;
v___y_973_ = v_a_996_;
goto v___jp_971_;
}
else
{
lean_object* v_a_997_; lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1005_; 
lean_dec_ref(v___y_967_);
lean_dec_ref(v_struct_966_);
lean_dec(v_idx_965_);
lean_dec(v_structName_964_);
v_a_997_ = lean_ctor_get(v___x_995_, 0);
v_a_998_ = lean_ctor_get(v___x_995_, 1);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_1000_ = v___x_995_;
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_inc(v_a_997_);
lean_dec(v___x_995_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1003_; 
if (v_isShared_1001_ == 0)
{
v___x_1003_ = v___x_1000_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_a_997_);
lean_ctor_set(v_reuseFailAlloc_1004_, 1, v_a_998_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
v___jp_971_:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = l_Lean_Expr_proj___override(v_structName_964_, v_idx_965_, v_struct_966_);
v___x_975_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_974_, v___y_973_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_985_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
v_a_977_ = lean_ctor_get(v___x_975_, 1);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_985_ == 0)
{
v___x_979_ = v___x_975_;
v_isShared_980_ = v_isSharedCheck_985_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_inc(v_a_976_);
lean_dec(v___x_975_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_985_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_981_; lean_object* v___x_983_; 
v___x_981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_981_, 0, v_a_976_);
lean_ctor_set(v___x_981_, 1, v___y_972_);
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 0, v___x_981_);
v___x_983_ = v___x_979_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_981_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v_a_977_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
else
{
lean_object* v_a_986_; lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_994_; 
lean_dec_ref(v___y_972_);
v_a_986_ = lean_ctor_get(v___x_975_, 0);
v_a_987_ = lean_ctor_get(v___x_975_, 1);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_994_ == 0)
{
v___x_989_ = v___x_975_;
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_inc(v_a_986_);
lean_dec(v___x_975_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_992_; 
if (v_isShared_990_ == 0)
{
v___x_992_ = v___x_989_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_a_986_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_a_987_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__6___boxed(lean_object* v_structName_1006_, lean_object* v_idx_1007_, lean_object* v_struct_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
uint8_t v___y_25366__boxed_1013_; lean_object* v_res_1014_; 
v___y_25366__boxed_1013_ = lean_unbox(v___y_1010_);
v_res_1014_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__6(v_structName_1006_, v_idx_1007_, v_struct_1008_, v___y_1009_, v___y_25366__boxed_1013_, v___y_1011_, v___y_1012_);
lean_dec_ref(v___y_1011_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__1(lean_object* v_f_1015_, lean_object* v_a_1016_, lean_object* v___y_1017_, uint8_t v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v___y_1022_; lean_object* v___y_1023_; 
if (v___y_1018_ == 0)
{
v___y_1022_ = v___y_1017_;
v___y_1023_ = v___y_1020_;
goto v___jp_1021_;
}
else
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_1015_, v___y_1018_, v___y_1019_, v___y_1020_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_a_1046_; lean_object* v___x_1047_; 
v_a_1046_ = lean_ctor_get(v___x_1045_, 1);
lean_inc(v_a_1046_);
lean_dec_ref_known(v___x_1045_, 2);
v___x_1047_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_1016_, v___y_1018_, v___y_1019_, v_a_1046_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v_a_1048_; 
v_a_1048_ = lean_ctor_get(v___x_1047_, 1);
lean_inc(v_a_1048_);
lean_dec_ref_known(v___x_1047_, 2);
v___y_1022_ = v___y_1017_;
v___y_1023_ = v_a_1048_;
goto v___jp_1021_;
}
else
{
lean_object* v_a_1049_; lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
lean_dec_ref(v___y_1017_);
lean_dec_ref(v_a_1016_);
lean_dec_ref(v_f_1015_);
v_a_1049_ = lean_ctor_get(v___x_1047_, 0);
v_a_1050_ = lean_ctor_get(v___x_1047_, 1);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1052_ = v___x_1047_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_inc(v_a_1049_);
lean_dec(v___x_1047_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1049_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v_a_1050_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
else
{
lean_object* v_a_1058_; lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1066_; 
lean_dec_ref(v___y_1017_);
lean_dec_ref(v_a_1016_);
lean_dec_ref(v_f_1015_);
v_a_1058_ = lean_ctor_get(v___x_1045_, 0);
v_a_1059_ = lean_ctor_get(v___x_1045_, 1);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1061_ = v___x_1045_;
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_inc(v_a_1058_);
lean_dec(v___x_1045_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1064_; 
if (v_isShared_1062_ == 0)
{
v___x_1064_ = v___x_1061_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_a_1058_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v_a_1059_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
}
v___jp_1021_:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = l_Lean_Expr_app___override(v_f_1015_, v_a_1016_);
v___x_1025_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1024_, v___y_1023_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1035_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
v_a_1027_ = lean_ctor_get(v___x_1025_, 1);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1029_ = v___x_1025_;
v_isShared_1030_ = v_isSharedCheck_1035_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_inc(v_a_1026_);
lean_dec(v___x_1025_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1035_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1031_; lean_object* v___x_1033_; 
v___x_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1031_, 0, v_a_1026_);
lean_ctor_set(v___x_1031_, 1, v___y_1022_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 0, v___x_1031_);
v___x_1033_ = v___x_1029_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1031_);
lean_ctor_set(v_reuseFailAlloc_1034_, 1, v_a_1027_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
else
{
lean_object* v_a_1036_; lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
lean_dec_ref(v___y_1022_);
v_a_1036_ = lean_ctor_get(v___x_1025_, 0);
v_a_1037_ = lean_ctor_get(v___x_1025_, 1);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1039_ = v___x_1025_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_inc(v_a_1036_);
lean_dec(v___x_1025_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
if (v_isShared_1040_ == 0)
{
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_a_1036_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v_a_1037_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__1___boxed(lean_object* v_f_1067_, lean_object* v_a_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
uint8_t v___y_25449__boxed_1073_; lean_object* v_res_1074_; 
v___y_25449__boxed_1073_ = lean_unbox(v___y_1070_);
v_res_1074_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__1(v_f_1067_, v_a_1068_, v___y_1069_, v___y_25449__boxed_1073_, v___y_1071_, v___y_1072_);
lean_dec_ref(v___y_1071_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4(lean_object* v_x_1075_, lean_object* v_t_1076_, lean_object* v_v_1077_, lean_object* v_b_1078_, uint8_t v_nondep_1079_, lean_object* v___y_1080_, uint8_t v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v___y_1085_; lean_object* v___y_1086_; 
if (v___y_1081_ == 0)
{
v___y_1085_ = v___y_1080_;
v___y_1086_ = v___y_1083_;
goto v___jp_1084_;
}
else
{
lean_object* v___x_1108_; 
v___x_1108_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_1076_, v___y_1081_, v___y_1082_, v___y_1083_);
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_object* v_a_1109_; lean_object* v___x_1110_; 
v_a_1109_ = lean_ctor_get(v___x_1108_, 1);
lean_inc(v_a_1109_);
lean_dec_ref_known(v___x_1108_, 2);
v___x_1110_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_v_1077_, v___y_1081_, v___y_1082_, v_a_1109_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_a_1111_; lean_object* v___x_1112_; 
v_a_1111_ = lean_ctor_get(v___x_1110_, 1);
lean_inc(v_a_1111_);
lean_dec_ref_known(v___x_1110_, 2);
v___x_1112_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_1078_, v___y_1081_, v___y_1082_, v_a_1111_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; 
v_a_1113_ = lean_ctor_get(v___x_1112_, 1);
lean_inc(v_a_1113_);
lean_dec_ref_known(v___x_1112_, 2);
v___y_1085_ = v___y_1080_;
v___y_1086_ = v_a_1113_;
goto v___jp_1084_;
}
else
{
lean_object* v_a_1114_; lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1122_; 
lean_dec_ref(v___y_1080_);
lean_dec_ref(v_b_1078_);
lean_dec_ref(v_v_1077_);
lean_dec_ref(v_t_1076_);
lean_dec(v_x_1075_);
v_a_1114_ = lean_ctor_get(v___x_1112_, 0);
v_a_1115_ = lean_ctor_get(v___x_1112_, 1);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1117_ = v___x_1112_;
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_inc(v_a_1114_);
lean_dec(v___x_1112_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
v___x_1120_ = v___x_1117_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1114_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v_a_1115_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
else
{
lean_object* v_a_1123_; lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1131_; 
lean_dec_ref(v___y_1080_);
lean_dec_ref(v_b_1078_);
lean_dec_ref(v_v_1077_);
lean_dec_ref(v_t_1076_);
lean_dec(v_x_1075_);
v_a_1123_ = lean_ctor_get(v___x_1110_, 0);
v_a_1124_ = lean_ctor_get(v___x_1110_, 1);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1126_ = v___x_1110_;
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_inc(v_a_1123_);
lean_dec(v___x_1110_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1129_; 
if (v_isShared_1127_ == 0)
{
v___x_1129_ = v___x_1126_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_a_1123_);
lean_ctor_set(v_reuseFailAlloc_1130_, 1, v_a_1124_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
}
else
{
lean_object* v_a_1132_; lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
lean_dec_ref(v___y_1080_);
lean_dec_ref(v_b_1078_);
lean_dec_ref(v_v_1077_);
lean_dec_ref(v_t_1076_);
lean_dec(v_x_1075_);
v_a_1132_ = lean_ctor_get(v___x_1108_, 0);
v_a_1133_ = lean_ctor_get(v___x_1108_, 1);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_1108_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_inc(v_a_1132_);
lean_dec(v___x_1108_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1132_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v_a_1133_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
v___jp_1084_:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = l_Lean_Expr_letE___override(v_x_1075_, v_t_1076_, v_v_1077_, v_b_1078_, v_nondep_1079_);
v___x_1088_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1087_, v___y_1086_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v_a_1089_; lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1098_; 
v_a_1089_ = lean_ctor_get(v___x_1088_, 0);
v_a_1090_ = lean_ctor_get(v___x_1088_, 1);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1092_ = v___x_1088_;
v_isShared_1093_ = v_isSharedCheck_1098_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_inc(v_a_1089_);
lean_dec(v___x_1088_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1098_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1094_; lean_object* v___x_1096_; 
v___x_1094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1094_, 0, v_a_1089_);
lean_ctor_set(v___x_1094_, 1, v___y_1085_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v___x_1094_);
v___x_1096_ = v___x_1092_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1094_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v_a_1090_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
else
{
lean_object* v_a_1099_; lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
lean_dec_ref(v___y_1085_);
v_a_1099_ = lean_ctor_get(v___x_1088_, 0);
v_a_1100_ = lean_ctor_get(v___x_1088_, 1);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1088_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_inc(v_a_1099_);
lean_dec(v___x_1088_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1099_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4___boxed(lean_object* v_x_1141_, lean_object* v_t_1142_, lean_object* v_v_1143_, lean_object* v_b_1144_, lean_object* v_nondep_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
uint8_t v_nondep_boxed_1150_; uint8_t v___y_25555__boxed_1151_; lean_object* v_res_1152_; 
v_nondep_boxed_1150_ = lean_unbox(v_nondep_1145_);
v___y_25555__boxed_1151_ = lean_unbox(v___y_1147_);
v_res_1152_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4(v_x_1141_, v_t_1142_, v_v_1143_, v_b_1144_, v_nondep_boxed_1150_, v___y_1146_, v___y_25555__boxed_1151_, v___y_1148_, v___y_1149_);
lean_dec_ref(v___y_1148_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7(lean_object* v_msg_1160_, lean_object* v___y_1161_, uint8_t v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v___f_1165_; lean_object* v___f_1166_; lean_object* v___f_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___f_1177_; lean_object* v___f_1178_; lean_object* v___f_1179_; lean_object* v___f_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_24789__overap_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___f_1165_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__0));
v___f_1166_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__1));
v___f_1167_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__2));
v___x_1168_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__3));
v___x_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1168_);
lean_ctor_set(v___x_1169_, 1, v___f_1165_);
v___x_1170_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__4));
v___x_1171_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__5));
v___x_1172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1169_);
lean_ctor_set(v___x_1172_, 1, v___x_1170_);
lean_ctor_set(v___x_1172_, 2, v___f_1166_);
lean_ctor_set(v___x_1172_, 3, v___f_1167_);
lean_ctor_set(v___x_1172_, 4, v___x_1171_);
v___x_1173_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__6));
v___x_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1172_);
lean_ctor_set(v___x_1174_, 1, v___x_1173_);
v___x_1175_ = l_ReaderT_instMonad___redArg(v___x_1174_);
v___x_1176_ = l_ReaderT_instMonad___redArg(v___x_1175_);
lean_inc_ref_n(v___x_1176_, 6);
v___f_1177_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1177_, 0, v___x_1176_);
v___f_1178_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1178_, 0, v___x_1176_);
v___f_1179_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_1179_, 0, v___x_1176_);
v___f_1180_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_1180_, 0, v___x_1176_);
v___x_1181_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_1181_, 0, lean_box(0));
lean_closure_set(v___x_1181_, 1, lean_box(0));
lean_closure_set(v___x_1181_, 2, v___x_1176_);
v___x_1182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1181_);
lean_ctor_set(v___x_1182_, 1, v___f_1177_);
v___x_1183_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_1183_, 0, lean_box(0));
lean_closure_set(v___x_1183_, 1, lean_box(0));
lean_closure_set(v___x_1183_, 2, v___x_1176_);
v___x_1184_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1182_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
lean_ctor_set(v___x_1184_, 2, v___f_1178_);
lean_ctor_set(v___x_1184_, 3, v___f_1179_);
lean_ctor_set(v___x_1184_, 4, v___f_1180_);
v___x_1185_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_1185_, 0, lean_box(0));
lean_closure_set(v___x_1185_, 1, lean_box(0));
lean_closure_set(v___x_1185_, 2, v___x_1176_);
v___x_1186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1184_);
lean_ctor_set(v___x_1186_, 1, v___x_1185_);
v___x_1187_ = l_Lean_instInhabitedExpr;
v___x_1188_ = l_instInhabitedOfMonad___redArg(v___x_1186_, v___x_1187_);
v___x_24789__overap_1189_ = lean_panic_fn_borrowed(v___x_1188_, v_msg_1160_);
lean_dec(v___x_1188_);
v___x_1190_ = lean_box(v___y_1162_);
lean_inc_ref(v___y_1163_);
v___x_1191_ = lean_apply_4(v___x_24789__overap_1189_, v___y_1161_, v___x_1190_, v___y_1163_, v___y_1164_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___boxed(lean_object* v_msg_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
uint8_t v___y_25698__boxed_1197_; lean_object* v_res_1198_; 
v___y_25698__boxed_1197_ = lean_unbox(v___y_1194_);
v_res_1198_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7(v_msg_1192_, v___y_1193_, v___y_25698__boxed_1197_, v___y_1195_, v___y_1196_);
lean_dec_ref(v___y_1195_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__5(lean_object* v_d_1199_, lean_object* v_e_1200_, lean_object* v___y_1201_, uint8_t v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
lean_object* v___y_1206_; lean_object* v___y_1207_; 
if (v___y_1202_ == 0)
{
v___y_1206_ = v___y_1201_;
v___y_1207_ = v___y_1204_;
goto v___jp_1205_;
}
else
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_1200_, v___y_1202_, v___y_1203_, v___y_1204_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v_a_1230_; 
v_a_1230_ = lean_ctor_get(v___x_1229_, 1);
lean_inc(v_a_1230_);
lean_dec_ref_known(v___x_1229_, 2);
v___y_1206_ = v___y_1201_;
v___y_1207_ = v_a_1230_;
goto v___jp_1205_;
}
else
{
lean_object* v_a_1231_; lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1239_; 
lean_dec_ref(v___y_1201_);
lean_dec_ref(v_e_1200_);
lean_dec(v_d_1199_);
v_a_1231_ = lean_ctor_get(v___x_1229_, 0);
v_a_1232_ = lean_ctor_get(v___x_1229_, 1);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1234_ = v___x_1229_;
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_inc(v_a_1231_);
lean_dec(v___x_1229_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1237_; 
if (v_isShared_1235_ == 0)
{
v___x_1237_ = v___x_1234_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_a_1231_);
lean_ctor_set(v_reuseFailAlloc_1238_, 1, v_a_1232_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
}
v___jp_1205_:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = l_Lean_Expr_mdata___override(v_d_1199_, v_e_1200_);
v___x_1209_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1208_, v___y_1207_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v_a_1210_; lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1219_; 
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
v_a_1211_ = lean_ctor_get(v___x_1209_, 1);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1213_ = v___x_1209_;
v_isShared_1214_ = v_isSharedCheck_1219_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_inc(v_a_1210_);
lean_dec(v___x_1209_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1219_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1215_; lean_object* v___x_1217_; 
v___x_1215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1215_, 0, v_a_1210_);
lean_ctor_set(v___x_1215_, 1, v___y_1206_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 0, v___x_1215_);
v___x_1217_ = v___x_1213_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1215_);
lean_ctor_set(v_reuseFailAlloc_1218_, 1, v_a_1211_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
else
{
lean_object* v_a_1220_; lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
lean_dec_ref(v___y_1206_);
v_a_1220_ = lean_ctor_get(v___x_1209_, 0);
v_a_1221_ = lean_ctor_get(v___x_1209_, 1);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1223_ = v___x_1209_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_inc(v_a_1220_);
lean_dec(v___x_1209_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_a_1220_);
lean_ctor_set(v_reuseFailAlloc_1227_, 1, v_a_1221_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__5___boxed(lean_object* v_d_1240_, lean_object* v_e_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
uint8_t v___y_25769__boxed_1246_; lean_object* v_res_1247_; 
v___y_25769__boxed_1246_ = lean_unbox(v___y_1243_);
v_res_1247_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__5(v_d_1240_, v_e_1241_, v___y_1242_, v___y_25769__boxed_1246_, v___y_1244_, v___y_1245_);
lean_dec_ref(v___y_1244_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__3(lean_object* v_x_1248_, uint8_t v_bi_1249_, lean_object* v_t_1250_, lean_object* v_b_1251_, lean_object* v___y_1252_, uint8_t v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
lean_object* v___y_1257_; lean_object* v___y_1258_; 
if (v___y_1253_ == 0)
{
v___y_1257_ = v___y_1252_;
v___y_1258_ = v___y_1255_;
goto v___jp_1256_;
}
else
{
lean_object* v___x_1280_; 
v___x_1280_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_1250_, v___y_1253_, v___y_1254_, v___y_1255_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; lean_object* v___x_1282_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 1);
lean_inc(v_a_1281_);
lean_dec_ref_known(v___x_1280_, 2);
v___x_1282_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_1251_, v___y_1253_, v___y_1254_, v_a_1281_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 1);
lean_inc(v_a_1283_);
lean_dec_ref_known(v___x_1282_, 2);
v___y_1257_ = v___y_1252_;
v___y_1258_ = v_a_1283_;
goto v___jp_1256_;
}
else
{
lean_object* v_a_1284_; lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
lean_dec_ref(v___y_1252_);
lean_dec_ref(v_b_1251_);
lean_dec_ref(v_t_1250_);
lean_dec(v_x_1248_);
v_a_1284_ = lean_ctor_get(v___x_1282_, 0);
v_a_1285_ = lean_ctor_get(v___x_1282_, 1);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1282_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_inc(v_a_1284_);
lean_dec(v___x_1282_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1284_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
else
{
lean_object* v_a_1293_; lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
lean_dec_ref(v___y_1252_);
lean_dec_ref(v_b_1251_);
lean_dec_ref(v_t_1250_);
lean_dec(v_x_1248_);
v_a_1293_ = lean_ctor_get(v___x_1280_, 0);
v_a_1294_ = lean_ctor_get(v___x_1280_, 1);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1280_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_inc(v_a_1293_);
lean_dec(v___x_1280_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1293_);
lean_ctor_set(v_reuseFailAlloc_1300_, 1, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
v___jp_1256_:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = l_Lean_Expr_forallE___override(v_x_1248_, v_t_1250_, v_b_1251_, v_bi_1249_);
v___x_1260_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1259_, v___y_1258_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1270_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
v_a_1262_ = lean_ctor_get(v___x_1260_, 1);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1264_ = v___x_1260_;
v_isShared_1265_ = v_isSharedCheck_1270_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_inc(v_a_1261_);
lean_dec(v___x_1260_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1270_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1266_; lean_object* v___x_1268_; 
v___x_1266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1266_, 0, v_a_1261_);
lean_ctor_set(v___x_1266_, 1, v___y_1257_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 0, v___x_1266_);
v___x_1268_ = v___x_1264_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v___x_1266_);
lean_ctor_set(v_reuseFailAlloc_1269_, 1, v_a_1262_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
else
{
lean_object* v_a_1271_; lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1279_; 
lean_dec_ref(v___y_1257_);
v_a_1271_ = lean_ctor_get(v___x_1260_, 0);
v_a_1272_ = lean_ctor_get(v___x_1260_, 1);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1274_ = v___x_1260_;
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_inc(v_a_1271_);
lean_dec(v___x_1260_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1275_ == 0)
{
v___x_1277_ = v___x_1274_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_a_1271_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v_a_1272_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__3___boxed(lean_object* v_x_1302_, lean_object* v_bi_1303_, lean_object* v_t_1304_, lean_object* v_b_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
uint8_t v_bi_boxed_1310_; uint8_t v___y_25852__boxed_1311_; lean_object* v_res_1312_; 
v_bi_boxed_1310_ = lean_unbox(v_bi_1303_);
v___y_25852__boxed_1311_ = lean_unbox(v___y_1307_);
v_res_1312_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__3(v_x_1302_, v_bi_boxed_1310_, v_t_1304_, v_b_1305_, v___y_1306_, v___y_25852__boxed_1311_, v___y_1308_, v___y_1309_);
lean_dec_ref(v___y_1308_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10___redArg(lean_object* v_a_1313_, lean_object* v_x_1314_){
_start:
{
if (lean_obj_tag(v_x_1314_) == 0)
{
lean_object* v___x_1315_; 
v___x_1315_ = lean_box(0);
return v___x_1315_;
}
else
{
lean_object* v_key_1316_; lean_object* v_value_1317_; lean_object* v_tail_1318_; lean_object* v_fst_1319_; lean_object* v_snd_1320_; lean_object* v_fst_1321_; lean_object* v_snd_1322_; size_t v___x_1323_; size_t v___x_1324_; uint8_t v___x_1325_; 
v_key_1316_ = lean_ctor_get(v_x_1314_, 0);
v_value_1317_ = lean_ctor_get(v_x_1314_, 1);
v_tail_1318_ = lean_ctor_get(v_x_1314_, 2);
v_fst_1319_ = lean_ctor_get(v_key_1316_, 0);
v_snd_1320_ = lean_ctor_get(v_key_1316_, 1);
v_fst_1321_ = lean_ctor_get(v_a_1313_, 0);
v_snd_1322_ = lean_ctor_get(v_a_1313_, 1);
v___x_1323_ = lean_ptr_addr(v_fst_1319_);
v___x_1324_ = lean_ptr_addr(v_fst_1321_);
v___x_1325_ = lean_usize_dec_eq(v___x_1323_, v___x_1324_);
if (v___x_1325_ == 0)
{
v_x_1314_ = v_tail_1318_;
goto _start;
}
else
{
uint8_t v___x_1327_; 
v___x_1327_ = lean_nat_dec_eq(v_snd_1320_, v_snd_1322_);
if (v___x_1327_ == 0)
{
v_x_1314_ = v_tail_1318_;
goto _start;
}
else
{
lean_object* v___x_1329_; 
lean_inc(v_value_1317_);
v___x_1329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1329_, 0, v_value_1317_);
return v___x_1329_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10___redArg___boxed(lean_object* v_a_1330_, lean_object* v_x_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10___redArg(v_a_1330_, v_x_1331_);
lean_dec(v_x_1331_);
lean_dec_ref(v_a_1330_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2___redArg(lean_object* v_m_1333_, lean_object* v_a_1334_){
_start:
{
lean_object* v_buckets_1335_; lean_object* v_fst_1336_; lean_object* v_snd_1337_; lean_object* v___x_1338_; size_t v___x_1339_; size_t v___x_1340_; size_t v___x_1341_; uint64_t v___x_1342_; uint64_t v___x_1343_; uint64_t v___x_1344_; uint64_t v___x_1345_; uint64_t v___x_1346_; uint64_t v_fold_1347_; uint64_t v___x_1348_; uint64_t v___x_1349_; uint64_t v___x_1350_; size_t v___x_1351_; size_t v___x_1352_; size_t v___x_1353_; size_t v___x_1354_; size_t v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v_buckets_1335_ = lean_ctor_get(v_m_1333_, 1);
v_fst_1336_ = lean_ctor_get(v_a_1334_, 0);
v_snd_1337_ = lean_ctor_get(v_a_1334_, 1);
v___x_1338_ = lean_array_get_size(v_buckets_1335_);
v___x_1339_ = lean_ptr_addr(v_fst_1336_);
v___x_1340_ = ((size_t)3ULL);
v___x_1341_ = lean_usize_shift_right(v___x_1339_, v___x_1340_);
v___x_1342_ = lean_usize_to_uint64(v___x_1341_);
v___x_1343_ = lean_uint64_of_nat(v_snd_1337_);
v___x_1344_ = lean_uint64_mix_hash(v___x_1342_, v___x_1343_);
v___x_1345_ = 32ULL;
v___x_1346_ = lean_uint64_shift_right(v___x_1344_, v___x_1345_);
v_fold_1347_ = lean_uint64_xor(v___x_1344_, v___x_1346_);
v___x_1348_ = 16ULL;
v___x_1349_ = lean_uint64_shift_right(v_fold_1347_, v___x_1348_);
v___x_1350_ = lean_uint64_xor(v_fold_1347_, v___x_1349_);
v___x_1351_ = lean_uint64_to_usize(v___x_1350_);
v___x_1352_ = lean_usize_of_nat(v___x_1338_);
v___x_1353_ = ((size_t)1ULL);
v___x_1354_ = lean_usize_sub(v___x_1352_, v___x_1353_);
v___x_1355_ = lean_usize_land(v___x_1351_, v___x_1354_);
v___x_1356_ = lean_array_uget_borrowed(v_buckets_1335_, v___x_1355_);
v___x_1357_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10___redArg(v_a_1334_, v___x_1356_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_m_1358_, lean_object* v_a_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2___redArg(v_m_1358_, v_a_1359_);
lean_dec_ref(v_a_1359_);
lean_dec_ref(v_m_1358_);
return v_res_1360_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1364_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__2));
v___x_1365_ = lean_unsigned_to_nat(67u);
v___x_1366_ = lean_unsigned_to_nat(35u);
v___x_1367_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__1));
v___x_1368_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__0));
v___x_1369_ = l_mkPanicMessageWithDecl(v___x_1368_, v___x_1367_, v___x_1366_, v___x_1365_, v___x_1364_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0(lean_object* v_n_1370_, lean_object* v_xs_1371_, lean_object* v_e_1372_, lean_object* v_offset_1373_, lean_object* v_a_1374_, uint8_t v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_){
_start:
{
switch(lean_obj_tag(v_e_1372_))
{
case 5:
{
lean_object* v_fn_1378_; lean_object* v_arg_1379_; lean_object* v___x_1380_; 
v_fn_1378_ = lean_ctor_get(v_e_1372_, 0);
v_arg_1379_ = lean_ctor_get(v_e_1372_, 1);
lean_inc(v_offset_1373_);
lean_inc_ref(v_fn_1378_);
v___x_1380_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1370_, v_xs_1371_, v_fn_1378_, v_offset_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v_a_1381_; lean_object* v_a_1382_; lean_object* v_fst_1383_; lean_object* v_snd_1384_; lean_object* v___x_1385_; 
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
lean_inc(v_a_1381_);
v_a_1382_ = lean_ctor_get(v___x_1380_, 1);
lean_inc(v_a_1382_);
lean_dec_ref_known(v___x_1380_, 2);
v_fst_1383_ = lean_ctor_get(v_a_1381_, 0);
lean_inc(v_fst_1383_);
v_snd_1384_ = lean_ctor_get(v_a_1381_, 1);
lean_inc(v_snd_1384_);
lean_dec(v_a_1381_);
lean_inc_ref(v_arg_1379_);
v___x_1385_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1370_, v_xs_1371_, v_arg_1379_, v_offset_1373_, v_snd_1384_, v_a_1375_, v_a_1376_, v_a_1382_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v_a_1386_; lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1411_; 
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
v_a_1387_ = lean_ctor_get(v___x_1385_, 1);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1389_ = v___x_1385_;
v_isShared_1390_ = v_isSharedCheck_1411_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_inc(v_a_1386_);
lean_dec(v___x_1385_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1411_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v_fst_1391_; lean_object* v_snd_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1410_; 
v_fst_1391_ = lean_ctor_get(v_a_1386_, 0);
v_snd_1392_ = lean_ctor_get(v_a_1386_, 1);
v_isSharedCheck_1410_ = !lean_is_exclusive(v_a_1386_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1394_ = v_a_1386_;
v_isShared_1395_ = v_isSharedCheck_1410_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_snd_1392_);
lean_inc(v_fst_1391_);
lean_dec(v_a_1386_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1410_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
size_t v___x_1396_; size_t v___x_1397_; uint8_t v___x_1398_; 
v___x_1396_ = lean_ptr_addr(v_fn_1378_);
v___x_1397_ = lean_ptr_addr(v_fst_1383_);
v___x_1398_ = lean_usize_dec_eq(v___x_1396_, v___x_1397_);
if (v___x_1398_ == 0)
{
lean_object* v___x_1399_; 
lean_del_object(v___x_1394_);
lean_del_object(v___x_1389_);
lean_dec_ref_known(v_e_1372_, 2);
v___x_1399_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__1(v_fst_1383_, v_fst_1391_, v_snd_1392_, v_a_1375_, v_a_1376_, v_a_1387_);
return v___x_1399_;
}
else
{
size_t v___x_1400_; size_t v___x_1401_; uint8_t v___x_1402_; 
v___x_1400_ = lean_ptr_addr(v_arg_1379_);
v___x_1401_ = lean_ptr_addr(v_fst_1391_);
v___x_1402_ = lean_usize_dec_eq(v___x_1400_, v___x_1401_);
if (v___x_1402_ == 0)
{
lean_object* v___x_1403_; 
lean_del_object(v___x_1394_);
lean_del_object(v___x_1389_);
lean_dec_ref_known(v_e_1372_, 2);
v___x_1403_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__1(v_fst_1383_, v_fst_1391_, v_snd_1392_, v_a_1375_, v_a_1376_, v_a_1387_);
return v___x_1403_;
}
else
{
lean_object* v___x_1405_; 
lean_dec(v_fst_1391_);
lean_dec(v_fst_1383_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 0, v_e_1372_);
v___x_1405_ = v___x_1394_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_e_1372_);
lean_ctor_set(v_reuseFailAlloc_1409_, 1, v_snd_1392_);
v___x_1405_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
lean_object* v___x_1407_; 
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1405_);
v___x_1407_ = v___x_1389_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___x_1405_);
lean_ctor_set(v_reuseFailAlloc_1408_, 1, v_a_1387_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1383_);
lean_dec_ref_known(v_e_1372_, 2);
return v___x_1385_;
}
}
else
{
lean_dec_ref_known(v_e_1372_, 2);
lean_dec(v_offset_1373_);
return v___x_1380_;
}
}
case 6:
{
lean_object* v_binderName_1412_; lean_object* v_binderType_1413_; lean_object* v_body_1414_; uint8_t v_binderInfo_1415_; lean_object* v___x_1416_; 
v_binderName_1412_ = lean_ctor_get(v_e_1372_, 0);
v_binderType_1413_ = lean_ctor_get(v_e_1372_, 1);
v_body_1414_ = lean_ctor_get(v_e_1372_, 2);
v_binderInfo_1415_ = lean_ctor_get_uint8(v_e_1372_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1373_);
lean_inc_ref(v_binderType_1413_);
v___x_1416_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1370_, v_xs_1371_, v_binderType_1413_, v_offset_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v_a_1417_; lean_object* v_a_1418_; lean_object* v_fst_1419_; lean_object* v_snd_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
lean_inc(v_a_1417_);
v_a_1418_ = lean_ctor_get(v___x_1416_, 1);
lean_inc(v_a_1418_);
lean_dec_ref_known(v___x_1416_, 2);
v_fst_1419_ = lean_ctor_get(v_a_1417_, 0);
lean_inc(v_fst_1419_);
v_snd_1420_ = lean_ctor_get(v_a_1417_, 1);
lean_inc(v_snd_1420_);
lean_dec(v_a_1417_);
v___x_1421_ = lean_unsigned_to_nat(1u);
v___x_1422_ = lean_nat_add(v_offset_1373_, v___x_1421_);
lean_dec(v_offset_1373_);
lean_inc_ref(v_body_1414_);
v___x_1423_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1370_, v_xs_1371_, v_body_1414_, v___x_1422_, v_snd_1420_, v_a_1375_, v_a_1376_, v_a_1418_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_a_1424_; lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1449_; 
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
v_a_1425_ = lean_ctor_get(v___x_1423_, 1);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1427_ = v___x_1423_;
v_isShared_1428_ = v_isSharedCheck_1449_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_inc(v_a_1424_);
lean_dec(v___x_1423_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1449_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v_fst_1429_; lean_object* v_snd_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1448_; 
v_fst_1429_ = lean_ctor_get(v_a_1424_, 0);
v_snd_1430_ = lean_ctor_get(v_a_1424_, 1);
v_isSharedCheck_1448_ = !lean_is_exclusive(v_a_1424_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1432_ = v_a_1424_;
v_isShared_1433_ = v_isSharedCheck_1448_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_snd_1430_);
lean_inc(v_fst_1429_);
lean_dec(v_a_1424_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1448_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
size_t v___x_1434_; size_t v___x_1435_; uint8_t v___x_1436_; 
v___x_1434_ = lean_ptr_addr(v_binderType_1413_);
v___x_1435_ = lean_ptr_addr(v_fst_1419_);
v___x_1436_ = lean_usize_dec_eq(v___x_1434_, v___x_1435_);
if (v___x_1436_ == 0)
{
lean_object* v___x_1437_; 
lean_inc(v_binderName_1412_);
lean_del_object(v___x_1432_);
lean_del_object(v___x_1427_);
lean_dec_ref_known(v_e_1372_, 3);
v___x_1437_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__2(v_binderName_1412_, v_binderInfo_1415_, v_fst_1419_, v_fst_1429_, v_snd_1430_, v_a_1375_, v_a_1376_, v_a_1425_);
return v___x_1437_;
}
else
{
size_t v___x_1438_; size_t v___x_1439_; uint8_t v___x_1440_; 
v___x_1438_ = lean_ptr_addr(v_body_1414_);
v___x_1439_ = lean_ptr_addr(v_fst_1429_);
v___x_1440_ = lean_usize_dec_eq(v___x_1438_, v___x_1439_);
if (v___x_1440_ == 0)
{
lean_object* v___x_1441_; 
lean_inc(v_binderName_1412_);
lean_del_object(v___x_1432_);
lean_del_object(v___x_1427_);
lean_dec_ref_known(v_e_1372_, 3);
v___x_1441_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__2(v_binderName_1412_, v_binderInfo_1415_, v_fst_1419_, v_fst_1429_, v_snd_1430_, v_a_1375_, v_a_1376_, v_a_1425_);
return v___x_1441_;
}
else
{
lean_object* v___x_1443_; 
lean_dec(v_fst_1429_);
lean_dec(v_fst_1419_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 0, v_e_1372_);
v___x_1443_ = v___x_1432_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_e_1372_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v_snd_1430_);
v___x_1443_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
lean_object* v___x_1445_; 
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 0, v___x_1443_);
v___x_1445_ = v___x_1427_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1443_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v_a_1425_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1419_);
lean_dec_ref_known(v_e_1372_, 3);
return v___x_1423_;
}
}
else
{
lean_dec_ref_known(v_e_1372_, 3);
lean_dec(v_offset_1373_);
return v___x_1416_;
}
}
case 7:
{
lean_object* v_binderName_1450_; lean_object* v_binderType_1451_; lean_object* v_body_1452_; uint8_t v_binderInfo_1453_; lean_object* v___x_1454_; 
v_binderName_1450_ = lean_ctor_get(v_e_1372_, 0);
v_binderType_1451_ = lean_ctor_get(v_e_1372_, 1);
v_body_1452_ = lean_ctor_get(v_e_1372_, 2);
v_binderInfo_1453_ = lean_ctor_get_uint8(v_e_1372_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1373_);
lean_inc_ref(v_binderType_1451_);
v___x_1454_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1370_, v_xs_1371_, v_binderType_1451_, v_offset_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; lean_object* v_a_1456_; lean_object* v_fst_1457_; lean_object* v_snd_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_a_1455_);
v_a_1456_ = lean_ctor_get(v___x_1454_, 1);
lean_inc(v_a_1456_);
lean_dec_ref_known(v___x_1454_, 2);
v_fst_1457_ = lean_ctor_get(v_a_1455_, 0);
lean_inc(v_fst_1457_);
v_snd_1458_ = lean_ctor_get(v_a_1455_, 1);
lean_inc(v_snd_1458_);
lean_dec(v_a_1455_);
v___x_1459_ = lean_unsigned_to_nat(1u);
v___x_1460_ = lean_nat_add(v_offset_1373_, v___x_1459_);
lean_dec(v_offset_1373_);
lean_inc_ref(v_body_1452_);
v___x_1461_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1370_, v_xs_1371_, v_body_1452_, v___x_1460_, v_snd_1458_, v_a_1375_, v_a_1376_, v_a_1456_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v_a_1462_; lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1487_; 
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
v_a_1463_ = lean_ctor_get(v___x_1461_, 1);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1465_ = v___x_1461_;
v_isShared_1466_ = v_isSharedCheck_1487_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_inc(v_a_1462_);
lean_dec(v___x_1461_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1487_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v_fst_1467_; lean_object* v_snd_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1486_; 
v_fst_1467_ = lean_ctor_get(v_a_1462_, 0);
v_snd_1468_ = lean_ctor_get(v_a_1462_, 1);
v_isSharedCheck_1486_ = !lean_is_exclusive(v_a_1462_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1470_ = v_a_1462_;
v_isShared_1471_ = v_isSharedCheck_1486_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_snd_1468_);
lean_inc(v_fst_1467_);
lean_dec(v_a_1462_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1486_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
size_t v___x_1472_; size_t v___x_1473_; uint8_t v___x_1474_; 
v___x_1472_ = lean_ptr_addr(v_binderType_1451_);
v___x_1473_ = lean_ptr_addr(v_fst_1457_);
v___x_1474_ = lean_usize_dec_eq(v___x_1472_, v___x_1473_);
if (v___x_1474_ == 0)
{
lean_object* v___x_1475_; 
lean_inc(v_binderName_1450_);
lean_del_object(v___x_1470_);
lean_del_object(v___x_1465_);
lean_dec_ref_known(v_e_1372_, 3);
v___x_1475_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__3(v_binderName_1450_, v_binderInfo_1453_, v_fst_1457_, v_fst_1467_, v_snd_1468_, v_a_1375_, v_a_1376_, v_a_1463_);
return v___x_1475_;
}
else
{
size_t v___x_1476_; size_t v___x_1477_; uint8_t v___x_1478_; 
v___x_1476_ = lean_ptr_addr(v_body_1452_);
v___x_1477_ = lean_ptr_addr(v_fst_1467_);
v___x_1478_ = lean_usize_dec_eq(v___x_1476_, v___x_1477_);
if (v___x_1478_ == 0)
{
lean_object* v___x_1479_; 
lean_inc(v_binderName_1450_);
lean_del_object(v___x_1470_);
lean_del_object(v___x_1465_);
lean_dec_ref_known(v_e_1372_, 3);
v___x_1479_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__3(v_binderName_1450_, v_binderInfo_1453_, v_fst_1457_, v_fst_1467_, v_snd_1468_, v_a_1375_, v_a_1376_, v_a_1463_);
return v___x_1479_;
}
else
{
lean_object* v___x_1481_; 
lean_dec(v_fst_1467_);
lean_dec(v_fst_1457_);
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 0, v_e_1372_);
v___x_1481_ = v___x_1470_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_e_1372_);
lean_ctor_set(v_reuseFailAlloc_1485_, 1, v_snd_1468_);
v___x_1481_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
lean_object* v___x_1483_; 
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 0, v___x_1481_);
v___x_1483_ = v___x_1465_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v___x_1481_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v_a_1463_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1457_);
lean_dec_ref_known(v_e_1372_, 3);
return v___x_1461_;
}
}
else
{
lean_dec_ref_known(v_e_1372_, 3);
lean_dec(v_offset_1373_);
return v___x_1454_;
}
}
case 8:
{
lean_object* v_declName_1488_; lean_object* v_type_1489_; lean_object* v_value_1490_; lean_object* v_body_1491_; uint8_t v_nondep_1492_; lean_object* v___x_1493_; 
v_declName_1488_ = lean_ctor_get(v_e_1372_, 0);
v_type_1489_ = lean_ctor_get(v_e_1372_, 1);
v_value_1490_ = lean_ctor_get(v_e_1372_, 2);
v_body_1491_ = lean_ctor_get(v_e_1372_, 3);
v_nondep_1492_ = lean_ctor_get_uint8(v_e_1372_, sizeof(void*)*4 + 8);
lean_inc(v_offset_1373_);
lean_inc_ref(v_type_1489_);
v___x_1493_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1370_, v_xs_1371_, v_type_1489_, v_offset_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v_a_1494_; lean_object* v_a_1495_; lean_object* v_fst_1496_; lean_object* v_snd_1497_; lean_object* v___x_1498_; 
v_a_1494_ = lean_ctor_get(v___x_1493_, 0);
lean_inc(v_a_1494_);
v_a_1495_ = lean_ctor_get(v___x_1493_, 1);
lean_inc(v_a_1495_);
lean_dec_ref_known(v___x_1493_, 2);
v_fst_1496_ = lean_ctor_get(v_a_1494_, 0);
lean_inc(v_fst_1496_);
v_snd_1497_ = lean_ctor_get(v_a_1494_, 1);
lean_inc(v_snd_1497_);
lean_dec(v_a_1494_);
lean_inc(v_offset_1373_);
lean_inc_ref(v_value_1490_);
v___x_1498_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1370_, v_xs_1371_, v_value_1490_, v_offset_1373_, v_snd_1497_, v_a_1375_, v_a_1376_, v_a_1495_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_object* v_a_1499_; lean_object* v_a_1500_; lean_object* v_fst_1501_; lean_object* v_snd_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v_a_1499_ = lean_ctor_get(v___x_1498_, 0);
lean_inc(v_a_1499_);
v_a_1500_ = lean_ctor_get(v___x_1498_, 1);
lean_inc(v_a_1500_);
lean_dec_ref_known(v___x_1498_, 2);
v_fst_1501_ = lean_ctor_get(v_a_1499_, 0);
lean_inc(v_fst_1501_);
v_snd_1502_ = lean_ctor_get(v_a_1499_, 1);
lean_inc(v_snd_1502_);
lean_dec(v_a_1499_);
v___x_1503_ = lean_unsigned_to_nat(1u);
v___x_1504_ = lean_nat_add(v_offset_1373_, v___x_1503_);
lean_dec(v_offset_1373_);
lean_inc_ref(v_body_1491_);
v___x_1505_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1370_, v_xs_1371_, v_body_1491_, v___x_1504_, v_snd_1502_, v_a_1375_, v_a_1376_, v_a_1500_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v_a_1506_; lean_object* v_a_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1535_; 
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
v_a_1507_ = lean_ctor_get(v___x_1505_, 1);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1509_ = v___x_1505_;
v_isShared_1510_ = v_isSharedCheck_1535_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_a_1507_);
lean_inc(v_a_1506_);
lean_dec(v___x_1505_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1535_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v_fst_1511_; lean_object* v_snd_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1534_; 
v_fst_1511_ = lean_ctor_get(v_a_1506_, 0);
v_snd_1512_ = lean_ctor_get(v_a_1506_, 1);
v_isSharedCheck_1534_ = !lean_is_exclusive(v_a_1506_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1514_ = v_a_1506_;
v_isShared_1515_ = v_isSharedCheck_1534_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_snd_1512_);
lean_inc(v_fst_1511_);
lean_dec(v_a_1506_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1534_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
size_t v___x_1516_; size_t v___x_1517_; uint8_t v___x_1518_; 
v___x_1516_ = lean_ptr_addr(v_type_1489_);
v___x_1517_ = lean_ptr_addr(v_fst_1496_);
v___x_1518_ = lean_usize_dec_eq(v___x_1516_, v___x_1517_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1519_; 
lean_inc(v_declName_1488_);
lean_del_object(v___x_1514_);
lean_del_object(v___x_1509_);
lean_dec_ref_known(v_e_1372_, 4);
v___x_1519_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4(v_declName_1488_, v_fst_1496_, v_fst_1501_, v_fst_1511_, v_nondep_1492_, v_snd_1512_, v_a_1375_, v_a_1376_, v_a_1507_);
return v___x_1519_;
}
else
{
size_t v___x_1520_; size_t v___x_1521_; uint8_t v___x_1522_; 
v___x_1520_ = lean_ptr_addr(v_value_1490_);
v___x_1521_ = lean_ptr_addr(v_fst_1501_);
v___x_1522_ = lean_usize_dec_eq(v___x_1520_, v___x_1521_);
if (v___x_1522_ == 0)
{
lean_object* v___x_1523_; 
lean_inc(v_declName_1488_);
lean_del_object(v___x_1514_);
lean_del_object(v___x_1509_);
lean_dec_ref_known(v_e_1372_, 4);
v___x_1523_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4(v_declName_1488_, v_fst_1496_, v_fst_1501_, v_fst_1511_, v_nondep_1492_, v_snd_1512_, v_a_1375_, v_a_1376_, v_a_1507_);
return v___x_1523_;
}
else
{
size_t v___x_1524_; size_t v___x_1525_; uint8_t v___x_1526_; 
v___x_1524_ = lean_ptr_addr(v_body_1491_);
v___x_1525_ = lean_ptr_addr(v_fst_1511_);
v___x_1526_ = lean_usize_dec_eq(v___x_1524_, v___x_1525_);
if (v___x_1526_ == 0)
{
lean_object* v___x_1527_; 
lean_inc(v_declName_1488_);
lean_del_object(v___x_1514_);
lean_del_object(v___x_1509_);
lean_dec_ref_known(v_e_1372_, 4);
v___x_1527_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4(v_declName_1488_, v_fst_1496_, v_fst_1501_, v_fst_1511_, v_nondep_1492_, v_snd_1512_, v_a_1375_, v_a_1376_, v_a_1507_);
return v___x_1527_;
}
else
{
lean_object* v___x_1529_; 
lean_dec(v_fst_1511_);
lean_dec(v_fst_1501_);
lean_dec(v_fst_1496_);
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 0, v_e_1372_);
v___x_1529_ = v___x_1514_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_e_1372_);
lean_ctor_set(v_reuseFailAlloc_1533_, 1, v_snd_1512_);
v___x_1529_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
lean_object* v___x_1531_; 
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 0, v___x_1529_);
v___x_1531_ = v___x_1509_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1529_);
lean_ctor_set(v_reuseFailAlloc_1532_, 1, v_a_1507_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
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
lean_dec(v_fst_1501_);
lean_dec(v_fst_1496_);
lean_dec_ref_known(v_e_1372_, 4);
return v___x_1505_;
}
}
else
{
lean_dec(v_fst_1496_);
lean_dec_ref_known(v_e_1372_, 4);
lean_dec(v_offset_1373_);
return v___x_1498_;
}
}
else
{
lean_dec_ref_known(v_e_1372_, 4);
lean_dec(v_offset_1373_);
return v___x_1493_;
}
}
case 10:
{
lean_object* v_data_1536_; lean_object* v_expr_1537_; lean_object* v___x_1538_; 
v_data_1536_ = lean_ctor_get(v_e_1372_, 0);
v_expr_1537_ = lean_ctor_get(v_e_1372_, 1);
lean_inc_ref(v_expr_1537_);
v___x_1538_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1370_, v_xs_1371_, v_expr_1537_, v_offset_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v_a_1539_; lean_object* v_a_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1560_; 
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
v_a_1540_ = lean_ctor_get(v___x_1538_, 1);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1542_ = v___x_1538_;
v_isShared_1543_ = v_isSharedCheck_1560_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_inc(v_a_1539_);
lean_dec(v___x_1538_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1560_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v_fst_1544_; lean_object* v_snd_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1559_; 
v_fst_1544_ = lean_ctor_get(v_a_1539_, 0);
v_snd_1545_ = lean_ctor_get(v_a_1539_, 1);
v_isSharedCheck_1559_ = !lean_is_exclusive(v_a_1539_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1547_ = v_a_1539_;
v_isShared_1548_ = v_isSharedCheck_1559_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_snd_1545_);
lean_inc(v_fst_1544_);
lean_dec(v_a_1539_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1559_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
size_t v___x_1549_; size_t v___x_1550_; uint8_t v___x_1551_; 
v___x_1549_ = lean_ptr_addr(v_expr_1537_);
v___x_1550_ = lean_ptr_addr(v_fst_1544_);
v___x_1551_ = lean_usize_dec_eq(v___x_1549_, v___x_1550_);
if (v___x_1551_ == 0)
{
lean_object* v___x_1552_; 
lean_inc(v_data_1536_);
lean_del_object(v___x_1547_);
lean_del_object(v___x_1542_);
lean_dec_ref_known(v_e_1372_, 2);
v___x_1552_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__5(v_data_1536_, v_fst_1544_, v_snd_1545_, v_a_1375_, v_a_1376_, v_a_1540_);
return v___x_1552_;
}
else
{
lean_object* v___x_1554_; 
lean_dec(v_fst_1544_);
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 0, v_e_1372_);
v___x_1554_ = v___x_1547_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_e_1372_);
lean_ctor_set(v_reuseFailAlloc_1558_, 1, v_snd_1545_);
v___x_1554_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
lean_object* v___x_1556_; 
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 0, v___x_1554_);
v___x_1556_ = v___x_1542_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1554_);
lean_ctor_set(v_reuseFailAlloc_1557_, 1, v_a_1540_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1372_, 2);
return v___x_1538_;
}
}
case 11:
{
lean_object* v_typeName_1561_; lean_object* v_idx_1562_; lean_object* v_struct_1563_; lean_object* v___x_1564_; 
v_typeName_1561_ = lean_ctor_get(v_e_1372_, 0);
v_idx_1562_ = lean_ctor_get(v_e_1372_, 1);
v_struct_1563_ = lean_ctor_get(v_e_1372_, 2);
lean_inc_ref(v_struct_1563_);
v___x_1564_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1370_, v_xs_1371_, v_struct_1563_, v_offset_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v_a_1565_; lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1586_; 
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
v_a_1566_ = lean_ctor_get(v___x_1564_, 1);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1568_ = v___x_1564_;
v_isShared_1569_ = v_isSharedCheck_1586_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_inc(v_a_1565_);
lean_dec(v___x_1564_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1586_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v_fst_1570_; lean_object* v_snd_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1585_; 
v_fst_1570_ = lean_ctor_get(v_a_1565_, 0);
v_snd_1571_ = lean_ctor_get(v_a_1565_, 1);
v_isSharedCheck_1585_ = !lean_is_exclusive(v_a_1565_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1573_ = v_a_1565_;
v_isShared_1574_ = v_isSharedCheck_1585_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_snd_1571_);
lean_inc(v_fst_1570_);
lean_dec(v_a_1565_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1585_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
size_t v___x_1575_; size_t v___x_1576_; uint8_t v___x_1577_; 
v___x_1575_ = lean_ptr_addr(v_struct_1563_);
v___x_1576_ = lean_ptr_addr(v_fst_1570_);
v___x_1577_ = lean_usize_dec_eq(v___x_1575_, v___x_1576_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1578_; 
lean_inc(v_idx_1562_);
lean_inc(v_typeName_1561_);
lean_del_object(v___x_1573_);
lean_del_object(v___x_1568_);
lean_dec_ref_known(v_e_1372_, 3);
v___x_1578_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__6(v_typeName_1561_, v_idx_1562_, v_fst_1570_, v_snd_1571_, v_a_1375_, v_a_1376_, v_a_1566_);
return v___x_1578_;
}
else
{
lean_object* v___x_1580_; 
lean_dec(v_fst_1570_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 0, v_e_1372_);
v___x_1580_ = v___x_1573_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_e_1372_);
lean_ctor_set(v_reuseFailAlloc_1584_, 1, v_snd_1571_);
v___x_1580_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
lean_object* v___x_1582_; 
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 0, v___x_1580_);
v___x_1582_ = v___x_1568_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1580_);
lean_ctor_set(v_reuseFailAlloc_1583_, 1, v_a_1566_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1372_, 3);
return v___x_1564_;
}
}
default: 
{
lean_object* v___x_1587_; lean_object* v___x_1588_; 
lean_dec(v_offset_1373_);
lean_dec_ref(v_e_1372_);
v___x_1587_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__3);
v___x_1588_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7(v___x_1587_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
return v___x_1588_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(lean_object* v_n_1589_, lean_object* v_xs_1590_, lean_object* v_e_1591_, lean_object* v_offset_1592_, lean_object* v_a_1593_, uint8_t v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_){
_start:
{
lean_object* v_key_1597_; lean_object* v___x_1598_; 
lean_inc(v_offset_1592_);
lean_inc_ref(v_e_1591_);
v_key_1597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1597_, 0, v_e_1591_);
lean_ctor_set(v_key_1597_, 1, v_offset_1592_);
v___x_1598_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2___redArg(v_a_1593_, v_key_1597_);
if (lean_obj_tag(v___x_1598_) == 1)
{
lean_object* v_val_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
lean_dec_ref_known(v_key_1597_, 2);
lean_dec(v_offset_1592_);
lean_dec_ref(v_e_1591_);
v_val_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_val_1599_);
lean_dec_ref_known(v___x_1598_, 1);
v___x_1600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1600_, 0, v_val_1599_);
lean_ctor_set(v___x_1600_, 1, v_a_1593_);
v___x_1601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1600_);
lean_ctor_set(v___x_1601_, 1, v_a_1596_);
return v___x_1601_;
}
else
{
lean_dec(v___x_1598_);
switch(lean_obj_tag(v_e_1591_))
{
case 0:
{
lean_object* v_deBruijnIndex_1602_; uint8_t v___x_1603_; 
v_deBruijnIndex_1602_ = lean_ctor_get(v_e_1591_, 0);
v___x_1603_ = lean_nat_dec_le(v_offset_1592_, v_deBruijnIndex_1602_);
if (v___x_1603_ == 0)
{
lean_object* v___x_1604_; 
lean_dec(v_offset_1592_);
v___x_1604_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1597_, v_e_1591_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_);
return v___x_1604_;
}
else
{
lean_object* v_size_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; uint8_t v___x_1611_; 
lean_inc(v_deBruijnIndex_1602_);
lean_dec_ref_known(v_e_1591_, 1);
v_size_1605_ = lean_ctor_get(v_xs_1590_, 2);
v___x_1606_ = l_Lean_instInhabitedExpr;
v___x_1607_ = lean_nat_sub(v_deBruijnIndex_1602_, v_offset_1592_);
lean_dec(v_offset_1592_);
lean_dec(v_deBruijnIndex_1602_);
v___x_1608_ = lean_nat_sub(v_n_1589_, v___x_1607_);
lean_dec(v___x_1607_);
v___x_1609_ = lean_unsigned_to_nat(1u);
v___x_1610_ = lean_nat_sub(v___x_1608_, v___x_1609_);
lean_dec(v___x_1608_);
v___x_1611_ = lean_nat_dec_lt(v___x_1610_, v_size_1605_);
if (v___x_1611_ == 0)
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
lean_dec(v___x_1610_);
v___x_1612_ = l_outOfBounds___redArg(v___x_1606_);
v___x_1613_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1597_, v___x_1612_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_);
return v___x_1613_;
}
else
{
lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1614_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1606_, v_xs_1590_, v___x_1610_);
lean_dec(v___x_1610_);
v___x_1615_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1597_, v___x_1614_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_);
return v___x_1615_;
}
}
}
case 9:
{
lean_object* v___x_1616_; 
lean_dec(v_offset_1592_);
v___x_1616_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1597_, v_e_1591_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_);
return v___x_1616_;
}
case 2:
{
lean_object* v___x_1617_; 
lean_dec(v_offset_1592_);
v___x_1617_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1597_, v_e_1591_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_);
return v___x_1617_;
}
case 1:
{
lean_object* v___x_1618_; 
lean_dec(v_offset_1592_);
v___x_1618_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1597_, v_e_1591_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_);
return v___x_1618_;
}
case 4:
{
lean_object* v___x_1619_; 
lean_dec(v_offset_1592_);
v___x_1619_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1597_, v_e_1591_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_);
return v___x_1619_;
}
case 3:
{
lean_object* v___x_1620_; 
lean_dec(v_offset_1592_);
v___x_1620_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1597_, v_e_1591_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_);
return v___x_1620_;
}
default: 
{
lean_object* v___x_1621_; uint8_t v___x_1622_; 
v___x_1621_ = l_Lean_Expr_looseBVarRange(v_e_1591_);
v___x_1622_ = lean_nat_dec_le(v___x_1621_, v_offset_1592_);
lean_dec(v___x_1621_);
if (v___x_1622_ == 0)
{
switch(lean_obj_tag(v_e_1591_))
{
case 9:
{
lean_object* v___x_1623_; 
lean_dec(v_offset_1592_);
v___x_1623_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1597_, v_e_1591_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_);
return v___x_1623_;
}
case 2:
{
lean_object* v___x_1624_; 
lean_dec(v_offset_1592_);
v___x_1624_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1597_, v_e_1591_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_);
return v___x_1624_;
}
case 0:
{
lean_object* v___x_1625_; 
lean_dec(v_offset_1592_);
v___x_1625_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1597_, v_e_1591_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_);
return v___x_1625_;
}
case 1:
{
lean_object* v___x_1626_; 
lean_dec(v_offset_1592_);
v___x_1626_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1597_, v_e_1591_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_);
return v___x_1626_;
}
case 4:
{
lean_object* v___x_1627_; 
lean_dec(v_offset_1592_);
v___x_1627_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1597_, v_e_1591_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_);
return v___x_1627_;
}
case 3:
{
lean_object* v___x_1628_; 
lean_dec(v_offset_1592_);
v___x_1628_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1597_, v_e_1591_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_);
return v___x_1628_;
}
default: 
{
lean_object* v___x_1629_; 
v___x_1629_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0(v_n_1589_, v_xs_1590_, v_e_1591_, v_offset_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; lean_object* v_a_1631_; lean_object* v_fst_1632_; lean_object* v_snd_1633_; lean_object* v___x_1634_; 
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
lean_inc(v_a_1630_);
v_a_1631_ = lean_ctor_get(v___x_1629_, 1);
lean_inc(v_a_1631_);
lean_dec_ref_known(v___x_1629_, 2);
v_fst_1632_ = lean_ctor_get(v_a_1630_, 0);
lean_inc(v_fst_1632_);
v_snd_1633_ = lean_ctor_get(v_a_1630_, 1);
lean_inc(v_snd_1633_);
lean_dec(v_a_1630_);
v___x_1634_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1597_, v_fst_1632_, v_snd_1633_, v_a_1594_, v_a_1595_, v_a_1631_);
return v___x_1634_;
}
else
{
lean_dec_ref_known(v_key_1597_, 2);
return v___x_1629_;
}
}
}
}
else
{
lean_object* v___x_1635_; 
lean_dec(v_offset_1592_);
v___x_1635_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1597_, v_e_1591_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_);
return v___x_1635_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0___boxed(lean_object* v_n_1636_, lean_object* v_xs_1637_, lean_object* v_e_1638_, lean_object* v_offset_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_){
_start:
{
uint8_t v_a_boxed_1644_; lean_object* v_res_1645_; 
v_a_boxed_1644_ = lean_unbox(v_a_1641_);
v_res_1645_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1636_, v_xs_1637_, v_e_1638_, v_offset_1639_, v_a_1640_, v_a_boxed_1644_, v_a_1642_, v_a_1643_);
lean_dec_ref(v_a_1642_);
lean_dec_ref(v_xs_1637_);
lean_dec(v_n_1636_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___boxed(lean_object* v_n_1646_, lean_object* v_xs_1647_, lean_object* v_e_1648_, lean_object* v_offset_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_){
_start:
{
uint8_t v_a_boxed_1654_; lean_object* v_res_1655_; 
v_a_boxed_1654_ = lean_unbox(v_a_1651_);
v_res_1655_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0(v_n_1646_, v_xs_1647_, v_e_1648_, v_offset_1649_, v_a_1650_, v_a_boxed_1654_, v_a_1652_, v_a_1653_);
lean_dec_ref(v_a_1652_);
lean_dec_ref(v_xs_1647_);
lean_dec(v_n_1646_);
return v_res_1655_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1656_ = lean_box(0);
v___x_1657_ = lean_unsigned_to_nat(16u);
v___x_1658_ = lean_mk_array(v___x_1657_, v___x_1656_);
return v___x_1658_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1659_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__0, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__0_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__0);
v___x_1660_ = lean_unsigned_to_nat(0u);
v___x_1661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1660_);
lean_ctor_set(v___x_1661_, 1, v___x_1659_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0(lean_object* v_e_1662_, lean_object* v_size_1663_, lean_object* v___x_1664_, lean_object* v_xs_1665_, uint8_t v_debug_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
lean_object* v___x_1669_; 
v___x_1669_ = lean_unsigned_to_nat(0u);
switch(lean_obj_tag(v_e_1662_))
{
case 0:
{
lean_object* v_deBruijnIndex_1670_; uint8_t v___x_1671_; 
v_deBruijnIndex_1670_ = lean_ctor_get(v_e_1662_, 0);
v___x_1671_ = lean_nat_dec_le(v___x_1669_, v_deBruijnIndex_1670_);
if (v___x_1671_ == 0)
{
lean_object* v___x_1672_; 
v___x_1672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1672_, 0, v_e_1662_);
lean_ctor_set(v___x_1672_, 1, v___y_1668_);
return v___x_1672_;
}
else
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; uint8_t v___x_1676_; 
lean_inc(v_deBruijnIndex_1670_);
lean_dec_ref_known(v_e_1662_, 1);
v___x_1673_ = lean_nat_sub(v_size_1663_, v_deBruijnIndex_1670_);
lean_dec(v_deBruijnIndex_1670_);
v___x_1674_ = lean_unsigned_to_nat(1u);
v___x_1675_ = lean_nat_sub(v___x_1673_, v___x_1674_);
lean_dec(v___x_1673_);
v___x_1676_ = lean_nat_dec_lt(v___x_1675_, v_size_1663_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
lean_dec(v___x_1675_);
v___x_1677_ = l_outOfBounds___redArg(v___x_1664_);
v___x_1678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1677_);
lean_ctor_set(v___x_1678_, 1, v___y_1668_);
return v___x_1678_;
}
else
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1664_, v_xs_1665_, v___x_1675_);
lean_dec(v___x_1675_);
v___x_1680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1679_);
lean_ctor_set(v___x_1680_, 1, v___y_1668_);
return v___x_1680_;
}
}
}
case 9:
{
lean_object* v___x_1681_; 
v___x_1681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1681_, 0, v_e_1662_);
lean_ctor_set(v___x_1681_, 1, v___y_1668_);
return v___x_1681_;
}
case 2:
{
lean_object* v___x_1682_; 
v___x_1682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1682_, 0, v_e_1662_);
lean_ctor_set(v___x_1682_, 1, v___y_1668_);
return v___x_1682_;
}
case 1:
{
lean_object* v___x_1683_; 
v___x_1683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1683_, 0, v_e_1662_);
lean_ctor_set(v___x_1683_, 1, v___y_1668_);
return v___x_1683_;
}
case 4:
{
lean_object* v___x_1684_; 
v___x_1684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1684_, 0, v_e_1662_);
lean_ctor_set(v___x_1684_, 1, v___y_1668_);
return v___x_1684_;
}
case 3:
{
lean_object* v___x_1685_; 
v___x_1685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1685_, 0, v_e_1662_);
lean_ctor_set(v___x_1685_, 1, v___y_1668_);
return v___x_1685_;
}
default: 
{
lean_object* v___x_1686_; uint8_t v___x_1687_; 
v___x_1686_ = l_Lean_Expr_looseBVarRange(v_e_1662_);
v___x_1687_ = lean_nat_dec_le(v___x_1686_, v___x_1669_);
lean_dec(v___x_1686_);
if (v___x_1687_ == 0)
{
switch(lean_obj_tag(v_e_1662_))
{
case 9:
{
lean_object* v___x_1688_; 
v___x_1688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1688_, 0, v_e_1662_);
lean_ctor_set(v___x_1688_, 1, v___y_1668_);
return v___x_1688_;
}
case 2:
{
lean_object* v___x_1689_; 
v___x_1689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1689_, 0, v_e_1662_);
lean_ctor_set(v___x_1689_, 1, v___y_1668_);
return v___x_1689_;
}
case 0:
{
lean_object* v___x_1690_; 
v___x_1690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1690_, 0, v_e_1662_);
lean_ctor_set(v___x_1690_, 1, v___y_1668_);
return v___x_1690_;
}
case 1:
{
lean_object* v___x_1691_; 
v___x_1691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1691_, 0, v_e_1662_);
lean_ctor_set(v___x_1691_, 1, v___y_1668_);
return v___x_1691_;
}
case 4:
{
lean_object* v___x_1692_; 
v___x_1692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1692_, 0, v_e_1662_);
lean_ctor_set(v___x_1692_, 1, v___y_1668_);
return v___x_1692_;
}
case 3:
{
lean_object* v___x_1693_; 
v___x_1693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1693_, 0, v_e_1662_);
lean_ctor_set(v___x_1693_, 1, v___y_1668_);
return v___x_1693_;
}
default: 
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1694_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__1, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__1);
v___x_1695_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0(v_size_1663_, v_xs_1665_, v_e_1662_, v___x_1669_, v___x_1694_, v_debug_1666_, v___y_1667_, v___y_1668_);
if (lean_obj_tag(v___x_1695_) == 0)
{
lean_object* v_a_1696_; lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1705_; 
v_a_1696_ = lean_ctor_get(v___x_1695_, 0);
v_a_1697_ = lean_ctor_get(v___x_1695_, 1);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1699_ = v___x_1695_;
v_isShared_1700_ = v_isSharedCheck_1705_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_inc(v_a_1696_);
lean_dec(v___x_1695_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1705_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v_fst_1701_; lean_object* v___x_1703_; 
v_fst_1701_ = lean_ctor_get(v_a_1696_, 0);
lean_inc(v_fst_1701_);
lean_dec(v_a_1696_);
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 0, v_fst_1701_);
v___x_1703_ = v___x_1699_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_fst_1701_);
lean_ctor_set(v_reuseFailAlloc_1704_, 1, v_a_1697_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
else
{
lean_object* v_a_1706_; lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1714_; 
v_a_1706_ = lean_ctor_get(v___x_1695_, 0);
v_a_1707_ = lean_ctor_get(v___x_1695_, 1);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1709_ = v___x_1695_;
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_inc(v_a_1706_);
lean_dec(v___x_1695_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1712_; 
if (v_isShared_1710_ == 0)
{
v___x_1712_ = v___x_1709_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_a_1706_);
lean_ctor_set(v_reuseFailAlloc_1713_, 1, v_a_1707_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
}
}
else
{
lean_object* v___x_1715_; 
v___x_1715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1715_, 0, v_e_1662_);
lean_ctor_set(v___x_1715_, 1, v___y_1668_);
return v___x_1715_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___boxed(lean_object* v_e_1716_, lean_object* v_size_1717_, lean_object* v___x_1718_, lean_object* v_xs_1719_, lean_object* v_debug_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
uint8_t v_debug_boxed_1723_; lean_object* v_res_1724_; 
v_debug_boxed_1723_ = lean_unbox(v_debug_1720_);
v_res_1724_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0(v_e_1716_, v_size_1717_, v___x_1718_, v_xs_1719_, v_debug_boxed_1723_, v___y_1721_, v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec_ref(v_xs_1719_);
lean_dec_ref(v___x_1718_);
lean_dec(v_size_1717_);
return v_res_1724_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2(void){
_start:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1727_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__2));
v___x_1728_ = lean_unsigned_to_nat(16u);
v___x_1729_ = lean_unsigned_to_nat(62u);
v___x_1730_ = ((lean_object*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__1));
v___x_1731_ = ((lean_object*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__0));
v___x_1732_ = l_mkPanicMessageWithDecl(v___x_1731_, v___x_1730_, v___x_1729_, v___x_1728_, v___x_1727_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg(lean_object* v_xs_1733_, lean_object* v_e_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_){
_start:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v_size_1744_; uint8_t v_debug_1745_; lean_object* v_env_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___f_1749_; uint8_t v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1742_ = lean_st_ref_get(v_a_1736_);
v___x_1743_ = lean_st_ref_get(v_a_1740_);
v_size_1744_ = lean_ctor_get(v_xs_1733_, 2);
lean_inc(v_size_1744_);
v_debug_1745_ = lean_ctor_get_uint8(v___x_1742_, sizeof(void*)*11);
lean_dec(v___x_1742_);
v_env_1746_ = lean_ctor_get(v___x_1743_, 0);
lean_inc_ref(v_env_1746_);
lean_dec(v___x_1743_);
v___x_1747_ = l_Lean_instInhabitedExpr;
v___x_1748_ = lean_box(v_debug_1745_);
v___f_1749_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___boxed), 7, 5);
lean_closure_set(v___f_1749_, 0, v_e_1734_);
lean_closure_set(v___f_1749_, 1, v_size_1744_);
lean_closure_set(v___f_1749_, 2, v___x_1747_);
lean_closure_set(v___f_1749_, 3, v_xs_1733_);
lean_closure_set(v___f_1749_, 4, v___x_1748_);
v___x_1750_ = 0;
v___x_1751_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1751_, 0, v_env_1746_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*1, v___x_1750_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*1 + 1, v___x_1750_);
v___x_1752_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_1749_, v___x_1751_, v_a_1736_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1763_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1755_ = v___x_1752_;
v_isShared_1756_ = v_isSharedCheck_1763_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1752_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1763_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
if (lean_obj_tag(v_a_1753_) == 0)
{
lean_object* v___x_1757_; lean_object* v___x_1758_; 
lean_dec_ref_known(v_a_1753_, 1);
lean_del_object(v___x_1755_);
v___x_1757_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2);
v___x_1758_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1(v___x_1757_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
return v___x_1758_;
}
else
{
lean_object* v_a_1759_; lean_object* v___x_1761_; 
v_a_1759_ = lean_ctor_get(v_a_1753_, 0);
lean_inc(v_a_1759_);
lean_dec_ref_known(v_a_1753_, 1);
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 0, v_a_1759_);
v___x_1761_ = v___x_1755_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_a_1759_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
}
else
{
lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1771_; 
v_a_1764_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1766_ = v___x_1752_;
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v___x_1752_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1769_; 
if (v_isShared_1767_ == 0)
{
v___x_1769_ = v___x_1766_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_a_1764_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___boxed(lean_object* v_xs_1772_, lean_object* v_e_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg(v_xs_1772_, v_e_1773_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_);
lean_dec(v_a_1779_);
lean_dec_ref(v_a_1778_);
lean_dec(v_a_1777_);
lean_dec_ref(v_a_1776_);
lean_dec(v_a_1775_);
lean_dec_ref(v_a_1774_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv(lean_object* v_xs_1782_, lean_object* v_e_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg(v_xs_1782_, v_e_1783_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_, v_a_1790_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___boxed(lean_object* v_xs_1793_, lean_object* v_e_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv(v_xs_1793_, v_e_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_);
lean_dec(v_a_1801_);
lean_dec_ref(v_a_1800_);
lean_dec(v_a_1799_);
lean_dec_ref(v_a_1798_);
lean_dec(v_a_1797_);
lean_dec_ref(v_a_1796_);
lean_dec(v_a_1795_);
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1804_, lean_object* v_m_1805_, lean_object* v_a_1806_){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2___redArg(v_m_1805_, v_a_1806_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1808_, lean_object* v_m_1809_, lean_object* v_a_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2(v_00_u03b2_1808_, v_m_1809_, v_a_1810_);
lean_dec_ref(v_a_1810_);
lean_dec_ref(v_m_1809_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10(lean_object* v_00_u03b2_1812_, lean_object* v_a_1813_, lean_object* v_x_1814_){
_start:
{
lean_object* v___x_1815_; 
v___x_1815_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10___redArg(v_a_1813_, v_x_1814_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10___boxed(lean_object* v_00_u03b2_1816_, lean_object* v_a_1817_, lean_object* v_x_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10(v_00_u03b2_1816_, v_a_1817_, v_x_1818_);
lean_dec(v_x_1818_);
lean_dec_ref(v_a_1817_);
return v_res_1819_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1820_; 
v___x_1820_ = l_instMonadEIO(lean_box(0));
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(lean_object* v_msg_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v_toApplicative_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1900_; 
v___x_1834_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__0);
v___x_1835_ = l_StateRefT_x27_instMonad___redArg(v___x_1834_);
v_toApplicative_1836_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1900_ == 0)
{
lean_object* v_unused_1901_; 
v_unused_1901_ = lean_ctor_get(v___x_1835_, 1);
lean_dec(v_unused_1901_);
v___x_1838_ = v___x_1835_;
v_isShared_1839_ = v_isSharedCheck_1900_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_toApplicative_1836_);
lean_dec(v___x_1835_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1900_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v_toFunctor_1840_; lean_object* v_toSeq_1841_; lean_object* v_toSeqLeft_1842_; lean_object* v_toSeqRight_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1898_; 
v_toFunctor_1840_ = lean_ctor_get(v_toApplicative_1836_, 0);
v_toSeq_1841_ = lean_ctor_get(v_toApplicative_1836_, 2);
v_toSeqLeft_1842_ = lean_ctor_get(v_toApplicative_1836_, 3);
v_toSeqRight_1843_ = lean_ctor_get(v_toApplicative_1836_, 4);
v_isSharedCheck_1898_ = !lean_is_exclusive(v_toApplicative_1836_);
if (v_isSharedCheck_1898_ == 0)
{
lean_object* v_unused_1899_; 
v_unused_1899_ = lean_ctor_get(v_toApplicative_1836_, 1);
lean_dec(v_unused_1899_);
v___x_1845_ = v_toApplicative_1836_;
v_isShared_1846_ = v_isSharedCheck_1898_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_toSeqRight_1843_);
lean_inc(v_toSeqLeft_1842_);
lean_inc(v_toSeq_1841_);
lean_inc(v_toFunctor_1840_);
lean_dec(v_toApplicative_1836_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1898_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___f_1847_; lean_object* v___f_1848_; lean_object* v___f_1849_; lean_object* v___f_1850_; lean_object* v___x_1851_; lean_object* v___f_1852_; lean_object* v___f_1853_; lean_object* v___f_1854_; lean_object* v___x_1856_; 
v___f_1847_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__1));
v___f_1848_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1840_);
v___f_1849_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1849_, 0, v_toFunctor_1840_);
v___f_1850_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1850_, 0, v_toFunctor_1840_);
v___x_1851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___f_1849_);
lean_ctor_set(v___x_1851_, 1, v___f_1850_);
v___f_1852_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1852_, 0, v_toSeqRight_1843_);
v___f_1853_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1853_, 0, v_toSeqLeft_1842_);
v___f_1854_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1854_, 0, v_toSeq_1841_);
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 4, v___f_1852_);
lean_ctor_set(v___x_1845_, 3, v___f_1853_);
lean_ctor_set(v___x_1845_, 2, v___f_1854_);
lean_ctor_set(v___x_1845_, 1, v___f_1847_);
lean_ctor_set(v___x_1845_, 0, v___x_1851_);
v___x_1856_ = v___x_1845_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v___x_1851_);
lean_ctor_set(v_reuseFailAlloc_1897_, 1, v___f_1847_);
lean_ctor_set(v_reuseFailAlloc_1897_, 2, v___f_1854_);
lean_ctor_set(v_reuseFailAlloc_1897_, 3, v___f_1853_);
lean_ctor_set(v_reuseFailAlloc_1897_, 4, v___f_1852_);
v___x_1856_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
lean_object* v___x_1858_; 
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 1, v___f_1848_);
lean_ctor_set(v___x_1838_, 0, v___x_1856_);
v___x_1858_ = v___x_1838_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1856_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v___f_1848_);
v___x_1858_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
lean_object* v___x_1859_; lean_object* v_toApplicative_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1894_; 
v___x_1859_ = l_StateRefT_x27_instMonad___redArg(v___x_1858_);
v_toApplicative_1860_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1894_ == 0)
{
lean_object* v_unused_1895_; 
v_unused_1895_ = lean_ctor_get(v___x_1859_, 1);
lean_dec(v_unused_1895_);
v___x_1862_ = v___x_1859_;
v_isShared_1863_ = v_isSharedCheck_1894_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_toApplicative_1860_);
lean_dec(v___x_1859_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1894_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v_toFunctor_1864_; lean_object* v_toSeq_1865_; lean_object* v_toSeqLeft_1866_; lean_object* v_toSeqRight_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1892_; 
v_toFunctor_1864_ = lean_ctor_get(v_toApplicative_1860_, 0);
v_toSeq_1865_ = lean_ctor_get(v_toApplicative_1860_, 2);
v_toSeqLeft_1866_ = lean_ctor_get(v_toApplicative_1860_, 3);
v_toSeqRight_1867_ = lean_ctor_get(v_toApplicative_1860_, 4);
v_isSharedCheck_1892_ = !lean_is_exclusive(v_toApplicative_1860_);
if (v_isSharedCheck_1892_ == 0)
{
lean_object* v_unused_1893_; 
v_unused_1893_ = lean_ctor_get(v_toApplicative_1860_, 1);
lean_dec(v_unused_1893_);
v___x_1869_ = v_toApplicative_1860_;
v_isShared_1870_ = v_isSharedCheck_1892_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_toSeqRight_1867_);
lean_inc(v_toSeqLeft_1866_);
lean_inc(v_toSeq_1865_);
lean_inc(v_toFunctor_1864_);
lean_dec(v_toApplicative_1860_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1892_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___f_1871_; lean_object* v___f_1872_; lean_object* v___f_1873_; lean_object* v___f_1874_; lean_object* v___x_1875_; lean_object* v___f_1876_; lean_object* v___f_1877_; lean_object* v___f_1878_; lean_object* v___x_1880_; 
v___f_1871_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__3));
v___f_1872_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1864_);
v___f_1873_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1873_, 0, v_toFunctor_1864_);
v___f_1874_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1874_, 0, v_toFunctor_1864_);
v___x_1875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___f_1873_);
lean_ctor_set(v___x_1875_, 1, v___f_1874_);
v___f_1876_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1876_, 0, v_toSeqRight_1867_);
v___f_1877_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1877_, 0, v_toSeqLeft_1866_);
v___f_1878_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1878_, 0, v_toSeq_1865_);
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 4, v___f_1876_);
lean_ctor_set(v___x_1869_, 3, v___f_1877_);
lean_ctor_set(v___x_1869_, 2, v___f_1878_);
lean_ctor_set(v___x_1869_, 1, v___f_1871_);
lean_ctor_set(v___x_1869_, 0, v___x_1875_);
v___x_1880_ = v___x_1869_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1875_);
lean_ctor_set(v_reuseFailAlloc_1891_, 1, v___f_1871_);
lean_ctor_set(v_reuseFailAlloc_1891_, 2, v___f_1878_);
lean_ctor_set(v_reuseFailAlloc_1891_, 3, v___f_1877_);
lean_ctor_set(v_reuseFailAlloc_1891_, 4, v___f_1876_);
v___x_1880_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
lean_object* v___x_1882_; 
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 1, v___f_1872_);
lean_ctor_set(v___x_1862_, 0, v___x_1880_);
v___x_1882_ = v___x_1862_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v___x_1880_);
lean_ctor_set(v_reuseFailAlloc_1890_, 1, v___f_1872_);
v___x_1882_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_14852__overap_1888_; lean_object* v___x_1889_; 
v___x_1883_ = l_StateRefT_x27_instMonad___redArg(v___x_1882_);
v___x_1884_ = l_ReaderT_instMonad___redArg(v___x_1883_);
v___x_1885_ = l_StateRefT_x27_instMonad___redArg(v___x_1884_);
v___x_1886_ = l_Lean_instInhabitedExpr;
v___x_1887_ = l_instInhabitedOfMonad___redArg(v___x_1885_, v___x_1886_);
v___x_14852__overap_1888_ = lean_panic_fn_borrowed(v___x_1887_, v_msg_1825_);
lean_dec(v___x_1887_);
lean_inc(v___y_1832_);
lean_inc_ref(v___y_1831_);
lean_inc(v___y_1830_);
lean_inc_ref(v___y_1829_);
lean_inc(v___y_1828_);
lean_inc_ref(v___y_1827_);
lean_inc(v___y_1826_);
v___x_1889_ = lean_apply_8(v___x_14852__overap_1888_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, lean_box(0));
return v___x_1889_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___boxed(lean_object* v_msg_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
lean_object* v_res_1911_; 
v_res_1911_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(v_msg_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1903_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1___redArg(lean_object* v_f_1912_, lean_object* v_a_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_){
_start:
{
lean_object* v___y_1922_; lean_object* v___x_1925_; uint8_t v_debug_1926_; 
v___x_1925_ = lean_st_ref_get(v___y_1915_);
v_debug_1926_ = lean_ctor_get_uint8(v___x_1925_, sizeof(void*)*11);
lean_dec(v___x_1925_);
if (v_debug_1926_ == 0)
{
v___y_1922_ = v___y_1915_;
goto v___jp_1921_;
}
else
{
lean_object* v___x_1927_; 
v___x_1927_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_1912_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v___x_1928_; 
lean_dec_ref_known(v___x_1927_, 1);
v___x_1928_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_dec_ref_known(v___x_1928_, 1);
v___y_1922_ = v___y_1915_;
goto v___jp_1921_;
}
else
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
lean_dec_ref(v_a_1913_);
lean_dec_ref(v_f_1912_);
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1931_ = v___x_1928_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1928_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1929_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
}
else
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
lean_dec_ref(v_a_1913_);
lean_dec_ref(v_f_1912_);
v_a_1937_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1939_ = v___x_1927_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1927_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1942_; 
if (v_isShared_1940_ == 0)
{
v___x_1942_ = v___x_1939_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_a_1937_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
v___jp_1921_:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1923_ = l_Lean_Expr_app___override(v_f_1912_, v_a_1913_);
v___x_1924_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1923_, v___y_1922_);
return v___x_1924_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1___redArg___boxed(lean_object* v_f_1945_, lean_object* v_a_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1___redArg(v_f_1945_, v_a_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1(lean_object* v_f_1955_, lean_object* v_a_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v___x_1965_; 
v___x_1965_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1___redArg(v_f_1955_, v_a_1956_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1___boxed(lean_object* v_f_1966_, lean_object* v_a_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1(v_f_1966_, v_a_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v___y_1968_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2___redArg(lean_object* v_d_1977_, lean_object* v_e_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_){
_start:
{
lean_object* v___y_1987_; lean_object* v___x_1990_; uint8_t v_debug_1991_; 
v___x_1990_ = lean_st_ref_get(v___y_1980_);
v_debug_1991_ = lean_ctor_get_uint8(v___x_1990_, sizeof(void*)*11);
lean_dec(v___x_1990_);
if (v_debug_1991_ == 0)
{
v___y_1987_ = v___y_1980_;
goto v___jp_1986_;
}
else
{
lean_object* v___x_1992_; 
v___x_1992_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_e_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_dec_ref_known(v___x_1992_, 1);
v___y_1987_ = v___y_1980_;
goto v___jp_1986_;
}
else
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2000_; 
lean_dec_ref(v_e_1978_);
lean_dec(v_d_1977_);
v_a_1993_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1995_ = v___x_1992_;
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1992_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1998_; 
if (v_isShared_1996_ == 0)
{
v___x_1998_ = v___x_1995_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_a_1993_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
}
v___jp_1986_:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___x_1988_ = l_Lean_Expr_mdata___override(v_d_1977_, v_e_1978_);
v___x_1989_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1988_, v___y_1987_);
return v___x_1989_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2___redArg___boxed(lean_object* v_d_2001_, lean_object* v_e_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2___redArg(v_d_2001_, v_e_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
return v_res_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2(lean_object* v_d_2011_, lean_object* v_e_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
lean_object* v___x_2021_; 
v___x_2021_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2___redArg(v_d_2011_, v_e_2012_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2___boxed(lean_object* v_d_2022_, lean_object* v_e_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2(v_d_2022_, v_e_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec(v___y_2024_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3___redArg(lean_object* v_structName_2033_, lean_object* v_idx_2034_, lean_object* v_struct_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
lean_object* v___y_2044_; lean_object* v___x_2047_; uint8_t v_debug_2048_; 
v___x_2047_ = lean_st_ref_get(v___y_2037_);
v_debug_2048_ = lean_ctor_get_uint8(v___x_2047_, sizeof(void*)*11);
lean_dec(v___x_2047_);
if (v_debug_2048_ == 0)
{
v___y_2044_ = v___y_2037_;
goto v___jp_2043_;
}
else
{
lean_object* v___x_2049_; 
v___x_2049_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_struct_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_dec_ref_known(v___x_2049_, 1);
v___y_2044_ = v___y_2037_;
goto v___jp_2043_;
}
else
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2057_; 
lean_dec_ref(v_struct_2035_);
lean_dec(v_idx_2034_);
lean_dec(v_structName_2033_);
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2052_ = v___x_2049_;
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_2049_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2055_; 
if (v_isShared_2053_ == 0)
{
v___x_2055_ = v___x_2052_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_a_2050_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
}
v___jp_2043_:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2045_ = l_Lean_Expr_proj___override(v_structName_2033_, v_idx_2034_, v_struct_2035_);
v___x_2046_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2045_, v___y_2044_);
return v___x_2046_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3___redArg___boxed(lean_object* v_structName_2058_, lean_object* v_idx_2059_, lean_object* v_struct_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3___redArg(v_structName_2058_, v_idx_2059_, v_struct_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
lean_dec(v___y_2062_);
lean_dec_ref(v___y_2061_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3(lean_object* v_structName_2069_, lean_object* v_idx_2070_, lean_object* v_struct_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
lean_object* v___x_2080_; 
v___x_2080_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3___redArg(v_structName_2069_, v_idx_2070_, v_struct_2071_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3___boxed(lean_object* v_structName_2081_, lean_object* v_idx_2082_, lean_object* v_struct_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3(v_structName_2081_, v_idx_2082_, v_struct_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
lean_dec(v___y_2086_);
lean_dec_ref(v___y_2085_);
lean_dec(v___y_2084_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5_spec__5(lean_object* v_msgData_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
lean_object* v___x_2099_; lean_object* v_env_2100_; lean_object* v___x_2101_; lean_object* v_mctx_2102_; lean_object* v_lctx_2103_; lean_object* v_options_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2099_ = lean_st_ref_get(v___y_2097_);
v_env_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc_ref(v_env_2100_);
lean_dec(v___x_2099_);
v___x_2101_ = lean_st_ref_get(v___y_2095_);
v_mctx_2102_ = lean_ctor_get(v___x_2101_, 0);
lean_inc_ref(v_mctx_2102_);
lean_dec(v___x_2101_);
v_lctx_2103_ = lean_ctor_get(v___y_2094_, 2);
v_options_2104_ = lean_ctor_get(v___y_2096_, 1);
lean_inc_ref(v_options_2104_);
lean_inc_ref(v_lctx_2103_);
v___x_2105_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2105_, 0, v_env_2100_);
lean_ctor_set(v___x_2105_, 1, v_mctx_2102_);
lean_ctor_set(v___x_2105_, 2, v_lctx_2103_);
lean_ctor_set(v___x_2105_, 3, v_options_2104_);
v___x_2106_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2105_);
lean_ctor_set(v___x_2106_, 1, v_msgData_2093_);
v___x_2107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2106_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5_spec__5___boxed(lean_object* v_msgData_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
lean_object* v_res_2114_; 
v_res_2114_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5_spec__5(v_msgData_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5___redArg(lean_object* v_msg_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_){
_start:
{
lean_object* v_ref_2121_; lean_object* v___x_2122_; lean_object* v_a_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2131_; 
v_ref_2121_ = lean_ctor_get(v___y_2118_, 4);
v___x_2122_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5_spec__5(v_msg_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2125_ = v___x_2122_;
v_isShared_2126_ = v_isSharedCheck_2131_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_a_2123_);
lean_dec(v___x_2122_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2131_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2127_; lean_object* v___x_2129_; 
lean_inc(v_ref_2121_);
v___x_2127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2127_, 0, v_ref_2121_);
lean_ctor_set(v___x_2127_, 1, v_a_2123_);
if (v_isShared_2126_ == 0)
{
lean_ctor_set_tag(v___x_2125_, 1);
lean_ctor_set(v___x_2125_, 0, v___x_2127_);
v___x_2129_ = v___x_2125_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2127_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5___redArg___boxed(lean_object* v_msg_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5___redArg(v_msg_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7___redArg(lean_object* v_a_2139_, lean_object* v_x_2140_){
_start:
{
if (lean_obj_tag(v_x_2140_) == 0)
{
lean_object* v___x_2141_; 
v___x_2141_ = lean_box(0);
return v___x_2141_;
}
else
{
lean_object* v_key_2142_; lean_object* v_value_2143_; lean_object* v_tail_2144_; lean_object* v_fst_2145_; lean_object* v_snd_2146_; lean_object* v_fst_2147_; lean_object* v_snd_2148_; size_t v___x_2149_; size_t v___x_2150_; uint8_t v___x_2151_; 
v_key_2142_ = lean_ctor_get(v_x_2140_, 0);
v_value_2143_ = lean_ctor_get(v_x_2140_, 1);
v_tail_2144_ = lean_ctor_get(v_x_2140_, 2);
v_fst_2145_ = lean_ctor_get(v_key_2142_, 0);
v_snd_2146_ = lean_ctor_get(v_key_2142_, 1);
v_fst_2147_ = lean_ctor_get(v_a_2139_, 0);
v_snd_2148_ = lean_ctor_get(v_a_2139_, 1);
v___x_2149_ = lean_ptr_addr(v_fst_2145_);
v___x_2150_ = lean_ptr_addr(v_fst_2147_);
v___x_2151_ = lean_usize_dec_eq(v___x_2149_, v___x_2150_);
if (v___x_2151_ == 0)
{
v_x_2140_ = v_tail_2144_;
goto _start;
}
else
{
size_t v___x_2153_; size_t v___x_2154_; uint8_t v___x_2155_; 
v___x_2153_ = lean_ptr_addr(v_snd_2146_);
v___x_2154_ = lean_ptr_addr(v_snd_2148_);
v___x_2155_ = lean_usize_dec_eq(v___x_2153_, v___x_2154_);
if (v___x_2155_ == 0)
{
v_x_2140_ = v_tail_2144_;
goto _start;
}
else
{
lean_object* v___x_2157_; 
lean_inc(v_value_2143_);
v___x_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2157_, 0, v_value_2143_);
return v___x_2157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7___redArg___boxed(lean_object* v_a_2158_, lean_object* v_x_2159_){
_start:
{
lean_object* v_res_2160_; 
v_res_2160_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7___redArg(v_a_2158_, v_x_2159_);
lean_dec(v_x_2159_);
lean_dec_ref(v_a_2158_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6___redArg(lean_object* v_m_2161_, lean_object* v_a_2162_){
_start:
{
lean_object* v_buckets_2163_; lean_object* v_fst_2164_; lean_object* v_snd_2165_; lean_object* v___x_2166_; size_t v___x_2167_; size_t v___x_2168_; size_t v___x_2169_; uint64_t v___x_2170_; size_t v___x_2171_; size_t v___x_2172_; uint64_t v___x_2173_; uint64_t v___x_2174_; uint64_t v___x_2175_; uint64_t v___x_2176_; uint64_t v_fold_2177_; uint64_t v___x_2178_; uint64_t v___x_2179_; uint64_t v___x_2180_; size_t v___x_2181_; size_t v___x_2182_; size_t v___x_2183_; size_t v___x_2184_; size_t v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v_buckets_2163_ = lean_ctor_get(v_m_2161_, 1);
v_fst_2164_ = lean_ctor_get(v_a_2162_, 0);
v_snd_2165_ = lean_ctor_get(v_a_2162_, 1);
v___x_2166_ = lean_array_get_size(v_buckets_2163_);
v___x_2167_ = lean_ptr_addr(v_fst_2164_);
v___x_2168_ = ((size_t)3ULL);
v___x_2169_ = lean_usize_shift_right(v___x_2167_, v___x_2168_);
v___x_2170_ = lean_usize_to_uint64(v___x_2169_);
v___x_2171_ = lean_ptr_addr(v_snd_2165_);
v___x_2172_ = lean_usize_shift_right(v___x_2171_, v___x_2168_);
v___x_2173_ = lean_usize_to_uint64(v___x_2172_);
v___x_2174_ = lean_uint64_mix_hash(v___x_2170_, v___x_2173_);
v___x_2175_ = 32ULL;
v___x_2176_ = lean_uint64_shift_right(v___x_2174_, v___x_2175_);
v_fold_2177_ = lean_uint64_xor(v___x_2174_, v___x_2176_);
v___x_2178_ = 16ULL;
v___x_2179_ = lean_uint64_shift_right(v_fold_2177_, v___x_2178_);
v___x_2180_ = lean_uint64_xor(v_fold_2177_, v___x_2179_);
v___x_2181_ = lean_uint64_to_usize(v___x_2180_);
v___x_2182_ = lean_usize_of_nat(v___x_2166_);
v___x_2183_ = ((size_t)1ULL);
v___x_2184_ = lean_usize_sub(v___x_2182_, v___x_2183_);
v___x_2185_ = lean_usize_land(v___x_2181_, v___x_2184_);
v___x_2186_ = lean_array_uget_borrowed(v_buckets_2163_, v___x_2185_);
v___x_2187_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7___redArg(v_a_2162_, v___x_2186_);
return v___x_2187_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6___redArg___boxed(lean_object* v_m_2188_, lean_object* v_a_2189_){
_start:
{
lean_object* v_res_2190_; 
v_res_2190_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6___redArg(v_m_2188_, v_a_2189_);
lean_dec_ref(v_a_2189_);
lean_dec_ref(v_m_2188_);
return v_res_2190_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9___redArg(lean_object* v_a_2191_, lean_object* v_x_2192_){
_start:
{
if (lean_obj_tag(v_x_2192_) == 0)
{
uint8_t v___x_2193_; 
v___x_2193_ = 0;
return v___x_2193_;
}
else
{
lean_object* v_key_2194_; lean_object* v_tail_2195_; lean_object* v_fst_2196_; lean_object* v_snd_2197_; lean_object* v_fst_2198_; lean_object* v_snd_2199_; size_t v___x_2200_; size_t v___x_2201_; uint8_t v___x_2202_; 
v_key_2194_ = lean_ctor_get(v_x_2192_, 0);
v_tail_2195_ = lean_ctor_get(v_x_2192_, 2);
v_fst_2196_ = lean_ctor_get(v_key_2194_, 0);
v_snd_2197_ = lean_ctor_get(v_key_2194_, 1);
v_fst_2198_ = lean_ctor_get(v_a_2191_, 0);
v_snd_2199_ = lean_ctor_get(v_a_2191_, 1);
v___x_2200_ = lean_ptr_addr(v_fst_2196_);
v___x_2201_ = lean_ptr_addr(v_fst_2198_);
v___x_2202_ = lean_usize_dec_eq(v___x_2200_, v___x_2201_);
if (v___x_2202_ == 0)
{
v_x_2192_ = v_tail_2195_;
goto _start;
}
else
{
size_t v___x_2204_; size_t v___x_2205_; uint8_t v___x_2206_; 
v___x_2204_ = lean_ptr_addr(v_snd_2197_);
v___x_2205_ = lean_ptr_addr(v_snd_2199_);
v___x_2206_ = lean_usize_dec_eq(v___x_2204_, v___x_2205_);
if (v___x_2206_ == 0)
{
v_x_2192_ = v_tail_2195_;
goto _start;
}
else
{
return v___x_2206_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9___redArg___boxed(lean_object* v_a_2208_, lean_object* v_x_2209_){
_start:
{
uint8_t v_res_2210_; lean_object* v_r_2211_; 
v_res_2210_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9___redArg(v_a_2208_, v_x_2209_);
lean_dec(v_x_2209_);
lean_dec_ref(v_a_2208_);
v_r_2211_ = lean_box(v_res_2210_);
return v_r_2211_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__11___redArg(lean_object* v_a_2212_, lean_object* v_b_2213_, lean_object* v_x_2214_){
_start:
{
if (lean_obj_tag(v_x_2214_) == 0)
{
lean_dec(v_b_2213_);
lean_dec_ref(v_a_2212_);
return v_x_2214_;
}
else
{
lean_object* v_key_2215_; lean_object* v_value_2216_; lean_object* v_tail_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2237_; 
v_key_2215_ = lean_ctor_get(v_x_2214_, 0);
v_value_2216_ = lean_ctor_get(v_x_2214_, 1);
v_tail_2217_ = lean_ctor_get(v_x_2214_, 2);
v_isSharedCheck_2237_ = !lean_is_exclusive(v_x_2214_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2219_ = v_x_2214_;
v_isShared_2220_ = v_isSharedCheck_2237_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_tail_2217_);
lean_inc(v_value_2216_);
lean_inc(v_key_2215_);
lean_dec(v_x_2214_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2237_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v_fst_2226_; lean_object* v_snd_2227_; lean_object* v_fst_2228_; lean_object* v_snd_2229_; size_t v___x_2230_; size_t v___x_2231_; uint8_t v___x_2232_; 
v_fst_2226_ = lean_ctor_get(v_key_2215_, 0);
v_snd_2227_ = lean_ctor_get(v_key_2215_, 1);
v_fst_2228_ = lean_ctor_get(v_a_2212_, 0);
v_snd_2229_ = lean_ctor_get(v_a_2212_, 1);
v___x_2230_ = lean_ptr_addr(v_fst_2226_);
v___x_2231_ = lean_ptr_addr(v_fst_2228_);
v___x_2232_ = lean_usize_dec_eq(v___x_2230_, v___x_2231_);
if (v___x_2232_ == 0)
{
goto v___jp_2221_;
}
else
{
size_t v___x_2233_; size_t v___x_2234_; uint8_t v___x_2235_; 
v___x_2233_ = lean_ptr_addr(v_snd_2227_);
v___x_2234_ = lean_ptr_addr(v_snd_2229_);
v___x_2235_ = lean_usize_dec_eq(v___x_2233_, v___x_2234_);
if (v___x_2235_ == 0)
{
goto v___jp_2221_;
}
else
{
lean_object* v___x_2236_; 
lean_del_object(v___x_2219_);
lean_dec(v_value_2216_);
lean_dec(v_key_2215_);
v___x_2236_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2236_, 0, v_a_2212_);
lean_ctor_set(v___x_2236_, 1, v_b_2213_);
lean_ctor_set(v___x_2236_, 2, v_tail_2217_);
return v___x_2236_;
}
}
v___jp_2221_:
{
lean_object* v___x_2222_; lean_object* v___x_2224_; 
v___x_2222_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__11___redArg(v_a_2212_, v_b_2213_, v_tail_2217_);
if (v_isShared_2220_ == 0)
{
lean_ctor_set(v___x_2219_, 2, v___x_2222_);
v___x_2224_ = v___x_2219_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_key_2215_);
lean_ctor_set(v_reuseFailAlloc_2225_, 1, v_value_2216_);
lean_ctor_set(v_reuseFailAlloc_2225_, 2, v___x_2222_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10_spec__11_spec__12___redArg(lean_object* v_x_2238_, lean_object* v_x_2239_){
_start:
{
if (lean_obj_tag(v_x_2239_) == 0)
{
return v_x_2238_;
}
else
{
lean_object* v_key_2240_; lean_object* v_value_2241_; lean_object* v_tail_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2274_; 
v_key_2240_ = lean_ctor_get(v_x_2239_, 0);
v_value_2241_ = lean_ctor_get(v_x_2239_, 1);
v_tail_2242_ = lean_ctor_get(v_x_2239_, 2);
v_isSharedCheck_2274_ = !lean_is_exclusive(v_x_2239_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2244_ = v_x_2239_;
v_isShared_2245_ = v_isSharedCheck_2274_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_tail_2242_);
lean_inc(v_value_2241_);
lean_inc(v_key_2240_);
lean_dec(v_x_2239_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2274_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v_fst_2246_; lean_object* v_snd_2247_; lean_object* v___x_2248_; size_t v___x_2249_; size_t v___x_2250_; size_t v___x_2251_; uint64_t v___x_2252_; size_t v___x_2253_; size_t v___x_2254_; uint64_t v___x_2255_; uint64_t v___x_2256_; uint64_t v___x_2257_; uint64_t v___x_2258_; uint64_t v_fold_2259_; uint64_t v___x_2260_; uint64_t v___x_2261_; uint64_t v___x_2262_; size_t v___x_2263_; size_t v___x_2264_; size_t v___x_2265_; size_t v___x_2266_; size_t v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2270_; 
v_fst_2246_ = lean_ctor_get(v_key_2240_, 0);
v_snd_2247_ = lean_ctor_get(v_key_2240_, 1);
v___x_2248_ = lean_array_get_size(v_x_2238_);
v___x_2249_ = lean_ptr_addr(v_fst_2246_);
v___x_2250_ = ((size_t)3ULL);
v___x_2251_ = lean_usize_shift_right(v___x_2249_, v___x_2250_);
v___x_2252_ = lean_usize_to_uint64(v___x_2251_);
v___x_2253_ = lean_ptr_addr(v_snd_2247_);
v___x_2254_ = lean_usize_shift_right(v___x_2253_, v___x_2250_);
v___x_2255_ = lean_usize_to_uint64(v___x_2254_);
v___x_2256_ = lean_uint64_mix_hash(v___x_2252_, v___x_2255_);
v___x_2257_ = 32ULL;
v___x_2258_ = lean_uint64_shift_right(v___x_2256_, v___x_2257_);
v_fold_2259_ = lean_uint64_xor(v___x_2256_, v___x_2258_);
v___x_2260_ = 16ULL;
v___x_2261_ = lean_uint64_shift_right(v_fold_2259_, v___x_2260_);
v___x_2262_ = lean_uint64_xor(v_fold_2259_, v___x_2261_);
v___x_2263_ = lean_uint64_to_usize(v___x_2262_);
v___x_2264_ = lean_usize_of_nat(v___x_2248_);
v___x_2265_ = ((size_t)1ULL);
v___x_2266_ = lean_usize_sub(v___x_2264_, v___x_2265_);
v___x_2267_ = lean_usize_land(v___x_2263_, v___x_2266_);
v___x_2268_ = lean_array_uget_borrowed(v_x_2238_, v___x_2267_);
lean_inc(v___x_2268_);
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 2, v___x_2268_);
v___x_2270_ = v___x_2244_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_key_2240_);
lean_ctor_set(v_reuseFailAlloc_2273_, 1, v_value_2241_);
lean_ctor_set(v_reuseFailAlloc_2273_, 2, v___x_2268_);
v___x_2270_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
lean_object* v___x_2271_; 
v___x_2271_ = lean_array_uset(v_x_2238_, v___x_2267_, v___x_2270_);
v_x_2238_ = v___x_2271_;
v_x_2239_ = v_tail_2242_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10_spec__11___redArg(lean_object* v_i_2275_, lean_object* v_source_2276_, lean_object* v_target_2277_){
_start:
{
lean_object* v___x_2278_; uint8_t v___x_2279_; 
v___x_2278_ = lean_array_get_size(v_source_2276_);
v___x_2279_ = lean_nat_dec_lt(v_i_2275_, v___x_2278_);
if (v___x_2279_ == 0)
{
lean_dec_ref(v_source_2276_);
lean_dec(v_i_2275_);
return v_target_2277_;
}
else
{
lean_object* v_es_2280_; lean_object* v___x_2281_; lean_object* v_source_2282_; lean_object* v_target_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v_es_2280_ = lean_array_fget(v_source_2276_, v_i_2275_);
v___x_2281_ = lean_box(0);
v_source_2282_ = lean_array_fset(v_source_2276_, v_i_2275_, v___x_2281_);
v_target_2283_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10_spec__11_spec__12___redArg(v_target_2277_, v_es_2280_);
v___x_2284_ = lean_unsigned_to_nat(1u);
v___x_2285_ = lean_nat_add(v_i_2275_, v___x_2284_);
lean_dec(v_i_2275_);
v_i_2275_ = v___x_2285_;
v_source_2276_ = v_source_2282_;
v_target_2277_ = v_target_2283_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10___redArg(lean_object* v_data_2287_){
_start:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v_nbuckets_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2288_ = lean_array_get_size(v_data_2287_);
v___x_2289_ = lean_unsigned_to_nat(2u);
v_nbuckets_2290_ = lean_nat_mul(v___x_2288_, v___x_2289_);
v___x_2291_ = lean_unsigned_to_nat(0u);
v___x_2292_ = lean_box(0);
v___x_2293_ = lean_mk_array(v_nbuckets_2290_, v___x_2292_);
v___x_2294_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10_spec__11___redArg(v___x_2291_, v_data_2287_, v___x_2293_);
return v___x_2294_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7___redArg(lean_object* v_m_2295_, lean_object* v_a_2296_, lean_object* v_b_2297_){
_start:
{
lean_object* v_size_2298_; lean_object* v_buckets_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2351_; 
v_size_2298_ = lean_ctor_get(v_m_2295_, 0);
v_buckets_2299_ = lean_ctor_get(v_m_2295_, 1);
v_isSharedCheck_2351_ = !lean_is_exclusive(v_m_2295_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2301_ = v_m_2295_;
v_isShared_2302_ = v_isSharedCheck_2351_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_buckets_2299_);
lean_inc(v_size_2298_);
lean_dec(v_m_2295_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2351_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v_fst_2303_; lean_object* v_snd_2304_; lean_object* v___x_2305_; size_t v___x_2306_; size_t v___x_2307_; size_t v___x_2308_; uint64_t v___x_2309_; size_t v___x_2310_; size_t v___x_2311_; uint64_t v___x_2312_; uint64_t v___x_2313_; uint64_t v___x_2314_; uint64_t v___x_2315_; uint64_t v_fold_2316_; uint64_t v___x_2317_; uint64_t v___x_2318_; uint64_t v___x_2319_; size_t v___x_2320_; size_t v___x_2321_; size_t v___x_2322_; size_t v___x_2323_; size_t v___x_2324_; lean_object* v_bkt_2325_; uint8_t v___x_2326_; 
v_fst_2303_ = lean_ctor_get(v_a_2296_, 0);
v_snd_2304_ = lean_ctor_get(v_a_2296_, 1);
v___x_2305_ = lean_array_get_size(v_buckets_2299_);
v___x_2306_ = lean_ptr_addr(v_fst_2303_);
v___x_2307_ = ((size_t)3ULL);
v___x_2308_ = lean_usize_shift_right(v___x_2306_, v___x_2307_);
v___x_2309_ = lean_usize_to_uint64(v___x_2308_);
v___x_2310_ = lean_ptr_addr(v_snd_2304_);
v___x_2311_ = lean_usize_shift_right(v___x_2310_, v___x_2307_);
v___x_2312_ = lean_usize_to_uint64(v___x_2311_);
v___x_2313_ = lean_uint64_mix_hash(v___x_2309_, v___x_2312_);
v___x_2314_ = 32ULL;
v___x_2315_ = lean_uint64_shift_right(v___x_2313_, v___x_2314_);
v_fold_2316_ = lean_uint64_xor(v___x_2313_, v___x_2315_);
v___x_2317_ = 16ULL;
v___x_2318_ = lean_uint64_shift_right(v_fold_2316_, v___x_2317_);
v___x_2319_ = lean_uint64_xor(v_fold_2316_, v___x_2318_);
v___x_2320_ = lean_uint64_to_usize(v___x_2319_);
v___x_2321_ = lean_usize_of_nat(v___x_2305_);
v___x_2322_ = ((size_t)1ULL);
v___x_2323_ = lean_usize_sub(v___x_2321_, v___x_2322_);
v___x_2324_ = lean_usize_land(v___x_2320_, v___x_2323_);
v_bkt_2325_ = lean_array_uget_borrowed(v_buckets_2299_, v___x_2324_);
v___x_2326_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9___redArg(v_a_2296_, v_bkt_2325_);
if (v___x_2326_ == 0)
{
lean_object* v___x_2327_; lean_object* v_size_x27_2328_; lean_object* v___x_2329_; lean_object* v_buckets_x27_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; uint8_t v___x_2336_; 
v___x_2327_ = lean_unsigned_to_nat(1u);
v_size_x27_2328_ = lean_nat_add(v_size_2298_, v___x_2327_);
lean_dec(v_size_2298_);
lean_inc(v_bkt_2325_);
v___x_2329_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2329_, 0, v_a_2296_);
lean_ctor_set(v___x_2329_, 1, v_b_2297_);
lean_ctor_set(v___x_2329_, 2, v_bkt_2325_);
v_buckets_x27_2330_ = lean_array_uset(v_buckets_2299_, v___x_2324_, v___x_2329_);
v___x_2331_ = lean_unsigned_to_nat(4u);
v___x_2332_ = lean_nat_mul(v_size_x27_2328_, v___x_2331_);
v___x_2333_ = lean_unsigned_to_nat(3u);
v___x_2334_ = lean_nat_div(v___x_2332_, v___x_2333_);
lean_dec(v___x_2332_);
v___x_2335_ = lean_array_get_size(v_buckets_x27_2330_);
v___x_2336_ = lean_nat_dec_le(v___x_2334_, v___x_2335_);
lean_dec(v___x_2334_);
if (v___x_2336_ == 0)
{
lean_object* v_val_2337_; lean_object* v___x_2339_; 
v_val_2337_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10___redArg(v_buckets_x27_2330_);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 1, v_val_2337_);
lean_ctor_set(v___x_2301_, 0, v_size_x27_2328_);
v___x_2339_ = v___x_2301_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_size_x27_2328_);
lean_ctor_set(v_reuseFailAlloc_2340_, 1, v_val_2337_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
else
{
lean_object* v___x_2342_; 
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 1, v_buckets_x27_2330_);
lean_ctor_set(v___x_2301_, 0, v_size_x27_2328_);
v___x_2342_ = v___x_2301_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_size_x27_2328_);
lean_ctor_set(v_reuseFailAlloc_2343_, 1, v_buckets_x27_2330_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
else
{
lean_object* v___x_2344_; lean_object* v_buckets_x27_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2349_; 
lean_inc(v_bkt_2325_);
v___x_2344_ = lean_box(0);
v_buckets_x27_2345_ = lean_array_uset(v_buckets_2299_, v___x_2324_, v___x_2344_);
v___x_2346_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__11___redArg(v_a_2296_, v_b_2297_, v_bkt_2325_);
v___x_2347_ = lean_array_uset(v_buckets_x27_2345_, v___x_2324_, v___x_2346_);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 1, v___x_2347_);
v___x_2349_ = v___x_2301_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_size_2298_);
lean_ctor_set(v_reuseFailAlloc_2350_, 1, v___x_2347_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__1(void){
_start:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___x_2353_ = ((lean_object*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__0));
v___x_2354_ = l_Lean_stringToMessageData(v___x_2353_);
return v___x_2354_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__2(void){
_start:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2355_ = lean_unsigned_to_nat(32u);
v___x_2356_ = lean_mk_empty_array_with_capacity(v___x_2355_);
v___x_2357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2356_);
return v___x_2357_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__3(void){
_start:
{
size_t v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2358_ = ((size_t)5ULL);
v___x_2359_ = lean_unsigned_to_nat(0u);
v___x_2360_ = lean_unsigned_to_nat(32u);
v___x_2361_ = lean_mk_empty_array_with_capacity(v___x_2360_);
v___x_2362_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__2);
v___x_2363_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2363_, 0, v___x_2362_);
lean_ctor_set(v___x_2363_, 1, v___x_2361_);
lean_ctor_set(v___x_2363_, 2, v___x_2359_);
lean_ctor_set(v___x_2363_, 3, v___x_2359_);
lean_ctor_set_usize(v___x_2363_, 4, v___x_2358_);
return v___x_2363_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2(void){
_start:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2366_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__2));
v___x_2367_ = lean_unsigned_to_nat(73u);
v___x_2368_ = lean_unsigned_to_nat(213u);
v___x_2369_ = ((lean_object*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__1));
v___x_2370_ = ((lean_object*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__0));
v___x_2371_ = l_mkPanicMessageWithDecl(v___x_2370_, v___x_2369_, v___x_2368_, v___x_2367_, v___x_2366_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit(lean_object* v_xs_2372_, lean_object* v_e_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_){
_start:
{
switch(lean_obj_tag(v_e_2373_))
{
case 0:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; 
lean_dec_ref_known(v_e_2373_, 1);
lean_dec_ref(v_xs_2372_);
v___x_2382_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2);
v___x_2383_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(v___x_2382_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
return v___x_2383_;
}
case 1:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; 
lean_dec_ref_known(v_e_2373_, 1);
lean_dec_ref(v_xs_2372_);
v___x_2384_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2);
v___x_2385_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(v___x_2384_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
return v___x_2385_;
}
case 2:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; 
lean_dec_ref_known(v_e_2373_, 1);
lean_dec_ref(v_xs_2372_);
v___x_2386_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2);
v___x_2387_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(v___x_2386_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
return v___x_2387_;
}
case 3:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; 
lean_dec_ref_known(v_e_2373_, 1);
lean_dec_ref(v_xs_2372_);
v___x_2388_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2);
v___x_2389_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(v___x_2388_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
return v___x_2389_;
}
case 4:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
lean_dec_ref_known(v_e_2373_, 2);
lean_dec_ref(v_xs_2372_);
v___x_2390_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2);
v___x_2391_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(v___x_2390_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
return v___x_2391_;
}
case 5:
{
lean_object* v_fn_2392_; lean_object* v_arg_2393_; lean_object* v___x_2394_; 
v_fn_2392_ = lean_ctor_get(v_e_2373_, 0);
v_arg_2393_ = lean_ctor_get(v_e_2373_, 1);
lean_inc_ref(v_fn_2392_);
lean_inc_ref(v_xs_2372_);
v___x_2394_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v_xs_2372_, v_fn_2392_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_object* v_a_2395_; lean_object* v___x_2396_; 
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
lean_inc(v_a_2395_);
lean_dec_ref_known(v___x_2394_, 1);
lean_inc_ref(v_arg_2393_);
v___x_2396_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v_xs_2372_, v_arg_2393_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2412_; 
v_a_2397_ = lean_ctor_get(v___x_2396_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2399_ = v___x_2396_;
v_isShared_2400_ = v_isSharedCheck_2412_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2396_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2412_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
size_t v___x_2401_; size_t v___x_2402_; uint8_t v___x_2403_; 
v___x_2401_ = lean_ptr_addr(v_fn_2392_);
v___x_2402_ = lean_ptr_addr(v_a_2395_);
v___x_2403_ = lean_usize_dec_eq(v___x_2401_, v___x_2402_);
if (v___x_2403_ == 0)
{
lean_object* v___x_2404_; 
lean_del_object(v___x_2399_);
lean_dec_ref_known(v_e_2373_, 2);
v___x_2404_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1___redArg(v_a_2395_, v_a_2397_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
return v___x_2404_;
}
else
{
size_t v___x_2405_; size_t v___x_2406_; uint8_t v___x_2407_; 
v___x_2405_ = lean_ptr_addr(v_arg_2393_);
v___x_2406_ = lean_ptr_addr(v_a_2397_);
v___x_2407_ = lean_usize_dec_eq(v___x_2405_, v___x_2406_);
if (v___x_2407_ == 0)
{
lean_object* v___x_2408_; 
lean_del_object(v___x_2399_);
lean_dec_ref_known(v_e_2373_, 2);
v___x_2408_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1___redArg(v_a_2395_, v_a_2397_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
return v___x_2408_;
}
else
{
lean_object* v___x_2410_; 
lean_dec(v_a_2397_);
lean_dec(v_a_2395_);
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 0, v_e_2373_);
v___x_2410_ = v___x_2399_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_e_2373_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
}
}
else
{
lean_dec(v_a_2395_);
lean_dec_ref_known(v_e_2373_, 2);
return v___x_2396_;
}
}
else
{
lean_dec_ref_known(v_e_2373_, 2);
lean_dec_ref(v_xs_2372_);
return v___x_2394_;
}
}
case 8:
{
lean_object* v_declName_2413_; lean_object* v_type_2414_; lean_object* v_value_2415_; lean_object* v_body_2416_; uint8_t v_nondep_2417_; lean_object* v___x_2418_; 
v_declName_2413_ = lean_ctor_get(v_e_2373_, 0);
lean_inc(v_declName_2413_);
v_type_2414_ = lean_ctor_get(v_e_2373_, 1);
lean_inc_ref(v_type_2414_);
v_value_2415_ = lean_ctor_get(v_e_2373_, 2);
lean_inc_ref(v_value_2415_);
v_body_2416_ = lean_ctor_get(v_e_2373_, 3);
lean_inc_ref(v_body_2416_);
v_nondep_2417_ = lean_ctor_get_uint8(v_e_2373_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2373_, 4);
lean_inc_ref(v_xs_2372_);
v___x_2418_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v_xs_2372_, v_type_2414_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
if (lean_obj_tag(v___x_2418_) == 0)
{
lean_object* v_a_2419_; lean_object* v___x_2420_; 
v_a_2419_ = lean_ctor_get(v___x_2418_, 0);
lean_inc(v_a_2419_);
lean_dec_ref_known(v___x_2418_, 1);
lean_inc_ref(v_xs_2372_);
v___x_2420_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v_xs_2372_, v_value_2415_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
if (lean_obj_tag(v___x_2420_) == 0)
{
lean_object* v_a_2421_; lean_object* v___x_2422_; 
v_a_2421_ = lean_ctor_get(v___x_2420_, 0);
lean_inc(v_a_2421_);
lean_dec_ref_known(v___x_2420_, 1);
v___x_2422_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl(v_declName_2413_, v_a_2419_, v_a_2421_, v_nondep_2417_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_object* v_a_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v_a_2423_ = lean_ctor_get(v___x_2422_, 0);
lean_inc(v_a_2423_);
lean_dec_ref_known(v___x_2422_, 1);
v___x_2424_ = l_Lean_PersistentArray_push___redArg(v_xs_2372_, v_a_2423_);
v___x_2425_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v___x_2424_, v_body_2416_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
return v___x_2425_;
}
else
{
lean_dec_ref(v_body_2416_);
lean_dec_ref(v_xs_2372_);
return v___x_2422_;
}
}
else
{
lean_dec(v_a_2419_);
lean_dec_ref(v_body_2416_);
lean_dec(v_declName_2413_);
lean_dec_ref(v_xs_2372_);
return v___x_2420_;
}
}
else
{
lean_dec_ref(v_body_2416_);
lean_dec_ref(v_value_2415_);
lean_dec(v_declName_2413_);
lean_dec_ref(v_xs_2372_);
return v___x_2418_;
}
}
case 9:
{
lean_object* v___x_2426_; lean_object* v___x_2427_; 
lean_dec_ref_known(v_e_2373_, 1);
lean_dec_ref(v_xs_2372_);
v___x_2426_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2);
v___x_2427_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(v___x_2426_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
return v___x_2427_;
}
case 10:
{
lean_object* v_data_2428_; lean_object* v_expr_2429_; lean_object* v___x_2430_; 
v_data_2428_ = lean_ctor_get(v_e_2373_, 0);
v_expr_2429_ = lean_ctor_get(v_e_2373_, 1);
lean_inc_ref(v_expr_2429_);
v___x_2430_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v_xs_2372_, v_expr_2429_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
if (lean_obj_tag(v___x_2430_) == 0)
{
lean_object* v_a_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2442_; 
v_a_2431_ = lean_ctor_get(v___x_2430_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2433_ = v___x_2430_;
v_isShared_2434_ = v_isSharedCheck_2442_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_a_2431_);
lean_dec(v___x_2430_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2442_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
size_t v___x_2435_; size_t v___x_2436_; uint8_t v___x_2437_; 
v___x_2435_ = lean_ptr_addr(v_expr_2429_);
v___x_2436_ = lean_ptr_addr(v_a_2431_);
v___x_2437_ = lean_usize_dec_eq(v___x_2435_, v___x_2436_);
if (v___x_2437_ == 0)
{
lean_object* v___x_2438_; 
lean_inc(v_data_2428_);
lean_del_object(v___x_2433_);
lean_dec_ref_known(v_e_2373_, 2);
v___x_2438_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2___redArg(v_data_2428_, v_a_2431_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
return v___x_2438_;
}
else
{
lean_object* v___x_2440_; 
lean_dec(v_a_2431_);
if (v_isShared_2434_ == 0)
{
lean_ctor_set(v___x_2433_, 0, v_e_2373_);
v___x_2440_ = v___x_2433_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_e_2373_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2373_, 2);
return v___x_2430_;
}
}
case 11:
{
lean_object* v_typeName_2443_; lean_object* v_idx_2444_; lean_object* v_struct_2445_; lean_object* v___x_2446_; 
v_typeName_2443_ = lean_ctor_get(v_e_2373_, 0);
v_idx_2444_ = lean_ctor_get(v_e_2373_, 1);
v_struct_2445_ = lean_ctor_get(v_e_2373_, 2);
lean_inc_ref(v_struct_2445_);
v___x_2446_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v_xs_2372_, v_struct_2445_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
if (lean_obj_tag(v___x_2446_) == 0)
{
lean_object* v_a_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2458_; 
v_a_2447_ = lean_ctor_get(v___x_2446_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2449_ = v___x_2446_;
v_isShared_2450_ = v_isSharedCheck_2458_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_a_2447_);
lean_dec(v___x_2446_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2458_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
size_t v___x_2451_; size_t v___x_2452_; uint8_t v___x_2453_; 
v___x_2451_ = lean_ptr_addr(v_struct_2445_);
v___x_2452_ = lean_ptr_addr(v_a_2447_);
v___x_2453_ = lean_usize_dec_eq(v___x_2451_, v___x_2452_);
if (v___x_2453_ == 0)
{
lean_object* v___x_2454_; 
lean_inc(v_idx_2444_);
lean_inc(v_typeName_2443_);
lean_del_object(v___x_2449_);
lean_dec_ref_known(v_e_2373_, 3);
v___x_2454_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3___redArg(v_typeName_2443_, v_idx_2444_, v_a_2447_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
return v___x_2454_;
}
else
{
lean_object* v___x_2456_; 
lean_dec(v_a_2447_);
if (v_isShared_2450_ == 0)
{
lean_ctor_set(v___x_2449_, 0, v_e_2373_);
v___x_2456_ = v___x_2449_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_e_2373_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2373_, 3);
return v___x_2446_;
}
}
default: 
{
lean_object* v___x_2459_; 
v___x_2459_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg(v_xs_2372_, v_e_2373_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
return v___x_2459_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(lean_object* v_xs_2460_, lean_object* v_e_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_){
_start:
{
switch(lean_obj_tag(v_e_2461_))
{
case 0:
{
lean_object* v_deBruijnIndex_2470_; lean_object* v_size_2471_; uint8_t v___x_2472_; 
v_deBruijnIndex_2470_ = lean_ctor_get(v_e_2461_, 0);
lean_inc(v_deBruijnIndex_2470_);
lean_dec_ref_known(v_e_2461_, 1);
v_size_2471_ = lean_ctor_get(v_xs_2460_, 2);
v___x_2472_ = lean_nat_dec_lt(v_deBruijnIndex_2470_, v_size_2471_);
if (v___x_2472_ == 0)
{
lean_object* v___x_2473_; lean_object* v___x_2474_; 
lean_dec(v_deBruijnIndex_2470_);
lean_dec_ref(v_xs_2460_);
v___x_2473_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__1, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__1_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__1);
v___x_2474_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5___redArg(v___x_2473_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_);
return v___x_2474_;
}
else
{
lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2475_ = l_Lean_instInhabitedExpr;
v___x_2476_ = lean_nat_sub(v_size_2471_, v_deBruijnIndex_2470_);
lean_dec(v_deBruijnIndex_2470_);
v___x_2477_ = lean_unsigned_to_nat(1u);
v___x_2478_ = lean_nat_sub(v___x_2476_, v___x_2477_);
lean_dec(v___x_2476_);
v___x_2479_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2475_, v_xs_2460_, v___x_2478_);
lean_dec(v___x_2478_);
lean_dec_ref(v_xs_2460_);
v___x_2480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2479_);
return v___x_2480_;
}
}
case 1:
{
lean_object* v___x_2481_; 
lean_dec_ref(v_xs_2460_);
v___x_2481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2481_, 0, v_e_2461_);
return v___x_2481_;
}
case 2:
{
lean_object* v___x_2482_; 
lean_dec_ref(v_xs_2460_);
v___x_2482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2482_, 0, v_e_2461_);
return v___x_2482_;
}
case 3:
{
lean_object* v___x_2483_; 
lean_dec_ref(v_xs_2460_);
v___x_2483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2483_, 0, v_e_2461_);
return v___x_2483_;
}
case 4:
{
lean_object* v___x_2484_; 
lean_dec_ref(v_xs_2460_);
v___x_2484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2484_, 0, v_e_2461_);
return v___x_2484_;
}
case 9:
{
lean_object* v___x_2485_; 
lean_dec_ref(v_xs_2460_);
v___x_2485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2485_, 0, v_e_2461_);
return v___x_2485_;
}
default: 
{
uint8_t v___x_2486_; 
v___x_2486_ = l_Lean_Expr_hasLooseBVars(v_e_2461_);
if (v___x_2486_ == 0)
{
lean_object* v___x_2487_; 
lean_dec_ref(v_xs_2460_);
lean_inc_ref(v_e_2461_);
v___x_2487_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet(v_e_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_);
if (lean_obj_tag(v___x_2487_) == 0)
{
lean_object* v_a_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2528_; 
v_a_2488_ = lean_ctor_get(v___x_2487_, 0);
v_isSharedCheck_2528_ = !lean_is_exclusive(v___x_2487_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2490_ = v___x_2487_;
v_isShared_2491_ = v_isSharedCheck_2528_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_a_2488_);
lean_dec(v___x_2487_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2528_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
uint8_t v___x_2492_; 
v___x_2492_ = lean_unbox(v_a_2488_);
lean_dec(v_a_2488_);
if (v___x_2492_ == 0)
{
lean_object* v___x_2494_; 
if (v_isShared_2491_ == 0)
{
lean_ctor_set(v___x_2490_, 0, v_e_2461_);
v___x_2494_ = v___x_2490_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_e_2461_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
else
{
lean_object* v___x_2496_; lean_object* v_cacheClosed_2497_; lean_object* v___x_2498_; 
v___x_2496_ = lean_st_ref_get(v_a_2462_);
v_cacheClosed_2497_ = lean_ctor_get(v___x_2496_, 1);
lean_inc_ref(v_cacheClosed_2497_);
lean_dec(v___x_2496_);
v___x_2498_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0___redArg(v_cacheClosed_2497_, v_e_2461_);
lean_dec_ref(v_cacheClosed_2497_);
if (lean_obj_tag(v___x_2498_) == 1)
{
lean_object* v_val_2499_; lean_object* v___x_2501_; 
lean_dec_ref(v_e_2461_);
v_val_2499_ = lean_ctor_get(v___x_2498_, 0);
lean_inc(v_val_2499_);
lean_dec_ref_known(v___x_2498_, 1);
if (v_isShared_2491_ == 0)
{
lean_ctor_set(v___x_2490_, 0, v_val_2499_);
v___x_2501_ = v___x_2490_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_val_2499_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
else
{
lean_object* v___x_2503_; lean_object* v___x_2504_; 
lean_dec(v___x_2498_);
lean_del_object(v___x_2490_);
v___x_2503_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__3, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__3_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__3);
lean_inc_ref(v_e_2461_);
v___x_2504_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit(v___x_2503_, v_e_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_);
if (lean_obj_tag(v___x_2504_) == 0)
{
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2527_; 
v_a_2505_ = lean_ctor_get(v___x_2504_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2507_ = v___x_2504_;
v_isShared_2508_ = v_isSharedCheck_2527_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2504_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2527_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2509_; lean_object* v_cache_2510_; lean_object* v_cacheClosed_2511_; lean_object* v_hasLetCache_2512_; lean_object* v_decls_2513_; lean_object* v_valueMap_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2526_; 
v___x_2509_ = lean_st_ref_take(v_a_2462_);
v_cache_2510_ = lean_ctor_get(v___x_2509_, 0);
v_cacheClosed_2511_ = lean_ctor_get(v___x_2509_, 1);
v_hasLetCache_2512_ = lean_ctor_get(v___x_2509_, 2);
v_decls_2513_ = lean_ctor_get(v___x_2509_, 3);
v_valueMap_2514_ = lean_ctor_get(v___x_2509_, 4);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2516_ = v___x_2509_;
v_isShared_2517_ = v_isSharedCheck_2526_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_valueMap_2514_);
lean_inc(v_decls_2513_);
lean_inc(v_hasLetCache_2512_);
lean_inc(v_cacheClosed_2511_);
lean_inc(v_cache_2510_);
lean_dec(v___x_2509_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2526_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2518_; lean_object* v___x_2520_; 
lean_inc(v_a_2505_);
v___x_2518_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1___redArg(v_cacheClosed_2511_, v_e_2461_, v_a_2505_);
if (v_isShared_2517_ == 0)
{
lean_ctor_set(v___x_2516_, 1, v___x_2518_);
v___x_2520_ = v___x_2516_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_cache_2510_);
lean_ctor_set(v_reuseFailAlloc_2525_, 1, v___x_2518_);
lean_ctor_set(v_reuseFailAlloc_2525_, 2, v_hasLetCache_2512_);
lean_ctor_set(v_reuseFailAlloc_2525_, 3, v_decls_2513_);
lean_ctor_set(v_reuseFailAlloc_2525_, 4, v_valueMap_2514_);
v___x_2520_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
lean_object* v___x_2521_; lean_object* v___x_2523_; 
v___x_2521_ = lean_st_ref_put(v_a_2462_, v___x_2520_);
if (v_isShared_2508_ == 0)
{
v___x_2523_ = v___x_2507_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_a_2505_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_2461_);
return v___x_2504_;
}
}
}
}
}
else
{
lean_object* v_a_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2536_; 
lean_dec_ref(v_e_2461_);
v_a_2529_ = lean_ctor_get(v___x_2487_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2487_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2531_ = v___x_2487_;
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_a_2529_);
lean_dec(v___x_2487_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v___x_2534_; 
if (v_isShared_2532_ == 0)
{
v___x_2534_ = v___x_2531_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_a_2529_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
}
}
else
{
lean_object* v___x_2537_; lean_object* v_cache_2538_; lean_object* v_key_2539_; lean_object* v___x_2540_; 
v___x_2537_ = lean_st_ref_get(v_a_2462_);
v_cache_2538_ = lean_ctor_get(v___x_2537_, 0);
lean_inc_ref(v_cache_2538_);
lean_dec(v___x_2537_);
lean_inc_ref(v_e_2461_);
lean_inc_ref(v_xs_2460_);
v_key_2539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_2539_, 0, v_xs_2460_);
lean_ctor_set(v_key_2539_, 1, v_e_2461_);
v___x_2540_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6___redArg(v_cache_2538_, v_key_2539_);
lean_dec_ref(v_cache_2538_);
if (lean_obj_tag(v___x_2540_) == 1)
{
lean_object* v_val_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2548_; 
lean_dec_ref_known(v_key_2539_, 2);
lean_dec_ref(v_e_2461_);
lean_dec_ref(v_xs_2460_);
v_val_2541_ = lean_ctor_get(v___x_2540_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2540_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2543_ = v___x_2540_;
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_val_2541_);
lean_dec(v___x_2540_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2546_; 
if (v_isShared_2544_ == 0)
{
lean_ctor_set_tag(v___x_2543_, 0);
v___x_2546_ = v___x_2543_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_val_2541_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
else
{
lean_object* v___x_2549_; 
lean_dec(v___x_2540_);
v___x_2549_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit(v_xs_2460_, v_e_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_);
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_object* v_a_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2572_; 
v_a_2550_ = lean_ctor_get(v___x_2549_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2552_ = v___x_2549_;
v_isShared_2553_ = v_isSharedCheck_2572_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_a_2550_);
lean_dec(v___x_2549_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2572_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2554_; lean_object* v_cache_2555_; lean_object* v_cacheClosed_2556_; lean_object* v_hasLetCache_2557_; lean_object* v_decls_2558_; lean_object* v_valueMap_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2571_; 
v___x_2554_ = lean_st_ref_take(v_a_2462_);
v_cache_2555_ = lean_ctor_get(v___x_2554_, 0);
v_cacheClosed_2556_ = lean_ctor_get(v___x_2554_, 1);
v_hasLetCache_2557_ = lean_ctor_get(v___x_2554_, 2);
v_decls_2558_ = lean_ctor_get(v___x_2554_, 3);
v_valueMap_2559_ = lean_ctor_get(v___x_2554_, 4);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2561_ = v___x_2554_;
v_isShared_2562_ = v_isSharedCheck_2571_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_valueMap_2559_);
lean_inc(v_decls_2558_);
lean_inc(v_hasLetCache_2557_);
lean_inc(v_cacheClosed_2556_);
lean_inc(v_cache_2555_);
lean_dec(v___x_2554_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2571_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2563_; lean_object* v___x_2565_; 
lean_inc(v_a_2550_);
v___x_2563_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7___redArg(v_cache_2555_, v_key_2539_, v_a_2550_);
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 0, v___x_2563_);
v___x_2565_ = v___x_2561_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v___x_2563_);
lean_ctor_set(v_reuseFailAlloc_2570_, 1, v_cacheClosed_2556_);
lean_ctor_set(v_reuseFailAlloc_2570_, 2, v_hasLetCache_2557_);
lean_ctor_set(v_reuseFailAlloc_2570_, 3, v_decls_2558_);
lean_ctor_set(v_reuseFailAlloc_2570_, 4, v_valueMap_2559_);
v___x_2565_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
lean_object* v___x_2566_; lean_object* v___x_2568_; 
v___x_2566_ = lean_st_ref_put(v_a_2462_, v___x_2565_);
if (v_isShared_2553_ == 0)
{
v___x_2568_ = v___x_2552_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_a_2550_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_2539_, 2);
return v___x_2549_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___boxed(lean_object* v_xs_2573_, lean_object* v_e_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_){
_start:
{
lean_object* v_res_2583_; 
v_res_2583_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v_xs_2573_, v_e_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_);
lean_dec(v_a_2581_);
lean_dec_ref(v_a_2580_);
lean_dec(v_a_2579_);
lean_dec_ref(v_a_2578_);
lean_dec(v_a_2577_);
lean_dec_ref(v_a_2576_);
lean_dec(v_a_2575_);
return v_res_2583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___boxed(lean_object* v_xs_2584_, lean_object* v_e_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_){
_start:
{
lean_object* v_res_2594_; 
v_res_2594_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit(v_xs_2584_, v_e_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_);
lean_dec(v_a_2592_);
lean_dec_ref(v_a_2591_);
lean_dec(v_a_2590_);
lean_dec_ref(v_a_2589_);
lean_dec(v_a_2588_);
lean_dec_ref(v_a_2587_);
lean_dec(v_a_2586_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5(lean_object* v_00_u03b1_2595_, lean_object* v_msg_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_){
_start:
{
lean_object* v___x_2605_; 
v___x_2605_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5___redArg(v_msg_2596_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_);
return v___x_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5___boxed(lean_object* v_00_u03b1_2606_, lean_object* v_msg_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_){
_start:
{
lean_object* v_res_2616_; 
v_res_2616_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5(v_00_u03b1_2606_, v_msg_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
return v_res_2616_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6(lean_object* v_00_u03b2_2617_, lean_object* v_m_2618_, lean_object* v_a_2619_){
_start:
{
lean_object* v___x_2620_; 
v___x_2620_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6___redArg(v_m_2618_, v_a_2619_);
return v___x_2620_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6___boxed(lean_object* v_00_u03b2_2621_, lean_object* v_m_2622_, lean_object* v_a_2623_){
_start:
{
lean_object* v_res_2624_; 
v_res_2624_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6(v_00_u03b2_2621_, v_m_2622_, v_a_2623_);
lean_dec_ref(v_a_2623_);
lean_dec_ref(v_m_2622_);
return v_res_2624_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7(lean_object* v_00_u03b2_2625_, lean_object* v_m_2626_, lean_object* v_a_2627_, lean_object* v_b_2628_){
_start:
{
lean_object* v___x_2629_; 
v___x_2629_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7___redArg(v_m_2626_, v_a_2627_, v_b_2628_);
return v___x_2629_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7(lean_object* v_00_u03b2_2630_, lean_object* v_a_2631_, lean_object* v_x_2632_){
_start:
{
lean_object* v___x_2633_; 
v___x_2633_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7___redArg(v_a_2631_, v_x_2632_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7___boxed(lean_object* v_00_u03b2_2634_, lean_object* v_a_2635_, lean_object* v_x_2636_){
_start:
{
lean_object* v_res_2637_; 
v_res_2637_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7(v_00_u03b2_2634_, v_a_2635_, v_x_2636_);
lean_dec(v_x_2636_);
lean_dec_ref(v_a_2635_);
return v_res_2637_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9(lean_object* v_00_u03b2_2638_, lean_object* v_a_2639_, lean_object* v_x_2640_){
_start:
{
uint8_t v___x_2641_; 
v___x_2641_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9___redArg(v_a_2639_, v_x_2640_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9___boxed(lean_object* v_00_u03b2_2642_, lean_object* v_a_2643_, lean_object* v_x_2644_){
_start:
{
uint8_t v_res_2645_; lean_object* v_r_2646_; 
v_res_2645_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9(v_00_u03b2_2642_, v_a_2643_, v_x_2644_);
lean_dec(v_x_2644_);
lean_dec_ref(v_a_2643_);
v_r_2646_ = lean_box(v_res_2645_);
return v_r_2646_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10(lean_object* v_00_u03b2_2647_, lean_object* v_data_2648_){
_start:
{
lean_object* v___x_2649_; 
v___x_2649_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10___redArg(v_data_2648_);
return v___x_2649_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__11(lean_object* v_00_u03b2_2650_, lean_object* v_a_2651_, lean_object* v_b_2652_, lean_object* v_x_2653_){
_start:
{
lean_object* v___x_2654_; 
v___x_2654_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__11___redArg(v_a_2651_, v_b_2652_, v_x_2653_);
return v___x_2654_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10_spec__11(lean_object* v_00_u03b2_2655_, lean_object* v_i_2656_, lean_object* v_source_2657_, lean_object* v_target_2658_){
_start:
{
lean_object* v___x_2659_; 
v___x_2659_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10_spec__11___redArg(v_i_2656_, v_source_2657_, v_target_2658_);
return v___x_2659_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10_spec__11_spec__12(lean_object* v_00_u03b2_2660_, lean_object* v_x_2661_, lean_object* v_x_2662_){
_start:
{
lean_object* v___x_2663_; 
v___x_2663_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10_spec__11_spec__12___redArg(v_x_2661_, v_x_2662_);
return v___x_2663_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3(lean_object* v_msg_2666_, uint8_t v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
lean_object* v___f_2670_; lean_object* v___f_2671_; lean_object* v___x_2672_; lean_object* v___f_2673_; lean_object* v___f_2674_; lean_object* v___f_2675_; lean_object* v___x_10670__overap_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___f_2670_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3___closed__0));
v___f_2671_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3___closed__1));
v___x_2672_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___f_2670_, v___f_2671_);
v___f_2673_ = lean_alloc_closure((void*)(l_EStateM_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2673_, 0, v___x_2672_);
v___f_2674_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2674_, 0, v___f_2673_);
v___f_2675_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2675_, 0, v___f_2674_);
v___x_10670__overap_2676_ = lean_panic_fn_borrowed(v___f_2675_, v_msg_2666_);
lean_dec_ref(v___f_2675_);
v___x_2677_ = lean_box(v___y_2667_);
lean_inc_ref(v___y_2668_);
v___x_2678_ = lean_apply_3(v___x_10670__overap_2676_, v___x_2677_, v___y_2668_, v___y_2669_);
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3___boxed(lean_object* v_msg_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_){
_start:
{
uint8_t v___y_15631__boxed_2683_; lean_object* v_res_2684_; 
v___y_15631__boxed_2683_ = lean_unbox(v___y_2680_);
v_res_2684_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3(v_msg_2679_, v___y_15631__boxed_2683_, v___y_2681_, v___y_2682_);
lean_dec_ref(v___y_2681_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4___redArg(lean_object* v_idx_2685_, lean_object* v___y_2686_){
_start:
{
lean_object* v___x_2687_; lean_object* v___x_2688_; 
v___x_2687_ = l_Lean_Expr_bvar___override(v_idx_2685_);
v___x_2688_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_2687_, v___y_2686_);
return v___x_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4(lean_object* v_idx_2689_, uint8_t v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_){
_start:
{
lean_object* v___x_2693_; 
v___x_2693_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4___redArg(v_idx_2689_, v___y_2692_);
return v___x_2693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4___boxed(lean_object* v_idx_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
uint8_t v___y_15664__boxed_2698_; lean_object* v_res_2699_; 
v___y_15664__boxed_2698_ = lean_unbox(v___y_2695_);
v_res_2699_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4(v_idx_2694_, v___y_15664__boxed_2698_, v___y_2696_, v___y_2697_);
lean_dec_ref(v___y_2696_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6___redArg(lean_object* v_x_2700_, lean_object* v_t_2701_, lean_object* v_v_2702_, lean_object* v_b_2703_, uint8_t v_nondep_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
lean_object* v___y_2713_; lean_object* v___x_2716_; uint8_t v_debug_2717_; 
v___x_2716_ = lean_st_ref_get(v___y_2706_);
v_debug_2717_ = lean_ctor_get_uint8(v___x_2716_, sizeof(void*)*11);
lean_dec(v___x_2716_);
if (v_debug_2717_ == 0)
{
v___y_2713_ = v___y_2706_;
goto v___jp_2712_;
}
else
{
lean_object* v___x_2718_; 
v___x_2718_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_2701_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_);
if (lean_obj_tag(v___x_2718_) == 0)
{
lean_object* v___x_2719_; 
lean_dec_ref_known(v___x_2718_, 1);
v___x_2719_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_v_2702_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_);
if (lean_obj_tag(v___x_2719_) == 0)
{
lean_object* v___x_2720_; 
lean_dec_ref_known(v___x_2719_, 1);
v___x_2720_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_2703_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_);
if (lean_obj_tag(v___x_2720_) == 0)
{
lean_dec_ref_known(v___x_2720_, 1);
v___y_2713_ = v___y_2706_;
goto v___jp_2712_;
}
else
{
lean_object* v_a_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2728_; 
lean_dec_ref(v_b_2703_);
lean_dec_ref(v_v_2702_);
lean_dec_ref(v_t_2701_);
lean_dec(v_x_2700_);
v_a_2721_ = lean_ctor_get(v___x_2720_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2720_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2723_ = v___x_2720_;
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_a_2721_);
lean_dec(v___x_2720_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2726_; 
if (v_isShared_2724_ == 0)
{
v___x_2726_ = v___x_2723_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_a_2721_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
return v___x_2726_;
}
}
}
}
else
{
lean_object* v_a_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2736_; 
lean_dec_ref(v_b_2703_);
lean_dec_ref(v_v_2702_);
lean_dec_ref(v_t_2701_);
lean_dec(v_x_2700_);
v_a_2729_ = lean_ctor_get(v___x_2719_, 0);
v_isSharedCheck_2736_ = !lean_is_exclusive(v___x_2719_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2731_ = v___x_2719_;
v_isShared_2732_ = v_isSharedCheck_2736_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_a_2729_);
lean_dec(v___x_2719_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2736_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
lean_object* v___x_2734_; 
if (v_isShared_2732_ == 0)
{
v___x_2734_ = v___x_2731_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v_a_2729_);
v___x_2734_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
return v___x_2734_;
}
}
}
}
else
{
lean_object* v_a_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2744_; 
lean_dec_ref(v_b_2703_);
lean_dec_ref(v_v_2702_);
lean_dec_ref(v_t_2701_);
lean_dec(v_x_2700_);
v_a_2737_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2739_ = v___x_2718_;
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_a_2737_);
lean_dec(v___x_2718_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2742_; 
if (v_isShared_2740_ == 0)
{
v___x_2742_ = v___x_2739_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_a_2737_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
}
}
v___jp_2712_:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2714_ = l_Lean_Expr_letE___override(v_x_2700_, v_t_2701_, v_v_2702_, v_b_2703_, v_nondep_2704_);
v___x_2715_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2714_, v___y_2713_);
return v___x_2715_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6___redArg___boxed(lean_object* v_x_2745_, lean_object* v_t_2746_, lean_object* v_v_2747_, lean_object* v_b_2748_, lean_object* v_nondep_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_){
_start:
{
uint8_t v_nondep_boxed_2757_; lean_object* v_res_2758_; 
v_nondep_boxed_2757_ = lean_unbox(v_nondep_2749_);
v_res_2758_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6___redArg(v_x_2745_, v_t_2746_, v_v_2747_, v_b_2748_, v_nondep_boxed_2757_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_);
lean_dec(v___y_2755_);
lean_dec_ref(v___y_2754_);
lean_dec(v___y_2753_);
lean_dec_ref(v___y_2752_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
return v_res_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6(lean_object* v_x_2759_, lean_object* v_t_2760_, lean_object* v_v_2761_, lean_object* v_b_2762_, uint8_t v_nondep_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_){
_start:
{
lean_object* v___x_2772_; 
v___x_2772_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6___redArg(v_x_2759_, v_t_2760_, v_v_2761_, v_b_2762_, v_nondep_2763_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6___boxed(lean_object* v_x_2773_, lean_object* v_t_2774_, lean_object* v_v_2775_, lean_object* v_b_2776_, lean_object* v_nondep_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_){
_start:
{
uint8_t v_nondep_boxed_2786_; lean_object* v_res_2787_; 
v_nondep_boxed_2786_ = lean_unbox(v_nondep_2777_);
v_res_2787_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6(v_x_2773_, v_t_2774_, v_v_2775_, v_b_2776_, v_nondep_boxed_2786_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_);
lean_dec(v___y_2784_);
lean_dec_ref(v___y_2783_);
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec(v___y_2780_);
lean_dec_ref(v___y_2779_);
lean_dec(v___y_2778_);
return v_res_2787_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2_spec__5___redArg(lean_object* v_a_2788_, lean_object* v_x_2789_){
_start:
{
if (lean_obj_tag(v_x_2789_) == 0)
{
lean_object* v___x_2790_; 
v___x_2790_ = lean_box(0);
return v___x_2790_;
}
else
{
lean_object* v_key_2791_; lean_object* v_value_2792_; lean_object* v_tail_2793_; uint8_t v___x_2794_; 
v_key_2791_ = lean_ctor_get(v_x_2789_, 0);
v_value_2792_ = lean_ctor_get(v_x_2789_, 1);
v_tail_2793_ = lean_ctor_get(v_x_2789_, 2);
v___x_2794_ = l_Lean_instBEqFVarId_beq(v_key_2791_, v_a_2788_);
if (v___x_2794_ == 0)
{
v_x_2789_ = v_tail_2793_;
goto _start;
}
else
{
lean_object* v___x_2796_; 
lean_inc(v_value_2792_);
v___x_2796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2796_, 0, v_value_2792_);
return v___x_2796_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2_spec__5___redArg___boxed(lean_object* v_a_2797_, lean_object* v_x_2798_){
_start:
{
lean_object* v_res_2799_; 
v_res_2799_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2_spec__5___redArg(v_a_2797_, v_x_2798_);
lean_dec(v_x_2798_);
lean_dec(v_a_2797_);
return v_res_2799_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___redArg(lean_object* v_m_2800_, lean_object* v_a_2801_){
_start:
{
lean_object* v_buckets_2802_; lean_object* v___x_2803_; uint64_t v___x_2804_; uint64_t v___x_2805_; uint64_t v___x_2806_; uint64_t v_fold_2807_; uint64_t v___x_2808_; uint64_t v___x_2809_; uint64_t v___x_2810_; size_t v___x_2811_; size_t v___x_2812_; size_t v___x_2813_; size_t v___x_2814_; size_t v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; 
v_buckets_2802_ = lean_ctor_get(v_m_2800_, 1);
v___x_2803_ = lean_array_get_size(v_buckets_2802_);
v___x_2804_ = l_Lean_instHashableFVarId_hash(v_a_2801_);
v___x_2805_ = 32ULL;
v___x_2806_ = lean_uint64_shift_right(v___x_2804_, v___x_2805_);
v_fold_2807_ = lean_uint64_xor(v___x_2804_, v___x_2806_);
v___x_2808_ = 16ULL;
v___x_2809_ = lean_uint64_shift_right(v_fold_2807_, v___x_2808_);
v___x_2810_ = lean_uint64_xor(v_fold_2807_, v___x_2809_);
v___x_2811_ = lean_uint64_to_usize(v___x_2810_);
v___x_2812_ = lean_usize_of_nat(v___x_2803_);
v___x_2813_ = ((size_t)1ULL);
v___x_2814_ = lean_usize_sub(v___x_2812_, v___x_2813_);
v___x_2815_ = lean_usize_land(v___x_2811_, v___x_2814_);
v___x_2816_ = lean_array_uget_borrowed(v_buckets_2802_, v___x_2815_);
v___x_2817_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2_spec__5___redArg(v_a_2801_, v___x_2816_);
return v___x_2817_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___redArg___boxed(lean_object* v_m_2818_, lean_object* v_a_2819_){
_start:
{
lean_object* v_res_2820_; 
v_res_2820_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___redArg(v_m_2818_, v_a_2819_);
lean_dec(v_a_2819_);
lean_dec_ref(v_m_2818_);
return v_res_2820_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2(void){
_start:
{
lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2823_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__1));
v___x_2824_ = lean_unsigned_to_nat(10u);
v___x_2825_ = lean_unsigned_to_nat(236u);
v___x_2826_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__0));
v___x_2827_ = ((lean_object*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__0));
v___x_2828_ = l_mkPanicMessageWithDecl(v___x_2827_, v___x_2826_, v___x_2825_, v___x_2824_, v___x_2823_);
return v___x_2828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5(lean_object* v___x_2829_, lean_object* v_i_2830_, lean_object* v_e_2831_, lean_object* v_offset_2832_, lean_object* v_a_2833_, uint8_t v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_){
_start:
{
switch(lean_obj_tag(v_e_2831_))
{
case 5:
{
lean_object* v_fn_2837_; lean_object* v_arg_2838_; lean_object* v___x_2839_; 
v_fn_2837_ = lean_ctor_get(v_e_2831_, 0);
v_arg_2838_ = lean_ctor_get(v_e_2831_, 1);
lean_inc(v_offset_2832_);
lean_inc_ref(v_fn_2837_);
v___x_2839_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2829_, v_i_2830_, v_fn_2837_, v_offset_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v_a_2840_; lean_object* v_a_2841_; lean_object* v_fst_2842_; lean_object* v_snd_2843_; lean_object* v___x_2844_; 
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
lean_inc(v_a_2840_);
v_a_2841_ = lean_ctor_get(v___x_2839_, 1);
lean_inc(v_a_2841_);
lean_dec_ref_known(v___x_2839_, 2);
v_fst_2842_ = lean_ctor_get(v_a_2840_, 0);
lean_inc(v_fst_2842_);
v_snd_2843_ = lean_ctor_get(v_a_2840_, 1);
lean_inc(v_snd_2843_);
lean_dec(v_a_2840_);
lean_inc_ref(v_arg_2838_);
v___x_2844_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2829_, v_i_2830_, v_arg_2838_, v_offset_2832_, v_snd_2843_, v_a_2834_, v_a_2835_, v_a_2841_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_object* v_a_2845_; lean_object* v_a_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2870_; 
v_a_2845_ = lean_ctor_get(v___x_2844_, 0);
v_a_2846_ = lean_ctor_get(v___x_2844_, 1);
v_isSharedCheck_2870_ = !lean_is_exclusive(v___x_2844_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2848_ = v___x_2844_;
v_isShared_2849_ = v_isSharedCheck_2870_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_a_2846_);
lean_inc(v_a_2845_);
lean_dec(v___x_2844_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2870_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v_fst_2850_; lean_object* v_snd_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2869_; 
v_fst_2850_ = lean_ctor_get(v_a_2845_, 0);
v_snd_2851_ = lean_ctor_get(v_a_2845_, 1);
v_isSharedCheck_2869_ = !lean_is_exclusive(v_a_2845_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2853_ = v_a_2845_;
v_isShared_2854_ = v_isSharedCheck_2869_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_snd_2851_);
lean_inc(v_fst_2850_);
lean_dec(v_a_2845_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2869_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
size_t v___x_2855_; size_t v___x_2856_; uint8_t v___x_2857_; 
v___x_2855_ = lean_ptr_addr(v_fn_2837_);
v___x_2856_ = lean_ptr_addr(v_fst_2842_);
v___x_2857_ = lean_usize_dec_eq(v___x_2855_, v___x_2856_);
if (v___x_2857_ == 0)
{
lean_object* v___x_2858_; 
lean_del_object(v___x_2853_);
lean_del_object(v___x_2848_);
lean_dec_ref_known(v_e_2831_, 2);
v___x_2858_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__1(v_fst_2842_, v_fst_2850_, v_snd_2851_, v_a_2834_, v_a_2835_, v_a_2846_);
return v___x_2858_;
}
else
{
size_t v___x_2859_; size_t v___x_2860_; uint8_t v___x_2861_; 
v___x_2859_ = lean_ptr_addr(v_arg_2838_);
v___x_2860_ = lean_ptr_addr(v_fst_2850_);
v___x_2861_ = lean_usize_dec_eq(v___x_2859_, v___x_2860_);
if (v___x_2861_ == 0)
{
lean_object* v___x_2862_; 
lean_del_object(v___x_2853_);
lean_del_object(v___x_2848_);
lean_dec_ref_known(v_e_2831_, 2);
v___x_2862_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__1(v_fst_2842_, v_fst_2850_, v_snd_2851_, v_a_2834_, v_a_2835_, v_a_2846_);
return v___x_2862_;
}
else
{
lean_object* v___x_2864_; 
lean_dec(v_fst_2850_);
lean_dec(v_fst_2842_);
if (v_isShared_2854_ == 0)
{
lean_ctor_set(v___x_2853_, 0, v_e_2831_);
v___x_2864_ = v___x_2853_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_e_2831_);
lean_ctor_set(v_reuseFailAlloc_2868_, 1, v_snd_2851_);
v___x_2864_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
lean_object* v___x_2866_; 
if (v_isShared_2849_ == 0)
{
lean_ctor_set(v___x_2848_, 0, v___x_2864_);
v___x_2866_ = v___x_2848_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v___x_2864_);
lean_ctor_set(v_reuseFailAlloc_2867_, 1, v_a_2846_);
v___x_2866_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
return v___x_2866_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_2842_);
lean_dec_ref_known(v_e_2831_, 2);
return v___x_2844_;
}
}
else
{
lean_dec_ref_known(v_e_2831_, 2);
lean_dec(v_offset_2832_);
return v___x_2839_;
}
}
case 6:
{
lean_object* v_binderName_2871_; lean_object* v_binderType_2872_; lean_object* v_body_2873_; uint8_t v_binderInfo_2874_; lean_object* v___x_2875_; 
v_binderName_2871_ = lean_ctor_get(v_e_2831_, 0);
v_binderType_2872_ = lean_ctor_get(v_e_2831_, 1);
v_body_2873_ = lean_ctor_get(v_e_2831_, 2);
v_binderInfo_2874_ = lean_ctor_get_uint8(v_e_2831_, sizeof(void*)*3 + 8);
lean_inc(v_offset_2832_);
lean_inc_ref(v_binderType_2872_);
v___x_2875_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2829_, v_i_2830_, v_binderType_2872_, v_offset_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_object* v_a_2876_; lean_object* v_a_2877_; lean_object* v_fst_2878_; lean_object* v_snd_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; 
v_a_2876_ = lean_ctor_get(v___x_2875_, 0);
lean_inc(v_a_2876_);
v_a_2877_ = lean_ctor_get(v___x_2875_, 1);
lean_inc(v_a_2877_);
lean_dec_ref_known(v___x_2875_, 2);
v_fst_2878_ = lean_ctor_get(v_a_2876_, 0);
lean_inc(v_fst_2878_);
v_snd_2879_ = lean_ctor_get(v_a_2876_, 1);
lean_inc(v_snd_2879_);
lean_dec(v_a_2876_);
v___x_2880_ = lean_unsigned_to_nat(1u);
v___x_2881_ = lean_nat_add(v_offset_2832_, v___x_2880_);
lean_dec(v_offset_2832_);
lean_inc_ref(v_body_2873_);
v___x_2882_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2829_, v_i_2830_, v_body_2873_, v___x_2881_, v_snd_2879_, v_a_2834_, v_a_2835_, v_a_2877_);
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_object* v_a_2883_; lean_object* v_a_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2908_; 
v_a_2883_ = lean_ctor_get(v___x_2882_, 0);
v_a_2884_ = lean_ctor_get(v___x_2882_, 1);
v_isSharedCheck_2908_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2886_ = v___x_2882_;
v_isShared_2887_ = v_isSharedCheck_2908_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_a_2884_);
lean_inc(v_a_2883_);
lean_dec(v___x_2882_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2908_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v_fst_2888_; lean_object* v_snd_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2907_; 
v_fst_2888_ = lean_ctor_get(v_a_2883_, 0);
v_snd_2889_ = lean_ctor_get(v_a_2883_, 1);
v_isSharedCheck_2907_ = !lean_is_exclusive(v_a_2883_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2891_ = v_a_2883_;
v_isShared_2892_ = v_isSharedCheck_2907_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_snd_2889_);
lean_inc(v_fst_2888_);
lean_dec(v_a_2883_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2907_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
size_t v___x_2893_; size_t v___x_2894_; uint8_t v___x_2895_; 
v___x_2893_ = lean_ptr_addr(v_binderType_2872_);
v___x_2894_ = lean_ptr_addr(v_fst_2878_);
v___x_2895_ = lean_usize_dec_eq(v___x_2893_, v___x_2894_);
if (v___x_2895_ == 0)
{
lean_object* v___x_2896_; 
lean_inc(v_binderName_2871_);
lean_del_object(v___x_2891_);
lean_del_object(v___x_2886_);
lean_dec_ref_known(v_e_2831_, 3);
v___x_2896_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__2(v_binderName_2871_, v_binderInfo_2874_, v_fst_2878_, v_fst_2888_, v_snd_2889_, v_a_2834_, v_a_2835_, v_a_2884_);
return v___x_2896_;
}
else
{
size_t v___x_2897_; size_t v___x_2898_; uint8_t v___x_2899_; 
v___x_2897_ = lean_ptr_addr(v_body_2873_);
v___x_2898_ = lean_ptr_addr(v_fst_2888_);
v___x_2899_ = lean_usize_dec_eq(v___x_2897_, v___x_2898_);
if (v___x_2899_ == 0)
{
lean_object* v___x_2900_; 
lean_inc(v_binderName_2871_);
lean_del_object(v___x_2891_);
lean_del_object(v___x_2886_);
lean_dec_ref_known(v_e_2831_, 3);
v___x_2900_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__2(v_binderName_2871_, v_binderInfo_2874_, v_fst_2878_, v_fst_2888_, v_snd_2889_, v_a_2834_, v_a_2835_, v_a_2884_);
return v___x_2900_;
}
else
{
lean_object* v___x_2902_; 
lean_dec(v_fst_2888_);
lean_dec(v_fst_2878_);
if (v_isShared_2892_ == 0)
{
lean_ctor_set(v___x_2891_, 0, v_e_2831_);
v___x_2902_ = v___x_2891_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_e_2831_);
lean_ctor_set(v_reuseFailAlloc_2906_, 1, v_snd_2889_);
v___x_2902_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
lean_object* v___x_2904_; 
if (v_isShared_2887_ == 0)
{
lean_ctor_set(v___x_2886_, 0, v___x_2902_);
v___x_2904_ = v___x_2886_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v___x_2902_);
lean_ctor_set(v_reuseFailAlloc_2905_, 1, v_a_2884_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_2878_);
lean_dec_ref_known(v_e_2831_, 3);
return v___x_2882_;
}
}
else
{
lean_dec_ref_known(v_e_2831_, 3);
lean_dec(v_offset_2832_);
return v___x_2875_;
}
}
case 7:
{
lean_object* v_binderName_2909_; lean_object* v_binderType_2910_; lean_object* v_body_2911_; uint8_t v_binderInfo_2912_; lean_object* v___x_2913_; 
v_binderName_2909_ = lean_ctor_get(v_e_2831_, 0);
v_binderType_2910_ = lean_ctor_get(v_e_2831_, 1);
v_body_2911_ = lean_ctor_get(v_e_2831_, 2);
v_binderInfo_2912_ = lean_ctor_get_uint8(v_e_2831_, sizeof(void*)*3 + 8);
lean_inc(v_offset_2832_);
lean_inc_ref(v_binderType_2910_);
v___x_2913_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2829_, v_i_2830_, v_binderType_2910_, v_offset_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_object* v_a_2914_; lean_object* v_a_2915_; lean_object* v_fst_2916_; lean_object* v_snd_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; 
v_a_2914_ = lean_ctor_get(v___x_2913_, 0);
lean_inc(v_a_2914_);
v_a_2915_ = lean_ctor_get(v___x_2913_, 1);
lean_inc(v_a_2915_);
lean_dec_ref_known(v___x_2913_, 2);
v_fst_2916_ = lean_ctor_get(v_a_2914_, 0);
lean_inc(v_fst_2916_);
v_snd_2917_ = lean_ctor_get(v_a_2914_, 1);
lean_inc(v_snd_2917_);
lean_dec(v_a_2914_);
v___x_2918_ = lean_unsigned_to_nat(1u);
v___x_2919_ = lean_nat_add(v_offset_2832_, v___x_2918_);
lean_dec(v_offset_2832_);
lean_inc_ref(v_body_2911_);
v___x_2920_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2829_, v_i_2830_, v_body_2911_, v___x_2919_, v_snd_2917_, v_a_2834_, v_a_2835_, v_a_2915_);
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_object* v_a_2921_; lean_object* v_a_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2946_; 
v_a_2921_ = lean_ctor_get(v___x_2920_, 0);
v_a_2922_ = lean_ctor_get(v___x_2920_, 1);
v_isSharedCheck_2946_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2924_ = v___x_2920_;
v_isShared_2925_ = v_isSharedCheck_2946_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_a_2922_);
lean_inc(v_a_2921_);
lean_dec(v___x_2920_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2946_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v_fst_2926_; lean_object* v_snd_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2945_; 
v_fst_2926_ = lean_ctor_get(v_a_2921_, 0);
v_snd_2927_ = lean_ctor_get(v_a_2921_, 1);
v_isSharedCheck_2945_ = !lean_is_exclusive(v_a_2921_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2929_ = v_a_2921_;
v_isShared_2930_ = v_isSharedCheck_2945_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_snd_2927_);
lean_inc(v_fst_2926_);
lean_dec(v_a_2921_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2945_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
size_t v___x_2931_; size_t v___x_2932_; uint8_t v___x_2933_; 
v___x_2931_ = lean_ptr_addr(v_binderType_2910_);
v___x_2932_ = lean_ptr_addr(v_fst_2916_);
v___x_2933_ = lean_usize_dec_eq(v___x_2931_, v___x_2932_);
if (v___x_2933_ == 0)
{
lean_object* v___x_2934_; 
lean_inc(v_binderName_2909_);
lean_del_object(v___x_2929_);
lean_del_object(v___x_2924_);
lean_dec_ref_known(v_e_2831_, 3);
v___x_2934_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__3(v_binderName_2909_, v_binderInfo_2912_, v_fst_2916_, v_fst_2926_, v_snd_2927_, v_a_2834_, v_a_2835_, v_a_2922_);
return v___x_2934_;
}
else
{
size_t v___x_2935_; size_t v___x_2936_; uint8_t v___x_2937_; 
v___x_2935_ = lean_ptr_addr(v_body_2911_);
v___x_2936_ = lean_ptr_addr(v_fst_2926_);
v___x_2937_ = lean_usize_dec_eq(v___x_2935_, v___x_2936_);
if (v___x_2937_ == 0)
{
lean_object* v___x_2938_; 
lean_inc(v_binderName_2909_);
lean_del_object(v___x_2929_);
lean_del_object(v___x_2924_);
lean_dec_ref_known(v_e_2831_, 3);
v___x_2938_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__3(v_binderName_2909_, v_binderInfo_2912_, v_fst_2916_, v_fst_2926_, v_snd_2927_, v_a_2834_, v_a_2835_, v_a_2922_);
return v___x_2938_;
}
else
{
lean_object* v___x_2940_; 
lean_dec(v_fst_2926_);
lean_dec(v_fst_2916_);
if (v_isShared_2930_ == 0)
{
lean_ctor_set(v___x_2929_, 0, v_e_2831_);
v___x_2940_ = v___x_2929_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_e_2831_);
lean_ctor_set(v_reuseFailAlloc_2944_, 1, v_snd_2927_);
v___x_2940_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
lean_object* v___x_2942_; 
if (v_isShared_2925_ == 0)
{
lean_ctor_set(v___x_2924_, 0, v___x_2940_);
v___x_2942_ = v___x_2924_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v___x_2940_);
lean_ctor_set(v_reuseFailAlloc_2943_, 1, v_a_2922_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_2916_);
lean_dec_ref_known(v_e_2831_, 3);
return v___x_2920_;
}
}
else
{
lean_dec_ref_known(v_e_2831_, 3);
lean_dec(v_offset_2832_);
return v___x_2913_;
}
}
case 8:
{
lean_object* v_declName_2947_; lean_object* v_type_2948_; lean_object* v_value_2949_; lean_object* v_body_2950_; uint8_t v_nondep_2951_; lean_object* v___x_2952_; 
v_declName_2947_ = lean_ctor_get(v_e_2831_, 0);
v_type_2948_ = lean_ctor_get(v_e_2831_, 1);
v_value_2949_ = lean_ctor_get(v_e_2831_, 2);
v_body_2950_ = lean_ctor_get(v_e_2831_, 3);
v_nondep_2951_ = lean_ctor_get_uint8(v_e_2831_, sizeof(void*)*4 + 8);
lean_inc(v_offset_2832_);
lean_inc_ref(v_type_2948_);
v___x_2952_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2829_, v_i_2830_, v_type_2948_, v_offset_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_);
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_object* v_a_2953_; lean_object* v_a_2954_; lean_object* v_fst_2955_; lean_object* v_snd_2956_; lean_object* v___x_2957_; 
v_a_2953_ = lean_ctor_get(v___x_2952_, 0);
lean_inc(v_a_2953_);
v_a_2954_ = lean_ctor_get(v___x_2952_, 1);
lean_inc(v_a_2954_);
lean_dec_ref_known(v___x_2952_, 2);
v_fst_2955_ = lean_ctor_get(v_a_2953_, 0);
lean_inc(v_fst_2955_);
v_snd_2956_ = lean_ctor_get(v_a_2953_, 1);
lean_inc(v_snd_2956_);
lean_dec(v_a_2953_);
lean_inc(v_offset_2832_);
lean_inc_ref(v_value_2949_);
v___x_2957_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2829_, v_i_2830_, v_value_2949_, v_offset_2832_, v_snd_2956_, v_a_2834_, v_a_2835_, v_a_2954_);
if (lean_obj_tag(v___x_2957_) == 0)
{
lean_object* v_a_2958_; lean_object* v_a_2959_; lean_object* v_fst_2960_; lean_object* v_snd_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
v_a_2958_ = lean_ctor_get(v___x_2957_, 0);
lean_inc(v_a_2958_);
v_a_2959_ = lean_ctor_get(v___x_2957_, 1);
lean_inc(v_a_2959_);
lean_dec_ref_known(v___x_2957_, 2);
v_fst_2960_ = lean_ctor_get(v_a_2958_, 0);
lean_inc(v_fst_2960_);
v_snd_2961_ = lean_ctor_get(v_a_2958_, 1);
lean_inc(v_snd_2961_);
lean_dec(v_a_2958_);
v___x_2962_ = lean_unsigned_to_nat(1u);
v___x_2963_ = lean_nat_add(v_offset_2832_, v___x_2962_);
lean_dec(v_offset_2832_);
lean_inc_ref(v_body_2950_);
v___x_2964_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2829_, v_i_2830_, v_body_2950_, v___x_2963_, v_snd_2961_, v_a_2834_, v_a_2835_, v_a_2959_);
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_object* v_a_2965_; lean_object* v_a_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2994_; 
v_a_2965_ = lean_ctor_get(v___x_2964_, 0);
v_a_2966_ = lean_ctor_get(v___x_2964_, 1);
v_isSharedCheck_2994_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2968_ = v___x_2964_;
v_isShared_2969_ = v_isSharedCheck_2994_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_a_2966_);
lean_inc(v_a_2965_);
lean_dec(v___x_2964_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2994_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v_fst_2970_; lean_object* v_snd_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2993_; 
v_fst_2970_ = lean_ctor_get(v_a_2965_, 0);
v_snd_2971_ = lean_ctor_get(v_a_2965_, 1);
v_isSharedCheck_2993_ = !lean_is_exclusive(v_a_2965_);
if (v_isSharedCheck_2993_ == 0)
{
v___x_2973_ = v_a_2965_;
v_isShared_2974_ = v_isSharedCheck_2993_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_snd_2971_);
lean_inc(v_fst_2970_);
lean_dec(v_a_2965_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2993_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
size_t v___x_2975_; size_t v___x_2976_; uint8_t v___x_2977_; 
v___x_2975_ = lean_ptr_addr(v_type_2948_);
v___x_2976_ = lean_ptr_addr(v_fst_2955_);
v___x_2977_ = lean_usize_dec_eq(v___x_2975_, v___x_2976_);
if (v___x_2977_ == 0)
{
lean_object* v___x_2978_; 
lean_inc(v_declName_2947_);
lean_del_object(v___x_2973_);
lean_del_object(v___x_2968_);
lean_dec_ref_known(v_e_2831_, 4);
v___x_2978_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4(v_declName_2947_, v_fst_2955_, v_fst_2960_, v_fst_2970_, v_nondep_2951_, v_snd_2971_, v_a_2834_, v_a_2835_, v_a_2966_);
return v___x_2978_;
}
else
{
size_t v___x_2979_; size_t v___x_2980_; uint8_t v___x_2981_; 
v___x_2979_ = lean_ptr_addr(v_value_2949_);
v___x_2980_ = lean_ptr_addr(v_fst_2960_);
v___x_2981_ = lean_usize_dec_eq(v___x_2979_, v___x_2980_);
if (v___x_2981_ == 0)
{
lean_object* v___x_2982_; 
lean_inc(v_declName_2947_);
lean_del_object(v___x_2973_);
lean_del_object(v___x_2968_);
lean_dec_ref_known(v_e_2831_, 4);
v___x_2982_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4(v_declName_2947_, v_fst_2955_, v_fst_2960_, v_fst_2970_, v_nondep_2951_, v_snd_2971_, v_a_2834_, v_a_2835_, v_a_2966_);
return v___x_2982_;
}
else
{
size_t v___x_2983_; size_t v___x_2984_; uint8_t v___x_2985_; 
v___x_2983_ = lean_ptr_addr(v_body_2950_);
v___x_2984_ = lean_ptr_addr(v_fst_2970_);
v___x_2985_ = lean_usize_dec_eq(v___x_2983_, v___x_2984_);
if (v___x_2985_ == 0)
{
lean_object* v___x_2986_; 
lean_inc(v_declName_2947_);
lean_del_object(v___x_2973_);
lean_del_object(v___x_2968_);
lean_dec_ref_known(v_e_2831_, 4);
v___x_2986_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4(v_declName_2947_, v_fst_2955_, v_fst_2960_, v_fst_2970_, v_nondep_2951_, v_snd_2971_, v_a_2834_, v_a_2835_, v_a_2966_);
return v___x_2986_;
}
else
{
lean_object* v___x_2988_; 
lean_dec(v_fst_2970_);
lean_dec(v_fst_2960_);
lean_dec(v_fst_2955_);
if (v_isShared_2974_ == 0)
{
lean_ctor_set(v___x_2973_, 0, v_e_2831_);
v___x_2988_ = v___x_2973_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v_e_2831_);
lean_ctor_set(v_reuseFailAlloc_2992_, 1, v_snd_2971_);
v___x_2988_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
lean_object* v___x_2990_; 
if (v_isShared_2969_ == 0)
{
lean_ctor_set(v___x_2968_, 0, v___x_2988_);
v___x_2990_ = v___x_2968_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v___x_2988_);
lean_ctor_set(v_reuseFailAlloc_2991_, 1, v_a_2966_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
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
lean_dec(v_fst_2960_);
lean_dec(v_fst_2955_);
lean_dec_ref_known(v_e_2831_, 4);
return v___x_2964_;
}
}
else
{
lean_dec(v_fst_2955_);
lean_dec_ref_known(v_e_2831_, 4);
lean_dec(v_offset_2832_);
return v___x_2957_;
}
}
else
{
lean_dec_ref_known(v_e_2831_, 4);
lean_dec(v_offset_2832_);
return v___x_2952_;
}
}
case 10:
{
lean_object* v_data_2995_; lean_object* v_expr_2996_; lean_object* v___x_2997_; 
v_data_2995_ = lean_ctor_get(v_e_2831_, 0);
v_expr_2996_ = lean_ctor_get(v_e_2831_, 1);
lean_inc_ref(v_expr_2996_);
v___x_2997_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2829_, v_i_2830_, v_expr_2996_, v_offset_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v_a_2998_; lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3019_; 
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
v_a_2999_ = lean_ctor_get(v___x_2997_, 1);
v_isSharedCheck_3019_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3019_ == 0)
{
v___x_3001_ = v___x_2997_;
v_isShared_3002_ = v_isSharedCheck_3019_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_inc(v_a_2998_);
lean_dec(v___x_2997_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3019_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v_fst_3003_; lean_object* v_snd_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3018_; 
v_fst_3003_ = lean_ctor_get(v_a_2998_, 0);
v_snd_3004_ = lean_ctor_get(v_a_2998_, 1);
v_isSharedCheck_3018_ = !lean_is_exclusive(v_a_2998_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_3006_ = v_a_2998_;
v_isShared_3007_ = v_isSharedCheck_3018_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_snd_3004_);
lean_inc(v_fst_3003_);
lean_dec(v_a_2998_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3018_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
size_t v___x_3008_; size_t v___x_3009_; uint8_t v___x_3010_; 
v___x_3008_ = lean_ptr_addr(v_expr_2996_);
v___x_3009_ = lean_ptr_addr(v_fst_3003_);
v___x_3010_ = lean_usize_dec_eq(v___x_3008_, v___x_3009_);
if (v___x_3010_ == 0)
{
lean_object* v___x_3011_; 
lean_inc(v_data_2995_);
lean_del_object(v___x_3006_);
lean_del_object(v___x_3001_);
lean_dec_ref_known(v_e_2831_, 2);
v___x_3011_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__5(v_data_2995_, v_fst_3003_, v_snd_3004_, v_a_2834_, v_a_2835_, v_a_2999_);
return v___x_3011_;
}
else
{
lean_object* v___x_3013_; 
lean_dec(v_fst_3003_);
if (v_isShared_3007_ == 0)
{
lean_ctor_set(v___x_3006_, 0, v_e_2831_);
v___x_3013_ = v___x_3006_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_e_2831_);
lean_ctor_set(v_reuseFailAlloc_3017_, 1, v_snd_3004_);
v___x_3013_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
lean_object* v___x_3015_; 
if (v_isShared_3002_ == 0)
{
lean_ctor_set(v___x_3001_, 0, v___x_3013_);
v___x_3015_ = v___x_3001_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v___x_3013_);
lean_ctor_set(v_reuseFailAlloc_3016_, 1, v_a_2999_);
v___x_3015_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
return v___x_3015_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2831_, 2);
return v___x_2997_;
}
}
case 11:
{
lean_object* v_typeName_3020_; lean_object* v_idx_3021_; lean_object* v_struct_3022_; lean_object* v___x_3023_; 
v_typeName_3020_ = lean_ctor_get(v_e_2831_, 0);
v_idx_3021_ = lean_ctor_get(v_e_2831_, 1);
v_struct_3022_ = lean_ctor_get(v_e_2831_, 2);
lean_inc_ref(v_struct_3022_);
v___x_3023_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2829_, v_i_2830_, v_struct_3022_, v_offset_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v_a_3024_; lean_object* v_a_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3045_; 
v_a_3024_ = lean_ctor_get(v___x_3023_, 0);
v_a_3025_ = lean_ctor_get(v___x_3023_, 1);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3027_ = v___x_3023_;
v_isShared_3028_ = v_isSharedCheck_3045_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_a_3025_);
lean_inc(v_a_3024_);
lean_dec(v___x_3023_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3045_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v_fst_3029_; lean_object* v_snd_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3044_; 
v_fst_3029_ = lean_ctor_get(v_a_3024_, 0);
v_snd_3030_ = lean_ctor_get(v_a_3024_, 1);
v_isSharedCheck_3044_ = !lean_is_exclusive(v_a_3024_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3032_ = v_a_3024_;
v_isShared_3033_ = v_isSharedCheck_3044_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_snd_3030_);
lean_inc(v_fst_3029_);
lean_dec(v_a_3024_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3044_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
size_t v___x_3034_; size_t v___x_3035_; uint8_t v___x_3036_; 
v___x_3034_ = lean_ptr_addr(v_struct_3022_);
v___x_3035_ = lean_ptr_addr(v_fst_3029_);
v___x_3036_ = lean_usize_dec_eq(v___x_3034_, v___x_3035_);
if (v___x_3036_ == 0)
{
lean_object* v___x_3037_; 
lean_inc(v_idx_3021_);
lean_inc(v_typeName_3020_);
lean_del_object(v___x_3032_);
lean_del_object(v___x_3027_);
lean_dec_ref_known(v_e_2831_, 3);
v___x_3037_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__6(v_typeName_3020_, v_idx_3021_, v_fst_3029_, v_snd_3030_, v_a_2834_, v_a_2835_, v_a_3025_);
return v___x_3037_;
}
else
{
lean_object* v___x_3039_; 
lean_dec(v_fst_3029_);
if (v_isShared_3033_ == 0)
{
lean_ctor_set(v___x_3032_, 0, v_e_2831_);
v___x_3039_ = v___x_3032_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_e_2831_);
lean_ctor_set(v_reuseFailAlloc_3043_, 1, v_snd_3030_);
v___x_3039_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
lean_object* v___x_3041_; 
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 0, v___x_3039_);
v___x_3041_ = v___x_3027_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v___x_3039_);
lean_ctor_set(v_reuseFailAlloc_3042_, 1, v_a_3025_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2831_, 3);
return v___x_3023_;
}
}
default: 
{
lean_object* v___x_3046_; lean_object* v___x_3047_; 
lean_dec(v_offset_2832_);
lean_dec_ref(v_e_2831_);
v___x_3046_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__3);
v___x_3047_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7(v___x_3046_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_);
return v___x_3047_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(lean_object* v___x_3048_, lean_object* v_i_3049_, lean_object* v_e_3050_, lean_object* v_offset_3051_, lean_object* v_a_3052_, uint8_t v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_){
_start:
{
lean_object* v_key_3056_; lean_object* v_a_3058_; lean_object* v___x_3071_; 
lean_inc(v_offset_3051_);
lean_inc_ref(v_e_3050_);
v_key_3056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_3056_, 0, v_e_3050_);
lean_ctor_set(v_key_3056_, 1, v_offset_3051_);
v___x_3071_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2___redArg(v_a_3052_, v_key_3056_);
if (lean_obj_tag(v___x_3071_) == 1)
{
lean_object* v_val_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
lean_dec_ref_known(v_key_3056_, 2);
lean_dec(v_offset_3051_);
lean_dec_ref(v_e_3050_);
v_val_3072_ = lean_ctor_get(v___x_3071_, 0);
lean_inc(v_val_3072_);
lean_dec_ref_known(v___x_3071_, 1);
v___x_3073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3073_, 0, v_val_3072_);
lean_ctor_set(v___x_3073_, 1, v_a_3052_);
v___x_3074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3074_, 0, v___x_3073_);
lean_ctor_set(v___x_3074_, 1, v_a_3055_);
return v___x_3074_;
}
else
{
lean_dec(v___x_3071_);
switch(lean_obj_tag(v_e_3050_))
{
case 1:
{
lean_object* v_fvarId_3075_; lean_object* v___x_3076_; 
v_fvarId_3075_ = lean_ctor_get(v_e_3050_, 0);
v___x_3076_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___redArg(v___x_3048_, v_fvarId_3075_);
if (lean_obj_tag(v___x_3076_) == 1)
{
lean_object* v_val_3077_; uint8_t v___x_3078_; 
v_val_3077_ = lean_ctor_get(v___x_3076_, 0);
lean_inc(v_val_3077_);
lean_dec_ref_known(v___x_3076_, 1);
v___x_3078_ = lean_nat_dec_lt(v_val_3077_, v_i_3049_);
if (v___x_3078_ == 0)
{
lean_object* v___x_3079_; lean_object* v___x_3080_; 
lean_dec(v_val_3077_);
v___x_3079_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2);
v___x_3080_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3(v___x_3079_, v_a_3053_, v_a_3054_, v_a_3055_);
if (lean_obj_tag(v___x_3080_) == 0)
{
lean_object* v_a_3081_; 
v_a_3081_ = lean_ctor_get(v___x_3080_, 0);
lean_inc(v_a_3081_);
if (lean_obj_tag(v_a_3081_) == 1)
{
lean_object* v_a_3082_; lean_object* v_val_3083_; lean_object* v___x_3084_; 
lean_dec_ref_known(v_e_3050_, 1);
lean_dec(v_offset_3051_);
v_a_3082_ = lean_ctor_get(v___x_3080_, 1);
lean_inc(v_a_3082_);
lean_dec_ref_known(v___x_3080_, 2);
v_val_3083_ = lean_ctor_get(v_a_3081_, 0);
lean_inc(v_val_3083_);
lean_dec_ref_known(v_a_3081_, 1);
v___x_3084_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3056_, v_val_3083_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3082_);
return v___x_3084_;
}
else
{
lean_object* v_a_3085_; 
lean_dec(v_a_3081_);
v_a_3085_ = lean_ctor_get(v___x_3080_, 1);
lean_inc(v_a_3085_);
lean_dec_ref_known(v___x_3080_, 2);
v_a_3058_ = v_a_3085_;
goto v___jp_3057_;
}
}
else
{
lean_object* v_a_3086_; lean_object* v_a_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3094_; 
lean_dec_ref_known(v_e_3050_, 1);
lean_dec_ref_known(v_key_3056_, 2);
lean_dec_ref(v_a_3052_);
lean_dec(v_offset_3051_);
v_a_3086_ = lean_ctor_get(v___x_3080_, 0);
v_a_3087_ = lean_ctor_get(v___x_3080_, 1);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3089_ = v___x_3080_;
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_a_3087_);
lean_inc(v_a_3086_);
lean_dec(v___x_3080_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3092_; 
if (v_isShared_3090_ == 0)
{
v___x_3092_ = v___x_3089_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_a_3086_);
lean_ctor_set(v_reuseFailAlloc_3093_, 1, v_a_3087_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
return v___x_3092_;
}
}
}
}
else
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
lean_dec_ref_known(v_e_3050_, 1);
v___x_3095_ = lean_nat_add(v_offset_3051_, v_i_3049_);
lean_dec(v_offset_3051_);
v___x_3096_ = lean_nat_sub(v___x_3095_, v_val_3077_);
lean_dec(v_val_3077_);
lean_dec(v___x_3095_);
v___x_3097_ = lean_unsigned_to_nat(1u);
v___x_3098_ = lean_nat_sub(v___x_3096_, v___x_3097_);
lean_dec(v___x_3096_);
v___x_3099_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4___redArg(v___x_3098_, v_a_3055_);
if (lean_obj_tag(v___x_3099_) == 0)
{
lean_object* v_a_3100_; lean_object* v_a_3101_; lean_object* v___x_3102_; 
v_a_3100_ = lean_ctor_get(v___x_3099_, 0);
lean_inc(v_a_3100_);
v_a_3101_ = lean_ctor_get(v___x_3099_, 1);
lean_inc(v_a_3101_);
lean_dec_ref_known(v___x_3099_, 2);
v___x_3102_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3056_, v_a_3100_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3101_);
return v___x_3102_;
}
else
{
lean_object* v_a_3103_; lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3111_; 
lean_dec_ref_known(v_key_3056_, 2);
lean_dec_ref(v_a_3052_);
v_a_3103_ = lean_ctor_get(v___x_3099_, 0);
v_a_3104_ = lean_ctor_get(v___x_3099_, 1);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3099_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3106_ = v___x_3099_;
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_inc(v_a_3103_);
lean_dec(v___x_3099_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3109_; 
if (v_isShared_3107_ == 0)
{
v___x_3109_ = v___x_3106_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_a_3103_);
lean_ctor_set(v_reuseFailAlloc_3110_, 1, v_a_3104_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
}
}
}
else
{
lean_object* v___x_3112_; 
lean_dec(v___x_3076_);
lean_dec(v_offset_3051_);
v___x_3112_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3056_, v_e_3050_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_);
return v___x_3112_;
}
}
case 9:
{
lean_object* v___x_3113_; 
lean_dec(v_offset_3051_);
v___x_3113_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3056_, v_e_3050_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_);
return v___x_3113_;
}
case 2:
{
lean_object* v___x_3114_; 
lean_dec(v_offset_3051_);
v___x_3114_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3056_, v_e_3050_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_);
return v___x_3114_;
}
case 0:
{
lean_object* v___x_3115_; 
lean_dec(v_offset_3051_);
v___x_3115_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3056_, v_e_3050_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_);
return v___x_3115_;
}
case 4:
{
lean_object* v___x_3116_; 
lean_dec(v_offset_3051_);
v___x_3116_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3056_, v_e_3050_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_);
return v___x_3116_;
}
case 3:
{
lean_object* v___x_3117_; 
lean_dec(v_offset_3051_);
v___x_3117_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3056_, v_e_3050_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_);
return v___x_3117_;
}
default: 
{
uint8_t v___x_3118_; 
v___x_3118_ = l_Lean_Expr_hasFVar(v_e_3050_);
if (v___x_3118_ == 0)
{
lean_object* v___x_3119_; 
lean_dec(v_offset_3051_);
v___x_3119_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3056_, v_e_3050_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_);
return v___x_3119_;
}
else
{
v_a_3058_ = v_a_3055_;
goto v___jp_3057_;
}
}
}
}
v___jp_3057_:
{
switch(lean_obj_tag(v_e_3050_))
{
case 9:
{
lean_object* v___x_3059_; 
lean_dec(v_offset_3051_);
v___x_3059_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3056_, v_e_3050_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3058_);
return v___x_3059_;
}
case 2:
{
lean_object* v___x_3060_; 
lean_dec(v_offset_3051_);
v___x_3060_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3056_, v_e_3050_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3058_);
return v___x_3060_;
}
case 0:
{
lean_object* v___x_3061_; 
lean_dec(v_offset_3051_);
v___x_3061_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3056_, v_e_3050_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3058_);
return v___x_3061_;
}
case 1:
{
lean_object* v___x_3062_; 
lean_dec(v_offset_3051_);
v___x_3062_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3056_, v_e_3050_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3058_);
return v___x_3062_;
}
case 4:
{
lean_object* v___x_3063_; 
lean_dec(v_offset_3051_);
v___x_3063_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3056_, v_e_3050_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3058_);
return v___x_3063_;
}
case 3:
{
lean_object* v___x_3064_; 
lean_dec(v_offset_3051_);
v___x_3064_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3056_, v_e_3050_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3058_);
return v___x_3064_;
}
default: 
{
lean_object* v___x_3065_; 
v___x_3065_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5(v___x_3048_, v_i_3049_, v_e_3050_, v_offset_3051_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3058_);
if (lean_obj_tag(v___x_3065_) == 0)
{
lean_object* v_a_3066_; lean_object* v_a_3067_; lean_object* v_fst_3068_; lean_object* v_snd_3069_; lean_object* v___x_3070_; 
v_a_3066_ = lean_ctor_get(v___x_3065_, 0);
lean_inc(v_a_3066_);
v_a_3067_ = lean_ctor_get(v___x_3065_, 1);
lean_inc(v_a_3067_);
lean_dec_ref_known(v___x_3065_, 2);
v_fst_3068_ = lean_ctor_get(v_a_3066_, 0);
lean_inc(v_fst_3068_);
v_snd_3069_ = lean_ctor_get(v_a_3066_, 1);
lean_inc(v_snd_3069_);
lean_dec(v_a_3066_);
v___x_3070_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3056_, v_fst_3068_, v_snd_3069_, v_a_3053_, v_a_3054_, v_a_3067_);
return v___x_3070_;
}
else
{
lean_dec_ref_known(v_key_3056_, 2);
return v___x_3065_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___boxed(lean_object* v___x_3120_, lean_object* v_i_3121_, lean_object* v_e_3122_, lean_object* v_offset_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_){
_start:
{
uint8_t v_a_boxed_3128_; lean_object* v_res_3129_; 
v_a_boxed_3128_ = lean_unbox(v_a_3125_);
v_res_3129_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_3120_, v_i_3121_, v_e_3122_, v_offset_3123_, v_a_3124_, v_a_boxed_3128_, v_a_3126_, v_a_3127_);
lean_dec_ref(v_a_3126_);
lean_dec(v_i_3121_);
lean_dec_ref(v___x_3120_);
return v_res_3129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5___boxed(lean_object* v___x_3130_, lean_object* v_i_3131_, lean_object* v_e_3132_, lean_object* v_offset_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_){
_start:
{
uint8_t v_a_boxed_3138_; lean_object* v_res_3139_; 
v_a_boxed_3138_ = lean_unbox(v_a_3135_);
v_res_3139_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5(v___x_3130_, v_i_3131_, v_e_3132_, v_offset_3133_, v_a_3134_, v_a_boxed_3138_, v_a_3136_, v_a_3137_);
lean_dec_ref(v_a_3136_);
lean_dec(v_i_3131_);
lean_dec_ref(v___x_3130_);
return v_res_3139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___lam__0(lean_object* v_e_3140_, lean_object* v___x_3141_, lean_object* v___x_3142_, lean_object* v_fst_3143_, lean_object* v___x_3144_, uint8_t v_debug_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_){
_start:
{
lean_object* v_a_3149_; 
switch(lean_obj_tag(v_e_3140_))
{
case 1:
{
lean_object* v_fvarId_3179_; lean_object* v___x_3180_; 
v_fvarId_3179_ = lean_ctor_get(v_e_3140_, 0);
v___x_3180_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___redArg(v_fst_3143_, v_fvarId_3179_);
if (lean_obj_tag(v___x_3180_) == 1)
{
lean_object* v_val_3181_; uint8_t v___x_3182_; 
v_val_3181_ = lean_ctor_get(v___x_3180_, 0);
lean_inc(v_val_3181_);
lean_dec_ref_known(v___x_3180_, 1);
v___x_3182_ = lean_nat_dec_lt(v_val_3181_, v___x_3144_);
if (v___x_3182_ == 0)
{
lean_object* v___x_3183_; lean_object* v___x_3184_; 
lean_dec(v_val_3181_);
v___x_3183_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2);
v___x_3184_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3(v___x_3183_, v_debug_3145_, v___y_3146_, v___y_3147_);
if (lean_obj_tag(v___x_3184_) == 0)
{
lean_object* v_a_3185_; 
v_a_3185_ = lean_ctor_get(v___x_3184_, 0);
lean_inc(v_a_3185_);
if (lean_obj_tag(v_a_3185_) == 1)
{
lean_object* v_a_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3194_; 
lean_dec_ref_known(v_e_3140_, 1);
lean_dec(v___x_3142_);
lean_dec(v___x_3141_);
v_a_3186_ = lean_ctor_get(v___x_3184_, 1);
v_isSharedCheck_3194_ = !lean_is_exclusive(v___x_3184_);
if (v_isSharedCheck_3194_ == 0)
{
lean_object* v_unused_3195_; 
v_unused_3195_ = lean_ctor_get(v___x_3184_, 0);
lean_dec(v_unused_3195_);
v___x_3188_ = v___x_3184_;
v_isShared_3189_ = v_isSharedCheck_3194_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_a_3186_);
lean_dec(v___x_3184_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3194_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v_val_3190_; lean_object* v___x_3192_; 
v_val_3190_ = lean_ctor_get(v_a_3185_, 0);
lean_inc(v_val_3190_);
lean_dec_ref_known(v_a_3185_, 1);
if (v_isShared_3189_ == 0)
{
lean_ctor_set(v___x_3188_, 0, v_val_3190_);
v___x_3192_ = v___x_3188_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_val_3190_);
lean_ctor_set(v_reuseFailAlloc_3193_, 1, v_a_3186_);
v___x_3192_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
return v___x_3192_;
}
}
}
else
{
lean_object* v_a_3196_; 
lean_dec(v_a_3185_);
v_a_3196_ = lean_ctor_get(v___x_3184_, 1);
lean_inc(v_a_3196_);
lean_dec_ref_known(v___x_3184_, 2);
v_a_3149_ = v_a_3196_;
goto v___jp_3148_;
}
}
else
{
lean_object* v_a_3197_; lean_object* v_a_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3205_; 
lean_dec_ref_known(v_e_3140_, 1);
lean_dec(v___x_3142_);
lean_dec(v___x_3141_);
v_a_3197_ = lean_ctor_get(v___x_3184_, 0);
v_a_3198_ = lean_ctor_get(v___x_3184_, 1);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3184_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3200_ = v___x_3184_;
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_a_3198_);
lean_inc(v_a_3197_);
lean_dec(v___x_3184_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v___x_3203_; 
if (v_isShared_3201_ == 0)
{
v___x_3203_ = v___x_3200_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_a_3197_);
lean_ctor_set(v_reuseFailAlloc_3204_, 1, v_a_3198_);
v___x_3203_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
return v___x_3203_;
}
}
}
}
else
{
lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; 
lean_dec_ref_known(v_e_3140_, 1);
lean_dec(v___x_3142_);
lean_dec(v___x_3141_);
v___x_3206_ = lean_nat_sub(v___x_3144_, v_val_3181_);
lean_dec(v_val_3181_);
v___x_3207_ = lean_unsigned_to_nat(1u);
v___x_3208_ = lean_nat_sub(v___x_3206_, v___x_3207_);
lean_dec(v___x_3206_);
v___x_3209_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4___redArg(v___x_3208_, v___y_3147_);
return v___x_3209_;
}
}
else
{
lean_object* v___x_3210_; 
lean_dec(v___x_3180_);
lean_dec(v___x_3142_);
lean_dec(v___x_3141_);
v___x_3210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3210_, 0, v_e_3140_);
lean_ctor_set(v___x_3210_, 1, v___y_3147_);
return v___x_3210_;
}
}
case 9:
{
lean_object* v___x_3211_; 
lean_dec(v___x_3142_);
lean_dec(v___x_3141_);
v___x_3211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3211_, 0, v_e_3140_);
lean_ctor_set(v___x_3211_, 1, v___y_3147_);
return v___x_3211_;
}
case 2:
{
lean_object* v___x_3212_; 
lean_dec(v___x_3142_);
lean_dec(v___x_3141_);
v___x_3212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3212_, 0, v_e_3140_);
lean_ctor_set(v___x_3212_, 1, v___y_3147_);
return v___x_3212_;
}
case 0:
{
lean_object* v___x_3213_; 
lean_dec(v___x_3142_);
lean_dec(v___x_3141_);
v___x_3213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3213_, 0, v_e_3140_);
lean_ctor_set(v___x_3213_, 1, v___y_3147_);
return v___x_3213_;
}
case 4:
{
lean_object* v___x_3214_; 
lean_dec(v___x_3142_);
lean_dec(v___x_3141_);
v___x_3214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3214_, 0, v_e_3140_);
lean_ctor_set(v___x_3214_, 1, v___y_3147_);
return v___x_3214_;
}
case 3:
{
lean_object* v___x_3215_; 
lean_dec(v___x_3142_);
lean_dec(v___x_3141_);
v___x_3215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3215_, 0, v_e_3140_);
lean_ctor_set(v___x_3215_, 1, v___y_3147_);
return v___x_3215_;
}
default: 
{
uint8_t v___x_3216_; 
v___x_3216_ = l_Lean_Expr_hasFVar(v_e_3140_);
if (v___x_3216_ == 0)
{
lean_object* v___x_3217_; 
lean_dec(v___x_3142_);
lean_dec(v___x_3141_);
v___x_3217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3217_, 0, v_e_3140_);
lean_ctor_set(v___x_3217_, 1, v___y_3147_);
return v___x_3217_;
}
else
{
v_a_3149_ = v___y_3147_;
goto v___jp_3148_;
}
}
}
v___jp_3148_:
{
switch(lean_obj_tag(v_e_3140_))
{
case 9:
{
lean_object* v___x_3150_; 
lean_dec(v___x_3142_);
lean_dec(v___x_3141_);
v___x_3150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3150_, 0, v_e_3140_);
lean_ctor_set(v___x_3150_, 1, v_a_3149_);
return v___x_3150_;
}
case 2:
{
lean_object* v___x_3151_; 
lean_dec(v___x_3142_);
lean_dec(v___x_3141_);
v___x_3151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3151_, 0, v_e_3140_);
lean_ctor_set(v___x_3151_, 1, v_a_3149_);
return v___x_3151_;
}
case 0:
{
lean_object* v___x_3152_; 
lean_dec(v___x_3142_);
lean_dec(v___x_3141_);
v___x_3152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3152_, 0, v_e_3140_);
lean_ctor_set(v___x_3152_, 1, v_a_3149_);
return v___x_3152_;
}
case 1:
{
lean_object* v___x_3153_; 
lean_dec(v___x_3142_);
lean_dec(v___x_3141_);
v___x_3153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3153_, 0, v_e_3140_);
lean_ctor_set(v___x_3153_, 1, v_a_3149_);
return v___x_3153_;
}
case 4:
{
lean_object* v___x_3154_; 
lean_dec(v___x_3142_);
lean_dec(v___x_3141_);
v___x_3154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3154_, 0, v_e_3140_);
lean_ctor_set(v___x_3154_, 1, v_a_3149_);
return v___x_3154_;
}
case 3:
{
lean_object* v___x_3155_; 
lean_dec(v___x_3142_);
lean_dec(v___x_3141_);
v___x_3155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3155_, 0, v_e_3140_);
lean_ctor_set(v___x_3155_, 1, v_a_3149_);
return v___x_3155_;
}
default: 
{
lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3156_ = lean_box(0);
v___x_3157_ = lean_mk_array(v___x_3141_, v___x_3156_);
lean_inc(v___x_3142_);
v___x_3158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3142_);
lean_ctor_set(v___x_3158_, 1, v___x_3157_);
v___x_3159_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5(v_fst_3143_, v___x_3144_, v_e_3140_, v___x_3142_, v___x_3158_, v_debug_3145_, v___y_3146_, v_a_3149_);
if (lean_obj_tag(v___x_3159_) == 0)
{
lean_object* v_a_3160_; lean_object* v_a_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3169_; 
v_a_3160_ = lean_ctor_get(v___x_3159_, 0);
v_a_3161_ = lean_ctor_get(v___x_3159_, 1);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3159_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3163_ = v___x_3159_;
v_isShared_3164_ = v_isSharedCheck_3169_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_a_3161_);
lean_inc(v_a_3160_);
lean_dec(v___x_3159_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3169_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v_fst_3165_; lean_object* v___x_3167_; 
v_fst_3165_ = lean_ctor_get(v_a_3160_, 0);
lean_inc(v_fst_3165_);
lean_dec(v_a_3160_);
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 0, v_fst_3165_);
v___x_3167_ = v___x_3163_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v_fst_3165_);
lean_ctor_set(v_reuseFailAlloc_3168_, 1, v_a_3161_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
}
else
{
lean_object* v_a_3170_; lean_object* v_a_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3178_; 
v_a_3170_ = lean_ctor_get(v___x_3159_, 0);
v_a_3171_ = lean_ctor_get(v___x_3159_, 1);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3159_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3173_ = v___x_3159_;
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_a_3171_);
lean_inc(v_a_3170_);
lean_dec(v___x_3159_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3176_; 
if (v_isShared_3174_ == 0)
{
v___x_3176_ = v___x_3173_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_a_3170_);
lean_ctor_set(v_reuseFailAlloc_3177_, 1, v_a_3171_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___lam__0___boxed(lean_object* v_e_3218_, lean_object* v___x_3219_, lean_object* v___x_3220_, lean_object* v_fst_3221_, lean_object* v___x_3222_, lean_object* v_debug_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_){
_start:
{
uint8_t v_debug_boxed_3226_; lean_object* v_res_3227_; 
v_debug_boxed_3226_ = lean_unbox(v_debug_3223_);
v_res_3227_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___lam__0(v_e_3218_, v___x_3219_, v___x_3220_, v_fst_3221_, v___x_3222_, v_debug_boxed_3226_, v___y_3224_, v___y_3225_);
lean_dec_ref(v___y_3224_);
lean_dec(v___x_3222_);
lean_dec(v_fst_3221_);
return v_res_3227_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__0(lean_object* v_piece_3228_, lean_object* v___x_3229_, lean_object* v___x_3230_, lean_object* v_i_3231_, uint8_t v_debug_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_){
_start:
{
lean_object* v_a_3236_; 
switch(lean_obj_tag(v_piece_3228_))
{
case 1:
{
lean_object* v_fvarId_3265_; lean_object* v___x_3266_; 
v_fvarId_3265_ = lean_ctor_get(v_piece_3228_, 0);
v___x_3266_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___redArg(v___x_3230_, v_fvarId_3265_);
if (lean_obj_tag(v___x_3266_) == 1)
{
lean_object* v_val_3267_; uint8_t v___x_3268_; 
v_val_3267_ = lean_ctor_get(v___x_3266_, 0);
lean_inc(v_val_3267_);
lean_dec_ref_known(v___x_3266_, 1);
v___x_3268_ = lean_nat_dec_lt(v_val_3267_, v_i_3231_);
if (v___x_3268_ == 0)
{
lean_object* v___x_3269_; lean_object* v___x_3270_; 
lean_dec(v_val_3267_);
v___x_3269_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2);
v___x_3270_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3(v___x_3269_, v_debug_3232_, v___y_3233_, v___y_3234_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v_a_3271_; 
v_a_3271_ = lean_ctor_get(v___x_3270_, 0);
lean_inc(v_a_3271_);
if (lean_obj_tag(v_a_3271_) == 1)
{
lean_object* v_a_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3280_; 
lean_dec_ref_known(v_piece_3228_, 1);
lean_dec(v___x_3229_);
v_a_3272_ = lean_ctor_get(v___x_3270_, 1);
v_isSharedCheck_3280_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3280_ == 0)
{
lean_object* v_unused_3281_; 
v_unused_3281_ = lean_ctor_get(v___x_3270_, 0);
lean_dec(v_unused_3281_);
v___x_3274_ = v___x_3270_;
v_isShared_3275_ = v_isSharedCheck_3280_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_a_3272_);
lean_dec(v___x_3270_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3280_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v_val_3276_; lean_object* v___x_3278_; 
v_val_3276_ = lean_ctor_get(v_a_3271_, 0);
lean_inc(v_val_3276_);
lean_dec_ref_known(v_a_3271_, 1);
if (v_isShared_3275_ == 0)
{
lean_ctor_set(v___x_3274_, 0, v_val_3276_);
v___x_3278_ = v___x_3274_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v_val_3276_);
lean_ctor_set(v_reuseFailAlloc_3279_, 1, v_a_3272_);
v___x_3278_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
return v___x_3278_;
}
}
}
else
{
lean_object* v_a_3282_; 
lean_dec(v_a_3271_);
v_a_3282_ = lean_ctor_get(v___x_3270_, 1);
lean_inc(v_a_3282_);
lean_dec_ref_known(v___x_3270_, 2);
v_a_3236_ = v_a_3282_;
goto v___jp_3235_;
}
}
else
{
lean_object* v_a_3283_; lean_object* v_a_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3291_; 
lean_dec_ref_known(v_piece_3228_, 1);
lean_dec(v___x_3229_);
v_a_3283_ = lean_ctor_get(v___x_3270_, 0);
v_a_3284_ = lean_ctor_get(v___x_3270_, 1);
v_isSharedCheck_3291_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3291_ == 0)
{
v___x_3286_ = v___x_3270_;
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_a_3284_);
lean_inc(v_a_3283_);
lean_dec(v___x_3270_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v___x_3289_; 
if (v_isShared_3287_ == 0)
{
v___x_3289_ = v___x_3286_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v_a_3283_);
lean_ctor_set(v_reuseFailAlloc_3290_, 1, v_a_3284_);
v___x_3289_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
return v___x_3289_;
}
}
}
}
else
{
lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; 
lean_dec_ref_known(v_piece_3228_, 1);
lean_dec(v___x_3229_);
v___x_3292_ = lean_nat_sub(v_i_3231_, v_val_3267_);
lean_dec(v_val_3267_);
v___x_3293_ = lean_unsigned_to_nat(1u);
v___x_3294_ = lean_nat_sub(v___x_3292_, v___x_3293_);
lean_dec(v___x_3292_);
v___x_3295_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4___redArg(v___x_3294_, v___y_3234_);
return v___x_3295_;
}
}
else
{
lean_object* v___x_3296_; 
lean_dec(v___x_3266_);
lean_dec(v___x_3229_);
v___x_3296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3296_, 0, v_piece_3228_);
lean_ctor_set(v___x_3296_, 1, v___y_3234_);
return v___x_3296_;
}
}
case 9:
{
lean_object* v___x_3297_; 
lean_dec(v___x_3229_);
v___x_3297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3297_, 0, v_piece_3228_);
lean_ctor_set(v___x_3297_, 1, v___y_3234_);
return v___x_3297_;
}
case 2:
{
lean_object* v___x_3298_; 
lean_dec(v___x_3229_);
v___x_3298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3298_, 0, v_piece_3228_);
lean_ctor_set(v___x_3298_, 1, v___y_3234_);
return v___x_3298_;
}
case 0:
{
lean_object* v___x_3299_; 
lean_dec(v___x_3229_);
v___x_3299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3299_, 0, v_piece_3228_);
lean_ctor_set(v___x_3299_, 1, v___y_3234_);
return v___x_3299_;
}
case 4:
{
lean_object* v___x_3300_; 
lean_dec(v___x_3229_);
v___x_3300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3300_, 0, v_piece_3228_);
lean_ctor_set(v___x_3300_, 1, v___y_3234_);
return v___x_3300_;
}
case 3:
{
lean_object* v___x_3301_; 
lean_dec(v___x_3229_);
v___x_3301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3301_, 0, v_piece_3228_);
lean_ctor_set(v___x_3301_, 1, v___y_3234_);
return v___x_3301_;
}
default: 
{
uint8_t v___x_3302_; 
v___x_3302_ = l_Lean_Expr_hasFVar(v_piece_3228_);
if (v___x_3302_ == 0)
{
lean_object* v___x_3303_; 
lean_dec(v___x_3229_);
v___x_3303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3303_, 0, v_piece_3228_);
lean_ctor_set(v___x_3303_, 1, v___y_3234_);
return v___x_3303_;
}
else
{
v_a_3236_ = v___y_3234_;
goto v___jp_3235_;
}
}
}
v___jp_3235_:
{
switch(lean_obj_tag(v_piece_3228_))
{
case 9:
{
lean_object* v___x_3237_; 
lean_dec(v___x_3229_);
v___x_3237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3237_, 0, v_piece_3228_);
lean_ctor_set(v___x_3237_, 1, v_a_3236_);
return v___x_3237_;
}
case 2:
{
lean_object* v___x_3238_; 
lean_dec(v___x_3229_);
v___x_3238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3238_, 0, v_piece_3228_);
lean_ctor_set(v___x_3238_, 1, v_a_3236_);
return v___x_3238_;
}
case 0:
{
lean_object* v___x_3239_; 
lean_dec(v___x_3229_);
v___x_3239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3239_, 0, v_piece_3228_);
lean_ctor_set(v___x_3239_, 1, v_a_3236_);
return v___x_3239_;
}
case 1:
{
lean_object* v___x_3240_; 
lean_dec(v___x_3229_);
v___x_3240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3240_, 0, v_piece_3228_);
lean_ctor_set(v___x_3240_, 1, v_a_3236_);
return v___x_3240_;
}
case 4:
{
lean_object* v___x_3241_; 
lean_dec(v___x_3229_);
v___x_3241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3241_, 0, v_piece_3228_);
lean_ctor_set(v___x_3241_, 1, v_a_3236_);
return v___x_3241_;
}
case 3:
{
lean_object* v___x_3242_; 
lean_dec(v___x_3229_);
v___x_3242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3242_, 0, v_piece_3228_);
lean_ctor_set(v___x_3242_, 1, v_a_3236_);
return v___x_3242_;
}
default: 
{
lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; 
v___x_3243_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__0, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__0_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__0);
lean_inc(v___x_3229_);
v___x_3244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3244_, 0, v___x_3229_);
lean_ctor_set(v___x_3244_, 1, v___x_3243_);
v___x_3245_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5(v___x_3230_, v_i_3231_, v_piece_3228_, v___x_3229_, v___x_3244_, v_debug_3232_, v___y_3233_, v_a_3236_);
if (lean_obj_tag(v___x_3245_) == 0)
{
lean_object* v_a_3246_; lean_object* v_a_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3255_; 
v_a_3246_ = lean_ctor_get(v___x_3245_, 0);
v_a_3247_ = lean_ctor_get(v___x_3245_, 1);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3245_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3249_ = v___x_3245_;
v_isShared_3250_ = v_isSharedCheck_3255_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_a_3247_);
lean_inc(v_a_3246_);
lean_dec(v___x_3245_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3255_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v_fst_3251_; lean_object* v___x_3253_; 
v_fst_3251_ = lean_ctor_get(v_a_3246_, 0);
lean_inc(v_fst_3251_);
lean_dec(v_a_3246_);
if (v_isShared_3250_ == 0)
{
lean_ctor_set(v___x_3249_, 0, v_fst_3251_);
v___x_3253_ = v___x_3249_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_fst_3251_);
lean_ctor_set(v_reuseFailAlloc_3254_, 1, v_a_3247_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
}
}
}
else
{
lean_object* v_a_3256_; lean_object* v_a_3257_; lean_object* v___x_3259_; uint8_t v_isShared_3260_; uint8_t v_isSharedCheck_3264_; 
v_a_3256_ = lean_ctor_get(v___x_3245_, 0);
v_a_3257_ = lean_ctor_get(v___x_3245_, 1);
v_isSharedCheck_3264_ = !lean_is_exclusive(v___x_3245_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3259_ = v___x_3245_;
v_isShared_3260_ = v_isSharedCheck_3264_;
goto v_resetjp_3258_;
}
else
{
lean_inc(v_a_3257_);
lean_inc(v_a_3256_);
lean_dec(v___x_3245_);
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
v_reuseFailAlloc_3263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v_a_3256_);
lean_ctor_set(v_reuseFailAlloc_3263_, 1, v_a_3257_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__0___boxed(lean_object* v_piece_3304_, lean_object* v___x_3305_, lean_object* v___x_3306_, lean_object* v_i_3307_, lean_object* v_debug_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_){
_start:
{
uint8_t v_debug_boxed_3311_; lean_object* v_res_3312_; 
v_debug_boxed_3311_ = lean_unbox(v_debug_3308_);
v_res_3312_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__0(v_piece_3304_, v___x_3305_, v___x_3306_, v_i_3307_, v_debug_boxed_3311_, v___y_3309_, v___y_3310_);
lean_dec_ref(v___y_3309_);
lean_dec(v_i_3307_);
lean_dec_ref(v___x_3306_);
return v_res_3312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__1(lean_object* v___x_3313_, lean_object* v___x_3314_, uint8_t v___x_3315_, lean_object* v_piece_3316_, lean_object* v_i_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_){
_start:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; uint8_t v_debug_3328_; lean_object* v_env_3329_; lean_object* v___x_3330_; lean_object* v___f_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
v___x_3326_ = lean_st_ref_get(v___y_3320_);
v___x_3327_ = lean_st_ref_get(v___y_3324_);
v_debug_3328_ = lean_ctor_get_uint8(v___x_3326_, sizeof(void*)*11);
lean_dec(v___x_3326_);
v_env_3329_ = lean_ctor_get(v___x_3327_, 0);
lean_inc_ref(v_env_3329_);
lean_dec(v___x_3327_);
v___x_3330_ = lean_box(v_debug_3328_);
v___f_3331_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__0___boxed), 7, 5);
lean_closure_set(v___f_3331_, 0, v_piece_3316_);
lean_closure_set(v___f_3331_, 1, v___x_3313_);
lean_closure_set(v___f_3331_, 2, v___x_3314_);
lean_closure_set(v___f_3331_, 3, v_i_3317_);
lean_closure_set(v___f_3331_, 4, v___x_3330_);
v___x_3332_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_3332_, 0, v_env_3329_);
lean_ctor_set_uint8(v___x_3332_, sizeof(void*)*1, v___x_3315_);
lean_ctor_set_uint8(v___x_3332_, sizeof(void*)*1 + 1, v___x_3315_);
v___x_3333_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_3331_, v___x_3332_, v___y_3320_);
if (lean_obj_tag(v___x_3333_) == 0)
{
lean_object* v_a_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3344_; 
v_a_3334_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3336_ = v___x_3333_;
v_isShared_3337_ = v_isSharedCheck_3344_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_a_3334_);
lean_dec(v___x_3333_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3344_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
if (lean_obj_tag(v_a_3334_) == 0)
{
lean_object* v___x_3338_; lean_object* v___x_3339_; 
lean_dec_ref_known(v_a_3334_, 1);
lean_del_object(v___x_3336_);
v___x_3338_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2);
v___x_3339_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1(v___x_3338_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_);
return v___x_3339_;
}
else
{
lean_object* v_a_3340_; lean_object* v___x_3342_; 
v_a_3340_ = lean_ctor_get(v_a_3334_, 0);
lean_inc(v_a_3340_);
lean_dec_ref_known(v_a_3334_, 1);
if (v_isShared_3337_ == 0)
{
lean_ctor_set(v___x_3336_, 0, v_a_3340_);
v___x_3342_ = v___x_3336_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v_a_3340_);
v___x_3342_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
return v___x_3342_;
}
}
}
}
else
{
lean_object* v_a_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3352_; 
v_a_3345_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3352_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3347_ = v___x_3333_;
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_a_3345_);
lean_dec(v___x_3333_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3350_; 
if (v_isShared_3348_ == 0)
{
v___x_3350_ = v___x_3347_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_a_3345_);
v___x_3350_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
return v___x_3350_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__1___boxed(lean_object* v___x_3353_, lean_object* v___x_3354_, lean_object* v___x_3355_, lean_object* v_piece_3356_, lean_object* v_i_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_){
_start:
{
uint8_t v___x_16850__boxed_3366_; lean_object* v_res_3367_; 
v___x_16850__boxed_3366_ = lean_unbox(v___x_3355_);
v_res_3367_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__1(v___x_3353_, v___x_3354_, v___x_16850__boxed_3366_, v_piece_3356_, v_i_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
lean_dec(v___y_3364_);
lean_dec_ref(v___y_3363_);
lean_dec(v___y_3362_);
lean_dec_ref(v___y_3361_);
lean_dec(v___y_3360_);
lean_dec_ref(v___y_3359_);
lean_dec(v___y_3358_);
return v_res_3367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7_spec__12(lean_object* v___x_3368_, lean_object* v___x_3369_, lean_object* v_as_3370_, size_t v_sz_3371_, size_t v_i_3372_, lean_object* v_b_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_){
_start:
{
uint8_t v___x_3382_; 
v___x_3382_ = lean_usize_dec_lt(v_i_3372_, v_sz_3371_);
if (v___x_3382_ == 0)
{
lean_object* v___x_3383_; 
lean_dec_ref(v___x_3368_);
v___x_3383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3383_, 0, v_b_3373_);
return v___x_3383_;
}
else
{
lean_object* v_fst_3384_; lean_object* v_snd_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3434_; 
v_fst_3384_ = lean_ctor_get(v_b_3373_, 0);
v_snd_3385_ = lean_ctor_get(v_b_3373_, 1);
v_isSharedCheck_3434_ = !lean_is_exclusive(v_b_3373_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3387_ = v_b_3373_;
v_isShared_3388_ = v_isSharedCheck_3434_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_snd_3385_);
lean_inc(v_fst_3384_);
lean_dec(v_b_3373_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3434_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v_a_3389_; lean_object* v_userName_3390_; lean_object* v_type_3391_; lean_object* v_value_3392_; uint8_t v_nondep_3393_; lean_object* v___x_3394_; uint8_t v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; 
v_a_3389_ = lean_array_uget_borrowed(v_as_3370_, v_i_3372_);
v_userName_3390_ = lean_ctor_get(v_a_3389_, 1);
v_type_3391_ = lean_ctor_get(v_a_3389_, 2);
v_value_3392_ = lean_ctor_get(v_a_3389_, 3);
v_nondep_3393_ = lean_ctor_get_uint8(v_a_3389_, sizeof(void*)*4);
v___x_3394_ = lean_unsigned_to_nat(0u);
v___x_3395_ = lean_nat_dec_eq(v___x_3369_, v___x_3394_);
v___x_3396_ = lean_unsigned_to_nat(1u);
v___x_3397_ = lean_nat_sub(v_snd_3385_, v___x_3396_);
lean_dec(v_snd_3385_);
lean_inc(v___x_3397_);
lean_inc_ref(v_type_3391_);
lean_inc_ref(v___x_3368_);
v___x_3398_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__1(v___x_3394_, v___x_3368_, v___x_3395_, v_type_3391_, v___x_3397_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
if (lean_obj_tag(v___x_3398_) == 0)
{
lean_object* v_a_3399_; lean_object* v___x_3400_; 
v_a_3399_ = lean_ctor_get(v___x_3398_, 0);
lean_inc(v_a_3399_);
lean_dec_ref_known(v___x_3398_, 1);
lean_inc(v___x_3397_);
lean_inc_ref(v_value_3392_);
lean_inc_ref(v___x_3368_);
v___x_3400_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__1(v___x_3394_, v___x_3368_, v___x_3395_, v_value_3392_, v___x_3397_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
if (lean_obj_tag(v___x_3400_) == 0)
{
lean_object* v_a_3401_; lean_object* v___x_3402_; 
v_a_3401_ = lean_ctor_get(v___x_3400_, 0);
lean_inc(v_a_3401_);
lean_dec_ref_known(v___x_3400_, 1);
lean_inc(v_userName_3390_);
v___x_3402_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6___redArg(v_userName_3390_, v_a_3399_, v_a_3401_, v_fst_3384_, v_nondep_3393_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
if (lean_obj_tag(v___x_3402_) == 0)
{
lean_object* v_a_3403_; lean_object* v___x_3405_; 
v_a_3403_ = lean_ctor_get(v___x_3402_, 0);
lean_inc(v_a_3403_);
lean_dec_ref_known(v___x_3402_, 1);
if (v_isShared_3388_ == 0)
{
lean_ctor_set(v___x_3387_, 1, v___x_3397_);
lean_ctor_set(v___x_3387_, 0, v_a_3403_);
v___x_3405_ = v___x_3387_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_a_3403_);
lean_ctor_set(v_reuseFailAlloc_3409_, 1, v___x_3397_);
v___x_3405_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
size_t v___x_3406_; size_t v___x_3407_; 
v___x_3406_ = ((size_t)1ULL);
v___x_3407_ = lean_usize_add(v_i_3372_, v___x_3406_);
v_i_3372_ = v___x_3407_;
v_b_3373_ = v___x_3405_;
goto _start;
}
}
else
{
lean_object* v_a_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3417_; 
lean_dec(v___x_3397_);
lean_del_object(v___x_3387_);
lean_dec_ref(v___x_3368_);
v_a_3410_ = lean_ctor_get(v___x_3402_, 0);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3402_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3412_ = v___x_3402_;
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_a_3410_);
lean_dec(v___x_3402_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3415_; 
if (v_isShared_3413_ == 0)
{
v___x_3415_ = v___x_3412_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_a_3410_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
}
}
else
{
lean_object* v_a_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3425_; 
lean_dec(v_a_3399_);
lean_dec(v___x_3397_);
lean_del_object(v___x_3387_);
lean_dec(v_fst_3384_);
lean_dec_ref(v___x_3368_);
v_a_3418_ = lean_ctor_get(v___x_3400_, 0);
v_isSharedCheck_3425_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3425_ == 0)
{
v___x_3420_ = v___x_3400_;
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_a_3418_);
lean_dec(v___x_3400_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3423_; 
if (v_isShared_3421_ == 0)
{
v___x_3423_ = v___x_3420_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_a_3418_);
v___x_3423_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
return v___x_3423_;
}
}
}
}
else
{
lean_object* v_a_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3433_; 
lean_dec(v___x_3397_);
lean_del_object(v___x_3387_);
lean_dec(v_fst_3384_);
lean_dec_ref(v___x_3368_);
v_a_3426_ = lean_ctor_get(v___x_3398_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3428_ = v___x_3398_;
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_a_3426_);
lean_dec(v___x_3398_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
lean_object* v___x_3431_; 
if (v_isShared_3429_ == 0)
{
v___x_3431_ = v___x_3428_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v_a_3426_);
v___x_3431_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
return v___x_3431_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7_spec__12___boxed(lean_object* v___x_3435_, lean_object* v___x_3436_, lean_object* v_as_3437_, lean_object* v_sz_3438_, lean_object* v_i_3439_, lean_object* v_b_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_){
_start:
{
size_t v_sz_boxed_3449_; size_t v_i_boxed_3450_; lean_object* v_res_3451_; 
v_sz_boxed_3449_ = lean_unbox_usize(v_sz_3438_);
lean_dec(v_sz_3438_);
v_i_boxed_3450_ = lean_unbox_usize(v_i_3439_);
lean_dec(v_i_3439_);
v_res_3451_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7_spec__12(v___x_3435_, v___x_3436_, v_as_3437_, v_sz_boxed_3449_, v_i_boxed_3450_, v_b_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_);
lean_dec(v___y_3447_);
lean_dec_ref(v___y_3446_);
lean_dec(v___y_3445_);
lean_dec_ref(v___y_3444_);
lean_dec(v___y_3443_);
lean_dec_ref(v___y_3442_);
lean_dec(v___y_3441_);
lean_dec_ref(v_as_3437_);
lean_dec(v___x_3436_);
return v_res_3451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7(lean_object* v___x_3452_, lean_object* v___x_3453_, lean_object* v_as_3454_, size_t v_sz_3455_, size_t v_i_3456_, lean_object* v_b_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_){
_start:
{
uint8_t v___x_3466_; 
v___x_3466_ = lean_usize_dec_lt(v_i_3456_, v_sz_3455_);
if (v___x_3466_ == 0)
{
lean_object* v___x_3467_; 
lean_dec_ref(v___x_3452_);
v___x_3467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3467_, 0, v_b_3457_);
return v___x_3467_;
}
else
{
lean_object* v_fst_3468_; lean_object* v_snd_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3518_; 
v_fst_3468_ = lean_ctor_get(v_b_3457_, 0);
v_snd_3469_ = lean_ctor_get(v_b_3457_, 1);
v_isSharedCheck_3518_ = !lean_is_exclusive(v_b_3457_);
if (v_isSharedCheck_3518_ == 0)
{
v___x_3471_ = v_b_3457_;
v_isShared_3472_ = v_isSharedCheck_3518_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_snd_3469_);
lean_inc(v_fst_3468_);
lean_dec(v_b_3457_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3518_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v_a_3473_; lean_object* v_userName_3474_; lean_object* v_type_3475_; lean_object* v_value_3476_; uint8_t v_nondep_3477_; lean_object* v___x_3478_; uint8_t v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; 
v_a_3473_ = lean_array_uget_borrowed(v_as_3454_, v_i_3456_);
v_userName_3474_ = lean_ctor_get(v_a_3473_, 1);
v_type_3475_ = lean_ctor_get(v_a_3473_, 2);
v_value_3476_ = lean_ctor_get(v_a_3473_, 3);
v_nondep_3477_ = lean_ctor_get_uint8(v_a_3473_, sizeof(void*)*4);
v___x_3478_ = lean_unsigned_to_nat(0u);
v___x_3479_ = lean_nat_dec_eq(v___x_3453_, v___x_3478_);
v___x_3480_ = lean_unsigned_to_nat(1u);
v___x_3481_ = lean_nat_sub(v_snd_3469_, v___x_3480_);
lean_dec(v_snd_3469_);
lean_inc(v___x_3481_);
lean_inc_ref(v_type_3475_);
lean_inc_ref(v___x_3452_);
v___x_3482_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__1(v___x_3478_, v___x_3452_, v___x_3479_, v_type_3475_, v___x_3481_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_);
if (lean_obj_tag(v___x_3482_) == 0)
{
lean_object* v_a_3483_; lean_object* v___x_3484_; 
v_a_3483_ = lean_ctor_get(v___x_3482_, 0);
lean_inc(v_a_3483_);
lean_dec_ref_known(v___x_3482_, 1);
lean_inc(v___x_3481_);
lean_inc_ref(v_value_3476_);
lean_inc_ref(v___x_3452_);
v___x_3484_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__1(v___x_3478_, v___x_3452_, v___x_3479_, v_value_3476_, v___x_3481_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_);
if (lean_obj_tag(v___x_3484_) == 0)
{
lean_object* v_a_3485_; lean_object* v___x_3486_; 
v_a_3485_ = lean_ctor_get(v___x_3484_, 0);
lean_inc(v_a_3485_);
lean_dec_ref_known(v___x_3484_, 1);
lean_inc(v_userName_3474_);
v___x_3486_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6___redArg(v_userName_3474_, v_a_3483_, v_a_3485_, v_fst_3468_, v_nondep_3477_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_);
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_object* v_a_3487_; lean_object* v___x_3489_; 
v_a_3487_ = lean_ctor_get(v___x_3486_, 0);
lean_inc(v_a_3487_);
lean_dec_ref_known(v___x_3486_, 1);
if (v_isShared_3472_ == 0)
{
lean_ctor_set(v___x_3471_, 1, v___x_3481_);
lean_ctor_set(v___x_3471_, 0, v_a_3487_);
v___x_3489_ = v___x_3471_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v_a_3487_);
lean_ctor_set(v_reuseFailAlloc_3493_, 1, v___x_3481_);
v___x_3489_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
size_t v___x_3490_; size_t v___x_3491_; lean_object* v___x_3492_; 
v___x_3490_ = ((size_t)1ULL);
v___x_3491_ = lean_usize_add(v_i_3456_, v___x_3490_);
v___x_3492_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7_spec__12(v___x_3452_, v___x_3453_, v_as_3454_, v_sz_3455_, v___x_3491_, v___x_3489_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_);
return v___x_3492_;
}
}
else
{
lean_object* v_a_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3501_; 
lean_dec(v___x_3481_);
lean_del_object(v___x_3471_);
lean_dec_ref(v___x_3452_);
v_a_3494_ = lean_ctor_get(v___x_3486_, 0);
v_isSharedCheck_3501_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3496_ = v___x_3486_;
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_a_3494_);
lean_dec(v___x_3486_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___x_3499_; 
if (v_isShared_3497_ == 0)
{
v___x_3499_ = v___x_3496_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v_a_3494_);
v___x_3499_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
return v___x_3499_;
}
}
}
}
else
{
lean_object* v_a_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3509_; 
lean_dec(v_a_3483_);
lean_dec(v___x_3481_);
lean_del_object(v___x_3471_);
lean_dec(v_fst_3468_);
lean_dec_ref(v___x_3452_);
v_a_3502_ = lean_ctor_get(v___x_3484_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3484_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3504_ = v___x_3484_;
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_a_3502_);
lean_dec(v___x_3484_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v___x_3507_; 
if (v_isShared_3505_ == 0)
{
v___x_3507_ = v___x_3504_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_a_3502_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
return v___x_3507_;
}
}
}
}
else
{
lean_object* v_a_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3517_; 
lean_dec(v___x_3481_);
lean_del_object(v___x_3471_);
lean_dec(v_fst_3468_);
lean_dec_ref(v___x_3452_);
v_a_3510_ = lean_ctor_get(v___x_3482_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3482_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3512_ = v___x_3482_;
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_a_3510_);
lean_dec(v___x_3482_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v___x_3515_; 
if (v_isShared_3513_ == 0)
{
v___x_3515_ = v___x_3512_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_a_3510_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___boxed(lean_object* v___x_3519_, lean_object* v___x_3520_, lean_object* v_as_3521_, lean_object* v_sz_3522_, lean_object* v_i_3523_, lean_object* v_b_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_){
_start:
{
size_t v_sz_boxed_3533_; size_t v_i_boxed_3534_; lean_object* v_res_3535_; 
v_sz_boxed_3533_ = lean_unbox_usize(v_sz_3522_);
lean_dec(v_sz_3522_);
v_i_boxed_3534_ = lean_unbox_usize(v_i_3523_);
lean_dec(v_i_3523_);
v_res_3535_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7(v___x_3519_, v___x_3520_, v_as_3521_, v_sz_boxed_3533_, v_i_boxed_3534_, v_b_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_);
lean_dec(v___y_3531_);
lean_dec_ref(v___y_3530_);
lean_dec(v___y_3529_);
lean_dec_ref(v___y_3528_);
lean_dec(v___y_3527_);
lean_dec_ref(v___y_3526_);
lean_dec(v___y_3525_);
lean_dec_ref(v_as_3521_);
lean_dec(v___x_3520_);
return v_res_3535_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0___redArg(lean_object* v_a_3536_, lean_object* v_x_3537_){
_start:
{
if (lean_obj_tag(v_x_3537_) == 0)
{
uint8_t v___x_3538_; 
v___x_3538_ = 0;
return v___x_3538_;
}
else
{
lean_object* v_key_3539_; lean_object* v_tail_3540_; uint8_t v___x_3541_; 
v_key_3539_ = lean_ctor_get(v_x_3537_, 0);
v_tail_3540_ = lean_ctor_get(v_x_3537_, 2);
v___x_3541_ = l_Lean_instBEqFVarId_beq(v_key_3539_, v_a_3536_);
if (v___x_3541_ == 0)
{
v_x_3537_ = v_tail_3540_;
goto _start;
}
else
{
return v___x_3541_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0___redArg___boxed(lean_object* v_a_3543_, lean_object* v_x_3544_){
_start:
{
uint8_t v_res_3545_; lean_object* v_r_3546_; 
v_res_3545_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0___redArg(v_a_3543_, v_x_3544_);
lean_dec(v_x_3544_);
lean_dec(v_a_3543_);
v_r_3546_ = lean_box(v_res_3545_);
return v_r_3546_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1_spec__5_spec__10___redArg(lean_object* v_x_3547_, lean_object* v_x_3548_){
_start:
{
if (lean_obj_tag(v_x_3548_) == 0)
{
return v_x_3547_;
}
else
{
lean_object* v_key_3549_; lean_object* v_value_3550_; lean_object* v_tail_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3574_; 
v_key_3549_ = lean_ctor_get(v_x_3548_, 0);
v_value_3550_ = lean_ctor_get(v_x_3548_, 1);
v_tail_3551_ = lean_ctor_get(v_x_3548_, 2);
v_isSharedCheck_3574_ = !lean_is_exclusive(v_x_3548_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3553_ = v_x_3548_;
v_isShared_3554_ = v_isSharedCheck_3574_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_tail_3551_);
lean_inc(v_value_3550_);
lean_inc(v_key_3549_);
lean_dec(v_x_3548_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3574_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v___x_3555_; uint64_t v___x_3556_; uint64_t v___x_3557_; uint64_t v___x_3558_; uint64_t v_fold_3559_; uint64_t v___x_3560_; uint64_t v___x_3561_; uint64_t v___x_3562_; size_t v___x_3563_; size_t v___x_3564_; size_t v___x_3565_; size_t v___x_3566_; size_t v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3570_; 
v___x_3555_ = lean_array_get_size(v_x_3547_);
v___x_3556_ = l_Lean_instHashableFVarId_hash(v_key_3549_);
v___x_3557_ = 32ULL;
v___x_3558_ = lean_uint64_shift_right(v___x_3556_, v___x_3557_);
v_fold_3559_ = lean_uint64_xor(v___x_3556_, v___x_3558_);
v___x_3560_ = 16ULL;
v___x_3561_ = lean_uint64_shift_right(v_fold_3559_, v___x_3560_);
v___x_3562_ = lean_uint64_xor(v_fold_3559_, v___x_3561_);
v___x_3563_ = lean_uint64_to_usize(v___x_3562_);
v___x_3564_ = lean_usize_of_nat(v___x_3555_);
v___x_3565_ = ((size_t)1ULL);
v___x_3566_ = lean_usize_sub(v___x_3564_, v___x_3565_);
v___x_3567_ = lean_usize_land(v___x_3563_, v___x_3566_);
v___x_3568_ = lean_array_uget_borrowed(v_x_3547_, v___x_3567_);
lean_inc(v___x_3568_);
if (v_isShared_3554_ == 0)
{
lean_ctor_set(v___x_3553_, 2, v___x_3568_);
v___x_3570_ = v___x_3553_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v_key_3549_);
lean_ctor_set(v_reuseFailAlloc_3573_, 1, v_value_3550_);
lean_ctor_set(v_reuseFailAlloc_3573_, 2, v___x_3568_);
v___x_3570_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
lean_object* v___x_3571_; 
v___x_3571_ = lean_array_uset(v_x_3547_, v___x_3567_, v___x_3570_);
v_x_3547_ = v___x_3571_;
v_x_3548_ = v_tail_3551_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1_spec__5___redArg(lean_object* v_i_3575_, lean_object* v_source_3576_, lean_object* v_target_3577_){
_start:
{
lean_object* v___x_3578_; uint8_t v___x_3579_; 
v___x_3578_ = lean_array_get_size(v_source_3576_);
v___x_3579_ = lean_nat_dec_lt(v_i_3575_, v___x_3578_);
if (v___x_3579_ == 0)
{
lean_dec_ref(v_source_3576_);
lean_dec(v_i_3575_);
return v_target_3577_;
}
else
{
lean_object* v_es_3580_; lean_object* v___x_3581_; lean_object* v_source_3582_; lean_object* v_target_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; 
v_es_3580_ = lean_array_fget(v_source_3576_, v_i_3575_);
v___x_3581_ = lean_box(0);
v_source_3582_ = lean_array_fset(v_source_3576_, v_i_3575_, v___x_3581_);
v_target_3583_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1_spec__5_spec__10___redArg(v_target_3577_, v_es_3580_);
v___x_3584_ = lean_unsigned_to_nat(1u);
v___x_3585_ = lean_nat_add(v_i_3575_, v___x_3584_);
lean_dec(v_i_3575_);
v_i_3575_ = v___x_3585_;
v_source_3576_ = v_source_3582_;
v_target_3577_ = v_target_3583_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1___redArg(lean_object* v_data_3587_){
_start:
{
lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v_nbuckets_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; 
v___x_3588_ = lean_array_get_size(v_data_3587_);
v___x_3589_ = lean_unsigned_to_nat(2u);
v_nbuckets_3590_ = lean_nat_mul(v___x_3588_, v___x_3589_);
v___x_3591_ = lean_unsigned_to_nat(0u);
v___x_3592_ = lean_box(0);
v___x_3593_ = lean_mk_array(v_nbuckets_3590_, v___x_3592_);
v___x_3594_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1_spec__5___redArg(v___x_3591_, v_data_3587_, v___x_3593_);
return v___x_3594_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__2___redArg(lean_object* v_a_3595_, lean_object* v_b_3596_, lean_object* v_x_3597_){
_start:
{
if (lean_obj_tag(v_x_3597_) == 0)
{
lean_dec(v_b_3596_);
lean_dec(v_a_3595_);
return v_x_3597_;
}
else
{
lean_object* v_key_3598_; lean_object* v_value_3599_; lean_object* v_tail_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3612_; 
v_key_3598_ = lean_ctor_get(v_x_3597_, 0);
v_value_3599_ = lean_ctor_get(v_x_3597_, 1);
v_tail_3600_ = lean_ctor_get(v_x_3597_, 2);
v_isSharedCheck_3612_ = !lean_is_exclusive(v_x_3597_);
if (v_isSharedCheck_3612_ == 0)
{
v___x_3602_ = v_x_3597_;
v_isShared_3603_ = v_isSharedCheck_3612_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_tail_3600_);
lean_inc(v_value_3599_);
lean_inc(v_key_3598_);
lean_dec(v_x_3597_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3612_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
uint8_t v___x_3604_; 
v___x_3604_ = l_Lean_instBEqFVarId_beq(v_key_3598_, v_a_3595_);
if (v___x_3604_ == 0)
{
lean_object* v___x_3605_; lean_object* v___x_3607_; 
v___x_3605_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__2___redArg(v_a_3595_, v_b_3596_, v_tail_3600_);
if (v_isShared_3603_ == 0)
{
lean_ctor_set(v___x_3602_, 2, v___x_3605_);
v___x_3607_ = v___x_3602_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v_key_3598_);
lean_ctor_set(v_reuseFailAlloc_3608_, 1, v_value_3599_);
lean_ctor_set(v_reuseFailAlloc_3608_, 2, v___x_3605_);
v___x_3607_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
return v___x_3607_;
}
}
else
{
lean_object* v___x_3610_; 
lean_dec(v_value_3599_);
lean_dec(v_key_3598_);
if (v_isShared_3603_ == 0)
{
lean_ctor_set(v___x_3602_, 1, v_b_3596_);
lean_ctor_set(v___x_3602_, 0, v_a_3595_);
v___x_3610_ = v___x_3602_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_a_3595_);
lean_ctor_set(v_reuseFailAlloc_3611_, 1, v_b_3596_);
lean_ctor_set(v_reuseFailAlloc_3611_, 2, v_tail_3600_);
v___x_3610_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
return v___x_3610_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0___redArg(lean_object* v_m_3613_, lean_object* v_a_3614_, lean_object* v_b_3615_){
_start:
{
lean_object* v_size_3616_; lean_object* v_buckets_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3660_; 
v_size_3616_ = lean_ctor_get(v_m_3613_, 0);
v_buckets_3617_ = lean_ctor_get(v_m_3613_, 1);
v_isSharedCheck_3660_ = !lean_is_exclusive(v_m_3613_);
if (v_isSharedCheck_3660_ == 0)
{
v___x_3619_ = v_m_3613_;
v_isShared_3620_ = v_isSharedCheck_3660_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_buckets_3617_);
lean_inc(v_size_3616_);
lean_dec(v_m_3613_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3660_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v___x_3621_; uint64_t v___x_3622_; uint64_t v___x_3623_; uint64_t v___x_3624_; uint64_t v_fold_3625_; uint64_t v___x_3626_; uint64_t v___x_3627_; uint64_t v___x_3628_; size_t v___x_3629_; size_t v___x_3630_; size_t v___x_3631_; size_t v___x_3632_; size_t v___x_3633_; lean_object* v_bkt_3634_; uint8_t v___x_3635_; 
v___x_3621_ = lean_array_get_size(v_buckets_3617_);
v___x_3622_ = l_Lean_instHashableFVarId_hash(v_a_3614_);
v___x_3623_ = 32ULL;
v___x_3624_ = lean_uint64_shift_right(v___x_3622_, v___x_3623_);
v_fold_3625_ = lean_uint64_xor(v___x_3622_, v___x_3624_);
v___x_3626_ = 16ULL;
v___x_3627_ = lean_uint64_shift_right(v_fold_3625_, v___x_3626_);
v___x_3628_ = lean_uint64_xor(v_fold_3625_, v___x_3627_);
v___x_3629_ = lean_uint64_to_usize(v___x_3628_);
v___x_3630_ = lean_usize_of_nat(v___x_3621_);
v___x_3631_ = ((size_t)1ULL);
v___x_3632_ = lean_usize_sub(v___x_3630_, v___x_3631_);
v___x_3633_ = lean_usize_land(v___x_3629_, v___x_3632_);
v_bkt_3634_ = lean_array_uget_borrowed(v_buckets_3617_, v___x_3633_);
v___x_3635_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0___redArg(v_a_3614_, v_bkt_3634_);
if (v___x_3635_ == 0)
{
lean_object* v___x_3636_; lean_object* v_size_x27_3637_; lean_object* v___x_3638_; lean_object* v_buckets_x27_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; uint8_t v___x_3645_; 
v___x_3636_ = lean_unsigned_to_nat(1u);
v_size_x27_3637_ = lean_nat_add(v_size_3616_, v___x_3636_);
lean_dec(v_size_3616_);
lean_inc(v_bkt_3634_);
v___x_3638_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3638_, 0, v_a_3614_);
lean_ctor_set(v___x_3638_, 1, v_b_3615_);
lean_ctor_set(v___x_3638_, 2, v_bkt_3634_);
v_buckets_x27_3639_ = lean_array_uset(v_buckets_3617_, v___x_3633_, v___x_3638_);
v___x_3640_ = lean_unsigned_to_nat(4u);
v___x_3641_ = lean_nat_mul(v_size_x27_3637_, v___x_3640_);
v___x_3642_ = lean_unsigned_to_nat(3u);
v___x_3643_ = lean_nat_div(v___x_3641_, v___x_3642_);
lean_dec(v___x_3641_);
v___x_3644_ = lean_array_get_size(v_buckets_x27_3639_);
v___x_3645_ = lean_nat_dec_le(v___x_3643_, v___x_3644_);
lean_dec(v___x_3643_);
if (v___x_3645_ == 0)
{
lean_object* v_val_3646_; lean_object* v___x_3648_; 
v_val_3646_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1___redArg(v_buckets_x27_3639_);
if (v_isShared_3620_ == 0)
{
lean_ctor_set(v___x_3619_, 1, v_val_3646_);
lean_ctor_set(v___x_3619_, 0, v_size_x27_3637_);
v___x_3648_ = v___x_3619_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v_size_x27_3637_);
lean_ctor_set(v_reuseFailAlloc_3649_, 1, v_val_3646_);
v___x_3648_ = v_reuseFailAlloc_3649_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
return v___x_3648_;
}
}
else
{
lean_object* v___x_3651_; 
if (v_isShared_3620_ == 0)
{
lean_ctor_set(v___x_3619_, 1, v_buckets_x27_3639_);
lean_ctor_set(v___x_3619_, 0, v_size_x27_3637_);
v___x_3651_ = v___x_3619_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_size_x27_3637_);
lean_ctor_set(v_reuseFailAlloc_3652_, 1, v_buckets_x27_3639_);
v___x_3651_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
return v___x_3651_;
}
}
}
else
{
lean_object* v___x_3653_; lean_object* v_buckets_x27_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3658_; 
lean_inc(v_bkt_3634_);
v___x_3653_ = lean_box(0);
v_buckets_x27_3654_ = lean_array_uset(v_buckets_3617_, v___x_3633_, v___x_3653_);
v___x_3655_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__2___redArg(v_a_3614_, v_b_3615_, v_bkt_3634_);
v___x_3656_ = lean_array_uset(v_buckets_x27_3654_, v___x_3633_, v___x_3655_);
if (v_isShared_3620_ == 0)
{
lean_ctor_set(v___x_3619_, 1, v___x_3656_);
v___x_3658_ = v___x_3619_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v_size_3616_);
lean_ctor_set(v_reuseFailAlloc_3659_, 1, v___x_3656_);
v___x_3658_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
return v___x_3658_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1___redArg(lean_object* v_as_3661_, size_t v_sz_3662_, size_t v_i_3663_, lean_object* v_b_3664_){
_start:
{
uint8_t v___x_3666_; 
v___x_3666_ = lean_usize_dec_lt(v_i_3663_, v_sz_3662_);
if (v___x_3666_ == 0)
{
lean_object* v___x_3667_; 
v___x_3667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3667_, 0, v_b_3664_);
return v___x_3667_;
}
else
{
lean_object* v_fst_3668_; lean_object* v_snd_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3685_; 
v_fst_3668_ = lean_ctor_get(v_b_3664_, 0);
v_snd_3669_ = lean_ctor_get(v_b_3664_, 1);
v_isSharedCheck_3685_ = !lean_is_exclusive(v_b_3664_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3671_ = v_b_3664_;
v_isShared_3672_ = v_isSharedCheck_3685_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_snd_3669_);
lean_inc(v_fst_3668_);
lean_dec(v_b_3664_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3685_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
lean_object* v_a_3673_; lean_object* v_fvar_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3680_; 
v_a_3673_ = lean_array_uget_borrowed(v_as_3661_, v_i_3663_);
v_fvar_3674_ = lean_ctor_get(v_a_3673_, 0);
v___x_3675_ = l_Lean_Expr_fvarId_x21(v_fvar_3674_);
lean_inc(v_snd_3669_);
v___x_3676_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0___redArg(v_fst_3668_, v___x_3675_, v_snd_3669_);
v___x_3677_ = lean_unsigned_to_nat(1u);
v___x_3678_ = lean_nat_add(v_snd_3669_, v___x_3677_);
lean_dec(v_snd_3669_);
if (v_isShared_3672_ == 0)
{
lean_ctor_set(v___x_3671_, 1, v___x_3678_);
lean_ctor_set(v___x_3671_, 0, v___x_3676_);
v___x_3680_ = v___x_3671_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v___x_3676_);
lean_ctor_set(v_reuseFailAlloc_3684_, 1, v___x_3678_);
v___x_3680_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
size_t v___x_3681_; size_t v___x_3682_; 
v___x_3681_ = ((size_t)1ULL);
v___x_3682_ = lean_usize_add(v_i_3663_, v___x_3681_);
v_i_3663_ = v___x_3682_;
v_b_3664_ = v___x_3680_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1___redArg___boxed(lean_object* v_as_3686_, lean_object* v_sz_3687_, lean_object* v_i_3688_, lean_object* v_b_3689_, lean_object* v___y_3690_){
_start:
{
size_t v_sz_boxed_3691_; size_t v_i_boxed_3692_; lean_object* v_res_3693_; 
v_sz_boxed_3691_ = lean_unbox_usize(v_sz_3687_);
lean_dec(v_sz_3687_);
v_i_boxed_3692_ = lean_unbox_usize(v_i_3688_);
lean_dec(v_i_3688_);
v_res_3693_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1___redArg(v_as_3686_, v_sz_boxed_3691_, v_i_boxed_3692_, v_b_3689_);
lean_dec_ref(v_as_3686_);
return v_res_3693_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__0(void){
_start:
{
lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; 
v___x_3694_ = lean_box(0);
v___x_3695_ = lean_unsigned_to_nat(16u);
v___x_3696_ = lean_mk_array(v___x_3695_, v___x_3694_);
return v___x_3696_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__1(void){
_start:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; 
v___x_3697_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__0, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__0_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__0);
v___x_3698_ = lean_unsigned_to_nat(0u);
v___x_3699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3699_, 0, v___x_3698_);
lean_ctor_set(v___x_3699_, 1, v___x_3697_);
return v___x_3699_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__2(void){
_start:
{
lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; 
v___x_3700_ = lean_unsigned_to_nat(0u);
v___x_3701_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__1, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__1_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__1);
v___x_3702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3702_, 0, v___x_3701_);
lean_ctor_set(v___x_3702_, 1, v___x_3700_);
return v___x_3702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets(lean_object* v_e_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_, lean_object* v_a_3710_){
_start:
{
lean_object* v___x_3712_; lean_object* v_decls_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; uint8_t v___x_3716_; 
v___x_3712_ = lean_st_ref_get(v_a_3704_);
v_decls_3713_ = lean_ctor_get(v___x_3712_, 3);
lean_inc_ref(v_decls_3713_);
lean_dec(v___x_3712_);
v___x_3714_ = lean_array_get_size(v_decls_3713_);
v___x_3715_ = lean_unsigned_to_nat(0u);
v___x_3716_ = lean_nat_dec_eq(v___x_3714_, v___x_3715_);
if (v___x_3716_ == 0)
{
lean_object* v___x_3717_; lean_object* v___x_3718_; size_t v_sz_3719_; size_t v___x_3720_; lean_object* v___x_3721_; 
v___x_3717_ = lean_unsigned_to_nat(16u);
v___x_3718_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__2);
v_sz_3719_ = lean_array_size(v_decls_3713_);
v___x_3720_ = ((size_t)0ULL);
v___x_3721_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1___redArg(v_decls_3713_, v_sz_3719_, v___x_3720_, v___x_3718_);
if (lean_obj_tag(v___x_3721_) == 0)
{
lean_object* v_a_3722_; lean_object* v_fst_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3773_; 
v_a_3722_ = lean_ctor_get(v___x_3721_, 0);
lean_inc(v_a_3722_);
lean_dec_ref_known(v___x_3721_, 1);
v_fst_3723_ = lean_ctor_get(v_a_3722_, 0);
v_isSharedCheck_3773_ = !lean_is_exclusive(v_a_3722_);
if (v_isSharedCheck_3773_ == 0)
{
lean_object* v_unused_3774_; 
v_unused_3774_ = lean_ctor_get(v_a_3722_, 1);
lean_dec(v_unused_3774_);
v___x_3725_ = v_a_3722_;
v_isShared_3726_ = v_isSharedCheck_3773_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_fst_3723_);
lean_dec(v_a_3722_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3773_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v_a_3728_; lean_object* v___x_3752_; lean_object* v___x_3753_; uint8_t v_debug_3754_; lean_object* v_env_3755_; lean_object* v___x_3756_; lean_object* v___f_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; 
v___x_3752_ = lean_st_ref_get(v_a_3706_);
v___x_3753_ = lean_st_ref_get(v_a_3710_);
v_debug_3754_ = lean_ctor_get_uint8(v___x_3752_, sizeof(void*)*11);
lean_dec(v___x_3752_);
v_env_3755_ = lean_ctor_get(v___x_3753_, 0);
lean_inc_ref(v_env_3755_);
lean_dec(v___x_3753_);
v___x_3756_ = lean_box(v_debug_3754_);
lean_inc(v_fst_3723_);
v___f_3757_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___lam__0___boxed), 8, 6);
lean_closure_set(v___f_3757_, 0, v_e_3703_);
lean_closure_set(v___f_3757_, 1, v___x_3717_);
lean_closure_set(v___f_3757_, 2, v___x_3715_);
lean_closure_set(v___f_3757_, 3, v_fst_3723_);
lean_closure_set(v___f_3757_, 4, v___x_3714_);
lean_closure_set(v___f_3757_, 5, v___x_3756_);
v___x_3758_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_3758_, 0, v_env_3755_);
lean_ctor_set_uint8(v___x_3758_, sizeof(void*)*1, v___x_3716_);
lean_ctor_set_uint8(v___x_3758_, sizeof(void*)*1 + 1, v___x_3716_);
v___x_3759_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_3757_, v___x_3758_, v_a_3706_);
if (lean_obj_tag(v___x_3759_) == 0)
{
lean_object* v_a_3760_; 
v_a_3760_ = lean_ctor_get(v___x_3759_, 0);
lean_inc(v_a_3760_);
lean_dec_ref_known(v___x_3759_, 1);
if (lean_obj_tag(v_a_3760_) == 0)
{
lean_object* v___x_3761_; lean_object* v___x_3762_; 
lean_dec_ref_known(v_a_3760_, 1);
v___x_3761_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2);
v___x_3762_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1(v___x_3761_, v_a_3705_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_);
if (lean_obj_tag(v___x_3762_) == 0)
{
lean_object* v_a_3763_; 
v_a_3763_ = lean_ctor_get(v___x_3762_, 0);
lean_inc(v_a_3763_);
lean_dec_ref_known(v___x_3762_, 1);
v_a_3728_ = v_a_3763_;
goto v___jp_3727_;
}
else
{
lean_del_object(v___x_3725_);
lean_dec(v_fst_3723_);
lean_dec_ref(v_decls_3713_);
return v___x_3762_;
}
}
else
{
lean_object* v_a_3764_; 
v_a_3764_ = lean_ctor_get(v_a_3760_, 0);
lean_inc(v_a_3764_);
lean_dec_ref_known(v_a_3760_, 1);
v_a_3728_ = v_a_3764_;
goto v___jp_3727_;
}
}
else
{
lean_object* v_a_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3772_; 
lean_del_object(v___x_3725_);
lean_dec(v_fst_3723_);
lean_dec_ref(v_decls_3713_);
v_a_3765_ = lean_ctor_get(v___x_3759_, 0);
v_isSharedCheck_3772_ = !lean_is_exclusive(v___x_3759_);
if (v_isSharedCheck_3772_ == 0)
{
v___x_3767_ = v___x_3759_;
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_a_3765_);
lean_dec(v___x_3759_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
lean_object* v___x_3770_; 
if (v_isShared_3768_ == 0)
{
v___x_3770_ = v___x_3767_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v_a_3765_);
v___x_3770_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
return v___x_3770_;
}
}
}
v___jp_3727_:
{
lean_object* v___x_3729_; lean_object* v___x_3731_; 
v___x_3729_ = l_Array_reverse___redArg(v_decls_3713_);
if (v_isShared_3726_ == 0)
{
lean_ctor_set(v___x_3725_, 1, v___x_3714_);
lean_ctor_set(v___x_3725_, 0, v_a_3728_);
v___x_3731_ = v___x_3725_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v_a_3728_);
lean_ctor_set(v_reuseFailAlloc_3751_, 1, v___x_3714_);
v___x_3731_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
size_t v_sz_3732_; lean_object* v___x_3733_; 
v_sz_3732_ = lean_array_size(v___x_3729_);
v___x_3733_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7(v_fst_3723_, v___x_3714_, v___x_3729_, v_sz_3732_, v___x_3720_, v___x_3731_, v_a_3704_, v_a_3705_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_);
lean_dec_ref(v___x_3729_);
if (lean_obj_tag(v___x_3733_) == 0)
{
lean_object* v_a_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3742_; 
v_a_3734_ = lean_ctor_get(v___x_3733_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3733_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3736_ = v___x_3733_;
v_isShared_3737_ = v_isSharedCheck_3742_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_a_3734_);
lean_dec(v___x_3733_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3742_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v_fst_3738_; lean_object* v___x_3740_; 
v_fst_3738_ = lean_ctor_get(v_a_3734_, 0);
lean_inc(v_fst_3738_);
lean_dec(v_a_3734_);
if (v_isShared_3737_ == 0)
{
lean_ctor_set(v___x_3736_, 0, v_fst_3738_);
v___x_3740_ = v___x_3736_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_fst_3738_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
return v___x_3740_;
}
}
}
else
{
lean_object* v_a_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3750_; 
v_a_3743_ = lean_ctor_get(v___x_3733_, 0);
v_isSharedCheck_3750_ = !lean_is_exclusive(v___x_3733_);
if (v_isSharedCheck_3750_ == 0)
{
v___x_3745_ = v___x_3733_;
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_a_3743_);
lean_dec(v___x_3733_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v___x_3748_; 
if (v_isShared_3746_ == 0)
{
v___x_3748_ = v___x_3745_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v_a_3743_);
v___x_3748_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
return v___x_3748_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3775_; lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_3782_; 
lean_dec_ref(v_decls_3713_);
lean_dec_ref(v_e_3703_);
v_a_3775_ = lean_ctor_get(v___x_3721_, 0);
v_isSharedCheck_3782_ = !lean_is_exclusive(v___x_3721_);
if (v_isSharedCheck_3782_ == 0)
{
v___x_3777_ = v___x_3721_;
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
else
{
lean_inc(v_a_3775_);
lean_dec(v___x_3721_);
v___x_3777_ = lean_box(0);
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
v_resetjp_3776_:
{
lean_object* v___x_3780_; 
if (v_isShared_3778_ == 0)
{
v___x_3780_ = v___x_3777_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_a_3775_);
v___x_3780_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
return v___x_3780_;
}
}
}
}
else
{
lean_object* v___x_3783_; 
lean_dec_ref(v_decls_3713_);
v___x_3783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3783_, 0, v_e_3703_);
return v___x_3783_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___boxed(lean_object* v_e_3784_, lean_object* v_a_3785_, lean_object* v_a_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_){
_start:
{
lean_object* v_res_3793_; 
v_res_3793_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets(v_e_3784_, v_a_3785_, v_a_3786_, v_a_3787_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_);
lean_dec(v_a_3791_);
lean_dec_ref(v_a_3790_);
lean_dec(v_a_3789_);
lean_dec_ref(v_a_3788_);
lean_dec(v_a_3787_);
lean_dec_ref(v_a_3786_);
lean_dec(v_a_3785_);
return v_res_3793_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0(lean_object* v_00_u03b2_3794_, lean_object* v_m_3795_, lean_object* v_a_3796_, lean_object* v_b_3797_){
_start:
{
lean_object* v___x_3798_; 
v___x_3798_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0___redArg(v_m_3795_, v_a_3796_, v_b_3797_);
return v___x_3798_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1(lean_object* v_as_3799_, size_t v_sz_3800_, size_t v_i_3801_, lean_object* v_b_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_){
_start:
{
lean_object* v___x_3811_; 
v___x_3811_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1___redArg(v_as_3799_, v_sz_3800_, v_i_3801_, v_b_3802_);
return v___x_3811_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1___boxed(lean_object* v_as_3812_, lean_object* v_sz_3813_, lean_object* v_i_3814_, lean_object* v_b_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_){
_start:
{
size_t v_sz_boxed_3824_; size_t v_i_boxed_3825_; lean_object* v_res_3826_; 
v_sz_boxed_3824_ = lean_unbox_usize(v_sz_3813_);
lean_dec(v_sz_3813_);
v_i_boxed_3825_ = lean_unbox_usize(v_i_3814_);
lean_dec(v_i_3814_);
v_res_3826_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1(v_as_3812_, v_sz_boxed_3824_, v_i_boxed_3825_, v_b_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_);
lean_dec(v___y_3822_);
lean_dec_ref(v___y_3821_);
lean_dec(v___y_3820_);
lean_dec_ref(v___y_3819_);
lean_dec(v___y_3818_);
lean_dec_ref(v___y_3817_);
lean_dec(v___y_3816_);
lean_dec_ref(v_as_3812_);
return v_res_3826_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2(lean_object* v_00_u03b2_3827_, lean_object* v_m_3828_, lean_object* v_a_3829_){
_start:
{
lean_object* v___x_3830_; 
v___x_3830_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___redArg(v_m_3828_, v_a_3829_);
return v___x_3830_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___boxed(lean_object* v_00_u03b2_3831_, lean_object* v_m_3832_, lean_object* v_a_3833_){
_start:
{
lean_object* v_res_3834_; 
v_res_3834_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2(v_00_u03b2_3831_, v_m_3832_, v_a_3833_);
lean_dec(v_a_3833_);
lean_dec_ref(v_m_3832_);
return v_res_3834_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0(lean_object* v_00_u03b2_3835_, lean_object* v_a_3836_, lean_object* v_x_3837_){
_start:
{
uint8_t v___x_3838_; 
v___x_3838_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0___redArg(v_a_3836_, v_x_3837_);
return v___x_3838_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3839_, lean_object* v_a_3840_, lean_object* v_x_3841_){
_start:
{
uint8_t v_res_3842_; lean_object* v_r_3843_; 
v_res_3842_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0(v_00_u03b2_3839_, v_a_3840_, v_x_3841_);
lean_dec(v_x_3841_);
lean_dec(v_a_3840_);
v_r_3843_ = lean_box(v_res_3842_);
return v_r_3843_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1(lean_object* v_00_u03b2_3844_, lean_object* v_data_3845_){
_start:
{
lean_object* v___x_3846_; 
v___x_3846_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1___redArg(v_data_3845_);
return v___x_3846_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__2(lean_object* v_00_u03b2_3847_, lean_object* v_a_3848_, lean_object* v_b_3849_, lean_object* v_x_3850_){
_start:
{
lean_object* v___x_3851_; 
v___x_3851_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__2___redArg(v_a_3848_, v_b_3849_, v_x_3850_);
return v___x_3851_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2_spec__5(lean_object* v_00_u03b2_3852_, lean_object* v_a_3853_, lean_object* v_x_3854_){
_start:
{
lean_object* v___x_3855_; 
v___x_3855_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2_spec__5___redArg(v_a_3853_, v_x_3854_);
return v___x_3855_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3856_, lean_object* v_a_3857_, lean_object* v_x_3858_){
_start:
{
lean_object* v_res_3859_; 
v_res_3859_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2_spec__5(v_00_u03b2_3856_, v_a_3857_, v_x_3858_);
lean_dec(v_x_3858_);
lean_dec(v_a_3857_);
return v_res_3859_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_3860_, lean_object* v_i_3861_, lean_object* v_source_3862_, lean_object* v_target_3863_){
_start:
{
lean_object* v___x_3864_; 
v___x_3864_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1_spec__5___redArg(v_i_3861_, v_source_3862_, v_target_3863_);
return v___x_3864_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1_spec__5_spec__10(lean_object* v_00_u03b2_3865_, lean_object* v_x_3866_, lean_object* v_x_3867_){
_start:
{
lean_object* v___x_3868_; 
v___x_3868_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1_spec__5_spec__10___redArg(v_x_3866_, v_x_3867_);
return v___x_3868_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0___redArg(lean_object* v_msg_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_){
_start:
{
lean_object* v_ref_3875_; lean_object* v___x_3876_; lean_object* v_a_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3885_; 
v_ref_3875_ = lean_ctor_get(v___y_3872_, 4);
v___x_3876_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5_spec__5(v_msg_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_);
v_a_3877_ = lean_ctor_get(v___x_3876_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3879_ = v___x_3876_;
v_isShared_3880_ = v_isSharedCheck_3885_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_a_3877_);
lean_dec(v___x_3876_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3885_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
lean_object* v___x_3881_; lean_object* v___x_3883_; 
lean_inc(v_ref_3875_);
v___x_3881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3881_, 0, v_ref_3875_);
lean_ctor_set(v___x_3881_, 1, v_a_3877_);
if (v_isShared_3880_ == 0)
{
lean_ctor_set_tag(v___x_3879_, 1);
lean_ctor_set(v___x_3879_, 0, v___x_3881_);
v___x_3883_ = v___x_3879_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v___x_3881_);
v___x_3883_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
return v___x_3883_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0___redArg___boxed(lean_object* v_msg_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_){
_start:
{
lean_object* v_res_3892_; 
v_res_3892_ = l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0___redArg(v_msg_3886_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_);
lean_dec(v___y_3890_);
lean_dec_ref(v___y_3889_);
lean_dec(v___y_3888_);
lean_dec_ref(v___y_3887_);
return v_res_3892_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_liftLets___closed__0(void){
_start:
{
lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; 
v___x_3893_ = lean_box(0);
v___x_3894_ = lean_unsigned_to_nat(16u);
v___x_3895_ = lean_mk_array(v___x_3894_, v___x_3893_);
return v___x_3895_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_liftLets___closed__1(void){
_start:
{
lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; 
v___x_3896_ = lean_obj_once(&l_Lean_Meta_Sym_liftLets___closed__0, &l_Lean_Meta_Sym_liftLets___closed__0_once, _init_l_Lean_Meta_Sym_liftLets___closed__0);
v___x_3897_ = lean_unsigned_to_nat(0u);
v___x_3898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3898_, 0, v___x_3897_);
lean_ctor_set(v___x_3898_, 1, v___x_3896_);
return v___x_3898_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_liftLets___closed__3(void){
_start:
{
lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; 
v___x_3901_ = ((lean_object*)(l_Lean_Meta_Sym_liftLets___closed__2));
v___x_3902_ = lean_obj_once(&l_Lean_Meta_Sym_liftLets___closed__1, &l_Lean_Meta_Sym_liftLets___closed__1_once, _init_l_Lean_Meta_Sym_liftLets___closed__1);
v___x_3903_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3903_, 0, v___x_3902_);
lean_ctor_set(v___x_3903_, 1, v___x_3902_);
lean_ctor_set(v___x_3903_, 2, v___x_3902_);
lean_ctor_set(v___x_3903_, 3, v___x_3901_);
lean_ctor_set(v___x_3903_, 4, v___x_3902_);
return v___x_3903_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_liftLets___closed__5(void){
_start:
{
lean_object* v___x_3905_; lean_object* v___x_3906_; 
v___x_3905_ = ((lean_object*)(l_Lean_Meta_Sym_liftLets___closed__4));
v___x_3906_ = l_Lean_stringToMessageData(v___x_3905_);
return v___x_3906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLets(lean_object* v_e_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_){
_start:
{
lean_object* v___y_3916_; lean_object* v___y_3917_; lean_object* v___y_3928_; lean_object* v___y_3929_; lean_object* v___y_3930_; lean_object* v___y_3931_; lean_object* v___y_3932_; lean_object* v___y_3933_; uint8_t v___x_3940_; 
v___x_3940_ = l_Lean_Expr_hasLooseBVars(v_e_3907_);
if (v___x_3940_ == 0)
{
v___y_3928_ = v_a_3908_;
v___y_3929_ = v_a_3909_;
v___y_3930_ = v_a_3910_;
v___y_3931_ = v_a_3911_;
v___y_3932_ = v_a_3912_;
v___y_3933_ = v_a_3913_;
goto v___jp_3927_;
}
else
{
lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v_a_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_3950_; 
lean_dec_ref(v_e_3907_);
v___x_3941_ = lean_obj_once(&l_Lean_Meta_Sym_liftLets___closed__5, &l_Lean_Meta_Sym_liftLets___closed__5_once, _init_l_Lean_Meta_Sym_liftLets___closed__5);
v___x_3942_ = l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0___redArg(v___x_3941_, v_a_3910_, v_a_3911_, v_a_3912_, v_a_3913_);
v_a_3943_ = lean_ctor_get(v___x_3942_, 0);
v_isSharedCheck_3950_ = !lean_is_exclusive(v___x_3942_);
if (v_isSharedCheck_3950_ == 0)
{
v___x_3945_ = v___x_3942_;
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_a_3943_);
lean_dec(v___x_3942_);
v___x_3945_ = lean_box(0);
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
v_resetjp_3944_:
{
lean_object* v___x_3948_; 
if (v_isShared_3946_ == 0)
{
v___x_3948_ = v___x_3945_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v_a_3943_);
v___x_3948_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
return v___x_3948_;
}
}
}
v___jp_3915_:
{
if (lean_obj_tag(v___y_3917_) == 0)
{
lean_object* v_a_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3926_; 
v_a_3918_ = lean_ctor_get(v___y_3917_, 0);
v_isSharedCheck_3926_ = !lean_is_exclusive(v___y_3917_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3920_ = v___y_3917_;
v_isShared_3921_ = v_isSharedCheck_3926_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_a_3918_);
lean_dec(v___y_3917_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3926_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
lean_object* v___x_3922_; lean_object* v___x_3924_; 
v___x_3922_ = lean_st_ref_get(v___y_3916_);
lean_dec(v___y_3916_);
lean_dec(v___x_3922_);
if (v_isShared_3921_ == 0)
{
v___x_3924_ = v___x_3920_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_a_3918_);
v___x_3924_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
return v___x_3924_;
}
}
}
else
{
lean_dec(v___y_3916_);
return v___y_3917_;
}
}
v___jp_3927_:
{
lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; 
v___x_3934_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__3, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__3_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__3);
v___x_3935_ = lean_obj_once(&l_Lean_Meta_Sym_liftLets___closed__3, &l_Lean_Meta_Sym_liftLets___closed__3_once, _init_l_Lean_Meta_Sym_liftLets___closed__3);
v___x_3936_ = lean_st_mk_ref(v___x_3935_);
v___x_3937_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v___x_3934_, v_e_3907_, v___x_3936_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_);
if (lean_obj_tag(v___x_3937_) == 0)
{
lean_object* v_a_3938_; lean_object* v___x_3939_; 
v_a_3938_ = lean_ctor_get(v___x_3937_, 0);
lean_inc(v_a_3938_);
lean_dec_ref_known(v___x_3937_, 1);
v___x_3939_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets(v_a_3938_, v___x_3936_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_);
v___y_3916_ = v___x_3936_;
v___y_3917_ = v___x_3939_;
goto v___jp_3915_;
}
else
{
v___y_3916_ = v___x_3936_;
v___y_3917_ = v___x_3937_;
goto v___jp_3915_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLets___boxed(lean_object* v_e_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_){
_start:
{
lean_object* v_res_3959_; 
v_res_3959_ = l_Lean_Meta_Sym_liftLets(v_e_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_);
lean_dec(v_a_3957_);
lean_dec_ref(v_a_3956_);
lean_dec(v_a_3955_);
lean_dec_ref(v_a_3954_);
lean_dec(v_a_3953_);
lean_dec_ref(v_a_3952_);
return v_res_3959_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0(lean_object* v_00_u03b1_3960_, lean_object* v_msg_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_){
_start:
{
lean_object* v___x_3969_; 
v___x_3969_ = l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0___redArg(v_msg_3961_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_);
return v___x_3969_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0___boxed(lean_object* v_00_u03b1_3970_, lean_object* v_msg_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_){
_start:
{
lean_object* v_res_3979_; 
v_res_3979_ = l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0(v_00_u03b1_3970_, v_msg_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_);
lean_dec(v___y_3977_);
lean_dec_ref(v___y_3976_);
lean_dec(v___y_3975_);
lean_dec_ref(v___y_3974_);
lean_dec(v___y_3973_);
lean_dec_ref(v___y_3972_);
return v_res_3979_;
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
