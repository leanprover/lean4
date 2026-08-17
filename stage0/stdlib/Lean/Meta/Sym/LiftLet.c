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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_key_486_; lean_object* v_value_487_; lean_object* v_tail_488_; uint8_t v___y_490_; lean_object* v_fst_493_; lean_object* v_snd_494_; lean_object* v_fst_495_; lean_object* v_snd_496_; size_t v___x_497_; size_t v___x_498_; uint8_t v___x_499_; 
v_key_486_ = lean_ctor_get(v_x_484_, 0);
v_value_487_ = lean_ctor_get(v_x_484_, 1);
v_tail_488_ = lean_ctor_get(v_x_484_, 2);
v_fst_493_ = lean_ctor_get(v_key_486_, 0);
v_snd_494_ = lean_ctor_get(v_key_486_, 1);
v_fst_495_ = lean_ctor_get(v_a_483_, 0);
v_snd_496_ = lean_ctor_get(v_a_483_, 1);
v___x_497_ = lean_ptr_addr(v_fst_493_);
v___x_498_ = lean_ptr_addr(v_fst_495_);
v___x_499_ = lean_usize_dec_eq(v___x_497_, v___x_498_);
if (v___x_499_ == 0)
{
v___y_490_ = v___x_499_;
goto v___jp_489_;
}
else
{
size_t v___x_500_; size_t v___x_501_; uint8_t v___x_502_; 
v___x_500_ = lean_ptr_addr(v_snd_494_);
v___x_501_ = lean_ptr_addr(v_snd_496_);
v___x_502_ = lean_usize_dec_eq(v___x_500_, v___x_501_);
v___y_490_ = v___x_502_;
goto v___jp_489_;
}
v___jp_489_:
{
if (v___y_490_ == 0)
{
v_x_484_ = v_tail_488_;
goto _start;
}
else
{
lean_object* v___x_492_; 
lean_inc(v_value_487_);
v___x_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_492_, 0, v_value_487_);
return v___x_492_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0___redArg___boxed(lean_object* v_a_503_, lean_object* v_x_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0___redArg(v_a_503_, v_x_504_);
lean_dec(v_x_504_);
lean_dec_ref(v_a_503_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0___redArg(lean_object* v_m_506_, lean_object* v_a_507_){
_start:
{
lean_object* v_buckets_508_; lean_object* v_fst_509_; lean_object* v_snd_510_; lean_object* v___x_511_; size_t v___x_512_; size_t v___x_513_; size_t v___x_514_; uint64_t v___x_515_; size_t v___x_516_; size_t v___x_517_; uint64_t v___x_518_; uint64_t v___x_519_; uint64_t v___x_520_; uint64_t v___x_521_; uint64_t v_fold_522_; uint64_t v___x_523_; uint64_t v___x_524_; uint64_t v___x_525_; size_t v___x_526_; size_t v___x_527_; size_t v___x_528_; size_t v___x_529_; size_t v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v_buckets_508_ = lean_ctor_get(v_m_506_, 1);
v_fst_509_ = lean_ctor_get(v_a_507_, 0);
v_snd_510_ = lean_ctor_get(v_a_507_, 1);
v___x_511_ = lean_array_get_size(v_buckets_508_);
v___x_512_ = lean_ptr_addr(v_fst_509_);
v___x_513_ = ((size_t)3ULL);
v___x_514_ = lean_usize_shift_right(v___x_512_, v___x_513_);
v___x_515_ = lean_usize_to_uint64(v___x_514_);
v___x_516_ = lean_ptr_addr(v_snd_510_);
v___x_517_ = lean_usize_shift_right(v___x_516_, v___x_513_);
v___x_518_ = lean_usize_to_uint64(v___x_517_);
v___x_519_ = lean_uint64_mix_hash(v___x_515_, v___x_518_);
v___x_520_ = 32ULL;
v___x_521_ = lean_uint64_shift_right(v___x_519_, v___x_520_);
v_fold_522_ = lean_uint64_xor(v___x_519_, v___x_521_);
v___x_523_ = 16ULL;
v___x_524_ = lean_uint64_shift_right(v_fold_522_, v___x_523_);
v___x_525_ = lean_uint64_xor(v_fold_522_, v___x_524_);
v___x_526_ = lean_uint64_to_usize(v___x_525_);
v___x_527_ = lean_usize_of_nat(v___x_511_);
v___x_528_ = ((size_t)1ULL);
v___x_529_ = lean_usize_sub(v___x_527_, v___x_528_);
v___x_530_ = lean_usize_land(v___x_526_, v___x_529_);
v___x_531_ = lean_array_uget_borrowed(v_buckets_508_, v___x_530_);
v___x_532_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0___redArg(v_a_507_, v___x_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0___redArg___boxed(lean_object* v_m_533_, lean_object* v_a_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0___redArg(v_m_533_, v_a_534_);
lean_dec_ref(v_a_534_);
lean_dec_ref(v_m_533_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__7___redArg(lean_object* v_a_536_, lean_object* v_b_537_, lean_object* v_x_538_){
_start:
{
if (lean_obj_tag(v_x_538_) == 0)
{
lean_dec(v_b_537_);
lean_dec_ref(v_a_536_);
return v_x_538_;
}
else
{
lean_object* v_key_539_; lean_object* v_value_540_; lean_object* v_tail_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_564_; 
v_key_539_ = lean_ctor_get(v_x_538_, 0);
v_value_540_ = lean_ctor_get(v_x_538_, 1);
v_tail_541_ = lean_ctor_get(v_x_538_, 2);
v_isSharedCheck_564_ = !lean_is_exclusive(v_x_538_);
if (v_isSharedCheck_564_ == 0)
{
v___x_543_ = v_x_538_;
v_isShared_544_ = v_isSharedCheck_564_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_tail_541_);
lean_inc(v_value_540_);
lean_inc(v_key_539_);
lean_dec(v_x_538_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_564_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
uint8_t v___y_546_; lean_object* v_fst_554_; lean_object* v_snd_555_; lean_object* v_fst_556_; lean_object* v_snd_557_; size_t v___x_558_; size_t v___x_559_; uint8_t v___x_560_; 
v_fst_554_ = lean_ctor_get(v_key_539_, 0);
v_snd_555_ = lean_ctor_get(v_key_539_, 1);
v_fst_556_ = lean_ctor_get(v_a_536_, 0);
v_snd_557_ = lean_ctor_get(v_a_536_, 1);
v___x_558_ = lean_ptr_addr(v_fst_554_);
v___x_559_ = lean_ptr_addr(v_fst_556_);
v___x_560_ = lean_usize_dec_eq(v___x_558_, v___x_559_);
if (v___x_560_ == 0)
{
v___y_546_ = v___x_560_;
goto v___jp_545_;
}
else
{
size_t v___x_561_; size_t v___x_562_; uint8_t v___x_563_; 
v___x_561_ = lean_ptr_addr(v_snd_555_);
v___x_562_ = lean_ptr_addr(v_snd_557_);
v___x_563_ = lean_usize_dec_eq(v___x_561_, v___x_562_);
v___y_546_ = v___x_563_;
goto v___jp_545_;
}
v___jp_545_:
{
if (v___y_546_ == 0)
{
lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_547_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__7___redArg(v_a_536_, v_b_537_, v_tail_541_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 2, v___x_547_);
v___x_549_ = v___x_543_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_key_539_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v_value_540_);
lean_ctor_set(v_reuseFailAlloc_550_, 2, v___x_547_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
else
{
lean_object* v___x_552_; 
lean_dec(v_value_540_);
lean_dec(v_key_539_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 1, v_b_537_);
lean_ctor_set(v___x_543_, 0, v_a_536_);
v___x_552_ = v___x_543_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_536_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_b_537_);
lean_ctor_set(v_reuseFailAlloc_553_, 2, v_tail_541_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5___redArg(lean_object* v_a_565_, lean_object* v_x_566_){
_start:
{
if (lean_obj_tag(v_x_566_) == 0)
{
uint8_t v___x_567_; 
v___x_567_ = 0;
return v___x_567_;
}
else
{
lean_object* v_key_568_; lean_object* v_tail_569_; uint8_t v___y_571_; lean_object* v_fst_573_; lean_object* v_snd_574_; lean_object* v_fst_575_; lean_object* v_snd_576_; size_t v___x_577_; size_t v___x_578_; uint8_t v___x_579_; 
v_key_568_ = lean_ctor_get(v_x_566_, 0);
v_tail_569_ = lean_ctor_get(v_x_566_, 2);
v_fst_573_ = lean_ctor_get(v_key_568_, 0);
v_snd_574_ = lean_ctor_get(v_key_568_, 1);
v_fst_575_ = lean_ctor_get(v_a_565_, 0);
v_snd_576_ = lean_ctor_get(v_a_565_, 1);
v___x_577_ = lean_ptr_addr(v_fst_573_);
v___x_578_ = lean_ptr_addr(v_fst_575_);
v___x_579_ = lean_usize_dec_eq(v___x_577_, v___x_578_);
if (v___x_579_ == 0)
{
v___y_571_ = v___x_579_;
goto v___jp_570_;
}
else
{
size_t v___x_580_; size_t v___x_581_; uint8_t v___x_582_; 
v___x_580_ = lean_ptr_addr(v_snd_574_);
v___x_581_ = lean_ptr_addr(v_snd_576_);
v___x_582_ = lean_usize_dec_eq(v___x_580_, v___x_581_);
v___y_571_ = v___x_582_;
goto v___jp_570_;
}
v___jp_570_:
{
if (v___y_571_ == 0)
{
v_x_566_ = v_tail_569_;
goto _start;
}
else
{
return v___y_571_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5___redArg___boxed(lean_object* v_a_583_, lean_object* v_x_584_){
_start:
{
uint8_t v_res_585_; lean_object* v_r_586_; 
v_res_585_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5___redArg(v_a_583_, v_x_584_);
lean_dec(v_x_584_);
lean_dec_ref(v_a_583_);
v_r_586_ = lean_box(v_res_585_);
return v_r_586_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6_spec__7_spec__8___redArg(lean_object* v_x_587_, lean_object* v_x_588_){
_start:
{
if (lean_obj_tag(v_x_588_) == 0)
{
return v_x_587_;
}
else
{
lean_object* v_key_589_; lean_object* v_value_590_; lean_object* v_tail_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_623_; 
v_key_589_ = lean_ctor_get(v_x_588_, 0);
v_value_590_ = lean_ctor_get(v_x_588_, 1);
v_tail_591_ = lean_ctor_get(v_x_588_, 2);
v_isSharedCheck_623_ = !lean_is_exclusive(v_x_588_);
if (v_isSharedCheck_623_ == 0)
{
v___x_593_ = v_x_588_;
v_isShared_594_ = v_isSharedCheck_623_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_tail_591_);
lean_inc(v_value_590_);
lean_inc(v_key_589_);
lean_dec(v_x_588_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_623_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v_fst_595_; lean_object* v_snd_596_; lean_object* v___x_597_; size_t v___x_598_; size_t v___x_599_; size_t v___x_600_; uint64_t v___x_601_; size_t v___x_602_; size_t v___x_603_; uint64_t v___x_604_; uint64_t v___x_605_; uint64_t v___x_606_; uint64_t v___x_607_; uint64_t v_fold_608_; uint64_t v___x_609_; uint64_t v___x_610_; uint64_t v___x_611_; size_t v___x_612_; size_t v___x_613_; size_t v___x_614_; size_t v___x_615_; size_t v___x_616_; lean_object* v___x_617_; lean_object* v___x_619_; 
v_fst_595_ = lean_ctor_get(v_key_589_, 0);
v_snd_596_ = lean_ctor_get(v_key_589_, 1);
v___x_597_ = lean_array_get_size(v_x_587_);
v___x_598_ = lean_ptr_addr(v_fst_595_);
v___x_599_ = ((size_t)3ULL);
v___x_600_ = lean_usize_shift_right(v___x_598_, v___x_599_);
v___x_601_ = lean_usize_to_uint64(v___x_600_);
v___x_602_ = lean_ptr_addr(v_snd_596_);
v___x_603_ = lean_usize_shift_right(v___x_602_, v___x_599_);
v___x_604_ = lean_usize_to_uint64(v___x_603_);
v___x_605_ = lean_uint64_mix_hash(v___x_601_, v___x_604_);
v___x_606_ = 32ULL;
v___x_607_ = lean_uint64_shift_right(v___x_605_, v___x_606_);
v_fold_608_ = lean_uint64_xor(v___x_605_, v___x_607_);
v___x_609_ = 16ULL;
v___x_610_ = lean_uint64_shift_right(v_fold_608_, v___x_609_);
v___x_611_ = lean_uint64_xor(v_fold_608_, v___x_610_);
v___x_612_ = lean_uint64_to_usize(v___x_611_);
v___x_613_ = lean_usize_of_nat(v___x_597_);
v___x_614_ = ((size_t)1ULL);
v___x_615_ = lean_usize_sub(v___x_613_, v___x_614_);
v___x_616_ = lean_usize_land(v___x_612_, v___x_615_);
v___x_617_ = lean_array_uget_borrowed(v_x_587_, v___x_616_);
lean_inc(v___x_617_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 2, v___x_617_);
v___x_619_ = v___x_593_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_key_589_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v_value_590_);
lean_ctor_set(v_reuseFailAlloc_622_, 2, v___x_617_);
v___x_619_ = v_reuseFailAlloc_622_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_object* v___x_620_; 
v___x_620_ = lean_array_uset(v_x_587_, v___x_616_, v___x_619_);
v_x_587_ = v___x_620_;
v_x_588_ = v_tail_591_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6_spec__7___redArg(lean_object* v_i_624_, lean_object* v_source_625_, lean_object* v_target_626_){
_start:
{
lean_object* v___x_627_; uint8_t v___x_628_; 
v___x_627_ = lean_array_get_size(v_source_625_);
v___x_628_ = lean_nat_dec_lt(v_i_624_, v___x_627_);
if (v___x_628_ == 0)
{
lean_dec_ref(v_source_625_);
lean_dec(v_i_624_);
return v_target_626_;
}
else
{
lean_object* v_es_629_; lean_object* v___x_630_; lean_object* v_source_631_; lean_object* v_target_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v_es_629_ = lean_array_fget(v_source_625_, v_i_624_);
v___x_630_ = lean_box(0);
v_source_631_ = lean_array_fset(v_source_625_, v_i_624_, v___x_630_);
v_target_632_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6_spec__7_spec__8___redArg(v_target_626_, v_es_629_);
v___x_633_ = lean_unsigned_to_nat(1u);
v___x_634_ = lean_nat_add(v_i_624_, v___x_633_);
lean_dec(v_i_624_);
v_i_624_ = v___x_634_;
v_source_625_ = v_source_631_;
v_target_626_ = v_target_632_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6___redArg(lean_object* v_data_636_){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v_nbuckets_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_637_ = lean_array_get_size(v_data_636_);
v___x_638_ = lean_unsigned_to_nat(2u);
v_nbuckets_639_ = lean_nat_mul(v___x_637_, v___x_638_);
v___x_640_ = lean_unsigned_to_nat(0u);
v___x_641_ = lean_box(0);
v___x_642_ = lean_mk_array(v_nbuckets_639_, v___x_641_);
v___x_643_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6_spec__7___redArg(v___x_640_, v_data_636_, v___x_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3___redArg(lean_object* v_m_644_, lean_object* v_a_645_, lean_object* v_b_646_){
_start:
{
lean_object* v_size_647_; lean_object* v_buckets_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_700_; 
v_size_647_ = lean_ctor_get(v_m_644_, 0);
v_buckets_648_ = lean_ctor_get(v_m_644_, 1);
v_isSharedCheck_700_ = !lean_is_exclusive(v_m_644_);
if (v_isSharedCheck_700_ == 0)
{
v___x_650_ = v_m_644_;
v_isShared_651_ = v_isSharedCheck_700_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_buckets_648_);
lean_inc(v_size_647_);
lean_dec(v_m_644_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_700_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v_fst_652_; lean_object* v_snd_653_; lean_object* v___x_654_; size_t v___x_655_; size_t v___x_656_; size_t v___x_657_; uint64_t v___x_658_; size_t v___x_659_; size_t v___x_660_; uint64_t v___x_661_; uint64_t v___x_662_; uint64_t v___x_663_; uint64_t v___x_664_; uint64_t v_fold_665_; uint64_t v___x_666_; uint64_t v___x_667_; uint64_t v___x_668_; size_t v___x_669_; size_t v___x_670_; size_t v___x_671_; size_t v___x_672_; size_t v___x_673_; lean_object* v_bkt_674_; uint8_t v___x_675_; 
v_fst_652_ = lean_ctor_get(v_a_645_, 0);
v_snd_653_ = lean_ctor_get(v_a_645_, 1);
v___x_654_ = lean_array_get_size(v_buckets_648_);
v___x_655_ = lean_ptr_addr(v_fst_652_);
v___x_656_ = ((size_t)3ULL);
v___x_657_ = lean_usize_shift_right(v___x_655_, v___x_656_);
v___x_658_ = lean_usize_to_uint64(v___x_657_);
v___x_659_ = lean_ptr_addr(v_snd_653_);
v___x_660_ = lean_usize_shift_right(v___x_659_, v___x_656_);
v___x_661_ = lean_usize_to_uint64(v___x_660_);
v___x_662_ = lean_uint64_mix_hash(v___x_658_, v___x_661_);
v___x_663_ = 32ULL;
v___x_664_ = lean_uint64_shift_right(v___x_662_, v___x_663_);
v_fold_665_ = lean_uint64_xor(v___x_662_, v___x_664_);
v___x_666_ = 16ULL;
v___x_667_ = lean_uint64_shift_right(v_fold_665_, v___x_666_);
v___x_668_ = lean_uint64_xor(v_fold_665_, v___x_667_);
v___x_669_ = lean_uint64_to_usize(v___x_668_);
v___x_670_ = lean_usize_of_nat(v___x_654_);
v___x_671_ = ((size_t)1ULL);
v___x_672_ = lean_usize_sub(v___x_670_, v___x_671_);
v___x_673_ = lean_usize_land(v___x_669_, v___x_672_);
v_bkt_674_ = lean_array_uget_borrowed(v_buckets_648_, v___x_673_);
v___x_675_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5___redArg(v_a_645_, v_bkt_674_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; lean_object* v_size_x27_677_; lean_object* v___x_678_; lean_object* v_buckets_x27_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; uint8_t v___x_685_; 
v___x_676_ = lean_unsigned_to_nat(1u);
v_size_x27_677_ = lean_nat_add(v_size_647_, v___x_676_);
lean_dec(v_size_647_);
lean_inc(v_bkt_674_);
v___x_678_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_678_, 0, v_a_645_);
lean_ctor_set(v___x_678_, 1, v_b_646_);
lean_ctor_set(v___x_678_, 2, v_bkt_674_);
v_buckets_x27_679_ = lean_array_uset(v_buckets_648_, v___x_673_, v___x_678_);
v___x_680_ = lean_unsigned_to_nat(4u);
v___x_681_ = lean_nat_mul(v_size_x27_677_, v___x_680_);
v___x_682_ = lean_unsigned_to_nat(3u);
v___x_683_ = lean_nat_div(v___x_681_, v___x_682_);
lean_dec(v___x_681_);
v___x_684_ = lean_array_get_size(v_buckets_x27_679_);
v___x_685_ = lean_nat_dec_le(v___x_683_, v___x_684_);
lean_dec(v___x_683_);
if (v___x_685_ == 0)
{
lean_object* v_val_686_; lean_object* v___x_688_; 
v_val_686_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6___redArg(v_buckets_x27_679_);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 1, v_val_686_);
lean_ctor_set(v___x_650_, 0, v_size_x27_677_);
v___x_688_ = v___x_650_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_size_x27_677_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v_val_686_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
else
{
lean_object* v___x_691_; 
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 1, v_buckets_x27_679_);
lean_ctor_set(v___x_650_, 0, v_size_x27_677_);
v___x_691_ = v___x_650_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_size_x27_677_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_buckets_x27_679_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
else
{
lean_object* v___x_693_; lean_object* v_buckets_x27_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_698_; 
lean_inc(v_bkt_674_);
v___x_693_ = lean_box(0);
v_buckets_x27_694_ = lean_array_uset(v_buckets_648_, v___x_673_, v___x_693_);
v___x_695_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__7___redArg(v_a_645_, v_b_646_, v_bkt_674_);
v___x_696_ = lean_array_uset(v_buckets_x27_694_, v___x_673_, v___x_695_);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 1, v___x_696_);
v___x_698_ = v___x_650_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_size_647_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v___x_696_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl(lean_object* v_userName_701_, lean_object* v_type_702_, lean_object* v_value_703_, uint8_t v_nondep_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_){
_start:
{
lean_object* v___x_713_; lean_object* v_valueMap_714_; lean_object* v_key_715_; lean_object* v___x_716_; 
v___x_713_ = lean_st_ref_get(v_a_705_);
v_valueMap_714_ = lean_ctor_get(v___x_713_, 4);
lean_inc_ref(v_valueMap_714_);
lean_dec(v___x_713_);
lean_inc_ref(v_value_703_);
lean_inc_ref(v_type_702_);
v_key_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_715_, 0, v_type_702_);
lean_ctor_set(v_key_715_, 1, v_value_703_);
v___x_716_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0___redArg(v_valueMap_714_, v_key_715_);
lean_dec_ref(v_valueMap_714_);
if (lean_obj_tag(v___x_716_) == 1)
{
lean_object* v_val_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_764_; 
lean_dec_ref_known(v_key_715_, 2);
lean_dec_ref(v_value_703_);
lean_dec_ref(v_type_702_);
lean_dec(v_userName_701_);
v_val_717_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_764_ == 0)
{
v___x_719_ = v___x_716_;
v_isShared_720_ = v_isSharedCheck_764_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_val_717_);
lean_dec(v___x_716_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_764_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_721_; lean_object* v___y_723_; 
v___x_721_ = l_Lean_Meta_Sym_LiftLet_instInhabitedDecl_default;
if (v_nondep_704_ == 0)
{
lean_object* v___x_731_; lean_object* v_cache_732_; lean_object* v_cacheClosed_733_; lean_object* v_hasLetCache_734_; lean_object* v_decls_735_; lean_object* v_valueMap_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_763_; 
v___x_731_ = lean_st_ref_take(v_a_705_);
v_cache_732_ = lean_ctor_get(v___x_731_, 0);
v_cacheClosed_733_ = lean_ctor_get(v___x_731_, 1);
v_hasLetCache_734_ = lean_ctor_get(v___x_731_, 2);
v_decls_735_ = lean_ctor_get(v___x_731_, 3);
v_valueMap_736_ = lean_ctor_get(v___x_731_, 4);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_763_ == 0)
{
v___x_738_ = v___x_731_;
v_isShared_739_ = v_isSharedCheck_763_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_valueMap_736_);
lean_inc(v_decls_735_);
lean_inc(v_hasLetCache_734_);
lean_inc(v_cacheClosed_733_);
lean_inc(v_cache_732_);
lean_dec(v___x_731_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_763_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___y_741_; lean_object* v___x_746_; uint8_t v___x_747_; 
v___x_746_ = lean_array_get_size(v_decls_735_);
v___x_747_ = lean_nat_dec_lt(v_val_717_, v___x_746_);
if (v___x_747_ == 0)
{
v___y_741_ = v_decls_735_;
goto v___jp_740_;
}
else
{
lean_object* v_v_748_; lean_object* v_fvar_749_; lean_object* v_userName_750_; lean_object* v_type_751_; lean_object* v_value_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_762_; 
v_v_748_ = lean_array_fget(v_decls_735_, v_val_717_);
v_fvar_749_ = lean_ctor_get(v_v_748_, 0);
v_userName_750_ = lean_ctor_get(v_v_748_, 1);
v_type_751_ = lean_ctor_get(v_v_748_, 2);
v_value_752_ = lean_ctor_get(v_v_748_, 3);
v_isSharedCheck_762_ = !lean_is_exclusive(v_v_748_);
if (v_isSharedCheck_762_ == 0)
{
v___x_754_ = v_v_748_;
v_isShared_755_ = v_isSharedCheck_762_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_value_752_);
lean_inc(v_type_751_);
lean_inc(v_userName_750_);
lean_inc(v_fvar_749_);
lean_dec(v_v_748_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_762_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_756_; lean_object* v_xs_x27_757_; lean_object* v___x_759_; 
v___x_756_ = lean_box(0);
v_xs_x27_757_ = lean_array_fset(v_decls_735_, v_val_717_, v___x_756_);
if (v_isShared_755_ == 0)
{
v___x_759_ = v___x_754_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_fvar_749_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v_userName_750_);
lean_ctor_set(v_reuseFailAlloc_761_, 2, v_type_751_);
lean_ctor_set(v_reuseFailAlloc_761_, 3, v_value_752_);
v___x_759_ = v_reuseFailAlloc_761_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
lean_object* v___x_760_; 
lean_ctor_set_uint8(v___x_759_, sizeof(void*)*4, v_nondep_704_);
v___x_760_ = lean_array_fset(v_xs_x27_757_, v_val_717_, v___x_759_);
v___y_741_ = v___x_760_;
goto v___jp_740_;
}
}
}
v___jp_740_:
{
lean_object* v___x_743_; 
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 3, v___y_741_);
v___x_743_ = v___x_738_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_cache_732_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_cacheClosed_733_);
lean_ctor_set(v_reuseFailAlloc_745_, 2, v_hasLetCache_734_);
lean_ctor_set(v_reuseFailAlloc_745_, 3, v___y_741_);
lean_ctor_set(v_reuseFailAlloc_745_, 4, v_valueMap_736_);
v___x_743_ = v_reuseFailAlloc_745_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
lean_object* v___x_744_; 
v___x_744_ = lean_st_ref_put(v_a_705_, v___x_743_);
v___y_723_ = v_a_705_;
goto v___jp_722_;
}
}
}
}
else
{
v___y_723_ = v_a_705_;
goto v___jp_722_;
}
v___jp_722_:
{
lean_object* v___x_724_; lean_object* v_decls_725_; lean_object* v___x_726_; lean_object* v_fvar_727_; lean_object* v___x_729_; 
v___x_724_ = lean_st_ref_get(v___y_723_);
v_decls_725_ = lean_ctor_get(v___x_724_, 3);
lean_inc_ref(v_decls_725_);
lean_dec(v___x_724_);
v___x_726_ = lean_array_get(v___x_721_, v_decls_725_, v_val_717_);
lean_dec(v_val_717_);
lean_dec_ref(v_decls_725_);
v_fvar_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc_ref(v_fvar_727_);
lean_dec(v___x_726_);
if (v_isShared_720_ == 0)
{
lean_ctor_set_tag(v___x_719_, 0);
lean_ctor_set(v___x_719_, 0, v_fvar_727_);
v___x_729_ = v___x_719_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_fvar_727_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
else
{
lean_object* v___x_765_; 
lean_dec(v___x_716_);
v___x_765_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1(v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; lean_object* v___x_767_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_a_766_);
lean_dec_ref_known(v___x_765_, 1);
v___x_767_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2___redArg(v_a_766_, v_a_707_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_795_; 
v_a_768_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_795_ == 0)
{
v___x_770_ = v___x_767_;
v_isShared_771_ = v_isSharedCheck_795_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_767_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_795_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v_decls_774_; lean_object* v_cache_775_; lean_object* v_cacheClosed_776_; lean_object* v_hasLetCache_777_; lean_object* v_decls_778_; lean_object* v_valueMap_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_794_; 
v___x_772_ = lean_st_ref_get(v_a_705_);
v___x_773_ = lean_st_ref_take(v_a_705_);
v_decls_774_ = lean_ctor_get(v___x_772_, 3);
lean_inc_ref(v_decls_774_);
lean_dec(v___x_772_);
v_cache_775_ = lean_ctor_get(v___x_773_, 0);
v_cacheClosed_776_ = lean_ctor_get(v___x_773_, 1);
v_hasLetCache_777_ = lean_ctor_get(v___x_773_, 2);
v_decls_778_ = lean_ctor_get(v___x_773_, 3);
v_valueMap_779_ = lean_ctor_get(v___x_773_, 4);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_794_ == 0)
{
v___x_781_ = v___x_773_;
v_isShared_782_ = v_isSharedCheck_794_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_valueMap_779_);
lean_inc(v_decls_778_);
lean_inc(v_hasLetCache_777_);
lean_inc(v_cacheClosed_776_);
lean_inc(v_cache_775_);
lean_dec(v___x_773_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_794_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_788_; 
v___x_783_ = lean_array_get_size(v_decls_774_);
lean_dec_ref(v_decls_774_);
lean_inc(v_a_768_);
v___x_784_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_784_, 0, v_a_768_);
lean_ctor_set(v___x_784_, 1, v_userName_701_);
lean_ctor_set(v___x_784_, 2, v_type_702_);
lean_ctor_set(v___x_784_, 3, v_value_703_);
lean_ctor_set_uint8(v___x_784_, sizeof(void*)*4, v_nondep_704_);
v___x_785_ = lean_array_push(v_decls_778_, v___x_784_);
v___x_786_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3___redArg(v_valueMap_779_, v_key_715_, v___x_783_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 4, v___x_786_);
lean_ctor_set(v___x_781_, 3, v___x_785_);
v___x_788_ = v___x_781_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_cache_775_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_cacheClosed_776_);
lean_ctor_set(v_reuseFailAlloc_793_, 2, v_hasLetCache_777_);
lean_ctor_set(v_reuseFailAlloc_793_, 3, v___x_785_);
lean_ctor_set(v_reuseFailAlloc_793_, 4, v___x_786_);
v___x_788_ = v_reuseFailAlloc_793_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
lean_object* v___x_789_; lean_object* v___x_791_; 
v___x_789_ = lean_st_ref_put(v_a_705_, v___x_788_);
if (v_isShared_771_ == 0)
{
v___x_791_ = v___x_770_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_768_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_715_, 2);
lean_dec_ref(v_value_703_);
lean_dec_ref(v_type_702_);
lean_dec(v_userName_701_);
return v___x_767_;
}
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
lean_dec_ref_known(v_key_715_, 2);
lean_dec_ref(v_value_703_);
lean_dec_ref(v_type_702_);
lean_dec(v_userName_701_);
v_a_796_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_765_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_765_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl___boxed(lean_object* v_userName_804_, lean_object* v_type_805_, lean_object* v_value_806_, lean_object* v_nondep_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_){
_start:
{
uint8_t v_nondep_boxed_816_; lean_object* v_res_817_; 
v_nondep_boxed_816_ = lean_unbox(v_nondep_807_);
v_res_817_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl(v_userName_804_, v_type_805_, v_value_806_, v_nondep_boxed_816_, v_a_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_);
lean_dec(v_a_814_);
lean_dec_ref(v_a_813_);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0(lean_object* v_00_u03b2_818_, lean_object* v_m_819_, lean_object* v_a_820_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0___redArg(v_m_819_, v_a_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0___boxed(lean_object* v_00_u03b2_822_, lean_object* v_m_823_, lean_object* v_a_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0(v_00_u03b2_822_, v_m_823_, v_a_824_);
lean_dec_ref(v_a_824_);
lean_dec_ref(v_m_823_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2(lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2___redArg(v___y_832_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2___boxed(lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2(v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v___y_835_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3(lean_object* v_00_u03b2_844_, lean_object* v_m_845_, lean_object* v_a_846_, lean_object* v_b_847_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3___redArg(v_m_845_, v_a_846_, v_b_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0(lean_object* v_00_u03b2_849_, lean_object* v_a_850_, lean_object* v_x_851_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0___redArg(v_a_850_, v_x_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_853_, lean_object* v_a_854_, lean_object* v_x_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0(v_00_u03b2_853_, v_a_854_, v_x_855_);
lean_dec(v_x_855_);
lean_dec_ref(v_a_854_);
return v_res_856_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5(lean_object* v_00_u03b2_857_, lean_object* v_a_858_, lean_object* v_x_859_){
_start:
{
uint8_t v___x_860_; 
v___x_860_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5___redArg(v_a_858_, v_x_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5___boxed(lean_object* v_00_u03b2_861_, lean_object* v_a_862_, lean_object* v_x_863_){
_start:
{
uint8_t v_res_864_; lean_object* v_r_865_; 
v_res_864_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5(v_00_u03b2_861_, v_a_862_, v_x_863_);
lean_dec(v_x_863_);
lean_dec_ref(v_a_862_);
v_r_865_ = lean_box(v_res_864_);
return v_r_865_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6(lean_object* v_00_u03b2_866_, lean_object* v_data_867_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6___redArg(v_data_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__7(lean_object* v_00_u03b2_869_, lean_object* v_a_870_, lean_object* v_b_871_, lean_object* v_x_872_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__7___redArg(v_a_870_, v_b_871_, v_x_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6_spec__7(lean_object* v_00_u03b2_874_, lean_object* v_i_875_, lean_object* v_source_876_, lean_object* v_target_877_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6_spec__7___redArg(v_i_875_, v_source_876_, v_target_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6_spec__7_spec__8(lean_object* v_00_u03b2_879_, lean_object* v_x_880_, lean_object* v_x_881_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6_spec__7_spec__8___redArg(v_x_880_, v_x_881_);
return v___x_882_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1___closed__0(void){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1(lean_object* v_msg_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v___x_892_; lean_object* v___x_2252__overap_893_; lean_object* v___x_894_; 
v___x_892_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1___closed__0);
v___x_2252__overap_893_ = lean_panic_fn_borrowed(v___x_892_, v_msg_884_);
lean_inc(v___y_890_);
lean_inc_ref(v___y_889_);
lean_inc(v___y_888_);
lean_inc_ref(v___y_887_);
lean_inc(v___y_886_);
lean_inc_ref(v___y_885_);
v___x_894_ = lean_apply_7(v___x_2252__overap_893_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, lean_box(0));
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1___boxed(lean_object* v_msg_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1(v_msg_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__2(lean_object* v_x_904_, uint8_t v_bi_905_, lean_object* v_t_906_, lean_object* v_b_907_, lean_object* v___y_908_, uint8_t v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v___y_913_; lean_object* v___y_914_; 
if (v___y_909_ == 0)
{
v___y_913_ = v___y_908_;
v___y_914_ = v___y_911_;
goto v___jp_912_;
}
else
{
lean_object* v___x_936_; 
v___x_936_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_906_, v___y_909_, v___y_910_, v___y_911_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v_a_937_; lean_object* v___x_938_; 
v_a_937_ = lean_ctor_get(v___x_936_, 1);
lean_inc(v_a_937_);
lean_dec_ref_known(v___x_936_, 2);
v___x_938_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_907_, v___y_909_, v___y_910_, v_a_937_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v_a_939_; 
v_a_939_ = lean_ctor_get(v___x_938_, 1);
lean_inc(v_a_939_);
lean_dec_ref_known(v___x_938_, 2);
v___y_913_ = v___y_908_;
v___y_914_ = v_a_939_;
goto v___jp_912_;
}
else
{
lean_object* v_a_940_; lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_948_; 
lean_dec_ref(v___y_908_);
lean_dec_ref(v_b_907_);
lean_dec_ref(v_t_906_);
lean_dec(v_x_904_);
v_a_940_ = lean_ctor_get(v___x_938_, 0);
v_a_941_ = lean_ctor_get(v___x_938_, 1);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_948_ == 0)
{
v___x_943_ = v___x_938_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_inc(v_a_940_);
lean_dec(v___x_938_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_a_940_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_a_941_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
else
{
lean_object* v_a_949_; lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
lean_dec_ref(v___y_908_);
lean_dec_ref(v_b_907_);
lean_dec_ref(v_t_906_);
lean_dec(v_x_904_);
v_a_949_ = lean_ctor_get(v___x_936_, 0);
v_a_950_ = lean_ctor_get(v___x_936_, 1);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_957_ == 0)
{
v___x_952_ = v___x_936_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_inc(v_a_949_);
lean_dec(v___x_936_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_953_ == 0)
{
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_949_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v_a_950_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
v___jp_912_:
{
lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_915_ = l_Lean_Expr_lam___override(v_x_904_, v_t_906_, v_b_907_, v_bi_905_);
v___x_916_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_915_, v___y_914_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v_a_917_; lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_926_; 
v_a_917_ = lean_ctor_get(v___x_916_, 0);
v_a_918_ = lean_ctor_get(v___x_916_, 1);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_926_ == 0)
{
v___x_920_ = v___x_916_;
v_isShared_921_ = v_isSharedCheck_926_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_inc(v_a_917_);
lean_dec(v___x_916_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_926_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_922_; lean_object* v___x_924_; 
v___x_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_922_, 0, v_a_917_);
lean_ctor_set(v___x_922_, 1, v___y_913_);
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 0, v___x_922_);
v___x_924_ = v___x_920_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_922_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v_a_918_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
else
{
lean_object* v_a_927_; lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_935_; 
lean_dec_ref(v___y_913_);
v_a_927_ = lean_ctor_get(v___x_916_, 0);
v_a_928_ = lean_ctor_get(v___x_916_, 1);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_935_ == 0)
{
v___x_930_ = v___x_916_;
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_inc(v_a_927_);
lean_dec(v___x_916_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_927_);
lean_ctor_set(v_reuseFailAlloc_934_, 1, v_a_928_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__2___boxed(lean_object* v_x_958_, lean_object* v_bi_959_, lean_object* v_t_960_, lean_object* v_b_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
uint8_t v_bi_boxed_966_; uint8_t v___y_25191__boxed_967_; lean_object* v_res_968_; 
v_bi_boxed_966_ = lean_unbox(v_bi_959_);
v___y_25191__boxed_967_ = lean_unbox(v___y_963_);
v_res_968_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__2(v_x_958_, v_bi_boxed_966_, v_t_960_, v_b_961_, v___y_962_, v___y_25191__boxed_967_, v___y_964_, v___y_965_);
lean_dec_ref(v___y_964_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__6(lean_object* v_structName_969_, lean_object* v_idx_970_, lean_object* v_struct_971_, lean_object* v___y_972_, uint8_t v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v___y_977_; lean_object* v___y_978_; 
if (v___y_973_ == 0)
{
v___y_977_ = v___y_972_;
v___y_978_ = v___y_975_;
goto v___jp_976_;
}
else
{
lean_object* v___x_1000_; 
v___x_1000_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_struct_971_, v___y_973_, v___y_974_, v___y_975_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 1);
lean_inc(v_a_1001_);
lean_dec_ref_known(v___x_1000_, 2);
v___y_977_ = v___y_972_;
v___y_978_ = v_a_1001_;
goto v___jp_976_;
}
else
{
lean_object* v_a_1002_; lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
lean_dec_ref(v___y_972_);
lean_dec_ref(v_struct_971_);
lean_dec(v_idx_970_);
lean_dec(v_structName_969_);
v_a_1002_ = lean_ctor_get(v___x_1000_, 0);
v_a_1003_ = lean_ctor_get(v___x_1000_, 1);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_1000_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_inc(v_a_1002_);
lean_dec(v___x_1000_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1002_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
v___jp_976_:
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = l_Lean_Expr_proj___override(v_structName_969_, v_idx_970_, v_struct_971_);
v___x_980_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_979_, v___y_978_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; lean_object* v_a_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_990_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
v_a_982_ = lean_ctor_get(v___x_980_, 1);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_990_ == 0)
{
v___x_984_ = v___x_980_;
v_isShared_985_ = v_isSharedCheck_990_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_a_982_);
lean_inc(v_a_981_);
lean_dec(v___x_980_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_990_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_986_; lean_object* v___x_988_; 
v___x_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_986_, 0, v_a_981_);
lean_ctor_set(v___x_986_, 1, v___y_977_);
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 0, v___x_986_);
v___x_988_ = v___x_984_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v___x_986_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v_a_982_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
else
{
lean_object* v_a_991_; lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_999_; 
lean_dec_ref(v___y_977_);
v_a_991_ = lean_ctor_get(v___x_980_, 0);
v_a_992_ = lean_ctor_get(v___x_980_, 1);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_999_ == 0)
{
v___x_994_ = v___x_980_;
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_inc(v_a_991_);
lean_dec(v___x_980_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_997_; 
if (v_isShared_995_ == 0)
{
v___x_997_ = v___x_994_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_a_991_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v_a_992_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__6___boxed(lean_object* v_structName_1011_, lean_object* v_idx_1012_, lean_object* v_struct_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
uint8_t v___y_25297__boxed_1018_; lean_object* v_res_1019_; 
v___y_25297__boxed_1018_ = lean_unbox(v___y_1015_);
v_res_1019_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__6(v_structName_1011_, v_idx_1012_, v_struct_1013_, v___y_1014_, v___y_25297__boxed_1018_, v___y_1016_, v___y_1017_);
lean_dec_ref(v___y_1016_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__1(lean_object* v_f_1020_, lean_object* v_a_1021_, lean_object* v___y_1022_, uint8_t v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v___y_1027_; lean_object* v___y_1028_; 
if (v___y_1023_ == 0)
{
v___y_1027_ = v___y_1022_;
v___y_1028_ = v___y_1025_;
goto v___jp_1026_;
}
else
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_1020_, v___y_1023_, v___y_1024_, v___y_1025_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_a_1051_; lean_object* v___x_1052_; 
v_a_1051_ = lean_ctor_get(v___x_1050_, 1);
lean_inc(v_a_1051_);
lean_dec_ref_known(v___x_1050_, 2);
v___x_1052_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_1021_, v___y_1023_, v___y_1024_, v_a_1051_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 1);
lean_inc(v_a_1053_);
lean_dec_ref_known(v___x_1052_, 2);
v___y_1027_ = v___y_1022_;
v___y_1028_ = v_a_1053_;
goto v___jp_1026_;
}
else
{
lean_object* v_a_1054_; lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
lean_dec_ref(v___y_1022_);
lean_dec_ref(v_a_1021_);
lean_dec_ref(v_f_1020_);
v_a_1054_ = lean_ctor_get(v___x_1052_, 0);
v_a_1055_ = lean_ctor_get(v___x_1052_, 1);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v___x_1052_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_inc(v_a_1054_);
lean_dec(v___x_1052_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1054_);
lean_ctor_set(v_reuseFailAlloc_1061_, 1, v_a_1055_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
else
{
lean_object* v_a_1063_; lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
lean_dec_ref(v___y_1022_);
lean_dec_ref(v_a_1021_);
lean_dec_ref(v_f_1020_);
v_a_1063_ = lean_ctor_get(v___x_1050_, 0);
v_a_1064_ = lean_ctor_get(v___x_1050_, 1);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_1050_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_inc(v_a_1063_);
lean_dec(v___x_1050_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1063_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v_a_1064_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
v___jp_1026_:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = l_Lean_Expr_app___override(v_f_1020_, v_a_1021_);
v___x_1030_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1029_, v___y_1028_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v_a_1031_; lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1040_; 
v_a_1031_ = lean_ctor_get(v___x_1030_, 0);
v_a_1032_ = lean_ctor_get(v___x_1030_, 1);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1034_ = v___x_1030_;
v_isShared_1035_ = v_isSharedCheck_1040_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_inc(v_a_1031_);
lean_dec(v___x_1030_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1040_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1036_; lean_object* v___x_1038_; 
v___x_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1036_, 0, v_a_1031_);
lean_ctor_set(v___x_1036_, 1, v___y_1027_);
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 0, v___x_1036_);
v___x_1038_ = v___x_1034_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1036_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_a_1032_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
else
{
lean_object* v_a_1041_; lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
lean_dec_ref(v___y_1027_);
v_a_1041_ = lean_ctor_get(v___x_1030_, 0);
v_a_1042_ = lean_ctor_get(v___x_1030_, 1);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_1030_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_inc(v_a_1041_);
lean_dec(v___x_1030_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1041_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v_a_1042_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__1___boxed(lean_object* v_f_1072_, lean_object* v_a_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
uint8_t v___y_25380__boxed_1078_; lean_object* v_res_1079_; 
v___y_25380__boxed_1078_ = lean_unbox(v___y_1075_);
v_res_1079_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__1(v_f_1072_, v_a_1073_, v___y_1074_, v___y_25380__boxed_1078_, v___y_1076_, v___y_1077_);
lean_dec_ref(v___y_1076_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4(lean_object* v_x_1080_, lean_object* v_t_1081_, lean_object* v_v_1082_, lean_object* v_b_1083_, uint8_t v_nondep_1084_, lean_object* v___y_1085_, uint8_t v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v___y_1090_; lean_object* v___y_1091_; 
if (v___y_1086_ == 0)
{
v___y_1090_ = v___y_1085_;
v___y_1091_ = v___y_1088_;
goto v___jp_1089_;
}
else
{
lean_object* v___x_1113_; 
v___x_1113_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_1081_, v___y_1086_, v___y_1087_, v___y_1088_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_object* v_a_1114_; lean_object* v___x_1115_; 
v_a_1114_ = lean_ctor_get(v___x_1113_, 1);
lean_inc(v_a_1114_);
lean_dec_ref_known(v___x_1113_, 2);
v___x_1115_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_v_1082_, v___y_1086_, v___y_1087_, v_a_1114_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; lean_object* v___x_1117_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 1);
lean_inc(v_a_1116_);
lean_dec_ref_known(v___x_1115_, 2);
v___x_1117_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_1083_, v___y_1086_, v___y_1087_, v_a_1116_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 1);
lean_inc(v_a_1118_);
lean_dec_ref_known(v___x_1117_, 2);
v___y_1090_ = v___y_1085_;
v___y_1091_ = v_a_1118_;
goto v___jp_1089_;
}
else
{
lean_object* v_a_1119_; lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
lean_dec_ref(v___y_1085_);
lean_dec_ref(v_b_1083_);
lean_dec_ref(v_v_1082_);
lean_dec_ref(v_t_1081_);
lean_dec(v_x_1080_);
v_a_1119_ = lean_ctor_get(v___x_1117_, 0);
v_a_1120_ = lean_ctor_get(v___x_1117_, 1);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1117_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_inc(v_a_1119_);
lean_dec(v___x_1117_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1119_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
else
{
lean_object* v_a_1128_; lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1136_; 
lean_dec_ref(v___y_1085_);
lean_dec_ref(v_b_1083_);
lean_dec_ref(v_v_1082_);
lean_dec_ref(v_t_1081_);
lean_dec(v_x_1080_);
v_a_1128_ = lean_ctor_get(v___x_1115_, 0);
v_a_1129_ = lean_ctor_get(v___x_1115_, 1);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1131_ = v___x_1115_;
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_inc(v_a_1128_);
lean_dec(v___x_1115_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1134_; 
if (v_isShared_1132_ == 0)
{
v___x_1134_ = v___x_1131_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_a_1128_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_a_1129_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
else
{
lean_object* v_a_1137_; lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1145_; 
lean_dec_ref(v___y_1085_);
lean_dec_ref(v_b_1083_);
lean_dec_ref(v_v_1082_);
lean_dec_ref(v_t_1081_);
lean_dec(v_x_1080_);
v_a_1137_ = lean_ctor_get(v___x_1113_, 0);
v_a_1138_ = lean_ctor_get(v___x_1113_, 1);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1140_ = v___x_1113_;
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_inc(v_a_1137_);
lean_dec(v___x_1113_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1143_; 
if (v_isShared_1141_ == 0)
{
v___x_1143_ = v___x_1140_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_a_1137_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v_a_1138_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
}
v___jp_1089_:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = l_Lean_Expr_letE___override(v_x_1080_, v_t_1081_, v_v_1082_, v_b_1083_, v_nondep_1084_);
v___x_1093_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1092_, v___y_1091_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v_a_1094_; lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1103_; 
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
v_a_1095_ = lean_ctor_get(v___x_1093_, 1);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1097_ = v___x_1093_;
v_isShared_1098_ = v_isSharedCheck_1103_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_inc(v_a_1094_);
lean_dec(v___x_1093_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1103_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1099_; lean_object* v___x_1101_; 
v___x_1099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1099_, 0, v_a_1094_);
lean_ctor_set(v___x_1099_, 1, v___y_1090_);
if (v_isShared_1098_ == 0)
{
lean_ctor_set(v___x_1097_, 0, v___x_1099_);
v___x_1101_ = v___x_1097_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1099_);
lean_ctor_set(v_reuseFailAlloc_1102_, 1, v_a_1095_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
else
{
lean_object* v_a_1104_; lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1112_; 
lean_dec_ref(v___y_1090_);
v_a_1104_ = lean_ctor_get(v___x_1093_, 0);
v_a_1105_ = lean_ctor_get(v___x_1093_, 1);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1107_ = v___x_1093_;
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_inc(v_a_1104_);
lean_dec(v___x_1093_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1110_; 
if (v_isShared_1108_ == 0)
{
v___x_1110_ = v___x_1107_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_a_1104_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v_a_1105_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4___boxed(lean_object* v_x_1146_, lean_object* v_t_1147_, lean_object* v_v_1148_, lean_object* v_b_1149_, lean_object* v_nondep_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
uint8_t v_nondep_boxed_1155_; uint8_t v___y_25486__boxed_1156_; lean_object* v_res_1157_; 
v_nondep_boxed_1155_ = lean_unbox(v_nondep_1150_);
v___y_25486__boxed_1156_ = lean_unbox(v___y_1152_);
v_res_1157_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4(v_x_1146_, v_t_1147_, v_v_1148_, v_b_1149_, v_nondep_boxed_1155_, v___y_1151_, v___y_25486__boxed_1156_, v___y_1153_, v___y_1154_);
lean_dec_ref(v___y_1153_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7(lean_object* v_msg_1165_, lean_object* v___y_1166_, uint8_t v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v___f_1170_; lean_object* v___f_1171_; lean_object* v___f_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___f_1182_; lean_object* v___f_1183_; lean_object* v___f_1184_; lean_object* v___f_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_24781__overap_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___f_1170_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__0));
v___f_1171_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__1));
v___f_1172_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__2));
v___x_1173_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__3));
v___x_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1173_);
lean_ctor_set(v___x_1174_, 1, v___f_1170_);
v___x_1175_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__4));
v___x_1176_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__5));
v___x_1177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1174_);
lean_ctor_set(v___x_1177_, 1, v___x_1175_);
lean_ctor_set(v___x_1177_, 2, v___f_1171_);
lean_ctor_set(v___x_1177_, 3, v___f_1172_);
lean_ctor_set(v___x_1177_, 4, v___x_1176_);
v___x_1178_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__6));
v___x_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1177_);
lean_ctor_set(v___x_1179_, 1, v___x_1178_);
v___x_1180_ = l_ReaderT_instMonad___redArg(v___x_1179_);
v___x_1181_ = l_ReaderT_instMonad___redArg(v___x_1180_);
lean_inc_ref_n(v___x_1181_, 6);
v___f_1182_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1182_, 0, v___x_1181_);
v___f_1183_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1183_, 0, v___x_1181_);
v___f_1184_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_1184_, 0, v___x_1181_);
v___f_1185_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_1185_, 0, v___x_1181_);
v___x_1186_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_1186_, 0, lean_box(0));
lean_closure_set(v___x_1186_, 1, lean_box(0));
lean_closure_set(v___x_1186_, 2, v___x_1181_);
v___x_1187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
lean_ctor_set(v___x_1187_, 1, v___f_1182_);
v___x_1188_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_1188_, 0, lean_box(0));
lean_closure_set(v___x_1188_, 1, lean_box(0));
lean_closure_set(v___x_1188_, 2, v___x_1181_);
v___x_1189_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1187_);
lean_ctor_set(v___x_1189_, 1, v___x_1188_);
lean_ctor_set(v___x_1189_, 2, v___f_1183_);
lean_ctor_set(v___x_1189_, 3, v___f_1184_);
lean_ctor_set(v___x_1189_, 4, v___f_1185_);
v___x_1190_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_1190_, 0, lean_box(0));
lean_closure_set(v___x_1190_, 1, lean_box(0));
lean_closure_set(v___x_1190_, 2, v___x_1181_);
v___x_1191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1189_);
lean_ctor_set(v___x_1191_, 1, v___x_1190_);
v___x_1192_ = l_Lean_instInhabitedExpr;
v___x_1193_ = l_instInhabitedOfMonad___redArg(v___x_1191_, v___x_1192_);
v___x_24781__overap_1194_ = lean_panic_fn_borrowed(v___x_1193_, v_msg_1165_);
lean_dec(v___x_1193_);
v___x_1195_ = lean_box(v___y_1167_);
lean_inc_ref(v___y_1168_);
v___x_1196_ = lean_apply_4(v___x_24781__overap_1194_, v___y_1166_, v___x_1195_, v___y_1168_, v___y_1169_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___boxed(lean_object* v_msg_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
uint8_t v___y_25629__boxed_1202_; lean_object* v_res_1203_; 
v___y_25629__boxed_1202_ = lean_unbox(v___y_1199_);
v_res_1203_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7(v_msg_1197_, v___y_1198_, v___y_25629__boxed_1202_, v___y_1200_, v___y_1201_);
lean_dec_ref(v___y_1200_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__5(lean_object* v_d_1204_, lean_object* v_e_1205_, lean_object* v___y_1206_, uint8_t v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v___y_1211_; lean_object* v___y_1212_; 
if (v___y_1207_ == 0)
{
v___y_1211_ = v___y_1206_;
v___y_1212_ = v___y_1209_;
goto v___jp_1210_;
}
else
{
lean_object* v___x_1234_; 
v___x_1234_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_1205_, v___y_1207_, v___y_1208_, v___y_1209_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v_a_1235_; 
v_a_1235_ = lean_ctor_get(v___x_1234_, 1);
lean_inc(v_a_1235_);
lean_dec_ref_known(v___x_1234_, 2);
v___y_1211_ = v___y_1206_;
v___y_1212_ = v_a_1235_;
goto v___jp_1210_;
}
else
{
lean_object* v_a_1236_; lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1244_; 
lean_dec_ref(v___y_1206_);
lean_dec_ref(v_e_1205_);
lean_dec(v_d_1204_);
v_a_1236_ = lean_ctor_get(v___x_1234_, 0);
v_a_1237_ = lean_ctor_get(v___x_1234_, 1);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1239_ = v___x_1234_;
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_inc(v_a_1236_);
lean_dec(v___x_1234_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1242_; 
if (v_isShared_1240_ == 0)
{
v___x_1242_ = v___x_1239_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_a_1236_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v_a_1237_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
}
v___jp_1210_:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1213_ = l_Lean_Expr_mdata___override(v_d_1204_, v_e_1205_);
v___x_1214_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1213_, v___y_1212_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_a_1215_; lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1224_; 
v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
v_a_1216_ = lean_ctor_get(v___x_1214_, 1);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1218_ = v___x_1214_;
v_isShared_1219_ = v_isSharedCheck_1224_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_inc(v_a_1215_);
lean_dec(v___x_1214_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1224_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1220_; lean_object* v___x_1222_; 
v___x_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1220_, 0, v_a_1215_);
lean_ctor_set(v___x_1220_, 1, v___y_1211_);
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 0, v___x_1220_);
v___x_1222_ = v___x_1218_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1220_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v_a_1216_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
else
{
lean_object* v_a_1225_; lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
lean_dec_ref(v___y_1211_);
v_a_1225_ = lean_ctor_get(v___x_1214_, 0);
v_a_1226_ = lean_ctor_get(v___x_1214_, 1);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1228_ = v___x_1214_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_inc(v_a_1225_);
lean_dec(v___x_1214_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1225_);
lean_ctor_set(v_reuseFailAlloc_1232_, 1, v_a_1226_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__5___boxed(lean_object* v_d_1245_, lean_object* v_e_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
uint8_t v___y_25700__boxed_1251_; lean_object* v_res_1252_; 
v___y_25700__boxed_1251_ = lean_unbox(v___y_1248_);
v_res_1252_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__5(v_d_1245_, v_e_1246_, v___y_1247_, v___y_25700__boxed_1251_, v___y_1249_, v___y_1250_);
lean_dec_ref(v___y_1249_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__3(lean_object* v_x_1253_, uint8_t v_bi_1254_, lean_object* v_t_1255_, lean_object* v_b_1256_, lean_object* v___y_1257_, uint8_t v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v___y_1262_; lean_object* v___y_1263_; 
if (v___y_1258_ == 0)
{
v___y_1262_ = v___y_1257_;
v___y_1263_ = v___y_1260_;
goto v___jp_1261_;
}
else
{
lean_object* v___x_1285_; 
v___x_1285_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_1255_, v___y_1258_, v___y_1259_, v___y_1260_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v_a_1286_; lean_object* v___x_1287_; 
v_a_1286_ = lean_ctor_get(v___x_1285_, 1);
lean_inc(v_a_1286_);
lean_dec_ref_known(v___x_1285_, 2);
v___x_1287_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_1256_, v___y_1258_, v___y_1259_, v_a_1286_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1288_; 
v_a_1288_ = lean_ctor_get(v___x_1287_, 1);
lean_inc(v_a_1288_);
lean_dec_ref_known(v___x_1287_, 2);
v___y_1262_ = v___y_1257_;
v___y_1263_ = v_a_1288_;
goto v___jp_1261_;
}
else
{
lean_object* v_a_1289_; lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
lean_dec_ref(v___y_1257_);
lean_dec_ref(v_b_1256_);
lean_dec_ref(v_t_1255_);
lean_dec(v_x_1253_);
v_a_1289_ = lean_ctor_get(v___x_1287_, 0);
v_a_1290_ = lean_ctor_get(v___x_1287_, 1);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1287_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_inc(v_a_1289_);
lean_dec(v___x_1287_);
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
lean_dec_ref(v___y_1257_);
lean_dec_ref(v_b_1256_);
lean_dec_ref(v_t_1255_);
lean_dec(v_x_1253_);
v_a_1298_ = lean_ctor_get(v___x_1285_, 0);
v_a_1299_ = lean_ctor_get(v___x_1285_, 1);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1301_ = v___x_1285_;
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_inc(v_a_1298_);
lean_dec(v___x_1285_);
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
v___jp_1261_:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1264_ = l_Lean_Expr_forallE___override(v_x_1253_, v_t_1255_, v_b_1256_, v_bi_1254_);
v___x_1265_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1264_, v___y_1263_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_a_1266_; lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1275_; 
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
v_a_1267_ = lean_ctor_get(v___x_1265_, 1);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1269_ = v___x_1265_;
v_isShared_1270_ = v_isSharedCheck_1275_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_inc(v_a_1266_);
lean_dec(v___x_1265_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1275_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1271_; lean_object* v___x_1273_; 
v___x_1271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1271_, 0, v_a_1266_);
lean_ctor_set(v___x_1271_, 1, v___y_1262_);
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 0, v___x_1271_);
v___x_1273_ = v___x_1269_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1271_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v_a_1267_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
else
{
lean_object* v_a_1276_; lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1284_; 
lean_dec_ref(v___y_1262_);
v_a_1276_ = lean_ctor_get(v___x_1265_, 0);
v_a_1277_ = lean_ctor_get(v___x_1265_, 1);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1279_ = v___x_1265_;
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_inc(v_a_1276_);
lean_dec(v___x_1265_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1282_; 
if (v_isShared_1280_ == 0)
{
v___x_1282_ = v___x_1279_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_a_1276_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v_a_1277_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__3___boxed(lean_object* v_x_1307_, lean_object* v_bi_1308_, lean_object* v_t_1309_, lean_object* v_b_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
uint8_t v_bi_boxed_1315_; uint8_t v___y_25783__boxed_1316_; lean_object* v_res_1317_; 
v_bi_boxed_1315_ = lean_unbox(v_bi_1308_);
v___y_25783__boxed_1316_ = lean_unbox(v___y_1312_);
v_res_1317_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__3(v_x_1307_, v_bi_boxed_1315_, v_t_1309_, v_b_1310_, v___y_1311_, v___y_25783__boxed_1316_, v___y_1313_, v___y_1314_);
lean_dec_ref(v___y_1313_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10___redArg(lean_object* v_a_1318_, lean_object* v_x_1319_){
_start:
{
if (lean_obj_tag(v_x_1319_) == 0)
{
lean_object* v___x_1320_; 
v___x_1320_ = lean_box(0);
return v___x_1320_;
}
else
{
lean_object* v_key_1321_; lean_object* v_value_1322_; lean_object* v_tail_1323_; uint8_t v___y_1325_; lean_object* v_fst_1328_; lean_object* v_snd_1329_; lean_object* v_fst_1330_; lean_object* v_snd_1331_; size_t v___x_1332_; size_t v___x_1333_; uint8_t v___x_1334_; 
v_key_1321_ = lean_ctor_get(v_x_1319_, 0);
v_value_1322_ = lean_ctor_get(v_x_1319_, 1);
v_tail_1323_ = lean_ctor_get(v_x_1319_, 2);
v_fst_1328_ = lean_ctor_get(v_key_1321_, 0);
v_snd_1329_ = lean_ctor_get(v_key_1321_, 1);
v_fst_1330_ = lean_ctor_get(v_a_1318_, 0);
v_snd_1331_ = lean_ctor_get(v_a_1318_, 1);
v___x_1332_ = lean_ptr_addr(v_fst_1328_);
v___x_1333_ = lean_ptr_addr(v_fst_1330_);
v___x_1334_ = lean_usize_dec_eq(v___x_1332_, v___x_1333_);
if (v___x_1334_ == 0)
{
v___y_1325_ = v___x_1334_;
goto v___jp_1324_;
}
else
{
uint8_t v___x_1335_; 
v___x_1335_ = lean_nat_dec_eq(v_snd_1329_, v_snd_1331_);
v___y_1325_ = v___x_1335_;
goto v___jp_1324_;
}
v___jp_1324_:
{
if (v___y_1325_ == 0)
{
v_x_1319_ = v_tail_1323_;
goto _start;
}
else
{
lean_object* v___x_1327_; 
lean_inc(v_value_1322_);
v___x_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1327_, 0, v_value_1322_);
return v___x_1327_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10___redArg___boxed(lean_object* v_a_1336_, lean_object* v_x_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10___redArg(v_a_1336_, v_x_1337_);
lean_dec(v_x_1337_);
lean_dec_ref(v_a_1336_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2___redArg(lean_object* v_m_1339_, lean_object* v_a_1340_){
_start:
{
lean_object* v_buckets_1341_; lean_object* v_fst_1342_; lean_object* v_snd_1343_; lean_object* v___x_1344_; size_t v___x_1345_; size_t v___x_1346_; size_t v___x_1347_; uint64_t v___x_1348_; uint64_t v___x_1349_; uint64_t v___x_1350_; uint64_t v___x_1351_; uint64_t v___x_1352_; uint64_t v_fold_1353_; uint64_t v___x_1354_; uint64_t v___x_1355_; uint64_t v___x_1356_; size_t v___x_1357_; size_t v___x_1358_; size_t v___x_1359_; size_t v___x_1360_; size_t v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v_buckets_1341_ = lean_ctor_get(v_m_1339_, 1);
v_fst_1342_ = lean_ctor_get(v_a_1340_, 0);
v_snd_1343_ = lean_ctor_get(v_a_1340_, 1);
v___x_1344_ = lean_array_get_size(v_buckets_1341_);
v___x_1345_ = lean_ptr_addr(v_fst_1342_);
v___x_1346_ = ((size_t)3ULL);
v___x_1347_ = lean_usize_shift_right(v___x_1345_, v___x_1346_);
v___x_1348_ = lean_usize_to_uint64(v___x_1347_);
v___x_1349_ = lean_uint64_of_nat(v_snd_1343_);
v___x_1350_ = lean_uint64_mix_hash(v___x_1348_, v___x_1349_);
v___x_1351_ = 32ULL;
v___x_1352_ = lean_uint64_shift_right(v___x_1350_, v___x_1351_);
v_fold_1353_ = lean_uint64_xor(v___x_1350_, v___x_1352_);
v___x_1354_ = 16ULL;
v___x_1355_ = lean_uint64_shift_right(v_fold_1353_, v___x_1354_);
v___x_1356_ = lean_uint64_xor(v_fold_1353_, v___x_1355_);
v___x_1357_ = lean_uint64_to_usize(v___x_1356_);
v___x_1358_ = lean_usize_of_nat(v___x_1344_);
v___x_1359_ = ((size_t)1ULL);
v___x_1360_ = lean_usize_sub(v___x_1358_, v___x_1359_);
v___x_1361_ = lean_usize_land(v___x_1357_, v___x_1360_);
v___x_1362_ = lean_array_uget_borrowed(v_buckets_1341_, v___x_1361_);
v___x_1363_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10___redArg(v_a_1340_, v___x_1362_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_m_1364_, lean_object* v_a_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2___redArg(v_m_1364_, v_a_1365_);
lean_dec_ref(v_a_1365_);
lean_dec_ref(v_m_1364_);
return v_res_1366_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1370_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__2));
v___x_1371_ = lean_unsigned_to_nat(67u);
v___x_1372_ = lean_unsigned_to_nat(35u);
v___x_1373_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__1));
v___x_1374_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__0));
v___x_1375_ = l_mkPanicMessageWithDecl(v___x_1374_, v___x_1373_, v___x_1372_, v___x_1371_, v___x_1370_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0(lean_object* v_n_1376_, lean_object* v_xs_1377_, lean_object* v_e_1378_, lean_object* v_offset_1379_, lean_object* v_a_1380_, uint8_t v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_){
_start:
{
switch(lean_obj_tag(v_e_1378_))
{
case 5:
{
lean_object* v_fn_1384_; lean_object* v_arg_1385_; lean_object* v___x_1386_; 
v_fn_1384_ = lean_ctor_get(v_e_1378_, 0);
v_arg_1385_ = lean_ctor_get(v_e_1378_, 1);
lean_inc(v_offset_1379_);
lean_inc_ref(v_fn_1384_);
v___x_1386_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1376_, v_xs_1377_, v_fn_1384_, v_offset_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; lean_object* v_a_1388_; lean_object* v_fst_1389_; lean_object* v_snd_1390_; lean_object* v___x_1391_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_a_1387_);
v_a_1388_ = lean_ctor_get(v___x_1386_, 1);
lean_inc(v_a_1388_);
lean_dec_ref_known(v___x_1386_, 2);
v_fst_1389_ = lean_ctor_get(v_a_1387_, 0);
lean_inc(v_fst_1389_);
v_snd_1390_ = lean_ctor_get(v_a_1387_, 1);
lean_inc(v_snd_1390_);
lean_dec(v_a_1387_);
lean_inc_ref(v_arg_1385_);
v___x_1391_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1376_, v_xs_1377_, v_arg_1385_, v_offset_1379_, v_snd_1390_, v_a_1381_, v_a_1382_, v_a_1388_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1418_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
v_a_1393_ = lean_ctor_get(v___x_1391_, 1);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1395_ = v___x_1391_;
v_isShared_1396_ = v_isSharedCheck_1418_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_inc(v_a_1392_);
lean_dec(v___x_1391_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1418_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v_fst_1397_; lean_object* v_snd_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1417_; 
v_fst_1397_ = lean_ctor_get(v_a_1392_, 0);
v_snd_1398_ = lean_ctor_get(v_a_1392_, 1);
v_isSharedCheck_1417_ = !lean_is_exclusive(v_a_1392_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1400_ = v_a_1392_;
v_isShared_1401_ = v_isSharedCheck_1417_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_snd_1398_);
lean_inc(v_fst_1397_);
lean_dec(v_a_1392_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1417_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
uint8_t v___y_1403_; size_t v___x_1411_; size_t v___x_1412_; uint8_t v___x_1413_; 
v___x_1411_ = lean_ptr_addr(v_fn_1384_);
v___x_1412_ = lean_ptr_addr(v_fst_1389_);
v___x_1413_ = lean_usize_dec_eq(v___x_1411_, v___x_1412_);
if (v___x_1413_ == 0)
{
v___y_1403_ = v___x_1413_;
goto v___jp_1402_;
}
else
{
size_t v___x_1414_; size_t v___x_1415_; uint8_t v___x_1416_; 
v___x_1414_ = lean_ptr_addr(v_arg_1385_);
v___x_1415_ = lean_ptr_addr(v_fst_1397_);
v___x_1416_ = lean_usize_dec_eq(v___x_1414_, v___x_1415_);
v___y_1403_ = v___x_1416_;
goto v___jp_1402_;
}
v___jp_1402_:
{
if (v___y_1403_ == 0)
{
lean_object* v___x_1404_; 
lean_del_object(v___x_1400_);
lean_del_object(v___x_1395_);
lean_dec_ref_known(v_e_1378_, 2);
v___x_1404_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__1(v_fst_1389_, v_fst_1397_, v_snd_1398_, v_a_1381_, v_a_1382_, v_a_1393_);
return v___x_1404_;
}
else
{
lean_object* v___x_1406_; 
lean_dec(v_fst_1397_);
lean_dec(v_fst_1389_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 0, v_e_1378_);
v___x_1406_ = v___x_1400_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_e_1378_);
lean_ctor_set(v_reuseFailAlloc_1410_, 1, v_snd_1398_);
v___x_1406_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
lean_object* v___x_1408_; 
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 0, v___x_1406_);
v___x_1408_ = v___x_1395_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1406_);
lean_ctor_set(v_reuseFailAlloc_1409_, 1, v_a_1393_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1389_);
lean_dec_ref_known(v_e_1378_, 2);
return v___x_1391_;
}
}
else
{
lean_dec_ref_known(v_e_1378_, 2);
lean_dec(v_offset_1379_);
return v___x_1386_;
}
}
case 6:
{
lean_object* v_binderName_1419_; lean_object* v_binderType_1420_; lean_object* v_body_1421_; uint8_t v_binderInfo_1422_; lean_object* v___x_1423_; 
v_binderName_1419_ = lean_ctor_get(v_e_1378_, 0);
v_binderType_1420_ = lean_ctor_get(v_e_1378_, 1);
v_body_1421_ = lean_ctor_get(v_e_1378_, 2);
v_binderInfo_1422_ = lean_ctor_get_uint8(v_e_1378_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1379_);
lean_inc_ref(v_binderType_1420_);
v___x_1423_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1376_, v_xs_1377_, v_binderType_1420_, v_offset_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_a_1424_; lean_object* v_a_1425_; lean_object* v_fst_1426_; lean_object* v_snd_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
lean_inc(v_a_1424_);
v_a_1425_ = lean_ctor_get(v___x_1423_, 1);
lean_inc(v_a_1425_);
lean_dec_ref_known(v___x_1423_, 2);
v_fst_1426_ = lean_ctor_get(v_a_1424_, 0);
lean_inc(v_fst_1426_);
v_snd_1427_ = lean_ctor_get(v_a_1424_, 1);
lean_inc(v_snd_1427_);
lean_dec(v_a_1424_);
v___x_1428_ = lean_unsigned_to_nat(1u);
v___x_1429_ = lean_nat_add(v_offset_1379_, v___x_1428_);
lean_dec(v_offset_1379_);
lean_inc_ref(v_body_1421_);
v___x_1430_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1376_, v_xs_1377_, v_body_1421_, v___x_1429_, v_snd_1427_, v_a_1381_, v_a_1382_, v_a_1425_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1457_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
v_a_1432_ = lean_ctor_get(v___x_1430_, 1);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1434_ = v___x_1430_;
v_isShared_1435_ = v_isSharedCheck_1457_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_inc(v_a_1431_);
lean_dec(v___x_1430_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1457_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v_fst_1436_; lean_object* v_snd_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1456_; 
v_fst_1436_ = lean_ctor_get(v_a_1431_, 0);
v_snd_1437_ = lean_ctor_get(v_a_1431_, 1);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_a_1431_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1439_ = v_a_1431_;
v_isShared_1440_ = v_isSharedCheck_1456_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_snd_1437_);
lean_inc(v_fst_1436_);
lean_dec(v_a_1431_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1456_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
uint8_t v___y_1442_; size_t v___x_1450_; size_t v___x_1451_; uint8_t v___x_1452_; 
v___x_1450_ = lean_ptr_addr(v_binderType_1420_);
v___x_1451_ = lean_ptr_addr(v_fst_1426_);
v___x_1452_ = lean_usize_dec_eq(v___x_1450_, v___x_1451_);
if (v___x_1452_ == 0)
{
v___y_1442_ = v___x_1452_;
goto v___jp_1441_;
}
else
{
size_t v___x_1453_; size_t v___x_1454_; uint8_t v___x_1455_; 
v___x_1453_ = lean_ptr_addr(v_body_1421_);
v___x_1454_ = lean_ptr_addr(v_fst_1436_);
v___x_1455_ = lean_usize_dec_eq(v___x_1453_, v___x_1454_);
v___y_1442_ = v___x_1455_;
goto v___jp_1441_;
}
v___jp_1441_:
{
if (v___y_1442_ == 0)
{
lean_object* v___x_1443_; 
lean_inc(v_binderName_1419_);
lean_del_object(v___x_1439_);
lean_del_object(v___x_1434_);
lean_dec_ref_known(v_e_1378_, 3);
v___x_1443_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__2(v_binderName_1419_, v_binderInfo_1422_, v_fst_1426_, v_fst_1436_, v_snd_1437_, v_a_1381_, v_a_1382_, v_a_1432_);
return v___x_1443_;
}
else
{
lean_object* v___x_1445_; 
lean_dec(v_fst_1436_);
lean_dec(v_fst_1426_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 0, v_e_1378_);
v___x_1445_ = v___x_1439_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_e_1378_);
lean_ctor_set(v_reuseFailAlloc_1449_, 1, v_snd_1437_);
v___x_1445_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
lean_object* v___x_1447_; 
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 0, v___x_1445_);
v___x_1447_ = v___x_1434_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1445_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v_a_1432_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1426_);
lean_dec_ref_known(v_e_1378_, 3);
return v___x_1430_;
}
}
else
{
lean_dec_ref_known(v_e_1378_, 3);
lean_dec(v_offset_1379_);
return v___x_1423_;
}
}
case 7:
{
lean_object* v_binderName_1458_; lean_object* v_binderType_1459_; lean_object* v_body_1460_; uint8_t v_binderInfo_1461_; lean_object* v___x_1462_; 
v_binderName_1458_ = lean_ctor_get(v_e_1378_, 0);
v_binderType_1459_ = lean_ctor_get(v_e_1378_, 1);
v_body_1460_ = lean_ctor_get(v_e_1378_, 2);
v_binderInfo_1461_ = lean_ctor_get_uint8(v_e_1378_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1379_);
lean_inc_ref(v_binderType_1459_);
v___x_1462_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1376_, v_xs_1377_, v_binderType_1459_, v_offset_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; lean_object* v_a_1464_; lean_object* v_fst_1465_; lean_object* v_snd_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
lean_inc(v_a_1463_);
v_a_1464_ = lean_ctor_get(v___x_1462_, 1);
lean_inc(v_a_1464_);
lean_dec_ref_known(v___x_1462_, 2);
v_fst_1465_ = lean_ctor_get(v_a_1463_, 0);
lean_inc(v_fst_1465_);
v_snd_1466_ = lean_ctor_get(v_a_1463_, 1);
lean_inc(v_snd_1466_);
lean_dec(v_a_1463_);
v___x_1467_ = lean_unsigned_to_nat(1u);
v___x_1468_ = lean_nat_add(v_offset_1379_, v___x_1467_);
lean_dec(v_offset_1379_);
lean_inc_ref(v_body_1460_);
v___x_1469_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1376_, v_xs_1377_, v_body_1460_, v___x_1468_, v_snd_1466_, v_a_1381_, v_a_1382_, v_a_1464_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v_a_1470_; lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1496_; 
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
v_a_1471_ = lean_ctor_get(v___x_1469_, 1);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1473_ = v___x_1469_;
v_isShared_1474_ = v_isSharedCheck_1496_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_inc(v_a_1470_);
lean_dec(v___x_1469_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1496_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v_fst_1475_; lean_object* v_snd_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1495_; 
v_fst_1475_ = lean_ctor_get(v_a_1470_, 0);
v_snd_1476_ = lean_ctor_get(v_a_1470_, 1);
v_isSharedCheck_1495_ = !lean_is_exclusive(v_a_1470_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1478_ = v_a_1470_;
v_isShared_1479_ = v_isSharedCheck_1495_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_snd_1476_);
lean_inc(v_fst_1475_);
lean_dec(v_a_1470_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1495_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
uint8_t v___y_1481_; size_t v___x_1489_; size_t v___x_1490_; uint8_t v___x_1491_; 
v___x_1489_ = lean_ptr_addr(v_binderType_1459_);
v___x_1490_ = lean_ptr_addr(v_fst_1465_);
v___x_1491_ = lean_usize_dec_eq(v___x_1489_, v___x_1490_);
if (v___x_1491_ == 0)
{
v___y_1481_ = v___x_1491_;
goto v___jp_1480_;
}
else
{
size_t v___x_1492_; size_t v___x_1493_; uint8_t v___x_1494_; 
v___x_1492_ = lean_ptr_addr(v_body_1460_);
v___x_1493_ = lean_ptr_addr(v_fst_1475_);
v___x_1494_ = lean_usize_dec_eq(v___x_1492_, v___x_1493_);
v___y_1481_ = v___x_1494_;
goto v___jp_1480_;
}
v___jp_1480_:
{
if (v___y_1481_ == 0)
{
lean_object* v___x_1482_; 
lean_inc(v_binderName_1458_);
lean_del_object(v___x_1478_);
lean_del_object(v___x_1473_);
lean_dec_ref_known(v_e_1378_, 3);
v___x_1482_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__3(v_binderName_1458_, v_binderInfo_1461_, v_fst_1465_, v_fst_1475_, v_snd_1476_, v_a_1381_, v_a_1382_, v_a_1471_);
return v___x_1482_;
}
else
{
lean_object* v___x_1484_; 
lean_dec(v_fst_1475_);
lean_dec(v_fst_1465_);
if (v_isShared_1479_ == 0)
{
lean_ctor_set(v___x_1478_, 0, v_e_1378_);
v___x_1484_ = v___x_1478_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_e_1378_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v_snd_1476_);
v___x_1484_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
lean_object* v___x_1486_; 
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 0, v___x_1484_);
v___x_1486_ = v___x_1473_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1484_);
lean_ctor_set(v_reuseFailAlloc_1487_, 1, v_a_1471_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1465_);
lean_dec_ref_known(v_e_1378_, 3);
return v___x_1469_;
}
}
else
{
lean_dec_ref_known(v_e_1378_, 3);
lean_dec(v_offset_1379_);
return v___x_1462_;
}
}
case 8:
{
lean_object* v_declName_1497_; lean_object* v_type_1498_; lean_object* v_value_1499_; lean_object* v_body_1500_; uint8_t v_nondep_1501_; lean_object* v___x_1502_; 
v_declName_1497_ = lean_ctor_get(v_e_1378_, 0);
v_type_1498_ = lean_ctor_get(v_e_1378_, 1);
v_value_1499_ = lean_ctor_get(v_e_1378_, 2);
v_body_1500_ = lean_ctor_get(v_e_1378_, 3);
v_nondep_1501_ = lean_ctor_get_uint8(v_e_1378_, sizeof(void*)*4 + 8);
lean_inc(v_offset_1379_);
lean_inc_ref(v_type_1498_);
v___x_1502_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1376_, v_xs_1377_, v_type_1498_, v_offset_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v_a_1503_; lean_object* v_a_1504_; lean_object* v_fst_1505_; lean_object* v_snd_1506_; lean_object* v___x_1507_; 
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_a_1503_);
v_a_1504_ = lean_ctor_get(v___x_1502_, 1);
lean_inc(v_a_1504_);
lean_dec_ref_known(v___x_1502_, 2);
v_fst_1505_ = lean_ctor_get(v_a_1503_, 0);
lean_inc(v_fst_1505_);
v_snd_1506_ = lean_ctor_get(v_a_1503_, 1);
lean_inc(v_snd_1506_);
lean_dec(v_a_1503_);
lean_inc(v_offset_1379_);
lean_inc_ref(v_value_1499_);
v___x_1507_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1376_, v_xs_1377_, v_value_1499_, v_offset_1379_, v_snd_1506_, v_a_1381_, v_a_1382_, v_a_1504_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v_a_1508_; lean_object* v_a_1509_; lean_object* v_fst_1510_; lean_object* v_snd_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v_a_1508_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_a_1508_);
v_a_1509_ = lean_ctor_get(v___x_1507_, 1);
lean_inc(v_a_1509_);
lean_dec_ref_known(v___x_1507_, 2);
v_fst_1510_ = lean_ctor_get(v_a_1508_, 0);
lean_inc(v_fst_1510_);
v_snd_1511_ = lean_ctor_get(v_a_1508_, 1);
lean_inc(v_snd_1511_);
lean_dec(v_a_1508_);
v___x_1512_ = lean_unsigned_to_nat(1u);
v___x_1513_ = lean_nat_add(v_offset_1379_, v___x_1512_);
lean_dec(v_offset_1379_);
lean_inc_ref(v_body_1500_);
v___x_1514_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1376_, v_xs_1377_, v_body_1500_, v___x_1513_, v_snd_1511_, v_a_1381_, v_a_1382_, v_a_1509_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1545_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
v_a_1516_ = lean_ctor_get(v___x_1514_, 1);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1518_ = v___x_1514_;
v_isShared_1519_ = v_isSharedCheck_1545_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_inc(v_a_1515_);
lean_dec(v___x_1514_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1545_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v_fst_1520_; lean_object* v_snd_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1544_; 
v_fst_1520_ = lean_ctor_get(v_a_1515_, 0);
v_snd_1521_ = lean_ctor_get(v_a_1515_, 1);
v_isSharedCheck_1544_ = !lean_is_exclusive(v_a_1515_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1523_ = v_a_1515_;
v_isShared_1524_ = v_isSharedCheck_1544_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_snd_1521_);
lean_inc(v_fst_1520_);
lean_dec(v_a_1515_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1544_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
uint8_t v___y_1526_; size_t v___x_1538_; size_t v___x_1539_; uint8_t v___x_1540_; 
v___x_1538_ = lean_ptr_addr(v_type_1498_);
v___x_1539_ = lean_ptr_addr(v_fst_1505_);
v___x_1540_ = lean_usize_dec_eq(v___x_1538_, v___x_1539_);
if (v___x_1540_ == 0)
{
v___y_1526_ = v___x_1540_;
goto v___jp_1525_;
}
else
{
size_t v___x_1541_; size_t v___x_1542_; uint8_t v___x_1543_; 
v___x_1541_ = lean_ptr_addr(v_value_1499_);
v___x_1542_ = lean_ptr_addr(v_fst_1510_);
v___x_1543_ = lean_usize_dec_eq(v___x_1541_, v___x_1542_);
v___y_1526_ = v___x_1543_;
goto v___jp_1525_;
}
v___jp_1525_:
{
if (v___y_1526_ == 0)
{
lean_object* v___x_1527_; 
lean_inc(v_declName_1497_);
lean_del_object(v___x_1523_);
lean_del_object(v___x_1518_);
lean_dec_ref_known(v_e_1378_, 4);
v___x_1527_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4(v_declName_1497_, v_fst_1505_, v_fst_1510_, v_fst_1520_, v_nondep_1501_, v_snd_1521_, v_a_1381_, v_a_1382_, v_a_1516_);
return v___x_1527_;
}
else
{
size_t v___x_1528_; size_t v___x_1529_; uint8_t v___x_1530_; 
v___x_1528_ = lean_ptr_addr(v_body_1500_);
v___x_1529_ = lean_ptr_addr(v_fst_1520_);
v___x_1530_ = lean_usize_dec_eq(v___x_1528_, v___x_1529_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1531_; 
lean_inc(v_declName_1497_);
lean_del_object(v___x_1523_);
lean_del_object(v___x_1518_);
lean_dec_ref_known(v_e_1378_, 4);
v___x_1531_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4(v_declName_1497_, v_fst_1505_, v_fst_1510_, v_fst_1520_, v_nondep_1501_, v_snd_1521_, v_a_1381_, v_a_1382_, v_a_1516_);
return v___x_1531_;
}
else
{
lean_object* v___x_1533_; 
lean_dec(v_fst_1520_);
lean_dec(v_fst_1510_);
lean_dec(v_fst_1505_);
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 0, v_e_1378_);
v___x_1533_ = v___x_1523_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_e_1378_);
lean_ctor_set(v_reuseFailAlloc_1537_, 1, v_snd_1521_);
v___x_1533_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
lean_object* v___x_1535_; 
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 0, v___x_1533_);
v___x_1535_ = v___x_1518_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1533_);
lean_ctor_set(v_reuseFailAlloc_1536_, 1, v_a_1516_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
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
lean_dec(v_fst_1510_);
lean_dec(v_fst_1505_);
lean_dec_ref_known(v_e_1378_, 4);
return v___x_1514_;
}
}
else
{
lean_dec(v_fst_1505_);
lean_dec_ref_known(v_e_1378_, 4);
lean_dec(v_offset_1379_);
return v___x_1507_;
}
}
else
{
lean_dec_ref_known(v_e_1378_, 4);
lean_dec(v_offset_1379_);
return v___x_1502_;
}
}
case 10:
{
lean_object* v_data_1546_; lean_object* v_expr_1547_; lean_object* v___x_1548_; 
v_data_1546_ = lean_ctor_get(v_e_1378_, 0);
v_expr_1547_ = lean_ctor_get(v_e_1378_, 1);
lean_inc_ref(v_expr_1547_);
v___x_1548_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1376_, v_xs_1377_, v_expr_1547_, v_offset_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1570_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
v_a_1550_ = lean_ctor_get(v___x_1548_, 1);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1552_ = v___x_1548_;
v_isShared_1553_ = v_isSharedCheck_1570_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_inc(v_a_1549_);
lean_dec(v___x_1548_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1570_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v_fst_1554_; lean_object* v_snd_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1569_; 
v_fst_1554_ = lean_ctor_get(v_a_1549_, 0);
v_snd_1555_ = lean_ctor_get(v_a_1549_, 1);
v_isSharedCheck_1569_ = !lean_is_exclusive(v_a_1549_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1557_ = v_a_1549_;
v_isShared_1558_ = v_isSharedCheck_1569_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_snd_1555_);
lean_inc(v_fst_1554_);
lean_dec(v_a_1549_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1569_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
size_t v___x_1559_; size_t v___x_1560_; uint8_t v___x_1561_; 
v___x_1559_ = lean_ptr_addr(v_expr_1547_);
v___x_1560_ = lean_ptr_addr(v_fst_1554_);
v___x_1561_ = lean_usize_dec_eq(v___x_1559_, v___x_1560_);
if (v___x_1561_ == 0)
{
lean_object* v___x_1562_; 
lean_inc(v_data_1546_);
lean_del_object(v___x_1557_);
lean_del_object(v___x_1552_);
lean_dec_ref_known(v_e_1378_, 2);
v___x_1562_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__5(v_data_1546_, v_fst_1554_, v_snd_1555_, v_a_1381_, v_a_1382_, v_a_1550_);
return v___x_1562_;
}
else
{
lean_object* v___x_1564_; 
lean_dec(v_fst_1554_);
if (v_isShared_1558_ == 0)
{
lean_ctor_set(v___x_1557_, 0, v_e_1378_);
v___x_1564_ = v___x_1557_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_e_1378_);
lean_ctor_set(v_reuseFailAlloc_1568_, 1, v_snd_1555_);
v___x_1564_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
lean_object* v___x_1566_; 
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 0, v___x_1564_);
v___x_1566_ = v___x_1552_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1564_);
lean_ctor_set(v_reuseFailAlloc_1567_, 1, v_a_1550_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1378_, 2);
return v___x_1548_;
}
}
case 11:
{
lean_object* v_typeName_1571_; lean_object* v_idx_1572_; lean_object* v_struct_1573_; lean_object* v___x_1574_; 
v_typeName_1571_ = lean_ctor_get(v_e_1378_, 0);
v_idx_1572_ = lean_ctor_get(v_e_1378_, 1);
v_struct_1573_ = lean_ctor_get(v_e_1378_, 2);
lean_inc_ref(v_struct_1573_);
v___x_1574_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1376_, v_xs_1377_, v_struct_1573_, v_offset_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v_a_1575_; lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1596_; 
v_a_1575_ = lean_ctor_get(v___x_1574_, 0);
v_a_1576_ = lean_ctor_get(v___x_1574_, 1);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1578_ = v___x_1574_;
v_isShared_1579_ = v_isSharedCheck_1596_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_inc(v_a_1575_);
lean_dec(v___x_1574_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1596_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v_fst_1580_; lean_object* v_snd_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1595_; 
v_fst_1580_ = lean_ctor_get(v_a_1575_, 0);
v_snd_1581_ = lean_ctor_get(v_a_1575_, 1);
v_isSharedCheck_1595_ = !lean_is_exclusive(v_a_1575_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1583_ = v_a_1575_;
v_isShared_1584_ = v_isSharedCheck_1595_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_snd_1581_);
lean_inc(v_fst_1580_);
lean_dec(v_a_1575_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1595_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
size_t v___x_1585_; size_t v___x_1586_; uint8_t v___x_1587_; 
v___x_1585_ = lean_ptr_addr(v_struct_1573_);
v___x_1586_ = lean_ptr_addr(v_fst_1580_);
v___x_1587_ = lean_usize_dec_eq(v___x_1585_, v___x_1586_);
if (v___x_1587_ == 0)
{
lean_object* v___x_1588_; 
lean_inc(v_idx_1572_);
lean_inc(v_typeName_1571_);
lean_del_object(v___x_1583_);
lean_del_object(v___x_1578_);
lean_dec_ref_known(v_e_1378_, 3);
v___x_1588_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__6(v_typeName_1571_, v_idx_1572_, v_fst_1580_, v_snd_1581_, v_a_1381_, v_a_1382_, v_a_1576_);
return v___x_1588_;
}
else
{
lean_object* v___x_1590_; 
lean_dec(v_fst_1580_);
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 0, v_e_1378_);
v___x_1590_ = v___x_1583_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_e_1378_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v_snd_1581_);
v___x_1590_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
lean_object* v___x_1592_; 
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 0, v___x_1590_);
v___x_1592_ = v___x_1578_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1590_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v_a_1576_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1378_, 3);
return v___x_1574_;
}
}
default: 
{
lean_object* v___x_1597_; lean_object* v___x_1598_; 
lean_dec(v_offset_1379_);
lean_dec_ref(v_e_1378_);
v___x_1597_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__3);
v___x_1598_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7(v___x_1597_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
return v___x_1598_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(lean_object* v_n_1599_, lean_object* v_xs_1600_, lean_object* v_e_1601_, lean_object* v_offset_1602_, lean_object* v_a_1603_, uint8_t v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_){
_start:
{
lean_object* v_key_1607_; lean_object* v___x_1608_; 
lean_inc(v_offset_1602_);
lean_inc_ref(v_e_1601_);
v_key_1607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1607_, 0, v_e_1601_);
lean_ctor_set(v_key_1607_, 1, v_offset_1602_);
v___x_1608_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2___redArg(v_a_1603_, v_key_1607_);
if (lean_obj_tag(v___x_1608_) == 1)
{
lean_object* v_val_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
lean_dec_ref_known(v_key_1607_, 2);
lean_dec(v_offset_1602_);
lean_dec_ref(v_e_1601_);
v_val_1609_ = lean_ctor_get(v___x_1608_, 0);
lean_inc(v_val_1609_);
lean_dec_ref_known(v___x_1608_, 1);
v___x_1610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1610_, 0, v_val_1609_);
lean_ctor_set(v___x_1610_, 1, v_a_1603_);
v___x_1611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1610_);
lean_ctor_set(v___x_1611_, 1, v_a_1606_);
return v___x_1611_;
}
else
{
lean_dec(v___x_1608_);
switch(lean_obj_tag(v_e_1601_))
{
case 0:
{
lean_object* v_deBruijnIndex_1612_; uint8_t v___x_1613_; 
v_deBruijnIndex_1612_ = lean_ctor_get(v_e_1601_, 0);
v___x_1613_ = lean_nat_dec_le(v_offset_1602_, v_deBruijnIndex_1612_);
if (v___x_1613_ == 0)
{
lean_object* v___x_1614_; 
lean_dec(v_offset_1602_);
v___x_1614_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1607_, v_e_1601_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_);
return v___x_1614_;
}
else
{
lean_object* v_size_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; uint8_t v___x_1621_; 
lean_inc(v_deBruijnIndex_1612_);
lean_dec_ref_known(v_e_1601_, 1);
v_size_1615_ = lean_ctor_get(v_xs_1600_, 2);
v___x_1616_ = l_Lean_instInhabitedExpr;
v___x_1617_ = lean_nat_sub(v_deBruijnIndex_1612_, v_offset_1602_);
lean_dec(v_offset_1602_);
lean_dec(v_deBruijnIndex_1612_);
v___x_1618_ = lean_nat_sub(v_n_1599_, v___x_1617_);
lean_dec(v___x_1617_);
v___x_1619_ = lean_unsigned_to_nat(1u);
v___x_1620_ = lean_nat_sub(v___x_1618_, v___x_1619_);
lean_dec(v___x_1618_);
v___x_1621_ = lean_nat_dec_lt(v___x_1620_, v_size_1615_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
lean_dec(v___x_1620_);
v___x_1622_ = l_outOfBounds___redArg(v___x_1616_);
v___x_1623_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1607_, v___x_1622_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_);
return v___x_1623_;
}
else
{
lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1624_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1616_, v_xs_1600_, v___x_1620_);
lean_dec(v___x_1620_);
v___x_1625_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1607_, v___x_1624_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_);
return v___x_1625_;
}
}
}
case 9:
{
lean_object* v___x_1626_; 
lean_dec(v_offset_1602_);
v___x_1626_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1607_, v_e_1601_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_);
return v___x_1626_;
}
case 2:
{
lean_object* v___x_1627_; 
lean_dec(v_offset_1602_);
v___x_1627_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1607_, v_e_1601_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_);
return v___x_1627_;
}
case 1:
{
lean_object* v___x_1628_; 
lean_dec(v_offset_1602_);
v___x_1628_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1607_, v_e_1601_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_);
return v___x_1628_;
}
case 4:
{
lean_object* v___x_1629_; 
lean_dec(v_offset_1602_);
v___x_1629_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1607_, v_e_1601_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_);
return v___x_1629_;
}
case 3:
{
lean_object* v___x_1630_; 
lean_dec(v_offset_1602_);
v___x_1630_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1607_, v_e_1601_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_);
return v___x_1630_;
}
default: 
{
lean_object* v___x_1631_; uint8_t v___x_1632_; 
v___x_1631_ = l_Lean_Expr_looseBVarRange(v_e_1601_);
v___x_1632_ = lean_nat_dec_le(v___x_1631_, v_offset_1602_);
lean_dec(v___x_1631_);
if (v___x_1632_ == 0)
{
switch(lean_obj_tag(v_e_1601_))
{
case 9:
{
lean_object* v___x_1633_; 
lean_dec(v_offset_1602_);
v___x_1633_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1607_, v_e_1601_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_);
return v___x_1633_;
}
case 2:
{
lean_object* v___x_1634_; 
lean_dec(v_offset_1602_);
v___x_1634_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1607_, v_e_1601_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_);
return v___x_1634_;
}
case 0:
{
lean_object* v___x_1635_; 
lean_dec(v_offset_1602_);
v___x_1635_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1607_, v_e_1601_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_);
return v___x_1635_;
}
case 1:
{
lean_object* v___x_1636_; 
lean_dec(v_offset_1602_);
v___x_1636_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1607_, v_e_1601_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_);
return v___x_1636_;
}
case 4:
{
lean_object* v___x_1637_; 
lean_dec(v_offset_1602_);
v___x_1637_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1607_, v_e_1601_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_);
return v___x_1637_;
}
case 3:
{
lean_object* v___x_1638_; 
lean_dec(v_offset_1602_);
v___x_1638_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1607_, v_e_1601_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_);
return v___x_1638_;
}
default: 
{
lean_object* v___x_1639_; 
v___x_1639_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0(v_n_1599_, v_xs_1600_, v_e_1601_, v_offset_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v_a_1641_; lean_object* v_fst_1642_; lean_object* v_snd_1643_; lean_object* v___x_1644_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_a_1640_);
v_a_1641_ = lean_ctor_get(v___x_1639_, 1);
lean_inc(v_a_1641_);
lean_dec_ref_known(v___x_1639_, 2);
v_fst_1642_ = lean_ctor_get(v_a_1640_, 0);
lean_inc(v_fst_1642_);
v_snd_1643_ = lean_ctor_get(v_a_1640_, 1);
lean_inc(v_snd_1643_);
lean_dec(v_a_1640_);
v___x_1644_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1607_, v_fst_1642_, v_snd_1643_, v_a_1604_, v_a_1605_, v_a_1641_);
return v___x_1644_;
}
else
{
lean_dec_ref_known(v_key_1607_, 2);
return v___x_1639_;
}
}
}
}
else
{
lean_object* v___x_1645_; 
lean_dec(v_offset_1602_);
v___x_1645_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1607_, v_e_1601_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_);
return v___x_1645_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0___boxed(lean_object* v_n_1646_, lean_object* v_xs_1647_, lean_object* v_e_1648_, lean_object* v_offset_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_){
_start:
{
uint8_t v_a_boxed_1654_; lean_object* v_res_1655_; 
v_a_boxed_1654_ = lean_unbox(v_a_1651_);
v_res_1655_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1646_, v_xs_1647_, v_e_1648_, v_offset_1649_, v_a_1650_, v_a_boxed_1654_, v_a_1652_, v_a_1653_);
lean_dec_ref(v_a_1652_);
lean_dec_ref(v_xs_1647_);
lean_dec(v_n_1646_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___boxed(lean_object* v_n_1656_, lean_object* v_xs_1657_, lean_object* v_e_1658_, lean_object* v_offset_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_){
_start:
{
uint8_t v_a_boxed_1664_; lean_object* v_res_1665_; 
v_a_boxed_1664_ = lean_unbox(v_a_1661_);
v_res_1665_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0(v_n_1656_, v_xs_1657_, v_e_1658_, v_offset_1659_, v_a_1660_, v_a_boxed_1664_, v_a_1662_, v_a_1663_);
lean_dec_ref(v_a_1662_);
lean_dec_ref(v_xs_1657_);
lean_dec(v_n_1656_);
return v_res_1665_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1666_ = lean_box(0);
v___x_1667_ = lean_unsigned_to_nat(16u);
v___x_1668_ = lean_mk_array(v___x_1667_, v___x_1666_);
return v___x_1668_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1669_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__0, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__0_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__0);
v___x_1670_ = lean_unsigned_to_nat(0u);
v___x_1671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1670_);
lean_ctor_set(v___x_1671_, 1, v___x_1669_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0(lean_object* v_e_1672_, lean_object* v_size_1673_, lean_object* v_xs_1674_, uint8_t v_debug_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = lean_unsigned_to_nat(0u);
switch(lean_obj_tag(v_e_1672_))
{
case 0:
{
lean_object* v_deBruijnIndex_1679_; uint8_t v___x_1680_; 
v_deBruijnIndex_1679_ = lean_ctor_get(v_e_1672_, 0);
v___x_1680_ = lean_nat_dec_le(v___x_1678_, v_deBruijnIndex_1679_);
if (v___x_1680_ == 0)
{
lean_object* v___x_1681_; 
v___x_1681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1681_, 0, v_e_1672_);
lean_ctor_set(v___x_1681_, 1, v___y_1677_);
return v___x_1681_;
}
else
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; uint8_t v___x_1686_; 
lean_inc(v_deBruijnIndex_1679_);
lean_dec_ref_known(v_e_1672_, 1);
v___x_1682_ = l_Lean_instInhabitedExpr;
v___x_1683_ = lean_nat_sub(v_size_1673_, v_deBruijnIndex_1679_);
lean_dec(v_deBruijnIndex_1679_);
v___x_1684_ = lean_unsigned_to_nat(1u);
v___x_1685_ = lean_nat_sub(v___x_1683_, v___x_1684_);
lean_dec(v___x_1683_);
v___x_1686_ = lean_nat_dec_lt(v___x_1685_, v_size_1673_);
if (v___x_1686_ == 0)
{
lean_object* v___x_1687_; lean_object* v___x_1688_; 
lean_dec(v___x_1685_);
v___x_1687_ = l_outOfBounds___redArg(v___x_1682_);
v___x_1688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1687_);
lean_ctor_set(v___x_1688_, 1, v___y_1677_);
return v___x_1688_;
}
else
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1689_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1682_, v_xs_1674_, v___x_1685_);
lean_dec(v___x_1685_);
v___x_1690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1689_);
lean_ctor_set(v___x_1690_, 1, v___y_1677_);
return v___x_1690_;
}
}
}
case 9:
{
lean_object* v___x_1691_; 
v___x_1691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1691_, 0, v_e_1672_);
lean_ctor_set(v___x_1691_, 1, v___y_1677_);
return v___x_1691_;
}
case 2:
{
lean_object* v___x_1692_; 
v___x_1692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1692_, 0, v_e_1672_);
lean_ctor_set(v___x_1692_, 1, v___y_1677_);
return v___x_1692_;
}
case 1:
{
lean_object* v___x_1693_; 
v___x_1693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1693_, 0, v_e_1672_);
lean_ctor_set(v___x_1693_, 1, v___y_1677_);
return v___x_1693_;
}
case 4:
{
lean_object* v___x_1694_; 
v___x_1694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1694_, 0, v_e_1672_);
lean_ctor_set(v___x_1694_, 1, v___y_1677_);
return v___x_1694_;
}
case 3:
{
lean_object* v___x_1695_; 
v___x_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1695_, 0, v_e_1672_);
lean_ctor_set(v___x_1695_, 1, v___y_1677_);
return v___x_1695_;
}
default: 
{
lean_object* v___x_1696_; uint8_t v___x_1697_; 
v___x_1696_ = l_Lean_Expr_looseBVarRange(v_e_1672_);
v___x_1697_ = lean_nat_dec_le(v___x_1696_, v___x_1678_);
lean_dec(v___x_1696_);
if (v___x_1697_ == 0)
{
switch(lean_obj_tag(v_e_1672_))
{
case 9:
{
lean_object* v___x_1698_; 
v___x_1698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1698_, 0, v_e_1672_);
lean_ctor_set(v___x_1698_, 1, v___y_1677_);
return v___x_1698_;
}
case 2:
{
lean_object* v___x_1699_; 
v___x_1699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1699_, 0, v_e_1672_);
lean_ctor_set(v___x_1699_, 1, v___y_1677_);
return v___x_1699_;
}
case 0:
{
lean_object* v___x_1700_; 
v___x_1700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1700_, 0, v_e_1672_);
lean_ctor_set(v___x_1700_, 1, v___y_1677_);
return v___x_1700_;
}
case 1:
{
lean_object* v___x_1701_; 
v___x_1701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1701_, 0, v_e_1672_);
lean_ctor_set(v___x_1701_, 1, v___y_1677_);
return v___x_1701_;
}
case 4:
{
lean_object* v___x_1702_; 
v___x_1702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1702_, 0, v_e_1672_);
lean_ctor_set(v___x_1702_, 1, v___y_1677_);
return v___x_1702_;
}
case 3:
{
lean_object* v___x_1703_; 
v___x_1703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1703_, 0, v_e_1672_);
lean_ctor_set(v___x_1703_, 1, v___y_1677_);
return v___x_1703_;
}
default: 
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1704_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__1, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__1);
v___x_1705_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0(v_size_1673_, v_xs_1674_, v_e_1672_, v___x_1678_, v___x_1704_, v_debug_1675_, v___y_1676_, v___y_1677_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_a_1706_; lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1715_; 
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
v_a_1707_ = lean_ctor_get(v___x_1705_, 1);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1709_ = v___x_1705_;
v_isShared_1710_ = v_isSharedCheck_1715_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_inc(v_a_1706_);
lean_dec(v___x_1705_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1715_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v_fst_1711_; lean_object* v___x_1713_; 
v_fst_1711_ = lean_ctor_get(v_a_1706_, 0);
lean_inc(v_fst_1711_);
lean_dec(v_a_1706_);
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 0, v_fst_1711_);
v___x_1713_ = v___x_1709_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_fst_1711_);
lean_ctor_set(v_reuseFailAlloc_1714_, 1, v_a_1707_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
else
{
lean_object* v_a_1716_; lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1724_; 
v_a_1716_ = lean_ctor_get(v___x_1705_, 0);
v_a_1717_ = lean_ctor_get(v___x_1705_, 1);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1719_ = v___x_1705_;
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_inc(v_a_1716_);
lean_dec(v___x_1705_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1722_; 
if (v_isShared_1720_ == 0)
{
v___x_1722_ = v___x_1719_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_a_1716_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v_a_1717_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
}
}
}
else
{
lean_object* v___x_1725_; 
v___x_1725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1725_, 0, v_e_1672_);
lean_ctor_set(v___x_1725_, 1, v___y_1677_);
return v___x_1725_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___boxed(lean_object* v_e_1726_, lean_object* v_size_1727_, lean_object* v_xs_1728_, lean_object* v_debug_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
uint8_t v_debug_boxed_1732_; lean_object* v_res_1733_; 
v_debug_boxed_1732_ = lean_unbox(v_debug_1729_);
v_res_1733_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0(v_e_1726_, v_size_1727_, v_xs_1728_, v_debug_boxed_1732_, v___y_1730_, v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec_ref(v_xs_1728_);
lean_dec(v_size_1727_);
return v_res_1733_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2(void){
_start:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1736_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__2));
v___x_1737_ = lean_unsigned_to_nat(16u);
v___x_1738_ = lean_unsigned_to_nat(62u);
v___x_1739_ = ((lean_object*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__1));
v___x_1740_ = ((lean_object*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__0));
v___x_1741_ = l_mkPanicMessageWithDecl(v___x_1740_, v___x_1739_, v___x_1738_, v___x_1737_, v___x_1736_);
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg(lean_object* v_xs_1742_, lean_object* v_e_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_){
_start:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v_size_1753_; uint8_t v_debug_1754_; lean_object* v_env_1755_; lean_object* v___x_1756_; lean_object* v___f_1757_; uint8_t v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1751_ = lean_st_ref_get(v_a_1745_);
v___x_1752_ = lean_st_ref_get(v_a_1749_);
v_size_1753_ = lean_ctor_get(v_xs_1742_, 2);
lean_inc(v_size_1753_);
v_debug_1754_ = lean_ctor_get_uint8(v___x_1751_, sizeof(void*)*11);
lean_dec(v___x_1751_);
v_env_1755_ = lean_ctor_get(v___x_1752_, 0);
lean_inc_ref(v_env_1755_);
lean_dec(v___x_1752_);
v___x_1756_ = lean_box(v_debug_1754_);
v___f_1757_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1757_, 0, v_e_1743_);
lean_closure_set(v___f_1757_, 1, v_size_1753_);
lean_closure_set(v___f_1757_, 2, v_xs_1742_);
lean_closure_set(v___f_1757_, 3, v___x_1756_);
v___x_1758_ = 0;
v___x_1759_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1759_, 0, v_env_1755_);
lean_ctor_set_uint8(v___x_1759_, sizeof(void*)*1, v___x_1758_);
lean_ctor_set_uint8(v___x_1759_, sizeof(void*)*1 + 1, v___x_1758_);
v___x_1760_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_1757_, v___x_1759_, v_a_1745_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1771_; 
v_a_1761_ = lean_ctor_get(v___x_1760_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1763_ = v___x_1760_;
v_isShared_1764_ = v_isSharedCheck_1771_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1760_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1771_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
if (lean_obj_tag(v_a_1761_) == 0)
{
lean_object* v___x_1765_; lean_object* v___x_1766_; 
lean_dec_ref_known(v_a_1761_, 1);
lean_del_object(v___x_1763_);
v___x_1765_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2);
v___x_1766_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1(v___x_1765_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_);
return v___x_1766_;
}
else
{
lean_object* v_a_1767_; lean_object* v___x_1769_; 
v_a_1767_ = lean_ctor_get(v_a_1761_, 0);
lean_inc(v_a_1767_);
lean_dec_ref_known(v_a_1761_, 1);
if (v_isShared_1764_ == 0)
{
lean_ctor_set(v___x_1763_, 0, v_a_1767_);
v___x_1769_ = v___x_1763_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_a_1767_);
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
else
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1779_; 
v_a_1772_ = lean_ctor_get(v___x_1760_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1774_ = v___x_1760_;
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1760_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1777_; 
if (v_isShared_1775_ == 0)
{
v___x_1777_ = v___x_1774_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_a_1772_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___boxed(lean_object* v_xs_1780_, lean_object* v_e_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_){
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg(v_xs_1780_, v_e_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
lean_dec(v_a_1787_);
lean_dec_ref(v_a_1786_);
lean_dec(v_a_1785_);
lean_dec_ref(v_a_1784_);
lean_dec(v_a_1783_);
lean_dec_ref(v_a_1782_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv(lean_object* v_xs_1790_, lean_object* v_e_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_){
_start:
{
lean_object* v___x_1800_; 
v___x_1800_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg(v_xs_1790_, v_e_1791_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___boxed(lean_object* v_xs_1801_, lean_object* v_e_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv(v_xs_1801_, v_e_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_);
lean_dec(v_a_1809_);
lean_dec_ref(v_a_1808_);
lean_dec(v_a_1807_);
lean_dec_ref(v_a_1806_);
lean_dec(v_a_1805_);
lean_dec_ref(v_a_1804_);
lean_dec(v_a_1803_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1812_, lean_object* v_m_1813_, lean_object* v_a_1814_){
_start:
{
lean_object* v___x_1815_; 
v___x_1815_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2___redArg(v_m_1813_, v_a_1814_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1816_, lean_object* v_m_1817_, lean_object* v_a_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2(v_00_u03b2_1816_, v_m_1817_, v_a_1818_);
lean_dec_ref(v_a_1818_);
lean_dec_ref(v_m_1817_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10(lean_object* v_00_u03b2_1820_, lean_object* v_a_1821_, lean_object* v_x_1822_){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10___redArg(v_a_1821_, v_x_1822_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10___boxed(lean_object* v_00_u03b2_1824_, lean_object* v_a_1825_, lean_object* v_x_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10(v_00_u03b2_1824_, v_a_1825_, v_x_1826_);
lean_dec(v_x_1826_);
lean_dec_ref(v_a_1825_);
return v_res_1827_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1828_; 
v___x_1828_ = l_instMonadEIO(lean_box(0));
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(lean_object* v_msg_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v_toApplicative_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1908_; 
v___x_1842_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__0);
v___x_1843_ = l_StateRefT_x27_instMonad___redArg(v___x_1842_);
v_toApplicative_1844_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1908_ == 0)
{
lean_object* v_unused_1909_; 
v_unused_1909_ = lean_ctor_get(v___x_1843_, 1);
lean_dec(v_unused_1909_);
v___x_1846_ = v___x_1843_;
v_isShared_1847_ = v_isSharedCheck_1908_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_toApplicative_1844_);
lean_dec(v___x_1843_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1908_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v_toFunctor_1848_; lean_object* v_toSeq_1849_; lean_object* v_toSeqLeft_1850_; lean_object* v_toSeqRight_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1906_; 
v_toFunctor_1848_ = lean_ctor_get(v_toApplicative_1844_, 0);
v_toSeq_1849_ = lean_ctor_get(v_toApplicative_1844_, 2);
v_toSeqLeft_1850_ = lean_ctor_get(v_toApplicative_1844_, 3);
v_toSeqRight_1851_ = lean_ctor_get(v_toApplicative_1844_, 4);
v_isSharedCheck_1906_ = !lean_is_exclusive(v_toApplicative_1844_);
if (v_isSharedCheck_1906_ == 0)
{
lean_object* v_unused_1907_; 
v_unused_1907_ = lean_ctor_get(v_toApplicative_1844_, 1);
lean_dec(v_unused_1907_);
v___x_1853_ = v_toApplicative_1844_;
v_isShared_1854_ = v_isSharedCheck_1906_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_toSeqRight_1851_);
lean_inc(v_toSeqLeft_1850_);
lean_inc(v_toSeq_1849_);
lean_inc(v_toFunctor_1848_);
lean_dec(v_toApplicative_1844_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1906_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___f_1855_; lean_object* v___f_1856_; lean_object* v___f_1857_; lean_object* v___f_1858_; lean_object* v___x_1859_; lean_object* v___f_1860_; lean_object* v___f_1861_; lean_object* v___f_1862_; lean_object* v___x_1864_; 
v___f_1855_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__1));
v___f_1856_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1848_);
v___f_1857_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1857_, 0, v_toFunctor_1848_);
v___f_1858_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1858_, 0, v_toFunctor_1848_);
v___x_1859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___f_1857_);
lean_ctor_set(v___x_1859_, 1, v___f_1858_);
v___f_1860_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1860_, 0, v_toSeqRight_1851_);
v___f_1861_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1861_, 0, v_toSeqLeft_1850_);
v___f_1862_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1862_, 0, v_toSeq_1849_);
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 4, v___f_1860_);
lean_ctor_set(v___x_1853_, 3, v___f_1861_);
lean_ctor_set(v___x_1853_, 2, v___f_1862_);
lean_ctor_set(v___x_1853_, 1, v___f_1855_);
lean_ctor_set(v___x_1853_, 0, v___x_1859_);
v___x_1864_ = v___x_1853_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v___x_1859_);
lean_ctor_set(v_reuseFailAlloc_1905_, 1, v___f_1855_);
lean_ctor_set(v_reuseFailAlloc_1905_, 2, v___f_1862_);
lean_ctor_set(v_reuseFailAlloc_1905_, 3, v___f_1861_);
lean_ctor_set(v_reuseFailAlloc_1905_, 4, v___f_1860_);
v___x_1864_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
lean_object* v___x_1866_; 
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 1, v___f_1856_);
lean_ctor_set(v___x_1846_, 0, v___x_1864_);
v___x_1866_ = v___x_1846_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v___x_1864_);
lean_ctor_set(v_reuseFailAlloc_1904_, 1, v___f_1856_);
v___x_1866_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
lean_object* v___x_1867_; lean_object* v_toApplicative_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1902_; 
v___x_1867_ = l_StateRefT_x27_instMonad___redArg(v___x_1866_);
v_toApplicative_1868_ = lean_ctor_get(v___x_1867_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1902_ == 0)
{
lean_object* v_unused_1903_; 
v_unused_1903_ = lean_ctor_get(v___x_1867_, 1);
lean_dec(v_unused_1903_);
v___x_1870_ = v___x_1867_;
v_isShared_1871_ = v_isSharedCheck_1902_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_toApplicative_1868_);
lean_dec(v___x_1867_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1902_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v_toFunctor_1872_; lean_object* v_toSeq_1873_; lean_object* v_toSeqLeft_1874_; lean_object* v_toSeqRight_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1900_; 
v_toFunctor_1872_ = lean_ctor_get(v_toApplicative_1868_, 0);
v_toSeq_1873_ = lean_ctor_get(v_toApplicative_1868_, 2);
v_toSeqLeft_1874_ = lean_ctor_get(v_toApplicative_1868_, 3);
v_toSeqRight_1875_ = lean_ctor_get(v_toApplicative_1868_, 4);
v_isSharedCheck_1900_ = !lean_is_exclusive(v_toApplicative_1868_);
if (v_isSharedCheck_1900_ == 0)
{
lean_object* v_unused_1901_; 
v_unused_1901_ = lean_ctor_get(v_toApplicative_1868_, 1);
lean_dec(v_unused_1901_);
v___x_1877_ = v_toApplicative_1868_;
v_isShared_1878_ = v_isSharedCheck_1900_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_toSeqRight_1875_);
lean_inc(v_toSeqLeft_1874_);
lean_inc(v_toSeq_1873_);
lean_inc(v_toFunctor_1872_);
lean_dec(v_toApplicative_1868_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1900_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___f_1879_; lean_object* v___f_1880_; lean_object* v___f_1881_; lean_object* v___f_1882_; lean_object* v___x_1883_; lean_object* v___f_1884_; lean_object* v___f_1885_; lean_object* v___f_1886_; lean_object* v___x_1888_; 
v___f_1879_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__3));
v___f_1880_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1872_);
v___f_1881_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1881_, 0, v_toFunctor_1872_);
v___f_1882_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1882_, 0, v_toFunctor_1872_);
v___x_1883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1883_, 0, v___f_1881_);
lean_ctor_set(v___x_1883_, 1, v___f_1882_);
v___f_1884_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1884_, 0, v_toSeqRight_1875_);
v___f_1885_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1885_, 0, v_toSeqLeft_1874_);
v___f_1886_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1886_, 0, v_toSeq_1873_);
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 4, v___f_1884_);
lean_ctor_set(v___x_1877_, 3, v___f_1885_);
lean_ctor_set(v___x_1877_, 2, v___f_1886_);
lean_ctor_set(v___x_1877_, 1, v___f_1879_);
lean_ctor_set(v___x_1877_, 0, v___x_1883_);
v___x_1888_ = v___x_1877_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1883_);
lean_ctor_set(v_reuseFailAlloc_1899_, 1, v___f_1879_);
lean_ctor_set(v_reuseFailAlloc_1899_, 2, v___f_1886_);
lean_ctor_set(v_reuseFailAlloc_1899_, 3, v___f_1885_);
lean_ctor_set(v_reuseFailAlloc_1899_, 4, v___f_1884_);
v___x_1888_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
lean_object* v___x_1890_; 
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 1, v___f_1880_);
lean_ctor_set(v___x_1870_, 0, v___x_1888_);
v___x_1890_ = v___x_1870_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v___x_1888_);
lean_ctor_set(v_reuseFailAlloc_1898_, 1, v___f_1880_);
v___x_1890_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_15845__overap_1896_; lean_object* v___x_1897_; 
v___x_1891_ = l_StateRefT_x27_instMonad___redArg(v___x_1890_);
v___x_1892_ = l_ReaderT_instMonad___redArg(v___x_1891_);
v___x_1893_ = l_StateRefT_x27_instMonad___redArg(v___x_1892_);
v___x_1894_ = l_Lean_instInhabitedExpr;
v___x_1895_ = l_instInhabitedOfMonad___redArg(v___x_1893_, v___x_1894_);
v___x_15845__overap_1896_ = lean_panic_fn_borrowed(v___x_1895_, v_msg_1833_);
lean_dec(v___x_1895_);
lean_inc(v___y_1840_);
lean_inc_ref(v___y_1839_);
lean_inc(v___y_1838_);
lean_inc_ref(v___y_1837_);
lean_inc(v___y_1836_);
lean_inc_ref(v___y_1835_);
lean_inc(v___y_1834_);
v___x_1897_ = lean_apply_8(v___x_15845__overap_1896_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, lean_box(0));
return v___x_1897_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___boxed(lean_object* v_msg_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_){
_start:
{
lean_object* v_res_1919_; 
v_res_1919_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(v_msg_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec(v___y_1911_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1___redArg(lean_object* v_f_1920_, lean_object* v_a_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
lean_object* v___y_1930_; lean_object* v___x_1933_; uint8_t v_debug_1934_; 
v___x_1933_ = lean_st_ref_get(v___y_1923_);
v_debug_1934_ = lean_ctor_get_uint8(v___x_1933_, sizeof(void*)*11);
lean_dec(v___x_1933_);
if (v_debug_1934_ == 0)
{
v___y_1930_ = v___y_1923_;
goto v___jp_1929_;
}
else
{
lean_object* v___x_1935_; 
v___x_1935_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_1920_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v___x_1936_; 
lean_dec_ref_known(v___x_1935_, 1);
v___x_1936_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_dec_ref_known(v___x_1936_, 1);
v___y_1930_ = v___y_1923_;
goto v___jp_1929_;
}
else
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
lean_dec_ref(v_a_1921_);
lean_dec_ref(v_f_1920_);
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1939_ = v___x_1936_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1936_);
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
else
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
lean_dec_ref(v_a_1921_);
lean_dec_ref(v_f_1920_);
v_a_1945_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___x_1935_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1935_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
v___jp_1929_:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1931_ = l_Lean_Expr_app___override(v_f_1920_, v_a_1921_);
v___x_1932_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1931_, v___y_1930_);
return v___x_1932_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1___redArg___boxed(lean_object* v_f_1953_, lean_object* v_a_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v_res_1962_; 
v_res_1962_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1___redArg(v_f_1953_, v_a_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1(lean_object* v_f_1963_, lean_object* v_a_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v___x_1973_; 
v___x_1973_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1___redArg(v_f_1963_, v_a_1964_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1___boxed(lean_object* v_f_1974_, lean_object* v_a_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1(v_f_1974_, v_a_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v___y_1976_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2___redArg(lean_object* v_d_1985_, lean_object* v_e_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v___y_1995_; lean_object* v___x_1998_; uint8_t v_debug_1999_; 
v___x_1998_ = lean_st_ref_get(v___y_1988_);
v_debug_1999_ = lean_ctor_get_uint8(v___x_1998_, sizeof(void*)*11);
lean_dec(v___x_1998_);
if (v_debug_1999_ == 0)
{
v___y_1995_ = v___y_1988_;
goto v___jp_1994_;
}
else
{
lean_object* v___x_2000_; 
v___x_2000_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_e_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_dec_ref_known(v___x_2000_, 1);
v___y_1995_ = v___y_1988_;
goto v___jp_1994_;
}
else
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
lean_dec_ref(v_e_1986_);
lean_dec(v_d_1985_);
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2003_ = v___x_2000_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_2000_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_a_2001_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
v___jp_1994_:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1996_ = l_Lean_Expr_mdata___override(v_d_1985_, v_e_1986_);
v___x_1997_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1996_, v___y_1995_);
return v___x_1997_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2___redArg___boxed(lean_object* v_d_2009_, lean_object* v_e_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2___redArg(v_d_2009_, v_e_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2(lean_object* v_d_2019_, lean_object* v_e_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_){
_start:
{
lean_object* v___x_2029_; 
v___x_2029_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2___redArg(v_d_2019_, v_e_2020_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
return v___x_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2___boxed(lean_object* v_d_2030_, lean_object* v_e_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2(v_d_2030_, v_e_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
lean_dec(v___y_2036_);
lean_dec_ref(v___y_2035_);
lean_dec(v___y_2034_);
lean_dec_ref(v___y_2033_);
lean_dec(v___y_2032_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3___redArg(lean_object* v_structName_2041_, lean_object* v_idx_2042_, lean_object* v_struct_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_){
_start:
{
lean_object* v___y_2052_; lean_object* v___x_2055_; uint8_t v_debug_2056_; 
v___x_2055_ = lean_st_ref_get(v___y_2045_);
v_debug_2056_ = lean_ctor_get_uint8(v___x_2055_, sizeof(void*)*11);
lean_dec(v___x_2055_);
if (v_debug_2056_ == 0)
{
v___y_2052_ = v___y_2045_;
goto v___jp_2051_;
}
else
{
lean_object* v___x_2057_; 
v___x_2057_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_struct_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_dec_ref_known(v___x_2057_, 1);
v___y_2052_ = v___y_2045_;
goto v___jp_2051_;
}
else
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
lean_dec_ref(v_struct_2043_);
lean_dec(v_idx_2042_);
lean_dec(v_structName_2041_);
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v___x_2057_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2057_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2063_; 
if (v_isShared_2061_ == 0)
{
v___x_2063_ = v___x_2060_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_a_2058_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
}
v___jp_2051_:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2053_ = l_Lean_Expr_proj___override(v_structName_2041_, v_idx_2042_, v_struct_2043_);
v___x_2054_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2053_, v___y_2052_);
return v___x_2054_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3___redArg___boxed(lean_object* v_structName_2066_, lean_object* v_idx_2067_, lean_object* v_struct_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3___redArg(v_structName_2066_, v_idx_2067_, v_struct_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
lean_dec(v___y_2074_);
lean_dec_ref(v___y_2073_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3(lean_object* v_structName_2077_, lean_object* v_idx_2078_, lean_object* v_struct_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_){
_start:
{
lean_object* v___x_2088_; 
v___x_2088_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3___redArg(v_structName_2077_, v_idx_2078_, v_struct_2079_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_);
return v___x_2088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3___boxed(lean_object* v_structName_2089_, lean_object* v_idx_2090_, lean_object* v_struct_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3(v_structName_2089_, v_idx_2090_, v_struct_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2092_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5_spec__5(lean_object* v_msgData_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
lean_object* v___x_2107_; lean_object* v_env_2108_; lean_object* v___x_2109_; lean_object* v_mctx_2110_; lean_object* v_lctx_2111_; lean_object* v_options_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2107_ = lean_st_ref_get(v___y_2105_);
v_env_2108_ = lean_ctor_get(v___x_2107_, 0);
lean_inc_ref(v_env_2108_);
lean_dec(v___x_2107_);
v___x_2109_ = lean_st_ref_get(v___y_2103_);
v_mctx_2110_ = lean_ctor_get(v___x_2109_, 0);
lean_inc_ref(v_mctx_2110_);
lean_dec(v___x_2109_);
v_lctx_2111_ = lean_ctor_get(v___y_2102_, 2);
v_options_2112_ = lean_ctor_get(v___y_2104_, 2);
lean_inc_ref(v_options_2112_);
lean_inc_ref(v_lctx_2111_);
v___x_2113_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2113_, 0, v_env_2108_);
lean_ctor_set(v___x_2113_, 1, v_mctx_2110_);
lean_ctor_set(v___x_2113_, 2, v_lctx_2111_);
lean_ctor_set(v___x_2113_, 3, v_options_2112_);
v___x_2114_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2113_);
lean_ctor_set(v___x_2114_, 1, v_msgData_2101_);
v___x_2115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5_spec__5___boxed(lean_object* v_msgData_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
lean_object* v_res_2122_; 
v_res_2122_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5_spec__5(v_msgData_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5___redArg(lean_object* v_msg_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
lean_object* v_ref_2129_; lean_object* v___x_2130_; lean_object* v_a_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2139_; 
v_ref_2129_ = lean_ctor_get(v___y_2126_, 5);
v___x_2130_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5_spec__5(v_msg_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2133_ = v___x_2130_;
v_isShared_2134_ = v_isSharedCheck_2139_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_a_2131_);
lean_dec(v___x_2130_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2139_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2135_; lean_object* v___x_2137_; 
lean_inc(v_ref_2129_);
v___x_2135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2135_, 0, v_ref_2129_);
lean_ctor_set(v___x_2135_, 1, v_a_2131_);
if (v_isShared_2134_ == 0)
{
lean_ctor_set_tag(v___x_2133_, 1);
lean_ctor_set(v___x_2133_, 0, v___x_2135_);
v___x_2137_ = v___x_2133_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v___x_2135_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5___redArg___boxed(lean_object* v_msg_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_){
_start:
{
lean_object* v_res_2146_; 
v_res_2146_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5___redArg(v_msg_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2143_);
lean_dec(v___y_2142_);
lean_dec_ref(v___y_2141_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7___redArg(lean_object* v_a_2147_, lean_object* v_x_2148_){
_start:
{
if (lean_obj_tag(v_x_2148_) == 0)
{
lean_object* v___x_2149_; 
v___x_2149_ = lean_box(0);
return v___x_2149_;
}
else
{
lean_object* v_key_2150_; lean_object* v_value_2151_; lean_object* v_tail_2152_; uint8_t v___y_2154_; lean_object* v_fst_2157_; lean_object* v_snd_2158_; lean_object* v_fst_2159_; lean_object* v_snd_2160_; size_t v___x_2161_; size_t v___x_2162_; uint8_t v___x_2163_; 
v_key_2150_ = lean_ctor_get(v_x_2148_, 0);
v_value_2151_ = lean_ctor_get(v_x_2148_, 1);
v_tail_2152_ = lean_ctor_get(v_x_2148_, 2);
v_fst_2157_ = lean_ctor_get(v_key_2150_, 0);
v_snd_2158_ = lean_ctor_get(v_key_2150_, 1);
v_fst_2159_ = lean_ctor_get(v_a_2147_, 0);
v_snd_2160_ = lean_ctor_get(v_a_2147_, 1);
v___x_2161_ = lean_ptr_addr(v_fst_2157_);
v___x_2162_ = lean_ptr_addr(v_fst_2159_);
v___x_2163_ = lean_usize_dec_eq(v___x_2161_, v___x_2162_);
if (v___x_2163_ == 0)
{
v___y_2154_ = v___x_2163_;
goto v___jp_2153_;
}
else
{
size_t v___x_2164_; size_t v___x_2165_; uint8_t v___x_2166_; 
v___x_2164_ = lean_ptr_addr(v_snd_2158_);
v___x_2165_ = lean_ptr_addr(v_snd_2160_);
v___x_2166_ = lean_usize_dec_eq(v___x_2164_, v___x_2165_);
v___y_2154_ = v___x_2166_;
goto v___jp_2153_;
}
v___jp_2153_:
{
if (v___y_2154_ == 0)
{
v_x_2148_ = v_tail_2152_;
goto _start;
}
else
{
lean_object* v___x_2156_; 
lean_inc(v_value_2151_);
v___x_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2156_, 0, v_value_2151_);
return v___x_2156_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7___redArg___boxed(lean_object* v_a_2167_, lean_object* v_x_2168_){
_start:
{
lean_object* v_res_2169_; 
v_res_2169_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7___redArg(v_a_2167_, v_x_2168_);
lean_dec(v_x_2168_);
lean_dec_ref(v_a_2167_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6___redArg(lean_object* v_m_2170_, lean_object* v_a_2171_){
_start:
{
lean_object* v_buckets_2172_; lean_object* v_fst_2173_; lean_object* v_snd_2174_; lean_object* v___x_2175_; size_t v___x_2176_; size_t v___x_2177_; size_t v___x_2178_; uint64_t v___x_2179_; size_t v___x_2180_; size_t v___x_2181_; uint64_t v___x_2182_; uint64_t v___x_2183_; uint64_t v___x_2184_; uint64_t v___x_2185_; uint64_t v_fold_2186_; uint64_t v___x_2187_; uint64_t v___x_2188_; uint64_t v___x_2189_; size_t v___x_2190_; size_t v___x_2191_; size_t v___x_2192_; size_t v___x_2193_; size_t v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v_buckets_2172_ = lean_ctor_get(v_m_2170_, 1);
v_fst_2173_ = lean_ctor_get(v_a_2171_, 0);
v_snd_2174_ = lean_ctor_get(v_a_2171_, 1);
v___x_2175_ = lean_array_get_size(v_buckets_2172_);
v___x_2176_ = lean_ptr_addr(v_fst_2173_);
v___x_2177_ = ((size_t)3ULL);
v___x_2178_ = lean_usize_shift_right(v___x_2176_, v___x_2177_);
v___x_2179_ = lean_usize_to_uint64(v___x_2178_);
v___x_2180_ = lean_ptr_addr(v_snd_2174_);
v___x_2181_ = lean_usize_shift_right(v___x_2180_, v___x_2177_);
v___x_2182_ = lean_usize_to_uint64(v___x_2181_);
v___x_2183_ = lean_uint64_mix_hash(v___x_2179_, v___x_2182_);
v___x_2184_ = 32ULL;
v___x_2185_ = lean_uint64_shift_right(v___x_2183_, v___x_2184_);
v_fold_2186_ = lean_uint64_xor(v___x_2183_, v___x_2185_);
v___x_2187_ = 16ULL;
v___x_2188_ = lean_uint64_shift_right(v_fold_2186_, v___x_2187_);
v___x_2189_ = lean_uint64_xor(v_fold_2186_, v___x_2188_);
v___x_2190_ = lean_uint64_to_usize(v___x_2189_);
v___x_2191_ = lean_usize_of_nat(v___x_2175_);
v___x_2192_ = ((size_t)1ULL);
v___x_2193_ = lean_usize_sub(v___x_2191_, v___x_2192_);
v___x_2194_ = lean_usize_land(v___x_2190_, v___x_2193_);
v___x_2195_ = lean_array_uget_borrowed(v_buckets_2172_, v___x_2194_);
v___x_2196_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7___redArg(v_a_2171_, v___x_2195_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6___redArg___boxed(lean_object* v_m_2197_, lean_object* v_a_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6___redArg(v_m_2197_, v_a_2198_);
lean_dec_ref(v_a_2198_);
lean_dec_ref(v_m_2197_);
return v_res_2199_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9___redArg(lean_object* v_a_2200_, lean_object* v_x_2201_){
_start:
{
if (lean_obj_tag(v_x_2201_) == 0)
{
uint8_t v___x_2202_; 
v___x_2202_ = 0;
return v___x_2202_;
}
else
{
lean_object* v_key_2203_; lean_object* v_tail_2204_; uint8_t v___y_2206_; lean_object* v_fst_2208_; lean_object* v_snd_2209_; lean_object* v_fst_2210_; lean_object* v_snd_2211_; size_t v___x_2212_; size_t v___x_2213_; uint8_t v___x_2214_; 
v_key_2203_ = lean_ctor_get(v_x_2201_, 0);
v_tail_2204_ = lean_ctor_get(v_x_2201_, 2);
v_fst_2208_ = lean_ctor_get(v_key_2203_, 0);
v_snd_2209_ = lean_ctor_get(v_key_2203_, 1);
v_fst_2210_ = lean_ctor_get(v_a_2200_, 0);
v_snd_2211_ = lean_ctor_get(v_a_2200_, 1);
v___x_2212_ = lean_ptr_addr(v_fst_2208_);
v___x_2213_ = lean_ptr_addr(v_fst_2210_);
v___x_2214_ = lean_usize_dec_eq(v___x_2212_, v___x_2213_);
if (v___x_2214_ == 0)
{
v___y_2206_ = v___x_2214_;
goto v___jp_2205_;
}
else
{
size_t v___x_2215_; size_t v___x_2216_; uint8_t v___x_2217_; 
v___x_2215_ = lean_ptr_addr(v_snd_2209_);
v___x_2216_ = lean_ptr_addr(v_snd_2211_);
v___x_2217_ = lean_usize_dec_eq(v___x_2215_, v___x_2216_);
v___y_2206_ = v___x_2217_;
goto v___jp_2205_;
}
v___jp_2205_:
{
if (v___y_2206_ == 0)
{
v_x_2201_ = v_tail_2204_;
goto _start;
}
else
{
return v___y_2206_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9___redArg___boxed(lean_object* v_a_2218_, lean_object* v_x_2219_){
_start:
{
uint8_t v_res_2220_; lean_object* v_r_2221_; 
v_res_2220_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9___redArg(v_a_2218_, v_x_2219_);
lean_dec(v_x_2219_);
lean_dec_ref(v_a_2218_);
v_r_2221_ = lean_box(v_res_2220_);
return v_r_2221_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__11___redArg(lean_object* v_a_2222_, lean_object* v_b_2223_, lean_object* v_x_2224_){
_start:
{
if (lean_obj_tag(v_x_2224_) == 0)
{
lean_dec(v_b_2223_);
lean_dec_ref(v_a_2222_);
return v_x_2224_;
}
else
{
lean_object* v_key_2225_; lean_object* v_value_2226_; lean_object* v_tail_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2250_; 
v_key_2225_ = lean_ctor_get(v_x_2224_, 0);
v_value_2226_ = lean_ctor_get(v_x_2224_, 1);
v_tail_2227_ = lean_ctor_get(v_x_2224_, 2);
v_isSharedCheck_2250_ = !lean_is_exclusive(v_x_2224_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2229_ = v_x_2224_;
v_isShared_2230_ = v_isSharedCheck_2250_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_tail_2227_);
lean_inc(v_value_2226_);
lean_inc(v_key_2225_);
lean_dec(v_x_2224_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2250_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
uint8_t v___y_2232_; lean_object* v_fst_2240_; lean_object* v_snd_2241_; lean_object* v_fst_2242_; lean_object* v_snd_2243_; size_t v___x_2244_; size_t v___x_2245_; uint8_t v___x_2246_; 
v_fst_2240_ = lean_ctor_get(v_key_2225_, 0);
v_snd_2241_ = lean_ctor_get(v_key_2225_, 1);
v_fst_2242_ = lean_ctor_get(v_a_2222_, 0);
v_snd_2243_ = lean_ctor_get(v_a_2222_, 1);
v___x_2244_ = lean_ptr_addr(v_fst_2240_);
v___x_2245_ = lean_ptr_addr(v_fst_2242_);
v___x_2246_ = lean_usize_dec_eq(v___x_2244_, v___x_2245_);
if (v___x_2246_ == 0)
{
v___y_2232_ = v___x_2246_;
goto v___jp_2231_;
}
else
{
size_t v___x_2247_; size_t v___x_2248_; uint8_t v___x_2249_; 
v___x_2247_ = lean_ptr_addr(v_snd_2241_);
v___x_2248_ = lean_ptr_addr(v_snd_2243_);
v___x_2249_ = lean_usize_dec_eq(v___x_2247_, v___x_2248_);
v___y_2232_ = v___x_2249_;
goto v___jp_2231_;
}
v___jp_2231_:
{
if (v___y_2232_ == 0)
{
lean_object* v___x_2233_; lean_object* v___x_2235_; 
v___x_2233_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__11___redArg(v_a_2222_, v_b_2223_, v_tail_2227_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 2, v___x_2233_);
v___x_2235_ = v___x_2229_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_key_2225_);
lean_ctor_set(v_reuseFailAlloc_2236_, 1, v_value_2226_);
lean_ctor_set(v_reuseFailAlloc_2236_, 2, v___x_2233_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
else
{
lean_object* v___x_2238_; 
lean_dec(v_value_2226_);
lean_dec(v_key_2225_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 1, v_b_2223_);
lean_ctor_set(v___x_2229_, 0, v_a_2222_);
v___x_2238_ = v___x_2229_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_a_2222_);
lean_ctor_set(v_reuseFailAlloc_2239_, 1, v_b_2223_);
lean_ctor_set(v_reuseFailAlloc_2239_, 2, v_tail_2227_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10_spec__11_spec__12___redArg(lean_object* v_x_2251_, lean_object* v_x_2252_){
_start:
{
if (lean_obj_tag(v_x_2252_) == 0)
{
return v_x_2251_;
}
else
{
lean_object* v_key_2253_; lean_object* v_value_2254_; lean_object* v_tail_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2287_; 
v_key_2253_ = lean_ctor_get(v_x_2252_, 0);
v_value_2254_ = lean_ctor_get(v_x_2252_, 1);
v_tail_2255_ = lean_ctor_get(v_x_2252_, 2);
v_isSharedCheck_2287_ = !lean_is_exclusive(v_x_2252_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2257_ = v_x_2252_;
v_isShared_2258_ = v_isSharedCheck_2287_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_tail_2255_);
lean_inc(v_value_2254_);
lean_inc(v_key_2253_);
lean_dec(v_x_2252_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2287_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v_fst_2259_; lean_object* v_snd_2260_; lean_object* v___x_2261_; size_t v___x_2262_; size_t v___x_2263_; size_t v___x_2264_; uint64_t v___x_2265_; size_t v___x_2266_; size_t v___x_2267_; uint64_t v___x_2268_; uint64_t v___x_2269_; uint64_t v___x_2270_; uint64_t v___x_2271_; uint64_t v_fold_2272_; uint64_t v___x_2273_; uint64_t v___x_2274_; uint64_t v___x_2275_; size_t v___x_2276_; size_t v___x_2277_; size_t v___x_2278_; size_t v___x_2279_; size_t v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2283_; 
v_fst_2259_ = lean_ctor_get(v_key_2253_, 0);
v_snd_2260_ = lean_ctor_get(v_key_2253_, 1);
v___x_2261_ = lean_array_get_size(v_x_2251_);
v___x_2262_ = lean_ptr_addr(v_fst_2259_);
v___x_2263_ = ((size_t)3ULL);
v___x_2264_ = lean_usize_shift_right(v___x_2262_, v___x_2263_);
v___x_2265_ = lean_usize_to_uint64(v___x_2264_);
v___x_2266_ = lean_ptr_addr(v_snd_2260_);
v___x_2267_ = lean_usize_shift_right(v___x_2266_, v___x_2263_);
v___x_2268_ = lean_usize_to_uint64(v___x_2267_);
v___x_2269_ = lean_uint64_mix_hash(v___x_2265_, v___x_2268_);
v___x_2270_ = 32ULL;
v___x_2271_ = lean_uint64_shift_right(v___x_2269_, v___x_2270_);
v_fold_2272_ = lean_uint64_xor(v___x_2269_, v___x_2271_);
v___x_2273_ = 16ULL;
v___x_2274_ = lean_uint64_shift_right(v_fold_2272_, v___x_2273_);
v___x_2275_ = lean_uint64_xor(v_fold_2272_, v___x_2274_);
v___x_2276_ = lean_uint64_to_usize(v___x_2275_);
v___x_2277_ = lean_usize_of_nat(v___x_2261_);
v___x_2278_ = ((size_t)1ULL);
v___x_2279_ = lean_usize_sub(v___x_2277_, v___x_2278_);
v___x_2280_ = lean_usize_land(v___x_2276_, v___x_2279_);
v___x_2281_ = lean_array_uget_borrowed(v_x_2251_, v___x_2280_);
lean_inc(v___x_2281_);
if (v_isShared_2258_ == 0)
{
lean_ctor_set(v___x_2257_, 2, v___x_2281_);
v___x_2283_ = v___x_2257_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_key_2253_);
lean_ctor_set(v_reuseFailAlloc_2286_, 1, v_value_2254_);
lean_ctor_set(v_reuseFailAlloc_2286_, 2, v___x_2281_);
v___x_2283_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
lean_object* v___x_2284_; 
v___x_2284_ = lean_array_uset(v_x_2251_, v___x_2280_, v___x_2283_);
v_x_2251_ = v___x_2284_;
v_x_2252_ = v_tail_2255_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10_spec__11___redArg(lean_object* v_i_2288_, lean_object* v_source_2289_, lean_object* v_target_2290_){
_start:
{
lean_object* v___x_2291_; uint8_t v___x_2292_; 
v___x_2291_ = lean_array_get_size(v_source_2289_);
v___x_2292_ = lean_nat_dec_lt(v_i_2288_, v___x_2291_);
if (v___x_2292_ == 0)
{
lean_dec_ref(v_source_2289_);
lean_dec(v_i_2288_);
return v_target_2290_;
}
else
{
lean_object* v_es_2293_; lean_object* v___x_2294_; lean_object* v_source_2295_; lean_object* v_target_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
v_es_2293_ = lean_array_fget(v_source_2289_, v_i_2288_);
v___x_2294_ = lean_box(0);
v_source_2295_ = lean_array_fset(v_source_2289_, v_i_2288_, v___x_2294_);
v_target_2296_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10_spec__11_spec__12___redArg(v_target_2290_, v_es_2293_);
v___x_2297_ = lean_unsigned_to_nat(1u);
v___x_2298_ = lean_nat_add(v_i_2288_, v___x_2297_);
lean_dec(v_i_2288_);
v_i_2288_ = v___x_2298_;
v_source_2289_ = v_source_2295_;
v_target_2290_ = v_target_2296_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10___redArg(lean_object* v_data_2300_){
_start:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v_nbuckets_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2301_ = lean_array_get_size(v_data_2300_);
v___x_2302_ = lean_unsigned_to_nat(2u);
v_nbuckets_2303_ = lean_nat_mul(v___x_2301_, v___x_2302_);
v___x_2304_ = lean_unsigned_to_nat(0u);
v___x_2305_ = lean_box(0);
v___x_2306_ = lean_mk_array(v_nbuckets_2303_, v___x_2305_);
v___x_2307_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10_spec__11___redArg(v___x_2304_, v_data_2300_, v___x_2306_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7___redArg(lean_object* v_m_2308_, lean_object* v_a_2309_, lean_object* v_b_2310_){
_start:
{
lean_object* v_size_2311_; lean_object* v_buckets_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2364_; 
v_size_2311_ = lean_ctor_get(v_m_2308_, 0);
v_buckets_2312_ = lean_ctor_get(v_m_2308_, 1);
v_isSharedCheck_2364_ = !lean_is_exclusive(v_m_2308_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2314_ = v_m_2308_;
v_isShared_2315_ = v_isSharedCheck_2364_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_buckets_2312_);
lean_inc(v_size_2311_);
lean_dec(v_m_2308_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2364_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v_fst_2316_; lean_object* v_snd_2317_; lean_object* v___x_2318_; size_t v___x_2319_; size_t v___x_2320_; size_t v___x_2321_; uint64_t v___x_2322_; size_t v___x_2323_; size_t v___x_2324_; uint64_t v___x_2325_; uint64_t v___x_2326_; uint64_t v___x_2327_; uint64_t v___x_2328_; uint64_t v_fold_2329_; uint64_t v___x_2330_; uint64_t v___x_2331_; uint64_t v___x_2332_; size_t v___x_2333_; size_t v___x_2334_; size_t v___x_2335_; size_t v___x_2336_; size_t v___x_2337_; lean_object* v_bkt_2338_; uint8_t v___x_2339_; 
v_fst_2316_ = lean_ctor_get(v_a_2309_, 0);
v_snd_2317_ = lean_ctor_get(v_a_2309_, 1);
v___x_2318_ = lean_array_get_size(v_buckets_2312_);
v___x_2319_ = lean_ptr_addr(v_fst_2316_);
v___x_2320_ = ((size_t)3ULL);
v___x_2321_ = lean_usize_shift_right(v___x_2319_, v___x_2320_);
v___x_2322_ = lean_usize_to_uint64(v___x_2321_);
v___x_2323_ = lean_ptr_addr(v_snd_2317_);
v___x_2324_ = lean_usize_shift_right(v___x_2323_, v___x_2320_);
v___x_2325_ = lean_usize_to_uint64(v___x_2324_);
v___x_2326_ = lean_uint64_mix_hash(v___x_2322_, v___x_2325_);
v___x_2327_ = 32ULL;
v___x_2328_ = lean_uint64_shift_right(v___x_2326_, v___x_2327_);
v_fold_2329_ = lean_uint64_xor(v___x_2326_, v___x_2328_);
v___x_2330_ = 16ULL;
v___x_2331_ = lean_uint64_shift_right(v_fold_2329_, v___x_2330_);
v___x_2332_ = lean_uint64_xor(v_fold_2329_, v___x_2331_);
v___x_2333_ = lean_uint64_to_usize(v___x_2332_);
v___x_2334_ = lean_usize_of_nat(v___x_2318_);
v___x_2335_ = ((size_t)1ULL);
v___x_2336_ = lean_usize_sub(v___x_2334_, v___x_2335_);
v___x_2337_ = lean_usize_land(v___x_2333_, v___x_2336_);
v_bkt_2338_ = lean_array_uget_borrowed(v_buckets_2312_, v___x_2337_);
v___x_2339_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9___redArg(v_a_2309_, v_bkt_2338_);
if (v___x_2339_ == 0)
{
lean_object* v___x_2340_; lean_object* v_size_x27_2341_; lean_object* v___x_2342_; lean_object* v_buckets_x27_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; uint8_t v___x_2349_; 
v___x_2340_ = lean_unsigned_to_nat(1u);
v_size_x27_2341_ = lean_nat_add(v_size_2311_, v___x_2340_);
lean_dec(v_size_2311_);
lean_inc(v_bkt_2338_);
v___x_2342_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2342_, 0, v_a_2309_);
lean_ctor_set(v___x_2342_, 1, v_b_2310_);
lean_ctor_set(v___x_2342_, 2, v_bkt_2338_);
v_buckets_x27_2343_ = lean_array_uset(v_buckets_2312_, v___x_2337_, v___x_2342_);
v___x_2344_ = lean_unsigned_to_nat(4u);
v___x_2345_ = lean_nat_mul(v_size_x27_2341_, v___x_2344_);
v___x_2346_ = lean_unsigned_to_nat(3u);
v___x_2347_ = lean_nat_div(v___x_2345_, v___x_2346_);
lean_dec(v___x_2345_);
v___x_2348_ = lean_array_get_size(v_buckets_x27_2343_);
v___x_2349_ = lean_nat_dec_le(v___x_2347_, v___x_2348_);
lean_dec(v___x_2347_);
if (v___x_2349_ == 0)
{
lean_object* v_val_2350_; lean_object* v___x_2352_; 
v_val_2350_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10___redArg(v_buckets_x27_2343_);
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 1, v_val_2350_);
lean_ctor_set(v___x_2314_, 0, v_size_x27_2341_);
v___x_2352_ = v___x_2314_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_size_x27_2341_);
lean_ctor_set(v_reuseFailAlloc_2353_, 1, v_val_2350_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
else
{
lean_object* v___x_2355_; 
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 1, v_buckets_x27_2343_);
lean_ctor_set(v___x_2314_, 0, v_size_x27_2341_);
v___x_2355_ = v___x_2314_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_size_x27_2341_);
lean_ctor_set(v_reuseFailAlloc_2356_, 1, v_buckets_x27_2343_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
else
{
lean_object* v___x_2357_; lean_object* v_buckets_x27_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2362_; 
lean_inc(v_bkt_2338_);
v___x_2357_ = lean_box(0);
v_buckets_x27_2358_ = lean_array_uset(v_buckets_2312_, v___x_2337_, v___x_2357_);
v___x_2359_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__11___redArg(v_a_2309_, v_b_2310_, v_bkt_2338_);
v___x_2360_ = lean_array_uset(v_buckets_x27_2358_, v___x_2337_, v___x_2359_);
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 1, v___x_2360_);
v___x_2362_ = v___x_2314_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_size_2311_);
lean_ctor_set(v_reuseFailAlloc_2363_, 1, v___x_2360_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__1(void){
_start:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2366_ = ((lean_object*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__0));
v___x_2367_ = l_Lean_stringToMessageData(v___x_2366_);
return v___x_2367_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__2(void){
_start:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2368_ = lean_unsigned_to_nat(32u);
v___x_2369_ = lean_mk_empty_array_with_capacity(v___x_2368_);
v___x_2370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2369_);
return v___x_2370_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__3(void){
_start:
{
size_t v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2371_ = ((size_t)5ULL);
v___x_2372_ = lean_unsigned_to_nat(0u);
v___x_2373_ = lean_unsigned_to_nat(32u);
v___x_2374_ = lean_mk_empty_array_with_capacity(v___x_2373_);
v___x_2375_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__2);
v___x_2376_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2376_, 0, v___x_2375_);
lean_ctor_set(v___x_2376_, 1, v___x_2374_);
lean_ctor_set(v___x_2376_, 2, v___x_2372_);
lean_ctor_set(v___x_2376_, 3, v___x_2372_);
lean_ctor_set_usize(v___x_2376_, 4, v___x_2371_);
return v___x_2376_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2(void){
_start:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
v___x_2379_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__2));
v___x_2380_ = lean_unsigned_to_nat(73u);
v___x_2381_ = lean_unsigned_to_nat(213u);
v___x_2382_ = ((lean_object*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__1));
v___x_2383_ = ((lean_object*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__0));
v___x_2384_ = l_mkPanicMessageWithDecl(v___x_2383_, v___x_2382_, v___x_2381_, v___x_2380_, v___x_2379_);
return v___x_2384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit(lean_object* v_xs_2385_, lean_object* v_e_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_){
_start:
{
switch(lean_obj_tag(v_e_2386_))
{
case 0:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; 
lean_dec_ref_known(v_e_2386_, 1);
lean_dec_ref(v_xs_2385_);
v___x_2395_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2);
v___x_2396_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(v___x_2395_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_);
return v___x_2396_;
}
case 1:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; 
lean_dec_ref_known(v_e_2386_, 1);
lean_dec_ref(v_xs_2385_);
v___x_2397_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2);
v___x_2398_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(v___x_2397_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_);
return v___x_2398_;
}
case 2:
{
lean_object* v___x_2399_; lean_object* v___x_2400_; 
lean_dec_ref_known(v_e_2386_, 1);
lean_dec_ref(v_xs_2385_);
v___x_2399_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2);
v___x_2400_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(v___x_2399_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_);
return v___x_2400_;
}
case 3:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; 
lean_dec_ref_known(v_e_2386_, 1);
lean_dec_ref(v_xs_2385_);
v___x_2401_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2);
v___x_2402_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(v___x_2401_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_);
return v___x_2402_;
}
case 4:
{
lean_object* v___x_2403_; lean_object* v___x_2404_; 
lean_dec_ref_known(v_e_2386_, 2);
lean_dec_ref(v_xs_2385_);
v___x_2403_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2);
v___x_2404_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(v___x_2403_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_);
return v___x_2404_;
}
case 5:
{
lean_object* v_fn_2405_; lean_object* v_arg_2406_; lean_object* v___x_2407_; 
v_fn_2405_ = lean_ctor_get(v_e_2386_, 0);
v_arg_2406_ = lean_ctor_get(v_e_2386_, 1);
lean_inc_ref(v_fn_2405_);
lean_inc_ref(v_xs_2385_);
v___x_2407_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v_xs_2385_, v_fn_2405_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v_a_2408_; lean_object* v___x_2409_; 
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
lean_inc(v_a_2408_);
lean_dec_ref_known(v___x_2407_, 1);
lean_inc_ref(v_arg_2406_);
v___x_2409_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v_xs_2385_, v_arg_2406_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_);
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2426_; 
v_a_2410_ = lean_ctor_get(v___x_2409_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2412_ = v___x_2409_;
v_isShared_2413_ = v_isSharedCheck_2426_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2409_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2426_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
uint8_t v___y_2415_; size_t v___x_2420_; size_t v___x_2421_; uint8_t v___x_2422_; 
v___x_2420_ = lean_ptr_addr(v_fn_2405_);
v___x_2421_ = lean_ptr_addr(v_a_2408_);
v___x_2422_ = lean_usize_dec_eq(v___x_2420_, v___x_2421_);
if (v___x_2422_ == 0)
{
v___y_2415_ = v___x_2422_;
goto v___jp_2414_;
}
else
{
size_t v___x_2423_; size_t v___x_2424_; uint8_t v___x_2425_; 
v___x_2423_ = lean_ptr_addr(v_arg_2406_);
v___x_2424_ = lean_ptr_addr(v_a_2410_);
v___x_2425_ = lean_usize_dec_eq(v___x_2423_, v___x_2424_);
v___y_2415_ = v___x_2425_;
goto v___jp_2414_;
}
v___jp_2414_:
{
if (v___y_2415_ == 0)
{
lean_object* v___x_2416_; 
lean_del_object(v___x_2412_);
lean_dec_ref_known(v_e_2386_, 2);
v___x_2416_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1___redArg(v_a_2408_, v_a_2410_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_);
return v___x_2416_;
}
else
{
lean_object* v___x_2418_; 
lean_dec(v_a_2410_);
lean_dec(v_a_2408_);
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 0, v_e_2386_);
v___x_2418_ = v___x_2412_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_e_2386_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
}
}
else
{
lean_dec(v_a_2408_);
lean_dec_ref_known(v_e_2386_, 2);
return v___x_2409_;
}
}
else
{
lean_dec_ref_known(v_e_2386_, 2);
lean_dec_ref(v_xs_2385_);
return v___x_2407_;
}
}
case 8:
{
lean_object* v_declName_2427_; lean_object* v_type_2428_; lean_object* v_value_2429_; lean_object* v_body_2430_; uint8_t v_nondep_2431_; lean_object* v___x_2432_; 
v_declName_2427_ = lean_ctor_get(v_e_2386_, 0);
lean_inc(v_declName_2427_);
v_type_2428_ = lean_ctor_get(v_e_2386_, 1);
lean_inc_ref(v_type_2428_);
v_value_2429_ = lean_ctor_get(v_e_2386_, 2);
lean_inc_ref(v_value_2429_);
v_body_2430_ = lean_ctor_get(v_e_2386_, 3);
lean_inc_ref(v_body_2430_);
v_nondep_2431_ = lean_ctor_get_uint8(v_e_2386_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2386_, 4);
lean_inc_ref(v_xs_2385_);
v___x_2432_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v_xs_2385_, v_type_2428_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_);
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_object* v_a_2433_; lean_object* v___x_2434_; 
v_a_2433_ = lean_ctor_get(v___x_2432_, 0);
lean_inc(v_a_2433_);
lean_dec_ref_known(v___x_2432_, 1);
lean_inc_ref(v_xs_2385_);
v___x_2434_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v_xs_2385_, v_value_2429_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_);
if (lean_obj_tag(v___x_2434_) == 0)
{
lean_object* v_a_2435_; lean_object* v___x_2436_; 
v_a_2435_ = lean_ctor_get(v___x_2434_, 0);
lean_inc(v_a_2435_);
lean_dec_ref_known(v___x_2434_, 1);
v___x_2436_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl(v_declName_2427_, v_a_2433_, v_a_2435_, v_nondep_2431_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v_a_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; 
v_a_2437_ = lean_ctor_get(v___x_2436_, 0);
lean_inc(v_a_2437_);
lean_dec_ref_known(v___x_2436_, 1);
v___x_2438_ = l_Lean_PersistentArray_push___redArg(v_xs_2385_, v_a_2437_);
v___x_2439_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v___x_2438_, v_body_2430_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_);
return v___x_2439_;
}
else
{
lean_dec_ref(v_body_2430_);
lean_dec_ref(v_xs_2385_);
return v___x_2436_;
}
}
else
{
lean_dec(v_a_2433_);
lean_dec_ref(v_body_2430_);
lean_dec(v_declName_2427_);
lean_dec_ref(v_xs_2385_);
return v___x_2434_;
}
}
else
{
lean_dec_ref(v_body_2430_);
lean_dec_ref(v_value_2429_);
lean_dec(v_declName_2427_);
lean_dec_ref(v_xs_2385_);
return v___x_2432_;
}
}
case 9:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; 
lean_dec_ref_known(v_e_2386_, 1);
lean_dec_ref(v_xs_2385_);
v___x_2440_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2);
v___x_2441_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(v___x_2440_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_);
return v___x_2441_;
}
case 10:
{
lean_object* v_data_2442_; lean_object* v_expr_2443_; lean_object* v___x_2444_; 
v_data_2442_ = lean_ctor_get(v_e_2386_, 0);
v_expr_2443_ = lean_ctor_get(v_e_2386_, 1);
lean_inc_ref(v_expr_2443_);
v___x_2444_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v_xs_2385_, v_expr_2443_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_);
if (lean_obj_tag(v___x_2444_) == 0)
{
lean_object* v_a_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2456_; 
v_a_2445_ = lean_ctor_get(v___x_2444_, 0);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2447_ = v___x_2444_;
v_isShared_2448_ = v_isSharedCheck_2456_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_a_2445_);
lean_dec(v___x_2444_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2456_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
size_t v___x_2449_; size_t v___x_2450_; uint8_t v___x_2451_; 
v___x_2449_ = lean_ptr_addr(v_expr_2443_);
v___x_2450_ = lean_ptr_addr(v_a_2445_);
v___x_2451_ = lean_usize_dec_eq(v___x_2449_, v___x_2450_);
if (v___x_2451_ == 0)
{
lean_object* v___x_2452_; 
lean_inc(v_data_2442_);
lean_del_object(v___x_2447_);
lean_dec_ref_known(v_e_2386_, 2);
v___x_2452_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2___redArg(v_data_2442_, v_a_2445_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_);
return v___x_2452_;
}
else
{
lean_object* v___x_2454_; 
lean_dec(v_a_2445_);
if (v_isShared_2448_ == 0)
{
lean_ctor_set(v___x_2447_, 0, v_e_2386_);
v___x_2454_ = v___x_2447_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_e_2386_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2386_, 2);
return v___x_2444_;
}
}
case 11:
{
lean_object* v_typeName_2457_; lean_object* v_idx_2458_; lean_object* v_struct_2459_; lean_object* v___x_2460_; 
v_typeName_2457_ = lean_ctor_get(v_e_2386_, 0);
v_idx_2458_ = lean_ctor_get(v_e_2386_, 1);
v_struct_2459_ = lean_ctor_get(v_e_2386_, 2);
lean_inc_ref(v_struct_2459_);
v___x_2460_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v_xs_2385_, v_struct_2459_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2472_; 
v_a_2461_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2463_ = v___x_2460_;
v_isShared_2464_ = v_isSharedCheck_2472_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2460_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2472_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
size_t v___x_2465_; size_t v___x_2466_; uint8_t v___x_2467_; 
v___x_2465_ = lean_ptr_addr(v_struct_2459_);
v___x_2466_ = lean_ptr_addr(v_a_2461_);
v___x_2467_ = lean_usize_dec_eq(v___x_2465_, v___x_2466_);
if (v___x_2467_ == 0)
{
lean_object* v___x_2468_; 
lean_inc(v_idx_2458_);
lean_inc(v_typeName_2457_);
lean_del_object(v___x_2463_);
lean_dec_ref_known(v_e_2386_, 3);
v___x_2468_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3___redArg(v_typeName_2457_, v_idx_2458_, v_a_2461_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_);
return v___x_2468_;
}
else
{
lean_object* v___x_2470_; 
lean_dec(v_a_2461_);
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 0, v_e_2386_);
v___x_2470_ = v___x_2463_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_e_2386_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2386_, 3);
return v___x_2460_;
}
}
default: 
{
lean_object* v___x_2473_; 
v___x_2473_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg(v_xs_2385_, v_e_2386_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_);
return v___x_2473_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(lean_object* v_xs_2474_, lean_object* v_e_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_){
_start:
{
switch(lean_obj_tag(v_e_2475_))
{
case 0:
{
lean_object* v_deBruijnIndex_2484_; lean_object* v_size_2485_; uint8_t v___x_2486_; 
v_deBruijnIndex_2484_ = lean_ctor_get(v_e_2475_, 0);
lean_inc(v_deBruijnIndex_2484_);
lean_dec_ref_known(v_e_2475_, 1);
v_size_2485_ = lean_ctor_get(v_xs_2474_, 2);
v___x_2486_ = lean_nat_dec_lt(v_deBruijnIndex_2484_, v_size_2485_);
if (v___x_2486_ == 0)
{
lean_object* v___x_2487_; lean_object* v___x_2488_; 
lean_dec(v_deBruijnIndex_2484_);
lean_dec_ref(v_xs_2474_);
v___x_2487_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__1, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__1_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__1);
v___x_2488_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5___redArg(v___x_2487_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_);
return v___x_2488_;
}
else
{
lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2489_ = l_Lean_instInhabitedExpr;
v___x_2490_ = lean_nat_sub(v_size_2485_, v_deBruijnIndex_2484_);
lean_dec(v_deBruijnIndex_2484_);
v___x_2491_ = lean_unsigned_to_nat(1u);
v___x_2492_ = lean_nat_sub(v___x_2490_, v___x_2491_);
lean_dec(v___x_2490_);
v___x_2493_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2489_, v_xs_2474_, v___x_2492_);
lean_dec(v___x_2492_);
lean_dec_ref(v_xs_2474_);
v___x_2494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2493_);
return v___x_2494_;
}
}
case 1:
{
lean_object* v___x_2495_; 
lean_dec_ref(v_xs_2474_);
v___x_2495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2495_, 0, v_e_2475_);
return v___x_2495_;
}
case 2:
{
lean_object* v___x_2496_; 
lean_dec_ref(v_xs_2474_);
v___x_2496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2496_, 0, v_e_2475_);
return v___x_2496_;
}
case 3:
{
lean_object* v___x_2497_; 
lean_dec_ref(v_xs_2474_);
v___x_2497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2497_, 0, v_e_2475_);
return v___x_2497_;
}
case 4:
{
lean_object* v___x_2498_; 
lean_dec_ref(v_xs_2474_);
v___x_2498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2498_, 0, v_e_2475_);
return v___x_2498_;
}
case 9:
{
lean_object* v___x_2499_; 
lean_dec_ref(v_xs_2474_);
v___x_2499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2499_, 0, v_e_2475_);
return v___x_2499_;
}
default: 
{
uint8_t v___x_2500_; 
v___x_2500_ = l_Lean_Expr_hasLooseBVars(v_e_2475_);
if (v___x_2500_ == 0)
{
lean_object* v___x_2501_; 
lean_dec_ref(v_xs_2474_);
lean_inc_ref(v_e_2475_);
v___x_2501_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet(v_e_2475_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_);
if (lean_obj_tag(v___x_2501_) == 0)
{
lean_object* v_a_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2542_; 
v_a_2502_ = lean_ctor_get(v___x_2501_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2501_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2504_ = v___x_2501_;
v_isShared_2505_ = v_isSharedCheck_2542_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_a_2502_);
lean_dec(v___x_2501_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2542_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
uint8_t v___x_2506_; 
v___x_2506_ = lean_unbox(v_a_2502_);
lean_dec(v_a_2502_);
if (v___x_2506_ == 0)
{
lean_object* v___x_2508_; 
if (v_isShared_2505_ == 0)
{
lean_ctor_set(v___x_2504_, 0, v_e_2475_);
v___x_2508_ = v___x_2504_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_e_2475_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
return v___x_2508_;
}
}
else
{
lean_object* v___x_2510_; lean_object* v_cacheClosed_2511_; lean_object* v___x_2512_; 
v___x_2510_ = lean_st_ref_get(v_a_2476_);
v_cacheClosed_2511_ = lean_ctor_get(v___x_2510_, 1);
lean_inc_ref(v_cacheClosed_2511_);
lean_dec(v___x_2510_);
v___x_2512_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0___redArg(v_cacheClosed_2511_, v_e_2475_);
lean_dec_ref(v_cacheClosed_2511_);
if (lean_obj_tag(v___x_2512_) == 1)
{
lean_object* v_val_2513_; lean_object* v___x_2515_; 
lean_dec_ref(v_e_2475_);
v_val_2513_ = lean_ctor_get(v___x_2512_, 0);
lean_inc(v_val_2513_);
lean_dec_ref_known(v___x_2512_, 1);
if (v_isShared_2505_ == 0)
{
lean_ctor_set(v___x_2504_, 0, v_val_2513_);
v___x_2515_ = v___x_2504_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_val_2513_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
else
{
lean_object* v___x_2517_; lean_object* v___x_2518_; 
lean_dec(v___x_2512_);
lean_del_object(v___x_2504_);
v___x_2517_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__3, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__3_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__3);
lean_inc_ref(v_e_2475_);
v___x_2518_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit(v___x_2517_, v_e_2475_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_);
if (lean_obj_tag(v___x_2518_) == 0)
{
lean_object* v_a_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2541_; 
v_a_2519_ = lean_ctor_get(v___x_2518_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2521_ = v___x_2518_;
v_isShared_2522_ = v_isSharedCheck_2541_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_a_2519_);
lean_dec(v___x_2518_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2541_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2523_; lean_object* v_cache_2524_; lean_object* v_cacheClosed_2525_; lean_object* v_hasLetCache_2526_; lean_object* v_decls_2527_; lean_object* v_valueMap_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2540_; 
v___x_2523_ = lean_st_ref_take(v_a_2476_);
v_cache_2524_ = lean_ctor_get(v___x_2523_, 0);
v_cacheClosed_2525_ = lean_ctor_get(v___x_2523_, 1);
v_hasLetCache_2526_ = lean_ctor_get(v___x_2523_, 2);
v_decls_2527_ = lean_ctor_get(v___x_2523_, 3);
v_valueMap_2528_ = lean_ctor_get(v___x_2523_, 4);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2530_ = v___x_2523_;
v_isShared_2531_ = v_isSharedCheck_2540_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_valueMap_2528_);
lean_inc(v_decls_2527_);
lean_inc(v_hasLetCache_2526_);
lean_inc(v_cacheClosed_2525_);
lean_inc(v_cache_2524_);
lean_dec(v___x_2523_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2540_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2532_; lean_object* v___x_2534_; 
lean_inc(v_a_2519_);
v___x_2532_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1___redArg(v_cacheClosed_2525_, v_e_2475_, v_a_2519_);
if (v_isShared_2531_ == 0)
{
lean_ctor_set(v___x_2530_, 1, v___x_2532_);
v___x_2534_ = v___x_2530_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_cache_2524_);
lean_ctor_set(v_reuseFailAlloc_2539_, 1, v___x_2532_);
lean_ctor_set(v_reuseFailAlloc_2539_, 2, v_hasLetCache_2526_);
lean_ctor_set(v_reuseFailAlloc_2539_, 3, v_decls_2527_);
lean_ctor_set(v_reuseFailAlloc_2539_, 4, v_valueMap_2528_);
v___x_2534_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
lean_object* v___x_2535_; lean_object* v___x_2537_; 
v___x_2535_ = lean_st_ref_put(v_a_2476_, v___x_2534_);
if (v_isShared_2522_ == 0)
{
v___x_2537_ = v___x_2521_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_a_2519_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_2475_);
return v___x_2518_;
}
}
}
}
}
else
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2550_; 
lean_dec_ref(v_e_2475_);
v_a_2543_ = lean_ctor_get(v___x_2501_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2501_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2545_ = v___x_2501_;
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2501_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2548_; 
if (v_isShared_2546_ == 0)
{
v___x_2548_ = v___x_2545_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_a_2543_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
}
else
{
lean_object* v___x_2551_; lean_object* v_cache_2552_; lean_object* v_key_2553_; lean_object* v___x_2554_; 
v___x_2551_ = lean_st_ref_get(v_a_2476_);
v_cache_2552_ = lean_ctor_get(v___x_2551_, 0);
lean_inc_ref(v_cache_2552_);
lean_dec(v___x_2551_);
lean_inc_ref(v_e_2475_);
lean_inc_ref(v_xs_2474_);
v_key_2553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_2553_, 0, v_xs_2474_);
lean_ctor_set(v_key_2553_, 1, v_e_2475_);
v___x_2554_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6___redArg(v_cache_2552_, v_key_2553_);
lean_dec_ref(v_cache_2552_);
if (lean_obj_tag(v___x_2554_) == 1)
{
lean_object* v_val_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2562_; 
lean_dec_ref_known(v_key_2553_, 2);
lean_dec_ref(v_e_2475_);
lean_dec_ref(v_xs_2474_);
v_val_2555_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2557_ = v___x_2554_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_val_2555_);
lean_dec(v___x_2554_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2560_; 
if (v_isShared_2558_ == 0)
{
lean_ctor_set_tag(v___x_2557_, 0);
v___x_2560_ = v___x_2557_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_val_2555_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
else
{
lean_object* v___x_2563_; 
lean_dec(v___x_2554_);
v___x_2563_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit(v_xs_2474_, v_e_2475_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_);
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2586_; 
v_a_2564_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2566_ = v___x_2563_;
v_isShared_2567_ = v_isSharedCheck_2586_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v___x_2563_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2586_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2568_; lean_object* v_cache_2569_; lean_object* v_cacheClosed_2570_; lean_object* v_hasLetCache_2571_; lean_object* v_decls_2572_; lean_object* v_valueMap_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2585_; 
v___x_2568_ = lean_st_ref_take(v_a_2476_);
v_cache_2569_ = lean_ctor_get(v___x_2568_, 0);
v_cacheClosed_2570_ = lean_ctor_get(v___x_2568_, 1);
v_hasLetCache_2571_ = lean_ctor_get(v___x_2568_, 2);
v_decls_2572_ = lean_ctor_get(v___x_2568_, 3);
v_valueMap_2573_ = lean_ctor_get(v___x_2568_, 4);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2575_ = v___x_2568_;
v_isShared_2576_ = v_isSharedCheck_2585_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_valueMap_2573_);
lean_inc(v_decls_2572_);
lean_inc(v_hasLetCache_2571_);
lean_inc(v_cacheClosed_2570_);
lean_inc(v_cache_2569_);
lean_dec(v___x_2568_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2585_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2577_; lean_object* v___x_2579_; 
lean_inc(v_a_2564_);
v___x_2577_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7___redArg(v_cache_2569_, v_key_2553_, v_a_2564_);
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 0, v___x_2577_);
v___x_2579_ = v___x_2575_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v___x_2577_);
lean_ctor_set(v_reuseFailAlloc_2584_, 1, v_cacheClosed_2570_);
lean_ctor_set(v_reuseFailAlloc_2584_, 2, v_hasLetCache_2571_);
lean_ctor_set(v_reuseFailAlloc_2584_, 3, v_decls_2572_);
lean_ctor_set(v_reuseFailAlloc_2584_, 4, v_valueMap_2573_);
v___x_2579_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
lean_object* v___x_2580_; lean_object* v___x_2582_; 
v___x_2580_ = lean_st_ref_put(v_a_2476_, v___x_2579_);
if (v_isShared_2567_ == 0)
{
v___x_2582_ = v___x_2566_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_a_2564_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_2553_, 2);
return v___x_2563_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___boxed(lean_object* v_xs_2587_, lean_object* v_e_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_){
_start:
{
lean_object* v_res_2597_; 
v_res_2597_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v_xs_2587_, v_e_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_);
lean_dec(v_a_2595_);
lean_dec_ref(v_a_2594_);
lean_dec(v_a_2593_);
lean_dec_ref(v_a_2592_);
lean_dec(v_a_2591_);
lean_dec_ref(v_a_2590_);
lean_dec(v_a_2589_);
return v_res_2597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___boxed(lean_object* v_xs_2598_, lean_object* v_e_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_){
_start:
{
lean_object* v_res_2608_; 
v_res_2608_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit(v_xs_2598_, v_e_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_);
lean_dec(v_a_2606_);
lean_dec_ref(v_a_2605_);
lean_dec(v_a_2604_);
lean_dec_ref(v_a_2603_);
lean_dec(v_a_2602_);
lean_dec_ref(v_a_2601_);
lean_dec(v_a_2600_);
return v_res_2608_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5(lean_object* v_00_u03b1_2609_, lean_object* v_msg_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_){
_start:
{
lean_object* v___x_2619_; 
v___x_2619_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5___redArg(v_msg_2610_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_);
return v___x_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5___boxed(lean_object* v_00_u03b1_2620_, lean_object* v_msg_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_){
_start:
{
lean_object* v_res_2630_; 
v_res_2630_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5(v_00_u03b1_2620_, v_msg_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
lean_dec(v___y_2622_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6(lean_object* v_00_u03b2_2631_, lean_object* v_m_2632_, lean_object* v_a_2633_){
_start:
{
lean_object* v___x_2634_; 
v___x_2634_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6___redArg(v_m_2632_, v_a_2633_);
return v___x_2634_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6___boxed(lean_object* v_00_u03b2_2635_, lean_object* v_m_2636_, lean_object* v_a_2637_){
_start:
{
lean_object* v_res_2638_; 
v_res_2638_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6(v_00_u03b2_2635_, v_m_2636_, v_a_2637_);
lean_dec_ref(v_a_2637_);
lean_dec_ref(v_m_2636_);
return v_res_2638_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7(lean_object* v_00_u03b2_2639_, lean_object* v_m_2640_, lean_object* v_a_2641_, lean_object* v_b_2642_){
_start:
{
lean_object* v___x_2643_; 
v___x_2643_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7___redArg(v_m_2640_, v_a_2641_, v_b_2642_);
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7(lean_object* v_00_u03b2_2644_, lean_object* v_a_2645_, lean_object* v_x_2646_){
_start:
{
lean_object* v___x_2647_; 
v___x_2647_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7___redArg(v_a_2645_, v_x_2646_);
return v___x_2647_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7___boxed(lean_object* v_00_u03b2_2648_, lean_object* v_a_2649_, lean_object* v_x_2650_){
_start:
{
lean_object* v_res_2651_; 
v_res_2651_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7(v_00_u03b2_2648_, v_a_2649_, v_x_2650_);
lean_dec(v_x_2650_);
lean_dec_ref(v_a_2649_);
return v_res_2651_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9(lean_object* v_00_u03b2_2652_, lean_object* v_a_2653_, lean_object* v_x_2654_){
_start:
{
uint8_t v___x_2655_; 
v___x_2655_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9___redArg(v_a_2653_, v_x_2654_);
return v___x_2655_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9___boxed(lean_object* v_00_u03b2_2656_, lean_object* v_a_2657_, lean_object* v_x_2658_){
_start:
{
uint8_t v_res_2659_; lean_object* v_r_2660_; 
v_res_2659_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9(v_00_u03b2_2656_, v_a_2657_, v_x_2658_);
lean_dec(v_x_2658_);
lean_dec_ref(v_a_2657_);
v_r_2660_ = lean_box(v_res_2659_);
return v_r_2660_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10(lean_object* v_00_u03b2_2661_, lean_object* v_data_2662_){
_start:
{
lean_object* v___x_2663_; 
v___x_2663_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10___redArg(v_data_2662_);
return v___x_2663_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__11(lean_object* v_00_u03b2_2664_, lean_object* v_a_2665_, lean_object* v_b_2666_, lean_object* v_x_2667_){
_start:
{
lean_object* v___x_2668_; 
v___x_2668_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__11___redArg(v_a_2665_, v_b_2666_, v_x_2667_);
return v___x_2668_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10_spec__11(lean_object* v_00_u03b2_2669_, lean_object* v_i_2670_, lean_object* v_source_2671_, lean_object* v_target_2672_){
_start:
{
lean_object* v___x_2673_; 
v___x_2673_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10_spec__11___redArg(v_i_2670_, v_source_2671_, v_target_2672_);
return v___x_2673_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10_spec__11_spec__12(lean_object* v_00_u03b2_2674_, lean_object* v_x_2675_, lean_object* v_x_2676_){
_start:
{
lean_object* v___x_2677_; 
v___x_2677_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10_spec__11_spec__12___redArg(v_x_2675_, v_x_2676_);
return v___x_2677_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3(lean_object* v_msg_2680_, uint8_t v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_){
_start:
{
lean_object* v___f_2684_; lean_object* v___f_2685_; lean_object* v___x_2686_; lean_object* v___f_2687_; lean_object* v___f_2688_; lean_object* v___f_2689_; lean_object* v___x_12295__overap_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v___f_2684_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3___closed__0));
v___f_2685_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3___closed__1));
v___x_2686_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___f_2684_, v___f_2685_);
v___f_2687_ = lean_alloc_closure((void*)(l_EStateM_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2687_, 0, v___x_2686_);
v___f_2688_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2688_, 0, v___f_2687_);
v___f_2689_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2689_, 0, v___f_2688_);
v___x_12295__overap_2690_ = lean_panic_fn_borrowed(v___f_2689_, v_msg_2680_);
lean_dec_ref(v___f_2689_);
v___x_2691_ = lean_box(v___y_2681_);
lean_inc_ref(v___y_2682_);
v___x_2692_ = lean_apply_3(v___x_12295__overap_2690_, v___x_2691_, v___y_2682_, v___y_2683_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3___boxed(lean_object* v_msg_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_){
_start:
{
uint8_t v___y_17265__boxed_2697_; lean_object* v_res_2698_; 
v___y_17265__boxed_2697_ = lean_unbox(v___y_2694_);
v_res_2698_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3(v_msg_2693_, v___y_17265__boxed_2697_, v___y_2695_, v___y_2696_);
lean_dec_ref(v___y_2695_);
return v_res_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4___redArg(lean_object* v_idx_2699_, lean_object* v___y_2700_){
_start:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2701_ = l_Lean_Expr_bvar___override(v_idx_2699_);
v___x_2702_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_2701_, v___y_2700_);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4(lean_object* v_idx_2703_, uint8_t v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_){
_start:
{
lean_object* v___x_2707_; 
v___x_2707_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4___redArg(v_idx_2703_, v___y_2706_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4___boxed(lean_object* v_idx_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_){
_start:
{
uint8_t v___y_17298__boxed_2712_; lean_object* v_res_2713_; 
v___y_17298__boxed_2712_ = lean_unbox(v___y_2709_);
v_res_2713_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4(v_idx_2708_, v___y_17298__boxed_2712_, v___y_2710_, v___y_2711_);
lean_dec_ref(v___y_2710_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6___redArg(lean_object* v_x_2714_, lean_object* v_t_2715_, lean_object* v_v_2716_, lean_object* v_b_2717_, uint8_t v_nondep_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v___y_2727_; lean_object* v___x_2730_; uint8_t v_debug_2731_; 
v___x_2730_ = lean_st_ref_get(v___y_2720_);
v_debug_2731_ = lean_ctor_get_uint8(v___x_2730_, sizeof(void*)*11);
lean_dec(v___x_2730_);
if (v_debug_2731_ == 0)
{
v___y_2727_ = v___y_2720_;
goto v___jp_2726_;
}
else
{
lean_object* v___x_2732_; 
v___x_2732_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_2715_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
if (lean_obj_tag(v___x_2732_) == 0)
{
lean_object* v___x_2733_; 
lean_dec_ref_known(v___x_2732_, 1);
v___x_2733_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_v_2716_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
if (lean_obj_tag(v___x_2733_) == 0)
{
lean_object* v___x_2734_; 
lean_dec_ref_known(v___x_2733_, 1);
v___x_2734_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_2717_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_dec_ref_known(v___x_2734_, 1);
v___y_2727_ = v___y_2720_;
goto v___jp_2726_;
}
else
{
lean_object* v_a_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2742_; 
lean_dec_ref(v_b_2717_);
lean_dec_ref(v_v_2716_);
lean_dec_ref(v_t_2715_);
lean_dec(v_x_2714_);
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2737_ = v___x_2734_;
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_a_2735_);
lean_dec(v___x_2734_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2740_; 
if (v_isShared_2738_ == 0)
{
v___x_2740_ = v___x_2737_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_a_2735_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
}
}
else
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2750_; 
lean_dec_ref(v_b_2717_);
lean_dec_ref(v_v_2716_);
lean_dec_ref(v_t_2715_);
lean_dec(v_x_2714_);
v_a_2743_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2745_ = v___x_2733_;
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2733_);
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
lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2758_; 
lean_dec_ref(v_b_2717_);
lean_dec_ref(v_v_2716_);
lean_dec_ref(v_t_2715_);
lean_dec(v_x_2714_);
v_a_2751_ = lean_ctor_get(v___x_2732_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2732_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2753_ = v___x_2732_;
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2732_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2756_; 
if (v_isShared_2754_ == 0)
{
v___x_2756_ = v___x_2753_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_a_2751_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
}
}
v___jp_2726_:
{
lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2728_ = l_Lean_Expr_letE___override(v_x_2714_, v_t_2715_, v_v_2716_, v_b_2717_, v_nondep_2718_);
v___x_2729_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2728_, v___y_2727_);
return v___x_2729_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6___redArg___boxed(lean_object* v_x_2759_, lean_object* v_t_2760_, lean_object* v_v_2761_, lean_object* v_b_2762_, lean_object* v_nondep_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_){
_start:
{
uint8_t v_nondep_boxed_2771_; lean_object* v_res_2772_; 
v_nondep_boxed_2771_ = lean_unbox(v_nondep_2763_);
v_res_2772_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6___redArg(v_x_2759_, v_t_2760_, v_v_2761_, v_b_2762_, v_nondep_boxed_2771_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_);
lean_dec(v___y_2769_);
lean_dec_ref(v___y_2768_);
lean_dec(v___y_2767_);
lean_dec_ref(v___y_2766_);
lean_dec(v___y_2765_);
lean_dec_ref(v___y_2764_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6(lean_object* v_x_2773_, lean_object* v_t_2774_, lean_object* v_v_2775_, lean_object* v_b_2776_, uint8_t v_nondep_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_){
_start:
{
lean_object* v___x_2786_; 
v___x_2786_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6___redArg(v_x_2773_, v_t_2774_, v_v_2775_, v_b_2776_, v_nondep_2777_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6___boxed(lean_object* v_x_2787_, lean_object* v_t_2788_, lean_object* v_v_2789_, lean_object* v_b_2790_, lean_object* v_nondep_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_){
_start:
{
uint8_t v_nondep_boxed_2800_; lean_object* v_res_2801_; 
v_nondep_boxed_2800_ = lean_unbox(v_nondep_2791_);
v_res_2801_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6(v_x_2787_, v_t_2788_, v_v_2789_, v_b_2790_, v_nondep_boxed_2800_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec(v___y_2792_);
return v_res_2801_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2_spec__5___redArg(lean_object* v_a_2802_, lean_object* v_x_2803_){
_start:
{
if (lean_obj_tag(v_x_2803_) == 0)
{
lean_object* v___x_2804_; 
v___x_2804_ = lean_box(0);
return v___x_2804_;
}
else
{
lean_object* v_key_2805_; lean_object* v_value_2806_; lean_object* v_tail_2807_; uint8_t v___x_2808_; 
v_key_2805_ = lean_ctor_get(v_x_2803_, 0);
v_value_2806_ = lean_ctor_get(v_x_2803_, 1);
v_tail_2807_ = lean_ctor_get(v_x_2803_, 2);
v___x_2808_ = l_Lean_instBEqFVarId_beq(v_key_2805_, v_a_2802_);
if (v___x_2808_ == 0)
{
v_x_2803_ = v_tail_2807_;
goto _start;
}
else
{
lean_object* v___x_2810_; 
lean_inc(v_value_2806_);
v___x_2810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2810_, 0, v_value_2806_);
return v___x_2810_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2_spec__5___redArg___boxed(lean_object* v_a_2811_, lean_object* v_x_2812_){
_start:
{
lean_object* v_res_2813_; 
v_res_2813_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2_spec__5___redArg(v_a_2811_, v_x_2812_);
lean_dec(v_x_2812_);
lean_dec(v_a_2811_);
return v_res_2813_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___redArg(lean_object* v_m_2814_, lean_object* v_a_2815_){
_start:
{
lean_object* v_buckets_2816_; lean_object* v___x_2817_; uint64_t v___x_2818_; uint64_t v___x_2819_; uint64_t v___x_2820_; uint64_t v_fold_2821_; uint64_t v___x_2822_; uint64_t v___x_2823_; uint64_t v___x_2824_; size_t v___x_2825_; size_t v___x_2826_; size_t v___x_2827_; size_t v___x_2828_; size_t v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
v_buckets_2816_ = lean_ctor_get(v_m_2814_, 1);
v___x_2817_ = lean_array_get_size(v_buckets_2816_);
v___x_2818_ = l_Lean_instHashableFVarId_hash(v_a_2815_);
v___x_2819_ = 32ULL;
v___x_2820_ = lean_uint64_shift_right(v___x_2818_, v___x_2819_);
v_fold_2821_ = lean_uint64_xor(v___x_2818_, v___x_2820_);
v___x_2822_ = 16ULL;
v___x_2823_ = lean_uint64_shift_right(v_fold_2821_, v___x_2822_);
v___x_2824_ = lean_uint64_xor(v_fold_2821_, v___x_2823_);
v___x_2825_ = lean_uint64_to_usize(v___x_2824_);
v___x_2826_ = lean_usize_of_nat(v___x_2817_);
v___x_2827_ = ((size_t)1ULL);
v___x_2828_ = lean_usize_sub(v___x_2826_, v___x_2827_);
v___x_2829_ = lean_usize_land(v___x_2825_, v___x_2828_);
v___x_2830_ = lean_array_uget_borrowed(v_buckets_2816_, v___x_2829_);
v___x_2831_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2_spec__5___redArg(v_a_2815_, v___x_2830_);
return v___x_2831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___redArg___boxed(lean_object* v_m_2832_, lean_object* v_a_2833_){
_start:
{
lean_object* v_res_2834_; 
v_res_2834_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___redArg(v_m_2832_, v_a_2833_);
lean_dec(v_a_2833_);
lean_dec_ref(v_m_2832_);
return v_res_2834_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2(void){
_start:
{
lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; 
v___x_2837_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__1));
v___x_2838_ = lean_unsigned_to_nat(10u);
v___x_2839_ = lean_unsigned_to_nat(236u);
v___x_2840_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__0));
v___x_2841_ = ((lean_object*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__0));
v___x_2842_ = l_mkPanicMessageWithDecl(v___x_2841_, v___x_2840_, v___x_2839_, v___x_2838_, v___x_2837_);
return v___x_2842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5(lean_object* v___x_2843_, lean_object* v_i_2844_, lean_object* v___x_2845_, lean_object* v_e_2846_, lean_object* v_offset_2847_, lean_object* v_a_2848_, uint8_t v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_){
_start:
{
switch(lean_obj_tag(v_e_2846_))
{
case 5:
{
lean_object* v_fn_2852_; lean_object* v_arg_2853_; lean_object* v___x_2854_; 
v_fn_2852_ = lean_ctor_get(v_e_2846_, 0);
v_arg_2853_ = lean_ctor_get(v_e_2846_, 1);
lean_inc(v_offset_2847_);
lean_inc_ref(v_fn_2852_);
v___x_2854_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2843_, v_i_2844_, v___x_2845_, v_fn_2852_, v_offset_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2855_; lean_object* v_a_2856_; lean_object* v_fst_2857_; lean_object* v_snd_2858_; lean_object* v___x_2859_; 
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
lean_inc(v_a_2855_);
v_a_2856_ = lean_ctor_get(v___x_2854_, 1);
lean_inc(v_a_2856_);
lean_dec_ref_known(v___x_2854_, 2);
v_fst_2857_ = lean_ctor_get(v_a_2855_, 0);
lean_inc(v_fst_2857_);
v_snd_2858_ = lean_ctor_get(v_a_2855_, 1);
lean_inc(v_snd_2858_);
lean_dec(v_a_2855_);
lean_inc_ref(v_arg_2853_);
v___x_2859_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2843_, v_i_2844_, v___x_2845_, v_arg_2853_, v_offset_2847_, v_snd_2858_, v_a_2849_, v_a_2850_, v_a_2856_);
if (lean_obj_tag(v___x_2859_) == 0)
{
lean_object* v_a_2860_; lean_object* v_a_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2886_; 
v_a_2860_ = lean_ctor_get(v___x_2859_, 0);
v_a_2861_ = lean_ctor_get(v___x_2859_, 1);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2863_ = v___x_2859_;
v_isShared_2864_ = v_isSharedCheck_2886_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_a_2861_);
lean_inc(v_a_2860_);
lean_dec(v___x_2859_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2886_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v_fst_2865_; lean_object* v_snd_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2885_; 
v_fst_2865_ = lean_ctor_get(v_a_2860_, 0);
v_snd_2866_ = lean_ctor_get(v_a_2860_, 1);
v_isSharedCheck_2885_ = !lean_is_exclusive(v_a_2860_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2868_ = v_a_2860_;
v_isShared_2869_ = v_isSharedCheck_2885_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_snd_2866_);
lean_inc(v_fst_2865_);
lean_dec(v_a_2860_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2885_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
uint8_t v___y_2871_; size_t v___x_2879_; size_t v___x_2880_; uint8_t v___x_2881_; 
v___x_2879_ = lean_ptr_addr(v_fn_2852_);
v___x_2880_ = lean_ptr_addr(v_fst_2857_);
v___x_2881_ = lean_usize_dec_eq(v___x_2879_, v___x_2880_);
if (v___x_2881_ == 0)
{
v___y_2871_ = v___x_2881_;
goto v___jp_2870_;
}
else
{
size_t v___x_2882_; size_t v___x_2883_; uint8_t v___x_2884_; 
v___x_2882_ = lean_ptr_addr(v_arg_2853_);
v___x_2883_ = lean_ptr_addr(v_fst_2865_);
v___x_2884_ = lean_usize_dec_eq(v___x_2882_, v___x_2883_);
v___y_2871_ = v___x_2884_;
goto v___jp_2870_;
}
v___jp_2870_:
{
if (v___y_2871_ == 0)
{
lean_object* v___x_2872_; 
lean_del_object(v___x_2868_);
lean_del_object(v___x_2863_);
lean_dec_ref_known(v_e_2846_, 2);
v___x_2872_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__1(v_fst_2857_, v_fst_2865_, v_snd_2866_, v_a_2849_, v_a_2850_, v_a_2861_);
return v___x_2872_;
}
else
{
lean_object* v___x_2874_; 
lean_dec(v_fst_2865_);
lean_dec(v_fst_2857_);
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 0, v_e_2846_);
v___x_2874_ = v___x_2868_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_e_2846_);
lean_ctor_set(v_reuseFailAlloc_2878_, 1, v_snd_2866_);
v___x_2874_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
lean_object* v___x_2876_; 
if (v_isShared_2864_ == 0)
{
lean_ctor_set(v___x_2863_, 0, v___x_2874_);
v___x_2876_ = v___x_2863_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v___x_2874_);
lean_ctor_set(v_reuseFailAlloc_2877_, 1, v_a_2861_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_2857_);
lean_dec_ref_known(v_e_2846_, 2);
return v___x_2859_;
}
}
else
{
lean_dec_ref_known(v_e_2846_, 2);
lean_dec(v_offset_2847_);
return v___x_2854_;
}
}
case 6:
{
lean_object* v_binderName_2887_; lean_object* v_binderType_2888_; lean_object* v_body_2889_; uint8_t v_binderInfo_2890_; lean_object* v___x_2891_; 
v_binderName_2887_ = lean_ctor_get(v_e_2846_, 0);
v_binderType_2888_ = lean_ctor_get(v_e_2846_, 1);
v_body_2889_ = lean_ctor_get(v_e_2846_, 2);
v_binderInfo_2890_ = lean_ctor_get_uint8(v_e_2846_, sizeof(void*)*3 + 8);
lean_inc(v_offset_2847_);
lean_inc_ref(v_binderType_2888_);
v___x_2891_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2843_, v_i_2844_, v___x_2845_, v_binderType_2888_, v_offset_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v_a_2892_; lean_object* v_a_2893_; lean_object* v_fst_2894_; lean_object* v_snd_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
lean_inc(v_a_2892_);
v_a_2893_ = lean_ctor_get(v___x_2891_, 1);
lean_inc(v_a_2893_);
lean_dec_ref_known(v___x_2891_, 2);
v_fst_2894_ = lean_ctor_get(v_a_2892_, 0);
lean_inc(v_fst_2894_);
v_snd_2895_ = lean_ctor_get(v_a_2892_, 1);
lean_inc(v_snd_2895_);
lean_dec(v_a_2892_);
v___x_2896_ = lean_unsigned_to_nat(1u);
v___x_2897_ = lean_nat_add(v_offset_2847_, v___x_2896_);
lean_dec(v_offset_2847_);
lean_inc_ref(v_body_2889_);
v___x_2898_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2843_, v_i_2844_, v___x_2845_, v_body_2889_, v___x_2897_, v_snd_2895_, v_a_2849_, v_a_2850_, v_a_2893_);
if (lean_obj_tag(v___x_2898_) == 0)
{
lean_object* v_a_2899_; lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2925_; 
v_a_2899_ = lean_ctor_get(v___x_2898_, 0);
v_a_2900_ = lean_ctor_get(v___x_2898_, 1);
v_isSharedCheck_2925_ = !lean_is_exclusive(v___x_2898_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2902_ = v___x_2898_;
v_isShared_2903_ = v_isSharedCheck_2925_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_inc(v_a_2899_);
lean_dec(v___x_2898_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2925_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v_fst_2904_; lean_object* v_snd_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2924_; 
v_fst_2904_ = lean_ctor_get(v_a_2899_, 0);
v_snd_2905_ = lean_ctor_get(v_a_2899_, 1);
v_isSharedCheck_2924_ = !lean_is_exclusive(v_a_2899_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2907_ = v_a_2899_;
v_isShared_2908_ = v_isSharedCheck_2924_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_snd_2905_);
lean_inc(v_fst_2904_);
lean_dec(v_a_2899_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2924_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
uint8_t v___y_2910_; size_t v___x_2918_; size_t v___x_2919_; uint8_t v___x_2920_; 
v___x_2918_ = lean_ptr_addr(v_binderType_2888_);
v___x_2919_ = lean_ptr_addr(v_fst_2894_);
v___x_2920_ = lean_usize_dec_eq(v___x_2918_, v___x_2919_);
if (v___x_2920_ == 0)
{
v___y_2910_ = v___x_2920_;
goto v___jp_2909_;
}
else
{
size_t v___x_2921_; size_t v___x_2922_; uint8_t v___x_2923_; 
v___x_2921_ = lean_ptr_addr(v_body_2889_);
v___x_2922_ = lean_ptr_addr(v_fst_2904_);
v___x_2923_ = lean_usize_dec_eq(v___x_2921_, v___x_2922_);
v___y_2910_ = v___x_2923_;
goto v___jp_2909_;
}
v___jp_2909_:
{
if (v___y_2910_ == 0)
{
lean_object* v___x_2911_; 
lean_inc(v_binderName_2887_);
lean_del_object(v___x_2907_);
lean_del_object(v___x_2902_);
lean_dec_ref_known(v_e_2846_, 3);
v___x_2911_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__2(v_binderName_2887_, v_binderInfo_2890_, v_fst_2894_, v_fst_2904_, v_snd_2905_, v_a_2849_, v_a_2850_, v_a_2900_);
return v___x_2911_;
}
else
{
lean_object* v___x_2913_; 
lean_dec(v_fst_2904_);
lean_dec(v_fst_2894_);
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 0, v_e_2846_);
v___x_2913_ = v___x_2907_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_e_2846_);
lean_ctor_set(v_reuseFailAlloc_2917_, 1, v_snd_2905_);
v___x_2913_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
lean_object* v___x_2915_; 
if (v_isShared_2903_ == 0)
{
lean_ctor_set(v___x_2902_, 0, v___x_2913_);
v___x_2915_ = v___x_2902_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v___x_2913_);
lean_ctor_set(v_reuseFailAlloc_2916_, 1, v_a_2900_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
return v___x_2915_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_2894_);
lean_dec_ref_known(v_e_2846_, 3);
return v___x_2898_;
}
}
else
{
lean_dec_ref_known(v_e_2846_, 3);
lean_dec(v_offset_2847_);
return v___x_2891_;
}
}
case 7:
{
lean_object* v_binderName_2926_; lean_object* v_binderType_2927_; lean_object* v_body_2928_; uint8_t v_binderInfo_2929_; lean_object* v___x_2930_; 
v_binderName_2926_ = lean_ctor_get(v_e_2846_, 0);
v_binderType_2927_ = lean_ctor_get(v_e_2846_, 1);
v_body_2928_ = lean_ctor_get(v_e_2846_, 2);
v_binderInfo_2929_ = lean_ctor_get_uint8(v_e_2846_, sizeof(void*)*3 + 8);
lean_inc(v_offset_2847_);
lean_inc_ref(v_binderType_2927_);
v___x_2930_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2843_, v_i_2844_, v___x_2845_, v_binderType_2927_, v_offset_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_);
if (lean_obj_tag(v___x_2930_) == 0)
{
lean_object* v_a_2931_; lean_object* v_a_2932_; lean_object* v_fst_2933_; lean_object* v_snd_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; 
v_a_2931_ = lean_ctor_get(v___x_2930_, 0);
lean_inc(v_a_2931_);
v_a_2932_ = lean_ctor_get(v___x_2930_, 1);
lean_inc(v_a_2932_);
lean_dec_ref_known(v___x_2930_, 2);
v_fst_2933_ = lean_ctor_get(v_a_2931_, 0);
lean_inc(v_fst_2933_);
v_snd_2934_ = lean_ctor_get(v_a_2931_, 1);
lean_inc(v_snd_2934_);
lean_dec(v_a_2931_);
v___x_2935_ = lean_unsigned_to_nat(1u);
v___x_2936_ = lean_nat_add(v_offset_2847_, v___x_2935_);
lean_dec(v_offset_2847_);
lean_inc_ref(v_body_2928_);
v___x_2937_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2843_, v_i_2844_, v___x_2845_, v_body_2928_, v___x_2936_, v_snd_2934_, v_a_2849_, v_a_2850_, v_a_2932_);
if (lean_obj_tag(v___x_2937_) == 0)
{
lean_object* v_a_2938_; lean_object* v_a_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2964_; 
v_a_2938_ = lean_ctor_get(v___x_2937_, 0);
v_a_2939_ = lean_ctor_get(v___x_2937_, 1);
v_isSharedCheck_2964_ = !lean_is_exclusive(v___x_2937_);
if (v_isSharedCheck_2964_ == 0)
{
v___x_2941_ = v___x_2937_;
v_isShared_2942_ = v_isSharedCheck_2964_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_a_2939_);
lean_inc(v_a_2938_);
lean_dec(v___x_2937_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2964_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v_fst_2943_; lean_object* v_snd_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2963_; 
v_fst_2943_ = lean_ctor_get(v_a_2938_, 0);
v_snd_2944_ = lean_ctor_get(v_a_2938_, 1);
v_isSharedCheck_2963_ = !lean_is_exclusive(v_a_2938_);
if (v_isSharedCheck_2963_ == 0)
{
v___x_2946_ = v_a_2938_;
v_isShared_2947_ = v_isSharedCheck_2963_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_snd_2944_);
lean_inc(v_fst_2943_);
lean_dec(v_a_2938_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2963_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
uint8_t v___y_2949_; size_t v___x_2957_; size_t v___x_2958_; uint8_t v___x_2959_; 
v___x_2957_ = lean_ptr_addr(v_binderType_2927_);
v___x_2958_ = lean_ptr_addr(v_fst_2933_);
v___x_2959_ = lean_usize_dec_eq(v___x_2957_, v___x_2958_);
if (v___x_2959_ == 0)
{
v___y_2949_ = v___x_2959_;
goto v___jp_2948_;
}
else
{
size_t v___x_2960_; size_t v___x_2961_; uint8_t v___x_2962_; 
v___x_2960_ = lean_ptr_addr(v_body_2928_);
v___x_2961_ = lean_ptr_addr(v_fst_2943_);
v___x_2962_ = lean_usize_dec_eq(v___x_2960_, v___x_2961_);
v___y_2949_ = v___x_2962_;
goto v___jp_2948_;
}
v___jp_2948_:
{
if (v___y_2949_ == 0)
{
lean_object* v___x_2950_; 
lean_inc(v_binderName_2926_);
lean_del_object(v___x_2946_);
lean_del_object(v___x_2941_);
lean_dec_ref_known(v_e_2846_, 3);
v___x_2950_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__3(v_binderName_2926_, v_binderInfo_2929_, v_fst_2933_, v_fst_2943_, v_snd_2944_, v_a_2849_, v_a_2850_, v_a_2939_);
return v___x_2950_;
}
else
{
lean_object* v___x_2952_; 
lean_dec(v_fst_2943_);
lean_dec(v_fst_2933_);
if (v_isShared_2947_ == 0)
{
lean_ctor_set(v___x_2946_, 0, v_e_2846_);
v___x_2952_ = v___x_2946_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v_e_2846_);
lean_ctor_set(v_reuseFailAlloc_2956_, 1, v_snd_2944_);
v___x_2952_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
lean_object* v___x_2954_; 
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 0, v___x_2952_);
v___x_2954_ = v___x_2941_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v___x_2952_);
lean_ctor_set(v_reuseFailAlloc_2955_, 1, v_a_2939_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
return v___x_2954_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_2933_);
lean_dec_ref_known(v_e_2846_, 3);
return v___x_2937_;
}
}
else
{
lean_dec_ref_known(v_e_2846_, 3);
lean_dec(v_offset_2847_);
return v___x_2930_;
}
}
case 8:
{
lean_object* v_declName_2965_; lean_object* v_type_2966_; lean_object* v_value_2967_; lean_object* v_body_2968_; uint8_t v_nondep_2969_; lean_object* v___x_2970_; 
v_declName_2965_ = lean_ctor_get(v_e_2846_, 0);
v_type_2966_ = lean_ctor_get(v_e_2846_, 1);
v_value_2967_ = lean_ctor_get(v_e_2846_, 2);
v_body_2968_ = lean_ctor_get(v_e_2846_, 3);
v_nondep_2969_ = lean_ctor_get_uint8(v_e_2846_, sizeof(void*)*4 + 8);
lean_inc(v_offset_2847_);
lean_inc_ref(v_type_2966_);
v___x_2970_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2843_, v_i_2844_, v___x_2845_, v_type_2966_, v_offset_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_);
if (lean_obj_tag(v___x_2970_) == 0)
{
lean_object* v_a_2971_; lean_object* v_a_2972_; lean_object* v_fst_2973_; lean_object* v_snd_2974_; lean_object* v___x_2975_; 
v_a_2971_ = lean_ctor_get(v___x_2970_, 0);
lean_inc(v_a_2971_);
v_a_2972_ = lean_ctor_get(v___x_2970_, 1);
lean_inc(v_a_2972_);
lean_dec_ref_known(v___x_2970_, 2);
v_fst_2973_ = lean_ctor_get(v_a_2971_, 0);
lean_inc(v_fst_2973_);
v_snd_2974_ = lean_ctor_get(v_a_2971_, 1);
lean_inc(v_snd_2974_);
lean_dec(v_a_2971_);
lean_inc(v_offset_2847_);
lean_inc_ref(v_value_2967_);
v___x_2975_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2843_, v_i_2844_, v___x_2845_, v_value_2967_, v_offset_2847_, v_snd_2974_, v_a_2849_, v_a_2850_, v_a_2972_);
if (lean_obj_tag(v___x_2975_) == 0)
{
lean_object* v_a_2976_; lean_object* v_a_2977_; lean_object* v_fst_2978_; lean_object* v_snd_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
v_a_2976_ = lean_ctor_get(v___x_2975_, 0);
lean_inc(v_a_2976_);
v_a_2977_ = lean_ctor_get(v___x_2975_, 1);
lean_inc(v_a_2977_);
lean_dec_ref_known(v___x_2975_, 2);
v_fst_2978_ = lean_ctor_get(v_a_2976_, 0);
lean_inc(v_fst_2978_);
v_snd_2979_ = lean_ctor_get(v_a_2976_, 1);
lean_inc(v_snd_2979_);
lean_dec(v_a_2976_);
v___x_2980_ = lean_unsigned_to_nat(1u);
v___x_2981_ = lean_nat_add(v_offset_2847_, v___x_2980_);
lean_dec(v_offset_2847_);
lean_inc_ref(v_body_2968_);
v___x_2982_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2843_, v_i_2844_, v___x_2845_, v_body_2968_, v___x_2981_, v_snd_2979_, v_a_2849_, v_a_2850_, v_a_2977_);
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v_a_2983_; lean_object* v_a_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_3013_; 
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
v_a_2984_ = lean_ctor_get(v___x_2982_, 1);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_2986_ = v___x_2982_;
v_isShared_2987_ = v_isSharedCheck_3013_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_a_2984_);
lean_inc(v_a_2983_);
lean_dec(v___x_2982_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_3013_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v_fst_2988_; lean_object* v_snd_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_3012_; 
v_fst_2988_ = lean_ctor_get(v_a_2983_, 0);
v_snd_2989_ = lean_ctor_get(v_a_2983_, 1);
v_isSharedCheck_3012_ = !lean_is_exclusive(v_a_2983_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_2991_ = v_a_2983_;
v_isShared_2992_ = v_isSharedCheck_3012_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_snd_2989_);
lean_inc(v_fst_2988_);
lean_dec(v_a_2983_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_3012_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
uint8_t v___y_2994_; size_t v___x_3006_; size_t v___x_3007_; uint8_t v___x_3008_; 
v___x_3006_ = lean_ptr_addr(v_type_2966_);
v___x_3007_ = lean_ptr_addr(v_fst_2973_);
v___x_3008_ = lean_usize_dec_eq(v___x_3006_, v___x_3007_);
if (v___x_3008_ == 0)
{
v___y_2994_ = v___x_3008_;
goto v___jp_2993_;
}
else
{
size_t v___x_3009_; size_t v___x_3010_; uint8_t v___x_3011_; 
v___x_3009_ = lean_ptr_addr(v_value_2967_);
v___x_3010_ = lean_ptr_addr(v_fst_2978_);
v___x_3011_ = lean_usize_dec_eq(v___x_3009_, v___x_3010_);
v___y_2994_ = v___x_3011_;
goto v___jp_2993_;
}
v___jp_2993_:
{
if (v___y_2994_ == 0)
{
lean_object* v___x_2995_; 
lean_inc(v_declName_2965_);
lean_del_object(v___x_2991_);
lean_del_object(v___x_2986_);
lean_dec_ref_known(v_e_2846_, 4);
v___x_2995_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4(v_declName_2965_, v_fst_2973_, v_fst_2978_, v_fst_2988_, v_nondep_2969_, v_snd_2989_, v_a_2849_, v_a_2850_, v_a_2984_);
return v___x_2995_;
}
else
{
size_t v___x_2996_; size_t v___x_2997_; uint8_t v___x_2998_; 
v___x_2996_ = lean_ptr_addr(v_body_2968_);
v___x_2997_ = lean_ptr_addr(v_fst_2988_);
v___x_2998_ = lean_usize_dec_eq(v___x_2996_, v___x_2997_);
if (v___x_2998_ == 0)
{
lean_object* v___x_2999_; 
lean_inc(v_declName_2965_);
lean_del_object(v___x_2991_);
lean_del_object(v___x_2986_);
lean_dec_ref_known(v_e_2846_, 4);
v___x_2999_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4(v_declName_2965_, v_fst_2973_, v_fst_2978_, v_fst_2988_, v_nondep_2969_, v_snd_2989_, v_a_2849_, v_a_2850_, v_a_2984_);
return v___x_2999_;
}
else
{
lean_object* v___x_3001_; 
lean_dec(v_fst_2988_);
lean_dec(v_fst_2978_);
lean_dec(v_fst_2973_);
if (v_isShared_2992_ == 0)
{
lean_ctor_set(v___x_2991_, 0, v_e_2846_);
v___x_3001_ = v___x_2991_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_e_2846_);
lean_ctor_set(v_reuseFailAlloc_3005_, 1, v_snd_2989_);
v___x_3001_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
lean_object* v___x_3003_; 
if (v_isShared_2987_ == 0)
{
lean_ctor_set(v___x_2986_, 0, v___x_3001_);
v___x_3003_ = v___x_2986_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v___x_3001_);
lean_ctor_set(v_reuseFailAlloc_3004_, 1, v_a_2984_);
v___x_3003_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
return v___x_3003_;
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
lean_dec(v_fst_2978_);
lean_dec(v_fst_2973_);
lean_dec_ref_known(v_e_2846_, 4);
return v___x_2982_;
}
}
else
{
lean_dec(v_fst_2973_);
lean_dec_ref_known(v_e_2846_, 4);
lean_dec(v_offset_2847_);
return v___x_2975_;
}
}
else
{
lean_dec_ref_known(v_e_2846_, 4);
lean_dec(v_offset_2847_);
return v___x_2970_;
}
}
case 10:
{
lean_object* v_data_3014_; lean_object* v_expr_3015_; lean_object* v___x_3016_; 
v_data_3014_ = lean_ctor_get(v_e_2846_, 0);
v_expr_3015_ = lean_ctor_get(v_e_2846_, 1);
lean_inc_ref(v_expr_3015_);
v___x_3016_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2843_, v_i_2844_, v___x_2845_, v_expr_3015_, v_offset_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_object* v_a_3017_; lean_object* v_a_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3038_; 
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
v_a_3018_ = lean_ctor_get(v___x_3016_, 1);
v_isSharedCheck_3038_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3020_ = v___x_3016_;
v_isShared_3021_ = v_isSharedCheck_3038_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_a_3018_);
lean_inc(v_a_3017_);
lean_dec(v___x_3016_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3038_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v_fst_3022_; lean_object* v_snd_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3037_; 
v_fst_3022_ = lean_ctor_get(v_a_3017_, 0);
v_snd_3023_ = lean_ctor_get(v_a_3017_, 1);
v_isSharedCheck_3037_ = !lean_is_exclusive(v_a_3017_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3025_ = v_a_3017_;
v_isShared_3026_ = v_isSharedCheck_3037_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_snd_3023_);
lean_inc(v_fst_3022_);
lean_dec(v_a_3017_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3037_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
size_t v___x_3027_; size_t v___x_3028_; uint8_t v___x_3029_; 
v___x_3027_ = lean_ptr_addr(v_expr_3015_);
v___x_3028_ = lean_ptr_addr(v_fst_3022_);
v___x_3029_ = lean_usize_dec_eq(v___x_3027_, v___x_3028_);
if (v___x_3029_ == 0)
{
lean_object* v___x_3030_; 
lean_inc(v_data_3014_);
lean_del_object(v___x_3025_);
lean_del_object(v___x_3020_);
lean_dec_ref_known(v_e_2846_, 2);
v___x_3030_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__5(v_data_3014_, v_fst_3022_, v_snd_3023_, v_a_2849_, v_a_2850_, v_a_3018_);
return v___x_3030_;
}
else
{
lean_object* v___x_3032_; 
lean_dec(v_fst_3022_);
if (v_isShared_3026_ == 0)
{
lean_ctor_set(v___x_3025_, 0, v_e_2846_);
v___x_3032_ = v___x_3025_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_e_2846_);
lean_ctor_set(v_reuseFailAlloc_3036_, 1, v_snd_3023_);
v___x_3032_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
lean_object* v___x_3034_; 
if (v_isShared_3021_ == 0)
{
lean_ctor_set(v___x_3020_, 0, v___x_3032_);
v___x_3034_ = v___x_3020_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___x_3032_);
lean_ctor_set(v_reuseFailAlloc_3035_, 1, v_a_3018_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2846_, 2);
return v___x_3016_;
}
}
case 11:
{
lean_object* v_typeName_3039_; lean_object* v_idx_3040_; lean_object* v_struct_3041_; lean_object* v___x_3042_; 
v_typeName_3039_ = lean_ctor_get(v_e_2846_, 0);
v_idx_3040_ = lean_ctor_get(v_e_2846_, 1);
v_struct_3041_ = lean_ctor_get(v_e_2846_, 2);
lean_inc_ref(v_struct_3041_);
v___x_3042_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2843_, v_i_2844_, v___x_2845_, v_struct_3041_, v_offset_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_);
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_object* v_a_3043_; lean_object* v_a_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3064_; 
v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
v_a_3044_ = lean_ctor_get(v___x_3042_, 1);
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_3046_ = v___x_3042_;
v_isShared_3047_ = v_isSharedCheck_3064_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_a_3044_);
lean_inc(v_a_3043_);
lean_dec(v___x_3042_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3064_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v_fst_3048_; lean_object* v_snd_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3063_; 
v_fst_3048_ = lean_ctor_get(v_a_3043_, 0);
v_snd_3049_ = lean_ctor_get(v_a_3043_, 1);
v_isSharedCheck_3063_ = !lean_is_exclusive(v_a_3043_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3051_ = v_a_3043_;
v_isShared_3052_ = v_isSharedCheck_3063_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_snd_3049_);
lean_inc(v_fst_3048_);
lean_dec(v_a_3043_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3063_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
size_t v___x_3053_; size_t v___x_3054_; uint8_t v___x_3055_; 
v___x_3053_ = lean_ptr_addr(v_struct_3041_);
v___x_3054_ = lean_ptr_addr(v_fst_3048_);
v___x_3055_ = lean_usize_dec_eq(v___x_3053_, v___x_3054_);
if (v___x_3055_ == 0)
{
lean_object* v___x_3056_; 
lean_inc(v_idx_3040_);
lean_inc(v_typeName_3039_);
lean_del_object(v___x_3051_);
lean_del_object(v___x_3046_);
lean_dec_ref_known(v_e_2846_, 3);
v___x_3056_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__6(v_typeName_3039_, v_idx_3040_, v_fst_3048_, v_snd_3049_, v_a_2849_, v_a_2850_, v_a_3044_);
return v___x_3056_;
}
else
{
lean_object* v___x_3058_; 
lean_dec(v_fst_3048_);
if (v_isShared_3052_ == 0)
{
lean_ctor_set(v___x_3051_, 0, v_e_2846_);
v___x_3058_ = v___x_3051_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_e_2846_);
lean_ctor_set(v_reuseFailAlloc_3062_, 1, v_snd_3049_);
v___x_3058_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
lean_object* v___x_3060_; 
if (v_isShared_3047_ == 0)
{
lean_ctor_set(v___x_3046_, 0, v___x_3058_);
v___x_3060_ = v___x_3046_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v___x_3058_);
lean_ctor_set(v_reuseFailAlloc_3061_, 1, v_a_3044_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2846_, 3);
return v___x_3042_;
}
}
default: 
{
lean_object* v___x_3065_; lean_object* v___x_3066_; 
lean_dec(v_offset_2847_);
lean_dec_ref(v_e_2846_);
v___x_3065_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__3);
v___x_3066_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7(v___x_3065_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_);
return v___x_3066_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(lean_object* v___x_3067_, lean_object* v_i_3068_, lean_object* v___x_3069_, lean_object* v_e_3070_, lean_object* v_offset_3071_, lean_object* v_a_3072_, uint8_t v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_){
_start:
{
lean_object* v_key_3076_; lean_object* v_a_3078_; lean_object* v___x_3091_; 
lean_inc(v_offset_3071_);
lean_inc_ref(v_e_3070_);
v_key_3076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_3076_, 0, v_e_3070_);
lean_ctor_set(v_key_3076_, 1, v_offset_3071_);
v___x_3091_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2___redArg(v_a_3072_, v_key_3076_);
if (lean_obj_tag(v___x_3091_) == 1)
{
lean_object* v_val_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
lean_dec_ref_known(v_key_3076_, 2);
lean_dec(v_offset_3071_);
lean_dec_ref(v_e_3070_);
v_val_3092_ = lean_ctor_get(v___x_3091_, 0);
lean_inc(v_val_3092_);
lean_dec_ref_known(v___x_3091_, 1);
v___x_3093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3093_, 0, v_val_3092_);
lean_ctor_set(v___x_3093_, 1, v_a_3072_);
v___x_3094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3093_);
lean_ctor_set(v___x_3094_, 1, v_a_3075_);
return v___x_3094_;
}
else
{
lean_dec(v___x_3091_);
switch(lean_obj_tag(v_e_3070_))
{
case 1:
{
lean_object* v_fvarId_3095_; lean_object* v___x_3096_; 
v_fvarId_3095_ = lean_ctor_get(v_e_3070_, 0);
v___x_3096_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___redArg(v___x_3067_, v_fvarId_3095_);
if (lean_obj_tag(v___x_3096_) == 1)
{
lean_object* v_val_3097_; uint8_t v___x_3098_; 
v_val_3097_ = lean_ctor_get(v___x_3096_, 0);
lean_inc(v_val_3097_);
lean_dec_ref_known(v___x_3096_, 1);
v___x_3098_ = lean_nat_dec_lt(v_val_3097_, v_i_3068_);
if (v___x_3098_ == 0)
{
lean_object* v___x_3099_; lean_object* v___x_3100_; 
lean_dec(v_val_3097_);
v___x_3099_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2);
v___x_3100_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3(v___x_3099_, v_a_3073_, v_a_3074_, v_a_3075_);
if (lean_obj_tag(v___x_3100_) == 0)
{
lean_object* v_a_3101_; 
v_a_3101_ = lean_ctor_get(v___x_3100_, 0);
lean_inc(v_a_3101_);
if (lean_obj_tag(v_a_3101_) == 1)
{
lean_object* v_a_3102_; lean_object* v_val_3103_; lean_object* v___x_3104_; 
lean_dec_ref_known(v_e_3070_, 1);
lean_dec(v_offset_3071_);
v_a_3102_ = lean_ctor_get(v___x_3100_, 1);
lean_inc(v_a_3102_);
lean_dec_ref_known(v___x_3100_, 2);
v_val_3103_ = lean_ctor_get(v_a_3101_, 0);
lean_inc(v_val_3103_);
lean_dec_ref_known(v_a_3101_, 1);
v___x_3104_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3076_, v_val_3103_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3102_);
return v___x_3104_;
}
else
{
lean_object* v_a_3105_; 
lean_dec(v_a_3101_);
v_a_3105_ = lean_ctor_get(v___x_3100_, 1);
lean_inc(v_a_3105_);
lean_dec_ref_known(v___x_3100_, 2);
v_a_3078_ = v_a_3105_;
goto v___jp_3077_;
}
}
else
{
lean_object* v_a_3106_; lean_object* v_a_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3114_; 
lean_dec_ref_known(v_e_3070_, 1);
lean_dec_ref_known(v_key_3076_, 2);
lean_dec_ref(v_a_3072_);
lean_dec(v_offset_3071_);
v_a_3106_ = lean_ctor_get(v___x_3100_, 0);
v_a_3107_ = lean_ctor_get(v___x_3100_, 1);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3109_ = v___x_3100_;
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_a_3107_);
lean_inc(v_a_3106_);
lean_dec(v___x_3100_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3112_; 
if (v_isShared_3110_ == 0)
{
v___x_3112_ = v___x_3109_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v_a_3106_);
lean_ctor_set(v_reuseFailAlloc_3113_, 1, v_a_3107_);
v___x_3112_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
return v___x_3112_;
}
}
}
}
else
{
lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; 
lean_dec_ref_known(v_e_3070_, 1);
v___x_3115_ = lean_nat_add(v_offset_3071_, v_i_3068_);
lean_dec(v_offset_3071_);
v___x_3116_ = lean_nat_sub(v___x_3115_, v_val_3097_);
lean_dec(v_val_3097_);
lean_dec(v___x_3115_);
v___x_3117_ = lean_unsigned_to_nat(1u);
v___x_3118_ = lean_nat_sub(v___x_3116_, v___x_3117_);
lean_dec(v___x_3116_);
v___x_3119_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4___redArg(v___x_3118_, v_a_3075_);
if (lean_obj_tag(v___x_3119_) == 0)
{
lean_object* v_a_3120_; lean_object* v_a_3121_; lean_object* v___x_3122_; 
v_a_3120_ = lean_ctor_get(v___x_3119_, 0);
lean_inc(v_a_3120_);
v_a_3121_ = lean_ctor_get(v___x_3119_, 1);
lean_inc(v_a_3121_);
lean_dec_ref_known(v___x_3119_, 2);
v___x_3122_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3076_, v_a_3120_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3121_);
return v___x_3122_;
}
else
{
lean_object* v_a_3123_; lean_object* v_a_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3131_; 
lean_dec_ref_known(v_key_3076_, 2);
lean_dec_ref(v_a_3072_);
v_a_3123_ = lean_ctor_get(v___x_3119_, 0);
v_a_3124_ = lean_ctor_get(v___x_3119_, 1);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3119_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3126_ = v___x_3119_;
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_a_3124_);
lean_inc(v_a_3123_);
lean_dec(v___x_3119_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v___x_3129_; 
if (v_isShared_3127_ == 0)
{
v___x_3129_ = v___x_3126_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_a_3123_);
lean_ctor_set(v_reuseFailAlloc_3130_, 1, v_a_3124_);
v___x_3129_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
return v___x_3129_;
}
}
}
}
}
else
{
lean_object* v___x_3132_; 
lean_dec(v___x_3096_);
lean_dec(v_offset_3071_);
v___x_3132_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3076_, v_e_3070_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_);
return v___x_3132_;
}
}
case 9:
{
lean_object* v___x_3133_; 
lean_dec(v_offset_3071_);
v___x_3133_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3076_, v_e_3070_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_);
return v___x_3133_;
}
case 2:
{
lean_object* v___x_3134_; 
lean_dec(v_offset_3071_);
v___x_3134_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3076_, v_e_3070_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_);
return v___x_3134_;
}
case 0:
{
lean_object* v___x_3135_; 
lean_dec(v_offset_3071_);
v___x_3135_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3076_, v_e_3070_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_);
return v___x_3135_;
}
case 4:
{
lean_object* v___x_3136_; 
lean_dec(v_offset_3071_);
v___x_3136_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3076_, v_e_3070_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_);
return v___x_3136_;
}
case 3:
{
lean_object* v___x_3137_; 
lean_dec(v_offset_3071_);
v___x_3137_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3076_, v_e_3070_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_);
return v___x_3137_;
}
default: 
{
uint8_t v___x_3138_; 
v___x_3138_ = l_Lean_Expr_hasFVar(v_e_3070_);
if (v___x_3138_ == 0)
{
lean_object* v___x_3139_; 
lean_dec(v_offset_3071_);
v___x_3139_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3076_, v_e_3070_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_);
return v___x_3139_;
}
else
{
lean_object* v___x_3140_; uint8_t v___x_3141_; 
v___x_3140_ = lean_unsigned_to_nat(0u);
v___x_3141_ = lean_nat_dec_eq(v___x_3069_, v___x_3140_);
if (v___x_3141_ == 0)
{
v_a_3078_ = v_a_3075_;
goto v___jp_3077_;
}
else
{
lean_object* v___x_3142_; 
lean_dec(v_offset_3071_);
v___x_3142_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3076_, v_e_3070_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_);
return v___x_3142_;
}
}
}
}
}
v___jp_3077_:
{
switch(lean_obj_tag(v_e_3070_))
{
case 9:
{
lean_object* v___x_3079_; 
lean_dec(v_offset_3071_);
v___x_3079_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3076_, v_e_3070_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3078_);
return v___x_3079_;
}
case 2:
{
lean_object* v___x_3080_; 
lean_dec(v_offset_3071_);
v___x_3080_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3076_, v_e_3070_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3078_);
return v___x_3080_;
}
case 0:
{
lean_object* v___x_3081_; 
lean_dec(v_offset_3071_);
v___x_3081_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3076_, v_e_3070_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3078_);
return v___x_3081_;
}
case 1:
{
lean_object* v___x_3082_; 
lean_dec(v_offset_3071_);
v___x_3082_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3076_, v_e_3070_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3078_);
return v___x_3082_;
}
case 4:
{
lean_object* v___x_3083_; 
lean_dec(v_offset_3071_);
v___x_3083_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3076_, v_e_3070_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3078_);
return v___x_3083_;
}
case 3:
{
lean_object* v___x_3084_; 
lean_dec(v_offset_3071_);
v___x_3084_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3076_, v_e_3070_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3078_);
return v___x_3084_;
}
default: 
{
lean_object* v___x_3085_; 
v___x_3085_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5(v___x_3067_, v_i_3068_, v___x_3069_, v_e_3070_, v_offset_3071_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3078_);
if (lean_obj_tag(v___x_3085_) == 0)
{
lean_object* v_a_3086_; lean_object* v_a_3087_; lean_object* v_fst_3088_; lean_object* v_snd_3089_; lean_object* v___x_3090_; 
v_a_3086_ = lean_ctor_get(v___x_3085_, 0);
lean_inc(v_a_3086_);
v_a_3087_ = lean_ctor_get(v___x_3085_, 1);
lean_inc(v_a_3087_);
lean_dec_ref_known(v___x_3085_, 2);
v_fst_3088_ = lean_ctor_get(v_a_3086_, 0);
lean_inc(v_fst_3088_);
v_snd_3089_ = lean_ctor_get(v_a_3086_, 1);
lean_inc(v_snd_3089_);
lean_dec(v_a_3086_);
v___x_3090_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3076_, v_fst_3088_, v_snd_3089_, v_a_3073_, v_a_3074_, v_a_3087_);
return v___x_3090_;
}
else
{
lean_dec_ref_known(v_key_3076_, 2);
return v___x_3085_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___boxed(lean_object* v___x_3143_, lean_object* v_i_3144_, lean_object* v___x_3145_, lean_object* v_e_3146_, lean_object* v_offset_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_){
_start:
{
uint8_t v_a_boxed_3152_; lean_object* v_res_3153_; 
v_a_boxed_3152_ = lean_unbox(v_a_3149_);
v_res_3153_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_3143_, v_i_3144_, v___x_3145_, v_e_3146_, v_offset_3147_, v_a_3148_, v_a_boxed_3152_, v_a_3150_, v_a_3151_);
lean_dec_ref(v_a_3150_);
lean_dec(v___x_3145_);
lean_dec(v_i_3144_);
lean_dec_ref(v___x_3143_);
return v_res_3153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5___boxed(lean_object* v___x_3154_, lean_object* v_i_3155_, lean_object* v___x_3156_, lean_object* v_e_3157_, lean_object* v_offset_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_){
_start:
{
uint8_t v_a_boxed_3163_; lean_object* v_res_3164_; 
v_a_boxed_3163_ = lean_unbox(v_a_3160_);
v_res_3164_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5(v___x_3154_, v_i_3155_, v___x_3156_, v_e_3157_, v_offset_3158_, v_a_3159_, v_a_boxed_3163_, v_a_3161_, v_a_3162_);
lean_dec_ref(v_a_3161_);
lean_dec(v___x_3156_);
lean_dec(v_i_3155_);
lean_dec_ref(v___x_3154_);
return v_res_3164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___lam__0(lean_object* v_e_3165_, lean_object* v___x_3166_, lean_object* v___x_3167_, lean_object* v_fst_3168_, lean_object* v___x_3169_, uint8_t v_debug_3170_, uint8_t v___x_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_){
_start:
{
lean_object* v_a_3175_; 
switch(lean_obj_tag(v_e_3165_))
{
case 1:
{
lean_object* v_fvarId_3205_; lean_object* v___x_3206_; 
v_fvarId_3205_ = lean_ctor_get(v_e_3165_, 0);
v___x_3206_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___redArg(v_fst_3168_, v_fvarId_3205_);
if (lean_obj_tag(v___x_3206_) == 1)
{
lean_object* v_val_3207_; uint8_t v___x_3208_; 
v_val_3207_ = lean_ctor_get(v___x_3206_, 0);
lean_inc(v_val_3207_);
lean_dec_ref_known(v___x_3206_, 1);
v___x_3208_ = lean_nat_dec_lt(v_val_3207_, v___x_3169_);
if (v___x_3208_ == 0)
{
lean_object* v___x_3209_; lean_object* v___x_3210_; 
lean_dec(v_val_3207_);
v___x_3209_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2);
v___x_3210_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3(v___x_3209_, v_debug_3170_, v___y_3172_, v___y_3173_);
if (lean_obj_tag(v___x_3210_) == 0)
{
lean_object* v_a_3211_; 
v_a_3211_ = lean_ctor_get(v___x_3210_, 0);
lean_inc(v_a_3211_);
if (lean_obj_tag(v_a_3211_) == 1)
{
lean_object* v_a_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3220_; 
lean_dec_ref_known(v_e_3165_, 1);
lean_dec(v___x_3167_);
lean_dec(v___x_3166_);
v_a_3212_ = lean_ctor_get(v___x_3210_, 1);
v_isSharedCheck_3220_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3220_ == 0)
{
lean_object* v_unused_3221_; 
v_unused_3221_ = lean_ctor_get(v___x_3210_, 0);
lean_dec(v_unused_3221_);
v___x_3214_ = v___x_3210_;
v_isShared_3215_ = v_isSharedCheck_3220_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_a_3212_);
lean_dec(v___x_3210_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3220_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v_val_3216_; lean_object* v___x_3218_; 
v_val_3216_ = lean_ctor_get(v_a_3211_, 0);
lean_inc(v_val_3216_);
lean_dec_ref_known(v_a_3211_, 1);
if (v_isShared_3215_ == 0)
{
lean_ctor_set(v___x_3214_, 0, v_val_3216_);
v___x_3218_ = v___x_3214_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v_val_3216_);
lean_ctor_set(v_reuseFailAlloc_3219_, 1, v_a_3212_);
v___x_3218_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
return v___x_3218_;
}
}
}
else
{
lean_object* v_a_3222_; 
lean_dec(v_a_3211_);
v_a_3222_ = lean_ctor_get(v___x_3210_, 1);
lean_inc(v_a_3222_);
lean_dec_ref_known(v___x_3210_, 2);
v_a_3175_ = v_a_3222_;
goto v___jp_3174_;
}
}
else
{
lean_object* v_a_3223_; lean_object* v_a_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3231_; 
lean_dec_ref_known(v_e_3165_, 1);
lean_dec(v___x_3167_);
lean_dec(v___x_3166_);
v_a_3223_ = lean_ctor_get(v___x_3210_, 0);
v_a_3224_ = lean_ctor_get(v___x_3210_, 1);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3231_ == 0)
{
v___x_3226_ = v___x_3210_;
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_a_3224_);
lean_inc(v_a_3223_);
lean_dec(v___x_3210_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3229_; 
if (v_isShared_3227_ == 0)
{
v___x_3229_ = v___x_3226_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v_a_3223_);
lean_ctor_set(v_reuseFailAlloc_3230_, 1, v_a_3224_);
v___x_3229_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
return v___x_3229_;
}
}
}
}
else
{
lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
lean_dec_ref_known(v_e_3165_, 1);
lean_dec(v___x_3167_);
lean_dec(v___x_3166_);
v___x_3232_ = lean_nat_sub(v___x_3169_, v_val_3207_);
lean_dec(v_val_3207_);
v___x_3233_ = lean_unsigned_to_nat(1u);
v___x_3234_ = lean_nat_sub(v___x_3232_, v___x_3233_);
lean_dec(v___x_3232_);
v___x_3235_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4___redArg(v___x_3234_, v___y_3173_);
return v___x_3235_;
}
}
else
{
lean_object* v___x_3236_; 
lean_dec(v___x_3206_);
lean_dec(v___x_3167_);
lean_dec(v___x_3166_);
v___x_3236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3236_, 0, v_e_3165_);
lean_ctor_set(v___x_3236_, 1, v___y_3173_);
return v___x_3236_;
}
}
case 9:
{
lean_object* v___x_3237_; 
lean_dec(v___x_3167_);
lean_dec(v___x_3166_);
v___x_3237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3237_, 0, v_e_3165_);
lean_ctor_set(v___x_3237_, 1, v___y_3173_);
return v___x_3237_;
}
case 2:
{
lean_object* v___x_3238_; 
lean_dec(v___x_3167_);
lean_dec(v___x_3166_);
v___x_3238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3238_, 0, v_e_3165_);
lean_ctor_set(v___x_3238_, 1, v___y_3173_);
return v___x_3238_;
}
case 0:
{
lean_object* v___x_3239_; 
lean_dec(v___x_3167_);
lean_dec(v___x_3166_);
v___x_3239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3239_, 0, v_e_3165_);
lean_ctor_set(v___x_3239_, 1, v___y_3173_);
return v___x_3239_;
}
case 4:
{
lean_object* v___x_3240_; 
lean_dec(v___x_3167_);
lean_dec(v___x_3166_);
v___x_3240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3240_, 0, v_e_3165_);
lean_ctor_set(v___x_3240_, 1, v___y_3173_);
return v___x_3240_;
}
case 3:
{
lean_object* v___x_3241_; 
lean_dec(v___x_3167_);
lean_dec(v___x_3166_);
v___x_3241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3241_, 0, v_e_3165_);
lean_ctor_set(v___x_3241_, 1, v___y_3173_);
return v___x_3241_;
}
default: 
{
uint8_t v___x_3242_; 
v___x_3242_ = l_Lean_Expr_hasFVar(v_e_3165_);
if (v___x_3242_ == 0)
{
lean_object* v___x_3243_; 
lean_dec(v___x_3167_);
lean_dec(v___x_3166_);
v___x_3243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3243_, 0, v_e_3165_);
lean_ctor_set(v___x_3243_, 1, v___y_3173_);
return v___x_3243_;
}
else
{
if (v___x_3171_ == 0)
{
v_a_3175_ = v___y_3173_;
goto v___jp_3174_;
}
else
{
lean_object* v___x_3244_; 
lean_dec(v___x_3167_);
lean_dec(v___x_3166_);
v___x_3244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3244_, 0, v_e_3165_);
lean_ctor_set(v___x_3244_, 1, v___y_3173_);
return v___x_3244_;
}
}
}
}
v___jp_3174_:
{
switch(lean_obj_tag(v_e_3165_))
{
case 9:
{
lean_object* v___x_3176_; 
lean_dec(v___x_3167_);
lean_dec(v___x_3166_);
v___x_3176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3176_, 0, v_e_3165_);
lean_ctor_set(v___x_3176_, 1, v_a_3175_);
return v___x_3176_;
}
case 2:
{
lean_object* v___x_3177_; 
lean_dec(v___x_3167_);
lean_dec(v___x_3166_);
v___x_3177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3177_, 0, v_e_3165_);
lean_ctor_set(v___x_3177_, 1, v_a_3175_);
return v___x_3177_;
}
case 0:
{
lean_object* v___x_3178_; 
lean_dec(v___x_3167_);
lean_dec(v___x_3166_);
v___x_3178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3178_, 0, v_e_3165_);
lean_ctor_set(v___x_3178_, 1, v_a_3175_);
return v___x_3178_;
}
case 1:
{
lean_object* v___x_3179_; 
lean_dec(v___x_3167_);
lean_dec(v___x_3166_);
v___x_3179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3179_, 0, v_e_3165_);
lean_ctor_set(v___x_3179_, 1, v_a_3175_);
return v___x_3179_;
}
case 4:
{
lean_object* v___x_3180_; 
lean_dec(v___x_3167_);
lean_dec(v___x_3166_);
v___x_3180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3180_, 0, v_e_3165_);
lean_ctor_set(v___x_3180_, 1, v_a_3175_);
return v___x_3180_;
}
case 3:
{
lean_object* v___x_3181_; 
lean_dec(v___x_3167_);
lean_dec(v___x_3166_);
v___x_3181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3181_, 0, v_e_3165_);
lean_ctor_set(v___x_3181_, 1, v_a_3175_);
return v___x_3181_;
}
default: 
{
lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3182_ = lean_box(0);
v___x_3183_ = lean_mk_array(v___x_3166_, v___x_3182_);
lean_inc(v___x_3167_);
v___x_3184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3184_, 0, v___x_3167_);
lean_ctor_set(v___x_3184_, 1, v___x_3183_);
v___x_3185_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5(v_fst_3168_, v___x_3169_, v___x_3169_, v_e_3165_, v___x_3167_, v___x_3184_, v_debug_3170_, v___y_3172_, v_a_3175_);
if (lean_obj_tag(v___x_3185_) == 0)
{
lean_object* v_a_3186_; lean_object* v_a_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3195_; 
v_a_3186_ = lean_ctor_get(v___x_3185_, 0);
v_a_3187_ = lean_ctor_get(v___x_3185_, 1);
v_isSharedCheck_3195_ = !lean_is_exclusive(v___x_3185_);
if (v_isSharedCheck_3195_ == 0)
{
v___x_3189_ = v___x_3185_;
v_isShared_3190_ = v_isSharedCheck_3195_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_a_3187_);
lean_inc(v_a_3186_);
lean_dec(v___x_3185_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3195_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v_fst_3191_; lean_object* v___x_3193_; 
v_fst_3191_ = lean_ctor_get(v_a_3186_, 0);
lean_inc(v_fst_3191_);
lean_dec(v_a_3186_);
if (v_isShared_3190_ == 0)
{
lean_ctor_set(v___x_3189_, 0, v_fst_3191_);
v___x_3193_ = v___x_3189_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v_fst_3191_);
lean_ctor_set(v_reuseFailAlloc_3194_, 1, v_a_3187_);
v___x_3193_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
return v___x_3193_;
}
}
}
else
{
lean_object* v_a_3196_; lean_object* v_a_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3204_; 
v_a_3196_ = lean_ctor_get(v___x_3185_, 0);
v_a_3197_ = lean_ctor_get(v___x_3185_, 1);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3185_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3199_ = v___x_3185_;
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_a_3197_);
lean_inc(v_a_3196_);
lean_dec(v___x_3185_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3202_; 
if (v_isShared_3200_ == 0)
{
v___x_3202_ = v___x_3199_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_a_3196_);
lean_ctor_set(v_reuseFailAlloc_3203_, 1, v_a_3197_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___lam__0___boxed(lean_object* v_e_3245_, lean_object* v___x_3246_, lean_object* v___x_3247_, lean_object* v_fst_3248_, lean_object* v___x_3249_, lean_object* v_debug_3250_, lean_object* v___x_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_){
_start:
{
uint8_t v_debug_boxed_3254_; uint8_t v___x_18145__boxed_3255_; lean_object* v_res_3256_; 
v_debug_boxed_3254_ = lean_unbox(v_debug_3250_);
v___x_18145__boxed_3255_ = lean_unbox(v___x_3251_);
v_res_3256_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___lam__0(v_e_3245_, v___x_3246_, v___x_3247_, v_fst_3248_, v___x_3249_, v_debug_boxed_3254_, v___x_18145__boxed_3255_, v___y_3252_, v___y_3253_);
lean_dec_ref(v___y_3252_);
lean_dec(v___x_3249_);
lean_dec(v_fst_3248_);
return v_res_3256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__0(lean_object* v_piece_3257_, lean_object* v___x_3258_, lean_object* v___x_3259_, lean_object* v_i_3260_, lean_object* v___x_3261_, uint8_t v_debug_3262_, uint8_t v___x_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_){
_start:
{
lean_object* v_a_3267_; 
switch(lean_obj_tag(v_piece_3257_))
{
case 1:
{
lean_object* v_fvarId_3296_; lean_object* v___x_3297_; 
v_fvarId_3296_ = lean_ctor_get(v_piece_3257_, 0);
v___x_3297_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___redArg(v___x_3259_, v_fvarId_3296_);
if (lean_obj_tag(v___x_3297_) == 1)
{
lean_object* v_val_3298_; uint8_t v___x_3299_; 
v_val_3298_ = lean_ctor_get(v___x_3297_, 0);
lean_inc(v_val_3298_);
lean_dec_ref_known(v___x_3297_, 1);
v___x_3299_ = lean_nat_dec_lt(v_val_3298_, v_i_3260_);
if (v___x_3299_ == 0)
{
lean_object* v___x_3300_; lean_object* v___x_3301_; 
lean_dec(v_val_3298_);
v___x_3300_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2);
v___x_3301_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3(v___x_3300_, v_debug_3262_, v___y_3264_, v___y_3265_);
if (lean_obj_tag(v___x_3301_) == 0)
{
lean_object* v_a_3302_; 
v_a_3302_ = lean_ctor_get(v___x_3301_, 0);
lean_inc(v_a_3302_);
if (lean_obj_tag(v_a_3302_) == 1)
{
lean_object* v_a_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3311_; 
lean_dec_ref_known(v_piece_3257_, 1);
lean_dec(v___x_3258_);
v_a_3303_ = lean_ctor_get(v___x_3301_, 1);
v_isSharedCheck_3311_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3311_ == 0)
{
lean_object* v_unused_3312_; 
v_unused_3312_ = lean_ctor_get(v___x_3301_, 0);
lean_dec(v_unused_3312_);
v___x_3305_ = v___x_3301_;
v_isShared_3306_ = v_isSharedCheck_3311_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_a_3303_);
lean_dec(v___x_3301_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3311_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v_val_3307_; lean_object* v___x_3309_; 
v_val_3307_ = lean_ctor_get(v_a_3302_, 0);
lean_inc(v_val_3307_);
lean_dec_ref_known(v_a_3302_, 1);
if (v_isShared_3306_ == 0)
{
lean_ctor_set(v___x_3305_, 0, v_val_3307_);
v___x_3309_ = v___x_3305_;
goto v_reusejp_3308_;
}
else
{
lean_object* v_reuseFailAlloc_3310_; 
v_reuseFailAlloc_3310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3310_, 0, v_val_3307_);
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
lean_object* v_a_3313_; 
lean_dec(v_a_3302_);
v_a_3313_ = lean_ctor_get(v___x_3301_, 1);
lean_inc(v_a_3313_);
lean_dec_ref_known(v___x_3301_, 2);
v_a_3267_ = v_a_3313_;
goto v___jp_3266_;
}
}
else
{
lean_object* v_a_3314_; lean_object* v_a_3315_; lean_object* v___x_3317_; uint8_t v_isShared_3318_; uint8_t v_isSharedCheck_3322_; 
lean_dec_ref_known(v_piece_3257_, 1);
lean_dec(v___x_3258_);
v_a_3314_ = lean_ctor_get(v___x_3301_, 0);
v_a_3315_ = lean_ctor_get(v___x_3301_, 1);
v_isSharedCheck_3322_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3322_ == 0)
{
v___x_3317_ = v___x_3301_;
v_isShared_3318_ = v_isSharedCheck_3322_;
goto v_resetjp_3316_;
}
else
{
lean_inc(v_a_3315_);
lean_inc(v_a_3314_);
lean_dec(v___x_3301_);
v___x_3317_ = lean_box(0);
v_isShared_3318_ = v_isSharedCheck_3322_;
goto v_resetjp_3316_;
}
v_resetjp_3316_:
{
lean_object* v___x_3320_; 
if (v_isShared_3318_ == 0)
{
v___x_3320_ = v___x_3317_;
goto v_reusejp_3319_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v_a_3314_);
lean_ctor_set(v_reuseFailAlloc_3321_, 1, v_a_3315_);
v___x_3320_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3319_;
}
v_reusejp_3319_:
{
return v___x_3320_;
}
}
}
}
else
{
lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; 
lean_dec_ref_known(v_piece_3257_, 1);
lean_dec(v___x_3258_);
v___x_3323_ = lean_nat_sub(v_i_3260_, v_val_3298_);
lean_dec(v_val_3298_);
v___x_3324_ = lean_unsigned_to_nat(1u);
v___x_3325_ = lean_nat_sub(v___x_3323_, v___x_3324_);
lean_dec(v___x_3323_);
v___x_3326_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4___redArg(v___x_3325_, v___y_3265_);
return v___x_3326_;
}
}
else
{
lean_object* v___x_3327_; 
lean_dec(v___x_3297_);
lean_dec(v___x_3258_);
v___x_3327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3327_, 0, v_piece_3257_);
lean_ctor_set(v___x_3327_, 1, v___y_3265_);
return v___x_3327_;
}
}
case 9:
{
lean_object* v___x_3328_; 
lean_dec(v___x_3258_);
v___x_3328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3328_, 0, v_piece_3257_);
lean_ctor_set(v___x_3328_, 1, v___y_3265_);
return v___x_3328_;
}
case 2:
{
lean_object* v___x_3329_; 
lean_dec(v___x_3258_);
v___x_3329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3329_, 0, v_piece_3257_);
lean_ctor_set(v___x_3329_, 1, v___y_3265_);
return v___x_3329_;
}
case 0:
{
lean_object* v___x_3330_; 
lean_dec(v___x_3258_);
v___x_3330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3330_, 0, v_piece_3257_);
lean_ctor_set(v___x_3330_, 1, v___y_3265_);
return v___x_3330_;
}
case 4:
{
lean_object* v___x_3331_; 
lean_dec(v___x_3258_);
v___x_3331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3331_, 0, v_piece_3257_);
lean_ctor_set(v___x_3331_, 1, v___y_3265_);
return v___x_3331_;
}
case 3:
{
lean_object* v___x_3332_; 
lean_dec(v___x_3258_);
v___x_3332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3332_, 0, v_piece_3257_);
lean_ctor_set(v___x_3332_, 1, v___y_3265_);
return v___x_3332_;
}
default: 
{
uint8_t v___x_3333_; 
v___x_3333_ = l_Lean_Expr_hasFVar(v_piece_3257_);
if (v___x_3333_ == 0)
{
lean_object* v___x_3334_; 
lean_dec(v___x_3258_);
v___x_3334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3334_, 0, v_piece_3257_);
lean_ctor_set(v___x_3334_, 1, v___y_3265_);
return v___x_3334_;
}
else
{
if (v___x_3263_ == 0)
{
v_a_3267_ = v___y_3265_;
goto v___jp_3266_;
}
else
{
lean_object* v___x_3335_; 
lean_dec(v___x_3258_);
v___x_3335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3335_, 0, v_piece_3257_);
lean_ctor_set(v___x_3335_, 1, v___y_3265_);
return v___x_3335_;
}
}
}
}
v___jp_3266_:
{
switch(lean_obj_tag(v_piece_3257_))
{
case 9:
{
lean_object* v___x_3268_; 
lean_dec(v___x_3258_);
v___x_3268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3268_, 0, v_piece_3257_);
lean_ctor_set(v___x_3268_, 1, v_a_3267_);
return v___x_3268_;
}
case 2:
{
lean_object* v___x_3269_; 
lean_dec(v___x_3258_);
v___x_3269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3269_, 0, v_piece_3257_);
lean_ctor_set(v___x_3269_, 1, v_a_3267_);
return v___x_3269_;
}
case 0:
{
lean_object* v___x_3270_; 
lean_dec(v___x_3258_);
v___x_3270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3270_, 0, v_piece_3257_);
lean_ctor_set(v___x_3270_, 1, v_a_3267_);
return v___x_3270_;
}
case 1:
{
lean_object* v___x_3271_; 
lean_dec(v___x_3258_);
v___x_3271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3271_, 0, v_piece_3257_);
lean_ctor_set(v___x_3271_, 1, v_a_3267_);
return v___x_3271_;
}
case 4:
{
lean_object* v___x_3272_; 
lean_dec(v___x_3258_);
v___x_3272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3272_, 0, v_piece_3257_);
lean_ctor_set(v___x_3272_, 1, v_a_3267_);
return v___x_3272_;
}
case 3:
{
lean_object* v___x_3273_; 
lean_dec(v___x_3258_);
v___x_3273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3273_, 0, v_piece_3257_);
lean_ctor_set(v___x_3273_, 1, v_a_3267_);
return v___x_3273_;
}
default: 
{
lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; 
v___x_3274_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__0, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__0_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__0);
lean_inc(v___x_3258_);
v___x_3275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3275_, 0, v___x_3258_);
lean_ctor_set(v___x_3275_, 1, v___x_3274_);
v___x_3276_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5(v___x_3259_, v_i_3260_, v___x_3261_, v_piece_3257_, v___x_3258_, v___x_3275_, v_debug_3262_, v___y_3264_, v_a_3267_);
if (lean_obj_tag(v___x_3276_) == 0)
{
lean_object* v_a_3277_; lean_object* v_a_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3286_; 
v_a_3277_ = lean_ctor_get(v___x_3276_, 0);
v_a_3278_ = lean_ctor_get(v___x_3276_, 1);
v_isSharedCheck_3286_ = !lean_is_exclusive(v___x_3276_);
if (v_isSharedCheck_3286_ == 0)
{
v___x_3280_ = v___x_3276_;
v_isShared_3281_ = v_isSharedCheck_3286_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_a_3278_);
lean_inc(v_a_3277_);
lean_dec(v___x_3276_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3286_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
lean_object* v_fst_3282_; lean_object* v___x_3284_; 
v_fst_3282_ = lean_ctor_get(v_a_3277_, 0);
lean_inc(v_fst_3282_);
lean_dec(v_a_3277_);
if (v_isShared_3281_ == 0)
{
lean_ctor_set(v___x_3280_, 0, v_fst_3282_);
v___x_3284_ = v___x_3280_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v_fst_3282_);
lean_ctor_set(v_reuseFailAlloc_3285_, 1, v_a_3278_);
v___x_3284_ = v_reuseFailAlloc_3285_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
return v___x_3284_;
}
}
}
else
{
lean_object* v_a_3287_; lean_object* v_a_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3295_; 
v_a_3287_ = lean_ctor_get(v___x_3276_, 0);
v_a_3288_ = lean_ctor_get(v___x_3276_, 1);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3276_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3290_ = v___x_3276_;
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_a_3288_);
lean_inc(v_a_3287_);
lean_dec(v___x_3276_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v___x_3293_; 
if (v_isShared_3291_ == 0)
{
v___x_3293_ = v___x_3290_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_a_3287_);
lean_ctor_set(v_reuseFailAlloc_3294_, 1, v_a_3288_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__0___boxed(lean_object* v_piece_3336_, lean_object* v___x_3337_, lean_object* v___x_3338_, lean_object* v_i_3339_, lean_object* v___x_3340_, lean_object* v_debug_3341_, lean_object* v___x_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_){
_start:
{
uint8_t v_debug_boxed_3345_; uint8_t v___x_18333__boxed_3346_; lean_object* v_res_3347_; 
v_debug_boxed_3345_ = lean_unbox(v_debug_3341_);
v___x_18333__boxed_3346_ = lean_unbox(v___x_3342_);
v_res_3347_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__0(v_piece_3336_, v___x_3337_, v___x_3338_, v_i_3339_, v___x_3340_, v_debug_boxed_3345_, v___x_18333__boxed_3346_, v___y_3343_, v___y_3344_);
lean_dec_ref(v___y_3343_);
lean_dec(v___x_3340_);
lean_dec(v_i_3339_);
lean_dec_ref(v___x_3338_);
return v_res_3347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__1(lean_object* v___x_3348_, lean_object* v___x_3349_, lean_object* v___x_3350_, uint8_t v___x_3351_, lean_object* v_piece_3352_, lean_object* v_i_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_){
_start:
{
lean_object* v___x_3362_; lean_object* v___x_3363_; uint8_t v_debug_3364_; lean_object* v_env_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___f_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; 
v___x_3362_ = lean_st_ref_get(v___y_3356_);
v___x_3363_ = lean_st_ref_get(v___y_3360_);
v_debug_3364_ = lean_ctor_get_uint8(v___x_3362_, sizeof(void*)*11);
lean_dec(v___x_3362_);
v_env_3365_ = lean_ctor_get(v___x_3363_, 0);
lean_inc_ref(v_env_3365_);
lean_dec(v___x_3363_);
v___x_3366_ = lean_box(v_debug_3364_);
v___x_3367_ = lean_box(v___x_3351_);
v___f_3368_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__0___boxed), 9, 7);
lean_closure_set(v___f_3368_, 0, v_piece_3352_);
lean_closure_set(v___f_3368_, 1, v___x_3348_);
lean_closure_set(v___f_3368_, 2, v___x_3349_);
lean_closure_set(v___f_3368_, 3, v_i_3353_);
lean_closure_set(v___f_3368_, 4, v___x_3350_);
lean_closure_set(v___f_3368_, 5, v___x_3366_);
lean_closure_set(v___f_3368_, 6, v___x_3367_);
v___x_3369_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_3369_, 0, v_env_3365_);
lean_ctor_set_uint8(v___x_3369_, sizeof(void*)*1, v___x_3351_);
lean_ctor_set_uint8(v___x_3369_, sizeof(void*)*1 + 1, v___x_3351_);
v___x_3370_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_3368_, v___x_3369_, v___y_3356_);
if (lean_obj_tag(v___x_3370_) == 0)
{
lean_object* v_a_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3381_; 
v_a_3371_ = lean_ctor_get(v___x_3370_, 0);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3370_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3373_ = v___x_3370_;
v_isShared_3374_ = v_isSharedCheck_3381_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_a_3371_);
lean_dec(v___x_3370_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3381_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
if (lean_obj_tag(v_a_3371_) == 0)
{
lean_object* v___x_3375_; lean_object* v___x_3376_; 
lean_dec_ref_known(v_a_3371_, 1);
lean_del_object(v___x_3373_);
v___x_3375_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2);
v___x_3376_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1(v___x_3375_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_);
return v___x_3376_;
}
else
{
lean_object* v_a_3377_; lean_object* v___x_3379_; 
v_a_3377_ = lean_ctor_get(v_a_3371_, 0);
lean_inc(v_a_3377_);
lean_dec_ref_known(v_a_3371_, 1);
if (v_isShared_3374_ == 0)
{
lean_ctor_set(v___x_3373_, 0, v_a_3377_);
v___x_3379_ = v___x_3373_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_a_3377_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
}
}
}
}
else
{
lean_object* v_a_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3389_; 
v_a_3382_ = lean_ctor_get(v___x_3370_, 0);
v_isSharedCheck_3389_ = !lean_is_exclusive(v___x_3370_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3384_ = v___x_3370_;
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_a_3382_);
lean_dec(v___x_3370_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v___x_3387_; 
if (v_isShared_3385_ == 0)
{
v___x_3387_ = v___x_3384_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_a_3382_);
v___x_3387_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
return v___x_3387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__1___boxed(lean_object* v___x_3390_, lean_object* v___x_3391_, lean_object* v___x_3392_, lean_object* v___x_3393_, lean_object* v_piece_3394_, lean_object* v_i_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_){
_start:
{
uint8_t v___x_18518__boxed_3404_; lean_object* v_res_3405_; 
v___x_18518__boxed_3404_ = lean_unbox(v___x_3393_);
v_res_3405_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__1(v___x_3390_, v___x_3391_, v___x_3392_, v___x_18518__boxed_3404_, v_piece_3394_, v_i_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_);
lean_dec(v___y_3402_);
lean_dec_ref(v___y_3401_);
lean_dec(v___y_3400_);
lean_dec_ref(v___y_3399_);
lean_dec(v___y_3398_);
lean_dec_ref(v___y_3397_);
lean_dec(v___y_3396_);
return v_res_3405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7_spec__12(lean_object* v___x_3406_, lean_object* v___x_3407_, lean_object* v_as_3408_, size_t v_sz_3409_, size_t v_i_3410_, lean_object* v_b_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_){
_start:
{
uint8_t v___x_3420_; 
v___x_3420_ = lean_usize_dec_lt(v_i_3410_, v_sz_3409_);
if (v___x_3420_ == 0)
{
lean_object* v___x_3421_; 
lean_dec(v___x_3407_);
lean_dec_ref(v___x_3406_);
v___x_3421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3421_, 0, v_b_3411_);
return v___x_3421_;
}
else
{
lean_object* v_fst_3422_; lean_object* v_snd_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3472_; 
v_fst_3422_ = lean_ctor_get(v_b_3411_, 0);
v_snd_3423_ = lean_ctor_get(v_b_3411_, 1);
v_isSharedCheck_3472_ = !lean_is_exclusive(v_b_3411_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3425_ = v_b_3411_;
v_isShared_3426_ = v_isSharedCheck_3472_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_snd_3423_);
lean_inc(v_fst_3422_);
lean_dec(v_b_3411_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3472_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v_a_3427_; lean_object* v_userName_3428_; lean_object* v_type_3429_; lean_object* v_value_3430_; uint8_t v_nondep_3431_; lean_object* v___x_3432_; uint8_t v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; 
v_a_3427_ = lean_array_uget_borrowed(v_as_3408_, v_i_3410_);
v_userName_3428_ = lean_ctor_get(v_a_3427_, 1);
v_type_3429_ = lean_ctor_get(v_a_3427_, 2);
v_value_3430_ = lean_ctor_get(v_a_3427_, 3);
v_nondep_3431_ = lean_ctor_get_uint8(v_a_3427_, sizeof(void*)*4);
v___x_3432_ = lean_unsigned_to_nat(0u);
v___x_3433_ = lean_nat_dec_eq(v___x_3407_, v___x_3432_);
v___x_3434_ = lean_unsigned_to_nat(1u);
v___x_3435_ = lean_nat_sub(v_snd_3423_, v___x_3434_);
lean_dec(v_snd_3423_);
lean_inc(v___x_3435_);
lean_inc_ref(v_type_3429_);
lean_inc(v___x_3407_);
lean_inc_ref(v___x_3406_);
v___x_3436_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__1(v___x_3432_, v___x_3406_, v___x_3407_, v___x_3433_, v_type_3429_, v___x_3435_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_);
if (lean_obj_tag(v___x_3436_) == 0)
{
lean_object* v_a_3437_; lean_object* v___x_3438_; 
v_a_3437_ = lean_ctor_get(v___x_3436_, 0);
lean_inc(v_a_3437_);
lean_dec_ref_known(v___x_3436_, 1);
lean_inc(v___x_3435_);
lean_inc_ref(v_value_3430_);
lean_inc(v___x_3407_);
lean_inc_ref(v___x_3406_);
v___x_3438_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__1(v___x_3432_, v___x_3406_, v___x_3407_, v___x_3433_, v_value_3430_, v___x_3435_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_);
if (lean_obj_tag(v___x_3438_) == 0)
{
lean_object* v_a_3439_; lean_object* v___x_3440_; 
v_a_3439_ = lean_ctor_get(v___x_3438_, 0);
lean_inc(v_a_3439_);
lean_dec_ref_known(v___x_3438_, 1);
lean_inc(v_userName_3428_);
v___x_3440_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6___redArg(v_userName_3428_, v_a_3437_, v_a_3439_, v_fst_3422_, v_nondep_3431_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_);
if (lean_obj_tag(v___x_3440_) == 0)
{
lean_object* v_a_3441_; lean_object* v___x_3443_; 
v_a_3441_ = lean_ctor_get(v___x_3440_, 0);
lean_inc(v_a_3441_);
lean_dec_ref_known(v___x_3440_, 1);
if (v_isShared_3426_ == 0)
{
lean_ctor_set(v___x_3425_, 1, v___x_3435_);
lean_ctor_set(v___x_3425_, 0, v_a_3441_);
v___x_3443_ = v___x_3425_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v_a_3441_);
lean_ctor_set(v_reuseFailAlloc_3447_, 1, v___x_3435_);
v___x_3443_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
size_t v___x_3444_; size_t v___x_3445_; 
v___x_3444_ = ((size_t)1ULL);
v___x_3445_ = lean_usize_add(v_i_3410_, v___x_3444_);
v_i_3410_ = v___x_3445_;
v_b_3411_ = v___x_3443_;
goto _start;
}
}
else
{
lean_object* v_a_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3455_; 
lean_dec(v___x_3435_);
lean_del_object(v___x_3425_);
lean_dec(v___x_3407_);
lean_dec_ref(v___x_3406_);
v_a_3448_ = lean_ctor_get(v___x_3440_, 0);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3440_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3450_ = v___x_3440_;
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_a_3448_);
lean_dec(v___x_3440_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v___x_3453_; 
if (v_isShared_3451_ == 0)
{
v___x_3453_ = v___x_3450_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_a_3448_);
v___x_3453_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
return v___x_3453_;
}
}
}
}
else
{
lean_object* v_a_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3463_; 
lean_dec(v_a_3437_);
lean_dec(v___x_3435_);
lean_del_object(v___x_3425_);
lean_dec(v_fst_3422_);
lean_dec(v___x_3407_);
lean_dec_ref(v___x_3406_);
v_a_3456_ = lean_ctor_get(v___x_3438_, 0);
v_isSharedCheck_3463_ = !lean_is_exclusive(v___x_3438_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3458_ = v___x_3438_;
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_a_3456_);
lean_dec(v___x_3438_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3461_; 
if (v_isShared_3459_ == 0)
{
v___x_3461_ = v___x_3458_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_a_3456_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
return v___x_3461_;
}
}
}
}
else
{
lean_object* v_a_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3471_; 
lean_dec(v___x_3435_);
lean_del_object(v___x_3425_);
lean_dec(v_fst_3422_);
lean_dec(v___x_3407_);
lean_dec_ref(v___x_3406_);
v_a_3464_ = lean_ctor_get(v___x_3436_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3436_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3466_ = v___x_3436_;
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_a_3464_);
lean_dec(v___x_3436_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3469_; 
if (v_isShared_3467_ == 0)
{
v___x_3469_ = v___x_3466_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_a_3464_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7_spec__12___boxed(lean_object* v___x_3473_, lean_object* v___x_3474_, lean_object* v_as_3475_, lean_object* v_sz_3476_, lean_object* v_i_3477_, lean_object* v_b_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_){
_start:
{
size_t v_sz_boxed_3487_; size_t v_i_boxed_3488_; lean_object* v_res_3489_; 
v_sz_boxed_3487_ = lean_unbox_usize(v_sz_3476_);
lean_dec(v_sz_3476_);
v_i_boxed_3488_ = lean_unbox_usize(v_i_3477_);
lean_dec(v_i_3477_);
v_res_3489_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7_spec__12(v___x_3473_, v___x_3474_, v_as_3475_, v_sz_boxed_3487_, v_i_boxed_3488_, v_b_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
lean_dec(v___y_3479_);
lean_dec_ref(v_as_3475_);
return v_res_3489_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7(lean_object* v___x_3490_, lean_object* v___x_3491_, lean_object* v_as_3492_, size_t v_sz_3493_, size_t v_i_3494_, lean_object* v_b_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_){
_start:
{
uint8_t v___x_3504_; 
v___x_3504_ = lean_usize_dec_lt(v_i_3494_, v_sz_3493_);
if (v___x_3504_ == 0)
{
lean_object* v___x_3505_; 
lean_dec(v___x_3491_);
lean_dec_ref(v___x_3490_);
v___x_3505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3505_, 0, v_b_3495_);
return v___x_3505_;
}
else
{
lean_object* v_fst_3506_; lean_object* v_snd_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3556_; 
v_fst_3506_ = lean_ctor_get(v_b_3495_, 0);
v_snd_3507_ = lean_ctor_get(v_b_3495_, 1);
v_isSharedCheck_3556_ = !lean_is_exclusive(v_b_3495_);
if (v_isSharedCheck_3556_ == 0)
{
v___x_3509_ = v_b_3495_;
v_isShared_3510_ = v_isSharedCheck_3556_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_snd_3507_);
lean_inc(v_fst_3506_);
lean_dec(v_b_3495_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3556_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v_a_3511_; lean_object* v_userName_3512_; lean_object* v_type_3513_; lean_object* v_value_3514_; uint8_t v_nondep_3515_; lean_object* v___x_3516_; uint8_t v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; 
v_a_3511_ = lean_array_uget_borrowed(v_as_3492_, v_i_3494_);
v_userName_3512_ = lean_ctor_get(v_a_3511_, 1);
v_type_3513_ = lean_ctor_get(v_a_3511_, 2);
v_value_3514_ = lean_ctor_get(v_a_3511_, 3);
v_nondep_3515_ = lean_ctor_get_uint8(v_a_3511_, sizeof(void*)*4);
v___x_3516_ = lean_unsigned_to_nat(0u);
v___x_3517_ = lean_nat_dec_eq(v___x_3491_, v___x_3516_);
v___x_3518_ = lean_unsigned_to_nat(1u);
v___x_3519_ = lean_nat_sub(v_snd_3507_, v___x_3518_);
lean_dec(v_snd_3507_);
lean_inc(v___x_3519_);
lean_inc_ref(v_type_3513_);
lean_inc(v___x_3491_);
lean_inc_ref(v___x_3490_);
v___x_3520_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__1(v___x_3516_, v___x_3490_, v___x_3491_, v___x_3517_, v_type_3513_, v___x_3519_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
if (lean_obj_tag(v___x_3520_) == 0)
{
lean_object* v_a_3521_; lean_object* v___x_3522_; 
v_a_3521_ = lean_ctor_get(v___x_3520_, 0);
lean_inc(v_a_3521_);
lean_dec_ref_known(v___x_3520_, 1);
lean_inc(v___x_3519_);
lean_inc_ref(v_value_3514_);
lean_inc(v___x_3491_);
lean_inc_ref(v___x_3490_);
v___x_3522_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__1(v___x_3516_, v___x_3490_, v___x_3491_, v___x_3517_, v_value_3514_, v___x_3519_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
if (lean_obj_tag(v___x_3522_) == 0)
{
lean_object* v_a_3523_; lean_object* v___x_3524_; 
v_a_3523_ = lean_ctor_get(v___x_3522_, 0);
lean_inc(v_a_3523_);
lean_dec_ref_known(v___x_3522_, 1);
lean_inc(v_userName_3512_);
v___x_3524_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6___redArg(v_userName_3512_, v_a_3521_, v_a_3523_, v_fst_3506_, v_nondep_3515_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
if (lean_obj_tag(v___x_3524_) == 0)
{
lean_object* v_a_3525_; lean_object* v___x_3527_; 
v_a_3525_ = lean_ctor_get(v___x_3524_, 0);
lean_inc(v_a_3525_);
lean_dec_ref_known(v___x_3524_, 1);
if (v_isShared_3510_ == 0)
{
lean_ctor_set(v___x_3509_, 1, v___x_3519_);
lean_ctor_set(v___x_3509_, 0, v_a_3525_);
v___x_3527_ = v___x_3509_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_a_3525_);
lean_ctor_set(v_reuseFailAlloc_3531_, 1, v___x_3519_);
v___x_3527_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
size_t v___x_3528_; size_t v___x_3529_; lean_object* v___x_3530_; 
v___x_3528_ = ((size_t)1ULL);
v___x_3529_ = lean_usize_add(v_i_3494_, v___x_3528_);
v___x_3530_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7_spec__12(v___x_3490_, v___x_3491_, v_as_3492_, v_sz_3493_, v___x_3529_, v___x_3527_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
return v___x_3530_;
}
}
else
{
lean_object* v_a_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3539_; 
lean_dec(v___x_3519_);
lean_del_object(v___x_3509_);
lean_dec(v___x_3491_);
lean_dec_ref(v___x_3490_);
v_a_3532_ = lean_ctor_get(v___x_3524_, 0);
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3524_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3534_ = v___x_3524_;
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_a_3532_);
lean_dec(v___x_3524_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
lean_object* v___x_3537_; 
if (v_isShared_3535_ == 0)
{
v___x_3537_ = v___x_3534_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_a_3532_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
return v___x_3537_;
}
}
}
}
else
{
lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3547_; 
lean_dec(v_a_3521_);
lean_dec(v___x_3519_);
lean_del_object(v___x_3509_);
lean_dec(v_fst_3506_);
lean_dec(v___x_3491_);
lean_dec_ref(v___x_3490_);
v_a_3540_ = lean_ctor_get(v___x_3522_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3522_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3542_ = v___x_3522_;
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v___x_3522_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3545_; 
if (v_isShared_3543_ == 0)
{
v___x_3545_ = v___x_3542_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_a_3540_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
}
}
}
}
else
{
lean_object* v_a_3548_; lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3555_; 
lean_dec(v___x_3519_);
lean_del_object(v___x_3509_);
lean_dec(v_fst_3506_);
lean_dec(v___x_3491_);
lean_dec_ref(v___x_3490_);
v_a_3548_ = lean_ctor_get(v___x_3520_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3520_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3550_ = v___x_3520_;
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
else
{
lean_inc(v_a_3548_);
lean_dec(v___x_3520_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
lean_object* v___x_3553_; 
if (v_isShared_3551_ == 0)
{
v___x_3553_ = v___x_3550_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v_a_3548_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___boxed(lean_object* v___x_3557_, lean_object* v___x_3558_, lean_object* v_as_3559_, lean_object* v_sz_3560_, lean_object* v_i_3561_, lean_object* v_b_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_){
_start:
{
size_t v_sz_boxed_3571_; size_t v_i_boxed_3572_; lean_object* v_res_3573_; 
v_sz_boxed_3571_ = lean_unbox_usize(v_sz_3560_);
lean_dec(v_sz_3560_);
v_i_boxed_3572_ = lean_unbox_usize(v_i_3561_);
lean_dec(v_i_3561_);
v_res_3573_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7(v___x_3557_, v___x_3558_, v_as_3559_, v_sz_boxed_3571_, v_i_boxed_3572_, v_b_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_);
lean_dec(v___y_3569_);
lean_dec_ref(v___y_3568_);
lean_dec(v___y_3567_);
lean_dec_ref(v___y_3566_);
lean_dec(v___y_3565_);
lean_dec_ref(v___y_3564_);
lean_dec(v___y_3563_);
lean_dec_ref(v_as_3559_);
return v_res_3573_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0___redArg(lean_object* v_a_3574_, lean_object* v_x_3575_){
_start:
{
if (lean_obj_tag(v_x_3575_) == 0)
{
uint8_t v___x_3576_; 
v___x_3576_ = 0;
return v___x_3576_;
}
else
{
lean_object* v_key_3577_; lean_object* v_tail_3578_; uint8_t v___x_3579_; 
v_key_3577_ = lean_ctor_get(v_x_3575_, 0);
v_tail_3578_ = lean_ctor_get(v_x_3575_, 2);
v___x_3579_ = l_Lean_instBEqFVarId_beq(v_key_3577_, v_a_3574_);
if (v___x_3579_ == 0)
{
v_x_3575_ = v_tail_3578_;
goto _start;
}
else
{
return v___x_3579_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0___redArg___boxed(lean_object* v_a_3581_, lean_object* v_x_3582_){
_start:
{
uint8_t v_res_3583_; lean_object* v_r_3584_; 
v_res_3583_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0___redArg(v_a_3581_, v_x_3582_);
lean_dec(v_x_3582_);
lean_dec(v_a_3581_);
v_r_3584_ = lean_box(v_res_3583_);
return v_r_3584_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1_spec__5_spec__10___redArg(lean_object* v_x_3585_, lean_object* v_x_3586_){
_start:
{
if (lean_obj_tag(v_x_3586_) == 0)
{
return v_x_3585_;
}
else
{
lean_object* v_key_3587_; lean_object* v_value_3588_; lean_object* v_tail_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3612_; 
v_key_3587_ = lean_ctor_get(v_x_3586_, 0);
v_value_3588_ = lean_ctor_get(v_x_3586_, 1);
v_tail_3589_ = lean_ctor_get(v_x_3586_, 2);
v_isSharedCheck_3612_ = !lean_is_exclusive(v_x_3586_);
if (v_isSharedCheck_3612_ == 0)
{
v___x_3591_ = v_x_3586_;
v_isShared_3592_ = v_isSharedCheck_3612_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_tail_3589_);
lean_inc(v_value_3588_);
lean_inc(v_key_3587_);
lean_dec(v_x_3586_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3612_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
lean_object* v___x_3593_; uint64_t v___x_3594_; uint64_t v___x_3595_; uint64_t v___x_3596_; uint64_t v_fold_3597_; uint64_t v___x_3598_; uint64_t v___x_3599_; uint64_t v___x_3600_; size_t v___x_3601_; size_t v___x_3602_; size_t v___x_3603_; size_t v___x_3604_; size_t v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3608_; 
v___x_3593_ = lean_array_get_size(v_x_3585_);
v___x_3594_ = l_Lean_instHashableFVarId_hash(v_key_3587_);
v___x_3595_ = 32ULL;
v___x_3596_ = lean_uint64_shift_right(v___x_3594_, v___x_3595_);
v_fold_3597_ = lean_uint64_xor(v___x_3594_, v___x_3596_);
v___x_3598_ = 16ULL;
v___x_3599_ = lean_uint64_shift_right(v_fold_3597_, v___x_3598_);
v___x_3600_ = lean_uint64_xor(v_fold_3597_, v___x_3599_);
v___x_3601_ = lean_uint64_to_usize(v___x_3600_);
v___x_3602_ = lean_usize_of_nat(v___x_3593_);
v___x_3603_ = ((size_t)1ULL);
v___x_3604_ = lean_usize_sub(v___x_3602_, v___x_3603_);
v___x_3605_ = lean_usize_land(v___x_3601_, v___x_3604_);
v___x_3606_ = lean_array_uget_borrowed(v_x_3585_, v___x_3605_);
lean_inc(v___x_3606_);
if (v_isShared_3592_ == 0)
{
lean_ctor_set(v___x_3591_, 2, v___x_3606_);
v___x_3608_ = v___x_3591_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_key_3587_);
lean_ctor_set(v_reuseFailAlloc_3611_, 1, v_value_3588_);
lean_ctor_set(v_reuseFailAlloc_3611_, 2, v___x_3606_);
v___x_3608_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
lean_object* v___x_3609_; 
v___x_3609_ = lean_array_uset(v_x_3585_, v___x_3605_, v___x_3608_);
v_x_3585_ = v___x_3609_;
v_x_3586_ = v_tail_3589_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1_spec__5___redArg(lean_object* v_i_3613_, lean_object* v_source_3614_, lean_object* v_target_3615_){
_start:
{
lean_object* v___x_3616_; uint8_t v___x_3617_; 
v___x_3616_ = lean_array_get_size(v_source_3614_);
v___x_3617_ = lean_nat_dec_lt(v_i_3613_, v___x_3616_);
if (v___x_3617_ == 0)
{
lean_dec_ref(v_source_3614_);
lean_dec(v_i_3613_);
return v_target_3615_;
}
else
{
lean_object* v_es_3618_; lean_object* v___x_3619_; lean_object* v_source_3620_; lean_object* v_target_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; 
v_es_3618_ = lean_array_fget(v_source_3614_, v_i_3613_);
v___x_3619_ = lean_box(0);
v_source_3620_ = lean_array_fset(v_source_3614_, v_i_3613_, v___x_3619_);
v_target_3621_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1_spec__5_spec__10___redArg(v_target_3615_, v_es_3618_);
v___x_3622_ = lean_unsigned_to_nat(1u);
v___x_3623_ = lean_nat_add(v_i_3613_, v___x_3622_);
lean_dec(v_i_3613_);
v_i_3613_ = v___x_3623_;
v_source_3614_ = v_source_3620_;
v_target_3615_ = v_target_3621_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1___redArg(lean_object* v_data_3625_){
_start:
{
lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v_nbuckets_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; 
v___x_3626_ = lean_array_get_size(v_data_3625_);
v___x_3627_ = lean_unsigned_to_nat(2u);
v_nbuckets_3628_ = lean_nat_mul(v___x_3626_, v___x_3627_);
v___x_3629_ = lean_unsigned_to_nat(0u);
v___x_3630_ = lean_box(0);
v___x_3631_ = lean_mk_array(v_nbuckets_3628_, v___x_3630_);
v___x_3632_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1_spec__5___redArg(v___x_3629_, v_data_3625_, v___x_3631_);
return v___x_3632_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__2___redArg(lean_object* v_a_3633_, lean_object* v_b_3634_, lean_object* v_x_3635_){
_start:
{
if (lean_obj_tag(v_x_3635_) == 0)
{
lean_dec(v_b_3634_);
lean_dec(v_a_3633_);
return v_x_3635_;
}
else
{
lean_object* v_key_3636_; lean_object* v_value_3637_; lean_object* v_tail_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3650_; 
v_key_3636_ = lean_ctor_get(v_x_3635_, 0);
v_value_3637_ = lean_ctor_get(v_x_3635_, 1);
v_tail_3638_ = lean_ctor_get(v_x_3635_, 2);
v_isSharedCheck_3650_ = !lean_is_exclusive(v_x_3635_);
if (v_isSharedCheck_3650_ == 0)
{
v___x_3640_ = v_x_3635_;
v_isShared_3641_ = v_isSharedCheck_3650_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_tail_3638_);
lean_inc(v_value_3637_);
lean_inc(v_key_3636_);
lean_dec(v_x_3635_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3650_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
uint8_t v___x_3642_; 
v___x_3642_ = l_Lean_instBEqFVarId_beq(v_key_3636_, v_a_3633_);
if (v___x_3642_ == 0)
{
lean_object* v___x_3643_; lean_object* v___x_3645_; 
v___x_3643_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__2___redArg(v_a_3633_, v_b_3634_, v_tail_3638_);
if (v_isShared_3641_ == 0)
{
lean_ctor_set(v___x_3640_, 2, v___x_3643_);
v___x_3645_ = v___x_3640_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v_key_3636_);
lean_ctor_set(v_reuseFailAlloc_3646_, 1, v_value_3637_);
lean_ctor_set(v_reuseFailAlloc_3646_, 2, v___x_3643_);
v___x_3645_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
return v___x_3645_;
}
}
else
{
lean_object* v___x_3648_; 
lean_dec(v_value_3637_);
lean_dec(v_key_3636_);
if (v_isShared_3641_ == 0)
{
lean_ctor_set(v___x_3640_, 1, v_b_3634_);
lean_ctor_set(v___x_3640_, 0, v_a_3633_);
v___x_3648_ = v___x_3640_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v_a_3633_);
lean_ctor_set(v_reuseFailAlloc_3649_, 1, v_b_3634_);
lean_ctor_set(v_reuseFailAlloc_3649_, 2, v_tail_3638_);
v___x_3648_ = v_reuseFailAlloc_3649_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
return v___x_3648_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0___redArg(lean_object* v_m_3651_, lean_object* v_a_3652_, lean_object* v_b_3653_){
_start:
{
lean_object* v_size_3654_; lean_object* v_buckets_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3698_; 
v_size_3654_ = lean_ctor_get(v_m_3651_, 0);
v_buckets_3655_ = lean_ctor_get(v_m_3651_, 1);
v_isSharedCheck_3698_ = !lean_is_exclusive(v_m_3651_);
if (v_isSharedCheck_3698_ == 0)
{
v___x_3657_ = v_m_3651_;
v_isShared_3658_ = v_isSharedCheck_3698_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_buckets_3655_);
lean_inc(v_size_3654_);
lean_dec(v_m_3651_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3698_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v___x_3659_; uint64_t v___x_3660_; uint64_t v___x_3661_; uint64_t v___x_3662_; uint64_t v_fold_3663_; uint64_t v___x_3664_; uint64_t v___x_3665_; uint64_t v___x_3666_; size_t v___x_3667_; size_t v___x_3668_; size_t v___x_3669_; size_t v___x_3670_; size_t v___x_3671_; lean_object* v_bkt_3672_; uint8_t v___x_3673_; 
v___x_3659_ = lean_array_get_size(v_buckets_3655_);
v___x_3660_ = l_Lean_instHashableFVarId_hash(v_a_3652_);
v___x_3661_ = 32ULL;
v___x_3662_ = lean_uint64_shift_right(v___x_3660_, v___x_3661_);
v_fold_3663_ = lean_uint64_xor(v___x_3660_, v___x_3662_);
v___x_3664_ = 16ULL;
v___x_3665_ = lean_uint64_shift_right(v_fold_3663_, v___x_3664_);
v___x_3666_ = lean_uint64_xor(v_fold_3663_, v___x_3665_);
v___x_3667_ = lean_uint64_to_usize(v___x_3666_);
v___x_3668_ = lean_usize_of_nat(v___x_3659_);
v___x_3669_ = ((size_t)1ULL);
v___x_3670_ = lean_usize_sub(v___x_3668_, v___x_3669_);
v___x_3671_ = lean_usize_land(v___x_3667_, v___x_3670_);
v_bkt_3672_ = lean_array_uget_borrowed(v_buckets_3655_, v___x_3671_);
v___x_3673_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0___redArg(v_a_3652_, v_bkt_3672_);
if (v___x_3673_ == 0)
{
lean_object* v___x_3674_; lean_object* v_size_x27_3675_; lean_object* v___x_3676_; lean_object* v_buckets_x27_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; uint8_t v___x_3683_; 
v___x_3674_ = lean_unsigned_to_nat(1u);
v_size_x27_3675_ = lean_nat_add(v_size_3654_, v___x_3674_);
lean_dec(v_size_3654_);
lean_inc(v_bkt_3672_);
v___x_3676_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3676_, 0, v_a_3652_);
lean_ctor_set(v___x_3676_, 1, v_b_3653_);
lean_ctor_set(v___x_3676_, 2, v_bkt_3672_);
v_buckets_x27_3677_ = lean_array_uset(v_buckets_3655_, v___x_3671_, v___x_3676_);
v___x_3678_ = lean_unsigned_to_nat(4u);
v___x_3679_ = lean_nat_mul(v_size_x27_3675_, v___x_3678_);
v___x_3680_ = lean_unsigned_to_nat(3u);
v___x_3681_ = lean_nat_div(v___x_3679_, v___x_3680_);
lean_dec(v___x_3679_);
v___x_3682_ = lean_array_get_size(v_buckets_x27_3677_);
v___x_3683_ = lean_nat_dec_le(v___x_3681_, v___x_3682_);
lean_dec(v___x_3681_);
if (v___x_3683_ == 0)
{
lean_object* v_val_3684_; lean_object* v___x_3686_; 
v_val_3684_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1___redArg(v_buckets_x27_3677_);
if (v_isShared_3658_ == 0)
{
lean_ctor_set(v___x_3657_, 1, v_val_3684_);
lean_ctor_set(v___x_3657_, 0, v_size_x27_3675_);
v___x_3686_ = v___x_3657_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_size_x27_3675_);
lean_ctor_set(v_reuseFailAlloc_3687_, 1, v_val_3684_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
return v___x_3686_;
}
}
else
{
lean_object* v___x_3689_; 
if (v_isShared_3658_ == 0)
{
lean_ctor_set(v___x_3657_, 1, v_buckets_x27_3677_);
lean_ctor_set(v___x_3657_, 0, v_size_x27_3675_);
v___x_3689_ = v___x_3657_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v_size_x27_3675_);
lean_ctor_set(v_reuseFailAlloc_3690_, 1, v_buckets_x27_3677_);
v___x_3689_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
return v___x_3689_;
}
}
}
else
{
lean_object* v___x_3691_; lean_object* v_buckets_x27_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3696_; 
lean_inc(v_bkt_3672_);
v___x_3691_ = lean_box(0);
v_buckets_x27_3692_ = lean_array_uset(v_buckets_3655_, v___x_3671_, v___x_3691_);
v___x_3693_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__2___redArg(v_a_3652_, v_b_3653_, v_bkt_3672_);
v___x_3694_ = lean_array_uset(v_buckets_x27_3692_, v___x_3671_, v___x_3693_);
if (v_isShared_3658_ == 0)
{
lean_ctor_set(v___x_3657_, 1, v___x_3694_);
v___x_3696_ = v___x_3657_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_size_3654_);
lean_ctor_set(v_reuseFailAlloc_3697_, 1, v___x_3694_);
v___x_3696_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
return v___x_3696_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1___redArg(lean_object* v_as_3699_, size_t v_sz_3700_, size_t v_i_3701_, lean_object* v_b_3702_){
_start:
{
uint8_t v___x_3704_; 
v___x_3704_ = lean_usize_dec_lt(v_i_3701_, v_sz_3700_);
if (v___x_3704_ == 0)
{
lean_object* v___x_3705_; 
v___x_3705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3705_, 0, v_b_3702_);
return v___x_3705_;
}
else
{
lean_object* v_fst_3706_; lean_object* v_snd_3707_; lean_object* v___x_3709_; uint8_t v_isShared_3710_; uint8_t v_isSharedCheck_3723_; 
v_fst_3706_ = lean_ctor_get(v_b_3702_, 0);
v_snd_3707_ = lean_ctor_get(v_b_3702_, 1);
v_isSharedCheck_3723_ = !lean_is_exclusive(v_b_3702_);
if (v_isSharedCheck_3723_ == 0)
{
v___x_3709_ = v_b_3702_;
v_isShared_3710_ = v_isSharedCheck_3723_;
goto v_resetjp_3708_;
}
else
{
lean_inc(v_snd_3707_);
lean_inc(v_fst_3706_);
lean_dec(v_b_3702_);
v___x_3709_ = lean_box(0);
v_isShared_3710_ = v_isSharedCheck_3723_;
goto v_resetjp_3708_;
}
v_resetjp_3708_:
{
lean_object* v_a_3711_; lean_object* v_fvar_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3718_; 
v_a_3711_ = lean_array_uget_borrowed(v_as_3699_, v_i_3701_);
v_fvar_3712_ = lean_ctor_get(v_a_3711_, 0);
v___x_3713_ = l_Lean_Expr_fvarId_x21(v_fvar_3712_);
lean_inc(v_snd_3707_);
v___x_3714_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0___redArg(v_fst_3706_, v___x_3713_, v_snd_3707_);
v___x_3715_ = lean_unsigned_to_nat(1u);
v___x_3716_ = lean_nat_add(v_snd_3707_, v___x_3715_);
lean_dec(v_snd_3707_);
if (v_isShared_3710_ == 0)
{
lean_ctor_set(v___x_3709_, 1, v___x_3716_);
lean_ctor_set(v___x_3709_, 0, v___x_3714_);
v___x_3718_ = v___x_3709_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v___x_3714_);
lean_ctor_set(v_reuseFailAlloc_3722_, 1, v___x_3716_);
v___x_3718_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
size_t v___x_3719_; size_t v___x_3720_; 
v___x_3719_ = ((size_t)1ULL);
v___x_3720_ = lean_usize_add(v_i_3701_, v___x_3719_);
v_i_3701_ = v___x_3720_;
v_b_3702_ = v___x_3718_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1___redArg___boxed(lean_object* v_as_3724_, lean_object* v_sz_3725_, lean_object* v_i_3726_, lean_object* v_b_3727_, lean_object* v___y_3728_){
_start:
{
size_t v_sz_boxed_3729_; size_t v_i_boxed_3730_; lean_object* v_res_3731_; 
v_sz_boxed_3729_ = lean_unbox_usize(v_sz_3725_);
lean_dec(v_sz_3725_);
v_i_boxed_3730_ = lean_unbox_usize(v_i_3726_);
lean_dec(v_i_3726_);
v_res_3731_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1___redArg(v_as_3724_, v_sz_boxed_3729_, v_i_boxed_3730_, v_b_3727_);
lean_dec_ref(v_as_3724_);
return v_res_3731_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__0(void){
_start:
{
lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; 
v___x_3732_ = lean_box(0);
v___x_3733_ = lean_unsigned_to_nat(16u);
v___x_3734_ = lean_mk_array(v___x_3733_, v___x_3732_);
return v___x_3734_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__1(void){
_start:
{
lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; 
v___x_3735_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__0, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__0_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__0);
v___x_3736_ = lean_unsigned_to_nat(0u);
v___x_3737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3737_, 0, v___x_3736_);
lean_ctor_set(v___x_3737_, 1, v___x_3735_);
return v___x_3737_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__2(void){
_start:
{
lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; 
v___x_3738_ = lean_unsigned_to_nat(0u);
v___x_3739_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__1, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__1_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__1);
v___x_3740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3740_, 0, v___x_3739_);
lean_ctor_set(v___x_3740_, 1, v___x_3738_);
return v___x_3740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets(lean_object* v_e_3741_, lean_object* v_a_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_){
_start:
{
lean_object* v___x_3750_; lean_object* v_decls_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; uint8_t v___x_3754_; 
v___x_3750_ = lean_st_ref_get(v_a_3742_);
v_decls_3751_ = lean_ctor_get(v___x_3750_, 3);
lean_inc_ref(v_decls_3751_);
lean_dec(v___x_3750_);
v___x_3752_ = lean_array_get_size(v_decls_3751_);
v___x_3753_ = lean_unsigned_to_nat(0u);
v___x_3754_ = lean_nat_dec_eq(v___x_3752_, v___x_3753_);
if (v___x_3754_ == 0)
{
lean_object* v___x_3755_; lean_object* v___x_3756_; size_t v_sz_3757_; size_t v___x_3758_; lean_object* v___x_3759_; 
v___x_3755_ = lean_unsigned_to_nat(16u);
v___x_3756_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__2);
v_sz_3757_ = lean_array_size(v_decls_3751_);
v___x_3758_ = ((size_t)0ULL);
v___x_3759_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1___redArg(v_decls_3751_, v_sz_3757_, v___x_3758_, v___x_3756_);
if (lean_obj_tag(v___x_3759_) == 0)
{
lean_object* v_a_3760_; lean_object* v_fst_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3812_; 
v_a_3760_ = lean_ctor_get(v___x_3759_, 0);
lean_inc(v_a_3760_);
lean_dec_ref_known(v___x_3759_, 1);
v_fst_3761_ = lean_ctor_get(v_a_3760_, 0);
v_isSharedCheck_3812_ = !lean_is_exclusive(v_a_3760_);
if (v_isSharedCheck_3812_ == 0)
{
lean_object* v_unused_3813_; 
v_unused_3813_ = lean_ctor_get(v_a_3760_, 1);
lean_dec(v_unused_3813_);
v___x_3763_ = v_a_3760_;
v_isShared_3764_ = v_isSharedCheck_3812_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_fst_3761_);
lean_dec(v_a_3760_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3812_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v_a_3766_; lean_object* v___x_3790_; lean_object* v___x_3791_; uint8_t v_debug_3792_; lean_object* v_env_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___f_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; 
v___x_3790_ = lean_st_ref_get(v_a_3744_);
v___x_3791_ = lean_st_ref_get(v_a_3748_);
v_debug_3792_ = lean_ctor_get_uint8(v___x_3790_, sizeof(void*)*11);
lean_dec(v___x_3790_);
v_env_3793_ = lean_ctor_get(v___x_3791_, 0);
lean_inc_ref(v_env_3793_);
lean_dec(v___x_3791_);
v___x_3794_ = lean_box(v_debug_3792_);
v___x_3795_ = lean_box(v___x_3754_);
lean_inc(v_fst_3761_);
v___f_3796_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___lam__0___boxed), 9, 7);
lean_closure_set(v___f_3796_, 0, v_e_3741_);
lean_closure_set(v___f_3796_, 1, v___x_3755_);
lean_closure_set(v___f_3796_, 2, v___x_3753_);
lean_closure_set(v___f_3796_, 3, v_fst_3761_);
lean_closure_set(v___f_3796_, 4, v___x_3752_);
lean_closure_set(v___f_3796_, 5, v___x_3794_);
lean_closure_set(v___f_3796_, 6, v___x_3795_);
v___x_3797_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_3797_, 0, v_env_3793_);
lean_ctor_set_uint8(v___x_3797_, sizeof(void*)*1, v___x_3754_);
lean_ctor_set_uint8(v___x_3797_, sizeof(void*)*1 + 1, v___x_3754_);
v___x_3798_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_3796_, v___x_3797_, v_a_3744_);
if (lean_obj_tag(v___x_3798_) == 0)
{
lean_object* v_a_3799_; 
v_a_3799_ = lean_ctor_get(v___x_3798_, 0);
lean_inc(v_a_3799_);
lean_dec_ref_known(v___x_3798_, 1);
if (lean_obj_tag(v_a_3799_) == 0)
{
lean_object* v___x_3800_; lean_object* v___x_3801_; 
lean_dec_ref_known(v_a_3799_, 1);
v___x_3800_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2);
v___x_3801_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1(v___x_3800_, v_a_3743_, v_a_3744_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_);
if (lean_obj_tag(v___x_3801_) == 0)
{
lean_object* v_a_3802_; 
v_a_3802_ = lean_ctor_get(v___x_3801_, 0);
lean_inc(v_a_3802_);
lean_dec_ref_known(v___x_3801_, 1);
v_a_3766_ = v_a_3802_;
goto v___jp_3765_;
}
else
{
lean_del_object(v___x_3763_);
lean_dec(v_fst_3761_);
lean_dec_ref(v_decls_3751_);
return v___x_3801_;
}
}
else
{
lean_object* v_a_3803_; 
v_a_3803_ = lean_ctor_get(v_a_3799_, 0);
lean_inc(v_a_3803_);
lean_dec_ref_known(v_a_3799_, 1);
v_a_3766_ = v_a_3803_;
goto v___jp_3765_;
}
}
else
{
lean_object* v_a_3804_; lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3811_; 
lean_del_object(v___x_3763_);
lean_dec(v_fst_3761_);
lean_dec_ref(v_decls_3751_);
v_a_3804_ = lean_ctor_get(v___x_3798_, 0);
v_isSharedCheck_3811_ = !lean_is_exclusive(v___x_3798_);
if (v_isSharedCheck_3811_ == 0)
{
v___x_3806_ = v___x_3798_;
v_isShared_3807_ = v_isSharedCheck_3811_;
goto v_resetjp_3805_;
}
else
{
lean_inc(v_a_3804_);
lean_dec(v___x_3798_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3811_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
lean_object* v___x_3809_; 
if (v_isShared_3807_ == 0)
{
v___x_3809_ = v___x_3806_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v_a_3804_);
v___x_3809_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
return v___x_3809_;
}
}
}
v___jp_3765_:
{
lean_object* v___x_3767_; lean_object* v___x_3769_; 
v___x_3767_ = l_Array_reverse___redArg(v_decls_3751_);
if (v_isShared_3764_ == 0)
{
lean_ctor_set(v___x_3763_, 1, v___x_3752_);
lean_ctor_set(v___x_3763_, 0, v_a_3766_);
v___x_3769_ = v___x_3763_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_a_3766_);
lean_ctor_set(v_reuseFailAlloc_3789_, 1, v___x_3752_);
v___x_3769_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
size_t v_sz_3770_; lean_object* v___x_3771_; 
v_sz_3770_ = lean_array_size(v___x_3767_);
v___x_3771_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7(v_fst_3761_, v___x_3752_, v___x_3767_, v_sz_3770_, v___x_3758_, v___x_3769_, v_a_3742_, v_a_3743_, v_a_3744_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_);
lean_dec_ref(v___x_3767_);
if (lean_obj_tag(v___x_3771_) == 0)
{
lean_object* v_a_3772_; lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3780_; 
v_a_3772_ = lean_ctor_get(v___x_3771_, 0);
v_isSharedCheck_3780_ = !lean_is_exclusive(v___x_3771_);
if (v_isSharedCheck_3780_ == 0)
{
v___x_3774_ = v___x_3771_;
v_isShared_3775_ = v_isSharedCheck_3780_;
goto v_resetjp_3773_;
}
else
{
lean_inc(v_a_3772_);
lean_dec(v___x_3771_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3780_;
goto v_resetjp_3773_;
}
v_resetjp_3773_:
{
lean_object* v_fst_3776_; lean_object* v___x_3778_; 
v_fst_3776_ = lean_ctor_get(v_a_3772_, 0);
lean_inc(v_fst_3776_);
lean_dec(v_a_3772_);
if (v_isShared_3775_ == 0)
{
lean_ctor_set(v___x_3774_, 0, v_fst_3776_);
v___x_3778_ = v___x_3774_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v_fst_3776_);
v___x_3778_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
return v___x_3778_;
}
}
}
else
{
lean_object* v_a_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3788_; 
v_a_3781_ = lean_ctor_get(v___x_3771_, 0);
v_isSharedCheck_3788_ = !lean_is_exclusive(v___x_3771_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3783_ = v___x_3771_;
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_a_3781_);
lean_dec(v___x_3771_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
lean_object* v___x_3786_; 
if (v_isShared_3784_ == 0)
{
v___x_3786_ = v___x_3783_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v_a_3781_);
v___x_3786_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
return v___x_3786_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3821_; 
lean_dec_ref(v_decls_3751_);
lean_dec_ref(v_e_3741_);
v_a_3814_ = lean_ctor_get(v___x_3759_, 0);
v_isSharedCheck_3821_ = !lean_is_exclusive(v___x_3759_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3816_ = v___x_3759_;
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_a_3814_);
lean_dec(v___x_3759_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
lean_object* v___x_3819_; 
if (v_isShared_3817_ == 0)
{
v___x_3819_ = v___x_3816_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v_a_3814_);
v___x_3819_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
return v___x_3819_;
}
}
}
}
else
{
lean_object* v___x_3822_; 
lean_dec_ref(v_decls_3751_);
v___x_3822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3822_, 0, v_e_3741_);
return v___x_3822_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___boxed(lean_object* v_e_3823_, lean_object* v_a_3824_, lean_object* v_a_3825_, lean_object* v_a_3826_, lean_object* v_a_3827_, lean_object* v_a_3828_, lean_object* v_a_3829_, lean_object* v_a_3830_, lean_object* v_a_3831_){
_start:
{
lean_object* v_res_3832_; 
v_res_3832_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets(v_e_3823_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_, v_a_3828_, v_a_3829_, v_a_3830_);
lean_dec(v_a_3830_);
lean_dec_ref(v_a_3829_);
lean_dec(v_a_3828_);
lean_dec_ref(v_a_3827_);
lean_dec(v_a_3826_);
lean_dec_ref(v_a_3825_);
lean_dec(v_a_3824_);
return v_res_3832_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0(lean_object* v_00_u03b2_3833_, lean_object* v_m_3834_, lean_object* v_a_3835_, lean_object* v_b_3836_){
_start:
{
lean_object* v___x_3837_; 
v___x_3837_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0___redArg(v_m_3834_, v_a_3835_, v_b_3836_);
return v___x_3837_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1(lean_object* v_as_3838_, size_t v_sz_3839_, size_t v_i_3840_, lean_object* v_b_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_){
_start:
{
lean_object* v___x_3850_; 
v___x_3850_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1___redArg(v_as_3838_, v_sz_3839_, v_i_3840_, v_b_3841_);
return v___x_3850_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1___boxed(lean_object* v_as_3851_, lean_object* v_sz_3852_, lean_object* v_i_3853_, lean_object* v_b_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_){
_start:
{
size_t v_sz_boxed_3863_; size_t v_i_boxed_3864_; lean_object* v_res_3865_; 
v_sz_boxed_3863_ = lean_unbox_usize(v_sz_3852_);
lean_dec(v_sz_3852_);
v_i_boxed_3864_ = lean_unbox_usize(v_i_3853_);
lean_dec(v_i_3853_);
v_res_3865_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1(v_as_3851_, v_sz_boxed_3863_, v_i_boxed_3864_, v_b_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
lean_dec(v___y_3861_);
lean_dec_ref(v___y_3860_);
lean_dec(v___y_3859_);
lean_dec_ref(v___y_3858_);
lean_dec(v___y_3857_);
lean_dec_ref(v___y_3856_);
lean_dec(v___y_3855_);
lean_dec_ref(v_as_3851_);
return v_res_3865_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2(lean_object* v_00_u03b2_3866_, lean_object* v_m_3867_, lean_object* v_a_3868_){
_start:
{
lean_object* v___x_3869_; 
v___x_3869_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___redArg(v_m_3867_, v_a_3868_);
return v___x_3869_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___boxed(lean_object* v_00_u03b2_3870_, lean_object* v_m_3871_, lean_object* v_a_3872_){
_start:
{
lean_object* v_res_3873_; 
v_res_3873_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2(v_00_u03b2_3870_, v_m_3871_, v_a_3872_);
lean_dec(v_a_3872_);
lean_dec_ref(v_m_3871_);
return v_res_3873_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0(lean_object* v_00_u03b2_3874_, lean_object* v_a_3875_, lean_object* v_x_3876_){
_start:
{
uint8_t v___x_3877_; 
v___x_3877_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0___redArg(v_a_3875_, v_x_3876_);
return v___x_3877_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3878_, lean_object* v_a_3879_, lean_object* v_x_3880_){
_start:
{
uint8_t v_res_3881_; lean_object* v_r_3882_; 
v_res_3881_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0(v_00_u03b2_3878_, v_a_3879_, v_x_3880_);
lean_dec(v_x_3880_);
lean_dec(v_a_3879_);
v_r_3882_ = lean_box(v_res_3881_);
return v_r_3882_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1(lean_object* v_00_u03b2_3883_, lean_object* v_data_3884_){
_start:
{
lean_object* v___x_3885_; 
v___x_3885_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1___redArg(v_data_3884_);
return v___x_3885_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__2(lean_object* v_00_u03b2_3886_, lean_object* v_a_3887_, lean_object* v_b_3888_, lean_object* v_x_3889_){
_start:
{
lean_object* v___x_3890_; 
v___x_3890_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__2___redArg(v_a_3887_, v_b_3888_, v_x_3889_);
return v___x_3890_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2_spec__5(lean_object* v_00_u03b2_3891_, lean_object* v_a_3892_, lean_object* v_x_3893_){
_start:
{
lean_object* v___x_3894_; 
v___x_3894_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2_spec__5___redArg(v_a_3892_, v_x_3893_);
return v___x_3894_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3895_, lean_object* v_a_3896_, lean_object* v_x_3897_){
_start:
{
lean_object* v_res_3898_; 
v_res_3898_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2_spec__5(v_00_u03b2_3895_, v_a_3896_, v_x_3897_);
lean_dec(v_x_3897_);
lean_dec(v_a_3896_);
return v_res_3898_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_3899_, lean_object* v_i_3900_, lean_object* v_source_3901_, lean_object* v_target_3902_){
_start:
{
lean_object* v___x_3903_; 
v___x_3903_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1_spec__5___redArg(v_i_3900_, v_source_3901_, v_target_3902_);
return v___x_3903_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1_spec__5_spec__10(lean_object* v_00_u03b2_3904_, lean_object* v_x_3905_, lean_object* v_x_3906_){
_start:
{
lean_object* v___x_3907_; 
v___x_3907_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1_spec__5_spec__10___redArg(v_x_3905_, v_x_3906_);
return v___x_3907_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0___redArg(lean_object* v_msg_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_){
_start:
{
lean_object* v_ref_3914_; lean_object* v___x_3915_; lean_object* v_a_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3924_; 
v_ref_3914_ = lean_ctor_get(v___y_3911_, 5);
v___x_3915_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5_spec__5(v_msg_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_);
v_a_3916_ = lean_ctor_get(v___x_3915_, 0);
v_isSharedCheck_3924_ = !lean_is_exclusive(v___x_3915_);
if (v_isSharedCheck_3924_ == 0)
{
v___x_3918_ = v___x_3915_;
v_isShared_3919_ = v_isSharedCheck_3924_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_a_3916_);
lean_dec(v___x_3915_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3924_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
lean_object* v___x_3920_; lean_object* v___x_3922_; 
lean_inc(v_ref_3914_);
v___x_3920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3920_, 0, v_ref_3914_);
lean_ctor_set(v___x_3920_, 1, v_a_3916_);
if (v_isShared_3919_ == 0)
{
lean_ctor_set_tag(v___x_3918_, 1);
lean_ctor_set(v___x_3918_, 0, v___x_3920_);
v___x_3922_ = v___x_3918_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v___x_3920_);
v___x_3922_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
return v___x_3922_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0___redArg___boxed(lean_object* v_msg_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_){
_start:
{
lean_object* v_res_3931_; 
v_res_3931_ = l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0___redArg(v_msg_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_);
lean_dec(v___y_3929_);
lean_dec_ref(v___y_3928_);
lean_dec(v___y_3927_);
lean_dec_ref(v___y_3926_);
return v_res_3931_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_liftLets___closed__0(void){
_start:
{
lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; 
v___x_3932_ = lean_box(0);
v___x_3933_ = lean_unsigned_to_nat(16u);
v___x_3934_ = lean_mk_array(v___x_3933_, v___x_3932_);
return v___x_3934_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_liftLets___closed__1(void){
_start:
{
lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; 
v___x_3935_ = lean_obj_once(&l_Lean_Meta_Sym_liftLets___closed__0, &l_Lean_Meta_Sym_liftLets___closed__0_once, _init_l_Lean_Meta_Sym_liftLets___closed__0);
v___x_3936_ = lean_unsigned_to_nat(0u);
v___x_3937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3937_, 0, v___x_3936_);
lean_ctor_set(v___x_3937_, 1, v___x_3935_);
return v___x_3937_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_liftLets___closed__3(void){
_start:
{
lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; 
v___x_3940_ = ((lean_object*)(l_Lean_Meta_Sym_liftLets___closed__2));
v___x_3941_ = lean_obj_once(&l_Lean_Meta_Sym_liftLets___closed__1, &l_Lean_Meta_Sym_liftLets___closed__1_once, _init_l_Lean_Meta_Sym_liftLets___closed__1);
v___x_3942_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3942_, 0, v___x_3941_);
lean_ctor_set(v___x_3942_, 1, v___x_3941_);
lean_ctor_set(v___x_3942_, 2, v___x_3941_);
lean_ctor_set(v___x_3942_, 3, v___x_3940_);
lean_ctor_set(v___x_3942_, 4, v___x_3941_);
return v___x_3942_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_liftLets___closed__5(void){
_start:
{
lean_object* v___x_3944_; lean_object* v___x_3945_; 
v___x_3944_ = ((lean_object*)(l_Lean_Meta_Sym_liftLets___closed__4));
v___x_3945_ = l_Lean_stringToMessageData(v___x_3944_);
return v___x_3945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLets(lean_object* v_e_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_){
_start:
{
lean_object* v___y_3955_; lean_object* v___y_3956_; lean_object* v___y_3967_; lean_object* v___y_3968_; lean_object* v___y_3969_; lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v___y_3972_; uint8_t v___x_3979_; 
v___x_3979_ = l_Lean_Expr_hasLooseBVars(v_e_3946_);
if (v___x_3979_ == 0)
{
v___y_3967_ = v_a_3947_;
v___y_3968_ = v_a_3948_;
v___y_3969_ = v_a_3949_;
v___y_3970_ = v_a_3950_;
v___y_3971_ = v_a_3951_;
v___y_3972_ = v_a_3952_;
goto v___jp_3966_;
}
else
{
lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v_a_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_3989_; 
lean_dec_ref(v_e_3946_);
v___x_3980_ = lean_obj_once(&l_Lean_Meta_Sym_liftLets___closed__5, &l_Lean_Meta_Sym_liftLets___closed__5_once, _init_l_Lean_Meta_Sym_liftLets___closed__5);
v___x_3981_ = l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0___redArg(v___x_3980_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_);
v_a_3982_ = lean_ctor_get(v___x_3981_, 0);
v_isSharedCheck_3989_ = !lean_is_exclusive(v___x_3981_);
if (v_isSharedCheck_3989_ == 0)
{
v___x_3984_ = v___x_3981_;
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_a_3982_);
lean_dec(v___x_3981_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v___x_3987_; 
if (v_isShared_3985_ == 0)
{
v___x_3987_ = v___x_3984_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v_a_3982_);
v___x_3987_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
return v___x_3987_;
}
}
}
v___jp_3954_:
{
if (lean_obj_tag(v___y_3956_) == 0)
{
lean_object* v_a_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3965_; 
v_a_3957_ = lean_ctor_get(v___y_3956_, 0);
v_isSharedCheck_3965_ = !lean_is_exclusive(v___y_3956_);
if (v_isSharedCheck_3965_ == 0)
{
v___x_3959_ = v___y_3956_;
v_isShared_3960_ = v_isSharedCheck_3965_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_a_3957_);
lean_dec(v___y_3956_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3965_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
lean_object* v___x_3961_; lean_object* v___x_3963_; 
v___x_3961_ = lean_st_ref_get(v___y_3955_);
lean_dec(v___y_3955_);
lean_dec(v___x_3961_);
if (v_isShared_3960_ == 0)
{
v___x_3963_ = v___x_3959_;
goto v_reusejp_3962_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v_a_3957_);
v___x_3963_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3962_;
}
v_reusejp_3962_:
{
return v___x_3963_;
}
}
}
else
{
lean_dec(v___y_3955_);
return v___y_3956_;
}
}
v___jp_3966_:
{
lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; 
v___x_3973_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__3, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__3_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__3);
v___x_3974_ = lean_obj_once(&l_Lean_Meta_Sym_liftLets___closed__3, &l_Lean_Meta_Sym_liftLets___closed__3_once, _init_l_Lean_Meta_Sym_liftLets___closed__3);
v___x_3975_ = lean_st_mk_ref(v___x_3974_);
v___x_3976_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v___x_3973_, v_e_3946_, v___x_3975_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_);
if (lean_obj_tag(v___x_3976_) == 0)
{
lean_object* v_a_3977_; lean_object* v___x_3978_; 
v_a_3977_ = lean_ctor_get(v___x_3976_, 0);
lean_inc(v_a_3977_);
lean_dec_ref_known(v___x_3976_, 1);
v___x_3978_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets(v_a_3977_, v___x_3975_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_);
v___y_3955_ = v___x_3975_;
v___y_3956_ = v___x_3978_;
goto v___jp_3954_;
}
else
{
v___y_3955_ = v___x_3975_;
v___y_3956_ = v___x_3976_;
goto v___jp_3954_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLets___boxed(lean_object* v_e_3990_, lean_object* v_a_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_){
_start:
{
lean_object* v_res_3998_; 
v_res_3998_ = l_Lean_Meta_Sym_liftLets(v_e_3990_, v_a_3991_, v_a_3992_, v_a_3993_, v_a_3994_, v_a_3995_, v_a_3996_);
lean_dec(v_a_3996_);
lean_dec_ref(v_a_3995_);
lean_dec(v_a_3994_);
lean_dec_ref(v_a_3993_);
lean_dec(v_a_3992_);
lean_dec_ref(v_a_3991_);
return v_res_3998_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0(lean_object* v_00_u03b1_3999_, lean_object* v_msg_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_){
_start:
{
lean_object* v___x_4008_; 
v___x_4008_ = l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0___redArg(v_msg_4000_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_);
return v___x_4008_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0___boxed(lean_object* v_00_u03b1_4009_, lean_object* v_msg_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_){
_start:
{
lean_object* v_res_4018_; 
v_res_4018_ = l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0(v_00_u03b1_4009_, v_msg_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_);
lean_dec(v___y_4016_);
lean_dec_ref(v___y_4015_);
lean_dec(v___y_4014_);
lean_dec_ref(v___y_4013_);
lean_dec(v___y_4012_);
lean_dec_ref(v___y_4011_);
return v_res_4018_;
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
