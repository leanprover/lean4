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
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v_nbuckets_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_112_ = lean_array_get_size(v_data_111_);
v___x_113_ = lean_unsigned_to_nat(2u);
v_nbuckets_114_ = lean_nat_mul(v___x_112_, v___x_113_);
v___x_115_ = lean_unsigned_to_nat(0u);
v___x_116_ = lean_box(0);
v___x_117_ = lean_mk_array(v_nbuckets_114_, v___x_116_);
v___x_118_ = lean_array_propagate_mark(v_data_111_, v___x_117_);
v___x_119_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__3_spec__4___redArg(v___x_115_, v_data_111_, v___x_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__4___redArg(lean_object* v_a_120_, lean_object* v_b_121_, lean_object* v_x_122_){
_start:
{
if (lean_obj_tag(v_x_122_) == 0)
{
lean_dec(v_b_121_);
lean_dec_ref(v_a_120_);
return v_x_122_;
}
else
{
lean_object* v_key_123_; lean_object* v_value_124_; lean_object* v_tail_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_139_; 
v_key_123_ = lean_ctor_get(v_x_122_, 0);
v_value_124_ = lean_ctor_get(v_x_122_, 1);
v_tail_125_ = lean_ctor_get(v_x_122_, 2);
v_isSharedCheck_139_ = !lean_is_exclusive(v_x_122_);
if (v_isSharedCheck_139_ == 0)
{
v___x_127_ = v_x_122_;
v_isShared_128_ = v_isSharedCheck_139_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_tail_125_);
lean_inc(v_value_124_);
lean_inc(v_key_123_);
lean_dec(v_x_122_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_139_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
size_t v___x_129_; size_t v___x_130_; uint8_t v___x_131_; 
v___x_129_ = lean_ptr_addr(v_key_123_);
v___x_130_ = lean_ptr_addr(v_a_120_);
v___x_131_ = lean_usize_dec_eq(v___x_129_, v___x_130_);
if (v___x_131_ == 0)
{
lean_object* v___x_132_; lean_object* v___x_134_; 
v___x_132_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__4___redArg(v_a_120_, v_b_121_, v_tail_125_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 2, v___x_132_);
v___x_134_ = v___x_127_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_key_123_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v_value_124_);
lean_ctor_set(v_reuseFailAlloc_135_, 2, v___x_132_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
else
{
lean_object* v___x_137_; 
lean_dec(v_value_124_);
lean_dec(v_key_123_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 1, v_b_121_);
lean_ctor_set(v___x_127_, 0, v_a_120_);
v___x_137_ = v___x_127_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_a_120_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v_b_121_);
lean_ctor_set(v_reuseFailAlloc_138_, 2, v_tail_125_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2___redArg(lean_object* v_a_140_, lean_object* v_x_141_){
_start:
{
if (lean_obj_tag(v_x_141_) == 0)
{
uint8_t v___x_142_; 
v___x_142_ = 0;
return v___x_142_;
}
else
{
lean_object* v_key_143_; lean_object* v_tail_144_; size_t v___x_145_; size_t v___x_146_; uint8_t v___x_147_; 
v_key_143_ = lean_ctor_get(v_x_141_, 0);
v_tail_144_ = lean_ctor_get(v_x_141_, 2);
v___x_145_ = lean_ptr_addr(v_key_143_);
v___x_146_ = lean_ptr_addr(v_a_140_);
v___x_147_ = lean_usize_dec_eq(v___x_145_, v___x_146_);
if (v___x_147_ == 0)
{
v_x_141_ = v_tail_144_;
goto _start;
}
else
{
return v___x_147_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2___redArg___boxed(lean_object* v_a_149_, lean_object* v_x_150_){
_start:
{
uint8_t v_res_151_; lean_object* v_r_152_; 
v_res_151_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2___redArg(v_a_149_, v_x_150_);
lean_dec(v_x_150_);
lean_dec_ref(v_a_149_);
v_r_152_ = lean_box(v_res_151_);
return v_r_152_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1___redArg(lean_object* v_m_153_, lean_object* v_a_154_, lean_object* v_b_155_){
_start:
{
lean_object* v_size_156_; lean_object* v_buckets_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_203_; 
v_size_156_ = lean_ctor_get(v_m_153_, 0);
v_buckets_157_ = lean_ctor_get(v_m_153_, 1);
v_isSharedCheck_203_ = !lean_is_exclusive(v_m_153_);
if (v_isSharedCheck_203_ == 0)
{
v___x_159_ = v_m_153_;
v_isShared_160_ = v_isSharedCheck_203_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_buckets_157_);
lean_inc(v_size_156_);
lean_dec(v_m_153_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_203_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_161_; size_t v___x_162_; size_t v___x_163_; size_t v___x_164_; uint64_t v___x_165_; uint64_t v___x_166_; uint64_t v___x_167_; uint64_t v_fold_168_; uint64_t v___x_169_; uint64_t v___x_170_; uint64_t v___x_171_; size_t v___x_172_; size_t v___x_173_; size_t v___x_174_; size_t v___x_175_; size_t v___x_176_; lean_object* v_bkt_177_; uint8_t v___x_178_; 
v___x_161_ = lean_array_get_size(v_buckets_157_);
v___x_162_ = lean_ptr_addr(v_a_154_);
v___x_163_ = ((size_t)3ULL);
v___x_164_ = lean_usize_shift_right(v___x_162_, v___x_163_);
v___x_165_ = lean_usize_to_uint64(v___x_164_);
v___x_166_ = 32ULL;
v___x_167_ = lean_uint64_shift_right(v___x_165_, v___x_166_);
v_fold_168_ = lean_uint64_xor(v___x_165_, v___x_167_);
v___x_169_ = 16ULL;
v___x_170_ = lean_uint64_shift_right(v_fold_168_, v___x_169_);
v___x_171_ = lean_uint64_xor(v_fold_168_, v___x_170_);
v___x_172_ = lean_uint64_to_usize(v___x_171_);
v___x_173_ = lean_usize_of_nat(v___x_161_);
v___x_174_ = ((size_t)1ULL);
v___x_175_ = lean_usize_sub(v___x_173_, v___x_174_);
v___x_176_ = lean_usize_land(v___x_172_, v___x_175_);
v_bkt_177_ = lean_array_uget_borrowed(v_buckets_157_, v___x_176_);
v___x_178_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2___redArg(v_a_154_, v_bkt_177_);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; lean_object* v_size_x27_180_; lean_object* v___x_181_; lean_object* v_buckets_x27_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_179_ = lean_unsigned_to_nat(1u);
v_size_x27_180_ = lean_nat_add(v_size_156_, v___x_179_);
lean_dec(v_size_156_);
lean_inc(v_bkt_177_);
v___x_181_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_181_, 0, v_a_154_);
lean_ctor_set(v___x_181_, 1, v_b_155_);
lean_ctor_set(v___x_181_, 2, v_bkt_177_);
v_buckets_x27_182_ = lean_array_uset(v_buckets_157_, v___x_176_, v___x_181_);
v___x_183_ = lean_unsigned_to_nat(4u);
v___x_184_ = lean_nat_mul(v_size_x27_180_, v___x_183_);
v___x_185_ = lean_unsigned_to_nat(3u);
v___x_186_ = lean_nat_div(v___x_184_, v___x_185_);
lean_dec(v___x_184_);
v___x_187_ = lean_array_get_size(v_buckets_x27_182_);
v___x_188_ = lean_nat_dec_le(v___x_186_, v___x_187_);
lean_dec(v___x_186_);
if (v___x_188_ == 0)
{
lean_object* v_val_189_; lean_object* v___x_191_; 
v_val_189_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__3___redArg(v_buckets_x27_182_);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 1, v_val_189_);
lean_ctor_set(v___x_159_, 0, v_size_x27_180_);
v___x_191_ = v___x_159_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_size_x27_180_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v_val_189_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
else
{
lean_object* v___x_194_; 
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 1, v_buckets_x27_182_);
lean_ctor_set(v___x_159_, 0, v_size_x27_180_);
v___x_194_ = v___x_159_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_size_x27_180_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v_buckets_x27_182_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
else
{
lean_object* v___x_196_; lean_object* v_buckets_x27_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_201_; 
lean_inc(v_bkt_177_);
v___x_196_ = lean_box(0);
v_buckets_x27_197_ = lean_array_uset(v_buckets_157_, v___x_176_, v___x_196_);
v___x_198_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__4___redArg(v_a_154_, v_b_155_, v_bkt_177_);
v___x_199_ = lean_array_uset(v_buckets_x27_197_, v___x_176_, v___x_198_);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 1, v___x_199_);
v___x_201_ = v___x_159_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_size_156_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v___x_199_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0_spec__0___redArg(lean_object* v_a_204_, lean_object* v_x_205_){
_start:
{
if (lean_obj_tag(v_x_205_) == 0)
{
lean_object* v___x_206_; 
v___x_206_ = lean_box(0);
return v___x_206_;
}
else
{
lean_object* v_key_207_; lean_object* v_value_208_; lean_object* v_tail_209_; size_t v___x_210_; size_t v___x_211_; uint8_t v___x_212_; 
v_key_207_ = lean_ctor_get(v_x_205_, 0);
v_value_208_ = lean_ctor_get(v_x_205_, 1);
v_tail_209_ = lean_ctor_get(v_x_205_, 2);
v___x_210_ = lean_ptr_addr(v_key_207_);
v___x_211_ = lean_ptr_addr(v_a_204_);
v___x_212_ = lean_usize_dec_eq(v___x_210_, v___x_211_);
if (v___x_212_ == 0)
{
v_x_205_ = v_tail_209_;
goto _start;
}
else
{
lean_object* v___x_214_; 
lean_inc(v_value_208_);
v___x_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_214_, 0, v_value_208_);
return v___x_214_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0_spec__0___redArg___boxed(lean_object* v_a_215_, lean_object* v_x_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0_spec__0___redArg(v_a_215_, v_x_216_);
lean_dec(v_x_216_);
lean_dec_ref(v_a_215_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0___redArg(lean_object* v_m_218_, lean_object* v_a_219_){
_start:
{
lean_object* v_buckets_220_; lean_object* v___x_221_; size_t v___x_222_; size_t v___x_223_; size_t v___x_224_; uint64_t v___x_225_; uint64_t v___x_226_; uint64_t v___x_227_; uint64_t v_fold_228_; uint64_t v___x_229_; uint64_t v___x_230_; uint64_t v___x_231_; size_t v___x_232_; size_t v___x_233_; size_t v___x_234_; size_t v___x_235_; size_t v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v_buckets_220_ = lean_ctor_get(v_m_218_, 1);
v___x_221_ = lean_array_get_size(v_buckets_220_);
v___x_222_ = lean_ptr_addr(v_a_219_);
v___x_223_ = ((size_t)3ULL);
v___x_224_ = lean_usize_shift_right(v___x_222_, v___x_223_);
v___x_225_ = lean_usize_to_uint64(v___x_224_);
v___x_226_ = 32ULL;
v___x_227_ = lean_uint64_shift_right(v___x_225_, v___x_226_);
v_fold_228_ = lean_uint64_xor(v___x_225_, v___x_227_);
v___x_229_ = 16ULL;
v___x_230_ = lean_uint64_shift_right(v_fold_228_, v___x_229_);
v___x_231_ = lean_uint64_xor(v_fold_228_, v___x_230_);
v___x_232_ = lean_uint64_to_usize(v___x_231_);
v___x_233_ = lean_usize_of_nat(v___x_221_);
v___x_234_ = ((size_t)1ULL);
v___x_235_ = lean_usize_sub(v___x_233_, v___x_234_);
v___x_236_ = lean_usize_land(v___x_232_, v___x_235_);
v___x_237_ = lean_array_uget_borrowed(v_buckets_220_, v___x_236_);
v___x_238_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0_spec__0___redArg(v_a_219_, v___x_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0___redArg___boxed(lean_object* v_m_239_, lean_object* v_a_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0___redArg(v_m_239_, v_a_240_);
lean_dec_ref(v_a_240_);
lean_dec_ref(v_m_239_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet___lam__0___boxed(lean_object* v_fn_242_, lean_object* v_arg_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet___lam__0(v_fn_242_, v_arg_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_);
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec(v___y_244_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet___boxed(lean_object* v_e_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet(v_e_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec(v_a_256_);
lean_dec_ref(v_a_255_);
lean_dec(v_a_254_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet(lean_object* v_e_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_){
_start:
{
lean_object* v_e_273_; lean_object* v_k_274_; lean_object* v___y_275_; lean_object* v___y_276_; lean_object* v___y_277_; lean_object* v___y_278_; lean_object* v___y_279_; lean_object* v___y_280_; lean_object* v___y_281_; 
switch(lean_obj_tag(v_e_263_))
{
case 8:
{
uint8_t v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
lean_dec_ref_known(v_e_263_, 4);
v___x_317_ = 1;
v___x_318_ = lean_box(v___x_317_);
v___x_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
return v___x_319_;
}
case 5:
{
lean_object* v_fn_320_; lean_object* v_arg_321_; lean_object* v___f_322_; 
v_fn_320_ = lean_ctor_get(v_e_263_, 0);
v_arg_321_ = lean_ctor_get(v_e_263_, 1);
lean_inc_ref(v_arg_321_);
lean_inc_ref(v_fn_320_);
v___f_322_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet___lam__0___boxed), 10, 2);
lean_closure_set(v___f_322_, 0, v_fn_320_);
lean_closure_set(v___f_322_, 1, v_arg_321_);
v_e_273_ = v_e_263_;
v_k_274_ = v___f_322_;
v___y_275_ = v_a_264_;
v___y_276_ = v_a_265_;
v___y_277_ = v_a_266_;
v___y_278_ = v_a_267_;
v___y_279_ = v_a_268_;
v___y_280_ = v_a_269_;
v___y_281_ = v_a_270_;
goto v___jp_272_;
}
case 10:
{
lean_object* v_expr_323_; lean_object* v___x_324_; 
v_expr_323_ = lean_ctor_get(v_e_263_, 1);
lean_inc_ref(v_expr_323_);
v___x_324_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet___boxed), 9, 1);
lean_closure_set(v___x_324_, 0, v_expr_323_);
v_e_273_ = v_e_263_;
v_k_274_ = v___x_324_;
v___y_275_ = v_a_264_;
v___y_276_ = v_a_265_;
v___y_277_ = v_a_266_;
v___y_278_ = v_a_267_;
v___y_279_ = v_a_268_;
v___y_280_ = v_a_269_;
v___y_281_ = v_a_270_;
goto v___jp_272_;
}
case 11:
{
lean_object* v_struct_325_; lean_object* v___x_326_; 
v_struct_325_ = lean_ctor_get(v_e_263_, 2);
lean_inc_ref(v_struct_325_);
v___x_326_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet___boxed), 9, 1);
lean_closure_set(v___x_326_, 0, v_struct_325_);
v_e_273_ = v_e_263_;
v_k_274_ = v___x_326_;
v___y_275_ = v_a_264_;
v___y_276_ = v_a_265_;
v___y_277_ = v_a_266_;
v___y_278_ = v_a_267_;
v___y_279_ = v_a_268_;
v___y_280_ = v_a_269_;
v___y_281_ = v_a_270_;
goto v___jp_272_;
}
default: 
{
uint8_t v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
lean_dec_ref(v_e_263_);
v___x_327_ = 0;
v___x_328_ = lean_box(v___x_327_);
v___x_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
return v___x_329_;
}
}
v___jp_272_:
{
lean_object* v___x_282_; lean_object* v_hasLetCache_283_; lean_object* v___x_284_; 
v___x_282_ = lean_st_ref_get(v___y_275_);
v_hasLetCache_283_ = lean_ctor_get(v___x_282_, 2);
lean_inc_ref(v_hasLetCache_283_);
lean_dec(v___x_282_);
v___x_284_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0___redArg(v_hasLetCache_283_, v_e_273_);
lean_dec_ref(v_hasLetCache_283_);
if (lean_obj_tag(v___x_284_) == 1)
{
lean_object* v_val_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_292_; 
lean_dec_ref(v_k_274_);
lean_dec_ref(v_e_273_);
v_val_285_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_292_ == 0)
{
v___x_287_ = v___x_284_;
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_val_285_);
lean_dec(v___x_284_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_290_; 
if (v_isShared_288_ == 0)
{
lean_ctor_set_tag(v___x_287_, 0);
v___x_290_ = v___x_287_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_val_285_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
else
{
lean_object* v___x_293_; 
lean_dec(v___x_284_);
lean_inc(v___y_281_);
lean_inc_ref(v___y_280_);
lean_inc(v___y_279_);
lean_inc_ref(v___y_278_);
lean_inc(v___y_277_);
lean_inc_ref(v___y_276_);
lean_inc(v___y_275_);
v___x_293_ = lean_apply_8(v_k_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, lean_box(0));
if (lean_obj_tag(v___x_293_) == 0)
{
lean_object* v_a_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_316_; 
v_a_294_ = lean_ctor_get(v___x_293_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_316_ == 0)
{
v___x_296_ = v___x_293_;
v_isShared_297_ = v_isSharedCheck_316_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_a_294_);
lean_dec(v___x_293_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_316_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_298_; lean_object* v_cache_299_; lean_object* v_cacheClosed_300_; lean_object* v_hasLetCache_301_; lean_object* v_decls_302_; lean_object* v_valueMap_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_315_; 
v___x_298_ = lean_st_ref_take(v___y_275_);
v_cache_299_ = lean_ctor_get(v___x_298_, 0);
v_cacheClosed_300_ = lean_ctor_get(v___x_298_, 1);
v_hasLetCache_301_ = lean_ctor_get(v___x_298_, 2);
v_decls_302_ = lean_ctor_get(v___x_298_, 3);
v_valueMap_303_ = lean_ctor_get(v___x_298_, 4);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_315_ == 0)
{
v___x_305_ = v___x_298_;
v_isShared_306_ = v_isSharedCheck_315_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_valueMap_303_);
lean_inc(v_decls_302_);
lean_inc(v_hasLetCache_301_);
lean_inc(v_cacheClosed_300_);
lean_inc(v_cache_299_);
lean_dec(v___x_298_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_315_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_307_; lean_object* v___x_309_; 
lean_inc(v_a_294_);
v___x_307_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1___redArg(v_hasLetCache_301_, v_e_273_, v_a_294_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 2, v___x_307_);
v___x_309_ = v___x_305_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_cache_299_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v_cacheClosed_300_);
lean_ctor_set(v_reuseFailAlloc_314_, 2, v___x_307_);
lean_ctor_set(v_reuseFailAlloc_314_, 3, v_decls_302_);
lean_ctor_set(v_reuseFailAlloc_314_, 4, v_valueMap_303_);
v___x_309_ = v_reuseFailAlloc_314_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
lean_object* v___x_310_; lean_object* v___x_312_; 
v___x_310_ = lean_st_ref_put(v___y_275_, v___x_309_);
if (v_isShared_297_ == 0)
{
v___x_312_ = v___x_296_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_a_294_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_273_);
return v___x_293_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet___lam__0(lean_object* v_fn_330_, lean_object* v_arg_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet(v_fn_330_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
if (lean_obj_tag(v___x_340_) == 0)
{
lean_object* v_a_341_; uint8_t v___x_342_; 
v_a_341_ = lean_ctor_get(v___x_340_, 0);
v___x_342_ = lean_unbox(v_a_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; 
lean_dec_ref_known(v___x_340_, 1);
v___x_343_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet(v_arg_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
return v___x_343_;
}
else
{
lean_dec_ref(v_arg_331_);
return v___x_340_;
}
}
else
{
lean_dec_ref(v_arg_331_);
return v___x_340_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0(lean_object* v_00_u03b2_344_, lean_object* v_m_345_, lean_object* v_a_346_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0___redArg(v_m_345_, v_a_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0___boxed(lean_object* v_00_u03b2_348_, lean_object* v_m_349_, lean_object* v_a_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0(v_00_u03b2_348_, v_m_349_, v_a_350_);
lean_dec_ref(v_a_350_);
lean_dec_ref(v_m_349_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1(lean_object* v_00_u03b2_352_, lean_object* v_m_353_, lean_object* v_a_354_, lean_object* v_b_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1___redArg(v_m_353_, v_a_354_, v_b_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0_spec__0(lean_object* v_00_u03b2_357_, lean_object* v_a_358_, lean_object* v_x_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0_spec__0___redArg(v_a_358_, v_x_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0_spec__0___boxed(lean_object* v_00_u03b2_361_, lean_object* v_a_362_, lean_object* v_x_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0_spec__0(v_00_u03b2_361_, v_a_362_, v_x_363_);
lean_dec(v_x_363_);
lean_dec_ref(v_a_362_);
return v_res_364_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2(lean_object* v_00_u03b2_365_, lean_object* v_a_366_, lean_object* v_x_367_){
_start:
{
uint8_t v___x_368_; 
v___x_368_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2___redArg(v_a_366_, v_x_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2___boxed(lean_object* v_00_u03b2_369_, lean_object* v_a_370_, lean_object* v_x_371_){
_start:
{
uint8_t v_res_372_; lean_object* v_r_373_; 
v_res_372_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__2(v_00_u03b2_369_, v_a_370_, v_x_371_);
lean_dec(v_x_371_);
lean_dec_ref(v_a_370_);
v_r_373_ = lean_box(v_res_372_);
return v_r_373_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__3(lean_object* v_00_u03b2_374_, lean_object* v_data_375_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__3___redArg(v_data_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__4(lean_object* v_00_u03b2_377_, lean_object* v_a_378_, lean_object* v_b_379_, lean_object* v_x_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__4___redArg(v_a_378_, v_b_379_, v_x_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_382_, lean_object* v_i_383_, lean_object* v_source_384_, lean_object* v_target_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__3_spec__4___redArg(v_i_383_, v_source_384_, v_target_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_387_, lean_object* v_x_388_, lean_object* v_x_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1_spec__3_spec__4_spec__5___redArg(v_x_388_, v_x_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2___redArg(lean_object* v_fvarId_391_, lean_object* v___y_392_){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = l_Lean_Expr_fvar___override(v_fvarId_391_);
v___x_395_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_394_, v___y_392_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2___redArg___boxed(lean_object* v_fvarId_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2___redArg(v_fvarId_396_, v___y_397_);
lean_dec(v___y_397_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2(lean_object* v_fvarId_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2___redArg(v_fvarId_400_, v___y_403_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2___boxed(lean_object* v_fvarId_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2(v_fvarId_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
lean_dec(v___y_411_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2___redArg(lean_object* v___y_420_){
_start:
{
lean_object* v___x_422_; lean_object* v_ngen_423_; lean_object* v_namePrefix_424_; lean_object* v_idx_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_455_; 
v___x_422_ = lean_st_ref_get(v___y_420_);
v_ngen_423_ = lean_ctor_get(v___x_422_, 2);
lean_inc_ref(v_ngen_423_);
lean_dec(v___x_422_);
v_namePrefix_424_ = lean_ctor_get(v_ngen_423_, 0);
v_idx_425_ = lean_ctor_get(v_ngen_423_, 1);
v_isSharedCheck_455_ = !lean_is_exclusive(v_ngen_423_);
if (v_isSharedCheck_455_ == 0)
{
v___x_427_ = v_ngen_423_;
v_isShared_428_ = v_isSharedCheck_455_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_idx_425_);
lean_inc(v_namePrefix_424_);
lean_dec(v_ngen_423_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_455_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v_r_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_433_; 
lean_inc(v_idx_425_);
lean_inc(v_namePrefix_424_);
v_r_429_ = l_Lean_Name_num___override(v_namePrefix_424_, v_idx_425_);
v___x_430_ = lean_unsigned_to_nat(1u);
v___x_431_ = lean_nat_add(v_idx_425_, v___x_430_);
lean_dec(v_idx_425_);
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 1, v___x_431_);
v___x_433_ = v___x_427_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_namePrefix_424_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v___x_431_);
v___x_433_ = v_reuseFailAlloc_454_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
lean_object* v___x_434_; lean_object* v_env_435_; lean_object* v_nextMacroScope_436_; lean_object* v_auxDeclNGen_437_; lean_object* v_traceState_438_; lean_object* v_cache_439_; lean_object* v_recordedDeps_440_; lean_object* v_messages_441_; lean_object* v_infoState_442_; lean_object* v_snapshotTasks_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_452_; 
v___x_434_ = lean_st_ref_take(v___y_420_);
v_env_435_ = lean_ctor_get(v___x_434_, 0);
v_nextMacroScope_436_ = lean_ctor_get(v___x_434_, 1);
v_auxDeclNGen_437_ = lean_ctor_get(v___x_434_, 3);
v_traceState_438_ = lean_ctor_get(v___x_434_, 4);
v_cache_439_ = lean_ctor_get(v___x_434_, 5);
v_recordedDeps_440_ = lean_ctor_get(v___x_434_, 6);
v_messages_441_ = lean_ctor_get(v___x_434_, 7);
v_infoState_442_ = lean_ctor_get(v___x_434_, 8);
v_snapshotTasks_443_ = lean_ctor_get(v___x_434_, 9);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_452_ == 0)
{
lean_object* v_unused_453_; 
v_unused_453_ = lean_ctor_get(v___x_434_, 2);
lean_dec(v_unused_453_);
v___x_445_ = v___x_434_;
v_isShared_446_ = v_isSharedCheck_452_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_snapshotTasks_443_);
lean_inc(v_infoState_442_);
lean_inc(v_messages_441_);
lean_inc(v_recordedDeps_440_);
lean_inc(v_cache_439_);
lean_inc(v_traceState_438_);
lean_inc(v_auxDeclNGen_437_);
lean_inc(v_nextMacroScope_436_);
lean_inc(v_env_435_);
lean_dec(v___x_434_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_452_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_448_; 
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 2, v___x_433_);
v___x_448_ = v___x_445_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_env_435_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v_nextMacroScope_436_);
lean_ctor_set(v_reuseFailAlloc_451_, 2, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_451_, 3, v_auxDeclNGen_437_);
lean_ctor_set(v_reuseFailAlloc_451_, 4, v_traceState_438_);
lean_ctor_set(v_reuseFailAlloc_451_, 5, v_cache_439_);
lean_ctor_set(v_reuseFailAlloc_451_, 6, v_recordedDeps_440_);
lean_ctor_set(v_reuseFailAlloc_451_, 7, v_messages_441_);
lean_ctor_set(v_reuseFailAlloc_451_, 8, v_infoState_442_);
lean_ctor_set(v_reuseFailAlloc_451_, 9, v_snapshotTasks_443_);
v___x_448_ = v_reuseFailAlloc_451_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = lean_st_ref_put(v___y_420_, v___x_448_);
v___x_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_450_, 0, v_r_429_);
return v___x_450_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2___redArg___boxed(lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2___redArg(v___y_456_);
lean_dec(v___y_456_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1(lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v___x_467_; lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_475_; 
v___x_467_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2___redArg(v___y_465_);
v_a_468_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_475_ == 0)
{
v___x_470_ = v___x_467_;
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_dec(v___x_467_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_473_; 
if (v_isShared_471_ == 0)
{
v___x_473_ = v___x_470_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_a_468_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1___boxed(lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1(v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
lean_dec(v___y_476_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0___redArg(lean_object* v_a_485_, lean_object* v_x_486_){
_start:
{
if (lean_obj_tag(v_x_486_) == 0)
{
lean_object* v___x_487_; 
v___x_487_ = lean_box(0);
return v___x_487_;
}
else
{
lean_object* v_key_488_; lean_object* v_value_489_; lean_object* v_tail_490_; lean_object* v_fst_491_; lean_object* v_snd_492_; lean_object* v_fst_493_; lean_object* v_snd_494_; size_t v___x_495_; size_t v___x_496_; uint8_t v___x_497_; 
v_key_488_ = lean_ctor_get(v_x_486_, 0);
v_value_489_ = lean_ctor_get(v_x_486_, 1);
v_tail_490_ = lean_ctor_get(v_x_486_, 2);
v_fst_491_ = lean_ctor_get(v_key_488_, 0);
v_snd_492_ = lean_ctor_get(v_key_488_, 1);
v_fst_493_ = lean_ctor_get(v_a_485_, 0);
v_snd_494_ = lean_ctor_get(v_a_485_, 1);
v___x_495_ = lean_ptr_addr(v_fst_491_);
v___x_496_ = lean_ptr_addr(v_fst_493_);
v___x_497_ = lean_usize_dec_eq(v___x_495_, v___x_496_);
if (v___x_497_ == 0)
{
v_x_486_ = v_tail_490_;
goto _start;
}
else
{
size_t v___x_499_; size_t v___x_500_; uint8_t v___x_501_; 
v___x_499_ = lean_ptr_addr(v_snd_492_);
v___x_500_ = lean_ptr_addr(v_snd_494_);
v___x_501_ = lean_usize_dec_eq(v___x_499_, v___x_500_);
if (v___x_501_ == 0)
{
v_x_486_ = v_tail_490_;
goto _start;
}
else
{
lean_object* v___x_503_; 
lean_inc(v_value_489_);
v___x_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_503_, 0, v_value_489_);
return v___x_503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0___redArg___boxed(lean_object* v_a_504_, lean_object* v_x_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0___redArg(v_a_504_, v_x_505_);
lean_dec(v_x_505_);
lean_dec_ref(v_a_504_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0___redArg(lean_object* v_m_507_, lean_object* v_a_508_){
_start:
{
lean_object* v_buckets_509_; lean_object* v_fst_510_; lean_object* v_snd_511_; lean_object* v___x_512_; size_t v___x_513_; size_t v___x_514_; size_t v___x_515_; uint64_t v___x_516_; size_t v___x_517_; size_t v___x_518_; uint64_t v___x_519_; uint64_t v___x_520_; uint64_t v___x_521_; uint64_t v___x_522_; uint64_t v_fold_523_; uint64_t v___x_524_; uint64_t v___x_525_; uint64_t v___x_526_; size_t v___x_527_; size_t v___x_528_; size_t v___x_529_; size_t v___x_530_; size_t v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v_buckets_509_ = lean_ctor_get(v_m_507_, 1);
v_fst_510_ = lean_ctor_get(v_a_508_, 0);
v_snd_511_ = lean_ctor_get(v_a_508_, 1);
v___x_512_ = lean_array_get_size(v_buckets_509_);
v___x_513_ = lean_ptr_addr(v_fst_510_);
v___x_514_ = ((size_t)3ULL);
v___x_515_ = lean_usize_shift_right(v___x_513_, v___x_514_);
v___x_516_ = lean_usize_to_uint64(v___x_515_);
v___x_517_ = lean_ptr_addr(v_snd_511_);
v___x_518_ = lean_usize_shift_right(v___x_517_, v___x_514_);
v___x_519_ = lean_usize_to_uint64(v___x_518_);
v___x_520_ = lean_uint64_mix_hash(v___x_516_, v___x_519_);
v___x_521_ = 32ULL;
v___x_522_ = lean_uint64_shift_right(v___x_520_, v___x_521_);
v_fold_523_ = lean_uint64_xor(v___x_520_, v___x_522_);
v___x_524_ = 16ULL;
v___x_525_ = lean_uint64_shift_right(v_fold_523_, v___x_524_);
v___x_526_ = lean_uint64_xor(v_fold_523_, v___x_525_);
v___x_527_ = lean_uint64_to_usize(v___x_526_);
v___x_528_ = lean_usize_of_nat(v___x_512_);
v___x_529_ = ((size_t)1ULL);
v___x_530_ = lean_usize_sub(v___x_528_, v___x_529_);
v___x_531_ = lean_usize_land(v___x_527_, v___x_530_);
v___x_532_ = lean_array_uget_borrowed(v_buckets_509_, v___x_531_);
v___x_533_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0___redArg(v_a_508_, v___x_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0___redArg___boxed(lean_object* v_m_534_, lean_object* v_a_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0___redArg(v_m_534_, v_a_535_);
lean_dec_ref(v_a_535_);
lean_dec_ref(v_m_534_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__7___redArg(lean_object* v_a_537_, lean_object* v_b_538_, lean_object* v_x_539_){
_start:
{
if (lean_obj_tag(v_x_539_) == 0)
{
lean_dec(v_b_538_);
lean_dec_ref(v_a_537_);
return v_x_539_;
}
else
{
lean_object* v_key_540_; lean_object* v_value_541_; lean_object* v_tail_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_562_; 
v_key_540_ = lean_ctor_get(v_x_539_, 0);
v_value_541_ = lean_ctor_get(v_x_539_, 1);
v_tail_542_ = lean_ctor_get(v_x_539_, 2);
v_isSharedCheck_562_ = !lean_is_exclusive(v_x_539_);
if (v_isSharedCheck_562_ == 0)
{
v___x_544_ = v_x_539_;
v_isShared_545_ = v_isSharedCheck_562_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_tail_542_);
lean_inc(v_value_541_);
lean_inc(v_key_540_);
lean_dec(v_x_539_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_562_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v_fst_551_; lean_object* v_snd_552_; lean_object* v_fst_553_; lean_object* v_snd_554_; size_t v___x_555_; size_t v___x_556_; uint8_t v___x_557_; 
v_fst_551_ = lean_ctor_get(v_key_540_, 0);
v_snd_552_ = lean_ctor_get(v_key_540_, 1);
v_fst_553_ = lean_ctor_get(v_a_537_, 0);
v_snd_554_ = lean_ctor_get(v_a_537_, 1);
v___x_555_ = lean_ptr_addr(v_fst_551_);
v___x_556_ = lean_ptr_addr(v_fst_553_);
v___x_557_ = lean_usize_dec_eq(v___x_555_, v___x_556_);
if (v___x_557_ == 0)
{
goto v___jp_546_;
}
else
{
size_t v___x_558_; size_t v___x_559_; uint8_t v___x_560_; 
v___x_558_ = lean_ptr_addr(v_snd_552_);
v___x_559_ = lean_ptr_addr(v_snd_554_);
v___x_560_ = lean_usize_dec_eq(v___x_558_, v___x_559_);
if (v___x_560_ == 0)
{
goto v___jp_546_;
}
else
{
lean_object* v___x_561_; 
lean_del_object(v___x_544_);
lean_dec(v_value_541_);
lean_dec(v_key_540_);
v___x_561_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_561_, 0, v_a_537_);
lean_ctor_set(v___x_561_, 1, v_b_538_);
lean_ctor_set(v___x_561_, 2, v_tail_542_);
return v___x_561_;
}
}
v___jp_546_:
{
lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_547_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__7___redArg(v_a_537_, v_b_538_, v_tail_542_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 2, v___x_547_);
v___x_549_ = v___x_544_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_key_540_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v_value_541_);
lean_ctor_set(v_reuseFailAlloc_550_, 2, v___x_547_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5___redArg(lean_object* v_a_563_, lean_object* v_x_564_){
_start:
{
if (lean_obj_tag(v_x_564_) == 0)
{
uint8_t v___x_565_; 
v___x_565_ = 0;
return v___x_565_;
}
else
{
lean_object* v_key_566_; lean_object* v_tail_567_; lean_object* v_fst_568_; lean_object* v_snd_569_; lean_object* v_fst_570_; lean_object* v_snd_571_; size_t v___x_572_; size_t v___x_573_; uint8_t v___x_574_; 
v_key_566_ = lean_ctor_get(v_x_564_, 0);
v_tail_567_ = lean_ctor_get(v_x_564_, 2);
v_fst_568_ = lean_ctor_get(v_key_566_, 0);
v_snd_569_ = lean_ctor_get(v_key_566_, 1);
v_fst_570_ = lean_ctor_get(v_a_563_, 0);
v_snd_571_ = lean_ctor_get(v_a_563_, 1);
v___x_572_ = lean_ptr_addr(v_fst_568_);
v___x_573_ = lean_ptr_addr(v_fst_570_);
v___x_574_ = lean_usize_dec_eq(v___x_572_, v___x_573_);
if (v___x_574_ == 0)
{
v_x_564_ = v_tail_567_;
goto _start;
}
else
{
size_t v___x_576_; size_t v___x_577_; uint8_t v___x_578_; 
v___x_576_ = lean_ptr_addr(v_snd_569_);
v___x_577_ = lean_ptr_addr(v_snd_571_);
v___x_578_ = lean_usize_dec_eq(v___x_576_, v___x_577_);
if (v___x_578_ == 0)
{
v_x_564_ = v_tail_567_;
goto _start;
}
else
{
return v___x_578_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5___redArg___boxed(lean_object* v_a_580_, lean_object* v_x_581_){
_start:
{
uint8_t v_res_582_; lean_object* v_r_583_; 
v_res_582_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5___redArg(v_a_580_, v_x_581_);
lean_dec(v_x_581_);
lean_dec_ref(v_a_580_);
v_r_583_ = lean_box(v_res_582_);
return v_r_583_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6_spec__7_spec__8___redArg(lean_object* v_x_584_, lean_object* v_x_585_){
_start:
{
if (lean_obj_tag(v_x_585_) == 0)
{
return v_x_584_;
}
else
{
lean_object* v_key_586_; lean_object* v_value_587_; lean_object* v_tail_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_620_; 
v_key_586_ = lean_ctor_get(v_x_585_, 0);
v_value_587_ = lean_ctor_get(v_x_585_, 1);
v_tail_588_ = lean_ctor_get(v_x_585_, 2);
v_isSharedCheck_620_ = !lean_is_exclusive(v_x_585_);
if (v_isSharedCheck_620_ == 0)
{
v___x_590_ = v_x_585_;
v_isShared_591_ = v_isSharedCheck_620_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_tail_588_);
lean_inc(v_value_587_);
lean_inc(v_key_586_);
lean_dec(v_x_585_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_620_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v_fst_592_; lean_object* v_snd_593_; lean_object* v___x_594_; size_t v___x_595_; size_t v___x_596_; size_t v___x_597_; uint64_t v___x_598_; size_t v___x_599_; size_t v___x_600_; uint64_t v___x_601_; uint64_t v___x_602_; uint64_t v___x_603_; uint64_t v___x_604_; uint64_t v_fold_605_; uint64_t v___x_606_; uint64_t v___x_607_; uint64_t v___x_608_; size_t v___x_609_; size_t v___x_610_; size_t v___x_611_; size_t v___x_612_; size_t v___x_613_; lean_object* v___x_614_; lean_object* v___x_616_; 
v_fst_592_ = lean_ctor_get(v_key_586_, 0);
v_snd_593_ = lean_ctor_get(v_key_586_, 1);
v___x_594_ = lean_array_get_size(v_x_584_);
v___x_595_ = lean_ptr_addr(v_fst_592_);
v___x_596_ = ((size_t)3ULL);
v___x_597_ = lean_usize_shift_right(v___x_595_, v___x_596_);
v___x_598_ = lean_usize_to_uint64(v___x_597_);
v___x_599_ = lean_ptr_addr(v_snd_593_);
v___x_600_ = lean_usize_shift_right(v___x_599_, v___x_596_);
v___x_601_ = lean_usize_to_uint64(v___x_600_);
v___x_602_ = lean_uint64_mix_hash(v___x_598_, v___x_601_);
v___x_603_ = 32ULL;
v___x_604_ = lean_uint64_shift_right(v___x_602_, v___x_603_);
v_fold_605_ = lean_uint64_xor(v___x_602_, v___x_604_);
v___x_606_ = 16ULL;
v___x_607_ = lean_uint64_shift_right(v_fold_605_, v___x_606_);
v___x_608_ = lean_uint64_xor(v_fold_605_, v___x_607_);
v___x_609_ = lean_uint64_to_usize(v___x_608_);
v___x_610_ = lean_usize_of_nat(v___x_594_);
v___x_611_ = ((size_t)1ULL);
v___x_612_ = lean_usize_sub(v___x_610_, v___x_611_);
v___x_613_ = lean_usize_land(v___x_609_, v___x_612_);
v___x_614_ = lean_array_uget_borrowed(v_x_584_, v___x_613_);
lean_inc(v___x_614_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 2, v___x_614_);
v___x_616_ = v___x_590_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_key_586_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v_value_587_);
lean_ctor_set(v_reuseFailAlloc_619_, 2, v___x_614_);
v___x_616_ = v_reuseFailAlloc_619_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
lean_object* v___x_617_; 
v___x_617_ = lean_array_uset(v_x_584_, v___x_613_, v___x_616_);
v_x_584_ = v___x_617_;
v_x_585_ = v_tail_588_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6_spec__7___redArg(lean_object* v_i_621_, lean_object* v_source_622_, lean_object* v_target_623_){
_start:
{
lean_object* v___x_624_; uint8_t v___x_625_; 
v___x_624_ = lean_array_get_size(v_source_622_);
v___x_625_ = lean_nat_dec_lt(v_i_621_, v___x_624_);
if (v___x_625_ == 0)
{
lean_dec_ref(v_source_622_);
lean_dec(v_i_621_);
return v_target_623_;
}
else
{
lean_object* v_es_626_; lean_object* v___x_627_; lean_object* v_source_628_; lean_object* v_target_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v_es_626_ = lean_array_fget(v_source_622_, v_i_621_);
v___x_627_ = lean_box(0);
v_source_628_ = lean_array_fset(v_source_622_, v_i_621_, v___x_627_);
v_target_629_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6_spec__7_spec__8___redArg(v_target_623_, v_es_626_);
v___x_630_ = lean_unsigned_to_nat(1u);
v___x_631_ = lean_nat_add(v_i_621_, v___x_630_);
lean_dec(v_i_621_);
v_i_621_ = v___x_631_;
v_source_622_ = v_source_628_;
v_target_623_ = v_target_629_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6___redArg(lean_object* v_data_633_){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v_nbuckets_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_634_ = lean_array_get_size(v_data_633_);
v___x_635_ = lean_unsigned_to_nat(2u);
v_nbuckets_636_ = lean_nat_mul(v___x_634_, v___x_635_);
v___x_637_ = lean_unsigned_to_nat(0u);
v___x_638_ = lean_box(0);
v___x_639_ = lean_mk_array(v_nbuckets_636_, v___x_638_);
v___x_640_ = lean_array_propagate_mark(v_data_633_, v___x_639_);
v___x_641_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6_spec__7___redArg(v___x_637_, v_data_633_, v___x_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3___redArg(lean_object* v_m_642_, lean_object* v_a_643_, lean_object* v_b_644_){
_start:
{
lean_object* v_size_645_; lean_object* v_buckets_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_698_; 
v_size_645_ = lean_ctor_get(v_m_642_, 0);
v_buckets_646_ = lean_ctor_get(v_m_642_, 1);
v_isSharedCheck_698_ = !lean_is_exclusive(v_m_642_);
if (v_isSharedCheck_698_ == 0)
{
v___x_648_ = v_m_642_;
v_isShared_649_ = v_isSharedCheck_698_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_buckets_646_);
lean_inc(v_size_645_);
lean_dec(v_m_642_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_698_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v_fst_650_; lean_object* v_snd_651_; lean_object* v___x_652_; size_t v___x_653_; size_t v___x_654_; size_t v___x_655_; uint64_t v___x_656_; size_t v___x_657_; size_t v___x_658_; uint64_t v___x_659_; uint64_t v___x_660_; uint64_t v___x_661_; uint64_t v___x_662_; uint64_t v_fold_663_; uint64_t v___x_664_; uint64_t v___x_665_; uint64_t v___x_666_; size_t v___x_667_; size_t v___x_668_; size_t v___x_669_; size_t v___x_670_; size_t v___x_671_; lean_object* v_bkt_672_; uint8_t v___x_673_; 
v_fst_650_ = lean_ctor_get(v_a_643_, 0);
v_snd_651_ = lean_ctor_get(v_a_643_, 1);
v___x_652_ = lean_array_get_size(v_buckets_646_);
v___x_653_ = lean_ptr_addr(v_fst_650_);
v___x_654_ = ((size_t)3ULL);
v___x_655_ = lean_usize_shift_right(v___x_653_, v___x_654_);
v___x_656_ = lean_usize_to_uint64(v___x_655_);
v___x_657_ = lean_ptr_addr(v_snd_651_);
v___x_658_ = lean_usize_shift_right(v___x_657_, v___x_654_);
v___x_659_ = lean_usize_to_uint64(v___x_658_);
v___x_660_ = lean_uint64_mix_hash(v___x_656_, v___x_659_);
v___x_661_ = 32ULL;
v___x_662_ = lean_uint64_shift_right(v___x_660_, v___x_661_);
v_fold_663_ = lean_uint64_xor(v___x_660_, v___x_662_);
v___x_664_ = 16ULL;
v___x_665_ = lean_uint64_shift_right(v_fold_663_, v___x_664_);
v___x_666_ = lean_uint64_xor(v_fold_663_, v___x_665_);
v___x_667_ = lean_uint64_to_usize(v___x_666_);
v___x_668_ = lean_usize_of_nat(v___x_652_);
v___x_669_ = ((size_t)1ULL);
v___x_670_ = lean_usize_sub(v___x_668_, v___x_669_);
v___x_671_ = lean_usize_land(v___x_667_, v___x_670_);
v_bkt_672_ = lean_array_uget_borrowed(v_buckets_646_, v___x_671_);
v___x_673_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5___redArg(v_a_643_, v_bkt_672_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; lean_object* v_size_x27_675_; lean_object* v___x_676_; lean_object* v_buckets_x27_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; uint8_t v___x_683_; 
v___x_674_ = lean_unsigned_to_nat(1u);
v_size_x27_675_ = lean_nat_add(v_size_645_, v___x_674_);
lean_dec(v_size_645_);
lean_inc(v_bkt_672_);
v___x_676_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_676_, 0, v_a_643_);
lean_ctor_set(v___x_676_, 1, v_b_644_);
lean_ctor_set(v___x_676_, 2, v_bkt_672_);
v_buckets_x27_677_ = lean_array_uset(v_buckets_646_, v___x_671_, v___x_676_);
v___x_678_ = lean_unsigned_to_nat(4u);
v___x_679_ = lean_nat_mul(v_size_x27_675_, v___x_678_);
v___x_680_ = lean_unsigned_to_nat(3u);
v___x_681_ = lean_nat_div(v___x_679_, v___x_680_);
lean_dec(v___x_679_);
v___x_682_ = lean_array_get_size(v_buckets_x27_677_);
v___x_683_ = lean_nat_dec_le(v___x_681_, v___x_682_);
lean_dec(v___x_681_);
if (v___x_683_ == 0)
{
lean_object* v_val_684_; lean_object* v___x_686_; 
v_val_684_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6___redArg(v_buckets_x27_677_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 1, v_val_684_);
lean_ctor_set(v___x_648_, 0, v_size_x27_675_);
v___x_686_ = v___x_648_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_size_x27_675_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v_val_684_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
else
{
lean_object* v___x_689_; 
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 1, v_buckets_x27_677_);
lean_ctor_set(v___x_648_, 0, v_size_x27_675_);
v___x_689_ = v___x_648_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_size_x27_675_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v_buckets_x27_677_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
else
{
lean_object* v___x_691_; lean_object* v_buckets_x27_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_696_; 
lean_inc(v_bkt_672_);
v___x_691_ = lean_box(0);
v_buckets_x27_692_ = lean_array_uset(v_buckets_646_, v___x_671_, v___x_691_);
v___x_693_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__7___redArg(v_a_643_, v_b_644_, v_bkt_672_);
v___x_694_ = lean_array_uset(v_buckets_x27_692_, v___x_671_, v___x_693_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 1, v___x_694_);
v___x_696_ = v___x_648_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_size_645_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v___x_694_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl(lean_object* v_userName_699_, lean_object* v_type_700_, lean_object* v_value_701_, uint8_t v_nondep_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_){
_start:
{
lean_object* v___x_711_; lean_object* v_key_712_; lean_object* v___x_713_; lean_object* v_valueMap_714_; lean_object* v___x_715_; 
v___x_711_ = l_Lean_Meta_Sym_LiftLet_instInhabitedDecl_default;
lean_inc_ref(v_value_701_);
lean_inc_ref(v_type_700_);
v_key_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_712_, 0, v_type_700_);
lean_ctor_set(v_key_712_, 1, v_value_701_);
v___x_713_ = lean_st_ref_get(v_a_703_);
v_valueMap_714_ = lean_ctor_get(v___x_713_, 4);
lean_inc_ref(v_valueMap_714_);
lean_dec(v___x_713_);
v___x_715_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0___redArg(v_valueMap_714_, v_key_712_);
lean_dec_ref(v_valueMap_714_);
if (lean_obj_tag(v___x_715_) == 1)
{
lean_object* v_val_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_762_; 
lean_dec_ref_known(v_key_712_, 2);
lean_dec_ref(v_value_701_);
lean_dec_ref(v_type_700_);
lean_dec(v_userName_699_);
v_val_716_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_762_ == 0)
{
v___x_718_ = v___x_715_;
v_isShared_719_ = v_isSharedCheck_762_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_val_716_);
lean_dec(v___x_715_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_762_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___y_721_; 
if (v_nondep_702_ == 0)
{
lean_object* v___x_729_; lean_object* v_cache_730_; lean_object* v_cacheClosed_731_; lean_object* v_hasLetCache_732_; lean_object* v_decls_733_; lean_object* v_valueMap_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_761_; 
v___x_729_ = lean_st_ref_take(v_a_703_);
v_cache_730_ = lean_ctor_get(v___x_729_, 0);
v_cacheClosed_731_ = lean_ctor_get(v___x_729_, 1);
v_hasLetCache_732_ = lean_ctor_get(v___x_729_, 2);
v_decls_733_ = lean_ctor_get(v___x_729_, 3);
v_valueMap_734_ = lean_ctor_get(v___x_729_, 4);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_761_ == 0)
{
v___x_736_ = v___x_729_;
v_isShared_737_ = v_isSharedCheck_761_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_valueMap_734_);
lean_inc(v_decls_733_);
lean_inc(v_hasLetCache_732_);
lean_inc(v_cacheClosed_731_);
lean_inc(v_cache_730_);
lean_dec(v___x_729_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_761_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___y_739_; lean_object* v___x_744_; uint8_t v___x_745_; 
v___x_744_ = lean_array_get_size(v_decls_733_);
v___x_745_ = lean_nat_dec_lt(v_val_716_, v___x_744_);
if (v___x_745_ == 0)
{
v___y_739_ = v_decls_733_;
goto v___jp_738_;
}
else
{
lean_object* v_v_746_; lean_object* v_fvar_747_; lean_object* v_userName_748_; lean_object* v_type_749_; lean_object* v_value_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_760_; 
v_v_746_ = lean_array_fget(v_decls_733_, v_val_716_);
v_fvar_747_ = lean_ctor_get(v_v_746_, 0);
v_userName_748_ = lean_ctor_get(v_v_746_, 1);
v_type_749_ = lean_ctor_get(v_v_746_, 2);
v_value_750_ = lean_ctor_get(v_v_746_, 3);
v_isSharedCheck_760_ = !lean_is_exclusive(v_v_746_);
if (v_isSharedCheck_760_ == 0)
{
v___x_752_ = v_v_746_;
v_isShared_753_ = v_isSharedCheck_760_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_value_750_);
lean_inc(v_type_749_);
lean_inc(v_userName_748_);
lean_inc(v_fvar_747_);
lean_dec(v_v_746_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_760_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_754_; lean_object* v_xs_x27_755_; lean_object* v___x_757_; 
v___x_754_ = lean_box(0);
v_xs_x27_755_ = lean_array_fset(v_decls_733_, v_val_716_, v___x_754_);
if (v_isShared_753_ == 0)
{
v___x_757_ = v___x_752_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_fvar_747_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_userName_748_);
lean_ctor_set(v_reuseFailAlloc_759_, 2, v_type_749_);
lean_ctor_set(v_reuseFailAlloc_759_, 3, v_value_750_);
v___x_757_ = v_reuseFailAlloc_759_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
lean_object* v___x_758_; 
lean_ctor_set_uint8(v___x_757_, sizeof(void*)*4, v_nondep_702_);
v___x_758_ = lean_array_fset(v_xs_x27_755_, v_val_716_, v___x_757_);
v___y_739_ = v___x_758_;
goto v___jp_738_;
}
}
}
v___jp_738_:
{
lean_object* v___x_741_; 
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 3, v___y_739_);
v___x_741_ = v___x_736_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_cache_730_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v_cacheClosed_731_);
lean_ctor_set(v_reuseFailAlloc_743_, 2, v_hasLetCache_732_);
lean_ctor_set(v_reuseFailAlloc_743_, 3, v___y_739_);
lean_ctor_set(v_reuseFailAlloc_743_, 4, v_valueMap_734_);
v___x_741_ = v_reuseFailAlloc_743_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
lean_object* v___x_742_; 
v___x_742_ = lean_st_ref_put(v_a_703_, v___x_741_);
v___y_721_ = v_a_703_;
goto v___jp_720_;
}
}
}
}
else
{
v___y_721_ = v_a_703_;
goto v___jp_720_;
}
v___jp_720_:
{
lean_object* v___x_722_; lean_object* v_decls_723_; lean_object* v___x_724_; lean_object* v_fvar_725_; lean_object* v___x_727_; 
v___x_722_ = lean_st_ref_get(v___y_721_);
v_decls_723_ = lean_ctor_get(v___x_722_, 3);
lean_inc_ref(v_decls_723_);
lean_dec(v___x_722_);
v___x_724_ = lean_array_get(v___x_711_, v_decls_723_, v_val_716_);
lean_dec(v_val_716_);
lean_dec_ref(v_decls_723_);
v_fvar_725_ = lean_ctor_get(v___x_724_, 0);
lean_inc_ref(v_fvar_725_);
lean_dec(v___x_724_);
if (v_isShared_719_ == 0)
{
lean_ctor_set_tag(v___x_718_, 0);
lean_ctor_set(v___x_718_, 0, v_fvar_725_);
v___x_727_ = v___x_718_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_fvar_725_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
else
{
lean_object* v___x_763_; 
lean_dec(v___x_715_);
v___x_763_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1(v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; lean_object* v___x_765_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_764_);
lean_dec_ref_known(v___x_763_, 1);
v___x_765_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__2___redArg(v_a_764_, v_a_705_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_793_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_793_ == 0)
{
v___x_768_ = v___x_765_;
v_isShared_769_ = v_isSharedCheck_793_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_765_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_793_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_770_; lean_object* v_decls_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v_cache_774_; lean_object* v_cacheClosed_775_; lean_object* v_hasLetCache_776_; lean_object* v_decls_777_; lean_object* v_valueMap_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_792_; 
v___x_770_ = lean_st_ref_get(v_a_703_);
v_decls_771_ = lean_ctor_get(v___x_770_, 3);
lean_inc_ref(v_decls_771_);
lean_dec(v___x_770_);
v___x_772_ = lean_array_get_size(v_decls_771_);
lean_dec_ref(v_decls_771_);
v___x_773_ = lean_st_ref_take(v_a_703_);
v_cache_774_ = lean_ctor_get(v___x_773_, 0);
v_cacheClosed_775_ = lean_ctor_get(v___x_773_, 1);
v_hasLetCache_776_ = lean_ctor_get(v___x_773_, 2);
v_decls_777_ = lean_ctor_get(v___x_773_, 3);
v_valueMap_778_ = lean_ctor_get(v___x_773_, 4);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_792_ == 0)
{
v___x_780_ = v___x_773_;
v_isShared_781_ = v_isSharedCheck_792_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_valueMap_778_);
lean_inc(v_decls_777_);
lean_inc(v_hasLetCache_776_);
lean_inc(v_cacheClosed_775_);
lean_inc(v_cache_774_);
lean_dec(v___x_773_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_792_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_786_; 
lean_inc(v_a_766_);
v___x_782_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_782_, 0, v_a_766_);
lean_ctor_set(v___x_782_, 1, v_userName_699_);
lean_ctor_set(v___x_782_, 2, v_type_700_);
lean_ctor_set(v___x_782_, 3, v_value_701_);
lean_ctor_set_uint8(v___x_782_, sizeof(void*)*4, v_nondep_702_);
v___x_783_ = lean_array_push(v_decls_777_, v___x_782_);
v___x_784_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3___redArg(v_valueMap_778_, v_key_712_, v___x_772_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 4, v___x_784_);
lean_ctor_set(v___x_780_, 3, v___x_783_);
v___x_786_ = v___x_780_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_cache_774_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_cacheClosed_775_);
lean_ctor_set(v_reuseFailAlloc_791_, 2, v_hasLetCache_776_);
lean_ctor_set(v_reuseFailAlloc_791_, 3, v___x_783_);
lean_ctor_set(v_reuseFailAlloc_791_, 4, v___x_784_);
v___x_786_ = v_reuseFailAlloc_791_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
lean_object* v___x_787_; lean_object* v___x_789_; 
v___x_787_ = lean_st_ref_put(v_a_703_, v___x_786_);
if (v_isShared_769_ == 0)
{
v___x_789_ = v___x_768_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_766_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_712_, 2);
lean_dec_ref(v_value_701_);
lean_dec_ref(v_type_700_);
lean_dec(v_userName_699_);
return v___x_765_;
}
}
else
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
lean_dec_ref_known(v_key_712_, 2);
lean_dec_ref(v_value_701_);
lean_dec_ref(v_type_700_);
lean_dec(v_userName_699_);
v_a_794_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v___x_763_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_763_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_794_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl___boxed(lean_object* v_userName_802_, lean_object* v_type_803_, lean_object* v_value_804_, lean_object* v_nondep_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_){
_start:
{
uint8_t v_nondep_boxed_814_; lean_object* v_res_815_; 
v_nondep_boxed_814_ = lean_unbox(v_nondep_805_);
v_res_815_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl(v_userName_802_, v_type_803_, v_value_804_, v_nondep_boxed_814_, v_a_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0(lean_object* v_00_u03b2_816_, lean_object* v_m_817_, lean_object* v_a_818_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0___redArg(v_m_817_, v_a_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0___boxed(lean_object* v_00_u03b2_820_, lean_object* v_m_821_, lean_object* v_a_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0(v_00_u03b2_820_, v_m_821_, v_a_822_);
lean_dec_ref(v_a_822_);
lean_dec_ref(v_m_821_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2(lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2___redArg(v___y_830_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2___boxed(lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__1_spec__2(v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec(v___y_833_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3(lean_object* v_00_u03b2_842_, lean_object* v_m_843_, lean_object* v_a_844_, lean_object* v_b_845_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3___redArg(v_m_843_, v_a_844_, v_b_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0(lean_object* v_00_u03b2_847_, lean_object* v_a_848_, lean_object* v_x_849_){
_start:
{
lean_object* v___x_850_; 
v___x_850_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0___redArg(v_a_848_, v_x_849_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_851_, lean_object* v_a_852_, lean_object* v_x_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__0_spec__0(v_00_u03b2_851_, v_a_852_, v_x_853_);
lean_dec(v_x_853_);
lean_dec_ref(v_a_852_);
return v_res_854_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5(lean_object* v_00_u03b2_855_, lean_object* v_a_856_, lean_object* v_x_857_){
_start:
{
uint8_t v___x_858_; 
v___x_858_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5___redArg(v_a_856_, v_x_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5___boxed(lean_object* v_00_u03b2_859_, lean_object* v_a_860_, lean_object* v_x_861_){
_start:
{
uint8_t v_res_862_; lean_object* v_r_863_; 
v_res_862_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__5(v_00_u03b2_859_, v_a_860_, v_x_861_);
lean_dec(v_x_861_);
lean_dec_ref(v_a_860_);
v_r_863_ = lean_box(v_res_862_);
return v_r_863_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6(lean_object* v_00_u03b2_864_, lean_object* v_data_865_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6___redArg(v_data_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__7(lean_object* v_00_u03b2_867_, lean_object* v_a_868_, lean_object* v_b_869_, lean_object* v_x_870_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__7___redArg(v_a_868_, v_b_869_, v_x_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6_spec__7(lean_object* v_00_u03b2_872_, lean_object* v_i_873_, lean_object* v_source_874_, lean_object* v_target_875_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6_spec__7___redArg(v_i_873_, v_source_874_, v_target_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6_spec__7_spec__8(lean_object* v_00_u03b2_877_, lean_object* v_x_878_, lean_object* v_x_879_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl_spec__3_spec__6_spec__7_spec__8___redArg(v_x_878_, v_x_879_);
return v___x_880_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1___closed__0(void){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Lean_Meta_Sym_instInhabitedSymM___redArg();
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1(lean_object* v_msg_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
lean_object* v___x_890_; lean_object* v___x_2263__overap_891_; lean_object* v___x_892_; 
v___x_890_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1___closed__0);
v___x_2263__overap_891_ = lean_panic_fn_borrowed(v___x_890_, v_msg_882_);
lean_inc(v___y_888_);
lean_inc_ref(v___y_887_);
lean_inc(v___y_886_);
lean_inc_ref(v___y_885_);
lean_inc(v___y_884_);
lean_inc_ref(v___y_883_);
v___x_892_ = lean_apply_7(v___x_2263__overap_891_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, lean_box(0));
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1___boxed(lean_object* v_msg_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1(v_msg_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__2(lean_object* v_x_902_, uint8_t v_bi_903_, lean_object* v_t_904_, lean_object* v_b_905_, lean_object* v___y_906_, uint8_t v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
lean_object* v___y_911_; lean_object* v___y_912_; 
if (v___y_907_ == 0)
{
v___y_911_ = v___y_906_;
v___y_912_ = v___y_909_;
goto v___jp_910_;
}
else
{
lean_object* v___x_934_; 
v___x_934_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_904_, v___y_907_, v___y_908_, v___y_909_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_object* v_a_935_; lean_object* v___x_936_; 
v_a_935_ = lean_ctor_get(v___x_934_, 1);
lean_inc(v_a_935_);
lean_dec_ref_known(v___x_934_, 2);
v___x_936_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_905_, v___y_907_, v___y_908_, v_a_935_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v_a_937_; 
v_a_937_ = lean_ctor_get(v___x_936_, 1);
lean_inc(v_a_937_);
lean_dec_ref_known(v___x_936_, 2);
v___y_911_ = v___y_906_;
v___y_912_ = v_a_937_;
goto v___jp_910_;
}
else
{
lean_object* v_a_938_; lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_946_; 
lean_dec_ref(v___y_906_);
lean_dec_ref(v_b_905_);
lean_dec_ref(v_t_904_);
lean_dec(v_x_902_);
v_a_938_ = lean_ctor_get(v___x_936_, 0);
v_a_939_ = lean_ctor_get(v___x_936_, 1);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_946_ == 0)
{
v___x_941_ = v___x_936_;
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_inc(v_a_938_);
lean_dec(v___x_936_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_944_; 
if (v_isShared_942_ == 0)
{
v___x_944_ = v___x_941_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_a_938_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v_a_939_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
}
else
{
lean_object* v_a_947_; lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
lean_dec_ref(v___y_906_);
lean_dec_ref(v_b_905_);
lean_dec_ref(v_t_904_);
lean_dec(v_x_902_);
v_a_947_ = lean_ctor_get(v___x_934_, 0);
v_a_948_ = lean_ctor_get(v___x_934_, 1);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_934_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_inc(v_a_947_);
lean_dec(v___x_934_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_947_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v_a_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
v___jp_910_:
{
lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_913_ = l_Lean_Expr_lam___override(v_x_902_, v_t_904_, v_b_905_, v_bi_903_);
v___x_914_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_913_, v___y_912_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_924_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
v_a_916_ = lean_ctor_get(v___x_914_, 1);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_924_ == 0)
{
v___x_918_ = v___x_914_;
v_isShared_919_ = v_isSharedCheck_924_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_inc(v_a_915_);
lean_dec(v___x_914_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_924_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_920_; lean_object* v___x_922_; 
v___x_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_920_, 0, v_a_915_);
lean_ctor_set(v___x_920_, 1, v___y_911_);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 0, v___x_920_);
v___x_922_ = v___x_918_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_920_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v_a_916_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
else
{
lean_object* v_a_925_; lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
lean_dec_ref(v___y_911_);
v_a_925_ = lean_ctor_get(v___x_914_, 0);
v_a_926_ = lean_ctor_get(v___x_914_, 1);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_914_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_inc(v_a_925_);
lean_dec(v___x_914_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_925_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v_a_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__2___boxed(lean_object* v_x_956_, lean_object* v_bi_957_, lean_object* v_t_958_, lean_object* v_b_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
uint8_t v_bi_boxed_964_; uint8_t v___y_25275__boxed_965_; lean_object* v_res_966_; 
v_bi_boxed_964_ = lean_unbox(v_bi_957_);
v___y_25275__boxed_965_ = lean_unbox(v___y_961_);
v_res_966_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__2(v_x_956_, v_bi_boxed_964_, v_t_958_, v_b_959_, v___y_960_, v___y_25275__boxed_965_, v___y_962_, v___y_963_);
lean_dec_ref(v___y_962_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__6(lean_object* v_structName_967_, lean_object* v_idx_968_, lean_object* v_struct_969_, lean_object* v___y_970_, uint8_t v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v___y_975_; lean_object* v___y_976_; 
if (v___y_971_ == 0)
{
v___y_975_ = v___y_970_;
v___y_976_ = v___y_973_;
goto v___jp_974_;
}
else
{
lean_object* v___x_998_; 
v___x_998_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_struct_969_, v___y_971_, v___y_972_, v___y_973_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; 
v_a_999_ = lean_ctor_get(v___x_998_, 1);
lean_inc(v_a_999_);
lean_dec_ref_known(v___x_998_, 2);
v___y_975_ = v___y_970_;
v___y_976_ = v_a_999_;
goto v___jp_974_;
}
else
{
lean_object* v_a_1000_; lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
lean_dec_ref(v___y_970_);
lean_dec_ref(v_struct_969_);
lean_dec(v_idx_968_);
lean_dec(v_structName_967_);
v_a_1000_ = lean_ctor_get(v___x_998_, 0);
v_a_1001_ = lean_ctor_get(v___x_998_, 1);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1003_ = v___x_998_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_inc(v_a_1000_);
lean_dec(v___x_998_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_1000_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v_a_1001_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
v___jp_974_:
{
lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_977_ = l_Lean_Expr_proj___override(v_structName_967_, v_idx_968_, v_struct_969_);
v___x_978_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_977_, v___y_976_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_988_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
v_a_980_ = lean_ctor_get(v___x_978_, 1);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_988_ == 0)
{
v___x_982_ = v___x_978_;
v_isShared_983_ = v_isSharedCheck_988_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_inc(v_a_979_);
lean_dec(v___x_978_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_988_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_984_; lean_object* v___x_986_; 
v___x_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_984_, 0, v_a_979_);
lean_ctor_set(v___x_984_, 1, v___y_975_);
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 0, v___x_984_);
v___x_986_ = v___x_982_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v___x_984_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v_a_980_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
else
{
lean_object* v_a_989_; lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
lean_dec_ref(v___y_975_);
v_a_989_ = lean_ctor_get(v___x_978_, 0);
v_a_990_ = lean_ctor_get(v___x_978_, 1);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_997_ == 0)
{
v___x_992_ = v___x_978_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_inc(v_a_989_);
lean_dec(v___x_978_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_a_989_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v_a_990_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__6___boxed(lean_object* v_structName_1009_, lean_object* v_idx_1010_, lean_object* v_struct_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
uint8_t v___y_25381__boxed_1016_; lean_object* v_res_1017_; 
v___y_25381__boxed_1016_ = lean_unbox(v___y_1013_);
v_res_1017_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__6(v_structName_1009_, v_idx_1010_, v_struct_1011_, v___y_1012_, v___y_25381__boxed_1016_, v___y_1014_, v___y_1015_);
lean_dec_ref(v___y_1014_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__1(lean_object* v_f_1018_, lean_object* v_a_1019_, lean_object* v___y_1020_, uint8_t v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v___y_1025_; lean_object* v___y_1026_; 
if (v___y_1021_ == 0)
{
v___y_1025_ = v___y_1020_;
v___y_1026_ = v___y_1023_;
goto v___jp_1024_;
}
else
{
lean_object* v___x_1048_; 
v___x_1048_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_1018_, v___y_1021_, v___y_1022_, v___y_1023_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v_a_1049_; lean_object* v___x_1050_; 
v_a_1049_ = lean_ctor_get(v___x_1048_, 1);
lean_inc(v_a_1049_);
lean_dec_ref_known(v___x_1048_, 2);
v___x_1050_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_1019_, v___y_1021_, v___y_1022_, v_a_1049_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_a_1051_; 
v_a_1051_ = lean_ctor_get(v___x_1050_, 1);
lean_inc(v_a_1051_);
lean_dec_ref_known(v___x_1050_, 2);
v___y_1025_ = v___y_1020_;
v___y_1026_ = v_a_1051_;
goto v___jp_1024_;
}
else
{
lean_object* v_a_1052_; lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
lean_dec_ref(v___y_1020_);
lean_dec_ref(v_a_1019_);
lean_dec_ref(v_f_1018_);
v_a_1052_ = lean_ctor_get(v___x_1050_, 0);
v_a_1053_ = lean_ctor_get(v___x_1050_, 1);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_1050_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_inc(v_a_1052_);
lean_dec(v___x_1050_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1052_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
else
{
lean_object* v_a_1061_; lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
lean_dec_ref(v___y_1020_);
lean_dec_ref(v_a_1019_);
lean_dec_ref(v_f_1018_);
v_a_1061_ = lean_ctor_get(v___x_1048_, 0);
v_a_1062_ = lean_ctor_get(v___x_1048_, 1);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1064_ = v___x_1048_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_inc(v_a_1061_);
lean_dec(v___x_1048_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_a_1061_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v_a_1062_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
v___jp_1024_:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = l_Lean_Expr_app___override(v_f_1018_, v_a_1019_);
v___x_1028_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1027_, v___y_1026_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v_a_1029_; lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1038_; 
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
v_a_1030_ = lean_ctor_get(v___x_1028_, 1);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1032_ = v___x_1028_;
v_isShared_1033_ = v_isSharedCheck_1038_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_inc(v_a_1029_);
lean_dec(v___x_1028_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1038_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1034_; lean_object* v___x_1036_; 
v___x_1034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1034_, 0, v_a_1029_);
lean_ctor_set(v___x_1034_, 1, v___y_1025_);
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 0, v___x_1034_);
v___x_1036_ = v___x_1032_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1034_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v_a_1030_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
else
{
lean_object* v_a_1039_; lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1047_; 
lean_dec_ref(v___y_1025_);
v_a_1039_ = lean_ctor_get(v___x_1028_, 0);
v_a_1040_ = lean_ctor_get(v___x_1028_, 1);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1042_ = v___x_1028_;
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_inc(v_a_1039_);
lean_dec(v___x_1028_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1045_; 
if (v_isShared_1043_ == 0)
{
v___x_1045_ = v___x_1042_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_a_1039_);
lean_ctor_set(v_reuseFailAlloc_1046_, 1, v_a_1040_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__1___boxed(lean_object* v_f_1070_, lean_object* v_a_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
uint8_t v___y_25464__boxed_1076_; lean_object* v_res_1077_; 
v___y_25464__boxed_1076_ = lean_unbox(v___y_1073_);
v_res_1077_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__1(v_f_1070_, v_a_1071_, v___y_1072_, v___y_25464__boxed_1076_, v___y_1074_, v___y_1075_);
lean_dec_ref(v___y_1074_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4(lean_object* v_x_1078_, lean_object* v_t_1079_, lean_object* v_v_1080_, lean_object* v_b_1081_, uint8_t v_nondep_1082_, lean_object* v___y_1083_, uint8_t v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
lean_object* v___y_1088_; lean_object* v___y_1089_; 
if (v___y_1084_ == 0)
{
v___y_1088_ = v___y_1083_;
v___y_1089_ = v___y_1086_;
goto v___jp_1087_;
}
else
{
lean_object* v___x_1111_; 
v___x_1111_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_1079_, v___y_1084_, v___y_1085_, v___y_1086_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v_a_1112_; lean_object* v___x_1113_; 
v_a_1112_ = lean_ctor_get(v___x_1111_, 1);
lean_inc(v_a_1112_);
lean_dec_ref_known(v___x_1111_, 2);
v___x_1113_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_v_1080_, v___y_1084_, v___y_1085_, v_a_1112_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_object* v_a_1114_; lean_object* v___x_1115_; 
v_a_1114_ = lean_ctor_get(v___x_1113_, 1);
lean_inc(v_a_1114_);
lean_dec_ref_known(v___x_1113_, 2);
v___x_1115_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_1081_, v___y_1084_, v___y_1085_, v_a_1114_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 1);
lean_inc(v_a_1116_);
lean_dec_ref_known(v___x_1115_, 2);
v___y_1088_ = v___y_1083_;
v___y_1089_ = v_a_1116_;
goto v___jp_1087_;
}
else
{
lean_object* v_a_1117_; lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
lean_dec_ref(v___y_1083_);
lean_dec_ref(v_b_1081_);
lean_dec_ref(v_v_1080_);
lean_dec_ref(v_t_1079_);
lean_dec(v_x_1078_);
v_a_1117_ = lean_ctor_get(v___x_1115_, 0);
v_a_1118_ = lean_ctor_get(v___x_1115_, 1);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1115_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_inc(v_a_1117_);
lean_dec(v___x_1115_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1117_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v_a_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
else
{
lean_object* v_a_1126_; lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
lean_dec_ref(v___y_1083_);
lean_dec_ref(v_b_1081_);
lean_dec_ref(v_v_1080_);
lean_dec_ref(v_t_1079_);
lean_dec(v_x_1078_);
v_a_1126_ = lean_ctor_get(v___x_1113_, 0);
v_a_1127_ = lean_ctor_get(v___x_1113_, 1);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1129_ = v___x_1113_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_inc(v_a_1126_);
lean_dec(v___x_1113_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1126_);
lean_ctor_set(v_reuseFailAlloc_1133_, 1, v_a_1127_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
else
{
lean_object* v_a_1135_; lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1143_; 
lean_dec_ref(v___y_1083_);
lean_dec_ref(v_b_1081_);
lean_dec_ref(v_v_1080_);
lean_dec_ref(v_t_1079_);
lean_dec(v_x_1078_);
v_a_1135_ = lean_ctor_get(v___x_1111_, 0);
v_a_1136_ = lean_ctor_get(v___x_1111_, 1);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1138_ = v___x_1111_;
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_inc(v_a_1135_);
lean_dec(v___x_1111_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; 
if (v_isShared_1139_ == 0)
{
v___x_1141_ = v___x_1138_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1135_);
lean_ctor_set(v_reuseFailAlloc_1142_, 1, v_a_1136_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
}
v___jp_1087_:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = l_Lean_Expr_letE___override(v_x_1078_, v_t_1079_, v_v_1080_, v_b_1081_, v_nondep_1082_);
v___x_1091_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1090_, v___y_1089_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_a_1092_; lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1101_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
v_a_1093_ = lean_ctor_get(v___x_1091_, 1);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1095_ = v___x_1091_;
v_isShared_1096_ = v_isSharedCheck_1101_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_inc(v_a_1092_);
lean_dec(v___x_1091_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1101_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1097_; lean_object* v___x_1099_; 
v___x_1097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1097_, 0, v_a_1092_);
lean_ctor_set(v___x_1097_, 1, v___y_1088_);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 0, v___x_1097_);
v___x_1099_ = v___x_1095_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1097_);
lean_ctor_set(v_reuseFailAlloc_1100_, 1, v_a_1093_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
else
{
lean_object* v_a_1102_; lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
lean_dec_ref(v___y_1088_);
v_a_1102_ = lean_ctor_get(v___x_1091_, 0);
v_a_1103_ = lean_ctor_get(v___x_1091_, 1);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___x_1091_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_inc(v_a_1102_);
lean_dec(v___x_1091_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1102_);
lean_ctor_set(v_reuseFailAlloc_1109_, 1, v_a_1103_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4___boxed(lean_object* v_x_1144_, lean_object* v_t_1145_, lean_object* v_v_1146_, lean_object* v_b_1147_, lean_object* v_nondep_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
uint8_t v_nondep_boxed_1153_; uint8_t v___y_25570__boxed_1154_; lean_object* v_res_1155_; 
v_nondep_boxed_1153_ = lean_unbox(v_nondep_1148_);
v___y_25570__boxed_1154_ = lean_unbox(v___y_1150_);
v_res_1155_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4(v_x_1144_, v_t_1145_, v_v_1146_, v_b_1147_, v_nondep_boxed_1153_, v___y_1149_, v___y_25570__boxed_1154_, v___y_1151_, v___y_1152_);
lean_dec_ref(v___y_1151_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7(lean_object* v_msg_1163_, lean_object* v___y_1164_, uint8_t v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v___f_1168_; lean_object* v___f_1169_; lean_object* v___f_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___f_1180_; lean_object* v___f_1181_; lean_object* v___f_1182_; lean_object* v___f_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_24789__overap_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___f_1168_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__0));
v___f_1169_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__1));
v___f_1170_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__2));
v___x_1171_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__3));
v___x_1172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1171_);
lean_ctor_set(v___x_1172_, 1, v___f_1168_);
v___x_1173_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__4));
v___x_1174_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__5));
v___x_1175_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1172_);
lean_ctor_set(v___x_1175_, 1, v___x_1173_);
lean_ctor_set(v___x_1175_, 2, v___f_1169_);
lean_ctor_set(v___x_1175_, 3, v___f_1170_);
lean_ctor_set(v___x_1175_, 4, v___x_1174_);
v___x_1176_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___closed__6));
v___x_1177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1175_);
lean_ctor_set(v___x_1177_, 1, v___x_1176_);
v___x_1178_ = l_ReaderT_instMonad___redArg(v___x_1177_);
v___x_1179_ = l_ReaderT_instMonad___redArg(v___x_1178_);
lean_inc_ref_n(v___x_1179_, 6);
v___f_1180_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1180_, 0, v___x_1179_);
v___f_1181_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1181_, 0, v___x_1179_);
v___f_1182_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_1182_, 0, v___x_1179_);
v___f_1183_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_1183_, 0, v___x_1179_);
v___x_1184_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_1184_, 0, lean_box(0));
lean_closure_set(v___x_1184_, 1, lean_box(0));
lean_closure_set(v___x_1184_, 2, v___x_1179_);
v___x_1185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1184_);
lean_ctor_set(v___x_1185_, 1, v___f_1180_);
v___x_1186_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_1186_, 0, lean_box(0));
lean_closure_set(v___x_1186_, 1, lean_box(0));
lean_closure_set(v___x_1186_, 2, v___x_1179_);
v___x_1187_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1185_);
lean_ctor_set(v___x_1187_, 1, v___x_1186_);
lean_ctor_set(v___x_1187_, 2, v___f_1181_);
lean_ctor_set(v___x_1187_, 3, v___f_1182_);
lean_ctor_set(v___x_1187_, 4, v___f_1183_);
v___x_1188_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_1188_, 0, lean_box(0));
lean_closure_set(v___x_1188_, 1, lean_box(0));
lean_closure_set(v___x_1188_, 2, v___x_1179_);
v___x_1189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1187_);
lean_ctor_set(v___x_1189_, 1, v___x_1188_);
v___x_1190_ = l_Lean_instInhabitedExpr;
v___x_1191_ = l_instInhabitedOfMonad___redArg(v___x_1189_, v___x_1190_);
v___x_24789__overap_1192_ = lean_panic_fn_borrowed(v___x_1191_, v_msg_1163_);
lean_dec(v___x_1191_);
v___x_1193_ = lean_box(v___y_1165_);
lean_inc_ref(v___y_1166_);
v___x_1194_ = lean_apply_4(v___x_24789__overap_1192_, v___y_1164_, v___x_1193_, v___y_1166_, v___y_1167_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7___boxed(lean_object* v_msg_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
uint8_t v___y_25713__boxed_1200_; lean_object* v_res_1201_; 
v___y_25713__boxed_1200_ = lean_unbox(v___y_1197_);
v_res_1201_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7(v_msg_1195_, v___y_1196_, v___y_25713__boxed_1200_, v___y_1198_, v___y_1199_);
lean_dec_ref(v___y_1198_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__5(lean_object* v_d_1202_, lean_object* v_e_1203_, lean_object* v___y_1204_, uint8_t v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v___y_1209_; lean_object* v___y_1210_; 
if (v___y_1205_ == 0)
{
v___y_1209_ = v___y_1204_;
v___y_1210_ = v___y_1207_;
goto v___jp_1208_;
}
else
{
lean_object* v___x_1232_; 
v___x_1232_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_1203_, v___y_1205_, v___y_1206_, v___y_1207_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v_a_1233_; 
v_a_1233_ = lean_ctor_get(v___x_1232_, 1);
lean_inc(v_a_1233_);
lean_dec_ref_known(v___x_1232_, 2);
v___y_1209_ = v___y_1204_;
v___y_1210_ = v_a_1233_;
goto v___jp_1208_;
}
else
{
lean_object* v_a_1234_; lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1242_; 
lean_dec_ref(v___y_1204_);
lean_dec_ref(v_e_1203_);
lean_dec(v_d_1202_);
v_a_1234_ = lean_ctor_get(v___x_1232_, 0);
v_a_1235_ = lean_ctor_get(v___x_1232_, 1);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1237_ = v___x_1232_;
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_inc(v_a_1234_);
lean_dec(v___x_1232_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1240_; 
if (v_isShared_1238_ == 0)
{
v___x_1240_ = v___x_1237_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_a_1234_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v_a_1235_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
v___jp_1208_:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = l_Lean_Expr_mdata___override(v_d_1202_, v_e_1203_);
v___x_1212_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1211_, v___y_1210_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v_a_1213_; lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1222_; 
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
v_a_1214_ = lean_ctor_get(v___x_1212_, 1);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1216_ = v___x_1212_;
v_isShared_1217_ = v_isSharedCheck_1222_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_inc(v_a_1213_);
lean_dec(v___x_1212_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1222_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1218_; lean_object* v___x_1220_; 
v___x_1218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1218_, 0, v_a_1213_);
lean_ctor_set(v___x_1218_, 1, v___y_1209_);
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 0, v___x_1218_);
v___x_1220_ = v___x_1216_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v___x_1218_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v_a_1214_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
else
{
lean_object* v_a_1223_; lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1231_; 
lean_dec_ref(v___y_1209_);
v_a_1223_ = lean_ctor_get(v___x_1212_, 0);
v_a_1224_ = lean_ctor_get(v___x_1212_, 1);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1226_ = v___x_1212_;
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_a_1224_);
lean_inc(v_a_1223_);
lean_dec(v___x_1212_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1229_; 
if (v_isShared_1227_ == 0)
{
v___x_1229_ = v___x_1226_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_a_1223_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v_a_1224_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__5___boxed(lean_object* v_d_1243_, lean_object* v_e_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
uint8_t v___y_25784__boxed_1249_; lean_object* v_res_1250_; 
v___y_25784__boxed_1249_ = lean_unbox(v___y_1246_);
v_res_1250_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__5(v_d_1243_, v_e_1244_, v___y_1245_, v___y_25784__boxed_1249_, v___y_1247_, v___y_1248_);
lean_dec_ref(v___y_1247_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__3(lean_object* v_x_1251_, uint8_t v_bi_1252_, lean_object* v_t_1253_, lean_object* v_b_1254_, lean_object* v___y_1255_, uint8_t v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v___y_1260_; lean_object* v___y_1261_; 
if (v___y_1256_ == 0)
{
v___y_1260_ = v___y_1255_;
v___y_1261_ = v___y_1258_;
goto v___jp_1259_;
}
else
{
lean_object* v___x_1283_; 
v___x_1283_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_1253_, v___y_1256_, v___y_1257_, v___y_1258_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; lean_object* v___x_1285_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 1);
lean_inc(v_a_1284_);
lean_dec_ref_known(v___x_1283_, 2);
v___x_1285_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_1254_, v___y_1256_, v___y_1257_, v_a_1284_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v_a_1286_; 
v_a_1286_ = lean_ctor_get(v___x_1285_, 1);
lean_inc(v_a_1286_);
lean_dec_ref_known(v___x_1285_, 2);
v___y_1260_ = v___y_1255_;
v___y_1261_ = v_a_1286_;
goto v___jp_1259_;
}
else
{
lean_object* v_a_1287_; lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_dec_ref(v___y_1255_);
lean_dec_ref(v_b_1254_);
lean_dec_ref(v_t_1253_);
lean_dec(v_x_1251_);
v_a_1287_ = lean_ctor_get(v___x_1285_, 0);
v_a_1288_ = lean_ctor_get(v___x_1285_, 1);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1285_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_inc(v_a_1287_);
lean_dec(v___x_1285_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1287_);
lean_ctor_set(v_reuseFailAlloc_1294_, 1, v_a_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
else
{
lean_object* v_a_1296_; lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
lean_dec_ref(v___y_1255_);
lean_dec_ref(v_b_1254_);
lean_dec_ref(v_t_1253_);
lean_dec(v_x_1251_);
v_a_1296_ = lean_ctor_get(v___x_1283_, 0);
v_a_1297_ = lean_ctor_get(v___x_1283_, 1);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1299_ = v___x_1283_;
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_inc(v_a_1296_);
lean_dec(v___x_1283_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1302_; 
if (v_isShared_1300_ == 0)
{
v___x_1302_ = v___x_1299_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_a_1296_);
lean_ctor_set(v_reuseFailAlloc_1303_, 1, v_a_1297_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
v___jp_1259_:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1262_ = l_Lean_Expr_forallE___override(v_x_1251_, v_t_1253_, v_b_1254_, v_bi_1252_);
v___x_1263_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1262_, v___y_1261_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1273_; 
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
v_a_1265_ = lean_ctor_get(v___x_1263_, 1);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1267_ = v___x_1263_;
v_isShared_1268_ = v_isSharedCheck_1273_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_inc(v_a_1264_);
lean_dec(v___x_1263_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1273_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1269_; lean_object* v___x_1271_; 
v___x_1269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1269_, 0, v_a_1264_);
lean_ctor_set(v___x_1269_, 1, v___y_1260_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 0, v___x_1269_);
v___x_1271_ = v___x_1267_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1269_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v_a_1265_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
else
{
lean_object* v_a_1274_; lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1282_; 
lean_dec_ref(v___y_1260_);
v_a_1274_ = lean_ctor_get(v___x_1263_, 0);
v_a_1275_ = lean_ctor_get(v___x_1263_, 1);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1277_ = v___x_1263_;
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_inc(v_a_1274_);
lean_dec(v___x_1263_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_a_1274_);
lean_ctor_set(v_reuseFailAlloc_1281_, 1, v_a_1275_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__3___boxed(lean_object* v_x_1305_, lean_object* v_bi_1306_, lean_object* v_t_1307_, lean_object* v_b_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
uint8_t v_bi_boxed_1313_; uint8_t v___y_25867__boxed_1314_; lean_object* v_res_1315_; 
v_bi_boxed_1313_ = lean_unbox(v_bi_1306_);
v___y_25867__boxed_1314_ = lean_unbox(v___y_1310_);
v_res_1315_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__3(v_x_1305_, v_bi_boxed_1313_, v_t_1307_, v_b_1308_, v___y_1309_, v___y_25867__boxed_1314_, v___y_1311_, v___y_1312_);
lean_dec_ref(v___y_1311_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10___redArg(lean_object* v_a_1316_, lean_object* v_x_1317_){
_start:
{
if (lean_obj_tag(v_x_1317_) == 0)
{
lean_object* v___x_1318_; 
v___x_1318_ = lean_box(0);
return v___x_1318_;
}
else
{
lean_object* v_key_1319_; lean_object* v_value_1320_; lean_object* v_tail_1321_; lean_object* v_fst_1322_; lean_object* v_snd_1323_; lean_object* v_fst_1324_; lean_object* v_snd_1325_; size_t v___x_1326_; size_t v___x_1327_; uint8_t v___x_1328_; 
v_key_1319_ = lean_ctor_get(v_x_1317_, 0);
v_value_1320_ = lean_ctor_get(v_x_1317_, 1);
v_tail_1321_ = lean_ctor_get(v_x_1317_, 2);
v_fst_1322_ = lean_ctor_get(v_key_1319_, 0);
v_snd_1323_ = lean_ctor_get(v_key_1319_, 1);
v_fst_1324_ = lean_ctor_get(v_a_1316_, 0);
v_snd_1325_ = lean_ctor_get(v_a_1316_, 1);
v___x_1326_ = lean_ptr_addr(v_fst_1322_);
v___x_1327_ = lean_ptr_addr(v_fst_1324_);
v___x_1328_ = lean_usize_dec_eq(v___x_1326_, v___x_1327_);
if (v___x_1328_ == 0)
{
v_x_1317_ = v_tail_1321_;
goto _start;
}
else
{
uint8_t v___x_1330_; 
v___x_1330_ = lean_nat_dec_eq(v_snd_1323_, v_snd_1325_);
if (v___x_1330_ == 0)
{
v_x_1317_ = v_tail_1321_;
goto _start;
}
else
{
lean_object* v___x_1332_; 
lean_inc(v_value_1320_);
v___x_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1332_, 0, v_value_1320_);
return v___x_1332_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10___redArg___boxed(lean_object* v_a_1333_, lean_object* v_x_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10___redArg(v_a_1333_, v_x_1334_);
lean_dec(v_x_1334_);
lean_dec_ref(v_a_1333_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2___redArg(lean_object* v_m_1336_, lean_object* v_a_1337_){
_start:
{
lean_object* v_buckets_1338_; lean_object* v_fst_1339_; lean_object* v_snd_1340_; lean_object* v___x_1341_; size_t v___x_1342_; size_t v___x_1343_; size_t v___x_1344_; uint64_t v___x_1345_; uint64_t v___x_1346_; uint64_t v___x_1347_; uint64_t v___x_1348_; uint64_t v___x_1349_; uint64_t v_fold_1350_; uint64_t v___x_1351_; uint64_t v___x_1352_; uint64_t v___x_1353_; size_t v___x_1354_; size_t v___x_1355_; size_t v___x_1356_; size_t v___x_1357_; size_t v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v_buckets_1338_ = lean_ctor_get(v_m_1336_, 1);
v_fst_1339_ = lean_ctor_get(v_a_1337_, 0);
v_snd_1340_ = lean_ctor_get(v_a_1337_, 1);
v___x_1341_ = lean_array_get_size(v_buckets_1338_);
v___x_1342_ = lean_ptr_addr(v_fst_1339_);
v___x_1343_ = ((size_t)3ULL);
v___x_1344_ = lean_usize_shift_right(v___x_1342_, v___x_1343_);
v___x_1345_ = lean_usize_to_uint64(v___x_1344_);
v___x_1346_ = lean_uint64_of_nat(v_snd_1340_);
v___x_1347_ = lean_uint64_mix_hash(v___x_1345_, v___x_1346_);
v___x_1348_ = 32ULL;
v___x_1349_ = lean_uint64_shift_right(v___x_1347_, v___x_1348_);
v_fold_1350_ = lean_uint64_xor(v___x_1347_, v___x_1349_);
v___x_1351_ = 16ULL;
v___x_1352_ = lean_uint64_shift_right(v_fold_1350_, v___x_1351_);
v___x_1353_ = lean_uint64_xor(v_fold_1350_, v___x_1352_);
v___x_1354_ = lean_uint64_to_usize(v___x_1353_);
v___x_1355_ = lean_usize_of_nat(v___x_1341_);
v___x_1356_ = ((size_t)1ULL);
v___x_1357_ = lean_usize_sub(v___x_1355_, v___x_1356_);
v___x_1358_ = lean_usize_land(v___x_1354_, v___x_1357_);
v___x_1359_ = lean_array_uget_borrowed(v_buckets_1338_, v___x_1358_);
v___x_1360_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10___redArg(v_a_1337_, v___x_1359_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_m_1361_, lean_object* v_a_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2___redArg(v_m_1361_, v_a_1362_);
lean_dec_ref(v_a_1362_);
lean_dec_ref(v_m_1361_);
return v_res_1363_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1367_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__2));
v___x_1368_ = lean_unsigned_to_nat(67u);
v___x_1369_ = lean_unsigned_to_nat(35u);
v___x_1370_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__1));
v___x_1371_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__0));
v___x_1372_ = l_mkPanicMessageWithDecl(v___x_1371_, v___x_1370_, v___x_1369_, v___x_1368_, v___x_1367_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0(lean_object* v_n_1373_, lean_object* v_xs_1374_, lean_object* v_e_1375_, lean_object* v_offset_1376_, lean_object* v_a_1377_, uint8_t v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_){
_start:
{
switch(lean_obj_tag(v_e_1375_))
{
case 5:
{
lean_object* v_fn_1381_; lean_object* v_arg_1382_; lean_object* v___x_1383_; 
v_fn_1381_ = lean_ctor_get(v_e_1375_, 0);
v_arg_1382_ = lean_ctor_get(v_e_1375_, 1);
lean_inc(v_offset_1376_);
lean_inc_ref(v_fn_1381_);
v___x_1383_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1373_, v_xs_1374_, v_fn_1381_, v_offset_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v_a_1385_; lean_object* v_fst_1386_; lean_object* v_snd_1387_; lean_object* v___x_1388_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_a_1384_);
v_a_1385_ = lean_ctor_get(v___x_1383_, 1);
lean_inc(v_a_1385_);
lean_dec_ref_known(v___x_1383_, 2);
v_fst_1386_ = lean_ctor_get(v_a_1384_, 0);
lean_inc(v_fst_1386_);
v_snd_1387_ = lean_ctor_get(v_a_1384_, 1);
lean_inc(v_snd_1387_);
lean_dec(v_a_1384_);
lean_inc_ref(v_arg_1382_);
v___x_1388_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1373_, v_xs_1374_, v_arg_1382_, v_offset_1376_, v_snd_1387_, v_a_1378_, v_a_1379_, v_a_1385_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v_a_1389_; lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1414_; 
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
v_a_1390_ = lean_ctor_get(v___x_1388_, 1);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1392_ = v___x_1388_;
v_isShared_1393_ = v_isSharedCheck_1414_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_inc(v_a_1389_);
lean_dec(v___x_1388_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1414_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v_fst_1394_; lean_object* v_snd_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1413_; 
v_fst_1394_ = lean_ctor_get(v_a_1389_, 0);
v_snd_1395_ = lean_ctor_get(v_a_1389_, 1);
v_isSharedCheck_1413_ = !lean_is_exclusive(v_a_1389_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1397_ = v_a_1389_;
v_isShared_1398_ = v_isSharedCheck_1413_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_snd_1395_);
lean_inc(v_fst_1394_);
lean_dec(v_a_1389_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1413_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
size_t v___x_1399_; size_t v___x_1400_; uint8_t v___x_1401_; 
v___x_1399_ = lean_ptr_addr(v_fn_1381_);
v___x_1400_ = lean_ptr_addr(v_fst_1386_);
v___x_1401_ = lean_usize_dec_eq(v___x_1399_, v___x_1400_);
if (v___x_1401_ == 0)
{
lean_object* v___x_1402_; 
lean_del_object(v___x_1397_);
lean_del_object(v___x_1392_);
lean_dec_ref_known(v_e_1375_, 2);
v___x_1402_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__1(v_fst_1386_, v_fst_1394_, v_snd_1395_, v_a_1378_, v_a_1379_, v_a_1390_);
return v___x_1402_;
}
else
{
size_t v___x_1403_; size_t v___x_1404_; uint8_t v___x_1405_; 
v___x_1403_ = lean_ptr_addr(v_arg_1382_);
v___x_1404_ = lean_ptr_addr(v_fst_1394_);
v___x_1405_ = lean_usize_dec_eq(v___x_1403_, v___x_1404_);
if (v___x_1405_ == 0)
{
lean_object* v___x_1406_; 
lean_del_object(v___x_1397_);
lean_del_object(v___x_1392_);
lean_dec_ref_known(v_e_1375_, 2);
v___x_1406_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__1(v_fst_1386_, v_fst_1394_, v_snd_1395_, v_a_1378_, v_a_1379_, v_a_1390_);
return v___x_1406_;
}
else
{
lean_object* v___x_1408_; 
lean_dec(v_fst_1394_);
lean_dec(v_fst_1386_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 0, v_e_1375_);
v___x_1408_ = v___x_1397_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_e_1375_);
lean_ctor_set(v_reuseFailAlloc_1412_, 1, v_snd_1395_);
v___x_1408_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
lean_object* v___x_1410_; 
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 0, v___x_1408_);
v___x_1410_ = v___x_1392_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v___x_1408_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v_a_1390_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1386_);
lean_dec_ref_known(v_e_1375_, 2);
return v___x_1388_;
}
}
else
{
lean_dec_ref_known(v_e_1375_, 2);
lean_dec(v_offset_1376_);
return v___x_1383_;
}
}
case 6:
{
lean_object* v_binderName_1415_; lean_object* v_binderType_1416_; lean_object* v_body_1417_; uint8_t v_binderInfo_1418_; lean_object* v___x_1419_; 
v_binderName_1415_ = lean_ctor_get(v_e_1375_, 0);
v_binderType_1416_ = lean_ctor_get(v_e_1375_, 1);
v_body_1417_ = lean_ctor_get(v_e_1375_, 2);
v_binderInfo_1418_ = lean_ctor_get_uint8(v_e_1375_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1376_);
lean_inc_ref(v_binderType_1416_);
v___x_1419_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1373_, v_xs_1374_, v_binderType_1416_, v_offset_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v_a_1420_; lean_object* v_a_1421_; lean_object* v_fst_1422_; lean_object* v_snd_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_a_1420_);
v_a_1421_ = lean_ctor_get(v___x_1419_, 1);
lean_inc(v_a_1421_);
lean_dec_ref_known(v___x_1419_, 2);
v_fst_1422_ = lean_ctor_get(v_a_1420_, 0);
lean_inc(v_fst_1422_);
v_snd_1423_ = lean_ctor_get(v_a_1420_, 1);
lean_inc(v_snd_1423_);
lean_dec(v_a_1420_);
v___x_1424_ = lean_unsigned_to_nat(1u);
v___x_1425_ = lean_nat_add(v_offset_1376_, v___x_1424_);
lean_dec(v_offset_1376_);
lean_inc_ref(v_body_1417_);
v___x_1426_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1373_, v_xs_1374_, v_body_1417_, v___x_1425_, v_snd_1423_, v_a_1378_, v_a_1379_, v_a_1421_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1452_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
v_a_1428_ = lean_ctor_get(v___x_1426_, 1);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1430_ = v___x_1426_;
v_isShared_1431_ = v_isSharedCheck_1452_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_inc(v_a_1427_);
lean_dec(v___x_1426_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1452_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v_fst_1432_; lean_object* v_snd_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1451_; 
v_fst_1432_ = lean_ctor_get(v_a_1427_, 0);
v_snd_1433_ = lean_ctor_get(v_a_1427_, 1);
v_isSharedCheck_1451_ = !lean_is_exclusive(v_a_1427_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1435_ = v_a_1427_;
v_isShared_1436_ = v_isSharedCheck_1451_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_snd_1433_);
lean_inc(v_fst_1432_);
lean_dec(v_a_1427_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1451_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
size_t v___x_1437_; size_t v___x_1438_; uint8_t v___x_1439_; 
v___x_1437_ = lean_ptr_addr(v_binderType_1416_);
v___x_1438_ = lean_ptr_addr(v_fst_1422_);
v___x_1439_ = lean_usize_dec_eq(v___x_1437_, v___x_1438_);
if (v___x_1439_ == 0)
{
lean_object* v___x_1440_; 
lean_inc(v_binderName_1415_);
lean_del_object(v___x_1435_);
lean_del_object(v___x_1430_);
lean_dec_ref_known(v_e_1375_, 3);
v___x_1440_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__2(v_binderName_1415_, v_binderInfo_1418_, v_fst_1422_, v_fst_1432_, v_snd_1433_, v_a_1378_, v_a_1379_, v_a_1428_);
return v___x_1440_;
}
else
{
size_t v___x_1441_; size_t v___x_1442_; uint8_t v___x_1443_; 
v___x_1441_ = lean_ptr_addr(v_body_1417_);
v___x_1442_ = lean_ptr_addr(v_fst_1432_);
v___x_1443_ = lean_usize_dec_eq(v___x_1441_, v___x_1442_);
if (v___x_1443_ == 0)
{
lean_object* v___x_1444_; 
lean_inc(v_binderName_1415_);
lean_del_object(v___x_1435_);
lean_del_object(v___x_1430_);
lean_dec_ref_known(v_e_1375_, 3);
v___x_1444_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__2(v_binderName_1415_, v_binderInfo_1418_, v_fst_1422_, v_fst_1432_, v_snd_1433_, v_a_1378_, v_a_1379_, v_a_1428_);
return v___x_1444_;
}
else
{
lean_object* v___x_1446_; 
lean_dec(v_fst_1432_);
lean_dec(v_fst_1422_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 0, v_e_1375_);
v___x_1446_ = v___x_1435_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_e_1375_);
lean_ctor_set(v_reuseFailAlloc_1450_, 1, v_snd_1433_);
v___x_1446_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
lean_object* v___x_1448_; 
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v___x_1446_);
v___x_1448_ = v___x_1430_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v___x_1446_);
lean_ctor_set(v_reuseFailAlloc_1449_, 1, v_a_1428_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1422_);
lean_dec_ref_known(v_e_1375_, 3);
return v___x_1426_;
}
}
else
{
lean_dec_ref_known(v_e_1375_, 3);
lean_dec(v_offset_1376_);
return v___x_1419_;
}
}
case 7:
{
lean_object* v_binderName_1453_; lean_object* v_binderType_1454_; lean_object* v_body_1455_; uint8_t v_binderInfo_1456_; lean_object* v___x_1457_; 
v_binderName_1453_ = lean_ctor_get(v_e_1375_, 0);
v_binderType_1454_ = lean_ctor_get(v_e_1375_, 1);
v_body_1455_ = lean_ctor_get(v_e_1375_, 2);
v_binderInfo_1456_ = lean_ctor_get_uint8(v_e_1375_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1376_);
lean_inc_ref(v_binderType_1454_);
v___x_1457_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1373_, v_xs_1374_, v_binderType_1454_, v_offset_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; lean_object* v_a_1459_; lean_object* v_fst_1460_; lean_object* v_snd_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_a_1458_);
v_a_1459_ = lean_ctor_get(v___x_1457_, 1);
lean_inc(v_a_1459_);
lean_dec_ref_known(v___x_1457_, 2);
v_fst_1460_ = lean_ctor_get(v_a_1458_, 0);
lean_inc(v_fst_1460_);
v_snd_1461_ = lean_ctor_get(v_a_1458_, 1);
lean_inc(v_snd_1461_);
lean_dec(v_a_1458_);
v___x_1462_ = lean_unsigned_to_nat(1u);
v___x_1463_ = lean_nat_add(v_offset_1376_, v___x_1462_);
lean_dec(v_offset_1376_);
lean_inc_ref(v_body_1455_);
v___x_1464_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1373_, v_xs_1374_, v_body_1455_, v___x_1463_, v_snd_1461_, v_a_1378_, v_a_1379_, v_a_1459_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v_a_1465_; lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1490_; 
v_a_1465_ = lean_ctor_get(v___x_1464_, 0);
v_a_1466_ = lean_ctor_get(v___x_1464_, 1);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1468_ = v___x_1464_;
v_isShared_1469_ = v_isSharedCheck_1490_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_inc(v_a_1465_);
lean_dec(v___x_1464_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1490_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v_fst_1470_; lean_object* v_snd_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1489_; 
v_fst_1470_ = lean_ctor_get(v_a_1465_, 0);
v_snd_1471_ = lean_ctor_get(v_a_1465_, 1);
v_isSharedCheck_1489_ = !lean_is_exclusive(v_a_1465_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1473_ = v_a_1465_;
v_isShared_1474_ = v_isSharedCheck_1489_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_snd_1471_);
lean_inc(v_fst_1470_);
lean_dec(v_a_1465_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1489_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
size_t v___x_1475_; size_t v___x_1476_; uint8_t v___x_1477_; 
v___x_1475_ = lean_ptr_addr(v_binderType_1454_);
v___x_1476_ = lean_ptr_addr(v_fst_1460_);
v___x_1477_ = lean_usize_dec_eq(v___x_1475_, v___x_1476_);
if (v___x_1477_ == 0)
{
lean_object* v___x_1478_; 
lean_inc(v_binderName_1453_);
lean_del_object(v___x_1473_);
lean_del_object(v___x_1468_);
lean_dec_ref_known(v_e_1375_, 3);
v___x_1478_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__3(v_binderName_1453_, v_binderInfo_1456_, v_fst_1460_, v_fst_1470_, v_snd_1471_, v_a_1378_, v_a_1379_, v_a_1466_);
return v___x_1478_;
}
else
{
size_t v___x_1479_; size_t v___x_1480_; uint8_t v___x_1481_; 
v___x_1479_ = lean_ptr_addr(v_body_1455_);
v___x_1480_ = lean_ptr_addr(v_fst_1470_);
v___x_1481_ = lean_usize_dec_eq(v___x_1479_, v___x_1480_);
if (v___x_1481_ == 0)
{
lean_object* v___x_1482_; 
lean_inc(v_binderName_1453_);
lean_del_object(v___x_1473_);
lean_del_object(v___x_1468_);
lean_dec_ref_known(v_e_1375_, 3);
v___x_1482_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__3(v_binderName_1453_, v_binderInfo_1456_, v_fst_1460_, v_fst_1470_, v_snd_1471_, v_a_1378_, v_a_1379_, v_a_1466_);
return v___x_1482_;
}
else
{
lean_object* v___x_1484_; 
lean_dec(v_fst_1470_);
lean_dec(v_fst_1460_);
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 0, v_e_1375_);
v___x_1484_ = v___x_1473_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_e_1375_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v_snd_1471_);
v___x_1484_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
lean_object* v___x_1486_; 
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 0, v___x_1484_);
v___x_1486_ = v___x_1468_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1484_);
lean_ctor_set(v_reuseFailAlloc_1487_, 1, v_a_1466_);
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
lean_dec(v_fst_1460_);
lean_dec_ref_known(v_e_1375_, 3);
return v___x_1464_;
}
}
else
{
lean_dec_ref_known(v_e_1375_, 3);
lean_dec(v_offset_1376_);
return v___x_1457_;
}
}
case 8:
{
lean_object* v_declName_1491_; lean_object* v_type_1492_; lean_object* v_value_1493_; lean_object* v_body_1494_; uint8_t v_nondep_1495_; lean_object* v___x_1496_; 
v_declName_1491_ = lean_ctor_get(v_e_1375_, 0);
v_type_1492_ = lean_ctor_get(v_e_1375_, 1);
v_value_1493_ = lean_ctor_get(v_e_1375_, 2);
v_body_1494_ = lean_ctor_get(v_e_1375_, 3);
v_nondep_1495_ = lean_ctor_get_uint8(v_e_1375_, sizeof(void*)*4 + 8);
lean_inc(v_offset_1376_);
lean_inc_ref(v_type_1492_);
v___x_1496_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1373_, v_xs_1374_, v_type_1492_, v_offset_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_a_1497_; lean_object* v_a_1498_; lean_object* v_fst_1499_; lean_object* v_snd_1500_; lean_object* v___x_1501_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
lean_inc(v_a_1497_);
v_a_1498_ = lean_ctor_get(v___x_1496_, 1);
lean_inc(v_a_1498_);
lean_dec_ref_known(v___x_1496_, 2);
v_fst_1499_ = lean_ctor_get(v_a_1497_, 0);
lean_inc(v_fst_1499_);
v_snd_1500_ = lean_ctor_get(v_a_1497_, 1);
lean_inc(v_snd_1500_);
lean_dec(v_a_1497_);
lean_inc(v_offset_1376_);
lean_inc_ref(v_value_1493_);
v___x_1501_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1373_, v_xs_1374_, v_value_1493_, v_offset_1376_, v_snd_1500_, v_a_1378_, v_a_1379_, v_a_1498_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_object* v_a_1502_; lean_object* v_a_1503_; lean_object* v_fst_1504_; lean_object* v_snd_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v_a_1502_ = lean_ctor_get(v___x_1501_, 0);
lean_inc(v_a_1502_);
v_a_1503_ = lean_ctor_get(v___x_1501_, 1);
lean_inc(v_a_1503_);
lean_dec_ref_known(v___x_1501_, 2);
v_fst_1504_ = lean_ctor_get(v_a_1502_, 0);
lean_inc(v_fst_1504_);
v_snd_1505_ = lean_ctor_get(v_a_1502_, 1);
lean_inc(v_snd_1505_);
lean_dec(v_a_1502_);
v___x_1506_ = lean_unsigned_to_nat(1u);
v___x_1507_ = lean_nat_add(v_offset_1376_, v___x_1506_);
lean_dec(v_offset_1376_);
lean_inc_ref(v_body_1494_);
v___x_1508_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1373_, v_xs_1374_, v_body_1494_, v___x_1507_, v_snd_1505_, v_a_1378_, v_a_1379_, v_a_1503_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_object* v_a_1509_; lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1538_; 
v_a_1509_ = lean_ctor_get(v___x_1508_, 0);
v_a_1510_ = lean_ctor_get(v___x_1508_, 1);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1512_ = v___x_1508_;
v_isShared_1513_ = v_isSharedCheck_1538_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_inc(v_a_1509_);
lean_dec(v___x_1508_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1538_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v_fst_1514_; lean_object* v_snd_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1537_; 
v_fst_1514_ = lean_ctor_get(v_a_1509_, 0);
v_snd_1515_ = lean_ctor_get(v_a_1509_, 1);
v_isSharedCheck_1537_ = !lean_is_exclusive(v_a_1509_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1517_ = v_a_1509_;
v_isShared_1518_ = v_isSharedCheck_1537_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_snd_1515_);
lean_inc(v_fst_1514_);
lean_dec(v_a_1509_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1537_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
size_t v___x_1519_; size_t v___x_1520_; uint8_t v___x_1521_; 
v___x_1519_ = lean_ptr_addr(v_type_1492_);
v___x_1520_ = lean_ptr_addr(v_fst_1499_);
v___x_1521_ = lean_usize_dec_eq(v___x_1519_, v___x_1520_);
if (v___x_1521_ == 0)
{
lean_object* v___x_1522_; 
lean_inc(v_declName_1491_);
lean_del_object(v___x_1517_);
lean_del_object(v___x_1512_);
lean_dec_ref_known(v_e_1375_, 4);
v___x_1522_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4(v_declName_1491_, v_fst_1499_, v_fst_1504_, v_fst_1514_, v_nondep_1495_, v_snd_1515_, v_a_1378_, v_a_1379_, v_a_1510_);
return v___x_1522_;
}
else
{
size_t v___x_1523_; size_t v___x_1524_; uint8_t v___x_1525_; 
v___x_1523_ = lean_ptr_addr(v_value_1493_);
v___x_1524_ = lean_ptr_addr(v_fst_1504_);
v___x_1525_ = lean_usize_dec_eq(v___x_1523_, v___x_1524_);
if (v___x_1525_ == 0)
{
lean_object* v___x_1526_; 
lean_inc(v_declName_1491_);
lean_del_object(v___x_1517_);
lean_del_object(v___x_1512_);
lean_dec_ref_known(v_e_1375_, 4);
v___x_1526_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4(v_declName_1491_, v_fst_1499_, v_fst_1504_, v_fst_1514_, v_nondep_1495_, v_snd_1515_, v_a_1378_, v_a_1379_, v_a_1510_);
return v___x_1526_;
}
else
{
size_t v___x_1527_; size_t v___x_1528_; uint8_t v___x_1529_; 
v___x_1527_ = lean_ptr_addr(v_body_1494_);
v___x_1528_ = lean_ptr_addr(v_fst_1514_);
v___x_1529_ = lean_usize_dec_eq(v___x_1527_, v___x_1528_);
if (v___x_1529_ == 0)
{
lean_object* v___x_1530_; 
lean_inc(v_declName_1491_);
lean_del_object(v___x_1517_);
lean_del_object(v___x_1512_);
lean_dec_ref_known(v_e_1375_, 4);
v___x_1530_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4(v_declName_1491_, v_fst_1499_, v_fst_1504_, v_fst_1514_, v_nondep_1495_, v_snd_1515_, v_a_1378_, v_a_1379_, v_a_1510_);
return v___x_1530_;
}
else
{
lean_object* v___x_1532_; 
lean_dec(v_fst_1514_);
lean_dec(v_fst_1504_);
lean_dec(v_fst_1499_);
if (v_isShared_1518_ == 0)
{
lean_ctor_set(v___x_1517_, 0, v_e_1375_);
v___x_1532_ = v___x_1517_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_e_1375_);
lean_ctor_set(v_reuseFailAlloc_1536_, 1, v_snd_1515_);
v___x_1532_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
lean_object* v___x_1534_; 
if (v_isShared_1513_ == 0)
{
lean_ctor_set(v___x_1512_, 0, v___x_1532_);
v___x_1534_ = v___x_1512_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v___x_1532_);
lean_ctor_set(v_reuseFailAlloc_1535_, 1, v_a_1510_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
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
lean_dec(v_fst_1504_);
lean_dec(v_fst_1499_);
lean_dec_ref_known(v_e_1375_, 4);
return v___x_1508_;
}
}
else
{
lean_dec(v_fst_1499_);
lean_dec_ref_known(v_e_1375_, 4);
lean_dec(v_offset_1376_);
return v___x_1501_;
}
}
else
{
lean_dec_ref_known(v_e_1375_, 4);
lean_dec(v_offset_1376_);
return v___x_1496_;
}
}
case 10:
{
lean_object* v_data_1539_; lean_object* v_expr_1540_; lean_object* v___x_1541_; 
v_data_1539_ = lean_ctor_get(v_e_1375_, 0);
v_expr_1540_ = lean_ctor_get(v_e_1375_, 1);
lean_inc_ref(v_expr_1540_);
v___x_1541_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1373_, v_xs_1374_, v_expr_1540_, v_offset_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1563_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
v_a_1543_ = lean_ctor_get(v___x_1541_, 1);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1545_ = v___x_1541_;
v_isShared_1546_ = v_isSharedCheck_1563_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_inc(v_a_1542_);
lean_dec(v___x_1541_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1563_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v_fst_1547_; lean_object* v_snd_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1562_; 
v_fst_1547_ = lean_ctor_get(v_a_1542_, 0);
v_snd_1548_ = lean_ctor_get(v_a_1542_, 1);
v_isSharedCheck_1562_ = !lean_is_exclusive(v_a_1542_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1550_ = v_a_1542_;
v_isShared_1551_ = v_isSharedCheck_1562_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_snd_1548_);
lean_inc(v_fst_1547_);
lean_dec(v_a_1542_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1562_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
size_t v___x_1552_; size_t v___x_1553_; uint8_t v___x_1554_; 
v___x_1552_ = lean_ptr_addr(v_expr_1540_);
v___x_1553_ = lean_ptr_addr(v_fst_1547_);
v___x_1554_ = lean_usize_dec_eq(v___x_1552_, v___x_1553_);
if (v___x_1554_ == 0)
{
lean_object* v___x_1555_; 
lean_inc(v_data_1539_);
lean_del_object(v___x_1550_);
lean_del_object(v___x_1545_);
lean_dec_ref_known(v_e_1375_, 2);
v___x_1555_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__5(v_data_1539_, v_fst_1547_, v_snd_1548_, v_a_1378_, v_a_1379_, v_a_1543_);
return v___x_1555_;
}
else
{
lean_object* v___x_1557_; 
lean_dec(v_fst_1547_);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 0, v_e_1375_);
v___x_1557_ = v___x_1550_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_e_1375_);
lean_ctor_set(v_reuseFailAlloc_1561_, 1, v_snd_1548_);
v___x_1557_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
lean_object* v___x_1559_; 
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 0, v___x_1557_);
v___x_1559_ = v___x_1545_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1557_);
lean_ctor_set(v_reuseFailAlloc_1560_, 1, v_a_1543_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1375_, 2);
return v___x_1541_;
}
}
case 11:
{
lean_object* v_typeName_1564_; lean_object* v_idx_1565_; lean_object* v_struct_1566_; lean_object* v___x_1567_; 
v_typeName_1564_ = lean_ctor_get(v_e_1375_, 0);
v_idx_1565_ = lean_ctor_get(v_e_1375_, 1);
v_struct_1566_ = lean_ctor_get(v_e_1375_, 2);
lean_inc_ref(v_struct_1566_);
v___x_1567_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1373_, v_xs_1374_, v_struct_1566_, v_offset_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
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
v___x_1578_ = lean_ptr_addr(v_struct_1566_);
v___x_1579_ = lean_ptr_addr(v_fst_1573_);
v___x_1580_ = lean_usize_dec_eq(v___x_1578_, v___x_1579_);
if (v___x_1580_ == 0)
{
lean_object* v___x_1581_; 
lean_inc(v_idx_1565_);
lean_inc(v_typeName_1564_);
lean_del_object(v___x_1576_);
lean_del_object(v___x_1571_);
lean_dec_ref_known(v_e_1375_, 3);
v___x_1581_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__6(v_typeName_1564_, v_idx_1565_, v_fst_1573_, v_snd_1574_, v_a_1378_, v_a_1379_, v_a_1569_);
return v___x_1581_;
}
else
{
lean_object* v___x_1583_; 
lean_dec(v_fst_1573_);
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 0, v_e_1375_);
v___x_1583_ = v___x_1576_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_e_1375_);
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
lean_dec_ref_known(v_e_1375_, 3);
return v___x_1567_;
}
}
default: 
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
lean_dec(v_offset_1376_);
lean_dec_ref(v_e_1375_);
v___x_1590_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__3);
v___x_1591_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7(v___x_1590_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
return v___x_1591_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(lean_object* v_n_1592_, lean_object* v_xs_1593_, lean_object* v_e_1594_, lean_object* v_offset_1595_, lean_object* v_a_1596_, uint8_t v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_){
_start:
{
lean_object* v_key_1600_; lean_object* v___x_1601_; 
lean_inc(v_offset_1595_);
lean_inc_ref(v_e_1594_);
v_key_1600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1600_, 0, v_e_1594_);
lean_ctor_set(v_key_1600_, 1, v_offset_1595_);
v___x_1601_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2___redArg(v_a_1596_, v_key_1600_);
if (lean_obj_tag(v___x_1601_) == 1)
{
lean_object* v_val_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
lean_dec_ref_known(v_key_1600_, 2);
lean_dec(v_offset_1595_);
lean_dec_ref(v_e_1594_);
v_val_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_val_1602_);
lean_dec_ref_known(v___x_1601_, 1);
v___x_1603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1603_, 0, v_val_1602_);
lean_ctor_set(v___x_1603_, 1, v_a_1596_);
v___x_1604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
lean_ctor_set(v___x_1604_, 1, v_a_1599_);
return v___x_1604_;
}
else
{
lean_dec(v___x_1601_);
switch(lean_obj_tag(v_e_1594_))
{
case 0:
{
lean_object* v_deBruijnIndex_1605_; uint8_t v___x_1606_; 
v_deBruijnIndex_1605_ = lean_ctor_get(v_e_1594_, 0);
v___x_1606_ = lean_nat_dec_le(v_offset_1595_, v_deBruijnIndex_1605_);
if (v___x_1606_ == 0)
{
lean_object* v___x_1607_; 
lean_dec(v_offset_1595_);
v___x_1607_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1600_, v_e_1594_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_);
return v___x_1607_;
}
else
{
lean_object* v_size_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; uint8_t v___x_1614_; 
lean_inc(v_deBruijnIndex_1605_);
lean_dec_ref_known(v_e_1594_, 1);
v_size_1608_ = lean_ctor_get(v_xs_1593_, 2);
v___x_1609_ = l_Lean_instInhabitedExpr;
v___x_1610_ = lean_nat_sub(v_deBruijnIndex_1605_, v_offset_1595_);
lean_dec(v_offset_1595_);
lean_dec(v_deBruijnIndex_1605_);
v___x_1611_ = lean_nat_sub(v_n_1592_, v___x_1610_);
lean_dec(v___x_1610_);
v___x_1612_ = lean_unsigned_to_nat(1u);
v___x_1613_ = lean_nat_sub(v___x_1611_, v___x_1612_);
lean_dec(v___x_1611_);
v___x_1614_ = lean_nat_dec_lt(v___x_1613_, v_size_1608_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1615_; lean_object* v___x_1616_; 
lean_dec(v___x_1613_);
v___x_1615_ = l_outOfBounds___redArg(v___x_1609_);
v___x_1616_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1600_, v___x_1615_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_);
return v___x_1616_;
}
else
{
lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1617_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1609_, v_xs_1593_, v___x_1613_);
lean_dec(v___x_1613_);
v___x_1618_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1600_, v___x_1617_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_);
return v___x_1618_;
}
}
}
case 9:
{
lean_object* v___x_1619_; 
lean_dec(v_offset_1595_);
v___x_1619_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1600_, v_e_1594_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_);
return v___x_1619_;
}
case 2:
{
lean_object* v___x_1620_; 
lean_dec(v_offset_1595_);
v___x_1620_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1600_, v_e_1594_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_);
return v___x_1620_;
}
case 1:
{
lean_object* v___x_1621_; 
lean_dec(v_offset_1595_);
v___x_1621_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1600_, v_e_1594_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_);
return v___x_1621_;
}
case 4:
{
lean_object* v___x_1622_; 
lean_dec(v_offset_1595_);
v___x_1622_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1600_, v_e_1594_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_);
return v___x_1622_;
}
case 3:
{
lean_object* v___x_1623_; 
lean_dec(v_offset_1595_);
v___x_1623_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1600_, v_e_1594_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_);
return v___x_1623_;
}
default: 
{
lean_object* v___x_1624_; uint8_t v___x_1625_; 
v___x_1624_ = l_Lean_Expr_looseBVarRange(v_e_1594_);
v___x_1625_ = lean_nat_dec_le(v___x_1624_, v_offset_1595_);
lean_dec(v___x_1624_);
if (v___x_1625_ == 0)
{
switch(lean_obj_tag(v_e_1594_))
{
case 9:
{
lean_object* v___x_1626_; 
lean_dec(v_offset_1595_);
v___x_1626_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1600_, v_e_1594_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_);
return v___x_1626_;
}
case 2:
{
lean_object* v___x_1627_; 
lean_dec(v_offset_1595_);
v___x_1627_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1600_, v_e_1594_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_);
return v___x_1627_;
}
case 0:
{
lean_object* v___x_1628_; 
lean_dec(v_offset_1595_);
v___x_1628_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1600_, v_e_1594_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_);
return v___x_1628_;
}
case 1:
{
lean_object* v___x_1629_; 
lean_dec(v_offset_1595_);
v___x_1629_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1600_, v_e_1594_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_);
return v___x_1629_;
}
case 4:
{
lean_object* v___x_1630_; 
lean_dec(v_offset_1595_);
v___x_1630_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1600_, v_e_1594_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_);
return v___x_1630_;
}
case 3:
{
lean_object* v___x_1631_; 
lean_dec(v_offset_1595_);
v___x_1631_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1600_, v_e_1594_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_);
return v___x_1631_;
}
default: 
{
lean_object* v___x_1632_; 
v___x_1632_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0(v_n_1592_, v_xs_1593_, v_e_1594_, v_offset_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v_a_1633_; lean_object* v_a_1634_; lean_object* v_fst_1635_; lean_object* v_snd_1636_; lean_object* v___x_1637_; 
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
lean_inc(v_a_1633_);
v_a_1634_ = lean_ctor_get(v___x_1632_, 1);
lean_inc(v_a_1634_);
lean_dec_ref_known(v___x_1632_, 2);
v_fst_1635_ = lean_ctor_get(v_a_1633_, 0);
lean_inc(v_fst_1635_);
v_snd_1636_ = lean_ctor_get(v_a_1633_, 1);
lean_inc(v_snd_1636_);
lean_dec(v_a_1633_);
v___x_1637_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1600_, v_fst_1635_, v_snd_1636_, v_a_1597_, v_a_1598_, v_a_1634_);
return v___x_1637_;
}
else
{
lean_dec_ref_known(v_key_1600_, 2);
return v___x_1632_;
}
}
}
}
else
{
lean_object* v___x_1638_; 
lean_dec(v_offset_1595_);
v___x_1638_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1600_, v_e_1594_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_);
return v___x_1638_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0___boxed(lean_object* v_n_1639_, lean_object* v_xs_1640_, lean_object* v_e_1641_, lean_object* v_offset_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_){
_start:
{
uint8_t v_a_boxed_1647_; lean_object* v_res_1648_; 
v_a_boxed_1647_ = lean_unbox(v_a_1644_);
v_res_1648_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0(v_n_1639_, v_xs_1640_, v_e_1641_, v_offset_1642_, v_a_1643_, v_a_boxed_1647_, v_a_1645_, v_a_1646_);
lean_dec_ref(v_a_1645_);
lean_dec_ref(v_xs_1640_);
lean_dec(v_n_1639_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___boxed(lean_object* v_n_1649_, lean_object* v_xs_1650_, lean_object* v_e_1651_, lean_object* v_offset_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_){
_start:
{
uint8_t v_a_boxed_1657_; lean_object* v_res_1658_; 
v_a_boxed_1657_ = lean_unbox(v_a_1654_);
v_res_1658_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0(v_n_1649_, v_xs_1650_, v_e_1651_, v_offset_1652_, v_a_1653_, v_a_boxed_1657_, v_a_1655_, v_a_1656_);
lean_dec_ref(v_a_1655_);
lean_dec_ref(v_xs_1650_);
lean_dec(v_n_1649_);
return v_res_1658_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1659_ = lean_box(0);
v___x_1660_ = lean_unsigned_to_nat(16u);
v___x_1661_ = lean_mk_array(v___x_1660_, v___x_1659_);
return v___x_1661_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1662_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__0, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__0_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__0);
v___x_1663_ = lean_unsigned_to_nat(0u);
v___x_1664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1663_);
lean_ctor_set(v___x_1664_, 1, v___x_1662_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0(lean_object* v_e_1665_, lean_object* v_size_1666_, lean_object* v___x_1667_, lean_object* v_xs_1668_, uint8_t v_debug_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = lean_unsigned_to_nat(0u);
switch(lean_obj_tag(v_e_1665_))
{
case 0:
{
lean_object* v_deBruijnIndex_1673_; uint8_t v___x_1674_; 
v_deBruijnIndex_1673_ = lean_ctor_get(v_e_1665_, 0);
v___x_1674_ = lean_nat_dec_le(v___x_1672_, v_deBruijnIndex_1673_);
if (v___x_1674_ == 0)
{
lean_object* v___x_1675_; 
v___x_1675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1675_, 0, v_e_1665_);
lean_ctor_set(v___x_1675_, 1, v___y_1671_);
return v___x_1675_;
}
else
{
lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; uint8_t v___x_1679_; 
lean_inc(v_deBruijnIndex_1673_);
lean_dec_ref_known(v_e_1665_, 1);
v___x_1676_ = lean_nat_sub(v_size_1666_, v_deBruijnIndex_1673_);
lean_dec(v_deBruijnIndex_1673_);
v___x_1677_ = lean_unsigned_to_nat(1u);
v___x_1678_ = lean_nat_sub(v___x_1676_, v___x_1677_);
lean_dec(v___x_1676_);
v___x_1679_ = lean_nat_dec_lt(v___x_1678_, v_size_1666_);
if (v___x_1679_ == 0)
{
lean_object* v___x_1680_; lean_object* v___x_1681_; 
lean_dec(v___x_1678_);
v___x_1680_ = l_outOfBounds___redArg(v___x_1667_);
v___x_1681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1680_);
lean_ctor_set(v___x_1681_, 1, v___y_1671_);
return v___x_1681_;
}
else
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1682_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1667_, v_xs_1668_, v___x_1678_);
lean_dec(v___x_1678_);
v___x_1683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1682_);
lean_ctor_set(v___x_1683_, 1, v___y_1671_);
return v___x_1683_;
}
}
}
case 9:
{
lean_object* v___x_1684_; 
v___x_1684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1684_, 0, v_e_1665_);
lean_ctor_set(v___x_1684_, 1, v___y_1671_);
return v___x_1684_;
}
case 2:
{
lean_object* v___x_1685_; 
v___x_1685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1685_, 0, v_e_1665_);
lean_ctor_set(v___x_1685_, 1, v___y_1671_);
return v___x_1685_;
}
case 1:
{
lean_object* v___x_1686_; 
v___x_1686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1686_, 0, v_e_1665_);
lean_ctor_set(v___x_1686_, 1, v___y_1671_);
return v___x_1686_;
}
case 4:
{
lean_object* v___x_1687_; 
v___x_1687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1687_, 0, v_e_1665_);
lean_ctor_set(v___x_1687_, 1, v___y_1671_);
return v___x_1687_;
}
case 3:
{
lean_object* v___x_1688_; 
v___x_1688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1688_, 0, v_e_1665_);
lean_ctor_set(v___x_1688_, 1, v___y_1671_);
return v___x_1688_;
}
default: 
{
lean_object* v___x_1689_; uint8_t v___x_1690_; 
v___x_1689_ = l_Lean_Expr_looseBVarRange(v_e_1665_);
v___x_1690_ = lean_nat_dec_le(v___x_1689_, v___x_1672_);
lean_dec(v___x_1689_);
if (v___x_1690_ == 0)
{
switch(lean_obj_tag(v_e_1665_))
{
case 9:
{
lean_object* v___x_1691_; 
v___x_1691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1691_, 0, v_e_1665_);
lean_ctor_set(v___x_1691_, 1, v___y_1671_);
return v___x_1691_;
}
case 2:
{
lean_object* v___x_1692_; 
v___x_1692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1692_, 0, v_e_1665_);
lean_ctor_set(v___x_1692_, 1, v___y_1671_);
return v___x_1692_;
}
case 0:
{
lean_object* v___x_1693_; 
v___x_1693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1693_, 0, v_e_1665_);
lean_ctor_set(v___x_1693_, 1, v___y_1671_);
return v___x_1693_;
}
case 1:
{
lean_object* v___x_1694_; 
v___x_1694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1694_, 0, v_e_1665_);
lean_ctor_set(v___x_1694_, 1, v___y_1671_);
return v___x_1694_;
}
case 4:
{
lean_object* v___x_1695_; 
v___x_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1695_, 0, v_e_1665_);
lean_ctor_set(v___x_1695_, 1, v___y_1671_);
return v___x_1695_;
}
case 3:
{
lean_object* v___x_1696_; 
v___x_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1696_, 0, v_e_1665_);
lean_ctor_set(v___x_1696_, 1, v___y_1671_);
return v___x_1696_;
}
default: 
{
lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1697_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__1, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__1);
v___x_1698_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0(v_size_1666_, v_xs_1668_, v_e_1665_, v___x_1672_, v___x_1697_, v_debug_1669_, v___y_1670_, v___y_1671_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_a_1699_; lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1708_; 
v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
v_a_1700_ = lean_ctor_get(v___x_1698_, 1);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1702_ = v___x_1698_;
v_isShared_1703_ = v_isSharedCheck_1708_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_inc(v_a_1699_);
lean_dec(v___x_1698_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1708_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v_fst_1704_; lean_object* v___x_1706_; 
v_fst_1704_ = lean_ctor_get(v_a_1699_, 0);
lean_inc(v_fst_1704_);
lean_dec(v_a_1699_);
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 0, v_fst_1704_);
v___x_1706_ = v___x_1702_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_fst_1704_);
lean_ctor_set(v_reuseFailAlloc_1707_, 1, v_a_1700_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
else
{
lean_object* v_a_1709_; lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1717_; 
v_a_1709_ = lean_ctor_get(v___x_1698_, 0);
v_a_1710_ = lean_ctor_get(v___x_1698_, 1);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1712_ = v___x_1698_;
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_inc(v_a_1709_);
lean_dec(v___x_1698_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1715_; 
if (v_isShared_1713_ == 0)
{
v___x_1715_ = v___x_1712_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_a_1709_);
lean_ctor_set(v_reuseFailAlloc_1716_, 1, v_a_1710_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
}
}
}
else
{
lean_object* v___x_1718_; 
v___x_1718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1718_, 0, v_e_1665_);
lean_ctor_set(v___x_1718_, 1, v___y_1671_);
return v___x_1718_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___boxed(lean_object* v_e_1719_, lean_object* v_size_1720_, lean_object* v___x_1721_, lean_object* v_xs_1722_, lean_object* v_debug_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
uint8_t v_debug_boxed_1726_; lean_object* v_res_1727_; 
v_debug_boxed_1726_ = lean_unbox(v_debug_1723_);
v_res_1727_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0(v_e_1719_, v_size_1720_, v___x_1721_, v_xs_1722_, v_debug_boxed_1726_, v___y_1724_, v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec_ref(v_xs_1722_);
lean_dec_ref(v___x_1721_);
lean_dec(v_size_1720_);
return v_res_1727_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2(void){
_start:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1730_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__2));
v___x_1731_ = lean_unsigned_to_nat(16u);
v___x_1732_ = lean_unsigned_to_nat(62u);
v___x_1733_ = ((lean_object*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__1));
v___x_1734_ = ((lean_object*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__0));
v___x_1735_ = l_mkPanicMessageWithDecl(v___x_1734_, v___x_1733_, v___x_1732_, v___x_1731_, v___x_1730_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg(lean_object* v_xs_1736_, lean_object* v_e_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_){
_start:
{
lean_object* v_size_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; uint8_t v_debug_1748_; lean_object* v___x_1749_; lean_object* v___f_1750_; lean_object* v___x_1751_; lean_object* v_env_1752_; uint8_t v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v_size_1745_ = lean_ctor_get(v_xs_1736_, 2);
lean_inc(v_size_1745_);
v___x_1746_ = l_Lean_instInhabitedExpr;
v___x_1747_ = lean_st_ref_get(v_a_1739_);
v_debug_1748_ = lean_ctor_get_uint8(v___x_1747_, sizeof(void*)*12);
lean_dec(v___x_1747_);
v___x_1749_ = lean_box(v_debug_1748_);
v___f_1750_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___boxed), 7, 5);
lean_closure_set(v___f_1750_, 0, v_e_1737_);
lean_closure_set(v___f_1750_, 1, v_size_1745_);
lean_closure_set(v___f_1750_, 2, v___x_1746_);
lean_closure_set(v___f_1750_, 3, v_xs_1736_);
lean_closure_set(v___f_1750_, 4, v___x_1749_);
v___x_1751_ = lean_st_ref_get(v_a_1743_);
v_env_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc_ref(v_env_1752_);
lean_dec(v___x_1751_);
v___x_1753_ = 0;
v___x_1754_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1754_, 0, v_env_1752_);
lean_ctor_set_uint8(v___x_1754_, sizeof(void*)*1, v___x_1753_);
lean_ctor_set_uint8(v___x_1754_, sizeof(void*)*1 + 1, v___x_1753_);
v___x_1755_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_1750_, v___x_1754_, v_a_1739_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1766_; 
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1758_ = v___x_1755_;
v_isShared_1759_ = v_isSharedCheck_1766_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1755_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1766_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
if (lean_obj_tag(v_a_1756_) == 0)
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
lean_dec_ref_known(v_a_1756_, 1);
lean_del_object(v___x_1758_);
v___x_1760_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2);
v___x_1761_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1(v___x_1760_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_);
return v___x_1761_;
}
else
{
lean_object* v_a_1762_; lean_object* v___x_1764_; 
v_a_1762_ = lean_ctor_get(v_a_1756_, 0);
lean_inc(v_a_1762_);
lean_dec_ref_known(v_a_1756_, 1);
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 0, v_a_1762_);
v___x_1764_ = v___x_1758_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_a_1762_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
}
else
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1774_; 
v_a_1767_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1769_ = v___x_1755_;
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1755_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1770_ == 0)
{
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_a_1767_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___boxed(lean_object* v_xs_1775_, lean_object* v_e_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg(v_xs_1775_, v_e_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_);
lean_dec(v_a_1782_);
lean_dec_ref(v_a_1781_);
lean_dec(v_a_1780_);
lean_dec_ref(v_a_1779_);
lean_dec(v_a_1778_);
lean_dec_ref(v_a_1777_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv(lean_object* v_xs_1785_, lean_object* v_e_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_){
_start:
{
lean_object* v___x_1795_; 
v___x_1795_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg(v_xs_1785_, v_e_1786_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___boxed(lean_object* v_xs_1796_, lean_object* v_e_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv(v_xs_1796_, v_e_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_);
lean_dec(v_a_1804_);
lean_dec_ref(v_a_1803_);
lean_dec(v_a_1802_);
lean_dec_ref(v_a_1801_);
lean_dec(v_a_1800_);
lean_dec_ref(v_a_1799_);
lean_dec(v_a_1798_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1807_, lean_object* v_m_1808_, lean_object* v_a_1809_){
_start:
{
lean_object* v___x_1810_; 
v___x_1810_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2___redArg(v_m_1808_, v_a_1809_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1811_, lean_object* v_m_1812_, lean_object* v_a_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2(v_00_u03b2_1811_, v_m_1812_, v_a_1813_);
lean_dec_ref(v_a_1813_);
lean_dec_ref(v_m_1812_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10(lean_object* v_00_u03b2_1815_, lean_object* v_a_1816_, lean_object* v_x_1817_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10___redArg(v_a_1816_, v_x_1817_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10___boxed(lean_object* v_00_u03b2_1819_, lean_object* v_a_1820_, lean_object* v_x_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2_spec__10(v_00_u03b2_1819_, v_a_1820_, v_x_1821_);
lean_dec(v_x_1821_);
lean_dec_ref(v_a_1820_);
return v_res_1822_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = l_instMonadEIO___redArg();
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(lean_object* v_msg_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_){
_start:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v_toApplicative_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1903_; 
v___x_1837_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__0);
v___x_1838_ = l_StateRefT_x27_instMonad___redArg(v___x_1837_);
v_toApplicative_1839_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1903_ == 0)
{
lean_object* v_unused_1904_; 
v_unused_1904_ = lean_ctor_get(v___x_1838_, 1);
lean_dec(v_unused_1904_);
v___x_1841_ = v___x_1838_;
v_isShared_1842_ = v_isSharedCheck_1903_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_toApplicative_1839_);
lean_dec(v___x_1838_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1903_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v_toFunctor_1843_; lean_object* v_toSeq_1844_; lean_object* v_toSeqLeft_1845_; lean_object* v_toSeqRight_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1901_; 
v_toFunctor_1843_ = lean_ctor_get(v_toApplicative_1839_, 0);
v_toSeq_1844_ = lean_ctor_get(v_toApplicative_1839_, 2);
v_toSeqLeft_1845_ = lean_ctor_get(v_toApplicative_1839_, 3);
v_toSeqRight_1846_ = lean_ctor_get(v_toApplicative_1839_, 4);
v_isSharedCheck_1901_ = !lean_is_exclusive(v_toApplicative_1839_);
if (v_isSharedCheck_1901_ == 0)
{
lean_object* v_unused_1902_; 
v_unused_1902_ = lean_ctor_get(v_toApplicative_1839_, 1);
lean_dec(v_unused_1902_);
v___x_1848_ = v_toApplicative_1839_;
v_isShared_1849_ = v_isSharedCheck_1901_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_toSeqRight_1846_);
lean_inc(v_toSeqLeft_1845_);
lean_inc(v_toSeq_1844_);
lean_inc(v_toFunctor_1843_);
lean_dec(v_toApplicative_1839_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1901_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___f_1850_; lean_object* v___f_1851_; lean_object* v___f_1852_; lean_object* v___f_1853_; lean_object* v___x_1854_; lean_object* v___f_1855_; lean_object* v___f_1856_; lean_object* v___f_1857_; lean_object* v___x_1859_; 
v___f_1850_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__1));
v___f_1851_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1843_);
v___f_1852_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1852_, 0, v_toFunctor_1843_);
v___f_1853_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1853_, 0, v_toFunctor_1843_);
v___x_1854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___f_1852_);
lean_ctor_set(v___x_1854_, 1, v___f_1853_);
v___f_1855_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1855_, 0, v_toSeqRight_1846_);
v___f_1856_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1856_, 0, v_toSeqLeft_1845_);
v___f_1857_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1857_, 0, v_toSeq_1844_);
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 4, v___f_1855_);
lean_ctor_set(v___x_1848_, 3, v___f_1856_);
lean_ctor_set(v___x_1848_, 2, v___f_1857_);
lean_ctor_set(v___x_1848_, 1, v___f_1850_);
lean_ctor_set(v___x_1848_, 0, v___x_1854_);
v___x_1859_ = v___x_1848_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v___x_1854_);
lean_ctor_set(v_reuseFailAlloc_1900_, 1, v___f_1850_);
lean_ctor_set(v_reuseFailAlloc_1900_, 2, v___f_1857_);
lean_ctor_set(v_reuseFailAlloc_1900_, 3, v___f_1856_);
lean_ctor_set(v_reuseFailAlloc_1900_, 4, v___f_1855_);
v___x_1859_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
lean_object* v___x_1861_; 
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 1, v___f_1851_);
lean_ctor_set(v___x_1841_, 0, v___x_1859_);
v___x_1861_ = v___x_1841_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1859_);
lean_ctor_set(v_reuseFailAlloc_1899_, 1, v___f_1851_);
v___x_1861_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
lean_object* v___x_1862_; lean_object* v_toApplicative_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1897_; 
v___x_1862_ = l_StateRefT_x27_instMonad___redArg(v___x_1861_);
v_toApplicative_1863_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1897_ == 0)
{
lean_object* v_unused_1898_; 
v_unused_1898_ = lean_ctor_get(v___x_1862_, 1);
lean_dec(v_unused_1898_);
v___x_1865_ = v___x_1862_;
v_isShared_1866_ = v_isSharedCheck_1897_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_toApplicative_1863_);
lean_dec(v___x_1862_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1897_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v_toFunctor_1867_; lean_object* v_toSeq_1868_; lean_object* v_toSeqLeft_1869_; lean_object* v_toSeqRight_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1895_; 
v_toFunctor_1867_ = lean_ctor_get(v_toApplicative_1863_, 0);
v_toSeq_1868_ = lean_ctor_get(v_toApplicative_1863_, 2);
v_toSeqLeft_1869_ = lean_ctor_get(v_toApplicative_1863_, 3);
v_toSeqRight_1870_ = lean_ctor_get(v_toApplicative_1863_, 4);
v_isSharedCheck_1895_ = !lean_is_exclusive(v_toApplicative_1863_);
if (v_isSharedCheck_1895_ == 0)
{
lean_object* v_unused_1896_; 
v_unused_1896_ = lean_ctor_get(v_toApplicative_1863_, 1);
lean_dec(v_unused_1896_);
v___x_1872_ = v_toApplicative_1863_;
v_isShared_1873_ = v_isSharedCheck_1895_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_toSeqRight_1870_);
lean_inc(v_toSeqLeft_1869_);
lean_inc(v_toSeq_1868_);
lean_inc(v_toFunctor_1867_);
lean_dec(v_toApplicative_1863_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1895_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___f_1874_; lean_object* v___f_1875_; lean_object* v___f_1876_; lean_object* v___f_1877_; lean_object* v___x_1878_; lean_object* v___f_1879_; lean_object* v___f_1880_; lean_object* v___f_1881_; lean_object* v___x_1883_; 
v___f_1874_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__3));
v___f_1875_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1867_);
v___f_1876_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1876_, 0, v_toFunctor_1867_);
v___f_1877_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1877_, 0, v_toFunctor_1867_);
v___x_1878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1878_, 0, v___f_1876_);
lean_ctor_set(v___x_1878_, 1, v___f_1877_);
v___f_1879_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1879_, 0, v_toSeqRight_1870_);
v___f_1880_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1880_, 0, v_toSeqLeft_1869_);
v___f_1881_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1881_, 0, v_toSeq_1868_);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 4, v___f_1879_);
lean_ctor_set(v___x_1872_, 3, v___f_1880_);
lean_ctor_set(v___x_1872_, 2, v___f_1881_);
lean_ctor_set(v___x_1872_, 1, v___f_1874_);
lean_ctor_set(v___x_1872_, 0, v___x_1878_);
v___x_1883_ = v___x_1872_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1878_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v___f_1874_);
lean_ctor_set(v_reuseFailAlloc_1894_, 2, v___f_1881_);
lean_ctor_set(v_reuseFailAlloc_1894_, 3, v___f_1880_);
lean_ctor_set(v_reuseFailAlloc_1894_, 4, v___f_1879_);
v___x_1883_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
lean_object* v___x_1885_; 
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 1, v___f_1875_);
lean_ctor_set(v___x_1865_, 0, v___x_1883_);
v___x_1885_ = v___x_1865_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v___x_1883_);
lean_ctor_set(v_reuseFailAlloc_1893_, 1, v___f_1875_);
v___x_1885_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_14116__overap_1891_; lean_object* v___x_1892_; 
v___x_1886_ = l_StateRefT_x27_instMonad___redArg(v___x_1885_);
v___x_1887_ = l_ReaderT_instMonad___redArg(v___x_1886_);
v___x_1888_ = l_StateRefT_x27_instMonad___redArg(v___x_1887_);
v___x_1889_ = l_Lean_instInhabitedExpr;
v___x_1890_ = l_instInhabitedOfMonad___redArg(v___x_1888_, v___x_1889_);
v___x_14116__overap_1891_ = lean_panic_fn_borrowed(v___x_1890_, v_msg_1828_);
lean_dec(v___x_1890_);
lean_inc(v___y_1835_);
lean_inc_ref(v___y_1834_);
lean_inc(v___y_1833_);
lean_inc_ref(v___y_1832_);
lean_inc(v___y_1831_);
lean_inc_ref(v___y_1830_);
lean_inc(v___y_1829_);
v___x_1892_ = lean_apply_8(v___x_14116__overap_1891_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, lean_box(0));
return v___x_1892_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0___boxed(lean_object* v_msg_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(v_msg_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec(v___y_1906_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1___redArg(lean_object* v_f_1915_, lean_object* v_a_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v___y_1925_; lean_object* v___x_1928_; uint8_t v_debug_1929_; 
v___x_1928_ = lean_st_ref_get(v___y_1918_);
v_debug_1929_ = lean_ctor_get_uint8(v___x_1928_, sizeof(void*)*12);
lean_dec(v___x_1928_);
if (v_debug_1929_ == 0)
{
v___y_1925_ = v___y_1918_;
goto v___jp_1924_;
}
else
{
lean_object* v___x_1930_; 
v___x_1930_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_1915_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v___x_1931_; 
lean_dec_ref_known(v___x_1930_, 1);
v___x_1931_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_dec_ref_known(v___x_1931_, 1);
v___y_1925_ = v___y_1918_;
goto v___jp_1924_;
}
else
{
lean_object* v_a_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1939_; 
lean_dec_ref(v_a_1916_);
lean_dec_ref(v_f_1915_);
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1934_ = v___x_1931_;
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_a_1932_);
lean_dec(v___x_1931_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1937_; 
if (v_isShared_1935_ == 0)
{
v___x_1937_ = v___x_1934_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_a_1932_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
else
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1947_; 
lean_dec_ref(v_a_1916_);
lean_dec_ref(v_f_1915_);
v_a_1940_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1942_ = v___x_1930_;
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1930_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1945_; 
if (v_isShared_1943_ == 0)
{
v___x_1945_ = v___x_1942_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_a_1940_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
}
v___jp_1924_:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1926_ = l_Lean_Expr_app___override(v_f_1915_, v_a_1916_);
v___x_1927_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1926_, v___y_1925_);
return v___x_1927_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1___redArg___boxed(lean_object* v_f_1948_, lean_object* v_a_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_){
_start:
{
lean_object* v_res_1957_; 
v_res_1957_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1___redArg(v_f_1948_, v_a_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1(lean_object* v_f_1958_, lean_object* v_a_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
lean_object* v___x_1968_; 
v___x_1968_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1___redArg(v_f_1958_, v_a_1959_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1___boxed(lean_object* v_f_1969_, lean_object* v_a_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1(v_f_1969_, v_a_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v___y_1971_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2___redArg(lean_object* v_d_1980_, lean_object* v_e_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
lean_object* v___y_1990_; lean_object* v___x_1993_; uint8_t v_debug_1994_; 
v___x_1993_ = lean_st_ref_get(v___y_1983_);
v_debug_1994_ = lean_ctor_get_uint8(v___x_1993_, sizeof(void*)*12);
lean_dec(v___x_1993_);
if (v_debug_1994_ == 0)
{
v___y_1990_ = v___y_1983_;
goto v___jp_1989_;
}
else
{
lean_object* v___x_1995_; 
v___x_1995_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_e_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_dec_ref_known(v___x_1995_, 1);
v___y_1990_ = v___y_1983_;
goto v___jp_1989_;
}
else
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
lean_dec_ref(v_e_1981_);
lean_dec(v_d_1980_);
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1998_ = v___x_1995_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1995_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
v___jp_1989_:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1991_ = l_Lean_Expr_mdata___override(v_d_1980_, v_e_1981_);
v___x_1992_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1991_, v___y_1990_);
return v___x_1992_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2___redArg___boxed(lean_object* v_d_2004_, lean_object* v_e_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2___redArg(v_d_2004_, v_e_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2(lean_object* v_d_2014_, lean_object* v_e_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_){
_start:
{
lean_object* v___x_2024_; 
v___x_2024_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2___redArg(v_d_2014_, v_e_2015_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2___boxed(lean_object* v_d_2025_, lean_object* v_e_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2(v_d_2025_, v_e_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec(v___y_2027_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3___redArg(lean_object* v_structName_2036_, lean_object* v_idx_2037_, lean_object* v_struct_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v___y_2047_; lean_object* v___x_2050_; uint8_t v_debug_2051_; 
v___x_2050_ = lean_st_ref_get(v___y_2040_);
v_debug_2051_ = lean_ctor_get_uint8(v___x_2050_, sizeof(void*)*12);
lean_dec(v___x_2050_);
if (v_debug_2051_ == 0)
{
v___y_2047_ = v___y_2040_;
goto v___jp_2046_;
}
else
{
lean_object* v___x_2052_; 
v___x_2052_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_struct_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_dec_ref_known(v___x_2052_, 1);
v___y_2047_ = v___y_2040_;
goto v___jp_2046_;
}
else
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
lean_dec_ref(v_struct_2038_);
lean_dec(v_idx_2037_);
lean_dec(v_structName_2036_);
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2055_ = v___x_2052_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_2052_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2056_ == 0)
{
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2053_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
}
v___jp_2046_:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2048_ = l_Lean_Expr_proj___override(v_structName_2036_, v_idx_2037_, v_struct_2038_);
v___x_2049_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2048_, v___y_2047_);
return v___x_2049_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3___redArg___boxed(lean_object* v_structName_2061_, lean_object* v_idx_2062_, lean_object* v_struct_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3___redArg(v_structName_2061_, v_idx_2062_, v_struct_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3(lean_object* v_structName_2072_, lean_object* v_idx_2073_, lean_object* v_struct_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
lean_object* v___x_2083_; 
v___x_2083_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3___redArg(v_structName_2072_, v_idx_2073_, v_struct_2074_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
return v___x_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3___boxed(lean_object* v_structName_2084_, lean_object* v_idx_2085_, lean_object* v_struct_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_){
_start:
{
lean_object* v_res_2095_; 
v_res_2095_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3(v_structName_2084_, v_idx_2085_, v_struct_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
lean_dec(v___y_2087_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5_spec__5(lean_object* v_msgData_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
lean_object* v___x_2102_; lean_object* v_env_2103_; uint8_t v___x_2104_; lean_object* v_env_2105_; lean_object* v___x_2106_; lean_object* v_toCold_2107_; lean_object* v_mctx_2108_; lean_object* v_lctx_2109_; lean_object* v_options_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2102_ = lean_st_ref_get(v___y_2100_);
v_env_2103_ = lean_ctor_get(v___x_2102_, 0);
lean_inc_ref(v_env_2103_);
lean_dec(v___x_2102_);
v___x_2104_ = 0;
v_env_2105_ = l_Lean_Environment_setRecordingDeps(v_env_2103_, v___x_2104_);
v___x_2106_ = lean_st_ref_get(v___y_2098_);
v_toCold_2107_ = lean_ctor_get(v___y_2099_, 0);
v_mctx_2108_ = lean_ctor_get(v___x_2106_, 0);
lean_inc_ref(v_mctx_2108_);
lean_dec(v___x_2106_);
v_lctx_2109_ = lean_ctor_get(v___y_2097_, 2);
v_options_2110_ = lean_ctor_get(v_toCold_2107_, 2);
lean_inc_ref(v_options_2110_);
lean_inc_ref(v_lctx_2109_);
v___x_2111_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2111_, 0, v_env_2105_);
lean_ctor_set(v___x_2111_, 1, v_mctx_2108_);
lean_ctor_set(v___x_2111_, 2, v_lctx_2109_);
lean_ctor_set(v___x_2111_, 3, v_options_2110_);
v___x_2112_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2111_);
lean_ctor_set(v___x_2112_, 1, v_msgData_2096_);
v___x_2113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2112_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5_spec__5___boxed(lean_object* v_msgData_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_){
_start:
{
lean_object* v_res_2120_; 
v_res_2120_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5_spec__5(v_msgData_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5___redArg(lean_object* v_msg_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_){
_start:
{
lean_object* v_ref_2127_; lean_object* v___x_2128_; lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2137_; 
v_ref_2127_ = lean_ctor_get(v___y_2124_, 2);
v___x_2128_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5_spec__5(v_msg_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2131_ = v___x_2128_;
v_isShared_2132_ = v_isSharedCheck_2137_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2128_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2137_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2133_; lean_object* v___x_2135_; 
lean_inc(v_ref_2127_);
v___x_2133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2133_, 0, v_ref_2127_);
lean_ctor_set(v___x_2133_, 1, v_a_2129_);
if (v_isShared_2132_ == 0)
{
lean_ctor_set_tag(v___x_2131_, 1);
lean_ctor_set(v___x_2131_, 0, v___x_2133_);
v___x_2135_ = v___x_2131_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v___x_2133_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5___redArg___boxed(lean_object* v_msg_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5___redArg(v_msg_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_);
lean_dec(v___y_2142_);
lean_dec_ref(v___y_2141_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7___redArg(lean_object* v_a_2145_, lean_object* v_x_2146_){
_start:
{
if (lean_obj_tag(v_x_2146_) == 0)
{
lean_object* v___x_2147_; 
v___x_2147_ = lean_box(0);
return v___x_2147_;
}
else
{
lean_object* v_key_2148_; lean_object* v_value_2149_; lean_object* v_tail_2150_; lean_object* v_fst_2151_; lean_object* v_snd_2152_; lean_object* v_fst_2153_; lean_object* v_snd_2154_; size_t v___x_2155_; size_t v___x_2156_; uint8_t v___x_2157_; 
v_key_2148_ = lean_ctor_get(v_x_2146_, 0);
v_value_2149_ = lean_ctor_get(v_x_2146_, 1);
v_tail_2150_ = lean_ctor_get(v_x_2146_, 2);
v_fst_2151_ = lean_ctor_get(v_key_2148_, 0);
v_snd_2152_ = lean_ctor_get(v_key_2148_, 1);
v_fst_2153_ = lean_ctor_get(v_a_2145_, 0);
v_snd_2154_ = lean_ctor_get(v_a_2145_, 1);
v___x_2155_ = lean_ptr_addr(v_fst_2151_);
v___x_2156_ = lean_ptr_addr(v_fst_2153_);
v___x_2157_ = lean_usize_dec_eq(v___x_2155_, v___x_2156_);
if (v___x_2157_ == 0)
{
v_x_2146_ = v_tail_2150_;
goto _start;
}
else
{
size_t v___x_2159_; size_t v___x_2160_; uint8_t v___x_2161_; 
v___x_2159_ = lean_ptr_addr(v_snd_2152_);
v___x_2160_ = lean_ptr_addr(v_snd_2154_);
v___x_2161_ = lean_usize_dec_eq(v___x_2159_, v___x_2160_);
if (v___x_2161_ == 0)
{
v_x_2146_ = v_tail_2150_;
goto _start;
}
else
{
lean_object* v___x_2163_; 
lean_inc(v_value_2149_);
v___x_2163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2163_, 0, v_value_2149_);
return v___x_2163_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7___redArg___boxed(lean_object* v_a_2164_, lean_object* v_x_2165_){
_start:
{
lean_object* v_res_2166_; 
v_res_2166_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7___redArg(v_a_2164_, v_x_2165_);
lean_dec(v_x_2165_);
lean_dec_ref(v_a_2164_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6___redArg(lean_object* v_m_2167_, lean_object* v_a_2168_){
_start:
{
lean_object* v_buckets_2169_; lean_object* v_fst_2170_; lean_object* v_snd_2171_; lean_object* v___x_2172_; size_t v___x_2173_; size_t v___x_2174_; size_t v___x_2175_; uint64_t v___x_2176_; size_t v___x_2177_; size_t v___x_2178_; uint64_t v___x_2179_; uint64_t v___x_2180_; uint64_t v___x_2181_; uint64_t v___x_2182_; uint64_t v_fold_2183_; uint64_t v___x_2184_; uint64_t v___x_2185_; uint64_t v___x_2186_; size_t v___x_2187_; size_t v___x_2188_; size_t v___x_2189_; size_t v___x_2190_; size_t v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
v_buckets_2169_ = lean_ctor_get(v_m_2167_, 1);
v_fst_2170_ = lean_ctor_get(v_a_2168_, 0);
v_snd_2171_ = lean_ctor_get(v_a_2168_, 1);
v___x_2172_ = lean_array_get_size(v_buckets_2169_);
v___x_2173_ = lean_ptr_addr(v_fst_2170_);
v___x_2174_ = ((size_t)3ULL);
v___x_2175_ = lean_usize_shift_right(v___x_2173_, v___x_2174_);
v___x_2176_ = lean_usize_to_uint64(v___x_2175_);
v___x_2177_ = lean_ptr_addr(v_snd_2171_);
v___x_2178_ = lean_usize_shift_right(v___x_2177_, v___x_2174_);
v___x_2179_ = lean_usize_to_uint64(v___x_2178_);
v___x_2180_ = lean_uint64_mix_hash(v___x_2176_, v___x_2179_);
v___x_2181_ = 32ULL;
v___x_2182_ = lean_uint64_shift_right(v___x_2180_, v___x_2181_);
v_fold_2183_ = lean_uint64_xor(v___x_2180_, v___x_2182_);
v___x_2184_ = 16ULL;
v___x_2185_ = lean_uint64_shift_right(v_fold_2183_, v___x_2184_);
v___x_2186_ = lean_uint64_xor(v_fold_2183_, v___x_2185_);
v___x_2187_ = lean_uint64_to_usize(v___x_2186_);
v___x_2188_ = lean_usize_of_nat(v___x_2172_);
v___x_2189_ = ((size_t)1ULL);
v___x_2190_ = lean_usize_sub(v___x_2188_, v___x_2189_);
v___x_2191_ = lean_usize_land(v___x_2187_, v___x_2190_);
v___x_2192_ = lean_array_uget_borrowed(v_buckets_2169_, v___x_2191_);
v___x_2193_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7___redArg(v_a_2168_, v___x_2192_);
return v___x_2193_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6___redArg___boxed(lean_object* v_m_2194_, lean_object* v_a_2195_){
_start:
{
lean_object* v_res_2196_; 
v_res_2196_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6___redArg(v_m_2194_, v_a_2195_);
lean_dec_ref(v_a_2195_);
lean_dec_ref(v_m_2194_);
return v_res_2196_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9___redArg(lean_object* v_a_2197_, lean_object* v_x_2198_){
_start:
{
if (lean_obj_tag(v_x_2198_) == 0)
{
uint8_t v___x_2199_; 
v___x_2199_ = 0;
return v___x_2199_;
}
else
{
lean_object* v_key_2200_; lean_object* v_tail_2201_; lean_object* v_fst_2202_; lean_object* v_snd_2203_; lean_object* v_fst_2204_; lean_object* v_snd_2205_; size_t v___x_2206_; size_t v___x_2207_; uint8_t v___x_2208_; 
v_key_2200_ = lean_ctor_get(v_x_2198_, 0);
v_tail_2201_ = lean_ctor_get(v_x_2198_, 2);
v_fst_2202_ = lean_ctor_get(v_key_2200_, 0);
v_snd_2203_ = lean_ctor_get(v_key_2200_, 1);
v_fst_2204_ = lean_ctor_get(v_a_2197_, 0);
v_snd_2205_ = lean_ctor_get(v_a_2197_, 1);
v___x_2206_ = lean_ptr_addr(v_fst_2202_);
v___x_2207_ = lean_ptr_addr(v_fst_2204_);
v___x_2208_ = lean_usize_dec_eq(v___x_2206_, v___x_2207_);
if (v___x_2208_ == 0)
{
v_x_2198_ = v_tail_2201_;
goto _start;
}
else
{
size_t v___x_2210_; size_t v___x_2211_; uint8_t v___x_2212_; 
v___x_2210_ = lean_ptr_addr(v_snd_2203_);
v___x_2211_ = lean_ptr_addr(v_snd_2205_);
v___x_2212_ = lean_usize_dec_eq(v___x_2210_, v___x_2211_);
if (v___x_2212_ == 0)
{
v_x_2198_ = v_tail_2201_;
goto _start;
}
else
{
return v___x_2212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9___redArg___boxed(lean_object* v_a_2214_, lean_object* v_x_2215_){
_start:
{
uint8_t v_res_2216_; lean_object* v_r_2217_; 
v_res_2216_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9___redArg(v_a_2214_, v_x_2215_);
lean_dec(v_x_2215_);
lean_dec_ref(v_a_2214_);
v_r_2217_ = lean_box(v_res_2216_);
return v_r_2217_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__11___redArg(lean_object* v_a_2218_, lean_object* v_b_2219_, lean_object* v_x_2220_){
_start:
{
if (lean_obj_tag(v_x_2220_) == 0)
{
lean_dec(v_b_2219_);
lean_dec_ref(v_a_2218_);
return v_x_2220_;
}
else
{
lean_object* v_key_2221_; lean_object* v_value_2222_; lean_object* v_tail_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2243_; 
v_key_2221_ = lean_ctor_get(v_x_2220_, 0);
v_value_2222_ = lean_ctor_get(v_x_2220_, 1);
v_tail_2223_ = lean_ctor_get(v_x_2220_, 2);
v_isSharedCheck_2243_ = !lean_is_exclusive(v_x_2220_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2225_ = v_x_2220_;
v_isShared_2226_ = v_isSharedCheck_2243_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_tail_2223_);
lean_inc(v_value_2222_);
lean_inc(v_key_2221_);
lean_dec(v_x_2220_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2243_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v_fst_2232_; lean_object* v_snd_2233_; lean_object* v_fst_2234_; lean_object* v_snd_2235_; size_t v___x_2236_; size_t v___x_2237_; uint8_t v___x_2238_; 
v_fst_2232_ = lean_ctor_get(v_key_2221_, 0);
v_snd_2233_ = lean_ctor_get(v_key_2221_, 1);
v_fst_2234_ = lean_ctor_get(v_a_2218_, 0);
v_snd_2235_ = lean_ctor_get(v_a_2218_, 1);
v___x_2236_ = lean_ptr_addr(v_fst_2232_);
v___x_2237_ = lean_ptr_addr(v_fst_2234_);
v___x_2238_ = lean_usize_dec_eq(v___x_2236_, v___x_2237_);
if (v___x_2238_ == 0)
{
goto v___jp_2227_;
}
else
{
size_t v___x_2239_; size_t v___x_2240_; uint8_t v___x_2241_; 
v___x_2239_ = lean_ptr_addr(v_snd_2233_);
v___x_2240_ = lean_ptr_addr(v_snd_2235_);
v___x_2241_ = lean_usize_dec_eq(v___x_2239_, v___x_2240_);
if (v___x_2241_ == 0)
{
goto v___jp_2227_;
}
else
{
lean_object* v___x_2242_; 
lean_del_object(v___x_2225_);
lean_dec(v_value_2222_);
lean_dec(v_key_2221_);
v___x_2242_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2242_, 0, v_a_2218_);
lean_ctor_set(v___x_2242_, 1, v_b_2219_);
lean_ctor_set(v___x_2242_, 2, v_tail_2223_);
return v___x_2242_;
}
}
v___jp_2227_:
{
lean_object* v___x_2228_; lean_object* v___x_2230_; 
v___x_2228_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__11___redArg(v_a_2218_, v_b_2219_, v_tail_2223_);
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 2, v___x_2228_);
v___x_2230_ = v___x_2225_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_key_2221_);
lean_ctor_set(v_reuseFailAlloc_2231_, 1, v_value_2222_);
lean_ctor_set(v_reuseFailAlloc_2231_, 2, v___x_2228_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10_spec__11_spec__12___redArg(lean_object* v_x_2244_, lean_object* v_x_2245_){
_start:
{
if (lean_obj_tag(v_x_2245_) == 0)
{
return v_x_2244_;
}
else
{
lean_object* v_key_2246_; lean_object* v_value_2247_; lean_object* v_tail_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2280_; 
v_key_2246_ = lean_ctor_get(v_x_2245_, 0);
v_value_2247_ = lean_ctor_get(v_x_2245_, 1);
v_tail_2248_ = lean_ctor_get(v_x_2245_, 2);
v_isSharedCheck_2280_ = !lean_is_exclusive(v_x_2245_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2250_ = v_x_2245_;
v_isShared_2251_ = v_isSharedCheck_2280_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_tail_2248_);
lean_inc(v_value_2247_);
lean_inc(v_key_2246_);
lean_dec(v_x_2245_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2280_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v_fst_2252_; lean_object* v_snd_2253_; lean_object* v___x_2254_; size_t v___x_2255_; size_t v___x_2256_; size_t v___x_2257_; uint64_t v___x_2258_; size_t v___x_2259_; size_t v___x_2260_; uint64_t v___x_2261_; uint64_t v___x_2262_; uint64_t v___x_2263_; uint64_t v___x_2264_; uint64_t v_fold_2265_; uint64_t v___x_2266_; uint64_t v___x_2267_; uint64_t v___x_2268_; size_t v___x_2269_; size_t v___x_2270_; size_t v___x_2271_; size_t v___x_2272_; size_t v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2276_; 
v_fst_2252_ = lean_ctor_get(v_key_2246_, 0);
v_snd_2253_ = lean_ctor_get(v_key_2246_, 1);
v___x_2254_ = lean_array_get_size(v_x_2244_);
v___x_2255_ = lean_ptr_addr(v_fst_2252_);
v___x_2256_ = ((size_t)3ULL);
v___x_2257_ = lean_usize_shift_right(v___x_2255_, v___x_2256_);
v___x_2258_ = lean_usize_to_uint64(v___x_2257_);
v___x_2259_ = lean_ptr_addr(v_snd_2253_);
v___x_2260_ = lean_usize_shift_right(v___x_2259_, v___x_2256_);
v___x_2261_ = lean_usize_to_uint64(v___x_2260_);
v___x_2262_ = lean_uint64_mix_hash(v___x_2258_, v___x_2261_);
v___x_2263_ = 32ULL;
v___x_2264_ = lean_uint64_shift_right(v___x_2262_, v___x_2263_);
v_fold_2265_ = lean_uint64_xor(v___x_2262_, v___x_2264_);
v___x_2266_ = 16ULL;
v___x_2267_ = lean_uint64_shift_right(v_fold_2265_, v___x_2266_);
v___x_2268_ = lean_uint64_xor(v_fold_2265_, v___x_2267_);
v___x_2269_ = lean_uint64_to_usize(v___x_2268_);
v___x_2270_ = lean_usize_of_nat(v___x_2254_);
v___x_2271_ = ((size_t)1ULL);
v___x_2272_ = lean_usize_sub(v___x_2270_, v___x_2271_);
v___x_2273_ = lean_usize_land(v___x_2269_, v___x_2272_);
v___x_2274_ = lean_array_uget_borrowed(v_x_2244_, v___x_2273_);
lean_inc(v___x_2274_);
if (v_isShared_2251_ == 0)
{
lean_ctor_set(v___x_2250_, 2, v___x_2274_);
v___x_2276_ = v___x_2250_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_key_2246_);
lean_ctor_set(v_reuseFailAlloc_2279_, 1, v_value_2247_);
lean_ctor_set(v_reuseFailAlloc_2279_, 2, v___x_2274_);
v___x_2276_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
lean_object* v___x_2277_; 
v___x_2277_ = lean_array_uset(v_x_2244_, v___x_2273_, v___x_2276_);
v_x_2244_ = v___x_2277_;
v_x_2245_ = v_tail_2248_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10_spec__11___redArg(lean_object* v_i_2281_, lean_object* v_source_2282_, lean_object* v_target_2283_){
_start:
{
lean_object* v___x_2284_; uint8_t v___x_2285_; 
v___x_2284_ = lean_array_get_size(v_source_2282_);
v___x_2285_ = lean_nat_dec_lt(v_i_2281_, v___x_2284_);
if (v___x_2285_ == 0)
{
lean_dec_ref(v_source_2282_);
lean_dec(v_i_2281_);
return v_target_2283_;
}
else
{
lean_object* v_es_2286_; lean_object* v___x_2287_; lean_object* v_source_2288_; lean_object* v_target_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v_es_2286_ = lean_array_fget(v_source_2282_, v_i_2281_);
v___x_2287_ = lean_box(0);
v_source_2288_ = lean_array_fset(v_source_2282_, v_i_2281_, v___x_2287_);
v_target_2289_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10_spec__11_spec__12___redArg(v_target_2283_, v_es_2286_);
v___x_2290_ = lean_unsigned_to_nat(1u);
v___x_2291_ = lean_nat_add(v_i_2281_, v___x_2290_);
lean_dec(v_i_2281_);
v_i_2281_ = v___x_2291_;
v_source_2282_ = v_source_2288_;
v_target_2283_ = v_target_2289_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10___redArg(lean_object* v_data_2293_){
_start:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v_nbuckets_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2294_ = lean_array_get_size(v_data_2293_);
v___x_2295_ = lean_unsigned_to_nat(2u);
v_nbuckets_2296_ = lean_nat_mul(v___x_2294_, v___x_2295_);
v___x_2297_ = lean_unsigned_to_nat(0u);
v___x_2298_ = lean_box(0);
v___x_2299_ = lean_mk_array(v_nbuckets_2296_, v___x_2298_);
v___x_2300_ = lean_array_propagate_mark(v_data_2293_, v___x_2299_);
v___x_2301_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10_spec__11___redArg(v___x_2297_, v_data_2293_, v___x_2300_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7___redArg(lean_object* v_m_2302_, lean_object* v_a_2303_, lean_object* v_b_2304_){
_start:
{
lean_object* v_size_2305_; lean_object* v_buckets_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2358_; 
v_size_2305_ = lean_ctor_get(v_m_2302_, 0);
v_buckets_2306_ = lean_ctor_get(v_m_2302_, 1);
v_isSharedCheck_2358_ = !lean_is_exclusive(v_m_2302_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2308_ = v_m_2302_;
v_isShared_2309_ = v_isSharedCheck_2358_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_buckets_2306_);
lean_inc(v_size_2305_);
lean_dec(v_m_2302_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2358_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v_fst_2310_; lean_object* v_snd_2311_; lean_object* v___x_2312_; size_t v___x_2313_; size_t v___x_2314_; size_t v___x_2315_; uint64_t v___x_2316_; size_t v___x_2317_; size_t v___x_2318_; uint64_t v___x_2319_; uint64_t v___x_2320_; uint64_t v___x_2321_; uint64_t v___x_2322_; uint64_t v_fold_2323_; uint64_t v___x_2324_; uint64_t v___x_2325_; uint64_t v___x_2326_; size_t v___x_2327_; size_t v___x_2328_; size_t v___x_2329_; size_t v___x_2330_; size_t v___x_2331_; lean_object* v_bkt_2332_; uint8_t v___x_2333_; 
v_fst_2310_ = lean_ctor_get(v_a_2303_, 0);
v_snd_2311_ = lean_ctor_get(v_a_2303_, 1);
v___x_2312_ = lean_array_get_size(v_buckets_2306_);
v___x_2313_ = lean_ptr_addr(v_fst_2310_);
v___x_2314_ = ((size_t)3ULL);
v___x_2315_ = lean_usize_shift_right(v___x_2313_, v___x_2314_);
v___x_2316_ = lean_usize_to_uint64(v___x_2315_);
v___x_2317_ = lean_ptr_addr(v_snd_2311_);
v___x_2318_ = lean_usize_shift_right(v___x_2317_, v___x_2314_);
v___x_2319_ = lean_usize_to_uint64(v___x_2318_);
v___x_2320_ = lean_uint64_mix_hash(v___x_2316_, v___x_2319_);
v___x_2321_ = 32ULL;
v___x_2322_ = lean_uint64_shift_right(v___x_2320_, v___x_2321_);
v_fold_2323_ = lean_uint64_xor(v___x_2320_, v___x_2322_);
v___x_2324_ = 16ULL;
v___x_2325_ = lean_uint64_shift_right(v_fold_2323_, v___x_2324_);
v___x_2326_ = lean_uint64_xor(v_fold_2323_, v___x_2325_);
v___x_2327_ = lean_uint64_to_usize(v___x_2326_);
v___x_2328_ = lean_usize_of_nat(v___x_2312_);
v___x_2329_ = ((size_t)1ULL);
v___x_2330_ = lean_usize_sub(v___x_2328_, v___x_2329_);
v___x_2331_ = lean_usize_land(v___x_2327_, v___x_2330_);
v_bkt_2332_ = lean_array_uget_borrowed(v_buckets_2306_, v___x_2331_);
v___x_2333_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9___redArg(v_a_2303_, v_bkt_2332_);
if (v___x_2333_ == 0)
{
lean_object* v___x_2334_; lean_object* v_size_x27_2335_; lean_object* v___x_2336_; lean_object* v_buckets_x27_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; uint8_t v___x_2343_; 
v___x_2334_ = lean_unsigned_to_nat(1u);
v_size_x27_2335_ = lean_nat_add(v_size_2305_, v___x_2334_);
lean_dec(v_size_2305_);
lean_inc(v_bkt_2332_);
v___x_2336_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2336_, 0, v_a_2303_);
lean_ctor_set(v___x_2336_, 1, v_b_2304_);
lean_ctor_set(v___x_2336_, 2, v_bkt_2332_);
v_buckets_x27_2337_ = lean_array_uset(v_buckets_2306_, v___x_2331_, v___x_2336_);
v___x_2338_ = lean_unsigned_to_nat(4u);
v___x_2339_ = lean_nat_mul(v_size_x27_2335_, v___x_2338_);
v___x_2340_ = lean_unsigned_to_nat(3u);
v___x_2341_ = lean_nat_div(v___x_2339_, v___x_2340_);
lean_dec(v___x_2339_);
v___x_2342_ = lean_array_get_size(v_buckets_x27_2337_);
v___x_2343_ = lean_nat_dec_le(v___x_2341_, v___x_2342_);
lean_dec(v___x_2341_);
if (v___x_2343_ == 0)
{
lean_object* v_val_2344_; lean_object* v___x_2346_; 
v_val_2344_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10___redArg(v_buckets_x27_2337_);
if (v_isShared_2309_ == 0)
{
lean_ctor_set(v___x_2308_, 1, v_val_2344_);
lean_ctor_set(v___x_2308_, 0, v_size_x27_2335_);
v___x_2346_ = v___x_2308_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_size_x27_2335_);
lean_ctor_set(v_reuseFailAlloc_2347_, 1, v_val_2344_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
else
{
lean_object* v___x_2349_; 
if (v_isShared_2309_ == 0)
{
lean_ctor_set(v___x_2308_, 1, v_buckets_x27_2337_);
lean_ctor_set(v___x_2308_, 0, v_size_x27_2335_);
v___x_2349_ = v___x_2308_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_size_x27_2335_);
lean_ctor_set(v_reuseFailAlloc_2350_, 1, v_buckets_x27_2337_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
else
{
lean_object* v___x_2351_; lean_object* v_buckets_x27_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2356_; 
lean_inc(v_bkt_2332_);
v___x_2351_ = lean_box(0);
v_buckets_x27_2352_ = lean_array_uset(v_buckets_2306_, v___x_2331_, v___x_2351_);
v___x_2353_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__11___redArg(v_a_2303_, v_b_2304_, v_bkt_2332_);
v___x_2354_ = lean_array_uset(v_buckets_x27_2352_, v___x_2331_, v___x_2353_);
if (v_isShared_2309_ == 0)
{
lean_ctor_set(v___x_2308_, 1, v___x_2354_);
v___x_2356_ = v___x_2308_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_size_2305_);
lean_ctor_set(v_reuseFailAlloc_2357_, 1, v___x_2354_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__1(void){
_start:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2360_ = ((lean_object*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__0));
v___x_2361_ = l_Lean_stringToMessageData(v___x_2360_);
return v___x_2361_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__2(void){
_start:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; 
v___x_2362_ = lean_unsigned_to_nat(32u);
v___x_2363_ = lean_mk_empty_array_with_capacity(v___x_2362_);
v___x_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2363_);
return v___x_2364_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__3(void){
_start:
{
size_t v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2365_ = ((size_t)5ULL);
v___x_2366_ = lean_unsigned_to_nat(0u);
v___x_2367_ = lean_unsigned_to_nat(32u);
v___x_2368_ = lean_mk_empty_array_with_capacity(v___x_2367_);
v___x_2369_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__2);
v___x_2370_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2370_, 0, v___x_2369_);
lean_ctor_set(v___x_2370_, 1, v___x_2368_);
lean_ctor_set(v___x_2370_, 2, v___x_2366_);
lean_ctor_set(v___x_2370_, 3, v___x_2366_);
lean_ctor_set_usize(v___x_2370_, 4, v___x_2365_);
return v___x_2370_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2(void){
_start:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2373_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__2));
v___x_2374_ = lean_unsigned_to_nat(73u);
v___x_2375_ = lean_unsigned_to_nat(213u);
v___x_2376_ = ((lean_object*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__1));
v___x_2377_ = ((lean_object*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__0));
v___x_2378_ = l_mkPanicMessageWithDecl(v___x_2377_, v___x_2376_, v___x_2375_, v___x_2374_, v___x_2373_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit(lean_object* v_xs_2379_, lean_object* v_e_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_){
_start:
{
switch(lean_obj_tag(v_e_2380_))
{
case 0:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; 
lean_dec_ref_known(v_e_2380_, 1);
lean_dec_ref(v_xs_2379_);
v___x_2389_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2);
v___x_2390_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(v___x_2389_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
return v___x_2390_;
}
case 1:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; 
lean_dec_ref_known(v_e_2380_, 1);
lean_dec_ref(v_xs_2379_);
v___x_2391_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2);
v___x_2392_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(v___x_2391_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
return v___x_2392_;
}
case 2:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; 
lean_dec_ref_known(v_e_2380_, 1);
lean_dec_ref(v_xs_2379_);
v___x_2393_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2);
v___x_2394_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(v___x_2393_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
return v___x_2394_;
}
case 3:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; 
lean_dec_ref_known(v_e_2380_, 1);
lean_dec_ref(v_xs_2379_);
v___x_2395_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2);
v___x_2396_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(v___x_2395_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
return v___x_2396_;
}
case 4:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; 
lean_dec_ref_known(v_e_2380_, 2);
lean_dec_ref(v_xs_2379_);
v___x_2397_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2);
v___x_2398_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(v___x_2397_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
return v___x_2398_;
}
case 5:
{
lean_object* v_fn_2399_; lean_object* v_arg_2400_; lean_object* v___x_2401_; 
v_fn_2399_ = lean_ctor_get(v_e_2380_, 0);
v_arg_2400_ = lean_ctor_get(v_e_2380_, 1);
lean_inc_ref(v_fn_2399_);
lean_inc_ref(v_xs_2379_);
v___x_2401_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v_xs_2379_, v_fn_2399_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_object* v_a_2402_; lean_object* v___x_2403_; 
v_a_2402_ = lean_ctor_get(v___x_2401_, 0);
lean_inc(v_a_2402_);
lean_dec_ref_known(v___x_2401_, 1);
lean_inc_ref(v_arg_2400_);
v___x_2403_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v_xs_2379_, v_arg_2400_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
if (lean_obj_tag(v___x_2403_) == 0)
{
lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2419_; 
v_a_2404_ = lean_ctor_get(v___x_2403_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2406_ = v___x_2403_;
v_isShared_2407_ = v_isSharedCheck_2419_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_dec(v___x_2403_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2419_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
size_t v___x_2408_; size_t v___x_2409_; uint8_t v___x_2410_; 
v___x_2408_ = lean_ptr_addr(v_fn_2399_);
v___x_2409_ = lean_ptr_addr(v_a_2402_);
v___x_2410_ = lean_usize_dec_eq(v___x_2408_, v___x_2409_);
if (v___x_2410_ == 0)
{
lean_object* v___x_2411_; 
lean_del_object(v___x_2406_);
lean_dec_ref_known(v_e_2380_, 2);
v___x_2411_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1___redArg(v_a_2402_, v_a_2404_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
return v___x_2411_;
}
else
{
size_t v___x_2412_; size_t v___x_2413_; uint8_t v___x_2414_; 
v___x_2412_ = lean_ptr_addr(v_arg_2400_);
v___x_2413_ = lean_ptr_addr(v_a_2404_);
v___x_2414_ = lean_usize_dec_eq(v___x_2412_, v___x_2413_);
if (v___x_2414_ == 0)
{
lean_object* v___x_2415_; 
lean_del_object(v___x_2406_);
lean_dec_ref_known(v_e_2380_, 2);
v___x_2415_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__1___redArg(v_a_2402_, v_a_2404_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
return v___x_2415_;
}
else
{
lean_object* v___x_2417_; 
lean_dec(v_a_2404_);
lean_dec(v_a_2402_);
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 0, v_e_2380_);
v___x_2417_ = v___x_2406_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_e_2380_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
}
else
{
lean_dec(v_a_2402_);
lean_dec_ref_known(v_e_2380_, 2);
return v___x_2403_;
}
}
else
{
lean_dec_ref_known(v_e_2380_, 2);
lean_dec_ref(v_xs_2379_);
return v___x_2401_;
}
}
case 8:
{
lean_object* v_declName_2420_; lean_object* v_type_2421_; lean_object* v_value_2422_; lean_object* v_body_2423_; uint8_t v_nondep_2424_; lean_object* v___x_2425_; 
v_declName_2420_ = lean_ctor_get(v_e_2380_, 0);
lean_inc(v_declName_2420_);
v_type_2421_ = lean_ctor_get(v_e_2380_, 1);
lean_inc_ref(v_type_2421_);
v_value_2422_ = lean_ctor_get(v_e_2380_, 2);
lean_inc_ref(v_value_2422_);
v_body_2423_ = lean_ctor_get(v_e_2380_, 3);
lean_inc_ref(v_body_2423_);
v_nondep_2424_ = lean_ctor_get_uint8(v_e_2380_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2380_, 4);
lean_inc_ref(v_xs_2379_);
v___x_2425_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v_xs_2379_, v_type_2421_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v_a_2426_; lean_object* v___x_2427_; 
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
lean_inc(v_a_2426_);
lean_dec_ref_known(v___x_2425_, 1);
lean_inc_ref(v_xs_2379_);
v___x_2427_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v_xs_2379_, v_value_2422_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
if (lean_obj_tag(v___x_2427_) == 0)
{
lean_object* v_a_2428_; lean_object* v___x_2429_; 
v_a_2428_ = lean_ctor_get(v___x_2427_, 0);
lean_inc(v_a_2428_);
lean_dec_ref_known(v___x_2427_, 1);
v___x_2429_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkDecl(v_declName_2420_, v_a_2426_, v_a_2428_, v_nondep_2424_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_object* v_a_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; 
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
lean_inc(v_a_2430_);
lean_dec_ref_known(v___x_2429_, 1);
v___x_2431_ = l_Lean_PersistentArray_push___redArg(v_xs_2379_, v_a_2430_);
v___x_2432_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v___x_2431_, v_body_2423_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
return v___x_2432_;
}
else
{
lean_dec_ref(v_body_2423_);
lean_dec_ref(v_xs_2379_);
return v___x_2429_;
}
}
else
{
lean_dec(v_a_2426_);
lean_dec_ref(v_body_2423_);
lean_dec(v_declName_2420_);
lean_dec_ref(v_xs_2379_);
return v___x_2427_;
}
}
else
{
lean_dec_ref(v_body_2423_);
lean_dec_ref(v_value_2422_);
lean_dec(v_declName_2420_);
lean_dec_ref(v_xs_2379_);
return v___x_2425_;
}
}
case 9:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; 
lean_dec_ref_known(v_e_2380_, 1);
lean_dec_ref(v_xs_2379_);
v___x_2433_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__2);
v___x_2434_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__0(v___x_2433_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
return v___x_2434_;
}
case 10:
{
lean_object* v_data_2435_; lean_object* v_expr_2436_; lean_object* v___x_2437_; 
v_data_2435_ = lean_ctor_get(v_e_2380_, 0);
v_expr_2436_ = lean_ctor_get(v_e_2380_, 1);
lean_inc_ref(v_expr_2436_);
v___x_2437_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v_xs_2379_, v_expr_2436_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v_a_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2449_; 
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2440_ = v___x_2437_;
v_isShared_2441_ = v_isSharedCheck_2449_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_a_2438_);
lean_dec(v___x_2437_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2449_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
size_t v___x_2442_; size_t v___x_2443_; uint8_t v___x_2444_; 
v___x_2442_ = lean_ptr_addr(v_expr_2436_);
v___x_2443_ = lean_ptr_addr(v_a_2438_);
v___x_2444_ = lean_usize_dec_eq(v___x_2442_, v___x_2443_);
if (v___x_2444_ == 0)
{
lean_object* v___x_2445_; 
lean_inc(v_data_2435_);
lean_del_object(v___x_2440_);
lean_dec_ref_known(v_e_2380_, 2);
v___x_2445_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__2___redArg(v_data_2435_, v_a_2438_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
return v___x_2445_;
}
else
{
lean_object* v___x_2447_; 
lean_dec(v_a_2438_);
if (v_isShared_2441_ == 0)
{
lean_ctor_set(v___x_2440_, 0, v_e_2380_);
v___x_2447_ = v___x_2440_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v_e_2380_);
v___x_2447_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
return v___x_2447_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2380_, 2);
return v___x_2437_;
}
}
case 11:
{
lean_object* v_typeName_2450_; lean_object* v_idx_2451_; lean_object* v_struct_2452_; lean_object* v___x_2453_; 
v_typeName_2450_ = lean_ctor_get(v_e_2380_, 0);
v_idx_2451_ = lean_ctor_get(v_e_2380_, 1);
v_struct_2452_ = lean_ctor_get(v_e_2380_, 2);
lean_inc_ref(v_struct_2452_);
v___x_2453_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v_xs_2379_, v_struct_2452_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
if (lean_obj_tag(v___x_2453_) == 0)
{
lean_object* v_a_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2465_; 
v_a_2454_ = lean_ctor_get(v___x_2453_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2456_ = v___x_2453_;
v_isShared_2457_ = v_isSharedCheck_2465_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_a_2454_);
lean_dec(v___x_2453_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2465_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
size_t v___x_2458_; size_t v___x_2459_; uint8_t v___x_2460_; 
v___x_2458_ = lean_ptr_addr(v_struct_2452_);
v___x_2459_ = lean_ptr_addr(v_a_2454_);
v___x_2460_ = lean_usize_dec_eq(v___x_2458_, v___x_2459_);
if (v___x_2460_ == 0)
{
lean_object* v___x_2461_; 
lean_inc(v_idx_2451_);
lean_inc(v_typeName_2450_);
lean_del_object(v___x_2456_);
lean_dec_ref_known(v_e_2380_, 3);
v___x_2461_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit_spec__3___redArg(v_typeName_2450_, v_idx_2451_, v_a_2454_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
return v___x_2461_;
}
else
{
lean_object* v___x_2463_; 
lean_dec(v_a_2454_);
if (v_isShared_2457_ == 0)
{
lean_ctor_set(v___x_2456_, 0, v_e_2380_);
v___x_2463_ = v___x_2456_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_e_2380_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2380_, 3);
return v___x_2453_;
}
}
default: 
{
lean_object* v___x_2466_; 
v___x_2466_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg(v_xs_2379_, v_e_2380_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
return v___x_2466_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(lean_object* v_xs_2467_, lean_object* v_e_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_){
_start:
{
switch(lean_obj_tag(v_e_2468_))
{
case 0:
{
lean_object* v_deBruijnIndex_2477_; lean_object* v_size_2478_; uint8_t v___x_2479_; 
v_deBruijnIndex_2477_ = lean_ctor_get(v_e_2468_, 0);
lean_inc(v_deBruijnIndex_2477_);
lean_dec_ref_known(v_e_2468_, 1);
v_size_2478_ = lean_ctor_get(v_xs_2467_, 2);
v___x_2479_ = lean_nat_dec_lt(v_deBruijnIndex_2477_, v_size_2478_);
if (v___x_2479_ == 0)
{
lean_object* v___x_2480_; lean_object* v___x_2481_; 
lean_dec(v_deBruijnIndex_2477_);
lean_dec_ref(v_xs_2467_);
v___x_2480_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__1, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__1_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__1);
v___x_2481_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5___redArg(v___x_2480_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
return v___x_2481_;
}
else
{
lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2482_ = l_Lean_instInhabitedExpr;
v___x_2483_ = lean_nat_sub(v_size_2478_, v_deBruijnIndex_2477_);
lean_dec(v_deBruijnIndex_2477_);
v___x_2484_ = lean_unsigned_to_nat(1u);
v___x_2485_ = lean_nat_sub(v___x_2483_, v___x_2484_);
lean_dec(v___x_2483_);
v___x_2486_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2482_, v_xs_2467_, v___x_2485_);
lean_dec(v___x_2485_);
lean_dec_ref(v_xs_2467_);
v___x_2487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2486_);
return v___x_2487_;
}
}
case 1:
{
lean_object* v___x_2488_; 
lean_dec_ref(v_xs_2467_);
v___x_2488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2488_, 0, v_e_2468_);
return v___x_2488_;
}
case 2:
{
lean_object* v___x_2489_; 
lean_dec_ref(v_xs_2467_);
v___x_2489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2489_, 0, v_e_2468_);
return v___x_2489_;
}
case 3:
{
lean_object* v___x_2490_; 
lean_dec_ref(v_xs_2467_);
v___x_2490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2490_, 0, v_e_2468_);
return v___x_2490_;
}
case 4:
{
lean_object* v___x_2491_; 
lean_dec_ref(v_xs_2467_);
v___x_2491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2491_, 0, v_e_2468_);
return v___x_2491_;
}
case 9:
{
lean_object* v___x_2492_; 
lean_dec_ref(v_xs_2467_);
v___x_2492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2492_, 0, v_e_2468_);
return v___x_2492_;
}
default: 
{
uint8_t v___x_2493_; 
v___x_2493_ = l_Lean_Expr_hasLooseBVars(v_e_2468_);
if (v___x_2493_ == 0)
{
lean_object* v___x_2494_; 
lean_dec_ref(v_xs_2467_);
lean_inc_ref(v_e_2468_);
v___x_2494_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet(v_e_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2535_; 
v_a_2495_ = lean_ctor_get(v___x_2494_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2497_ = v___x_2494_;
v_isShared_2498_ = v_isSharedCheck_2535_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2494_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2535_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
uint8_t v___x_2499_; 
v___x_2499_ = lean_unbox(v_a_2495_);
lean_dec(v_a_2495_);
if (v___x_2499_ == 0)
{
lean_object* v___x_2501_; 
if (v_isShared_2498_ == 0)
{
lean_ctor_set(v___x_2497_, 0, v_e_2468_);
v___x_2501_ = v___x_2497_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_e_2468_);
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
lean_object* v___x_2503_; lean_object* v_cacheClosed_2504_; lean_object* v___x_2505_; 
v___x_2503_ = lean_st_ref_get(v_a_2469_);
v_cacheClosed_2504_ = lean_ctor_get(v___x_2503_, 1);
lean_inc_ref(v_cacheClosed_2504_);
lean_dec(v___x_2503_);
v___x_2505_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__0___redArg(v_cacheClosed_2504_, v_e_2468_);
lean_dec_ref(v_cacheClosed_2504_);
if (lean_obj_tag(v___x_2505_) == 1)
{
lean_object* v_val_2506_; lean_object* v___x_2508_; 
lean_dec_ref(v_e_2468_);
v_val_2506_ = lean_ctor_get(v___x_2505_, 0);
lean_inc(v_val_2506_);
lean_dec_ref_known(v___x_2505_, 1);
if (v_isShared_2498_ == 0)
{
lean_ctor_set(v___x_2497_, 0, v_val_2506_);
v___x_2508_ = v___x_2497_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_val_2506_);
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
lean_object* v___x_2510_; lean_object* v___x_2511_; 
lean_dec(v___x_2505_);
lean_del_object(v___x_2497_);
v___x_2510_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__3, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__3_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__3);
lean_inc_ref(v_e_2468_);
v___x_2511_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit(v___x_2510_, v_e_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
if (lean_obj_tag(v___x_2511_) == 0)
{
lean_object* v_a_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2534_; 
v_a_2512_ = lean_ctor_get(v___x_2511_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2514_ = v___x_2511_;
v_isShared_2515_ = v_isSharedCheck_2534_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_a_2512_);
lean_dec(v___x_2511_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2534_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2516_; lean_object* v_cache_2517_; lean_object* v_cacheClosed_2518_; lean_object* v_hasLetCache_2519_; lean_object* v_decls_2520_; lean_object* v_valueMap_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2533_; 
v___x_2516_ = lean_st_ref_take(v_a_2469_);
v_cache_2517_ = lean_ctor_get(v___x_2516_, 0);
v_cacheClosed_2518_ = lean_ctor_get(v___x_2516_, 1);
v_hasLetCache_2519_ = lean_ctor_get(v___x_2516_, 2);
v_decls_2520_ = lean_ctor_get(v___x_2516_, 3);
v_valueMap_2521_ = lean_ctor_get(v___x_2516_, 4);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2516_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2523_ = v___x_2516_;
v_isShared_2524_ = v_isSharedCheck_2533_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_valueMap_2521_);
lean_inc(v_decls_2520_);
lean_inc(v_hasLetCache_2519_);
lean_inc(v_cacheClosed_2518_);
lean_inc(v_cache_2517_);
lean_dec(v___x_2516_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2533_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2525_; lean_object* v___x_2527_; 
lean_inc(v_a_2512_);
v___x_2525_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_hasLiftableLet_spec__1___redArg(v_cacheClosed_2518_, v_e_2468_, v_a_2512_);
if (v_isShared_2524_ == 0)
{
lean_ctor_set(v___x_2523_, 1, v___x_2525_);
v___x_2527_ = v___x_2523_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_cache_2517_);
lean_ctor_set(v_reuseFailAlloc_2532_, 1, v___x_2525_);
lean_ctor_set(v_reuseFailAlloc_2532_, 2, v_hasLetCache_2519_);
lean_ctor_set(v_reuseFailAlloc_2532_, 3, v_decls_2520_);
lean_ctor_set(v_reuseFailAlloc_2532_, 4, v_valueMap_2521_);
v___x_2527_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
lean_object* v___x_2528_; lean_object* v___x_2530_; 
v___x_2528_ = lean_st_ref_put(v_a_2469_, v___x_2527_);
if (v_isShared_2515_ == 0)
{
v___x_2530_ = v___x_2514_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_a_2512_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_2468_);
return v___x_2511_;
}
}
}
}
}
else
{
lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
lean_dec_ref(v_e_2468_);
v_a_2536_ = lean_ctor_get(v___x_2494_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2538_ = v___x_2494_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2494_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2536_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
}
else
{
lean_object* v_key_2544_; lean_object* v___x_2545_; lean_object* v_cache_2546_; lean_object* v___x_2547_; 
lean_inc_ref(v_e_2468_);
lean_inc_ref(v_xs_2467_);
v_key_2544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_2544_, 0, v_xs_2467_);
lean_ctor_set(v_key_2544_, 1, v_e_2468_);
v___x_2545_ = lean_st_ref_get(v_a_2469_);
v_cache_2546_ = lean_ctor_get(v___x_2545_, 0);
lean_inc_ref(v_cache_2546_);
lean_dec(v___x_2545_);
v___x_2547_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6___redArg(v_cache_2546_, v_key_2544_);
lean_dec_ref(v_cache_2546_);
if (lean_obj_tag(v___x_2547_) == 1)
{
lean_object* v_val_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2555_; 
lean_dec_ref_known(v_key_2544_, 2);
lean_dec_ref(v_e_2468_);
lean_dec_ref(v_xs_2467_);
v_val_2548_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2550_ = v___x_2547_;
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_val_2548_);
lean_dec(v___x_2547_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2553_; 
if (v_isShared_2551_ == 0)
{
lean_ctor_set_tag(v___x_2550_, 0);
v___x_2553_ = v___x_2550_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_val_2548_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
return v___x_2553_;
}
}
}
else
{
lean_object* v___x_2556_; 
lean_dec(v___x_2547_);
v___x_2556_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit(v_xs_2467_, v_e_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2579_; 
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2559_ = v___x_2556_;
v_isShared_2560_ = v_isSharedCheck_2579_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_dec(v___x_2556_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2579_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2561_; lean_object* v_cache_2562_; lean_object* v_cacheClosed_2563_; lean_object* v_hasLetCache_2564_; lean_object* v_decls_2565_; lean_object* v_valueMap_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2578_; 
v___x_2561_ = lean_st_ref_take(v_a_2469_);
v_cache_2562_ = lean_ctor_get(v___x_2561_, 0);
v_cacheClosed_2563_ = lean_ctor_get(v___x_2561_, 1);
v_hasLetCache_2564_ = lean_ctor_get(v___x_2561_, 2);
v_decls_2565_ = lean_ctor_get(v___x_2561_, 3);
v_valueMap_2566_ = lean_ctor_get(v___x_2561_, 4);
v_isSharedCheck_2578_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2568_ = v___x_2561_;
v_isShared_2569_ = v_isSharedCheck_2578_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_valueMap_2566_);
lean_inc(v_decls_2565_);
lean_inc(v_hasLetCache_2564_);
lean_inc(v_cacheClosed_2563_);
lean_inc(v_cache_2562_);
lean_dec(v___x_2561_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2578_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2570_; lean_object* v___x_2572_; 
lean_inc(v_a_2557_);
v___x_2570_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7___redArg(v_cache_2562_, v_key_2544_, v_a_2557_);
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 0, v___x_2570_);
v___x_2572_ = v___x_2568_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v___x_2570_);
lean_ctor_set(v_reuseFailAlloc_2577_, 1, v_cacheClosed_2563_);
lean_ctor_set(v_reuseFailAlloc_2577_, 2, v_hasLetCache_2564_);
lean_ctor_set(v_reuseFailAlloc_2577_, 3, v_decls_2565_);
lean_ctor_set(v_reuseFailAlloc_2577_, 4, v_valueMap_2566_);
v___x_2572_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
lean_object* v___x_2573_; lean_object* v___x_2575_; 
v___x_2573_ = lean_st_ref_put(v_a_2469_, v___x_2572_);
if (v_isShared_2560_ == 0)
{
v___x_2575_ = v___x_2559_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_a_2557_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_2544_, 2);
return v___x_2556_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___boxed(lean_object* v_xs_2580_, lean_object* v_e_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_){
_start:
{
lean_object* v_res_2590_; 
v_res_2590_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v_xs_2580_, v_e_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_);
lean_dec(v_a_2588_);
lean_dec_ref(v_a_2587_);
lean_dec(v_a_2586_);
lean_dec_ref(v_a_2585_);
lean_dec(v_a_2584_);
lean_dec_ref(v_a_2583_);
lean_dec(v_a_2582_);
return v_res_2590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___boxed(lean_object* v_xs_2591_, lean_object* v_e_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit(v_xs_2591_, v_e_2592_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_, v_a_2599_);
lean_dec(v_a_2599_);
lean_dec_ref(v_a_2598_);
lean_dec(v_a_2597_);
lean_dec_ref(v_a_2596_);
lean_dec(v_a_2595_);
lean_dec_ref(v_a_2594_);
lean_dec(v_a_2593_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5(lean_object* v_00_u03b1_2602_, lean_object* v_msg_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_){
_start:
{
lean_object* v___x_2612_; 
v___x_2612_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5___redArg(v_msg_2603_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
return v___x_2612_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5___boxed(lean_object* v_00_u03b1_2613_, lean_object* v_msg_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_){
_start:
{
lean_object* v_res_2623_; 
v_res_2623_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5(v_00_u03b1_2613_, v_msg_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
lean_dec(v___y_2621_);
lean_dec_ref(v___y_2620_);
lean_dec(v___y_2619_);
lean_dec_ref(v___y_2618_);
lean_dec(v___y_2617_);
lean_dec_ref(v___y_2616_);
lean_dec(v___y_2615_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6(lean_object* v_00_u03b2_2624_, lean_object* v_m_2625_, lean_object* v_a_2626_){
_start:
{
lean_object* v___x_2627_; 
v___x_2627_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6___redArg(v_m_2625_, v_a_2626_);
return v___x_2627_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6___boxed(lean_object* v_00_u03b2_2628_, lean_object* v_m_2629_, lean_object* v_a_2630_){
_start:
{
lean_object* v_res_2631_; 
v_res_2631_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6(v_00_u03b2_2628_, v_m_2629_, v_a_2630_);
lean_dec_ref(v_a_2630_);
lean_dec_ref(v_m_2629_);
return v_res_2631_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7(lean_object* v_00_u03b2_2632_, lean_object* v_m_2633_, lean_object* v_a_2634_, lean_object* v_b_2635_){
_start:
{
lean_object* v___x_2636_; 
v___x_2636_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7___redArg(v_m_2633_, v_a_2634_, v_b_2635_);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7(lean_object* v_00_u03b2_2637_, lean_object* v_a_2638_, lean_object* v_x_2639_){
_start:
{
lean_object* v___x_2640_; 
v___x_2640_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7___redArg(v_a_2638_, v_x_2639_);
return v___x_2640_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7___boxed(lean_object* v_00_u03b2_2641_, lean_object* v_a_2642_, lean_object* v_x_2643_){
_start:
{
lean_object* v_res_2644_; 
v_res_2644_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__6_spec__7(v_00_u03b2_2641_, v_a_2642_, v_x_2643_);
lean_dec(v_x_2643_);
lean_dec_ref(v_a_2642_);
return v_res_2644_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9(lean_object* v_00_u03b2_2645_, lean_object* v_a_2646_, lean_object* v_x_2647_){
_start:
{
uint8_t v___x_2648_; 
v___x_2648_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9___redArg(v_a_2646_, v_x_2647_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9___boxed(lean_object* v_00_u03b2_2649_, lean_object* v_a_2650_, lean_object* v_x_2651_){
_start:
{
uint8_t v_res_2652_; lean_object* v_r_2653_; 
v_res_2652_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__9(v_00_u03b2_2649_, v_a_2650_, v_x_2651_);
lean_dec(v_x_2651_);
lean_dec_ref(v_a_2650_);
v_r_2653_ = lean_box(v_res_2652_);
return v_r_2653_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10(lean_object* v_00_u03b2_2654_, lean_object* v_data_2655_){
_start:
{
lean_object* v___x_2656_; 
v___x_2656_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10___redArg(v_data_2655_);
return v___x_2656_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__11(lean_object* v_00_u03b2_2657_, lean_object* v_a_2658_, lean_object* v_b_2659_, lean_object* v_x_2660_){
_start:
{
lean_object* v___x_2661_; 
v___x_2661_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__11___redArg(v_a_2658_, v_b_2659_, v_x_2660_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10_spec__11(lean_object* v_00_u03b2_2662_, lean_object* v_i_2663_, lean_object* v_source_2664_, lean_object* v_target_2665_){
_start:
{
lean_object* v___x_2666_; 
v___x_2666_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10_spec__11___redArg(v_i_2663_, v_source_2664_, v_target_2665_);
return v___x_2666_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10_spec__11_spec__12(lean_object* v_00_u03b2_2667_, lean_object* v_x_2668_, lean_object* v_x_2669_){
_start:
{
lean_object* v___x_2670_; 
v___x_2670_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__7_spec__10_spec__11_spec__12___redArg(v_x_2668_, v_x_2669_);
return v___x_2670_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2671_; 
v___x_2671_ = l_Std_HashMap_instInhabited___redArg();
return v___x_2671_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3(lean_object* v_msg_2672_, uint8_t v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_){
_start:
{
lean_object* v___x_2676_; lean_object* v___f_2677_; lean_object* v___f_2678_; lean_object* v___f_2679_; lean_object* v___x_10671__overap_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; 
v___x_2676_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3___closed__0);
v___f_2677_ = lean_alloc_closure((void*)(l_EStateM_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2677_, 0, v___x_2676_);
v___f_2678_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2678_, 0, v___f_2677_);
v___f_2679_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2679_, 0, v___f_2678_);
v___x_10671__overap_2680_ = lean_panic_fn_borrowed(v___f_2679_, v_msg_2672_);
lean_dec_ref(v___f_2679_);
v___x_2681_ = lean_box(v___y_2673_);
lean_inc_ref(v___y_2674_);
v___x_2682_ = lean_apply_3(v___x_10671__overap_2680_, v___x_2681_, v___y_2674_, v___y_2675_);
return v___x_2682_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3___boxed(lean_object* v_msg_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_){
_start:
{
uint8_t v___y_15640__boxed_2687_; lean_object* v_res_2688_; 
v___y_15640__boxed_2687_ = lean_unbox(v___y_2684_);
v_res_2688_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3(v_msg_2683_, v___y_15640__boxed_2687_, v___y_2685_, v___y_2686_);
lean_dec_ref(v___y_2685_);
return v_res_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4___redArg(lean_object* v_idx_2689_, lean_object* v___y_2690_){
_start:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; 
v___x_2691_ = l_Lean_Expr_bvar___override(v_idx_2689_);
v___x_2692_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_2691_, v___y_2690_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4(lean_object* v_idx_2693_, uint8_t v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_){
_start:
{
lean_object* v___x_2697_; 
v___x_2697_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4___redArg(v_idx_2693_, v___y_2696_);
return v___x_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4___boxed(lean_object* v_idx_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_){
_start:
{
uint8_t v___y_15668__boxed_2702_; lean_object* v_res_2703_; 
v___y_15668__boxed_2702_ = lean_unbox(v___y_2699_);
v_res_2703_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4(v_idx_2698_, v___y_15668__boxed_2702_, v___y_2700_, v___y_2701_);
lean_dec_ref(v___y_2700_);
return v_res_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6___redArg(lean_object* v_x_2704_, lean_object* v_t_2705_, lean_object* v_v_2706_, lean_object* v_b_2707_, uint8_t v_nondep_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_){
_start:
{
lean_object* v___y_2717_; lean_object* v___x_2720_; uint8_t v_debug_2721_; 
v___x_2720_ = lean_st_ref_get(v___y_2710_);
v_debug_2721_ = lean_ctor_get_uint8(v___x_2720_, sizeof(void*)*12);
lean_dec(v___x_2720_);
if (v_debug_2721_ == 0)
{
v___y_2717_ = v___y_2710_;
goto v___jp_2716_;
}
else
{
lean_object* v___x_2722_; 
v___x_2722_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_2705_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_);
if (lean_obj_tag(v___x_2722_) == 0)
{
lean_object* v___x_2723_; 
lean_dec_ref_known(v___x_2722_, 1);
v___x_2723_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_v_2706_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_);
if (lean_obj_tag(v___x_2723_) == 0)
{
lean_object* v___x_2724_; 
lean_dec_ref_known(v___x_2723_, 1);
v___x_2724_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_2707_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_);
if (lean_obj_tag(v___x_2724_) == 0)
{
lean_dec_ref_known(v___x_2724_, 1);
v___y_2717_ = v___y_2710_;
goto v___jp_2716_;
}
else
{
lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2732_; 
lean_dec_ref(v_b_2707_);
lean_dec_ref(v_v_2706_);
lean_dec_ref(v_t_2705_);
lean_dec(v_x_2704_);
v_a_2725_ = lean_ctor_get(v___x_2724_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2724_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2727_ = v___x_2724_;
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v___x_2724_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2730_; 
if (v_isShared_2728_ == 0)
{
v___x_2730_ = v___x_2727_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_a_2725_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
}
else
{
lean_object* v_a_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2740_; 
lean_dec_ref(v_b_2707_);
lean_dec_ref(v_v_2706_);
lean_dec_ref(v_t_2705_);
lean_dec(v_x_2704_);
v_a_2733_ = lean_ctor_get(v___x_2723_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2735_ = v___x_2723_;
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_a_2733_);
lean_dec(v___x_2723_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2738_; 
if (v_isShared_2736_ == 0)
{
v___x_2738_ = v___x_2735_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_a_2733_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
}
}
else
{
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2748_; 
lean_dec_ref(v_b_2707_);
lean_dec_ref(v_v_2706_);
lean_dec_ref(v_t_2705_);
lean_dec(v_x_2704_);
v_a_2741_ = lean_ctor_get(v___x_2722_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2743_ = v___x_2722_;
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___x_2722_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2746_; 
if (v_isShared_2744_ == 0)
{
v___x_2746_ = v___x_2743_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_a_2741_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
}
}
}
}
v___jp_2716_:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2718_ = l_Lean_Expr_letE___override(v_x_2704_, v_t_2705_, v_v_2706_, v_b_2707_, v_nondep_2708_);
v___x_2719_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2718_, v___y_2717_);
return v___x_2719_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6___redArg___boxed(lean_object* v_x_2749_, lean_object* v_t_2750_, lean_object* v_v_2751_, lean_object* v_b_2752_, lean_object* v_nondep_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_){
_start:
{
uint8_t v_nondep_boxed_2761_; lean_object* v_res_2762_; 
v_nondep_boxed_2761_ = lean_unbox(v_nondep_2753_);
v_res_2762_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6___redArg(v_x_2749_, v_t_2750_, v_v_2751_, v_b_2752_, v_nondep_boxed_2761_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
lean_dec(v___y_2759_);
lean_dec_ref(v___y_2758_);
lean_dec(v___y_2757_);
lean_dec_ref(v___y_2756_);
lean_dec(v___y_2755_);
lean_dec_ref(v___y_2754_);
return v_res_2762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6(lean_object* v_x_2763_, lean_object* v_t_2764_, lean_object* v_v_2765_, lean_object* v_b_2766_, uint8_t v_nondep_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
lean_object* v___x_2776_; 
v___x_2776_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6___redArg(v_x_2763_, v_t_2764_, v_v_2765_, v_b_2766_, v_nondep_2767_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_);
return v___x_2776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6___boxed(lean_object* v_x_2777_, lean_object* v_t_2778_, lean_object* v_v_2779_, lean_object* v_b_2780_, lean_object* v_nondep_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_){
_start:
{
uint8_t v_nondep_boxed_2790_; lean_object* v_res_2791_; 
v_nondep_boxed_2790_ = lean_unbox(v_nondep_2781_);
v_res_2791_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6(v_x_2777_, v_t_2778_, v_v_2779_, v_b_2780_, v_nondep_boxed_2790_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_);
lean_dec(v___y_2788_);
lean_dec_ref(v___y_2787_);
lean_dec(v___y_2786_);
lean_dec_ref(v___y_2785_);
lean_dec(v___y_2784_);
lean_dec_ref(v___y_2783_);
lean_dec(v___y_2782_);
return v_res_2791_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2_spec__5___redArg(lean_object* v_a_2792_, lean_object* v_x_2793_){
_start:
{
if (lean_obj_tag(v_x_2793_) == 0)
{
lean_object* v___x_2794_; 
v___x_2794_ = lean_box(0);
return v___x_2794_;
}
else
{
lean_object* v_key_2795_; lean_object* v_value_2796_; lean_object* v_tail_2797_; uint8_t v___x_2798_; 
v_key_2795_ = lean_ctor_get(v_x_2793_, 0);
v_value_2796_ = lean_ctor_get(v_x_2793_, 1);
v_tail_2797_ = lean_ctor_get(v_x_2793_, 2);
v___x_2798_ = l_Lean_instBEqFVarId_beq(v_key_2795_, v_a_2792_);
if (v___x_2798_ == 0)
{
v_x_2793_ = v_tail_2797_;
goto _start;
}
else
{
lean_object* v___x_2800_; 
lean_inc(v_value_2796_);
v___x_2800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2800_, 0, v_value_2796_);
return v___x_2800_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2_spec__5___redArg___boxed(lean_object* v_a_2801_, lean_object* v_x_2802_){
_start:
{
lean_object* v_res_2803_; 
v_res_2803_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2_spec__5___redArg(v_a_2801_, v_x_2802_);
lean_dec(v_x_2802_);
lean_dec(v_a_2801_);
return v_res_2803_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___redArg(lean_object* v_m_2804_, lean_object* v_a_2805_){
_start:
{
lean_object* v_buckets_2806_; lean_object* v___x_2807_; uint64_t v___x_2808_; uint64_t v___x_2809_; uint64_t v___x_2810_; uint64_t v_fold_2811_; uint64_t v___x_2812_; uint64_t v___x_2813_; uint64_t v___x_2814_; size_t v___x_2815_; size_t v___x_2816_; size_t v___x_2817_; size_t v___x_2818_; size_t v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; 
v_buckets_2806_ = lean_ctor_get(v_m_2804_, 1);
v___x_2807_ = lean_array_get_size(v_buckets_2806_);
v___x_2808_ = l_Lean_instHashableFVarId_hash(v_a_2805_);
v___x_2809_ = 32ULL;
v___x_2810_ = lean_uint64_shift_right(v___x_2808_, v___x_2809_);
v_fold_2811_ = lean_uint64_xor(v___x_2808_, v___x_2810_);
v___x_2812_ = 16ULL;
v___x_2813_ = lean_uint64_shift_right(v_fold_2811_, v___x_2812_);
v___x_2814_ = lean_uint64_xor(v_fold_2811_, v___x_2813_);
v___x_2815_ = lean_uint64_to_usize(v___x_2814_);
v___x_2816_ = lean_usize_of_nat(v___x_2807_);
v___x_2817_ = ((size_t)1ULL);
v___x_2818_ = lean_usize_sub(v___x_2816_, v___x_2817_);
v___x_2819_ = lean_usize_land(v___x_2815_, v___x_2818_);
v___x_2820_ = lean_array_uget_borrowed(v_buckets_2806_, v___x_2819_);
v___x_2821_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2_spec__5___redArg(v_a_2805_, v___x_2820_);
return v___x_2821_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___redArg___boxed(lean_object* v_m_2822_, lean_object* v_a_2823_){
_start:
{
lean_object* v_res_2824_; 
v_res_2824_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___redArg(v_m_2822_, v_a_2823_);
lean_dec(v_a_2823_);
lean_dec_ref(v_m_2822_);
return v_res_2824_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2(void){
_start:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; 
v___x_2827_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__1));
v___x_2828_ = lean_unsigned_to_nat(10u);
v___x_2829_ = lean_unsigned_to_nat(236u);
v___x_2830_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__0));
v___x_2831_ = ((lean_object*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_visit___closed__0));
v___x_2832_ = l_mkPanicMessageWithDecl(v___x_2831_, v___x_2830_, v___x_2829_, v___x_2828_, v___x_2827_);
return v___x_2832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5(lean_object* v___x_2833_, lean_object* v_i_2834_, lean_object* v_e_2835_, lean_object* v_offset_2836_, lean_object* v_a_2837_, uint8_t v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_){
_start:
{
switch(lean_obj_tag(v_e_2835_))
{
case 5:
{
lean_object* v_fn_2841_; lean_object* v_arg_2842_; lean_object* v___x_2843_; 
v_fn_2841_ = lean_ctor_get(v_e_2835_, 0);
v_arg_2842_ = lean_ctor_get(v_e_2835_, 1);
lean_inc(v_offset_2836_);
lean_inc_ref(v_fn_2841_);
v___x_2843_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2833_, v_i_2834_, v_fn_2841_, v_offset_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_);
if (lean_obj_tag(v___x_2843_) == 0)
{
lean_object* v_a_2844_; lean_object* v_a_2845_; lean_object* v_fst_2846_; lean_object* v_snd_2847_; lean_object* v___x_2848_; 
v_a_2844_ = lean_ctor_get(v___x_2843_, 0);
lean_inc(v_a_2844_);
v_a_2845_ = lean_ctor_get(v___x_2843_, 1);
lean_inc(v_a_2845_);
lean_dec_ref_known(v___x_2843_, 2);
v_fst_2846_ = lean_ctor_get(v_a_2844_, 0);
lean_inc(v_fst_2846_);
v_snd_2847_ = lean_ctor_get(v_a_2844_, 1);
lean_inc(v_snd_2847_);
lean_dec(v_a_2844_);
lean_inc_ref(v_arg_2842_);
v___x_2848_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2833_, v_i_2834_, v_arg_2842_, v_offset_2836_, v_snd_2847_, v_a_2838_, v_a_2839_, v_a_2845_);
if (lean_obj_tag(v___x_2848_) == 0)
{
lean_object* v_a_2849_; lean_object* v_a_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2874_; 
v_a_2849_ = lean_ctor_get(v___x_2848_, 0);
v_a_2850_ = lean_ctor_get(v___x_2848_, 1);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2852_ = v___x_2848_;
v_isShared_2853_ = v_isSharedCheck_2874_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_a_2850_);
lean_inc(v_a_2849_);
lean_dec(v___x_2848_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2874_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v_fst_2854_; lean_object* v_snd_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2873_; 
v_fst_2854_ = lean_ctor_get(v_a_2849_, 0);
v_snd_2855_ = lean_ctor_get(v_a_2849_, 1);
v_isSharedCheck_2873_ = !lean_is_exclusive(v_a_2849_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2857_ = v_a_2849_;
v_isShared_2858_ = v_isSharedCheck_2873_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_snd_2855_);
lean_inc(v_fst_2854_);
lean_dec(v_a_2849_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2873_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
size_t v___x_2859_; size_t v___x_2860_; uint8_t v___x_2861_; 
v___x_2859_ = lean_ptr_addr(v_fn_2841_);
v___x_2860_ = lean_ptr_addr(v_fst_2846_);
v___x_2861_ = lean_usize_dec_eq(v___x_2859_, v___x_2860_);
if (v___x_2861_ == 0)
{
lean_object* v___x_2862_; 
lean_del_object(v___x_2857_);
lean_del_object(v___x_2852_);
lean_dec_ref_known(v_e_2835_, 2);
v___x_2862_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__1(v_fst_2846_, v_fst_2854_, v_snd_2855_, v_a_2838_, v_a_2839_, v_a_2850_);
return v___x_2862_;
}
else
{
size_t v___x_2863_; size_t v___x_2864_; uint8_t v___x_2865_; 
v___x_2863_ = lean_ptr_addr(v_arg_2842_);
v___x_2864_ = lean_ptr_addr(v_fst_2854_);
v___x_2865_ = lean_usize_dec_eq(v___x_2863_, v___x_2864_);
if (v___x_2865_ == 0)
{
lean_object* v___x_2866_; 
lean_del_object(v___x_2857_);
lean_del_object(v___x_2852_);
lean_dec_ref_known(v_e_2835_, 2);
v___x_2866_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__1(v_fst_2846_, v_fst_2854_, v_snd_2855_, v_a_2838_, v_a_2839_, v_a_2850_);
return v___x_2866_;
}
else
{
lean_object* v___x_2868_; 
lean_dec(v_fst_2854_);
lean_dec(v_fst_2846_);
if (v_isShared_2858_ == 0)
{
lean_ctor_set(v___x_2857_, 0, v_e_2835_);
v___x_2868_ = v___x_2857_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_e_2835_);
lean_ctor_set(v_reuseFailAlloc_2872_, 1, v_snd_2855_);
v___x_2868_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
lean_object* v___x_2870_; 
if (v_isShared_2853_ == 0)
{
lean_ctor_set(v___x_2852_, 0, v___x_2868_);
v___x_2870_ = v___x_2852_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v___x_2868_);
lean_ctor_set(v_reuseFailAlloc_2871_, 1, v_a_2850_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_2846_);
lean_dec_ref_known(v_e_2835_, 2);
return v___x_2848_;
}
}
else
{
lean_dec_ref_known(v_e_2835_, 2);
lean_dec(v_offset_2836_);
return v___x_2843_;
}
}
case 6:
{
lean_object* v_binderName_2875_; lean_object* v_binderType_2876_; lean_object* v_body_2877_; uint8_t v_binderInfo_2878_; lean_object* v___x_2879_; 
v_binderName_2875_ = lean_ctor_get(v_e_2835_, 0);
v_binderType_2876_ = lean_ctor_get(v_e_2835_, 1);
v_body_2877_ = lean_ctor_get(v_e_2835_, 2);
v_binderInfo_2878_ = lean_ctor_get_uint8(v_e_2835_, sizeof(void*)*3 + 8);
lean_inc(v_offset_2836_);
lean_inc_ref(v_binderType_2876_);
v___x_2879_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2833_, v_i_2834_, v_binderType_2876_, v_offset_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v_a_2880_; lean_object* v_a_2881_; lean_object* v_fst_2882_; lean_object* v_snd_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v_a_2880_ = lean_ctor_get(v___x_2879_, 0);
lean_inc(v_a_2880_);
v_a_2881_ = lean_ctor_get(v___x_2879_, 1);
lean_inc(v_a_2881_);
lean_dec_ref_known(v___x_2879_, 2);
v_fst_2882_ = lean_ctor_get(v_a_2880_, 0);
lean_inc(v_fst_2882_);
v_snd_2883_ = lean_ctor_get(v_a_2880_, 1);
lean_inc(v_snd_2883_);
lean_dec(v_a_2880_);
v___x_2884_ = lean_unsigned_to_nat(1u);
v___x_2885_ = lean_nat_add(v_offset_2836_, v___x_2884_);
lean_dec(v_offset_2836_);
lean_inc_ref(v_body_2877_);
v___x_2886_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2833_, v_i_2834_, v_body_2877_, v___x_2885_, v_snd_2883_, v_a_2838_, v_a_2839_, v_a_2881_);
if (lean_obj_tag(v___x_2886_) == 0)
{
lean_object* v_a_2887_; lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2912_; 
v_a_2887_ = lean_ctor_get(v___x_2886_, 0);
v_a_2888_ = lean_ctor_get(v___x_2886_, 1);
v_isSharedCheck_2912_ = !lean_is_exclusive(v___x_2886_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2890_ = v___x_2886_;
v_isShared_2891_ = v_isSharedCheck_2912_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_inc(v_a_2887_);
lean_dec(v___x_2886_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2912_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v_fst_2892_; lean_object* v_snd_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2911_; 
v_fst_2892_ = lean_ctor_get(v_a_2887_, 0);
v_snd_2893_ = lean_ctor_get(v_a_2887_, 1);
v_isSharedCheck_2911_ = !lean_is_exclusive(v_a_2887_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2895_ = v_a_2887_;
v_isShared_2896_ = v_isSharedCheck_2911_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_snd_2893_);
lean_inc(v_fst_2892_);
lean_dec(v_a_2887_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2911_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
size_t v___x_2897_; size_t v___x_2898_; uint8_t v___x_2899_; 
v___x_2897_ = lean_ptr_addr(v_binderType_2876_);
v___x_2898_ = lean_ptr_addr(v_fst_2882_);
v___x_2899_ = lean_usize_dec_eq(v___x_2897_, v___x_2898_);
if (v___x_2899_ == 0)
{
lean_object* v___x_2900_; 
lean_inc(v_binderName_2875_);
lean_del_object(v___x_2895_);
lean_del_object(v___x_2890_);
lean_dec_ref_known(v_e_2835_, 3);
v___x_2900_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__2(v_binderName_2875_, v_binderInfo_2878_, v_fst_2882_, v_fst_2892_, v_snd_2893_, v_a_2838_, v_a_2839_, v_a_2888_);
return v___x_2900_;
}
else
{
size_t v___x_2901_; size_t v___x_2902_; uint8_t v___x_2903_; 
v___x_2901_ = lean_ptr_addr(v_body_2877_);
v___x_2902_ = lean_ptr_addr(v_fst_2892_);
v___x_2903_ = lean_usize_dec_eq(v___x_2901_, v___x_2902_);
if (v___x_2903_ == 0)
{
lean_object* v___x_2904_; 
lean_inc(v_binderName_2875_);
lean_del_object(v___x_2895_);
lean_del_object(v___x_2890_);
lean_dec_ref_known(v_e_2835_, 3);
v___x_2904_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__2(v_binderName_2875_, v_binderInfo_2878_, v_fst_2882_, v_fst_2892_, v_snd_2893_, v_a_2838_, v_a_2839_, v_a_2888_);
return v___x_2904_;
}
else
{
lean_object* v___x_2906_; 
lean_dec(v_fst_2892_);
lean_dec(v_fst_2882_);
if (v_isShared_2896_ == 0)
{
lean_ctor_set(v___x_2895_, 0, v_e_2835_);
v___x_2906_ = v___x_2895_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_e_2835_);
lean_ctor_set(v_reuseFailAlloc_2910_, 1, v_snd_2893_);
v___x_2906_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
lean_object* v___x_2908_; 
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 0, v___x_2906_);
v___x_2908_ = v___x_2890_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v___x_2906_);
lean_ctor_set(v_reuseFailAlloc_2909_, 1, v_a_2888_);
v___x_2908_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
return v___x_2908_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_2882_);
lean_dec_ref_known(v_e_2835_, 3);
return v___x_2886_;
}
}
else
{
lean_dec_ref_known(v_e_2835_, 3);
lean_dec(v_offset_2836_);
return v___x_2879_;
}
}
case 7:
{
lean_object* v_binderName_2913_; lean_object* v_binderType_2914_; lean_object* v_body_2915_; uint8_t v_binderInfo_2916_; lean_object* v___x_2917_; 
v_binderName_2913_ = lean_ctor_get(v_e_2835_, 0);
v_binderType_2914_ = lean_ctor_get(v_e_2835_, 1);
v_body_2915_ = lean_ctor_get(v_e_2835_, 2);
v_binderInfo_2916_ = lean_ctor_get_uint8(v_e_2835_, sizeof(void*)*3 + 8);
lean_inc(v_offset_2836_);
lean_inc_ref(v_binderType_2914_);
v___x_2917_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2833_, v_i_2834_, v_binderType_2914_, v_offset_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_);
if (lean_obj_tag(v___x_2917_) == 0)
{
lean_object* v_a_2918_; lean_object* v_a_2919_; lean_object* v_fst_2920_; lean_object* v_snd_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; 
v_a_2918_ = lean_ctor_get(v___x_2917_, 0);
lean_inc(v_a_2918_);
v_a_2919_ = lean_ctor_get(v___x_2917_, 1);
lean_inc(v_a_2919_);
lean_dec_ref_known(v___x_2917_, 2);
v_fst_2920_ = lean_ctor_get(v_a_2918_, 0);
lean_inc(v_fst_2920_);
v_snd_2921_ = lean_ctor_get(v_a_2918_, 1);
lean_inc(v_snd_2921_);
lean_dec(v_a_2918_);
v___x_2922_ = lean_unsigned_to_nat(1u);
v___x_2923_ = lean_nat_add(v_offset_2836_, v___x_2922_);
lean_dec(v_offset_2836_);
lean_inc_ref(v_body_2915_);
v___x_2924_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2833_, v_i_2834_, v_body_2915_, v___x_2923_, v_snd_2921_, v_a_2838_, v_a_2839_, v_a_2919_);
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_object* v_a_2925_; lean_object* v_a_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2950_; 
v_a_2925_ = lean_ctor_get(v___x_2924_, 0);
v_a_2926_ = lean_ctor_get(v___x_2924_, 1);
v_isSharedCheck_2950_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2928_ = v___x_2924_;
v_isShared_2929_ = v_isSharedCheck_2950_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_a_2926_);
lean_inc(v_a_2925_);
lean_dec(v___x_2924_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2950_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v_fst_2930_; lean_object* v_snd_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2949_; 
v_fst_2930_ = lean_ctor_get(v_a_2925_, 0);
v_snd_2931_ = lean_ctor_get(v_a_2925_, 1);
v_isSharedCheck_2949_ = !lean_is_exclusive(v_a_2925_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2933_ = v_a_2925_;
v_isShared_2934_ = v_isSharedCheck_2949_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_snd_2931_);
lean_inc(v_fst_2930_);
lean_dec(v_a_2925_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2949_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
size_t v___x_2935_; size_t v___x_2936_; uint8_t v___x_2937_; 
v___x_2935_ = lean_ptr_addr(v_binderType_2914_);
v___x_2936_ = lean_ptr_addr(v_fst_2920_);
v___x_2937_ = lean_usize_dec_eq(v___x_2935_, v___x_2936_);
if (v___x_2937_ == 0)
{
lean_object* v___x_2938_; 
lean_inc(v_binderName_2913_);
lean_del_object(v___x_2933_);
lean_del_object(v___x_2928_);
lean_dec_ref_known(v_e_2835_, 3);
v___x_2938_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__3(v_binderName_2913_, v_binderInfo_2916_, v_fst_2920_, v_fst_2930_, v_snd_2931_, v_a_2838_, v_a_2839_, v_a_2926_);
return v___x_2938_;
}
else
{
size_t v___x_2939_; size_t v___x_2940_; uint8_t v___x_2941_; 
v___x_2939_ = lean_ptr_addr(v_body_2915_);
v___x_2940_ = lean_ptr_addr(v_fst_2930_);
v___x_2941_ = lean_usize_dec_eq(v___x_2939_, v___x_2940_);
if (v___x_2941_ == 0)
{
lean_object* v___x_2942_; 
lean_inc(v_binderName_2913_);
lean_del_object(v___x_2933_);
lean_del_object(v___x_2928_);
lean_dec_ref_known(v_e_2835_, 3);
v___x_2942_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__3(v_binderName_2913_, v_binderInfo_2916_, v_fst_2920_, v_fst_2930_, v_snd_2931_, v_a_2838_, v_a_2839_, v_a_2926_);
return v___x_2942_;
}
else
{
lean_object* v___x_2944_; 
lean_dec(v_fst_2930_);
lean_dec(v_fst_2920_);
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 0, v_e_2835_);
v___x_2944_ = v___x_2933_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_e_2835_);
lean_ctor_set(v_reuseFailAlloc_2948_, 1, v_snd_2931_);
v___x_2944_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
lean_object* v___x_2946_; 
if (v_isShared_2929_ == 0)
{
lean_ctor_set(v___x_2928_, 0, v___x_2944_);
v___x_2946_ = v___x_2928_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v___x_2944_);
lean_ctor_set(v_reuseFailAlloc_2947_, 1, v_a_2926_);
v___x_2946_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
return v___x_2946_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_2920_);
lean_dec_ref_known(v_e_2835_, 3);
return v___x_2924_;
}
}
else
{
lean_dec_ref_known(v_e_2835_, 3);
lean_dec(v_offset_2836_);
return v___x_2917_;
}
}
case 8:
{
lean_object* v_declName_2951_; lean_object* v_type_2952_; lean_object* v_value_2953_; lean_object* v_body_2954_; uint8_t v_nondep_2955_; lean_object* v___x_2956_; 
v_declName_2951_ = lean_ctor_get(v_e_2835_, 0);
v_type_2952_ = lean_ctor_get(v_e_2835_, 1);
v_value_2953_ = lean_ctor_get(v_e_2835_, 2);
v_body_2954_ = lean_ctor_get(v_e_2835_, 3);
v_nondep_2955_ = lean_ctor_get_uint8(v_e_2835_, sizeof(void*)*4 + 8);
lean_inc(v_offset_2836_);
lean_inc_ref(v_type_2952_);
v___x_2956_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2833_, v_i_2834_, v_type_2952_, v_offset_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v_a_2957_; lean_object* v_a_2958_; lean_object* v_fst_2959_; lean_object* v_snd_2960_; lean_object* v___x_2961_; 
v_a_2957_ = lean_ctor_get(v___x_2956_, 0);
lean_inc(v_a_2957_);
v_a_2958_ = lean_ctor_get(v___x_2956_, 1);
lean_inc(v_a_2958_);
lean_dec_ref_known(v___x_2956_, 2);
v_fst_2959_ = lean_ctor_get(v_a_2957_, 0);
lean_inc(v_fst_2959_);
v_snd_2960_ = lean_ctor_get(v_a_2957_, 1);
lean_inc(v_snd_2960_);
lean_dec(v_a_2957_);
lean_inc(v_offset_2836_);
lean_inc_ref(v_value_2953_);
v___x_2961_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2833_, v_i_2834_, v_value_2953_, v_offset_2836_, v_snd_2960_, v_a_2838_, v_a_2839_, v_a_2958_);
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_object* v_a_2962_; lean_object* v_a_2963_; lean_object* v_fst_2964_; lean_object* v_snd_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
v_a_2962_ = lean_ctor_get(v___x_2961_, 0);
lean_inc(v_a_2962_);
v_a_2963_ = lean_ctor_get(v___x_2961_, 1);
lean_inc(v_a_2963_);
lean_dec_ref_known(v___x_2961_, 2);
v_fst_2964_ = lean_ctor_get(v_a_2962_, 0);
lean_inc(v_fst_2964_);
v_snd_2965_ = lean_ctor_get(v_a_2962_, 1);
lean_inc(v_snd_2965_);
lean_dec(v_a_2962_);
v___x_2966_ = lean_unsigned_to_nat(1u);
v___x_2967_ = lean_nat_add(v_offset_2836_, v___x_2966_);
lean_dec(v_offset_2836_);
lean_inc_ref(v_body_2954_);
v___x_2968_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2833_, v_i_2834_, v_body_2954_, v___x_2967_, v_snd_2965_, v_a_2838_, v_a_2839_, v_a_2963_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v_a_2969_; lean_object* v_a_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2998_; 
v_a_2969_ = lean_ctor_get(v___x_2968_, 0);
v_a_2970_ = lean_ctor_get(v___x_2968_, 1);
v_isSharedCheck_2998_ = !lean_is_exclusive(v___x_2968_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2972_ = v___x_2968_;
v_isShared_2973_ = v_isSharedCheck_2998_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_a_2970_);
lean_inc(v_a_2969_);
lean_dec(v___x_2968_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2998_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v_fst_2974_; lean_object* v_snd_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2997_; 
v_fst_2974_ = lean_ctor_get(v_a_2969_, 0);
v_snd_2975_ = lean_ctor_get(v_a_2969_, 1);
v_isSharedCheck_2997_ = !lean_is_exclusive(v_a_2969_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2977_ = v_a_2969_;
v_isShared_2978_ = v_isSharedCheck_2997_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_snd_2975_);
lean_inc(v_fst_2974_);
lean_dec(v_a_2969_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2997_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
size_t v___x_2979_; size_t v___x_2980_; uint8_t v___x_2981_; 
v___x_2979_ = lean_ptr_addr(v_type_2952_);
v___x_2980_ = lean_ptr_addr(v_fst_2959_);
v___x_2981_ = lean_usize_dec_eq(v___x_2979_, v___x_2980_);
if (v___x_2981_ == 0)
{
lean_object* v___x_2982_; 
lean_inc(v_declName_2951_);
lean_del_object(v___x_2977_);
lean_del_object(v___x_2972_);
lean_dec_ref_known(v_e_2835_, 4);
v___x_2982_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4(v_declName_2951_, v_fst_2959_, v_fst_2964_, v_fst_2974_, v_nondep_2955_, v_snd_2975_, v_a_2838_, v_a_2839_, v_a_2970_);
return v___x_2982_;
}
else
{
size_t v___x_2983_; size_t v___x_2984_; uint8_t v___x_2985_; 
v___x_2983_ = lean_ptr_addr(v_value_2953_);
v___x_2984_ = lean_ptr_addr(v_fst_2964_);
v___x_2985_ = lean_usize_dec_eq(v___x_2983_, v___x_2984_);
if (v___x_2985_ == 0)
{
lean_object* v___x_2986_; 
lean_inc(v_declName_2951_);
lean_del_object(v___x_2977_);
lean_del_object(v___x_2972_);
lean_dec_ref_known(v_e_2835_, 4);
v___x_2986_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4(v_declName_2951_, v_fst_2959_, v_fst_2964_, v_fst_2974_, v_nondep_2955_, v_snd_2975_, v_a_2838_, v_a_2839_, v_a_2970_);
return v___x_2986_;
}
else
{
size_t v___x_2987_; size_t v___x_2988_; uint8_t v___x_2989_; 
v___x_2987_ = lean_ptr_addr(v_body_2954_);
v___x_2988_ = lean_ptr_addr(v_fst_2974_);
v___x_2989_ = lean_usize_dec_eq(v___x_2987_, v___x_2988_);
if (v___x_2989_ == 0)
{
lean_object* v___x_2990_; 
lean_inc(v_declName_2951_);
lean_del_object(v___x_2977_);
lean_del_object(v___x_2972_);
lean_dec_ref_known(v_e_2835_, 4);
v___x_2990_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__4(v_declName_2951_, v_fst_2959_, v_fst_2964_, v_fst_2974_, v_nondep_2955_, v_snd_2975_, v_a_2838_, v_a_2839_, v_a_2970_);
return v___x_2990_;
}
else
{
lean_object* v___x_2992_; 
lean_dec(v_fst_2974_);
lean_dec(v_fst_2964_);
lean_dec(v_fst_2959_);
if (v_isShared_2978_ == 0)
{
lean_ctor_set(v___x_2977_, 0, v_e_2835_);
v___x_2992_ = v___x_2977_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_e_2835_);
lean_ctor_set(v_reuseFailAlloc_2996_, 1, v_snd_2975_);
v___x_2992_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
lean_object* v___x_2994_; 
if (v_isShared_2973_ == 0)
{
lean_ctor_set(v___x_2972_, 0, v___x_2992_);
v___x_2994_ = v___x_2972_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v___x_2992_);
lean_ctor_set(v_reuseFailAlloc_2995_, 1, v_a_2970_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
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
lean_dec(v_fst_2964_);
lean_dec(v_fst_2959_);
lean_dec_ref_known(v_e_2835_, 4);
return v___x_2968_;
}
}
else
{
lean_dec(v_fst_2959_);
lean_dec_ref_known(v_e_2835_, 4);
lean_dec(v_offset_2836_);
return v___x_2961_;
}
}
else
{
lean_dec_ref_known(v_e_2835_, 4);
lean_dec(v_offset_2836_);
return v___x_2956_;
}
}
case 10:
{
lean_object* v_data_2999_; lean_object* v_expr_3000_; lean_object* v___x_3001_; 
v_data_2999_ = lean_ctor_get(v_e_2835_, 0);
v_expr_3000_ = lean_ctor_get(v_e_2835_, 1);
lean_inc_ref(v_expr_3000_);
v___x_3001_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2833_, v_i_2834_, v_expr_3000_, v_offset_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_);
if (lean_obj_tag(v___x_3001_) == 0)
{
lean_object* v_a_3002_; lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3023_; 
v_a_3002_ = lean_ctor_get(v___x_3001_, 0);
v_a_3003_ = lean_ctor_get(v___x_3001_, 1);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_3005_ = v___x_3001_;
v_isShared_3006_ = v_isSharedCheck_3023_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_inc(v_a_3002_);
lean_dec(v___x_3001_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3023_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v_fst_3007_; lean_object* v_snd_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3022_; 
v_fst_3007_ = lean_ctor_get(v_a_3002_, 0);
v_snd_3008_ = lean_ctor_get(v_a_3002_, 1);
v_isSharedCheck_3022_ = !lean_is_exclusive(v_a_3002_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3010_ = v_a_3002_;
v_isShared_3011_ = v_isSharedCheck_3022_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_snd_3008_);
lean_inc(v_fst_3007_);
lean_dec(v_a_3002_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3022_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
size_t v___x_3012_; size_t v___x_3013_; uint8_t v___x_3014_; 
v___x_3012_ = lean_ptr_addr(v_expr_3000_);
v___x_3013_ = lean_ptr_addr(v_fst_3007_);
v___x_3014_ = lean_usize_dec_eq(v___x_3012_, v___x_3013_);
if (v___x_3014_ == 0)
{
lean_object* v___x_3015_; 
lean_inc(v_data_2999_);
lean_del_object(v___x_3010_);
lean_del_object(v___x_3005_);
lean_dec_ref_known(v_e_2835_, 2);
v___x_3015_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__5(v_data_2999_, v_fst_3007_, v_snd_3008_, v_a_2838_, v_a_2839_, v_a_3003_);
return v___x_3015_;
}
else
{
lean_object* v___x_3017_; 
lean_dec(v_fst_3007_);
if (v_isShared_3011_ == 0)
{
lean_ctor_set(v___x_3010_, 0, v_e_2835_);
v___x_3017_ = v___x_3010_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_e_2835_);
lean_ctor_set(v_reuseFailAlloc_3021_, 1, v_snd_3008_);
v___x_3017_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
lean_object* v___x_3019_; 
if (v_isShared_3006_ == 0)
{
lean_ctor_set(v___x_3005_, 0, v___x_3017_);
v___x_3019_ = v___x_3005_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v___x_3017_);
lean_ctor_set(v_reuseFailAlloc_3020_, 1, v_a_3003_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2835_, 2);
return v___x_3001_;
}
}
case 11:
{
lean_object* v_typeName_3024_; lean_object* v_idx_3025_; lean_object* v_struct_3026_; lean_object* v___x_3027_; 
v_typeName_3024_ = lean_ctor_get(v_e_2835_, 0);
v_idx_3025_ = lean_ctor_get(v_e_2835_, 1);
v_struct_3026_ = lean_ctor_get(v_e_2835_, 2);
lean_inc_ref(v_struct_3026_);
v___x_3027_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_2833_, v_i_2834_, v_struct_3026_, v_offset_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_);
if (lean_obj_tag(v___x_3027_) == 0)
{
lean_object* v_a_3028_; lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3049_; 
v_a_3028_ = lean_ctor_get(v___x_3027_, 0);
v_a_3029_ = lean_ctor_get(v___x_3027_, 1);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_3027_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3031_ = v___x_3027_;
v_isShared_3032_ = v_isSharedCheck_3049_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_inc(v_a_3028_);
lean_dec(v___x_3027_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3049_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v_fst_3033_; lean_object* v_snd_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3048_; 
v_fst_3033_ = lean_ctor_get(v_a_3028_, 0);
v_snd_3034_ = lean_ctor_get(v_a_3028_, 1);
v_isSharedCheck_3048_ = !lean_is_exclusive(v_a_3028_);
if (v_isSharedCheck_3048_ == 0)
{
v___x_3036_ = v_a_3028_;
v_isShared_3037_ = v_isSharedCheck_3048_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_snd_3034_);
lean_inc(v_fst_3033_);
lean_dec(v_a_3028_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3048_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
size_t v___x_3038_; size_t v___x_3039_; uint8_t v___x_3040_; 
v___x_3038_ = lean_ptr_addr(v_struct_3026_);
v___x_3039_ = lean_ptr_addr(v_fst_3033_);
v___x_3040_ = lean_usize_dec_eq(v___x_3038_, v___x_3039_);
if (v___x_3040_ == 0)
{
lean_object* v___x_3041_; 
lean_inc(v_idx_3025_);
lean_inc(v_typeName_3024_);
lean_del_object(v___x_3036_);
lean_del_object(v___x_3031_);
lean_dec_ref_known(v_e_2835_, 3);
v___x_3041_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__6(v_typeName_3024_, v_idx_3025_, v_fst_3033_, v_snd_3034_, v_a_2838_, v_a_2839_, v_a_3029_);
return v___x_3041_;
}
else
{
lean_object* v___x_3043_; 
lean_dec(v_fst_3033_);
if (v_isShared_3037_ == 0)
{
lean_ctor_set(v___x_3036_, 0, v_e_2835_);
v___x_3043_ = v___x_3036_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_e_2835_);
lean_ctor_set(v_reuseFailAlloc_3047_, 1, v_snd_3034_);
v___x_3043_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
lean_object* v___x_3045_; 
if (v_isShared_3032_ == 0)
{
lean_ctor_set(v___x_3031_, 0, v___x_3043_);
v___x_3045_ = v___x_3031_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v___x_3043_);
lean_ctor_set(v_reuseFailAlloc_3046_, 1, v_a_3029_);
v___x_3045_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
return v___x_3045_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2835_, 3);
return v___x_3027_;
}
}
default: 
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
lean_dec(v_offset_2836_);
lean_dec_ref(v_e_2835_);
v___x_3050_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0___closed__3);
v___x_3051_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__7(v___x_3050_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_);
return v___x_3051_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(lean_object* v___x_3052_, lean_object* v_i_3053_, lean_object* v_e_3054_, lean_object* v_offset_3055_, lean_object* v_a_3056_, uint8_t v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_){
_start:
{
lean_object* v_key_3060_; lean_object* v_a_3062_; lean_object* v___x_3075_; 
lean_inc(v_offset_3055_);
lean_inc_ref(v_e_3054_);
v_key_3060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_3060_, 0, v_e_3054_);
lean_ctor_set(v_key_3060_, 1, v_offset_3055_);
v___x_3075_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__0_spec__0_spec__2___redArg(v_a_3056_, v_key_3060_);
if (lean_obj_tag(v___x_3075_) == 1)
{
lean_object* v_val_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
lean_dec_ref_known(v_key_3060_, 2);
lean_dec(v_offset_3055_);
lean_dec_ref(v_e_3054_);
v_val_3076_ = lean_ctor_get(v___x_3075_, 0);
lean_inc(v_val_3076_);
lean_dec_ref_known(v___x_3075_, 1);
v___x_3077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3077_, 0, v_val_3076_);
lean_ctor_set(v___x_3077_, 1, v_a_3056_);
v___x_3078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3077_);
lean_ctor_set(v___x_3078_, 1, v_a_3059_);
return v___x_3078_;
}
else
{
lean_dec(v___x_3075_);
switch(lean_obj_tag(v_e_3054_))
{
case 1:
{
lean_object* v_fvarId_3079_; lean_object* v___x_3080_; 
v_fvarId_3079_ = lean_ctor_get(v_e_3054_, 0);
v___x_3080_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___redArg(v___x_3052_, v_fvarId_3079_);
if (lean_obj_tag(v___x_3080_) == 1)
{
lean_object* v_val_3081_; uint8_t v___x_3082_; 
v_val_3081_ = lean_ctor_get(v___x_3080_, 0);
lean_inc(v_val_3081_);
lean_dec_ref_known(v___x_3080_, 1);
v___x_3082_ = lean_nat_dec_lt(v_val_3081_, v_i_3053_);
if (v___x_3082_ == 0)
{
lean_object* v___x_3083_; lean_object* v___x_3084_; 
lean_dec(v_val_3081_);
v___x_3083_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2);
v___x_3084_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3(v___x_3083_, v_a_3057_, v_a_3058_, v_a_3059_);
if (lean_obj_tag(v___x_3084_) == 0)
{
lean_object* v_a_3085_; 
v_a_3085_ = lean_ctor_get(v___x_3084_, 0);
if (lean_obj_tag(v_a_3085_) == 1)
{
lean_object* v_a_3086_; lean_object* v_val_3087_; lean_object* v___x_3088_; 
lean_inc_ref(v_a_3085_);
lean_dec_ref_known(v_e_3054_, 1);
lean_dec(v_offset_3055_);
v_a_3086_ = lean_ctor_get(v___x_3084_, 1);
lean_inc(v_a_3086_);
lean_dec_ref_known(v___x_3084_, 2);
v_val_3087_ = lean_ctor_get(v_a_3085_, 0);
lean_inc(v_val_3087_);
lean_dec_ref_known(v_a_3085_, 1);
v___x_3088_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3060_, v_val_3087_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3086_);
return v___x_3088_;
}
else
{
lean_object* v_a_3089_; 
v_a_3089_ = lean_ctor_get(v___x_3084_, 1);
lean_inc(v_a_3089_);
lean_dec_ref_known(v___x_3084_, 2);
v_a_3062_ = v_a_3089_;
goto v___jp_3061_;
}
}
else
{
lean_object* v_a_3090_; lean_object* v_a_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3098_; 
lean_dec_ref_known(v_e_3054_, 1);
lean_dec_ref_known(v_key_3060_, 2);
lean_dec_ref(v_a_3056_);
lean_dec(v_offset_3055_);
v_a_3090_ = lean_ctor_get(v___x_3084_, 0);
v_a_3091_ = lean_ctor_get(v___x_3084_, 1);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3093_ = v___x_3084_;
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_a_3091_);
lean_inc(v_a_3090_);
lean_dec(v___x_3084_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3096_; 
if (v_isShared_3094_ == 0)
{
v___x_3096_ = v___x_3093_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_a_3090_);
lean_ctor_set(v_reuseFailAlloc_3097_, 1, v_a_3091_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
}
else
{
lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
lean_dec_ref_known(v_e_3054_, 1);
v___x_3099_ = lean_nat_add(v_offset_3055_, v_i_3053_);
lean_dec(v_offset_3055_);
v___x_3100_ = lean_nat_sub(v___x_3099_, v_val_3081_);
lean_dec(v_val_3081_);
lean_dec(v___x_3099_);
v___x_3101_ = lean_unsigned_to_nat(1u);
v___x_3102_ = lean_nat_sub(v___x_3100_, v___x_3101_);
lean_dec(v___x_3100_);
v___x_3103_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4___redArg(v___x_3102_, v_a_3059_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_object* v_a_3104_; lean_object* v_a_3105_; lean_object* v___x_3106_; 
v_a_3104_ = lean_ctor_get(v___x_3103_, 0);
lean_inc(v_a_3104_);
v_a_3105_ = lean_ctor_get(v___x_3103_, 1);
lean_inc(v_a_3105_);
lean_dec_ref_known(v___x_3103_, 2);
v___x_3106_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3060_, v_a_3104_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3105_);
return v___x_3106_;
}
else
{
lean_object* v_a_3107_; lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3115_; 
lean_dec_ref_known(v_key_3060_, 2);
lean_dec_ref(v_a_3056_);
v_a_3107_ = lean_ctor_get(v___x_3103_, 0);
v_a_3108_ = lean_ctor_get(v___x_3103_, 1);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3110_ = v___x_3103_;
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_inc(v_a_3107_);
lean_dec(v___x_3103_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3113_; 
if (v_isShared_3111_ == 0)
{
v___x_3113_ = v___x_3110_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_a_3107_);
lean_ctor_set(v_reuseFailAlloc_3114_, 1, v_a_3108_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
}
}
else
{
lean_object* v___x_3116_; 
lean_dec(v___x_3080_);
lean_dec(v_offset_3055_);
v___x_3116_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3060_, v_e_3054_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3059_);
return v___x_3116_;
}
}
case 9:
{
lean_object* v___x_3117_; 
lean_dec(v_offset_3055_);
v___x_3117_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3060_, v_e_3054_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3059_);
return v___x_3117_;
}
case 2:
{
lean_object* v___x_3118_; 
lean_dec(v_offset_3055_);
v___x_3118_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3060_, v_e_3054_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3059_);
return v___x_3118_;
}
case 0:
{
lean_object* v___x_3119_; 
lean_dec(v_offset_3055_);
v___x_3119_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3060_, v_e_3054_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3059_);
return v___x_3119_;
}
case 4:
{
lean_object* v___x_3120_; 
lean_dec(v_offset_3055_);
v___x_3120_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3060_, v_e_3054_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3059_);
return v___x_3120_;
}
case 3:
{
lean_object* v___x_3121_; 
lean_dec(v_offset_3055_);
v___x_3121_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3060_, v_e_3054_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3059_);
return v___x_3121_;
}
default: 
{
uint8_t v___x_3122_; 
v___x_3122_ = l_Lean_Expr_hasFVar(v_e_3054_);
if (v___x_3122_ == 0)
{
lean_object* v___x_3123_; 
lean_dec(v_offset_3055_);
v___x_3123_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3060_, v_e_3054_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3059_);
return v___x_3123_;
}
else
{
v_a_3062_ = v_a_3059_;
goto v___jp_3061_;
}
}
}
}
v___jp_3061_:
{
switch(lean_obj_tag(v_e_3054_))
{
case 9:
{
lean_object* v___x_3063_; 
lean_dec(v_offset_3055_);
v___x_3063_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3060_, v_e_3054_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3062_);
return v___x_3063_;
}
case 2:
{
lean_object* v___x_3064_; 
lean_dec(v_offset_3055_);
v___x_3064_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3060_, v_e_3054_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3062_);
return v___x_3064_;
}
case 0:
{
lean_object* v___x_3065_; 
lean_dec(v_offset_3055_);
v___x_3065_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3060_, v_e_3054_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3062_);
return v___x_3065_;
}
case 1:
{
lean_object* v___x_3066_; 
lean_dec(v_offset_3055_);
v___x_3066_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3060_, v_e_3054_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3062_);
return v___x_3066_;
}
case 4:
{
lean_object* v___x_3067_; 
lean_dec(v_offset_3055_);
v___x_3067_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3060_, v_e_3054_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3062_);
return v___x_3067_;
}
case 3:
{
lean_object* v___x_3068_; 
lean_dec(v_offset_3055_);
v___x_3068_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3060_, v_e_3054_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3062_);
return v___x_3068_;
}
default: 
{
lean_object* v___x_3069_; 
v___x_3069_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5(v___x_3052_, v_i_3053_, v_e_3054_, v_offset_3055_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3062_);
if (lean_obj_tag(v___x_3069_) == 0)
{
lean_object* v_a_3070_; lean_object* v_a_3071_; lean_object* v_fst_3072_; lean_object* v_snd_3073_; lean_object* v___x_3074_; 
v_a_3070_ = lean_ctor_get(v___x_3069_, 0);
lean_inc(v_a_3070_);
v_a_3071_ = lean_ctor_get(v___x_3069_, 1);
lean_inc(v_a_3071_);
lean_dec_ref_known(v___x_3069_, 2);
v_fst_3072_ = lean_ctor_get(v_a_3070_, 0);
lean_inc(v_fst_3072_);
v_snd_3073_ = lean_ctor_get(v_a_3070_, 1);
lean_inc(v_snd_3073_);
lean_dec(v_a_3070_);
v___x_3074_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_3060_, v_fst_3072_, v_snd_3073_, v_a_3057_, v_a_3058_, v_a_3071_);
return v___x_3074_;
}
else
{
lean_dec_ref_known(v_key_3060_, 2);
return v___x_3069_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___boxed(lean_object* v___x_3124_, lean_object* v_i_3125_, lean_object* v_e_3126_, lean_object* v_offset_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_){
_start:
{
uint8_t v_a_boxed_3132_; lean_object* v_res_3133_; 
v_a_boxed_3132_ = lean_unbox(v_a_3129_);
v_res_3133_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9(v___x_3124_, v_i_3125_, v_e_3126_, v_offset_3127_, v_a_3128_, v_a_boxed_3132_, v_a_3130_, v_a_3131_);
lean_dec_ref(v_a_3130_);
lean_dec(v_i_3125_);
lean_dec_ref(v___x_3124_);
return v_res_3133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5___boxed(lean_object* v___x_3134_, lean_object* v_i_3135_, lean_object* v_e_3136_, lean_object* v_offset_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_){
_start:
{
uint8_t v_a_boxed_3142_; lean_object* v_res_3143_; 
v_a_boxed_3142_ = lean_unbox(v_a_3139_);
v_res_3143_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5(v___x_3134_, v_i_3135_, v_e_3136_, v_offset_3137_, v_a_3138_, v_a_boxed_3142_, v_a_3140_, v_a_3141_);
lean_dec_ref(v_a_3140_);
lean_dec(v_i_3135_);
lean_dec_ref(v___x_3134_);
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___lam__0(lean_object* v_e_3144_, lean_object* v___x_3145_, lean_object* v___x_3146_, lean_object* v_fst_3147_, lean_object* v___x_3148_, uint8_t v_debug_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_){
_start:
{
lean_object* v_a_3153_; 
switch(lean_obj_tag(v_e_3144_))
{
case 1:
{
lean_object* v_fvarId_3183_; lean_object* v___x_3184_; 
v_fvarId_3183_ = lean_ctor_get(v_e_3144_, 0);
v___x_3184_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___redArg(v_fst_3147_, v_fvarId_3183_);
if (lean_obj_tag(v___x_3184_) == 1)
{
lean_object* v_val_3185_; uint8_t v___x_3186_; 
v_val_3185_ = lean_ctor_get(v___x_3184_, 0);
lean_inc(v_val_3185_);
lean_dec_ref_known(v___x_3184_, 1);
v___x_3186_ = lean_nat_dec_lt(v_val_3185_, v___x_3148_);
if (v___x_3186_ == 0)
{
lean_object* v___x_3187_; lean_object* v___x_3188_; 
lean_dec(v_val_3185_);
v___x_3187_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2);
v___x_3188_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3(v___x_3187_, v_debug_3149_, v___y_3150_, v___y_3151_);
if (lean_obj_tag(v___x_3188_) == 0)
{
lean_object* v_a_3189_; 
v_a_3189_ = lean_ctor_get(v___x_3188_, 0);
if (lean_obj_tag(v_a_3189_) == 1)
{
lean_object* v_a_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3198_; 
lean_inc_ref(v_a_3189_);
lean_dec_ref_known(v_e_3144_, 1);
lean_dec(v___x_3146_);
lean_dec(v___x_3145_);
v_a_3190_ = lean_ctor_get(v___x_3188_, 1);
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_3188_);
if (v_isSharedCheck_3198_ == 0)
{
lean_object* v_unused_3199_; 
v_unused_3199_ = lean_ctor_get(v___x_3188_, 0);
lean_dec(v_unused_3199_);
v___x_3192_ = v___x_3188_;
v_isShared_3193_ = v_isSharedCheck_3198_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_a_3190_);
lean_dec(v___x_3188_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3198_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v_val_3194_; lean_object* v___x_3196_; 
v_val_3194_ = lean_ctor_get(v_a_3189_, 0);
lean_inc(v_val_3194_);
lean_dec_ref_known(v_a_3189_, 1);
if (v_isShared_3193_ == 0)
{
lean_ctor_set(v___x_3192_, 0, v_val_3194_);
v___x_3196_ = v___x_3192_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_val_3194_);
lean_ctor_set(v_reuseFailAlloc_3197_, 1, v_a_3190_);
v___x_3196_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
return v___x_3196_;
}
}
}
else
{
lean_object* v_a_3200_; 
v_a_3200_ = lean_ctor_get(v___x_3188_, 1);
lean_inc(v_a_3200_);
lean_dec_ref_known(v___x_3188_, 2);
v_a_3153_ = v_a_3200_;
goto v___jp_3152_;
}
}
else
{
lean_object* v_a_3201_; lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3209_; 
lean_dec_ref_known(v_e_3144_, 1);
lean_dec(v___x_3146_);
lean_dec(v___x_3145_);
v_a_3201_ = lean_ctor_get(v___x_3188_, 0);
v_a_3202_ = lean_ctor_get(v___x_3188_, 1);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3188_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3204_ = v___x_3188_;
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_inc(v_a_3201_);
lean_dec(v___x_3188_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3207_; 
if (v_isShared_3205_ == 0)
{
v___x_3207_ = v___x_3204_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_a_3201_);
lean_ctor_set(v_reuseFailAlloc_3208_, 1, v_a_3202_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
}
}
else
{
lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
lean_dec_ref_known(v_e_3144_, 1);
lean_dec(v___x_3146_);
lean_dec(v___x_3145_);
v___x_3210_ = lean_nat_sub(v___x_3148_, v_val_3185_);
lean_dec(v_val_3185_);
v___x_3211_ = lean_unsigned_to_nat(1u);
v___x_3212_ = lean_nat_sub(v___x_3210_, v___x_3211_);
lean_dec(v___x_3210_);
v___x_3213_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4___redArg(v___x_3212_, v___y_3151_);
return v___x_3213_;
}
}
else
{
lean_object* v___x_3214_; 
lean_dec(v___x_3184_);
lean_dec(v___x_3146_);
lean_dec(v___x_3145_);
v___x_3214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3214_, 0, v_e_3144_);
lean_ctor_set(v___x_3214_, 1, v___y_3151_);
return v___x_3214_;
}
}
case 9:
{
lean_object* v___x_3215_; 
lean_dec(v___x_3146_);
lean_dec(v___x_3145_);
v___x_3215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3215_, 0, v_e_3144_);
lean_ctor_set(v___x_3215_, 1, v___y_3151_);
return v___x_3215_;
}
case 2:
{
lean_object* v___x_3216_; 
lean_dec(v___x_3146_);
lean_dec(v___x_3145_);
v___x_3216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3216_, 0, v_e_3144_);
lean_ctor_set(v___x_3216_, 1, v___y_3151_);
return v___x_3216_;
}
case 0:
{
lean_object* v___x_3217_; 
lean_dec(v___x_3146_);
lean_dec(v___x_3145_);
v___x_3217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3217_, 0, v_e_3144_);
lean_ctor_set(v___x_3217_, 1, v___y_3151_);
return v___x_3217_;
}
case 4:
{
lean_object* v___x_3218_; 
lean_dec(v___x_3146_);
lean_dec(v___x_3145_);
v___x_3218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3218_, 0, v_e_3144_);
lean_ctor_set(v___x_3218_, 1, v___y_3151_);
return v___x_3218_;
}
case 3:
{
lean_object* v___x_3219_; 
lean_dec(v___x_3146_);
lean_dec(v___x_3145_);
v___x_3219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3219_, 0, v_e_3144_);
lean_ctor_set(v___x_3219_, 1, v___y_3151_);
return v___x_3219_;
}
default: 
{
uint8_t v___x_3220_; 
v___x_3220_ = l_Lean_Expr_hasFVar(v_e_3144_);
if (v___x_3220_ == 0)
{
lean_object* v___x_3221_; 
lean_dec(v___x_3146_);
lean_dec(v___x_3145_);
v___x_3221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3221_, 0, v_e_3144_);
lean_ctor_set(v___x_3221_, 1, v___y_3151_);
return v___x_3221_;
}
else
{
v_a_3153_ = v___y_3151_;
goto v___jp_3152_;
}
}
}
v___jp_3152_:
{
switch(lean_obj_tag(v_e_3144_))
{
case 9:
{
lean_object* v___x_3154_; 
lean_dec(v___x_3146_);
lean_dec(v___x_3145_);
v___x_3154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3154_, 0, v_e_3144_);
lean_ctor_set(v___x_3154_, 1, v_a_3153_);
return v___x_3154_;
}
case 2:
{
lean_object* v___x_3155_; 
lean_dec(v___x_3146_);
lean_dec(v___x_3145_);
v___x_3155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3155_, 0, v_e_3144_);
lean_ctor_set(v___x_3155_, 1, v_a_3153_);
return v___x_3155_;
}
case 0:
{
lean_object* v___x_3156_; 
lean_dec(v___x_3146_);
lean_dec(v___x_3145_);
v___x_3156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3156_, 0, v_e_3144_);
lean_ctor_set(v___x_3156_, 1, v_a_3153_);
return v___x_3156_;
}
case 1:
{
lean_object* v___x_3157_; 
lean_dec(v___x_3146_);
lean_dec(v___x_3145_);
v___x_3157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3157_, 0, v_e_3144_);
lean_ctor_set(v___x_3157_, 1, v_a_3153_);
return v___x_3157_;
}
case 4:
{
lean_object* v___x_3158_; 
lean_dec(v___x_3146_);
lean_dec(v___x_3145_);
v___x_3158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3158_, 0, v_e_3144_);
lean_ctor_set(v___x_3158_, 1, v_a_3153_);
return v___x_3158_;
}
case 3:
{
lean_object* v___x_3159_; 
lean_dec(v___x_3146_);
lean_dec(v___x_3145_);
v___x_3159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3159_, 0, v_e_3144_);
lean_ctor_set(v___x_3159_, 1, v_a_3153_);
return v___x_3159_;
}
default: 
{
lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3160_ = lean_box(0);
v___x_3161_ = lean_mk_array(v___x_3145_, v___x_3160_);
lean_inc(v___x_3146_);
v___x_3162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3162_, 0, v___x_3146_);
lean_ctor_set(v___x_3162_, 1, v___x_3161_);
v___x_3163_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5(v_fst_3147_, v___x_3148_, v_e_3144_, v___x_3146_, v___x_3162_, v_debug_3149_, v___y_3150_, v_a_3153_);
if (lean_obj_tag(v___x_3163_) == 0)
{
lean_object* v_a_3164_; lean_object* v_a_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3173_; 
v_a_3164_ = lean_ctor_get(v___x_3163_, 0);
v_a_3165_ = lean_ctor_get(v___x_3163_, 1);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_3163_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3167_ = v___x_3163_;
v_isShared_3168_ = v_isSharedCheck_3173_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_a_3165_);
lean_inc(v_a_3164_);
lean_dec(v___x_3163_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3173_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v_fst_3169_; lean_object* v___x_3171_; 
v_fst_3169_ = lean_ctor_get(v_a_3164_, 0);
lean_inc(v_fst_3169_);
lean_dec(v_a_3164_);
if (v_isShared_3168_ == 0)
{
lean_ctor_set(v___x_3167_, 0, v_fst_3169_);
v___x_3171_ = v___x_3167_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_fst_3169_);
lean_ctor_set(v_reuseFailAlloc_3172_, 1, v_a_3165_);
v___x_3171_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
return v___x_3171_;
}
}
}
else
{
lean_object* v_a_3174_; lean_object* v_a_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3182_; 
v_a_3174_ = lean_ctor_get(v___x_3163_, 0);
v_a_3175_ = lean_ctor_get(v___x_3163_, 1);
v_isSharedCheck_3182_ = !lean_is_exclusive(v___x_3163_);
if (v_isSharedCheck_3182_ == 0)
{
v___x_3177_ = v___x_3163_;
v_isShared_3178_ = v_isSharedCheck_3182_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_a_3175_);
lean_inc(v_a_3174_);
lean_dec(v___x_3163_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3182_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
lean_object* v___x_3180_; 
if (v_isShared_3178_ == 0)
{
v___x_3180_ = v___x_3177_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v_a_3174_);
lean_ctor_set(v_reuseFailAlloc_3181_, 1, v_a_3175_);
v___x_3180_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
return v___x_3180_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___lam__0___boxed(lean_object* v_e_3222_, lean_object* v___x_3223_, lean_object* v___x_3224_, lean_object* v_fst_3225_, lean_object* v___x_3226_, lean_object* v_debug_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_){
_start:
{
uint8_t v_debug_boxed_3230_; lean_object* v_res_3231_; 
v_debug_boxed_3230_ = lean_unbox(v_debug_3227_);
v_res_3231_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___lam__0(v_e_3222_, v___x_3223_, v___x_3224_, v_fst_3225_, v___x_3226_, v_debug_boxed_3230_, v___y_3228_, v___y_3229_);
lean_dec_ref(v___y_3228_);
lean_dec(v___x_3226_);
lean_dec(v_fst_3225_);
return v_res_3231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__0(lean_object* v_piece_3232_, lean_object* v___x_3233_, lean_object* v___x_3234_, lean_object* v_i_3235_, uint8_t v_debug_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_){
_start:
{
lean_object* v_a_3240_; 
switch(lean_obj_tag(v_piece_3232_))
{
case 1:
{
lean_object* v_fvarId_3269_; lean_object* v___x_3270_; 
v_fvarId_3269_ = lean_ctor_get(v_piece_3232_, 0);
v___x_3270_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___redArg(v___x_3234_, v_fvarId_3269_);
if (lean_obj_tag(v___x_3270_) == 1)
{
lean_object* v_val_3271_; uint8_t v___x_3272_; 
v_val_3271_ = lean_ctor_get(v___x_3270_, 0);
lean_inc(v_val_3271_);
lean_dec_ref_known(v___x_3270_, 1);
v___x_3272_ = lean_nat_dec_lt(v_val_3271_, v_i_3235_);
if (v___x_3272_ == 0)
{
lean_object* v___x_3273_; lean_object* v___x_3274_; 
lean_dec(v_val_3271_);
v___x_3273_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5_spec__9___closed__2);
v___x_3274_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__3(v___x_3273_, v_debug_3236_, v___y_3237_, v___y_3238_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_a_3275_; 
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
if (lean_obj_tag(v_a_3275_) == 1)
{
lean_object* v_a_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3284_; 
lean_inc_ref(v_a_3275_);
lean_dec_ref_known(v_piece_3232_, 1);
lean_dec(v___x_3233_);
v_a_3276_ = lean_ctor_get(v___x_3274_, 1);
v_isSharedCheck_3284_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3284_ == 0)
{
lean_object* v_unused_3285_; 
v_unused_3285_ = lean_ctor_get(v___x_3274_, 0);
lean_dec(v_unused_3285_);
v___x_3278_ = v___x_3274_;
v_isShared_3279_ = v_isSharedCheck_3284_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_a_3276_);
lean_dec(v___x_3274_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3284_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v_val_3280_; lean_object* v___x_3282_; 
v_val_3280_ = lean_ctor_get(v_a_3275_, 0);
lean_inc(v_val_3280_);
lean_dec_ref_known(v_a_3275_, 1);
if (v_isShared_3279_ == 0)
{
lean_ctor_set(v___x_3278_, 0, v_val_3280_);
v___x_3282_ = v___x_3278_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v_val_3280_);
lean_ctor_set(v_reuseFailAlloc_3283_, 1, v_a_3276_);
v___x_3282_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
return v___x_3282_;
}
}
}
else
{
lean_object* v_a_3286_; 
v_a_3286_ = lean_ctor_get(v___x_3274_, 1);
lean_inc(v_a_3286_);
lean_dec_ref_known(v___x_3274_, 2);
v_a_3240_ = v_a_3286_;
goto v___jp_3239_;
}
}
else
{
lean_object* v_a_3287_; lean_object* v_a_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3295_; 
lean_dec_ref_known(v_piece_3232_, 1);
lean_dec(v___x_3233_);
v_a_3287_ = lean_ctor_get(v___x_3274_, 0);
v_a_3288_ = lean_ctor_get(v___x_3274_, 1);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3290_ = v___x_3274_;
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_a_3288_);
lean_inc(v_a_3287_);
lean_dec(v___x_3274_);
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
else
{
lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; 
lean_dec_ref_known(v_piece_3232_, 1);
lean_dec(v___x_3233_);
v___x_3296_ = lean_nat_sub(v_i_3235_, v_val_3271_);
lean_dec(v_val_3271_);
v___x_3297_ = lean_unsigned_to_nat(1u);
v___x_3298_ = lean_nat_sub(v___x_3296_, v___x_3297_);
lean_dec(v___x_3296_);
v___x_3299_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__4___redArg(v___x_3298_, v___y_3238_);
return v___x_3299_;
}
}
else
{
lean_object* v___x_3300_; 
lean_dec(v___x_3270_);
lean_dec(v___x_3233_);
v___x_3300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3300_, 0, v_piece_3232_);
lean_ctor_set(v___x_3300_, 1, v___y_3238_);
return v___x_3300_;
}
}
case 9:
{
lean_object* v___x_3301_; 
lean_dec(v___x_3233_);
v___x_3301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3301_, 0, v_piece_3232_);
lean_ctor_set(v___x_3301_, 1, v___y_3238_);
return v___x_3301_;
}
case 2:
{
lean_object* v___x_3302_; 
lean_dec(v___x_3233_);
v___x_3302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3302_, 0, v_piece_3232_);
lean_ctor_set(v___x_3302_, 1, v___y_3238_);
return v___x_3302_;
}
case 0:
{
lean_object* v___x_3303_; 
lean_dec(v___x_3233_);
v___x_3303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3303_, 0, v_piece_3232_);
lean_ctor_set(v___x_3303_, 1, v___y_3238_);
return v___x_3303_;
}
case 4:
{
lean_object* v___x_3304_; 
lean_dec(v___x_3233_);
v___x_3304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3304_, 0, v_piece_3232_);
lean_ctor_set(v___x_3304_, 1, v___y_3238_);
return v___x_3304_;
}
case 3:
{
lean_object* v___x_3305_; 
lean_dec(v___x_3233_);
v___x_3305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3305_, 0, v_piece_3232_);
lean_ctor_set(v___x_3305_, 1, v___y_3238_);
return v___x_3305_;
}
default: 
{
uint8_t v___x_3306_; 
v___x_3306_ = l_Lean_Expr_hasFVar(v_piece_3232_);
if (v___x_3306_ == 0)
{
lean_object* v___x_3307_; 
lean_dec(v___x_3233_);
v___x_3307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3307_, 0, v_piece_3232_);
lean_ctor_set(v___x_3307_, 1, v___y_3238_);
return v___x_3307_;
}
else
{
v_a_3240_ = v___y_3238_;
goto v___jp_3239_;
}
}
}
v___jp_3239_:
{
switch(lean_obj_tag(v_piece_3232_))
{
case 9:
{
lean_object* v___x_3241_; 
lean_dec(v___x_3233_);
v___x_3241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3241_, 0, v_piece_3232_);
lean_ctor_set(v___x_3241_, 1, v_a_3240_);
return v___x_3241_;
}
case 2:
{
lean_object* v___x_3242_; 
lean_dec(v___x_3233_);
v___x_3242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3242_, 0, v_piece_3232_);
lean_ctor_set(v___x_3242_, 1, v_a_3240_);
return v___x_3242_;
}
case 0:
{
lean_object* v___x_3243_; 
lean_dec(v___x_3233_);
v___x_3243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3243_, 0, v_piece_3232_);
lean_ctor_set(v___x_3243_, 1, v_a_3240_);
return v___x_3243_;
}
case 1:
{
lean_object* v___x_3244_; 
lean_dec(v___x_3233_);
v___x_3244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3244_, 0, v_piece_3232_);
lean_ctor_set(v___x_3244_, 1, v_a_3240_);
return v___x_3244_;
}
case 4:
{
lean_object* v___x_3245_; 
lean_dec(v___x_3233_);
v___x_3245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3245_, 0, v_piece_3232_);
lean_ctor_set(v___x_3245_, 1, v_a_3240_);
return v___x_3245_;
}
case 3:
{
lean_object* v___x_3246_; 
lean_dec(v___x_3233_);
v___x_3246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3246_, 0, v_piece_3232_);
lean_ctor_set(v___x_3246_, 1, v_a_3240_);
return v___x_3246_;
}
default: 
{
lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; 
v___x_3247_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__0, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__0_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___lam__0___closed__0);
lean_inc(v___x_3233_);
v___x_3248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3248_, 0, v___x_3233_);
lean_ctor_set(v___x_3248_, 1, v___x_3247_);
v___x_3249_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__5(v___x_3234_, v_i_3235_, v_piece_3232_, v___x_3233_, v___x_3248_, v_debug_3236_, v___y_3237_, v_a_3240_);
if (lean_obj_tag(v___x_3249_) == 0)
{
lean_object* v_a_3250_; lean_object* v_a_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3259_; 
v_a_3250_ = lean_ctor_get(v___x_3249_, 0);
v_a_3251_ = lean_ctor_get(v___x_3249_, 1);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3249_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3253_ = v___x_3249_;
v_isShared_3254_ = v_isSharedCheck_3259_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_a_3251_);
lean_inc(v_a_3250_);
lean_dec(v___x_3249_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3259_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v_fst_3255_; lean_object* v___x_3257_; 
v_fst_3255_ = lean_ctor_get(v_a_3250_, 0);
lean_inc(v_fst_3255_);
lean_dec(v_a_3250_);
if (v_isShared_3254_ == 0)
{
lean_ctor_set(v___x_3253_, 0, v_fst_3255_);
v___x_3257_ = v___x_3253_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v_fst_3255_);
lean_ctor_set(v_reuseFailAlloc_3258_, 1, v_a_3251_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
}
else
{
lean_object* v_a_3260_; lean_object* v_a_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3268_; 
v_a_3260_ = lean_ctor_get(v___x_3249_, 0);
v_a_3261_ = lean_ctor_get(v___x_3249_, 1);
v_isSharedCheck_3268_ = !lean_is_exclusive(v___x_3249_);
if (v_isSharedCheck_3268_ == 0)
{
v___x_3263_ = v___x_3249_;
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_a_3261_);
lean_inc(v_a_3260_);
lean_dec(v___x_3249_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
lean_object* v___x_3266_; 
if (v_isShared_3264_ == 0)
{
v___x_3266_ = v___x_3263_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v_a_3260_);
lean_ctor_set(v_reuseFailAlloc_3267_, 1, v_a_3261_);
v___x_3266_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
return v___x_3266_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__0___boxed(lean_object* v_piece_3308_, lean_object* v___x_3309_, lean_object* v___x_3310_, lean_object* v_i_3311_, lean_object* v_debug_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_){
_start:
{
uint8_t v_debug_boxed_3315_; lean_object* v_res_3316_; 
v_debug_boxed_3315_ = lean_unbox(v_debug_3312_);
v_res_3316_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__0(v_piece_3308_, v___x_3309_, v___x_3310_, v_i_3311_, v_debug_boxed_3315_, v___y_3313_, v___y_3314_);
lean_dec_ref(v___y_3313_);
lean_dec(v_i_3311_);
lean_dec_ref(v___x_3310_);
return v_res_3316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__1(lean_object* v___x_3317_, lean_object* v___x_3318_, uint8_t v___x_3319_, lean_object* v_piece_3320_, lean_object* v_i_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
lean_object* v___x_3330_; uint8_t v_debug_3331_; lean_object* v___x_3332_; lean_object* v___f_3333_; lean_object* v___x_3334_; lean_object* v_env_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; 
v___x_3330_ = lean_st_ref_get(v___y_3324_);
v_debug_3331_ = lean_ctor_get_uint8(v___x_3330_, sizeof(void*)*12);
lean_dec(v___x_3330_);
v___x_3332_ = lean_box(v_debug_3331_);
v___f_3333_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__0___boxed), 7, 5);
lean_closure_set(v___f_3333_, 0, v_piece_3320_);
lean_closure_set(v___f_3333_, 1, v___x_3317_);
lean_closure_set(v___f_3333_, 2, v___x_3318_);
lean_closure_set(v___f_3333_, 3, v_i_3321_);
lean_closure_set(v___f_3333_, 4, v___x_3332_);
v___x_3334_ = lean_st_ref_get(v___y_3328_);
v_env_3335_ = lean_ctor_get(v___x_3334_, 0);
lean_inc_ref(v_env_3335_);
lean_dec(v___x_3334_);
v___x_3336_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_3336_, 0, v_env_3335_);
lean_ctor_set_uint8(v___x_3336_, sizeof(void*)*1, v___x_3319_);
lean_ctor_set_uint8(v___x_3336_, sizeof(void*)*1 + 1, v___x_3319_);
v___x_3337_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_3333_, v___x_3336_, v___y_3324_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_object* v_a_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3348_; 
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3348_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3340_ = v___x_3337_;
v_isShared_3341_ = v_isSharedCheck_3348_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___x_3337_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3348_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
if (lean_obj_tag(v_a_3338_) == 0)
{
lean_object* v___x_3342_; lean_object* v___x_3343_; 
lean_dec_ref_known(v_a_3338_, 1);
lean_del_object(v___x_3340_);
v___x_3342_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2);
v___x_3343_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1(v___x_3342_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
return v___x_3343_;
}
else
{
lean_object* v_a_3344_; lean_object* v___x_3346_; 
v_a_3344_ = lean_ctor_get(v_a_3338_, 0);
lean_inc(v_a_3344_);
lean_dec_ref_known(v_a_3338_, 1);
if (v_isShared_3341_ == 0)
{
lean_ctor_set(v___x_3340_, 0, v_a_3344_);
v___x_3346_ = v___x_3340_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v_a_3344_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
}
}
else
{
lean_object* v_a_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3356_; 
v_a_3349_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3351_ = v___x_3337_;
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_a_3349_);
lean_dec(v___x_3337_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v___x_3354_; 
if (v_isShared_3352_ == 0)
{
v___x_3354_ = v___x_3351_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_a_3349_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__1___boxed(lean_object* v___x_3357_, lean_object* v___x_3358_, lean_object* v___x_3359_, lean_object* v_piece_3360_, lean_object* v_i_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_){
_start:
{
uint8_t v___x_16854__boxed_3370_; lean_object* v_res_3371_; 
v___x_16854__boxed_3370_ = lean_unbox(v___x_3359_);
v_res_3371_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__1(v___x_3357_, v___x_3358_, v___x_16854__boxed_3370_, v_piece_3360_, v_i_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_);
lean_dec(v___y_3368_);
lean_dec_ref(v___y_3367_);
lean_dec(v___y_3366_);
lean_dec_ref(v___y_3365_);
lean_dec(v___y_3364_);
lean_dec_ref(v___y_3363_);
lean_dec(v___y_3362_);
return v_res_3371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7_spec__12(lean_object* v___x_3372_, lean_object* v___x_3373_, lean_object* v_as_3374_, size_t v_sz_3375_, size_t v_i_3376_, lean_object* v_b_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_){
_start:
{
uint8_t v___x_3386_; 
v___x_3386_ = lean_usize_dec_lt(v_i_3376_, v_sz_3375_);
if (v___x_3386_ == 0)
{
lean_object* v___x_3387_; 
lean_dec_ref(v___x_3372_);
v___x_3387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3387_, 0, v_b_3377_);
return v___x_3387_;
}
else
{
lean_object* v_fst_3388_; lean_object* v_snd_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3438_; 
v_fst_3388_ = lean_ctor_get(v_b_3377_, 0);
v_snd_3389_ = lean_ctor_get(v_b_3377_, 1);
v_isSharedCheck_3438_ = !lean_is_exclusive(v_b_3377_);
if (v_isSharedCheck_3438_ == 0)
{
v___x_3391_ = v_b_3377_;
v_isShared_3392_ = v_isSharedCheck_3438_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_snd_3389_);
lean_inc(v_fst_3388_);
lean_dec(v_b_3377_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3438_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v_a_3393_; lean_object* v_userName_3394_; lean_object* v_type_3395_; lean_object* v_value_3396_; uint8_t v_nondep_3397_; lean_object* v___x_3398_; uint8_t v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
v_a_3393_ = lean_array_uget_borrowed(v_as_3374_, v_i_3376_);
v_userName_3394_ = lean_ctor_get(v_a_3393_, 1);
v_type_3395_ = lean_ctor_get(v_a_3393_, 2);
v_value_3396_ = lean_ctor_get(v_a_3393_, 3);
v_nondep_3397_ = lean_ctor_get_uint8(v_a_3393_, sizeof(void*)*4);
v___x_3398_ = lean_unsigned_to_nat(0u);
v___x_3399_ = lean_nat_dec_eq(v___x_3373_, v___x_3398_);
v___x_3400_ = lean_unsigned_to_nat(1u);
v___x_3401_ = lean_nat_sub(v_snd_3389_, v___x_3400_);
lean_dec(v_snd_3389_);
lean_inc(v___x_3401_);
lean_inc_ref(v_type_3395_);
lean_inc_ref(v___x_3372_);
v___x_3402_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__1(v___x_3398_, v___x_3372_, v___x_3399_, v_type_3395_, v___x_3401_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_);
if (lean_obj_tag(v___x_3402_) == 0)
{
lean_object* v_a_3403_; lean_object* v___x_3404_; 
v_a_3403_ = lean_ctor_get(v___x_3402_, 0);
lean_inc(v_a_3403_);
lean_dec_ref_known(v___x_3402_, 1);
lean_inc(v___x_3401_);
lean_inc_ref(v_value_3396_);
lean_inc_ref(v___x_3372_);
v___x_3404_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__1(v___x_3398_, v___x_3372_, v___x_3399_, v_value_3396_, v___x_3401_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_);
if (lean_obj_tag(v___x_3404_) == 0)
{
lean_object* v_a_3405_; lean_object* v___x_3406_; 
v_a_3405_ = lean_ctor_get(v___x_3404_, 0);
lean_inc(v_a_3405_);
lean_dec_ref_known(v___x_3404_, 1);
lean_inc(v_userName_3394_);
v___x_3406_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6___redArg(v_userName_3394_, v_a_3403_, v_a_3405_, v_fst_3388_, v_nondep_3397_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_);
if (lean_obj_tag(v___x_3406_) == 0)
{
lean_object* v_a_3407_; lean_object* v___x_3409_; 
v_a_3407_ = lean_ctor_get(v___x_3406_, 0);
lean_inc(v_a_3407_);
lean_dec_ref_known(v___x_3406_, 1);
if (v_isShared_3392_ == 0)
{
lean_ctor_set(v___x_3391_, 1, v___x_3401_);
lean_ctor_set(v___x_3391_, 0, v_a_3407_);
v___x_3409_ = v___x_3391_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_a_3407_);
lean_ctor_set(v_reuseFailAlloc_3413_, 1, v___x_3401_);
v___x_3409_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
size_t v___x_3410_; size_t v___x_3411_; 
v___x_3410_ = ((size_t)1ULL);
v___x_3411_ = lean_usize_add(v_i_3376_, v___x_3410_);
v_i_3376_ = v___x_3411_;
v_b_3377_ = v___x_3409_;
goto _start;
}
}
else
{
lean_object* v_a_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3421_; 
lean_dec(v___x_3401_);
lean_del_object(v___x_3391_);
lean_dec_ref(v___x_3372_);
v_a_3414_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3421_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3421_ == 0)
{
v___x_3416_ = v___x_3406_;
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_a_3414_);
lean_dec(v___x_3406_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3419_; 
if (v_isShared_3417_ == 0)
{
v___x_3419_ = v___x_3416_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v_a_3414_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
return v___x_3419_;
}
}
}
}
else
{
lean_object* v_a_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3429_; 
lean_dec(v_a_3403_);
lean_dec(v___x_3401_);
lean_del_object(v___x_3391_);
lean_dec(v_fst_3388_);
lean_dec_ref(v___x_3372_);
v_a_3422_ = lean_ctor_get(v___x_3404_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3404_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3424_ = v___x_3404_;
v_isShared_3425_ = v_isSharedCheck_3429_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_a_3422_);
lean_dec(v___x_3404_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3429_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v___x_3427_; 
if (v_isShared_3425_ == 0)
{
v___x_3427_ = v___x_3424_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v_a_3422_);
v___x_3427_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
return v___x_3427_;
}
}
}
}
else
{
lean_object* v_a_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3437_; 
lean_dec(v___x_3401_);
lean_del_object(v___x_3391_);
lean_dec(v_fst_3388_);
lean_dec_ref(v___x_3372_);
v_a_3430_ = lean_ctor_get(v___x_3402_, 0);
v_isSharedCheck_3437_ = !lean_is_exclusive(v___x_3402_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3432_ = v___x_3402_;
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_a_3430_);
lean_dec(v___x_3402_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3435_; 
if (v_isShared_3433_ == 0)
{
v___x_3435_ = v___x_3432_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_a_3430_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
return v___x_3435_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7_spec__12___boxed(lean_object* v___x_3439_, lean_object* v___x_3440_, lean_object* v_as_3441_, lean_object* v_sz_3442_, lean_object* v_i_3443_, lean_object* v_b_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_){
_start:
{
size_t v_sz_boxed_3453_; size_t v_i_boxed_3454_; lean_object* v_res_3455_; 
v_sz_boxed_3453_ = lean_unbox_usize(v_sz_3442_);
lean_dec(v_sz_3442_);
v_i_boxed_3454_ = lean_unbox_usize(v_i_3443_);
lean_dec(v_i_3443_);
v_res_3455_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7_spec__12(v___x_3439_, v___x_3440_, v_as_3441_, v_sz_boxed_3453_, v_i_boxed_3454_, v_b_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
lean_dec(v___y_3449_);
lean_dec_ref(v___y_3448_);
lean_dec(v___y_3447_);
lean_dec_ref(v___y_3446_);
lean_dec(v___y_3445_);
lean_dec_ref(v_as_3441_);
lean_dec(v___x_3440_);
return v_res_3455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7(lean_object* v___x_3456_, lean_object* v___x_3457_, lean_object* v_as_3458_, size_t v_sz_3459_, size_t v_i_3460_, lean_object* v_b_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_){
_start:
{
uint8_t v___x_3470_; 
v___x_3470_ = lean_usize_dec_lt(v_i_3460_, v_sz_3459_);
if (v___x_3470_ == 0)
{
lean_object* v___x_3471_; 
lean_dec_ref(v___x_3456_);
v___x_3471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3471_, 0, v_b_3461_);
return v___x_3471_;
}
else
{
lean_object* v_fst_3472_; lean_object* v_snd_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3522_; 
v_fst_3472_ = lean_ctor_get(v_b_3461_, 0);
v_snd_3473_ = lean_ctor_get(v_b_3461_, 1);
v_isSharedCheck_3522_ = !lean_is_exclusive(v_b_3461_);
if (v_isSharedCheck_3522_ == 0)
{
v___x_3475_ = v_b_3461_;
v_isShared_3476_ = v_isSharedCheck_3522_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_snd_3473_);
lean_inc(v_fst_3472_);
lean_dec(v_b_3461_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3522_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v_a_3477_; lean_object* v_userName_3478_; lean_object* v_type_3479_; lean_object* v_value_3480_; uint8_t v_nondep_3481_; lean_object* v___x_3482_; uint8_t v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; 
v_a_3477_ = lean_array_uget_borrowed(v_as_3458_, v_i_3460_);
v_userName_3478_ = lean_ctor_get(v_a_3477_, 1);
v_type_3479_ = lean_ctor_get(v_a_3477_, 2);
v_value_3480_ = lean_ctor_get(v_a_3477_, 3);
v_nondep_3481_ = lean_ctor_get_uint8(v_a_3477_, sizeof(void*)*4);
v___x_3482_ = lean_unsigned_to_nat(0u);
v___x_3483_ = lean_nat_dec_eq(v___x_3457_, v___x_3482_);
v___x_3484_ = lean_unsigned_to_nat(1u);
v___x_3485_ = lean_nat_sub(v_snd_3473_, v___x_3484_);
lean_dec(v_snd_3473_);
lean_inc(v___x_3485_);
lean_inc_ref(v_type_3479_);
lean_inc_ref(v___x_3456_);
v___x_3486_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__1(v___x_3482_, v___x_3456_, v___x_3483_, v_type_3479_, v___x_3485_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_);
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_object* v_a_3487_; lean_object* v___x_3488_; 
v_a_3487_ = lean_ctor_get(v___x_3486_, 0);
lean_inc(v_a_3487_);
lean_dec_ref_known(v___x_3486_, 1);
lean_inc(v___x_3485_);
lean_inc_ref(v_value_3480_);
lean_inc_ref(v___x_3456_);
v___x_3488_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___lam__1(v___x_3482_, v___x_3456_, v___x_3483_, v_value_3480_, v___x_3485_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v_a_3489_; lean_object* v___x_3490_; 
v_a_3489_ = lean_ctor_get(v___x_3488_, 0);
lean_inc(v_a_3489_);
lean_dec_ref_known(v___x_3488_, 1);
lean_inc(v_userName_3478_);
v___x_3490_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__6___redArg(v_userName_3478_, v_a_3487_, v_a_3489_, v_fst_3472_, v_nondep_3481_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_);
if (lean_obj_tag(v___x_3490_) == 0)
{
lean_object* v_a_3491_; lean_object* v___x_3493_; 
v_a_3491_ = lean_ctor_get(v___x_3490_, 0);
lean_inc(v_a_3491_);
lean_dec_ref_known(v___x_3490_, 1);
if (v_isShared_3476_ == 0)
{
lean_ctor_set(v___x_3475_, 1, v___x_3485_);
lean_ctor_set(v___x_3475_, 0, v_a_3491_);
v___x_3493_ = v___x_3475_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v_a_3491_);
lean_ctor_set(v_reuseFailAlloc_3497_, 1, v___x_3485_);
v___x_3493_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
size_t v___x_3494_; size_t v___x_3495_; lean_object* v___x_3496_; 
v___x_3494_ = ((size_t)1ULL);
v___x_3495_ = lean_usize_add(v_i_3460_, v___x_3494_);
v___x_3496_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7_spec__12(v___x_3456_, v___x_3457_, v_as_3458_, v_sz_3459_, v___x_3495_, v___x_3493_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_);
return v___x_3496_;
}
}
else
{
lean_object* v_a_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3505_; 
lean_dec(v___x_3485_);
lean_del_object(v___x_3475_);
lean_dec_ref(v___x_3456_);
v_a_3498_ = lean_ctor_get(v___x_3490_, 0);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3490_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3500_ = v___x_3490_;
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_a_3498_);
lean_dec(v___x_3490_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3503_; 
if (v_isShared_3501_ == 0)
{
v___x_3503_ = v___x_3500_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_a_3498_);
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
else
{
lean_object* v_a_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3513_; 
lean_dec(v_a_3487_);
lean_dec(v___x_3485_);
lean_del_object(v___x_3475_);
lean_dec(v_fst_3472_);
lean_dec_ref(v___x_3456_);
v_a_3506_ = lean_ctor_get(v___x_3488_, 0);
v_isSharedCheck_3513_ = !lean_is_exclusive(v___x_3488_);
if (v_isSharedCheck_3513_ == 0)
{
v___x_3508_ = v___x_3488_;
v_isShared_3509_ = v_isSharedCheck_3513_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_a_3506_);
lean_dec(v___x_3488_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3513_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v___x_3511_; 
if (v_isShared_3509_ == 0)
{
v___x_3511_ = v___x_3508_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3512_; 
v_reuseFailAlloc_3512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3512_, 0, v_a_3506_);
v___x_3511_ = v_reuseFailAlloc_3512_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
return v___x_3511_;
}
}
}
}
else
{
lean_object* v_a_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3521_; 
lean_dec(v___x_3485_);
lean_del_object(v___x_3475_);
lean_dec(v_fst_3472_);
lean_dec_ref(v___x_3456_);
v_a_3514_ = lean_ctor_get(v___x_3486_, 0);
v_isSharedCheck_3521_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3521_ == 0)
{
v___x_3516_ = v___x_3486_;
v_isShared_3517_ = v_isSharedCheck_3521_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_a_3514_);
lean_dec(v___x_3486_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3521_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
lean_object* v___x_3519_; 
if (v_isShared_3517_ == 0)
{
v___x_3519_ = v___x_3516_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v_a_3514_);
v___x_3519_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
return v___x_3519_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7___boxed(lean_object* v___x_3523_, lean_object* v___x_3524_, lean_object* v_as_3525_, lean_object* v_sz_3526_, lean_object* v_i_3527_, lean_object* v_b_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_){
_start:
{
size_t v_sz_boxed_3537_; size_t v_i_boxed_3538_; lean_object* v_res_3539_; 
v_sz_boxed_3537_ = lean_unbox_usize(v_sz_3526_);
lean_dec(v_sz_3526_);
v_i_boxed_3538_ = lean_unbox_usize(v_i_3527_);
lean_dec(v_i_3527_);
v_res_3539_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7(v___x_3523_, v___x_3524_, v_as_3525_, v_sz_boxed_3537_, v_i_boxed_3538_, v_b_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_);
lean_dec(v___y_3535_);
lean_dec_ref(v___y_3534_);
lean_dec(v___y_3533_);
lean_dec_ref(v___y_3532_);
lean_dec(v___y_3531_);
lean_dec_ref(v___y_3530_);
lean_dec(v___y_3529_);
lean_dec_ref(v_as_3525_);
lean_dec(v___x_3524_);
return v_res_3539_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0___redArg(lean_object* v_a_3540_, lean_object* v_x_3541_){
_start:
{
if (lean_obj_tag(v_x_3541_) == 0)
{
uint8_t v___x_3542_; 
v___x_3542_ = 0;
return v___x_3542_;
}
else
{
lean_object* v_key_3543_; lean_object* v_tail_3544_; uint8_t v___x_3545_; 
v_key_3543_ = lean_ctor_get(v_x_3541_, 0);
v_tail_3544_ = lean_ctor_get(v_x_3541_, 2);
v___x_3545_ = l_Lean_instBEqFVarId_beq(v_key_3543_, v_a_3540_);
if (v___x_3545_ == 0)
{
v_x_3541_ = v_tail_3544_;
goto _start;
}
else
{
return v___x_3545_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0___redArg___boxed(lean_object* v_a_3547_, lean_object* v_x_3548_){
_start:
{
uint8_t v_res_3549_; lean_object* v_r_3550_; 
v_res_3549_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0___redArg(v_a_3547_, v_x_3548_);
lean_dec(v_x_3548_);
lean_dec(v_a_3547_);
v_r_3550_ = lean_box(v_res_3549_);
return v_r_3550_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1_spec__5_spec__10___redArg(lean_object* v_x_3551_, lean_object* v_x_3552_){
_start:
{
if (lean_obj_tag(v_x_3552_) == 0)
{
return v_x_3551_;
}
else
{
lean_object* v_key_3553_; lean_object* v_value_3554_; lean_object* v_tail_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3578_; 
v_key_3553_ = lean_ctor_get(v_x_3552_, 0);
v_value_3554_ = lean_ctor_get(v_x_3552_, 1);
v_tail_3555_ = lean_ctor_get(v_x_3552_, 2);
v_isSharedCheck_3578_ = !lean_is_exclusive(v_x_3552_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3557_ = v_x_3552_;
v_isShared_3558_ = v_isSharedCheck_3578_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_tail_3555_);
lean_inc(v_value_3554_);
lean_inc(v_key_3553_);
lean_dec(v_x_3552_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3578_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
lean_object* v___x_3559_; uint64_t v___x_3560_; uint64_t v___x_3561_; uint64_t v___x_3562_; uint64_t v_fold_3563_; uint64_t v___x_3564_; uint64_t v___x_3565_; uint64_t v___x_3566_; size_t v___x_3567_; size_t v___x_3568_; size_t v___x_3569_; size_t v___x_3570_; size_t v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3574_; 
v___x_3559_ = lean_array_get_size(v_x_3551_);
v___x_3560_ = l_Lean_instHashableFVarId_hash(v_key_3553_);
v___x_3561_ = 32ULL;
v___x_3562_ = lean_uint64_shift_right(v___x_3560_, v___x_3561_);
v_fold_3563_ = lean_uint64_xor(v___x_3560_, v___x_3562_);
v___x_3564_ = 16ULL;
v___x_3565_ = lean_uint64_shift_right(v_fold_3563_, v___x_3564_);
v___x_3566_ = lean_uint64_xor(v_fold_3563_, v___x_3565_);
v___x_3567_ = lean_uint64_to_usize(v___x_3566_);
v___x_3568_ = lean_usize_of_nat(v___x_3559_);
v___x_3569_ = ((size_t)1ULL);
v___x_3570_ = lean_usize_sub(v___x_3568_, v___x_3569_);
v___x_3571_ = lean_usize_land(v___x_3567_, v___x_3570_);
v___x_3572_ = lean_array_uget_borrowed(v_x_3551_, v___x_3571_);
lean_inc(v___x_3572_);
if (v_isShared_3558_ == 0)
{
lean_ctor_set(v___x_3557_, 2, v___x_3572_);
v___x_3574_ = v___x_3557_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v_key_3553_);
lean_ctor_set(v_reuseFailAlloc_3577_, 1, v_value_3554_);
lean_ctor_set(v_reuseFailAlloc_3577_, 2, v___x_3572_);
v___x_3574_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
lean_object* v___x_3575_; 
v___x_3575_ = lean_array_uset(v_x_3551_, v___x_3571_, v___x_3574_);
v_x_3551_ = v___x_3575_;
v_x_3552_ = v_tail_3555_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1_spec__5___redArg(lean_object* v_i_3579_, lean_object* v_source_3580_, lean_object* v_target_3581_){
_start:
{
lean_object* v___x_3582_; uint8_t v___x_3583_; 
v___x_3582_ = lean_array_get_size(v_source_3580_);
v___x_3583_ = lean_nat_dec_lt(v_i_3579_, v___x_3582_);
if (v___x_3583_ == 0)
{
lean_dec_ref(v_source_3580_);
lean_dec(v_i_3579_);
return v_target_3581_;
}
else
{
lean_object* v_es_3584_; lean_object* v___x_3585_; lean_object* v_source_3586_; lean_object* v_target_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; 
v_es_3584_ = lean_array_fget(v_source_3580_, v_i_3579_);
v___x_3585_ = lean_box(0);
v_source_3586_ = lean_array_fset(v_source_3580_, v_i_3579_, v___x_3585_);
v_target_3587_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1_spec__5_spec__10___redArg(v_target_3581_, v_es_3584_);
v___x_3588_ = lean_unsigned_to_nat(1u);
v___x_3589_ = lean_nat_add(v_i_3579_, v___x_3588_);
lean_dec(v_i_3579_);
v_i_3579_ = v___x_3589_;
v_source_3580_ = v_source_3586_;
v_target_3581_ = v_target_3587_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1___redArg(lean_object* v_data_3591_){
_start:
{
lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v_nbuckets_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; 
v___x_3592_ = lean_array_get_size(v_data_3591_);
v___x_3593_ = lean_unsigned_to_nat(2u);
v_nbuckets_3594_ = lean_nat_mul(v___x_3592_, v___x_3593_);
v___x_3595_ = lean_unsigned_to_nat(0u);
v___x_3596_ = lean_box(0);
v___x_3597_ = lean_mk_array(v_nbuckets_3594_, v___x_3596_);
v___x_3598_ = lean_array_propagate_mark(v_data_3591_, v___x_3597_);
v___x_3599_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1_spec__5___redArg(v___x_3595_, v_data_3591_, v___x_3598_);
return v___x_3599_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__2___redArg(lean_object* v_a_3600_, lean_object* v_b_3601_, lean_object* v_x_3602_){
_start:
{
if (lean_obj_tag(v_x_3602_) == 0)
{
lean_dec(v_b_3601_);
lean_dec(v_a_3600_);
return v_x_3602_;
}
else
{
lean_object* v_key_3603_; lean_object* v_value_3604_; lean_object* v_tail_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3617_; 
v_key_3603_ = lean_ctor_get(v_x_3602_, 0);
v_value_3604_ = lean_ctor_get(v_x_3602_, 1);
v_tail_3605_ = lean_ctor_get(v_x_3602_, 2);
v_isSharedCheck_3617_ = !lean_is_exclusive(v_x_3602_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3607_ = v_x_3602_;
v_isShared_3608_ = v_isSharedCheck_3617_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_tail_3605_);
lean_inc(v_value_3604_);
lean_inc(v_key_3603_);
lean_dec(v_x_3602_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3617_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
uint8_t v___x_3609_; 
v___x_3609_ = l_Lean_instBEqFVarId_beq(v_key_3603_, v_a_3600_);
if (v___x_3609_ == 0)
{
lean_object* v___x_3610_; lean_object* v___x_3612_; 
v___x_3610_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__2___redArg(v_a_3600_, v_b_3601_, v_tail_3605_);
if (v_isShared_3608_ == 0)
{
lean_ctor_set(v___x_3607_, 2, v___x_3610_);
v___x_3612_ = v___x_3607_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_key_3603_);
lean_ctor_set(v_reuseFailAlloc_3613_, 1, v_value_3604_);
lean_ctor_set(v_reuseFailAlloc_3613_, 2, v___x_3610_);
v___x_3612_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
return v___x_3612_;
}
}
else
{
lean_object* v___x_3615_; 
lean_dec(v_value_3604_);
lean_dec(v_key_3603_);
if (v_isShared_3608_ == 0)
{
lean_ctor_set(v___x_3607_, 1, v_b_3601_);
lean_ctor_set(v___x_3607_, 0, v_a_3600_);
v___x_3615_ = v___x_3607_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v_a_3600_);
lean_ctor_set(v_reuseFailAlloc_3616_, 1, v_b_3601_);
lean_ctor_set(v_reuseFailAlloc_3616_, 2, v_tail_3605_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
return v___x_3615_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0___redArg(lean_object* v_m_3618_, lean_object* v_a_3619_, lean_object* v_b_3620_){
_start:
{
lean_object* v_size_3621_; lean_object* v_buckets_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3665_; 
v_size_3621_ = lean_ctor_get(v_m_3618_, 0);
v_buckets_3622_ = lean_ctor_get(v_m_3618_, 1);
v_isSharedCheck_3665_ = !lean_is_exclusive(v_m_3618_);
if (v_isSharedCheck_3665_ == 0)
{
v___x_3624_ = v_m_3618_;
v_isShared_3625_ = v_isSharedCheck_3665_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_buckets_3622_);
lean_inc(v_size_3621_);
lean_dec(v_m_3618_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3665_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
lean_object* v___x_3626_; uint64_t v___x_3627_; uint64_t v___x_3628_; uint64_t v___x_3629_; uint64_t v_fold_3630_; uint64_t v___x_3631_; uint64_t v___x_3632_; uint64_t v___x_3633_; size_t v___x_3634_; size_t v___x_3635_; size_t v___x_3636_; size_t v___x_3637_; size_t v___x_3638_; lean_object* v_bkt_3639_; uint8_t v___x_3640_; 
v___x_3626_ = lean_array_get_size(v_buckets_3622_);
v___x_3627_ = l_Lean_instHashableFVarId_hash(v_a_3619_);
v___x_3628_ = 32ULL;
v___x_3629_ = lean_uint64_shift_right(v___x_3627_, v___x_3628_);
v_fold_3630_ = lean_uint64_xor(v___x_3627_, v___x_3629_);
v___x_3631_ = 16ULL;
v___x_3632_ = lean_uint64_shift_right(v_fold_3630_, v___x_3631_);
v___x_3633_ = lean_uint64_xor(v_fold_3630_, v___x_3632_);
v___x_3634_ = lean_uint64_to_usize(v___x_3633_);
v___x_3635_ = lean_usize_of_nat(v___x_3626_);
v___x_3636_ = ((size_t)1ULL);
v___x_3637_ = lean_usize_sub(v___x_3635_, v___x_3636_);
v___x_3638_ = lean_usize_land(v___x_3634_, v___x_3637_);
v_bkt_3639_ = lean_array_uget_borrowed(v_buckets_3622_, v___x_3638_);
v___x_3640_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0___redArg(v_a_3619_, v_bkt_3639_);
if (v___x_3640_ == 0)
{
lean_object* v___x_3641_; lean_object* v_size_x27_3642_; lean_object* v___x_3643_; lean_object* v_buckets_x27_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; uint8_t v___x_3650_; 
v___x_3641_ = lean_unsigned_to_nat(1u);
v_size_x27_3642_ = lean_nat_add(v_size_3621_, v___x_3641_);
lean_dec(v_size_3621_);
lean_inc(v_bkt_3639_);
v___x_3643_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3643_, 0, v_a_3619_);
lean_ctor_set(v___x_3643_, 1, v_b_3620_);
lean_ctor_set(v___x_3643_, 2, v_bkt_3639_);
v_buckets_x27_3644_ = lean_array_uset(v_buckets_3622_, v___x_3638_, v___x_3643_);
v___x_3645_ = lean_unsigned_to_nat(4u);
v___x_3646_ = lean_nat_mul(v_size_x27_3642_, v___x_3645_);
v___x_3647_ = lean_unsigned_to_nat(3u);
v___x_3648_ = lean_nat_div(v___x_3646_, v___x_3647_);
lean_dec(v___x_3646_);
v___x_3649_ = lean_array_get_size(v_buckets_x27_3644_);
v___x_3650_ = lean_nat_dec_le(v___x_3648_, v___x_3649_);
lean_dec(v___x_3648_);
if (v___x_3650_ == 0)
{
lean_object* v_val_3651_; lean_object* v___x_3653_; 
v_val_3651_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1___redArg(v_buckets_x27_3644_);
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 1, v_val_3651_);
lean_ctor_set(v___x_3624_, 0, v_size_x27_3642_);
v___x_3653_ = v___x_3624_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v_size_x27_3642_);
lean_ctor_set(v_reuseFailAlloc_3654_, 1, v_val_3651_);
v___x_3653_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
return v___x_3653_;
}
}
else
{
lean_object* v___x_3656_; 
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 1, v_buckets_x27_3644_);
lean_ctor_set(v___x_3624_, 0, v_size_x27_3642_);
v___x_3656_ = v___x_3624_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v_size_x27_3642_);
lean_ctor_set(v_reuseFailAlloc_3657_, 1, v_buckets_x27_3644_);
v___x_3656_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
return v___x_3656_;
}
}
}
else
{
lean_object* v___x_3658_; lean_object* v_buckets_x27_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3663_; 
lean_inc(v_bkt_3639_);
v___x_3658_ = lean_box(0);
v_buckets_x27_3659_ = lean_array_uset(v_buckets_3622_, v___x_3638_, v___x_3658_);
v___x_3660_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__2___redArg(v_a_3619_, v_b_3620_, v_bkt_3639_);
v___x_3661_ = lean_array_uset(v_buckets_x27_3659_, v___x_3638_, v___x_3660_);
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 1, v___x_3661_);
v___x_3663_ = v___x_3624_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v_size_3621_);
lean_ctor_set(v_reuseFailAlloc_3664_, 1, v___x_3661_);
v___x_3663_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
return v___x_3663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1___redArg(lean_object* v_as_3666_, size_t v_sz_3667_, size_t v_i_3668_, lean_object* v_b_3669_){
_start:
{
uint8_t v___x_3671_; 
v___x_3671_ = lean_usize_dec_lt(v_i_3668_, v_sz_3667_);
if (v___x_3671_ == 0)
{
lean_object* v___x_3672_; 
v___x_3672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3672_, 0, v_b_3669_);
return v___x_3672_;
}
else
{
lean_object* v_fst_3673_; lean_object* v_snd_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3690_; 
v_fst_3673_ = lean_ctor_get(v_b_3669_, 0);
v_snd_3674_ = lean_ctor_get(v_b_3669_, 1);
v_isSharedCheck_3690_ = !lean_is_exclusive(v_b_3669_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3676_ = v_b_3669_;
v_isShared_3677_ = v_isSharedCheck_3690_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_snd_3674_);
lean_inc(v_fst_3673_);
lean_dec(v_b_3669_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3690_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v_a_3678_; lean_object* v_fvar_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3685_; 
v_a_3678_ = lean_array_uget_borrowed(v_as_3666_, v_i_3668_);
v_fvar_3679_ = lean_ctor_get(v_a_3678_, 0);
v___x_3680_ = l_Lean_Expr_fvarId_x21(v_fvar_3679_);
lean_inc(v_snd_3674_);
v___x_3681_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0___redArg(v_fst_3673_, v___x_3680_, v_snd_3674_);
v___x_3682_ = lean_unsigned_to_nat(1u);
v___x_3683_ = lean_nat_add(v_snd_3674_, v___x_3682_);
lean_dec(v_snd_3674_);
if (v_isShared_3677_ == 0)
{
lean_ctor_set(v___x_3676_, 1, v___x_3683_);
lean_ctor_set(v___x_3676_, 0, v___x_3681_);
v___x_3685_ = v___x_3676_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v___x_3681_);
lean_ctor_set(v_reuseFailAlloc_3689_, 1, v___x_3683_);
v___x_3685_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
size_t v___x_3686_; size_t v___x_3687_; 
v___x_3686_ = ((size_t)1ULL);
v___x_3687_ = lean_usize_add(v_i_3668_, v___x_3686_);
v_i_3668_ = v___x_3687_;
v_b_3669_ = v___x_3685_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1___redArg___boxed(lean_object* v_as_3691_, lean_object* v_sz_3692_, lean_object* v_i_3693_, lean_object* v_b_3694_, lean_object* v___y_3695_){
_start:
{
size_t v_sz_boxed_3696_; size_t v_i_boxed_3697_; lean_object* v_res_3698_; 
v_sz_boxed_3696_ = lean_unbox_usize(v_sz_3692_);
lean_dec(v_sz_3692_);
v_i_boxed_3697_ = lean_unbox_usize(v_i_3693_);
lean_dec(v_i_3693_);
v_res_3698_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1___redArg(v_as_3691_, v_sz_boxed_3696_, v_i_boxed_3697_, v_b_3694_);
lean_dec_ref(v_as_3691_);
return v_res_3698_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__0(void){
_start:
{
lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; 
v___x_3699_ = lean_box(0);
v___x_3700_ = lean_unsigned_to_nat(16u);
v___x_3701_ = lean_mk_array(v___x_3700_, v___x_3699_);
return v___x_3701_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__1(void){
_start:
{
lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; 
v___x_3702_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__0, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__0_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__0);
v___x_3703_ = lean_unsigned_to_nat(0u);
v___x_3704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3704_, 0, v___x_3703_);
lean_ctor_set(v___x_3704_, 1, v___x_3702_);
return v___x_3704_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__2(void){
_start:
{
lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
v___x_3705_ = lean_unsigned_to_nat(0u);
v___x_3706_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__1, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__1_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__1);
v___x_3707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3707_, 0, v___x_3706_);
lean_ctor_set(v___x_3707_, 1, v___x_3705_);
return v___x_3707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets(lean_object* v_e_3708_, lean_object* v_a_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_, lean_object* v_a_3712_, lean_object* v_a_3713_, lean_object* v_a_3714_, lean_object* v_a_3715_){
_start:
{
lean_object* v___x_3717_; lean_object* v_decls_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; uint8_t v___x_3721_; 
v___x_3717_ = lean_st_ref_get(v_a_3709_);
v_decls_3718_ = lean_ctor_get(v___x_3717_, 3);
lean_inc_ref(v_decls_3718_);
lean_dec(v___x_3717_);
v___x_3719_ = lean_array_get_size(v_decls_3718_);
v___x_3720_ = lean_unsigned_to_nat(0u);
v___x_3721_ = lean_nat_dec_eq(v___x_3719_, v___x_3720_);
if (v___x_3721_ == 0)
{
lean_object* v___x_3722_; lean_object* v___x_3723_; size_t v_sz_3724_; size_t v___x_3725_; lean_object* v___x_3726_; 
v___x_3722_ = lean_unsigned_to_nat(16u);
v___x_3723_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___closed__2);
v_sz_3724_ = lean_array_size(v_decls_3718_);
v___x_3725_ = ((size_t)0ULL);
v___x_3726_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1___redArg(v_decls_3718_, v_sz_3724_, v___x_3725_, v___x_3723_);
if (lean_obj_tag(v___x_3726_) == 0)
{
lean_object* v_a_3727_; lean_object* v_fst_3728_; lean_object* v___x_3730_; uint8_t v_isShared_3731_; uint8_t v_isSharedCheck_3778_; 
v_a_3727_ = lean_ctor_get(v___x_3726_, 0);
lean_inc(v_a_3727_);
lean_dec_ref_known(v___x_3726_, 1);
v_fst_3728_ = lean_ctor_get(v_a_3727_, 0);
v_isSharedCheck_3778_ = !lean_is_exclusive(v_a_3727_);
if (v_isSharedCheck_3778_ == 0)
{
lean_object* v_unused_3779_; 
v_unused_3779_ = lean_ctor_get(v_a_3727_, 1);
lean_dec(v_unused_3779_);
v___x_3730_ = v_a_3727_;
v_isShared_3731_ = v_isSharedCheck_3778_;
goto v_resetjp_3729_;
}
else
{
lean_inc(v_fst_3728_);
lean_dec(v_a_3727_);
v___x_3730_ = lean_box(0);
v_isShared_3731_ = v_isSharedCheck_3778_;
goto v_resetjp_3729_;
}
v_resetjp_3729_:
{
lean_object* v_a_3733_; lean_object* v___x_3757_; uint8_t v_debug_3758_; lean_object* v___x_3759_; lean_object* v___f_3760_; lean_object* v___x_3761_; lean_object* v_env_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; 
v___x_3757_ = lean_st_ref_get(v_a_3711_);
v_debug_3758_ = lean_ctor_get_uint8(v___x_3757_, sizeof(void*)*12);
lean_dec(v___x_3757_);
v___x_3759_ = lean_box(v_debug_3758_);
lean_inc(v_fst_3728_);
v___f_3760_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___lam__0___boxed), 8, 6);
lean_closure_set(v___f_3760_, 0, v_e_3708_);
lean_closure_set(v___f_3760_, 1, v___x_3722_);
lean_closure_set(v___f_3760_, 2, v___x_3720_);
lean_closure_set(v___f_3760_, 3, v_fst_3728_);
lean_closure_set(v___f_3760_, 4, v___x_3719_);
lean_closure_set(v___f_3760_, 5, v___x_3759_);
v___x_3761_ = lean_st_ref_get(v_a_3715_);
v_env_3762_ = lean_ctor_get(v___x_3761_, 0);
lean_inc_ref(v_env_3762_);
lean_dec(v___x_3761_);
v___x_3763_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_3763_, 0, v_env_3762_);
lean_ctor_set_uint8(v___x_3763_, sizeof(void*)*1, v___x_3721_);
lean_ctor_set_uint8(v___x_3763_, sizeof(void*)*1 + 1, v___x_3721_);
v___x_3764_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_3760_, v___x_3763_, v_a_3711_);
if (lean_obj_tag(v___x_3764_) == 0)
{
lean_object* v_a_3765_; 
v_a_3765_ = lean_ctor_get(v___x_3764_, 0);
lean_inc(v_a_3765_);
lean_dec_ref_known(v___x_3764_, 1);
if (lean_obj_tag(v_a_3765_) == 0)
{
lean_object* v___x_3766_; lean_object* v___x_3767_; 
lean_dec_ref_known(v_a_3765_, 1);
v___x_3766_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv___redArg___closed__2);
v___x_3767_ = l_panic___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_substEnv_spec__1(v___x_3766_, v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_, v_a_3714_, v_a_3715_);
if (lean_obj_tag(v___x_3767_) == 0)
{
lean_object* v_a_3768_; 
v_a_3768_ = lean_ctor_get(v___x_3767_, 0);
lean_inc(v_a_3768_);
lean_dec_ref_known(v___x_3767_, 1);
v_a_3733_ = v_a_3768_;
goto v___jp_3732_;
}
else
{
lean_del_object(v___x_3730_);
lean_dec(v_fst_3728_);
lean_dec_ref(v_decls_3718_);
return v___x_3767_;
}
}
else
{
lean_object* v_a_3769_; 
v_a_3769_ = lean_ctor_get(v_a_3765_, 0);
lean_inc(v_a_3769_);
lean_dec_ref_known(v_a_3765_, 1);
v_a_3733_ = v_a_3769_;
goto v___jp_3732_;
}
}
else
{
lean_object* v_a_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3777_; 
lean_del_object(v___x_3730_);
lean_dec(v_fst_3728_);
lean_dec_ref(v_decls_3718_);
v_a_3770_ = lean_ctor_get(v___x_3764_, 0);
v_isSharedCheck_3777_ = !lean_is_exclusive(v___x_3764_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3772_ = v___x_3764_;
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_a_3770_);
lean_dec(v___x_3764_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v___x_3775_; 
if (v_isShared_3773_ == 0)
{
v___x_3775_ = v___x_3772_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v_a_3770_);
v___x_3775_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
return v___x_3775_;
}
}
}
v___jp_3732_:
{
lean_object* v___x_3734_; lean_object* v___x_3736_; 
v___x_3734_ = l_Array_reverse___redArg(v_decls_3718_);
if (v_isShared_3731_ == 0)
{
lean_ctor_set(v___x_3730_, 1, v___x_3719_);
lean_ctor_set(v___x_3730_, 0, v_a_3733_);
v___x_3736_ = v___x_3730_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v_a_3733_);
lean_ctor_set(v_reuseFailAlloc_3756_, 1, v___x_3719_);
v___x_3736_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
size_t v_sz_3737_; lean_object* v___x_3738_; 
v_sz_3737_ = lean_array_size(v___x_3734_);
v___x_3738_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__7(v_fst_3728_, v___x_3719_, v___x_3734_, v_sz_3737_, v___x_3725_, v___x_3736_, v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_, v_a_3714_, v_a_3715_);
lean_dec_ref(v___x_3734_);
if (lean_obj_tag(v___x_3738_) == 0)
{
lean_object* v_a_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3747_; 
v_a_3739_ = lean_ctor_get(v___x_3738_, 0);
v_isSharedCheck_3747_ = !lean_is_exclusive(v___x_3738_);
if (v_isSharedCheck_3747_ == 0)
{
v___x_3741_ = v___x_3738_;
v_isShared_3742_ = v_isSharedCheck_3747_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_a_3739_);
lean_dec(v___x_3738_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3747_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v_fst_3743_; lean_object* v___x_3745_; 
v_fst_3743_ = lean_ctor_get(v_a_3739_, 0);
lean_inc(v_fst_3743_);
lean_dec(v_a_3739_);
if (v_isShared_3742_ == 0)
{
lean_ctor_set(v___x_3741_, 0, v_fst_3743_);
v___x_3745_ = v___x_3741_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_fst_3743_);
v___x_3745_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
return v___x_3745_;
}
}
}
else
{
lean_object* v_a_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3755_; 
v_a_3748_ = lean_ctor_get(v___x_3738_, 0);
v_isSharedCheck_3755_ = !lean_is_exclusive(v___x_3738_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3750_ = v___x_3738_;
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_a_3748_);
lean_dec(v___x_3738_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___x_3753_; 
if (v_isShared_3751_ == 0)
{
v___x_3753_ = v___x_3750_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_a_3748_);
v___x_3753_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
return v___x_3753_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3787_; 
lean_dec_ref(v_decls_3718_);
lean_dec_ref(v_e_3708_);
v_a_3780_ = lean_ctor_get(v___x_3726_, 0);
v_isSharedCheck_3787_ = !lean_is_exclusive(v___x_3726_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3782_ = v___x_3726_;
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_a_3780_);
lean_dec(v___x_3726_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v___x_3785_; 
if (v_isShared_3783_ == 0)
{
v___x_3785_ = v___x_3782_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v_a_3780_);
v___x_3785_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
return v___x_3785_;
}
}
}
}
else
{
lean_object* v___x_3788_; 
lean_dec_ref(v_decls_3718_);
v___x_3788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3788_, 0, v_e_3708_);
return v___x_3788_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets___boxed(lean_object* v_e_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_, lean_object* v_a_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_, lean_object* v_a_3796_, lean_object* v_a_3797_){
_start:
{
lean_object* v_res_3798_; 
v_res_3798_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets(v_e_3789_, v_a_3790_, v_a_3791_, v_a_3792_, v_a_3793_, v_a_3794_, v_a_3795_, v_a_3796_);
lean_dec(v_a_3796_);
lean_dec_ref(v_a_3795_);
lean_dec(v_a_3794_);
lean_dec_ref(v_a_3793_);
lean_dec(v_a_3792_);
lean_dec_ref(v_a_3791_);
lean_dec(v_a_3790_);
return v_res_3798_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0(lean_object* v_00_u03b2_3799_, lean_object* v_m_3800_, lean_object* v_a_3801_, lean_object* v_b_3802_){
_start:
{
lean_object* v___x_3803_; 
v___x_3803_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0___redArg(v_m_3800_, v_a_3801_, v_b_3802_);
return v___x_3803_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1(lean_object* v_as_3804_, size_t v_sz_3805_, size_t v_i_3806_, lean_object* v_b_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_){
_start:
{
lean_object* v___x_3816_; 
v___x_3816_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1___redArg(v_as_3804_, v_sz_3805_, v_i_3806_, v_b_3807_);
return v___x_3816_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1___boxed(lean_object* v_as_3817_, lean_object* v_sz_3818_, lean_object* v_i_3819_, lean_object* v_b_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_){
_start:
{
size_t v_sz_boxed_3829_; size_t v_i_boxed_3830_; lean_object* v_res_3831_; 
v_sz_boxed_3829_ = lean_unbox_usize(v_sz_3818_);
lean_dec(v_sz_3818_);
v_i_boxed_3830_ = lean_unbox_usize(v_i_3819_);
lean_dec(v_i_3819_);
v_res_3831_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__1(v_as_3817_, v_sz_boxed_3829_, v_i_boxed_3830_, v_b_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_);
lean_dec(v___y_3827_);
lean_dec_ref(v___y_3826_);
lean_dec(v___y_3825_);
lean_dec_ref(v___y_3824_);
lean_dec(v___y_3823_);
lean_dec_ref(v___y_3822_);
lean_dec(v___y_3821_);
lean_dec_ref(v_as_3817_);
return v_res_3831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2(lean_object* v_00_u03b2_3832_, lean_object* v_m_3833_, lean_object* v_a_3834_){
_start:
{
lean_object* v___x_3835_; 
v___x_3835_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___redArg(v_m_3833_, v_a_3834_);
return v___x_3835_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2___boxed(lean_object* v_00_u03b2_3836_, lean_object* v_m_3837_, lean_object* v_a_3838_){
_start:
{
lean_object* v_res_3839_; 
v_res_3839_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2(v_00_u03b2_3836_, v_m_3837_, v_a_3838_);
lean_dec(v_a_3838_);
lean_dec_ref(v_m_3837_);
return v_res_3839_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0(lean_object* v_00_u03b2_3840_, lean_object* v_a_3841_, lean_object* v_x_3842_){
_start:
{
uint8_t v___x_3843_; 
v___x_3843_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0___redArg(v_a_3841_, v_x_3842_);
return v___x_3843_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3844_, lean_object* v_a_3845_, lean_object* v_x_3846_){
_start:
{
uint8_t v_res_3847_; lean_object* v_r_3848_; 
v_res_3847_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__0(v_00_u03b2_3844_, v_a_3845_, v_x_3846_);
lean_dec(v_x_3846_);
lean_dec(v_a_3845_);
v_r_3848_ = lean_box(v_res_3847_);
return v_r_3848_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1(lean_object* v_00_u03b2_3849_, lean_object* v_data_3850_){
_start:
{
lean_object* v___x_3851_; 
v___x_3851_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1___redArg(v_data_3850_);
return v___x_3851_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__2(lean_object* v_00_u03b2_3852_, lean_object* v_a_3853_, lean_object* v_b_3854_, lean_object* v_x_3855_){
_start:
{
lean_object* v___x_3856_; 
v___x_3856_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__2___redArg(v_a_3853_, v_b_3854_, v_x_3855_);
return v___x_3856_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2_spec__5(lean_object* v_00_u03b2_3857_, lean_object* v_a_3858_, lean_object* v_x_3859_){
_start:
{
lean_object* v___x_3860_; 
v___x_3860_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2_spec__5___redArg(v_a_3858_, v_x_3859_);
return v___x_3860_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3861_, lean_object* v_a_3862_, lean_object* v_x_3863_){
_start:
{
lean_object* v_res_3864_; 
v_res_3864_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__2_spec__5(v_00_u03b2_3861_, v_a_3862_, v_x_3863_);
lean_dec(v_x_3863_);
lean_dec(v_a_3862_);
return v_res_3864_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_3865_, lean_object* v_i_3866_, lean_object* v_source_3867_, lean_object* v_target_3868_){
_start:
{
lean_object* v___x_3869_; 
v___x_3869_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1_spec__5___redArg(v_i_3866_, v_source_3867_, v_target_3868_);
return v___x_3869_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1_spec__5_spec__10(lean_object* v_00_u03b2_3870_, lean_object* v_x_3871_, lean_object* v_x_3872_){
_start:
{
lean_object* v___x_3873_; 
v___x_3873_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets_spec__0_spec__1_spec__5_spec__10___redArg(v_x_3871_, v_x_3872_);
return v___x_3873_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0___redArg(lean_object* v_msg_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_){
_start:
{
lean_object* v_ref_3880_; lean_object* v___x_3881_; lean_object* v_a_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3890_; 
v_ref_3880_ = lean_ctor_get(v___y_3877_, 2);
v___x_3881_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go_spec__5_spec__5(v_msg_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_);
v_a_3882_ = lean_ctor_get(v___x_3881_, 0);
v_isSharedCheck_3890_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3890_ == 0)
{
v___x_3884_ = v___x_3881_;
v_isShared_3885_ = v_isSharedCheck_3890_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_a_3882_);
lean_dec(v___x_3881_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3890_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v___x_3886_; lean_object* v___x_3888_; 
lean_inc(v_ref_3880_);
v___x_3886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3886_, 0, v_ref_3880_);
lean_ctor_set(v___x_3886_, 1, v_a_3882_);
if (v_isShared_3885_ == 0)
{
lean_ctor_set_tag(v___x_3884_, 1);
lean_ctor_set(v___x_3884_, 0, v___x_3886_);
v___x_3888_ = v___x_3884_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v___x_3886_);
v___x_3888_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
return v___x_3888_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0___redArg___boxed(lean_object* v_msg_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_){
_start:
{
lean_object* v_res_3897_; 
v_res_3897_ = l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0___redArg(v_msg_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_);
lean_dec(v___y_3895_);
lean_dec_ref(v___y_3894_);
lean_dec(v___y_3893_);
lean_dec_ref(v___y_3892_);
return v_res_3897_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_liftLets___closed__0(void){
_start:
{
lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; 
v___x_3898_ = lean_box(0);
v___x_3899_ = lean_unsigned_to_nat(16u);
v___x_3900_ = lean_mk_array(v___x_3899_, v___x_3898_);
return v___x_3900_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_liftLets___closed__1(void){
_start:
{
lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; 
v___x_3901_ = lean_obj_once(&l_Lean_Meta_Sym_liftLets___closed__0, &l_Lean_Meta_Sym_liftLets___closed__0_once, _init_l_Lean_Meta_Sym_liftLets___closed__0);
v___x_3902_ = lean_unsigned_to_nat(0u);
v___x_3903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3903_, 0, v___x_3902_);
lean_ctor_set(v___x_3903_, 1, v___x_3901_);
return v___x_3903_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_liftLets___closed__3(void){
_start:
{
lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; 
v___x_3906_ = ((lean_object*)(l_Lean_Meta_Sym_liftLets___closed__2));
v___x_3907_ = lean_obj_once(&l_Lean_Meta_Sym_liftLets___closed__1, &l_Lean_Meta_Sym_liftLets___closed__1_once, _init_l_Lean_Meta_Sym_liftLets___closed__1);
v___x_3908_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3908_, 0, v___x_3907_);
lean_ctor_set(v___x_3908_, 1, v___x_3907_);
lean_ctor_set(v___x_3908_, 2, v___x_3907_);
lean_ctor_set(v___x_3908_, 3, v___x_3906_);
lean_ctor_set(v___x_3908_, 4, v___x_3907_);
return v___x_3908_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_liftLets___closed__5(void){
_start:
{
lean_object* v___x_3910_; lean_object* v___x_3911_; 
v___x_3910_ = ((lean_object*)(l_Lean_Meta_Sym_liftLets___closed__4));
v___x_3911_ = l_Lean_stringToMessageData(v___x_3910_);
return v___x_3911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLets(lean_object* v_e_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_, lean_object* v_a_3915_, lean_object* v_a_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_){
_start:
{
lean_object* v___y_3921_; lean_object* v___y_3922_; lean_object* v___y_3933_; lean_object* v___y_3934_; lean_object* v___y_3935_; lean_object* v___y_3936_; lean_object* v___y_3937_; lean_object* v___y_3938_; uint8_t v___x_3945_; 
v___x_3945_ = l_Lean_Expr_hasLooseBVars(v_e_3912_);
if (v___x_3945_ == 0)
{
v___y_3933_ = v_a_3913_;
v___y_3934_ = v_a_3914_;
v___y_3935_ = v_a_3915_;
v___y_3936_ = v_a_3916_;
v___y_3937_ = v_a_3917_;
v___y_3938_ = v_a_3918_;
goto v___jp_3932_;
}
else
{
lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v_a_3948_; lean_object* v___x_3950_; uint8_t v_isShared_3951_; uint8_t v_isSharedCheck_3955_; 
lean_dec_ref(v_e_3912_);
v___x_3946_ = lean_obj_once(&l_Lean_Meta_Sym_liftLets___closed__5, &l_Lean_Meta_Sym_liftLets___closed__5_once, _init_l_Lean_Meta_Sym_liftLets___closed__5);
v___x_3947_ = l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0___redArg(v___x_3946_, v_a_3915_, v_a_3916_, v_a_3917_, v_a_3918_);
v_a_3948_ = lean_ctor_get(v___x_3947_, 0);
v_isSharedCheck_3955_ = !lean_is_exclusive(v___x_3947_);
if (v_isSharedCheck_3955_ == 0)
{
v___x_3950_ = v___x_3947_;
v_isShared_3951_ = v_isSharedCheck_3955_;
goto v_resetjp_3949_;
}
else
{
lean_inc(v_a_3948_);
lean_dec(v___x_3947_);
v___x_3950_ = lean_box(0);
v_isShared_3951_ = v_isSharedCheck_3955_;
goto v_resetjp_3949_;
}
v_resetjp_3949_:
{
lean_object* v___x_3953_; 
if (v_isShared_3951_ == 0)
{
v___x_3953_ = v___x_3950_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3954_; 
v_reuseFailAlloc_3954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3954_, 0, v_a_3948_);
v___x_3953_ = v_reuseFailAlloc_3954_;
goto v_reusejp_3952_;
}
v_reusejp_3952_:
{
return v___x_3953_;
}
}
}
v___jp_3920_:
{
if (lean_obj_tag(v___y_3922_) == 0)
{
lean_object* v_a_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3931_; 
v_a_3923_ = lean_ctor_get(v___y_3922_, 0);
v_isSharedCheck_3931_ = !lean_is_exclusive(v___y_3922_);
if (v_isSharedCheck_3931_ == 0)
{
v___x_3925_ = v___y_3922_;
v_isShared_3926_ = v_isSharedCheck_3931_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_a_3923_);
lean_dec(v___y_3922_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3931_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3927_; lean_object* v___x_3929_; 
v___x_3927_ = lean_st_ref_get(v___y_3921_);
lean_dec(v___y_3921_);
lean_dec(v___x_3927_);
if (v_isShared_3926_ == 0)
{
v___x_3929_ = v___x_3925_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v_a_3923_);
v___x_3929_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
return v___x_3929_;
}
}
}
else
{
lean_dec(v___y_3921_);
return v___y_3922_;
}
}
v___jp_3932_:
{
lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; 
v___x_3939_ = lean_obj_once(&l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__3, &l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__3_once, _init_l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go___closed__3);
v___x_3940_ = lean_obj_once(&l_Lean_Meta_Sym_liftLets___closed__3, &l_Lean_Meta_Sym_liftLets___closed__3_once, _init_l_Lean_Meta_Sym_liftLets___closed__3);
v___x_3941_ = lean_st_mk_ref(v___x_3940_);
v___x_3942_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_go(v___x_3939_, v_e_3912_, v___x_3941_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_);
if (lean_obj_tag(v___x_3942_) == 0)
{
lean_object* v_a_3943_; lean_object* v___x_3944_; 
v_a_3943_ = lean_ctor_get(v___x_3942_, 0);
lean_inc(v_a_3943_);
lean_dec_ref_known(v___x_3942_, 1);
v___x_3944_ = l___private_Lean_Meta_Sym_LiftLet_0__Lean_Meta_Sym_LiftLet_mkLets(v_a_3943_, v___x_3941_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_);
v___y_3921_ = v___x_3941_;
v___y_3922_ = v___x_3944_;
goto v___jp_3920_;
}
else
{
v___y_3921_ = v___x_3941_;
v___y_3922_ = v___x_3942_;
goto v___jp_3920_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLets___boxed(lean_object* v_e_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_){
_start:
{
lean_object* v_res_3964_; 
v_res_3964_ = l_Lean_Meta_Sym_liftLets(v_e_3956_, v_a_3957_, v_a_3958_, v_a_3959_, v_a_3960_, v_a_3961_, v_a_3962_);
lean_dec(v_a_3962_);
lean_dec_ref(v_a_3961_);
lean_dec(v_a_3960_);
lean_dec_ref(v_a_3959_);
lean_dec(v_a_3958_);
lean_dec_ref(v_a_3957_);
return v_res_3964_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0(lean_object* v_00_u03b1_3965_, lean_object* v_msg_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_){
_start:
{
lean_object* v___x_3974_; 
v___x_3974_ = l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0___redArg(v_msg_3966_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_);
return v___x_3974_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0___boxed(lean_object* v_00_u03b1_3975_, lean_object* v_msg_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_){
_start:
{
lean_object* v_res_3984_; 
v_res_3984_ = l_Lean_throwError___at___00Lean_Meta_Sym_liftLets_spec__0(v_00_u03b1_3975_, v_msg_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_);
lean_dec(v___y_3982_);
lean_dec_ref(v___y_3981_);
lean_dec(v___y_3980_);
lean_dec_ref(v___y_3979_);
lean_dec(v___y_3978_);
lean_dec_ref(v___y_3977_);
return v_res_3984_;
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
