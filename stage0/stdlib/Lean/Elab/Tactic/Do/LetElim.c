// Lean compiler output
// Module: Lean.Elab.Tactic.Do.LetElim
// Imports: public import Lean.Meta.Tactic.Simp import Init.Omega
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
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_KVMap_setNat(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_mergeBy(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_setType(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_setValue(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
extern lean_object* l_Lean_instInhabitedLocalDecl_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_KVMap_getNat(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Simp_isCharLit(lean_object*);
uint8_t l_Lean_Meta_Simp_isOfNatNatLit(lean_object*);
uint8_t l_Lean_Meta_Simp_isOfScientificLit(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofFn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_instBEqUses_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instBEqUses_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_instBEqUses___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_instBEqUses_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_instBEqUses___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_instBEqUses___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_instBEqUses = (const lean_object*)&l_Lean_Elab_Tactic_Do_instBEqUses___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_instOrdUses_ord(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instOrdUses_ord___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_instOrdUses___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_instOrdUses_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_instOrdUses___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_instOrdUses___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_instOrdUses = (const lean_object*)&l_Lean_Elab_Tactic_Do_instOrdUses___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_instInhabitedUses_default;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_instInhabitedUses;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_Uses_add(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_add___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_toNat(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_toNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_Uses_fromNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_fromNat___boxed(lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_instAddUses___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_Uses_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_instAddUses___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_instAddUses___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_instAddUses = (const lean_object*)&l_Lean_Elab_Tactic_Do_instAddUses___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_FVarUses_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_FVarUses_add___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_instAddFVarUses___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_FVarUses_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_instAddFVarUses___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_instAddFVarUses___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_instAddFVarUses = (const lean_object*)&l_Lean_Elab_Tactic_Do_instAddFVarUses___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_none_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_none_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_none_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_some_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_some_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_some_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value;
static const lean_array_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "tacticGet_elem_tactic"};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(141, 31, 109, 153, 11, 229, 201, 51)}};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__11_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "get_elem_tactic"};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__12_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_pop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_pop___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_pop___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_pop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_pop___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_Do_BVarUses_add___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_add___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_add___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_add___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_add(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_add___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instAddBVarUses(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_over1Of2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_over1Of2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addMData___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addMData___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_addMData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_addMData___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_addMData___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_addMData___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addMData(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_countUsesDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "uses"};
static const lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(183, 67, 224, 192, 49, 118, 23, 147)}};
static const lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3;
static const lean_closure_object l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_countUsesDecl___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_countUses___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "BVar index out of bounds: "};
static const lean_object* l_Lean_Elab_Tactic_Do_countUses___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_countUses___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_countUses___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_countUses___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Do_countUses___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " >= "};
static const lean_object* l_Lean_Elab_Tactic_Do_countUses___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_countUses___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_countUses___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_countUses___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_Do_countUses___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l_Lean_Elab_Tactic_Do_countUses___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_countUses___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_countUses___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_countUses___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesLCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesLCtx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_doNotDup(uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_doNotDup___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "transform"};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___closed__0_value;
static const lean_array_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_elimLetsCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elimLetsCore___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elimLets___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_elimLets___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elimLets___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Elab_Tactic_Do_Uses_ctorIdx(v_x_boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_toCtorIdx(uint8_t v_x_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_Elab_Tactic_Do_Uses_ctorIdx(v_x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_toCtorIdx___boxed(lean_object* v_x_10_){
_start:
{
uint8_t v_x_4__boxed_11_; lean_object* v_res_12_; 
v_x_4__boxed_11_ = lean_unbox(v_x_10_);
v_res_12_ = l_Lean_Elab_Tactic_Do_Uses_toCtorIdx(v_x_4__boxed_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim___redArg(lean_object* v_k_13_){
_start:
{
lean_inc(v_k_13_);
return v_k_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim___redArg___boxed(lean_object* v_k_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lean_Elab_Tactic_Do_Uses_ctorElim___redArg(v_k_14_);
lean_dec(v_k_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, uint8_t v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_inc(v_k_20_);
return v_k_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
uint8_t v_t_boxed_26_; lean_object* v_res_27_; 
v_t_boxed_26_ = lean_unbox(v_t_23_);
v_res_27_ = l_Lean_Elab_Tactic_Do_Uses_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_boxed_26_, v_h_24_, v_k_25_);
lean_dec(v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim___redArg(lean_object* v_zero_28_){
_start:
{
lean_inc(v_zero_28_);
return v_zero_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim___redArg___boxed(lean_object* v_zero_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Elab_Tactic_Do_Uses_zero_elim___redArg(v_zero_29_);
lean_dec(v_zero_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim(lean_object* v_motive_31_, uint8_t v_t_32_, lean_object* v_h_33_, lean_object* v_zero_34_){
_start:
{
lean_inc(v_zero_34_);
return v_zero_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim___boxed(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_zero_38_){
_start:
{
uint8_t v_t_boxed_39_; lean_object* v_res_40_; 
v_t_boxed_39_ = lean_unbox(v_t_36_);
v_res_40_ = l_Lean_Elab_Tactic_Do_Uses_zero_elim(v_motive_35_, v_t_boxed_39_, v_h_37_, v_zero_38_);
lean_dec(v_zero_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim___redArg(lean_object* v_one_41_){
_start:
{
lean_inc(v_one_41_);
return v_one_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim___redArg___boxed(lean_object* v_one_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Elab_Tactic_Do_Uses_one_elim___redArg(v_one_42_);
lean_dec(v_one_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim(lean_object* v_motive_44_, uint8_t v_t_45_, lean_object* v_h_46_, lean_object* v_one_47_){
_start:
{
lean_inc(v_one_47_);
return v_one_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim___boxed(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_one_51_){
_start:
{
uint8_t v_t_boxed_52_; lean_object* v_res_53_; 
v_t_boxed_52_ = lean_unbox(v_t_49_);
v_res_53_ = l_Lean_Elab_Tactic_Do_Uses_one_elim(v_motive_48_, v_t_boxed_52_, v_h_50_, v_one_51_);
lean_dec(v_one_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim___redArg(lean_object* v_many_54_){
_start:
{
lean_inc(v_many_54_);
return v_many_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim___redArg___boxed(lean_object* v_many_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_Elab_Tactic_Do_Uses_many_elim___redArg(v_many_55_);
lean_dec(v_many_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim(lean_object* v_motive_57_, uint8_t v_t_58_, lean_object* v_h_59_, lean_object* v_many_60_){
_start:
{
lean_inc(v_many_60_);
return v_many_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim___boxed(lean_object* v_motive_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_many_64_){
_start:
{
uint8_t v_t_boxed_65_; lean_object* v_res_66_; 
v_t_boxed_65_ = lean_unbox(v_t_62_);
v_res_66_ = l_Lean_Elab_Tactic_Do_Uses_many_elim(v_motive_61_, v_t_boxed_65_, v_h_63_, v_many_64_);
lean_dec(v_many_64_);
return v_res_66_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_instBEqUses_beq(uint8_t v_x_67_, uint8_t v_y_68_){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; uint8_t v___x_71_; 
v___x_69_ = l_Lean_Elab_Tactic_Do_Uses_ctorIdx(v_x_67_);
v___x_70_ = l_Lean_Elab_Tactic_Do_Uses_ctorIdx(v_y_68_);
v___x_71_ = lean_nat_dec_eq(v___x_69_, v___x_70_);
lean_dec(v___x_70_);
lean_dec(v___x_69_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instBEqUses_beq___boxed(lean_object* v_x_72_, lean_object* v_y_73_){
_start:
{
uint8_t v_x_17__boxed_74_; uint8_t v_y_18__boxed_75_; uint8_t v_res_76_; lean_object* v_r_77_; 
v_x_17__boxed_74_ = lean_unbox(v_x_72_);
v_y_18__boxed_75_ = lean_unbox(v_y_73_);
v_res_76_ = l_Lean_Elab_Tactic_Do_instBEqUses_beq(v_x_17__boxed_74_, v_y_18__boxed_75_);
v_r_77_ = lean_box(v_res_76_);
return v_r_77_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_instOrdUses_ord(uint8_t v_x_80_, uint8_t v_y_81_){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_82_ = l_Lean_Elab_Tactic_Do_Uses_ctorIdx(v_x_80_);
v___x_83_ = l_Lean_Elab_Tactic_Do_Uses_ctorIdx(v_y_81_);
v___x_84_ = lean_nat_dec_lt(v___x_82_, v___x_83_);
if (v___x_84_ == 0)
{
uint8_t v___x_85_; 
v___x_85_ = lean_nat_dec_eq(v___x_82_, v___x_83_);
lean_dec(v___x_83_);
lean_dec(v___x_82_);
if (v___x_85_ == 0)
{
uint8_t v___x_86_; 
v___x_86_ = 2;
return v___x_86_;
}
else
{
uint8_t v___x_87_; 
v___x_87_ = 1;
return v___x_87_;
}
}
else
{
uint8_t v___x_88_; 
lean_dec(v___x_83_);
lean_dec(v___x_82_);
v___x_88_ = 0;
return v___x_88_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instOrdUses_ord___boxed(lean_object* v_x_89_, lean_object* v_y_90_){
_start:
{
uint8_t v_x_30__boxed_91_; uint8_t v_y_31__boxed_92_; uint8_t v_res_93_; lean_object* v_r_94_; 
v_x_30__boxed_91_ = lean_unbox(v_x_89_);
v_y_31__boxed_92_ = lean_unbox(v_y_90_);
v_res_93_ = l_Lean_Elab_Tactic_Do_instOrdUses_ord(v_x_30__boxed_91_, v_y_31__boxed_92_);
v_r_94_ = lean_box(v_res_93_);
return v_r_94_;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_Do_instInhabitedUses_default(void){
_start:
{
uint8_t v___x_97_; 
v___x_97_ = 0;
return v___x_97_;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_Do_instInhabitedUses(void){
_start:
{
uint8_t v___x_98_; 
v___x_98_ = 0;
return v___x_98_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_Uses_add(uint8_t v_x_99_, uint8_t v_x_100_){
_start:
{
if (v_x_99_ == 0)
{
return v_x_100_;
}
else
{
if (v_x_100_ == 0)
{
return v_x_99_;
}
else
{
uint8_t v___x_101_; 
v___x_101_ = 2;
return v___x_101_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_add___boxed(lean_object* v_x_102_, lean_object* v_x_103_){
_start:
{
uint8_t v_x_30__boxed_104_; uint8_t v_x_31__boxed_105_; uint8_t v_res_106_; lean_object* v_r_107_; 
v_x_30__boxed_104_ = lean_unbox(v_x_102_);
v_x_31__boxed_105_ = lean_unbox(v_x_103_);
v_res_106_ = l_Lean_Elab_Tactic_Do_Uses_add(v_x_30__boxed_104_, v_x_31__boxed_105_);
v_r_107_ = lean_box(v_res_106_);
return v_r_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_toNat(uint8_t v_x_108_){
_start:
{
switch(v_x_108_)
{
case 0:
{
lean_object* v___x_109_; 
v___x_109_ = lean_unsigned_to_nat(0u);
return v___x_109_;
}
case 1:
{
lean_object* v___x_110_; 
v___x_110_ = lean_unsigned_to_nat(1u);
return v___x_110_;
}
default: 
{
lean_object* v___x_111_; 
v___x_111_ = lean_unsigned_to_nat(2u);
return v___x_111_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_toNat___boxed(lean_object* v_x_112_){
_start:
{
uint8_t v_x_34__boxed_113_; lean_object* v_res_114_; 
v_x_34__boxed_113_ = lean_unbox(v_x_112_);
v_res_114_ = l_Lean_Elab_Tactic_Do_Uses_toNat(v_x_34__boxed_113_);
return v_res_114_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_Uses_fromNat(lean_object* v_x_115_){
_start:
{
lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_116_ = lean_unsigned_to_nat(0u);
v___x_117_ = lean_nat_dec_eq(v_x_115_, v___x_116_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_118_ = lean_unsigned_to_nat(1u);
v___x_119_ = lean_nat_dec_eq(v_x_115_, v___x_118_);
if (v___x_119_ == 0)
{
uint8_t v___x_120_; 
v___x_120_ = 2;
return v___x_120_;
}
else
{
uint8_t v___x_121_; 
v___x_121_ = 1;
return v___x_121_;
}
}
else
{
uint8_t v___x_122_; 
v___x_122_ = 0;
return v___x_122_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_fromNat___boxed(lean_object* v_x_123_){
_start:
{
uint8_t v_res_124_; lean_object* v_r_125_; 
v_res_124_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v_x_123_);
lean_dec(v_x_123_);
v_r_125_ = lean_box(v_res_124_);
return v_r_125_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_x_128_, lean_object* v_x_129_){
_start:
{
if (lean_obj_tag(v_x_129_) == 0)
{
return v_x_128_;
}
else
{
lean_object* v_key_130_; lean_object* v_value_131_; lean_object* v_tail_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_155_; 
v_key_130_ = lean_ctor_get(v_x_129_, 0);
v_value_131_ = lean_ctor_get(v_x_129_, 1);
v_tail_132_ = lean_ctor_get(v_x_129_, 2);
v_isSharedCheck_155_ = !lean_is_exclusive(v_x_129_);
if (v_isSharedCheck_155_ == 0)
{
v___x_134_ = v_x_129_;
v_isShared_135_ = v_isSharedCheck_155_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_tail_132_);
lean_inc(v_value_131_);
lean_inc(v_key_130_);
lean_dec(v_x_129_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_155_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_136_; uint64_t v___x_137_; uint64_t v___x_138_; uint64_t v___x_139_; uint64_t v_fold_140_; uint64_t v___x_141_; uint64_t v___x_142_; uint64_t v___x_143_; size_t v___x_144_; size_t v___x_145_; size_t v___x_146_; size_t v___x_147_; size_t v___x_148_; lean_object* v___x_149_; lean_object* v___x_151_; 
v___x_136_ = lean_array_get_size(v_x_128_);
v___x_137_ = l_Lean_instHashableFVarId_hash(v_key_130_);
v___x_138_ = 32ULL;
v___x_139_ = lean_uint64_shift_right(v___x_137_, v___x_138_);
v_fold_140_ = lean_uint64_xor(v___x_137_, v___x_139_);
v___x_141_ = 16ULL;
v___x_142_ = lean_uint64_shift_right(v_fold_140_, v___x_141_);
v___x_143_ = lean_uint64_xor(v_fold_140_, v___x_142_);
v___x_144_ = lean_uint64_to_usize(v___x_143_);
v___x_145_ = lean_usize_of_nat(v___x_136_);
v___x_146_ = ((size_t)1ULL);
v___x_147_ = lean_usize_sub(v___x_145_, v___x_146_);
v___x_148_ = lean_usize_land(v___x_144_, v___x_147_);
v___x_149_ = lean_array_uget_borrowed(v_x_128_, v___x_148_);
lean_inc(v___x_149_);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 2, v___x_149_);
v___x_151_ = v___x_134_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_key_130_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v_value_131_);
lean_ctor_set(v_reuseFailAlloc_154_, 2, v___x_149_);
v___x_151_ = v_reuseFailAlloc_154_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
lean_object* v___x_152_; 
v___x_152_ = lean_array_uset(v_x_128_, v___x_148_, v___x_151_);
v_x_128_ = v___x_152_;
v_x_129_ = v_tail_132_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2___redArg(lean_object* v_i_156_, lean_object* v_source_157_, lean_object* v_target_158_){
_start:
{
lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_159_ = lean_array_get_size(v_source_157_);
v___x_160_ = lean_nat_dec_lt(v_i_156_, v___x_159_);
if (v___x_160_ == 0)
{
lean_dec_ref(v_source_157_);
lean_dec(v_i_156_);
return v_target_158_;
}
else
{
lean_object* v_es_161_; lean_object* v___x_162_; lean_object* v_source_163_; lean_object* v_target_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v_es_161_ = lean_array_fget(v_source_157_, v_i_156_);
v___x_162_ = lean_box(0);
v_source_163_ = lean_array_fset(v_source_157_, v_i_156_, v___x_162_);
v_target_164_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5___redArg(v_target_158_, v_es_161_);
v___x_165_ = lean_unsigned_to_nat(1u);
v___x_166_ = lean_nat_add(v_i_156_, v___x_165_);
lean_dec(v_i_156_);
v_i_156_ = v___x_166_;
v_source_157_ = v_source_163_;
v_target_158_ = v_target_164_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1___redArg(lean_object* v_data_168_){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v_nbuckets_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_169_ = lean_array_get_size(v_data_168_);
v___x_170_ = lean_unsigned_to_nat(2u);
v_nbuckets_171_ = lean_nat_mul(v___x_169_, v___x_170_);
v___x_172_ = lean_unsigned_to_nat(0u);
v___x_173_ = lean_box(0);
v___x_174_ = lean_mk_array(v_nbuckets_171_, v___x_173_);
v___x_175_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2___redArg(v___x_172_, v_data_168_, v___x_174_);
return v___x_175_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(lean_object* v_a_176_, lean_object* v_x_177_){
_start:
{
if (lean_obj_tag(v_x_177_) == 0)
{
uint8_t v___x_178_; 
v___x_178_ = 0;
return v___x_178_;
}
else
{
lean_object* v_key_179_; lean_object* v_tail_180_; uint8_t v___x_181_; 
v_key_179_ = lean_ctor_get(v_x_177_, 0);
v_tail_180_ = lean_ctor_get(v_x_177_, 2);
v___x_181_ = l_Lean_instBEqFVarId_beq(v_key_179_, v_a_176_);
if (v___x_181_ == 0)
{
v_x_177_ = v_tail_180_;
goto _start;
}
else
{
return v___x_181_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg___boxed(lean_object* v_a_183_, lean_object* v_x_184_){
_start:
{
uint8_t v_res_185_; lean_object* v_r_186_; 
v_res_185_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_183_, v_x_184_);
lean_dec(v_x_184_);
lean_dec(v_a_183_);
v_r_186_ = lean_box(v_res_185_);
return v_r_186_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0(uint8_t v_x3_187_, lean_object* v_x_188_){
_start:
{
if (lean_obj_tag(v_x_188_) == 0)
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = lean_box(v_x3_187_);
v___x_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
return v___x_190_;
}
else
{
lean_object* v_val_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_201_; 
v_val_191_ = lean_ctor_get(v_x_188_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v_x_188_);
if (v_isSharedCheck_201_ == 0)
{
v___x_193_ = v_x_188_;
v_isShared_194_ = v_isSharedCheck_201_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_val_191_);
lean_dec(v_x_188_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_201_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
uint8_t v___x_195_; uint8_t v___x_196_; lean_object* v___x_197_; lean_object* v___x_199_; 
v___x_195_ = lean_unbox(v_val_191_);
lean_dec(v_val_191_);
v___x_196_ = l_Lean_Elab_Tactic_Do_Uses_add(v_x3_187_, v___x_195_);
v___x_197_ = lean_box(v___x_196_);
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 0, v___x_197_);
v___x_199_ = v___x_193_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_197_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0___boxed(lean_object* v_x3_202_, lean_object* v_x_203_){
_start:
{
uint8_t v_x3_854__boxed_204_; lean_object* v_res_205_; 
v_x3_854__boxed_204_ = lean_unbox(v_x3_202_);
v_res_205_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0(v_x3_854__boxed_204_, v_x_203_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2(uint8_t v_x3_206_, lean_object* v_a_207_, lean_object* v_x_208_){
_start:
{
if (lean_obj_tag(v_x_208_) == 0)
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v_val_211_; lean_object* v___x_212_; 
v___x_209_ = lean_box(0);
v___x_210_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0(v_x3_206_, v___x_209_);
v_val_211_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_val_211_);
lean_dec(v___x_210_);
v___x_212_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_212_, 0, v_a_207_);
lean_ctor_set(v___x_212_, 1, v_val_211_);
lean_ctor_set(v___x_212_, 2, v_x_208_);
return v___x_212_;
}
else
{
lean_object* v_key_213_; lean_object* v_value_214_; lean_object* v_tail_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_230_; 
v_key_213_ = lean_ctor_get(v_x_208_, 0);
v_value_214_ = lean_ctor_get(v_x_208_, 1);
v_tail_215_ = lean_ctor_get(v_x_208_, 2);
v_isSharedCheck_230_ = !lean_is_exclusive(v_x_208_);
if (v_isSharedCheck_230_ == 0)
{
v___x_217_ = v_x_208_;
v_isShared_218_ = v_isSharedCheck_230_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_tail_215_);
lean_inc(v_value_214_);
lean_inc(v_key_213_);
lean_dec(v_x_208_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_230_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
uint8_t v___x_219_; 
v___x_219_ = l_Lean_instBEqFVarId_beq(v_key_213_, v_a_207_);
if (v___x_219_ == 0)
{
lean_object* v_tail_220_; lean_object* v___x_222_; 
v_tail_220_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2(v_x3_206_, v_a_207_, v_tail_215_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 2, v_tail_220_);
v___x_222_ = v___x_217_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v_key_213_);
lean_ctor_set(v_reuseFailAlloc_223_, 1, v_value_214_);
lean_ctor_set(v_reuseFailAlloc_223_, 2, v_tail_220_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
else
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v_val_226_; lean_object* v___x_228_; 
lean_dec(v_key_213_);
v___x_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_224_, 0, v_value_214_);
v___x_225_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0(v_x3_206_, v___x_224_);
v_val_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_val_226_);
lean_dec(v___x_225_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 1, v_val_226_);
lean_ctor_set(v___x_217_, 0, v_a_207_);
v___x_228_ = v___x_217_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v_a_207_);
lean_ctor_set(v_reuseFailAlloc_229_, 1, v_val_226_);
lean_ctor_set(v_reuseFailAlloc_229_, 2, v_tail_215_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___boxed(lean_object* v_x3_231_, lean_object* v_a_232_, lean_object* v_x_233_){
_start:
{
uint8_t v_x3_886__boxed_234_; lean_object* v_res_235_; 
v_x3_886__boxed_234_ = lean_unbox(v_x3_231_);
v_res_235_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2(v_x3_886__boxed_234_, v_a_232_, v_x_233_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0(uint8_t v_x3_236_, lean_object* v_m_237_, lean_object* v_a_238_){
_start:
{
lean_object* v_size_239_; lean_object* v_buckets_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_289_; 
v_size_239_ = lean_ctor_get(v_m_237_, 0);
v_buckets_240_ = lean_ctor_get(v_m_237_, 1);
v_isSharedCheck_289_ = !lean_is_exclusive(v_m_237_);
if (v_isSharedCheck_289_ == 0)
{
v___x_242_ = v_m_237_;
v_isShared_243_ = v_isSharedCheck_289_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_buckets_240_);
lean_inc(v_size_239_);
lean_dec(v_m_237_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_289_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_244_; uint64_t v___x_245_; uint64_t v___x_246_; uint64_t v___x_247_; uint64_t v_fold_248_; uint64_t v___x_249_; uint64_t v___x_250_; uint64_t v___x_251_; size_t v___x_252_; size_t v___x_253_; size_t v___x_254_; size_t v___x_255_; size_t v___x_256_; lean_object* v_bkt_257_; uint8_t v___x_258_; 
v___x_244_ = lean_array_get_size(v_buckets_240_);
v___x_245_ = l_Lean_instHashableFVarId_hash(v_a_238_);
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
v_bkt_257_ = lean_array_uget_borrowed(v_buckets_240_, v___x_256_);
v___x_258_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_238_, v_bkt_257_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; lean_object* v_size_x27_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v_buckets_x27_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_259_ = lean_unsigned_to_nat(1u);
v_size_x27_260_ = lean_nat_add(v_size_239_, v___x_259_);
lean_dec(v_size_239_);
v___x_261_ = lean_box(v_x3_236_);
lean_inc(v_bkt_257_);
v___x_262_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_262_, 0, v_a_238_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
lean_ctor_set(v___x_262_, 2, v_bkt_257_);
v_buckets_x27_263_ = lean_array_uset(v_buckets_240_, v___x_256_, v___x_262_);
v___x_264_ = lean_unsigned_to_nat(4u);
v___x_265_ = lean_nat_mul(v_size_x27_260_, v___x_264_);
v___x_266_ = lean_unsigned_to_nat(3u);
v___x_267_ = lean_nat_div(v___x_265_, v___x_266_);
lean_dec(v___x_265_);
v___x_268_ = lean_array_get_size(v_buckets_x27_263_);
v___x_269_ = lean_nat_dec_le(v___x_267_, v___x_268_);
lean_dec(v___x_267_);
if (v___x_269_ == 0)
{
lean_object* v_val_270_; lean_object* v___x_272_; 
v_val_270_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1___redArg(v_buckets_x27_263_);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 1, v_val_270_);
lean_ctor_set(v___x_242_, 0, v_size_x27_260_);
v___x_272_ = v___x_242_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_size_x27_260_);
lean_ctor_set(v_reuseFailAlloc_273_, 1, v_val_270_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
else
{
lean_object* v___x_275_; 
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 1, v_buckets_x27_263_);
lean_ctor_set(v___x_242_, 0, v_size_x27_260_);
v___x_275_ = v___x_242_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_size_x27_260_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v_buckets_x27_263_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
else
{
lean_object* v___x_277_; lean_object* v_buckets_x27_278_; lean_object* v_bkt_x27_279_; lean_object* v___y_281_; uint8_t v___x_286_; 
lean_inc(v_bkt_257_);
v___x_277_ = lean_box(0);
v_buckets_x27_278_ = lean_array_uset(v_buckets_240_, v___x_256_, v___x_277_);
lean_inc(v_a_238_);
v_bkt_x27_279_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2(v_x3_236_, v_a_238_, v_bkt_257_);
v___x_286_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_238_, v_bkt_x27_279_);
lean_dec(v_a_238_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = lean_unsigned_to_nat(1u);
v___x_288_ = lean_nat_sub(v_size_239_, v___x_287_);
lean_dec(v_size_239_);
v___y_281_ = v___x_288_;
goto v___jp_280_;
}
else
{
v___y_281_ = v_size_239_;
goto v___jp_280_;
}
v___jp_280_:
{
lean_object* v___x_282_; lean_object* v___x_284_; 
v___x_282_ = lean_array_uset(v_buckets_x27_278_, v___x_256_, v_bkt_x27_279_);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 1, v___x_282_);
lean_ctor_set(v___x_242_, 0, v___y_281_);
v___x_284_ = v___x_242_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___y_281_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v___x_282_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0___boxed(lean_object* v_x3_290_, lean_object* v_m_291_, lean_object* v_a_292_){
_start:
{
uint8_t v_x3_934__boxed_293_; lean_object* v_res_294_; 
v_x3_934__boxed_293_ = lean_unbox(v_x3_290_);
v_res_294_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0(v_x3_934__boxed_293_, v_m_291_, v_a_292_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1(lean_object* v_x_295_, lean_object* v_x_296_){
_start:
{
if (lean_obj_tag(v_x_296_) == 0)
{
return v_x_295_;
}
else
{
lean_object* v_key_297_; lean_object* v_value_298_; lean_object* v_tail_299_; uint8_t v___x_300_; lean_object* v___x_301_; 
v_key_297_ = lean_ctor_get(v_x_296_, 0);
lean_inc(v_key_297_);
v_value_298_ = lean_ctor_get(v_x_296_, 1);
lean_inc(v_value_298_);
v_tail_299_ = lean_ctor_get(v_x_296_, 2);
lean_inc(v_tail_299_);
lean_dec_ref(v_x_296_);
v___x_300_ = lean_unbox(v_value_298_);
lean_dec(v_value_298_);
v___x_301_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0(v___x_300_, v_x_295_, v_key_297_);
v_x_295_ = v___x_301_;
v_x_296_ = v_tail_299_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(lean_object* v_as_303_, size_t v_i_304_, size_t v_stop_305_, lean_object* v_b_306_){
_start:
{
uint8_t v___x_307_; 
v___x_307_ = lean_usize_dec_eq(v_i_304_, v_stop_305_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; lean_object* v___x_309_; size_t v___x_310_; size_t v___x_311_; 
v___x_308_ = lean_array_uget_borrowed(v_as_303_, v_i_304_);
lean_inc(v___x_308_);
v___x_309_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1(v_b_306_, v___x_308_);
v___x_310_ = ((size_t)1ULL);
v___x_311_ = lean_usize_add(v_i_304_, v___x_310_);
v_i_304_ = v___x_311_;
v_b_306_ = v___x_309_;
goto _start;
}
else
{
return v_b_306_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2___boxed(lean_object* v_as_313_, lean_object* v_i_314_, lean_object* v_stop_315_, lean_object* v_b_316_){
_start:
{
size_t v_i_boxed_317_; size_t v_stop_boxed_318_; lean_object* v_res_319_; 
v_i_boxed_317_ = lean_unbox_usize(v_i_314_);
lean_dec(v_i_314_);
v_stop_boxed_318_ = lean_unbox_usize(v_stop_315_);
lean_dec(v_stop_315_);
v_res_319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(v_as_313_, v_i_boxed_317_, v_stop_boxed_318_, v_b_316_);
lean_dec_ref(v_as_313_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_FVarUses_add(lean_object* v_a_320_, lean_object* v_b_321_){
_start:
{
lean_object* v_buckets_322_; lean_object* v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; 
v_buckets_322_ = lean_ctor_get(v_a_320_, 1);
v___x_323_ = lean_unsigned_to_nat(0u);
v___x_324_ = lean_array_get_size(v_buckets_322_);
v___x_325_ = lean_nat_dec_lt(v___x_323_, v___x_324_);
if (v___x_325_ == 0)
{
return v_b_321_;
}
else
{
uint8_t v___x_326_; 
v___x_326_ = lean_nat_dec_le(v___x_324_, v___x_324_);
if (v___x_326_ == 0)
{
if (v___x_325_ == 0)
{
return v_b_321_;
}
else
{
size_t v___x_327_; size_t v___x_328_; lean_object* v___x_329_; 
v___x_327_ = ((size_t)0ULL);
v___x_328_ = lean_usize_of_nat(v___x_324_);
v___x_329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(v_buckets_322_, v___x_327_, v___x_328_, v_b_321_);
return v___x_329_;
}
}
else
{
size_t v___x_330_; size_t v___x_331_; lean_object* v___x_332_; 
v___x_330_ = ((size_t)0ULL);
v___x_331_ = lean_usize_of_nat(v___x_324_);
v___x_332_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(v_buckets_322_, v___x_330_, v___x_331_, v_b_321_);
return v___x_332_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_FVarUses_add___boxed(lean_object* v_a_333_, lean_object* v_b_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_a_333_, v_b_334_);
lean_dec_ref(v_a_333_);
return v_res_335_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0(lean_object* v_00_u03b2_336_, lean_object* v_a_337_, lean_object* v_x_338_){
_start:
{
uint8_t v___x_339_; 
v___x_339_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_337_, v_x_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___boxed(lean_object* v_00_u03b2_340_, lean_object* v_a_341_, lean_object* v_x_342_){
_start:
{
uint8_t v_res_343_; lean_object* v_r_344_; 
v_res_343_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0(v_00_u03b2_340_, v_a_341_, v_x_342_);
lean_dec(v_x_342_);
lean_dec(v_a_341_);
v_r_344_ = lean_box(v_res_343_);
return v_r_344_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1(lean_object* v_00_u03b2_345_, lean_object* v_data_346_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1___redArg(v_data_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_348_, lean_object* v_i_349_, lean_object* v_source_350_, lean_object* v_target_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2___redArg(v_i_349_, v_source_350_, v_target_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_353_, lean_object* v_x_354_, lean_object* v_x_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5___redArg(v_x_354_, v_x_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___redArg(lean_object* v_x_359_){
_start:
{
if (lean_obj_tag(v_x_359_) == 0)
{
lean_object* v___x_360_; 
v___x_360_ = lean_unsigned_to_nat(0u);
return v___x_360_;
}
else
{
lean_object* v___x_361_; 
v___x_361_ = lean_unsigned_to_nat(1u);
return v___x_361_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___redArg___boxed(lean_object* v_x_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___redArg(v_x_362_);
lean_dec(v_x_362_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx(lean_object* v_n_364_, lean_object* v_x_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___redArg(v_x_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___boxed(lean_object* v_n_367_, lean_object* v_x_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx(v_n_367_, v_x_368_);
lean_dec(v_x_368_);
lean_dec(v_n_367_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(lean_object* v_t_370_, lean_object* v_k_371_){
_start:
{
if (lean_obj_tag(v_t_370_) == 0)
{
return v_k_371_;
}
else
{
lean_object* v_uses_372_; lean_object* v___x_373_; 
v_uses_372_ = lean_ctor_get(v_t_370_, 0);
lean_inc_ref(v_uses_372_);
lean_dec_ref(v_t_370_);
v___x_373_ = lean_apply_1(v_k_371_, v_uses_372_);
return v___x_373_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorElim(lean_object* v_n_374_, lean_object* v_motive_375_, lean_object* v_ctorIdx_376_, lean_object* v_t_377_, lean_object* v_h_378_, lean_object* v_k_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_377_, v_k_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___boxed(lean_object* v_n_381_, lean_object* v_motive_382_, lean_object* v_ctorIdx_383_, lean_object* v_t_384_, lean_object* v_h_385_, lean_object* v_k_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim(v_n_381_, v_motive_382_, v_ctorIdx_383_, v_t_384_, v_h_385_, v_k_386_);
lean_dec(v_ctorIdx_383_);
lean_dec(v_n_381_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_none_elim___redArg(lean_object* v_t_388_, lean_object* v_none_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_388_, v_none_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_none_elim(lean_object* v_n_391_, lean_object* v_motive_392_, lean_object* v_t_393_, lean_object* v_h_394_, lean_object* v_none_395_){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_393_, v_none_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_none_elim___boxed(lean_object* v_n_397_, lean_object* v_motive_398_, lean_object* v_t_399_, lean_object* v_h_400_, lean_object* v_none_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Lean_Elab_Tactic_Do_BVarUses_none_elim(v_n_397_, v_motive_398_, v_t_399_, v_h_400_, v_none_401_);
lean_dec(v_n_397_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_some_elim___redArg(lean_object* v_t_403_, lean_object* v_some_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_403_, v_some_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_some_elim(lean_object* v_n_406_, lean_object* v_motive_407_, lean_object* v_t_408_, lean_object* v_h_409_, lean_object* v_some_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_408_, v_some_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_some_elim___boxed(lean_object* v_n_412_, lean_object* v_motive_413_, lean_object* v_t_414_, lean_object* v_h_415_, lean_object* v_some_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_Elab_Tactic_Do_BVarUses_some_elim(v_n_412_, v_motive_413_, v_t_414_, v_h_415_, v_some_416_);
lean_dec(v_n_412_);
return v_res_417_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__12));
v___x_443_ = l_Lean_mkAtom(v___x_442_);
return v___x_443_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14(void){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_444_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13);
v___x_445_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5));
v___x_446_ = lean_array_push(v___x_445_, v___x_444_);
return v___x_446_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15(void){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_447_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14);
v___x_448_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__11));
v___x_449_ = lean_box(2);
v___x_450_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
lean_ctor_set(v___x_450_, 1, v___x_448_);
lean_ctor_set(v___x_450_, 2, v___x_447_);
return v___x_450_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16(void){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_451_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15);
v___x_452_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5));
v___x_453_ = lean_array_push(v___x_452_, v___x_451_);
return v___x_453_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_454_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16);
v___x_455_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__9));
v___x_456_ = lean_box(2);
v___x_457_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
lean_ctor_set(v___x_457_, 1, v___x_455_);
lean_ctor_set(v___x_457_, 2, v___x_454_);
return v___x_457_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_458_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17);
v___x_459_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5));
v___x_460_ = lean_array_push(v___x_459_, v___x_458_);
return v___x_460_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_461_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18);
v___x_462_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7));
v___x_463_ = lean_box(2);
v___x_464_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
lean_ctor_set(v___x_464_, 1, v___x_462_);
lean_ctor_set(v___x_464_, 2, v___x_461_);
return v___x_464_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_465_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19);
v___x_466_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5));
v___x_467_ = lean_array_push(v___x_466_, v___x_465_);
return v___x_467_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_468_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20);
v___x_469_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4));
v___x_470_ = lean_box(2);
v___x_471_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
lean_ctor_set(v___x_471_, 1, v___x_469_);
lean_ctor_set(v___x_471_, 2, v___x_468_);
return v___x_471_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1(void){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21);
return v___x_472_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0(lean_object* v_numBVars_473_, lean_object* v_n_474_, lean_object* v_i_475_){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_476_ = lean_unsigned_to_nat(1u);
v___x_477_ = lean_nat_sub(v_numBVars_473_, v___x_476_);
v___x_478_ = lean_nat_sub(v___x_477_, v_n_474_);
lean_dec(v___x_477_);
v___x_479_ = lean_nat_dec_eq(v_i_475_, v___x_478_);
lean_dec(v___x_478_);
if (v___x_479_ == 0)
{
uint8_t v___x_480_; 
v___x_480_ = 0;
return v___x_480_;
}
else
{
uint8_t v___x_481_; 
v___x_481_ = 1;
return v___x_481_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0___boxed(lean_object* v_numBVars_482_, lean_object* v_n_483_, lean_object* v_i_484_){
_start:
{
uint8_t v_res_485_; lean_object* v_r_486_; 
v_res_485_ = l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0(v_numBVars_482_, v_n_483_, v_i_484_);
lean_dec(v_i_484_);
lean_dec(v_n_483_);
lean_dec(v_numBVars_482_);
v_r_486_ = lean_box(v_res_485_);
return v_r_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___redArg(lean_object* v_numBVars_487_, lean_object* v_n_488_){
_start:
{
lean_object* v___f_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
lean_inc(v_numBVars_487_);
v___f_489_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_489_, 0, v_numBVars_487_);
lean_closure_set(v___f_489_, 1, v_n_488_);
v___x_490_ = l_Array_ofFn___redArg(v_numBVars_487_, v___f_489_);
v___x_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single(lean_object* v_numBVars_492_, lean_object* v_n_493_, lean_object* v_x_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Lean_Elab_Tactic_Do_BVarUses_single___redArg(v_numBVars_492_, v_n_493_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_pop(lean_object* v_numBVars_500_, lean_object* v_x_501_){
_start:
{
if (lean_obj_tag(v_x_501_) == 0)
{
lean_object* v___x_502_; 
v___x_502_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_pop___closed__0));
return v___x_502_;
}
else
{
lean_object* v_uses_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_516_; 
v_uses_503_ = lean_ctor_get(v_x_501_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v_x_501_);
if (v_isSharedCheck_516_ == 0)
{
v___x_505_ = v_x_501_;
v_isShared_506_ = v_isSharedCheck_516_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_uses_503_);
lean_dec(v_x_501_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_516_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_507_ = lean_unsigned_to_nat(1u);
v___x_508_ = lean_nat_add(v_numBVars_500_, v___x_507_);
v___x_509_ = lean_nat_sub(v___x_508_, v___x_507_);
lean_dec(v___x_508_);
v___x_510_ = lean_array_fget(v_uses_503_, v___x_509_);
lean_dec(v___x_509_);
v___x_511_ = lean_array_pop(v_uses_503_);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v___x_511_);
v___x_513_ = v___x_505_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_511_);
v___x_513_ = v_reuseFailAlloc_515_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
lean_object* v___x_514_; 
v___x_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_510_);
lean_ctor_set(v___x_514_, 1, v___x_513_);
return v___x_514_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_pop___boxed(lean_object* v_numBVars_517_, lean_object* v_x_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Lean_Elab_Tactic_Do_BVarUses_pop(v_numBVars_517_, v_x_518_);
lean_dec(v_numBVars_517_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0(lean_object* v_as_520_, lean_object* v_bs_521_, lean_object* v_i_522_, lean_object* v_cs_523_){
_start:
{
lean_object* v___x_524_; uint8_t v___x_525_; 
v___x_524_ = lean_array_get_size(v_as_520_);
v___x_525_ = lean_nat_dec_lt(v_i_522_, v___x_524_);
if (v___x_525_ == 0)
{
lean_dec(v_i_522_);
return v_cs_523_;
}
else
{
lean_object* v___x_526_; uint8_t v___x_527_; 
v___x_526_ = lean_array_get_size(v_bs_521_);
v___x_527_ = lean_nat_dec_lt(v_i_522_, v___x_526_);
if (v___x_527_ == 0)
{
lean_dec(v_i_522_);
return v_cs_523_;
}
else
{
lean_object* v_a_528_; lean_object* v_b_529_; uint8_t v___x_530_; uint8_t v___x_531_; uint8_t v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v_a_528_ = lean_array_fget_borrowed(v_as_520_, v_i_522_);
v_b_529_ = lean_array_fget_borrowed(v_bs_521_, v_i_522_);
v___x_530_ = lean_unbox(v_a_528_);
v___x_531_ = lean_unbox(v_b_529_);
v___x_532_ = l_Lean_Elab_Tactic_Do_Uses_add(v___x_530_, v___x_531_);
v___x_533_ = lean_unsigned_to_nat(1u);
v___x_534_ = lean_nat_add(v_i_522_, v___x_533_);
lean_dec(v_i_522_);
v___x_535_ = lean_box(v___x_532_);
v___x_536_ = lean_array_push(v_cs_523_, v___x_535_);
v_i_522_ = v___x_534_;
v_cs_523_ = v___x_536_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0___boxed(lean_object* v_as_538_, lean_object* v_bs_539_, lean_object* v_i_540_, lean_object* v_cs_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0(v_as_538_, v_bs_539_, v_i_540_, v_cs_541_);
lean_dec_ref(v_bs_539_);
lean_dec_ref(v_as_538_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_add___redArg(lean_object* v_a_545_, lean_object* v_b_546_){
_start:
{
if (lean_obj_tag(v_a_545_) == 0)
{
return v_b_546_;
}
else
{
if (lean_obj_tag(v_b_546_) == 0)
{
lean_object* v_uses_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
v_uses_547_ = lean_ctor_get(v_a_545_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v_a_545_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v_a_545_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_uses_547_);
lean_dec(v_a_545_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_uses_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
else
{
lean_object* v_uses_555_; lean_object* v_uses_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_566_; 
v_uses_555_ = lean_ctor_get(v_a_545_, 0);
lean_inc_ref(v_uses_555_);
lean_dec_ref(v_a_545_);
v_uses_556_ = lean_ctor_get(v_b_546_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v_b_546_);
if (v_isSharedCheck_566_ == 0)
{
v___x_558_ = v_b_546_;
v_isShared_559_ = v_isSharedCheck_566_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_uses_556_);
lean_dec(v_b_546_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_566_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_564_; 
v___x_560_ = lean_unsigned_to_nat(0u);
v___x_561_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_add___redArg___closed__0));
v___x_562_ = l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0(v_uses_555_, v_uses_556_, v___x_560_, v___x_561_);
lean_dec_ref(v_uses_556_);
lean_dec_ref(v_uses_555_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 0, v___x_562_);
v___x_564_ = v___x_558_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_562_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_add(lean_object* v_numBVars_567_, lean_object* v_a_568_, lean_object* v_b_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Lean_Elab_Tactic_Do_BVarUses_add___redArg(v_a_568_, v_b_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_add___boxed(lean_object* v_numBVars_571_, lean_object* v_a_572_, lean_object* v_b_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Lean_Elab_Tactic_Do_BVarUses_add(v_numBVars_571_, v_a_572_, v_b_573_);
lean_dec(v_numBVars_571_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instAddBVarUses(lean_object* v_numBVars_575_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_BVarUses_add___boxed), 3, 1);
lean_closure_set(v___x_576_, 0, v_numBVars_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_over1Of2___redArg(lean_object* v_f_577_, lean_object* v_x_578_){
_start:
{
lean_object* v_fst_579_; lean_object* v_snd_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_588_; 
v_fst_579_ = lean_ctor_get(v_x_578_, 0);
v_snd_580_ = lean_ctor_get(v_x_578_, 1);
v_isSharedCheck_588_ = !lean_is_exclusive(v_x_578_);
if (v_isSharedCheck_588_ == 0)
{
v___x_582_ = v_x_578_;
v_isShared_583_ = v_isSharedCheck_588_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_snd_580_);
lean_inc(v_fst_579_);
lean_dec(v_x_578_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_588_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_584_; lean_object* v___x_586_; 
v___x_584_ = lean_apply_1(v_f_577_, v_fst_579_);
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 0, v___x_584_);
v___x_586_ = v___x_582_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_584_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v_snd_580_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_over1Of2(lean_object* v_00_u03b1_u2081_589_, lean_object* v_00_u03b1_u2082_590_, lean_object* v_00_u03b2_591_, lean_object* v_f_592_, lean_object* v_x_593_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v_f_592_, v_x_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addMData___lam__0(lean_object* v_x_595_, lean_object* v_new_596_, lean_object* v_x_597_){
_start:
{
lean_inc_ref(v_new_596_);
return v_new_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addMData___lam__0___boxed(lean_object* v_x_598_, lean_object* v_new_599_, lean_object* v_x_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Lean_Elab_Tactic_Do_addMData___lam__0(v_x_598_, v_new_599_, v_x_600_);
lean_dec_ref(v_x_600_);
lean_dec_ref(v_new_599_);
lean_dec(v_x_598_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addMData(lean_object* v_d_603_, lean_object* v_e_604_){
_start:
{
if (lean_obj_tag(v_e_604_) == 10)
{
lean_object* v_data_605_; lean_object* v_expr_606_; lean_object* v___f_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v_data_605_ = lean_ctor_get(v_e_604_, 0);
lean_inc(v_data_605_);
v_expr_606_ = lean_ctor_get(v_e_604_, 1);
lean_inc_ref(v_expr_606_);
lean_dec_ref(v_e_604_);
v___f_607_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_addMData___closed__0));
v___x_608_ = l_Lean_KVMap_mergeBy(v___f_607_, v_d_603_, v_data_605_);
lean_dec(v_data_605_);
v___x_609_ = l_Lean_Expr_mdata___override(v___x_608_, v_expr_606_);
return v___x_609_;
}
else
{
lean_object* v___x_610_; 
v___x_610_ = l_Lean_Expr_mdata___override(v_d_603_, v_e_604_);
return v___x_610_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup(lean_object* v_e_611_){
_start:
{
uint8_t v___y_613_; 
switch(lean_obj_tag(v_e_611_))
{
case 1:
{
uint8_t v___x_615_; 
v___x_615_ = 0;
return v___x_615_;
}
case 5:
{
uint8_t v___x_616_; 
v___x_616_ = l_Lean_Meta_Simp_isOfNatNatLit(v_e_611_);
if (v___x_616_ == 0)
{
uint8_t v___x_617_; 
v___x_617_ = l_Lean_Meta_Simp_isOfScientificLit(v_e_611_);
v___y_613_ = v___x_617_;
goto v___jp_612_;
}
else
{
v___y_613_ = v___x_616_;
goto v___jp_612_;
}
}
case 6:
{
uint8_t v___x_618_; 
v___x_618_ = 0;
return v___x_618_;
}
case 7:
{
uint8_t v___x_619_; 
v___x_619_ = 0;
return v___x_619_;
}
case 8:
{
uint8_t v___x_620_; 
v___x_620_ = 0;
return v___x_620_;
}
case 10:
{
lean_object* v_expr_621_; 
v_expr_621_ = lean_ctor_get(v_e_611_, 1);
v_e_611_ = v_expr_621_;
goto _start;
}
case 11:
{
lean_object* v_struct_623_; 
v_struct_623_ = lean_ctor_get(v_e_611_, 2);
v_e_611_ = v_struct_623_;
goto _start;
}
default: 
{
uint8_t v___x_625_; 
v___x_625_ = 1;
return v___x_625_;
}
}
v___jp_612_:
{
if (v___y_613_ == 0)
{
uint8_t v___x_614_; 
v___x_614_ = l_Lean_Meta_Simp_isCharLit(v_e_611_);
return v___x_614_;
}
else
{
return v___y_613_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup___boxed(lean_object* v_e_626_){
_start:
{
uint8_t v_res_627_; lean_object* v_r_628_; 
v_res_627_ = l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup(v_e_626_);
lean_dec_ref(v_e_626_);
v_r_628_ = lean_box(v_res_627_);
return v_r_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___lam__0(lean_object* v_val_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_630_, 0, v_val_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5(lean_object* v_msgData_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
lean_object* v___x_637_; lean_object* v_env_638_; lean_object* v___x_639_; lean_object* v_mctx_640_; lean_object* v_lctx_641_; lean_object* v_options_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_637_ = lean_st_ref_get(v___y_635_);
v_env_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc_ref(v_env_638_);
lean_dec(v___x_637_);
v___x_639_ = lean_st_ref_get(v___y_633_);
v_mctx_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc_ref(v_mctx_640_);
lean_dec(v___x_639_);
v_lctx_641_ = lean_ctor_get(v___y_632_, 2);
v_options_642_ = lean_ctor_get(v___y_634_, 2);
lean_inc_ref(v_options_642_);
lean_inc_ref(v_lctx_641_);
v___x_643_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_643_, 0, v_env_638_);
lean_ctor_set(v___x_643_, 1, v_mctx_640_);
lean_ctor_set(v___x_643_, 2, v_lctx_641_);
lean_ctor_set(v___x_643_, 3, v_options_642_);
v___x_644_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
lean_ctor_set(v___x_644_, 1, v_msgData_631_);
v___x_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5___boxed(lean_object* v_msgData_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5(v_msgData_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(lean_object* v_msg_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
lean_object* v_ref_659_; lean_object* v___x_660_; lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_669_; 
v_ref_659_ = lean_ctor_get(v___y_656_, 5);
v___x_660_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5(v_msg_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
v_a_661_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_669_ == 0)
{
v___x_663_ = v___x_660_;
v_isShared_664_ = v_isSharedCheck_669_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_660_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_669_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_665_; lean_object* v___x_667_; 
lean_inc(v_ref_659_);
v___x_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_665_, 0, v_ref_659_);
lean_ctor_set(v___x_665_, 1, v_a_661_);
if (v_isShared_664_ == 0)
{
lean_ctor_set_tag(v___x_663_, 1);
lean_ctor_set(v___x_663_, 0, v___x_665_);
v___x_667_ = v___x_663_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_665_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg___boxed(lean_object* v_msg_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v_msg_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses___lam__0(lean_object* v_data_677_, lean_object* v_expr_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Lean_Expr_mdata___override(v_data_677_, v_expr_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses___lam__1(lean_object* v_typeName_680_, lean_object* v_idx_681_, lean_object* v_struct_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Lean_Expr_proj___override(v_typeName_680_, v_idx_681_, v_struct_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(lean_object* v_a_684_, lean_object* v_b_685_, lean_object* v_x_686_){
_start:
{
if (lean_obj_tag(v_x_686_) == 0)
{
lean_dec(v_b_685_);
lean_dec(v_a_684_);
return v_x_686_;
}
else
{
lean_object* v_key_687_; lean_object* v_value_688_; lean_object* v_tail_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_701_; 
v_key_687_ = lean_ctor_get(v_x_686_, 0);
v_value_688_ = lean_ctor_get(v_x_686_, 1);
v_tail_689_ = lean_ctor_get(v_x_686_, 2);
v_isSharedCheck_701_ = !lean_is_exclusive(v_x_686_);
if (v_isSharedCheck_701_ == 0)
{
v___x_691_ = v_x_686_;
v_isShared_692_ = v_isSharedCheck_701_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_tail_689_);
lean_inc(v_value_688_);
lean_inc(v_key_687_);
lean_dec(v_x_686_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_701_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
uint8_t v___x_693_; 
v___x_693_ = l_Lean_instBEqFVarId_beq(v_key_687_, v_a_684_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; lean_object* v___x_696_; 
v___x_694_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(v_a_684_, v_b_685_, v_tail_689_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 2, v___x_694_);
v___x_696_ = v___x_691_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_key_687_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v_value_688_);
lean_ctor_set(v_reuseFailAlloc_697_, 2, v___x_694_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
else
{
lean_object* v___x_699_; 
lean_dec(v_value_688_);
lean_dec(v_key_687_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 1, v_b_685_);
lean_ctor_set(v___x_691_, 0, v_a_684_);
v___x_699_ = v___x_691_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_684_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_b_685_);
lean_ctor_set(v_reuseFailAlloc_700_, 2, v_tail_689_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(lean_object* v_m_702_, lean_object* v_a_703_, lean_object* v_b_704_){
_start:
{
lean_object* v_size_705_; lean_object* v_buckets_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_749_; 
v_size_705_ = lean_ctor_get(v_m_702_, 0);
v_buckets_706_ = lean_ctor_get(v_m_702_, 1);
v_isSharedCheck_749_ = !lean_is_exclusive(v_m_702_);
if (v_isSharedCheck_749_ == 0)
{
v___x_708_ = v_m_702_;
v_isShared_709_ = v_isSharedCheck_749_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_buckets_706_);
lean_inc(v_size_705_);
lean_dec(v_m_702_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_749_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_710_; uint64_t v___x_711_; uint64_t v___x_712_; uint64_t v___x_713_; uint64_t v_fold_714_; uint64_t v___x_715_; uint64_t v___x_716_; uint64_t v___x_717_; size_t v___x_718_; size_t v___x_719_; size_t v___x_720_; size_t v___x_721_; size_t v___x_722_; lean_object* v_bkt_723_; uint8_t v___x_724_; 
v___x_710_ = lean_array_get_size(v_buckets_706_);
v___x_711_ = l_Lean_instHashableFVarId_hash(v_a_703_);
v___x_712_ = 32ULL;
v___x_713_ = lean_uint64_shift_right(v___x_711_, v___x_712_);
v_fold_714_ = lean_uint64_xor(v___x_711_, v___x_713_);
v___x_715_ = 16ULL;
v___x_716_ = lean_uint64_shift_right(v_fold_714_, v___x_715_);
v___x_717_ = lean_uint64_xor(v_fold_714_, v___x_716_);
v___x_718_ = lean_uint64_to_usize(v___x_717_);
v___x_719_ = lean_usize_of_nat(v___x_710_);
v___x_720_ = ((size_t)1ULL);
v___x_721_ = lean_usize_sub(v___x_719_, v___x_720_);
v___x_722_ = lean_usize_land(v___x_718_, v___x_721_);
v_bkt_723_ = lean_array_uget_borrowed(v_buckets_706_, v___x_722_);
v___x_724_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_703_, v_bkt_723_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; lean_object* v_size_x27_726_; lean_object* v___x_727_; lean_object* v_buckets_x27_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; uint8_t v___x_734_; 
v___x_725_ = lean_unsigned_to_nat(1u);
v_size_x27_726_ = lean_nat_add(v_size_705_, v___x_725_);
lean_dec(v_size_705_);
lean_inc(v_bkt_723_);
v___x_727_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_727_, 0, v_a_703_);
lean_ctor_set(v___x_727_, 1, v_b_704_);
lean_ctor_set(v___x_727_, 2, v_bkt_723_);
v_buckets_x27_728_ = lean_array_uset(v_buckets_706_, v___x_722_, v___x_727_);
v___x_729_ = lean_unsigned_to_nat(4u);
v___x_730_ = lean_nat_mul(v_size_x27_726_, v___x_729_);
v___x_731_ = lean_unsigned_to_nat(3u);
v___x_732_ = lean_nat_div(v___x_730_, v___x_731_);
lean_dec(v___x_730_);
v___x_733_ = lean_array_get_size(v_buckets_x27_728_);
v___x_734_ = lean_nat_dec_le(v___x_732_, v___x_733_);
lean_dec(v___x_732_);
if (v___x_734_ == 0)
{
lean_object* v_val_735_; lean_object* v___x_737_; 
v_val_735_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1___redArg(v_buckets_x27_728_);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 1, v_val_735_);
lean_ctor_set(v___x_708_, 0, v_size_x27_726_);
v___x_737_ = v___x_708_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_size_x27_726_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v_val_735_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
else
{
lean_object* v___x_740_; 
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 1, v_buckets_x27_728_);
lean_ctor_set(v___x_708_, 0, v_size_x27_726_);
v___x_740_ = v___x_708_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_size_x27_726_);
lean_ctor_set(v_reuseFailAlloc_741_, 1, v_buckets_x27_728_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
else
{
lean_object* v___x_742_; lean_object* v_buckets_x27_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_747_; 
lean_inc(v_bkt_723_);
v___x_742_ = lean_box(0);
v_buckets_x27_743_ = lean_array_uset(v_buckets_706_, v___x_722_, v___x_742_);
v___x_744_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(v_a_703_, v_b_704_, v_bkt_723_);
v___x_745_ = lean_array_uset(v_buckets_x27_743_, v___x_722_, v___x_744_);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 1, v___x_745_);
v___x_747_ = v___x_708_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_size_705_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v___x_745_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(lean_object* v___y_750_){
_start:
{
lean_object* v___x_752_; lean_object* v_ngen_753_; lean_object* v_namePrefix_754_; lean_object* v_idx_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_785_; 
v___x_752_ = lean_st_ref_get(v___y_750_);
v_ngen_753_ = lean_ctor_get(v___x_752_, 2);
lean_inc_ref(v_ngen_753_);
lean_dec(v___x_752_);
v_namePrefix_754_ = lean_ctor_get(v_ngen_753_, 0);
v_idx_755_ = lean_ctor_get(v_ngen_753_, 1);
v_isSharedCheck_785_ = !lean_is_exclusive(v_ngen_753_);
if (v_isSharedCheck_785_ == 0)
{
v___x_757_ = v_ngen_753_;
v_isShared_758_ = v_isSharedCheck_785_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_idx_755_);
lean_inc(v_namePrefix_754_);
lean_dec(v_ngen_753_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_785_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_759_; lean_object* v_env_760_; lean_object* v_nextMacroScope_761_; lean_object* v_auxDeclNGen_762_; lean_object* v_traceState_763_; lean_object* v_cache_764_; lean_object* v_messages_765_; lean_object* v_infoState_766_; lean_object* v_snapshotTasks_767_; lean_object* v_newDecls_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_783_; 
v___x_759_ = lean_st_ref_take(v___y_750_);
v_env_760_ = lean_ctor_get(v___x_759_, 0);
v_nextMacroScope_761_ = lean_ctor_get(v___x_759_, 1);
v_auxDeclNGen_762_ = lean_ctor_get(v___x_759_, 3);
v_traceState_763_ = lean_ctor_get(v___x_759_, 4);
v_cache_764_ = lean_ctor_get(v___x_759_, 5);
v_messages_765_ = lean_ctor_get(v___x_759_, 6);
v_infoState_766_ = lean_ctor_get(v___x_759_, 7);
v_snapshotTasks_767_ = lean_ctor_get(v___x_759_, 8);
v_newDecls_768_ = lean_ctor_get(v___x_759_, 9);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_783_ == 0)
{
lean_object* v_unused_784_; 
v_unused_784_ = lean_ctor_get(v___x_759_, 2);
lean_dec(v_unused_784_);
v___x_770_ = v___x_759_;
v_isShared_771_ = v_isSharedCheck_783_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_newDecls_768_);
lean_inc(v_snapshotTasks_767_);
lean_inc(v_infoState_766_);
lean_inc(v_messages_765_);
lean_inc(v_cache_764_);
lean_inc(v_traceState_763_);
lean_inc(v_auxDeclNGen_762_);
lean_inc(v_nextMacroScope_761_);
lean_inc(v_env_760_);
lean_dec(v___x_759_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_783_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v_r_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_776_; 
lean_inc(v_idx_755_);
lean_inc(v_namePrefix_754_);
v_r_772_ = l_Lean_Name_num___override(v_namePrefix_754_, v_idx_755_);
v___x_773_ = lean_unsigned_to_nat(1u);
v___x_774_ = lean_nat_add(v_idx_755_, v___x_773_);
lean_dec(v_idx_755_);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 1, v___x_774_);
v___x_776_ = v___x_757_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_namePrefix_754_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v___x_774_);
v___x_776_ = v_reuseFailAlloc_782_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
lean_object* v___x_778_; 
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 2, v___x_776_);
v___x_778_ = v___x_770_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_env_760_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v_nextMacroScope_761_);
lean_ctor_set(v_reuseFailAlloc_781_, 2, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_781_, 3, v_auxDeclNGen_762_);
lean_ctor_set(v_reuseFailAlloc_781_, 4, v_traceState_763_);
lean_ctor_set(v_reuseFailAlloc_781_, 5, v_cache_764_);
lean_ctor_set(v_reuseFailAlloc_781_, 6, v_messages_765_);
lean_ctor_set(v_reuseFailAlloc_781_, 7, v_infoState_766_);
lean_ctor_set(v_reuseFailAlloc_781_, 8, v_snapshotTasks_767_);
lean_ctor_set(v_reuseFailAlloc_781_, 9, v_newDecls_768_);
v___x_778_ = v_reuseFailAlloc_781_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = lean_st_ref_set(v___y_750_, v___x_778_);
v___x_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_780_, 0, v_r_772_);
return v___x_780_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg___boxed(lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(v___y_786_);
lean_dec(v___y_786_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
lean_object* v___x_794_; lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
v___x_794_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(v___y_792_);
v_a_795_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_794_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_794_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_795_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5___boxed(lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(v___y_803_, v___y_804_, v___y_805_, v___y_806_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(lean_object* v_a_809_, lean_object* v_x_810_){
_start:
{
if (lean_obj_tag(v_x_810_) == 0)
{
return v_x_810_;
}
else
{
lean_object* v_key_811_; lean_object* v_value_812_; lean_object* v_tail_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_822_; 
v_key_811_ = lean_ctor_get(v_x_810_, 0);
v_value_812_ = lean_ctor_get(v_x_810_, 1);
v_tail_813_ = lean_ctor_get(v_x_810_, 2);
v_isSharedCheck_822_ = !lean_is_exclusive(v_x_810_);
if (v_isSharedCheck_822_ == 0)
{
v___x_815_ = v_x_810_;
v_isShared_816_ = v_isSharedCheck_822_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_tail_813_);
lean_inc(v_value_812_);
lean_inc(v_key_811_);
lean_dec(v_x_810_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_822_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
uint8_t v___x_817_; 
v___x_817_ = l_Lean_instBEqFVarId_beq(v_key_811_, v_a_809_);
if (v___x_817_ == 0)
{
lean_object* v___x_818_; lean_object* v___x_820_; 
v___x_818_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_809_, v_tail_813_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 2, v___x_818_);
v___x_820_ = v___x_815_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_key_811_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_value_812_);
lean_ctor_set(v_reuseFailAlloc_821_, 2, v___x_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
else
{
lean_del_object(v___x_815_);
lean_dec(v_value_812_);
lean_dec(v_key_811_);
return v_tail_813_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg___boxed(lean_object* v_a_823_, lean_object* v_x_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_823_, v_x_824_);
lean_dec(v_a_823_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(lean_object* v_m_826_, lean_object* v_a_827_){
_start:
{
lean_object* v_size_828_; lean_object* v_buckets_829_; lean_object* v___x_830_; uint64_t v___x_831_; uint64_t v___x_832_; uint64_t v___x_833_; uint64_t v_fold_834_; uint64_t v___x_835_; uint64_t v___x_836_; uint64_t v___x_837_; size_t v___x_838_; size_t v___x_839_; size_t v___x_840_; size_t v___x_841_; size_t v___x_842_; lean_object* v_bkt_843_; uint8_t v___x_844_; 
v_size_828_ = lean_ctor_get(v_m_826_, 0);
v_buckets_829_ = lean_ctor_get(v_m_826_, 1);
v___x_830_ = lean_array_get_size(v_buckets_829_);
v___x_831_ = l_Lean_instHashableFVarId_hash(v_a_827_);
v___x_832_ = 32ULL;
v___x_833_ = lean_uint64_shift_right(v___x_831_, v___x_832_);
v_fold_834_ = lean_uint64_xor(v___x_831_, v___x_833_);
v___x_835_ = 16ULL;
v___x_836_ = lean_uint64_shift_right(v_fold_834_, v___x_835_);
v___x_837_ = lean_uint64_xor(v_fold_834_, v___x_836_);
v___x_838_ = lean_uint64_to_usize(v___x_837_);
v___x_839_ = lean_usize_of_nat(v___x_830_);
v___x_840_ = ((size_t)1ULL);
v___x_841_ = lean_usize_sub(v___x_839_, v___x_840_);
v___x_842_ = lean_usize_land(v___x_838_, v___x_841_);
v_bkt_843_ = lean_array_uget_borrowed(v_buckets_829_, v___x_842_);
v___x_844_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_827_, v_bkt_843_);
if (v___x_844_ == 0)
{
return v_m_826_;
}
else
{
lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_857_; 
lean_inc(v_bkt_843_);
lean_inc_ref(v_buckets_829_);
lean_inc(v_size_828_);
v_isSharedCheck_857_ = !lean_is_exclusive(v_m_826_);
if (v_isSharedCheck_857_ == 0)
{
lean_object* v_unused_858_; lean_object* v_unused_859_; 
v_unused_858_ = lean_ctor_get(v_m_826_, 1);
lean_dec(v_unused_858_);
v_unused_859_ = lean_ctor_get(v_m_826_, 0);
lean_dec(v_unused_859_);
v___x_846_ = v_m_826_;
v_isShared_847_ = v_isSharedCheck_857_;
goto v_resetjp_845_;
}
else
{
lean_dec(v_m_826_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_857_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_848_; lean_object* v_buckets_x27_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_855_; 
v___x_848_ = lean_box(0);
v_buckets_x27_849_ = lean_array_uset(v_buckets_829_, v___x_842_, v___x_848_);
v___x_850_ = lean_unsigned_to_nat(1u);
v___x_851_ = lean_nat_sub(v_size_828_, v___x_850_);
lean_dec(v_size_828_);
v___x_852_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_827_, v_bkt_843_);
v___x_853_ = lean_array_uset(v_buckets_x27_849_, v___x_842_, v___x_852_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 1, v___x_853_);
lean_ctor_set(v___x_846_, 0, v___x_851_);
v___x_855_ = v___x_846_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_851_);
lean_ctor_set(v_reuseFailAlloc_856_, 1, v___x_853_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg___boxed(lean_object* v_m_860_, lean_object* v_a_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v_m_860_, v_a_861_);
lean_dec(v_a_861_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(lean_object* v_a_863_, lean_object* v_fallback_864_, lean_object* v_x_865_){
_start:
{
if (lean_obj_tag(v_x_865_) == 0)
{
lean_inc(v_fallback_864_);
return v_fallback_864_;
}
else
{
lean_object* v_key_866_; lean_object* v_value_867_; lean_object* v_tail_868_; uint8_t v___x_869_; 
v_key_866_ = lean_ctor_get(v_x_865_, 0);
v_value_867_ = lean_ctor_get(v_x_865_, 1);
v_tail_868_ = lean_ctor_get(v_x_865_, 2);
v___x_869_ = l_Lean_instBEqFVarId_beq(v_key_866_, v_a_863_);
if (v___x_869_ == 0)
{
v_x_865_ = v_tail_868_;
goto _start;
}
else
{
lean_inc(v_value_867_);
return v_value_867_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg___boxed(lean_object* v_a_871_, lean_object* v_fallback_872_, lean_object* v_x_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(v_a_871_, v_fallback_872_, v_x_873_);
lean_dec(v_x_873_);
lean_dec(v_fallback_872_);
lean_dec(v_a_871_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(lean_object* v_m_875_, lean_object* v_a_876_, lean_object* v_fallback_877_){
_start:
{
lean_object* v_buckets_878_; lean_object* v___x_879_; uint64_t v___x_880_; uint64_t v___x_881_; uint64_t v___x_882_; uint64_t v_fold_883_; uint64_t v___x_884_; uint64_t v___x_885_; uint64_t v___x_886_; size_t v___x_887_; size_t v___x_888_; size_t v___x_889_; size_t v___x_890_; size_t v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v_buckets_878_ = lean_ctor_get(v_m_875_, 1);
v___x_879_ = lean_array_get_size(v_buckets_878_);
v___x_880_ = l_Lean_instHashableFVarId_hash(v_a_876_);
v___x_881_ = 32ULL;
v___x_882_ = lean_uint64_shift_right(v___x_880_, v___x_881_);
v_fold_883_ = lean_uint64_xor(v___x_880_, v___x_882_);
v___x_884_ = 16ULL;
v___x_885_ = lean_uint64_shift_right(v_fold_883_, v___x_884_);
v___x_886_ = lean_uint64_xor(v_fold_883_, v___x_885_);
v___x_887_ = lean_uint64_to_usize(v___x_886_);
v___x_888_ = lean_usize_of_nat(v___x_879_);
v___x_889_ = ((size_t)1ULL);
v___x_890_ = lean_usize_sub(v___x_888_, v___x_889_);
v___x_891_ = lean_usize_land(v___x_887_, v___x_890_);
v___x_892_ = lean_array_uget_borrowed(v_buckets_878_, v___x_891_);
v___x_893_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(v_a_876_, v_fallback_877_, v___x_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg___boxed(lean_object* v_m_894_, lean_object* v_a_895_, lean_object* v_fallback_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(v_m_894_, v_a_895_, v_fallback_896_);
lean_dec(v_fallback_896_);
lean_dec(v_a_895_);
lean_dec_ref(v_m_894_);
return v_res_897_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2(void){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_901_ = lean_box(0);
v___x_902_ = lean_unsigned_to_nat(16u);
v___x_903_ = lean_mk_array(v___x_902_, v___x_901_);
return v___x_903_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_904_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2);
v___x_905_ = lean_unsigned_to_nat(0u);
v___x_906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_905_);
lean_ctor_set(v___x_906_, 1, v___x_904_);
return v___x_906_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUses___closed__1(void){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_909_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUses___closed__0));
v___x_910_ = l_Lean_stringToMessageData(v___x_909_);
return v___x_910_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUses___closed__3(void){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUses___closed__2));
v___x_913_ = l_Lean_stringToMessageData(v___x_912_);
return v___x_913_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUses___closed__5(void){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_915_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUses___closed__4));
v___x_916_ = l_Lean_stringToMessageData(v___x_915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses(lean_object* v_e_917_, lean_object* v_subst_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_){
_start:
{
switch(lean_obj_tag(v_e_917_))
{
case 0:
{
lean_object* v_deBruijnIndex_924_; lean_object* v___x_925_; uint8_t v___x_926_; 
v_deBruijnIndex_924_ = lean_ctor_get(v_e_917_, 0);
v___x_925_ = lean_array_get_size(v_subst_918_);
v___x_926_ = lean_nat_dec_lt(v_deBruijnIndex_924_, v___x_925_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
lean_inc(v_deBruijnIndex_924_);
lean_dec_ref(v_e_917_);
lean_dec_ref(v_subst_918_);
v___x_927_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__1, &l_Lean_Elab_Tactic_Do_countUses___closed__1_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__1);
v___x_928_ = l_Nat_reprFast(v_deBruijnIndex_924_);
v___x_929_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
v___x_930_ = l_Lean_MessageData_ofFormat(v___x_929_);
v___x_931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_927_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
v___x_932_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__3, &l_Lean_Elab_Tactic_Do_countUses___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__3);
v___x_933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_931_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
v___x_934_ = l_Nat_reprFast(v___x_925_);
v___x_935_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
v___x_936_ = l_Lean_MessageData_ofFormat(v___x_935_);
v___x_937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_933_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v___x_937_, v_a_919_, v_a_920_, v_a_921_, v_a_922_);
return v___x_938_;
}
else
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; uint8_t v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_939_ = lean_unsigned_to_nat(1u);
v___x_940_ = lean_nat_sub(v___x_925_, v___x_939_);
v___x_941_ = lean_nat_sub(v___x_940_, v_deBruijnIndex_924_);
lean_dec(v___x_940_);
v___x_942_ = lean_array_fget(v_subst_918_, v___x_941_);
lean_dec(v___x_941_);
lean_dec_ref(v_subst_918_);
v___x_943_ = 1;
v___x_944_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3);
v___x_945_ = lean_box(v___x_943_);
v___x_946_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(v___x_944_, v___x_942_, v___x_945_);
v___x_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_947_, 0, v_e_917_);
lean_ctor_set(v___x_947_, 1, v___x_946_);
v___x_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_948_, 0, v___x_947_);
return v___x_948_;
}
}
case 1:
{
lean_object* v_fvarId_949_; uint8_t v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
lean_dec_ref(v_subst_918_);
v_fvarId_949_ = lean_ctor_get(v_e_917_, 0);
v___x_950_ = 1;
v___x_951_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3);
v___x_952_ = lean_box(v___x_950_);
lean_inc(v_fvarId_949_);
v___x_953_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(v___x_951_, v_fvarId_949_, v___x_952_);
v___x_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_954_, 0, v_e_917_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v___x_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
return v___x_955_;
}
case 5:
{
lean_object* v_fn_956_; lean_object* v_arg_957_; lean_object* v___x_958_; 
v_fn_956_ = lean_ctor_get(v_e_917_, 0);
lean_inc_ref(v_fn_956_);
v_arg_957_ = lean_ctor_get(v_e_917_, 1);
lean_inc_ref(v_arg_957_);
lean_dec_ref(v_e_917_);
lean_inc_ref(v_subst_918_);
v___x_958_ = l_Lean_Elab_Tactic_Do_countUses(v_fn_956_, v_subst_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v_a_959_; lean_object* v_fst_960_; lean_object* v_snd_961_; lean_object* v___x_962_; 
v_a_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_a_959_);
lean_dec_ref(v___x_958_);
v_fst_960_ = lean_ctor_get(v_a_959_, 0);
lean_inc(v_fst_960_);
v_snd_961_ = lean_ctor_get(v_a_959_, 1);
lean_inc(v_snd_961_);
lean_dec(v_a_959_);
v___x_962_ = l_Lean_Elab_Tactic_Do_countUses(v_arg_957_, v_subst_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_981_; 
v_a_963_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_981_ == 0)
{
v___x_965_ = v___x_962_;
v_isShared_966_ = v_isSharedCheck_981_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_962_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_981_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v_fst_967_; lean_object* v_snd_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_980_; 
v_fst_967_ = lean_ctor_get(v_a_963_, 0);
v_snd_968_ = lean_ctor_get(v_a_963_, 1);
v_isSharedCheck_980_ = !lean_is_exclusive(v_a_963_);
if (v_isSharedCheck_980_ == 0)
{
v___x_970_ = v_a_963_;
v_isShared_971_ = v_isSharedCheck_980_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_snd_968_);
lean_inc(v_fst_967_);
lean_dec(v_a_963_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_980_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_975_; 
v___x_972_ = l_Lean_Expr_app___override(v_fst_960_, v_fst_967_);
v___x_973_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_snd_961_, v_snd_968_);
lean_dec(v_snd_961_);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 1, v___x_973_);
lean_ctor_set(v___x_970_, 0, v___x_972_);
v___x_975_ = v___x_970_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v___x_972_);
lean_ctor_set(v_reuseFailAlloc_979_, 1, v___x_973_);
v___x_975_ = v_reuseFailAlloc_979_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
lean_object* v___x_977_; 
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 0, v___x_975_);
v___x_977_ = v___x_965_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_975_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
}
else
{
lean_dec(v_snd_961_);
lean_dec(v_fst_960_);
return v___x_962_;
}
}
else
{
lean_dec_ref(v_arg_957_);
lean_dec_ref(v_subst_918_);
return v___x_958_;
}
}
case 6:
{
lean_object* v_binderName_982_; lean_object* v_binderType_983_; lean_object* v_body_984_; uint8_t v_binderInfo_985_; lean_object* v___x_986_; 
v_binderName_982_ = lean_ctor_get(v_e_917_, 0);
lean_inc(v_binderName_982_);
v_binderType_983_ = lean_ctor_get(v_e_917_, 1);
lean_inc_ref(v_binderType_983_);
v_body_984_ = lean_ctor_get(v_e_917_, 2);
lean_inc_ref(v_body_984_);
v_binderInfo_985_ = lean_ctor_get_uint8(v_e_917_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_917_);
v___x_986_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(v_a_919_, v_a_920_, v_a_921_, v_a_922_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_987_; lean_object* v___x_988_; 
v_a_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_a_987_);
lean_dec_ref(v___x_986_);
lean_inc_ref(v_subst_918_);
v___x_988_ = l_Lean_Elab_Tactic_Do_countUses(v_binderType_983_, v_subst_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v_a_989_; lean_object* v_fst_990_; lean_object* v_snd_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v_a_989_ = lean_ctor_get(v___x_988_, 0);
lean_inc(v_a_989_);
lean_dec_ref(v___x_988_);
v_fst_990_ = lean_ctor_get(v_a_989_, 0);
lean_inc(v_fst_990_);
v_snd_991_ = lean_ctor_get(v_a_989_, 1);
lean_inc(v_snd_991_);
lean_dec(v_a_989_);
lean_inc(v_a_987_);
v___x_992_ = lean_array_push(v_subst_918_, v_a_987_);
v___x_993_ = l_Lean_Elab_Tactic_Do_countUses(v_body_984_, v___x_992_, v_a_919_, v_a_920_, v_a_921_, v_a_922_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1013_; 
v_a_994_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_996_ = v___x_993_;
v_isShared_997_ = v_isSharedCheck_1013_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_993_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1013_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v_fst_998_; lean_object* v_snd_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1012_; 
v_fst_998_ = lean_ctor_get(v_a_994_, 0);
v_snd_999_ = lean_ctor_get(v_a_994_, 1);
v_isSharedCheck_1012_ = !lean_is_exclusive(v_a_994_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1001_ = v_a_994_;
v_isShared_1002_ = v_isSharedCheck_1012_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_snd_999_);
lean_inc(v_fst_998_);
lean_dec(v_a_994_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1012_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1007_; 
v___x_1003_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_snd_991_, v_snd_999_);
lean_dec(v_snd_991_);
v___x_1004_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v___x_1003_, v_a_987_);
lean_dec(v_a_987_);
v___x_1005_ = l_Lean_Expr_lam___override(v_binderName_982_, v_fst_990_, v_fst_998_, v_binderInfo_985_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 1, v___x_1004_);
lean_ctor_set(v___x_1001_, 0, v___x_1005_);
v___x_1007_ = v___x_1001_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1005_);
lean_ctor_set(v_reuseFailAlloc_1011_, 1, v___x_1004_);
v___x_1007_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
lean_object* v___x_1009_; 
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v___x_1007_);
v___x_1009_ = v___x_996_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1007_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
}
else
{
lean_dec(v_snd_991_);
lean_dec(v_fst_990_);
lean_dec(v_a_987_);
lean_dec(v_binderName_982_);
return v___x_993_;
}
}
else
{
lean_dec(v_a_987_);
lean_dec_ref(v_body_984_);
lean_dec(v_binderName_982_);
lean_dec_ref(v_subst_918_);
return v___x_988_;
}
}
else
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
lean_dec_ref(v_body_984_);
lean_dec_ref(v_binderType_983_);
lean_dec(v_binderName_982_);
lean_dec_ref(v_subst_918_);
v_a_1014_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_986_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_986_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
case 7:
{
lean_object* v_binderName_1022_; lean_object* v_binderType_1023_; lean_object* v_body_1024_; uint8_t v_binderInfo_1025_; lean_object* v___x_1026_; 
v_binderName_1022_ = lean_ctor_get(v_e_917_, 0);
lean_inc(v_binderName_1022_);
v_binderType_1023_ = lean_ctor_get(v_e_917_, 1);
lean_inc_ref(v_binderType_1023_);
v_body_1024_ = lean_ctor_get(v_e_917_, 2);
lean_inc_ref(v_body_1024_);
v_binderInfo_1025_ = lean_ctor_get_uint8(v_e_917_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_917_);
v___x_1026_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(v_a_919_, v_a_920_, v_a_921_, v_a_922_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; lean_object* v___x_1028_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_a_1027_);
lean_dec_ref(v___x_1026_);
lean_inc_ref(v_subst_918_);
v___x_1028_ = l_Lean_Elab_Tactic_Do_countUses(v_binderType_1023_, v_subst_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v_a_1029_; lean_object* v_fst_1030_; lean_object* v_snd_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_a_1029_);
lean_dec_ref(v___x_1028_);
v_fst_1030_ = lean_ctor_get(v_a_1029_, 0);
lean_inc(v_fst_1030_);
v_snd_1031_ = lean_ctor_get(v_a_1029_, 1);
lean_inc(v_snd_1031_);
lean_dec(v_a_1029_);
lean_inc(v_a_1027_);
v___x_1032_ = lean_array_push(v_subst_918_, v_a_1027_);
v___x_1033_ = l_Lean_Elab_Tactic_Do_countUses(v_body_1024_, v___x_1032_, v_a_919_, v_a_920_, v_a_921_, v_a_922_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1053_; 
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1036_ = v___x_1033_;
v_isShared_1037_ = v_isSharedCheck_1053_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1033_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1053_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v_fst_1038_; lean_object* v_snd_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1052_; 
v_fst_1038_ = lean_ctor_get(v_a_1034_, 0);
v_snd_1039_ = lean_ctor_get(v_a_1034_, 1);
v_isSharedCheck_1052_ = !lean_is_exclusive(v_a_1034_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1041_ = v_a_1034_;
v_isShared_1042_ = v_isSharedCheck_1052_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_snd_1039_);
lean_inc(v_fst_1038_);
lean_dec(v_a_1034_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1052_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1047_; 
v___x_1043_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_snd_1031_, v_snd_1039_);
lean_dec(v_snd_1031_);
v___x_1044_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v___x_1043_, v_a_1027_);
lean_dec(v_a_1027_);
v___x_1045_ = l_Lean_Expr_forallE___override(v_binderName_1022_, v_fst_1030_, v_fst_1038_, v_binderInfo_1025_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 1, v___x_1044_);
lean_ctor_set(v___x_1041_, 0, v___x_1045_);
v___x_1047_ = v___x_1041_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v___x_1044_);
v___x_1047_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
lean_object* v___x_1049_; 
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 0, v___x_1047_);
v___x_1049_ = v___x_1036_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v___x_1047_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
}
else
{
lean_dec(v_snd_1031_);
lean_dec(v_fst_1030_);
lean_dec(v_a_1027_);
lean_dec(v_binderName_1022_);
return v___x_1033_;
}
}
else
{
lean_dec(v_a_1027_);
lean_dec_ref(v_body_1024_);
lean_dec(v_binderName_1022_);
lean_dec_ref(v_subst_918_);
return v___x_1028_;
}
}
else
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1061_; 
lean_dec_ref(v_body_1024_);
lean_dec_ref(v_binderType_1023_);
lean_dec(v_binderName_1022_);
lean_dec_ref(v_subst_918_);
v_a_1054_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1056_ = v___x_1026_;
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_1026_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1059_; 
if (v_isShared_1057_ == 0)
{
v___x_1059_ = v___x_1056_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1054_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
case 8:
{
lean_object* v_declName_1062_; lean_object* v_type_1063_; lean_object* v_value_1064_; lean_object* v_body_1065_; uint8_t v_nondep_1066_; lean_object* v___x_1067_; 
v_declName_1062_ = lean_ctor_get(v_e_917_, 0);
lean_inc(v_declName_1062_);
v_type_1063_ = lean_ctor_get(v_e_917_, 1);
lean_inc_ref(v_type_1063_);
v_value_1064_ = lean_ctor_get(v_e_917_, 2);
lean_inc_ref(v_value_1064_);
v_body_1065_ = lean_ctor_get(v_e_917_, 3);
lean_inc_ref(v_body_1065_);
v_nondep_1066_ = lean_ctor_get_uint8(v_e_917_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_917_);
v___x_1067_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(v_a_919_, v_a_920_, v_a_921_, v_a_922_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v_a_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v_a_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc_n(v_a_1068_, 2);
lean_dec_ref(v___x_1067_);
lean_inc_ref(v_subst_918_);
v___x_1069_ = lean_array_push(v_subst_918_, v_a_1068_);
v___x_1070_ = l_Lean_Elab_Tactic_Do_countUses(v_body_1065_, v___x_1069_, v_a_919_, v_a_920_, v_a_921_, v_a_922_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1113_; 
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1073_ = v___x_1070_;
v_isShared_1074_ = v_isSharedCheck_1113_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1070_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1113_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v_fst_1075_; lean_object* v_snd_1076_; lean_object* v___x_1078_; 
v_fst_1075_ = lean_ctor_get(v_a_1071_, 0);
lean_inc(v_fst_1075_);
v_snd_1076_ = lean_ctor_get(v_a_1071_, 1);
lean_inc(v_snd_1076_);
lean_dec(v_a_1071_);
if (v_isShared_1074_ == 0)
{
lean_ctor_set_tag(v___x_1073_, 1);
lean_ctor_set(v___x_1073_, 0, v_value_1064_);
v___x_1078_ = v___x_1073_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_value_1064_);
v___x_1078_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_Elab_Tactic_Do_countUsesDecl(v_a_1068_, v_type_1063_, v___x_1078_, v_snd_1076_, v_subst_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_);
lean_dec(v_a_1068_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1103_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1082_ = v___x_1079_;
v_isShared_1083_ = v_isSharedCheck_1103_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1079_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1103_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v_snd_1084_; lean_object* v_fst_1085_; 
v_snd_1084_ = lean_ctor_get(v_a_1080_, 1);
lean_inc(v_snd_1084_);
v_fst_1085_ = lean_ctor_get(v_snd_1084_, 0);
lean_inc(v_fst_1085_);
if (lean_obj_tag(v_fst_1085_) == 1)
{
lean_object* v_fst_1086_; lean_object* v_snd_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1099_; 
v_fst_1086_ = lean_ctor_get(v_a_1080_, 0);
lean_inc(v_fst_1086_);
lean_dec(v_a_1080_);
v_snd_1087_ = lean_ctor_get(v_snd_1084_, 1);
v_isSharedCheck_1099_ = !lean_is_exclusive(v_snd_1084_);
if (v_isSharedCheck_1099_ == 0)
{
lean_object* v_unused_1100_; 
v_unused_1100_ = lean_ctor_get(v_snd_1084_, 0);
lean_dec(v_unused_1100_);
v___x_1089_ = v_snd_1084_;
v_isShared_1090_ = v_isSharedCheck_1099_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_snd_1087_);
lean_dec(v_snd_1084_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1099_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v_val_1091_; lean_object* v___x_1092_; lean_object* v___x_1094_; 
v_val_1091_ = lean_ctor_get(v_fst_1085_, 0);
lean_inc(v_val_1091_);
lean_dec_ref(v_fst_1085_);
v___x_1092_ = l_Lean_Expr_letE___override(v_declName_1062_, v_fst_1086_, v_val_1091_, v_fst_1075_, v_nondep_1066_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v___x_1092_);
v___x_1094_ = v___x_1089_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1092_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v_snd_1087_);
v___x_1094_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
lean_object* v___x_1096_; 
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 0, v___x_1094_);
v___x_1096_ = v___x_1082_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1094_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
else
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
lean_dec(v_fst_1085_);
lean_dec(v_snd_1084_);
lean_del_object(v___x_1082_);
lean_dec(v_a_1080_);
lean_dec(v_fst_1075_);
lean_dec(v_declName_1062_);
v___x_1101_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__5, &l_Lean_Elab_Tactic_Do_countUses___closed__5_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__5);
v___x_1102_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v___x_1101_, v_a_919_, v_a_920_, v_a_921_, v_a_922_);
return v___x_1102_;
}
}
}
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
lean_dec(v_fst_1075_);
lean_dec(v_declName_1062_);
v_a_1104_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1079_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1079_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1068_);
lean_dec_ref(v_value_1064_);
lean_dec_ref(v_type_1063_);
lean_dec(v_declName_1062_);
lean_dec_ref(v_subst_918_);
return v___x_1070_;
}
}
else
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
lean_dec_ref(v_body_1065_);
lean_dec_ref(v_value_1064_);
lean_dec_ref(v_type_1063_);
lean_dec(v_declName_1062_);
lean_dec_ref(v_subst_918_);
v_a_1114_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1116_ = v___x_1067_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1067_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1114_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
case 10:
{
lean_object* v_data_1122_; lean_object* v_expr_1123_; lean_object* v___x_1124_; 
v_data_1122_ = lean_ctor_get(v_e_917_, 0);
lean_inc(v_data_1122_);
v_expr_1123_ = lean_ctor_get(v_e_917_, 1);
lean_inc_ref(v_expr_1123_);
lean_dec_ref(v_e_917_);
v___x_1124_ = l_Lean_Elab_Tactic_Do_countUses(v_expr_1123_, v_subst_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1134_; 
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1127_ = v___x_1124_;
v_isShared_1128_ = v_isSharedCheck_1134_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1124_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1134_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___f_1129_; lean_object* v___x_1130_; lean_object* v___x_1132_; 
v___f_1129_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_countUses___lam__0), 2, 1);
lean_closure_set(v___f_1129_, 0, v_data_1122_);
v___x_1130_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v___f_1129_, v_a_1125_);
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v___x_1130_);
v___x_1132_ = v___x_1127_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
else
{
lean_dec(v_data_1122_);
return v___x_1124_;
}
}
case 11:
{
lean_object* v_typeName_1135_; lean_object* v_idx_1136_; lean_object* v_struct_1137_; lean_object* v___x_1138_; 
v_typeName_1135_ = lean_ctor_get(v_e_917_, 0);
lean_inc(v_typeName_1135_);
v_idx_1136_ = lean_ctor_get(v_e_917_, 1);
lean_inc(v_idx_1136_);
v_struct_1137_ = lean_ctor_get(v_e_917_, 2);
lean_inc_ref(v_struct_1137_);
lean_dec_ref(v_e_917_);
v___x_1138_ = l_Lean_Elab_Tactic_Do_countUses(v_struct_1137_, v_subst_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1148_; 
v_a_1139_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1141_ = v___x_1138_;
v_isShared_1142_ = v_isSharedCheck_1148_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1138_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1148_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___f_1143_; lean_object* v___x_1144_; lean_object* v___x_1146_; 
v___f_1143_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_countUses___lam__1), 3, 2);
lean_closure_set(v___f_1143_, 0, v_typeName_1135_);
lean_closure_set(v___f_1143_, 1, v_idx_1136_);
v___x_1144_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v___f_1143_, v_a_1139_);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 0, v___x_1144_);
v___x_1146_ = v___x_1141_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1144_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
else
{
lean_dec(v_idx_1136_);
lean_dec(v_typeName_1135_);
return v___x_1138_;
}
}
default: 
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
lean_dec_ref(v_subst_918_);
v___x_1149_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3);
v___x_1150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1150_, 0, v_e_917_);
lean_ctor_set(v___x_1150_, 1, v___x_1149_);
v___x_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1150_);
return v___x_1151_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl(lean_object* v_fvarId_1152_, lean_object* v_ty_1153_, lean_object* v_val_x3f_1154_, lean_object* v_bodyUses_1155_, lean_object* v_subst_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_){
_start:
{
lean_object* v___x_1162_; 
lean_inc_ref(v_subst_1156_);
v___x_1162_ = l_Lean_Elab_Tactic_Do_countUses(v_ty_1153_, v_subst_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1218_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1165_ = v___x_1162_;
v_isShared_1166_ = v_isSharedCheck_1218_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1162_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1218_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v_fst_1167_; lean_object* v_snd_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1217_; 
v_fst_1167_ = lean_ctor_get(v_a_1163_, 0);
v_snd_1168_ = lean_ctor_get(v_a_1163_, 1);
v_isSharedCheck_1217_ = !lean_is_exclusive(v_a_1163_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1170_ = v_a_1163_;
v_isShared_1171_ = v_isSharedCheck_1217_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_snd_1168_);
lean_inc(v_fst_1167_);
lean_dec(v_a_1163_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1217_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
uint8_t v___y_1173_; lean_object* v___y_1174_; lean_object* v___y_1175_; lean_object* v_fst_1190_; lean_object* v_snd_1191_; 
if (lean_obj_tag(v_val_x3f_1154_) == 0)
{
lean_object* v___x_1201_; 
lean_dec_ref(v_subst_1156_);
v___x_1201_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3);
v_fst_1190_ = v_val_x3f_1154_;
v_snd_1191_ = v___x_1201_;
goto v___jp_1189_;
}
else
{
lean_object* v_val_1202_; lean_object* v___x_1203_; 
v_val_1202_ = lean_ctor_get(v_val_x3f_1154_, 0);
lean_inc(v_val_1202_);
lean_dec_ref(v_val_x3f_1154_);
v___x_1203_ = l_Lean_Elab_Tactic_Do_countUses(v_val_1202_, v_subst_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v_a_1204_; lean_object* v___f_1205_; lean_object* v___x_1206_; lean_object* v_fst_1207_; lean_object* v_snd_1208_; 
v_a_1204_ = lean_ctor_get(v___x_1203_, 0);
lean_inc(v_a_1204_);
lean_dec_ref(v___x_1203_);
v___f_1205_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4));
v___x_1206_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v___f_1205_, v_a_1204_);
v_fst_1207_ = lean_ctor_get(v___x_1206_, 0);
lean_inc(v_fst_1207_);
v_snd_1208_ = lean_ctor_get(v___x_1206_, 1);
lean_inc(v_snd_1208_);
lean_dec_ref(v___x_1206_);
v_fst_1190_ = v_fst_1207_;
v_snd_1191_ = v_snd_1208_;
goto v___jp_1189_;
}
else
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
lean_del_object(v___x_1170_);
lean_dec(v_snd_1168_);
lean_dec(v_fst_1167_);
lean_del_object(v___x_1165_);
lean_dec_ref(v_bodyUses_1155_);
v_a_1209_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1203_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1203_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1209_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
v___jp_1172_:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1183_; 
v___x_1176_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v___y_1175_, v_fvarId_1152_);
v___x_1177_ = lean_box(0);
v___x_1178_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_1179_ = l_Lean_Elab_Tactic_Do_Uses_toNat(v___y_1173_);
v___x_1180_ = l_Lean_KVMap_setNat(v___x_1177_, v___x_1178_, v___x_1179_);
v___x_1181_ = l_Lean_Elab_Tactic_Do_addMData(v___x_1180_, v_fst_1167_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 1, v___x_1176_);
lean_ctor_set(v___x_1170_, 0, v___y_1174_);
v___x_1183_ = v___x_1170_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___y_1174_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v___x_1176_);
v___x_1183_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
lean_object* v___x_1184_; lean_object* v___x_1186_; 
v___x_1184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1181_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 0, v___x_1184_);
v___x_1186_ = v___x_1165_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1184_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
v___jp_1189_:
{
uint8_t v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; uint8_t v___x_1195_; uint8_t v___x_1196_; 
v___x_1192_ = 0;
v___x_1193_ = lean_box(v___x_1192_);
v___x_1194_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(v_bodyUses_1155_, v_fvarId_1152_, v___x_1193_);
lean_dec(v___x_1193_);
v___x_1195_ = lean_unbox(v___x_1194_);
v___x_1196_ = l_Lean_Elab_Tactic_Do_instBEqUses_beq(v___x_1195_, v___x_1192_);
if (v___x_1196_ == 0)
{
lean_object* v___x_1197_; lean_object* v___x_1198_; uint8_t v___x_1199_; 
v___x_1197_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_bodyUses_1155_, v_snd_1168_);
lean_dec_ref(v_bodyUses_1155_);
v___x_1198_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v___x_1197_, v_snd_1191_);
lean_dec_ref(v___x_1197_);
v___x_1199_ = lean_unbox(v___x_1194_);
lean_dec(v___x_1194_);
v___y_1173_ = v___x_1199_;
v___y_1174_ = v_fst_1190_;
v___y_1175_ = v___x_1198_;
goto v___jp_1172_;
}
else
{
uint8_t v___x_1200_; 
lean_dec_ref(v_snd_1191_);
lean_dec(v_snd_1168_);
v___x_1200_ = lean_unbox(v___x_1194_);
lean_dec(v___x_1194_);
v___y_1173_ = v___x_1200_;
v___y_1174_ = v_fst_1190_;
v___y_1175_ = v_bodyUses_1155_;
goto v___jp_1172_;
}
}
}
}
}
else
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1226_; 
lean_dec_ref(v_subst_1156_);
lean_dec_ref(v_bodyUses_1155_);
lean_dec(v_val_x3f_1154_);
v_a_1219_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1221_ = v___x_1162_;
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1162_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1224_; 
if (v_isShared_1222_ == 0)
{
v___x_1224_ = v___x_1221_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_a_1219_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___boxed(lean_object* v_fvarId_1227_, lean_object* v_ty_1228_, lean_object* v_val_x3f_1229_, lean_object* v_bodyUses_1230_, lean_object* v_subst_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l_Lean_Elab_Tactic_Do_countUsesDecl(v_fvarId_1227_, v_ty_1228_, v_val_x3f_1229_, v_bodyUses_1230_, v_subst_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_);
lean_dec(v_a_1235_);
lean_dec_ref(v_a_1234_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
lean_dec(v_fvarId_1227_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses___boxed(lean_object* v_e_1238_, lean_object* v_subst_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Lean_Elab_Tactic_Do_countUses(v_e_1238_, v_subst_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_);
lean_dec(v_a_1243_);
lean_dec_ref(v_a_1242_);
lean_dec(v_a_1241_);
lean_dec_ref(v_a_1240_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0(lean_object* v_00_u03b2_1246_, lean_object* v_m_1247_, lean_object* v_a_1248_, lean_object* v_fallback_1249_){
_start:
{
lean_object* v___x_1250_; 
v___x_1250_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(v_m_1247_, v_a_1248_, v_fallback_1249_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___boxed(lean_object* v_00_u03b2_1251_, lean_object* v_m_1252_, lean_object* v_a_1253_, lean_object* v_fallback_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0(v_00_u03b2_1251_, v_m_1252_, v_a_1253_, v_fallback_1254_);
lean_dec(v_fallback_1254_);
lean_dec(v_a_1253_);
lean_dec_ref(v_m_1252_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1(lean_object* v_00_u03b2_1256_, lean_object* v_m_1257_, lean_object* v_a_1258_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v_m_1257_, v_a_1258_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___boxed(lean_object* v_00_u03b2_1260_, lean_object* v_m_1261_, lean_object* v_a_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1(v_00_u03b2_1260_, v_m_1261_, v_a_1262_);
lean_dec(v_a_1262_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3(lean_object* v_00_u03b1_1264_, lean_object* v_msg_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v___x_1271_; 
v___x_1271_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v_msg_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___boxed(lean_object* v_00_u03b1_1272_, lean_object* v_msg_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3(v_00_u03b1_1272_, v_msg_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4(lean_object* v_00_u03b2_1280_, lean_object* v_m_1281_, lean_object* v_a_1282_, lean_object* v_b_1283_){
_start:
{
lean_object* v___x_1284_; 
v___x_1284_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(v_m_1281_, v_a_1282_, v_b_1283_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9(lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(v___y_1288_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___boxed(lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9(v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0(lean_object* v_00_u03b2_1297_, lean_object* v_a_1298_, lean_object* v_fallback_1299_, lean_object* v_x_1300_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(v_a_1298_, v_fallback_1299_, v_x_1300_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1302_, lean_object* v_a_1303_, lean_object* v_fallback_1304_, lean_object* v_x_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0(v_00_u03b2_1302_, v_a_1303_, v_fallback_1304_, v_x_1305_);
lean_dec(v_x_1305_);
lean_dec(v_fallback_1304_);
lean_dec(v_a_1303_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2(lean_object* v_00_u03b2_1307_, lean_object* v_a_1308_, lean_object* v_x_1309_){
_start:
{
lean_object* v___x_1310_; 
v___x_1310_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_1308_, v_x_1309_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1311_, lean_object* v_a_1312_, lean_object* v_x_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2(v_00_u03b2_1311_, v_a_1312_, v_x_1313_);
lean_dec(v_a_1312_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7(lean_object* v_00_u03b2_1315_, lean_object* v_a_1316_, lean_object* v_b_1317_, lean_object* v_x_1318_){
_start:
{
lean_object* v___x_1319_; 
v___x_1319_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(v_a_1316_, v_b_1317_, v_x_1318_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(lean_object* v_as_1322_, size_t v_i_1323_, size_t v_stop_1324_, lean_object* v_b_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
uint8_t v___x_1331_; 
v___x_1331_ = lean_usize_dec_eq(v_i_1323_, v_stop_1324_);
if (v___x_1331_ == 0)
{
size_t v___x_1332_; size_t v___x_1333_; lean_object* v___x_1334_; 
v___x_1332_ = ((size_t)1ULL);
v___x_1333_ = lean_usize_sub(v_i_1323_, v___x_1332_);
v___x_1334_ = lean_array_uget_borrowed(v_as_1322_, v___x_1333_);
if (lean_obj_tag(v___x_1334_) == 0)
{
v_i_1323_ = v___x_1333_;
goto _start;
}
else
{
lean_object* v_val_1336_; lean_object* v_fst_1337_; lean_object* v_snd_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v_val_1336_ = lean_ctor_get(v___x_1334_, 0);
v_fst_1337_ = lean_ctor_get(v_b_1325_, 0);
lean_inc(v_fst_1337_);
v_snd_1338_ = lean_ctor_get(v_b_1325_, 1);
lean_inc(v_snd_1338_);
lean_dec_ref(v_b_1325_);
v___x_1339_ = l_Lean_LocalDecl_fvarId(v_val_1336_);
v___x_1340_ = l_Lean_LocalDecl_type(v_val_1336_);
v___x_1341_ = l_Lean_LocalDecl_value_x3f(v_val_1336_, v___x_1331_);
v___x_1342_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0));
v___x_1343_ = l_Lean_Elab_Tactic_Do_countUsesDecl(v___x_1339_, v___x_1340_, v___x_1341_, v_snd_1338_, v___x_1342_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
lean_dec(v___x_1339_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v_a_1344_; lean_object* v_snd_1345_; lean_object* v_fst_1346_; lean_object* v_fst_1347_; lean_object* v_snd_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1363_; 
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_a_1344_);
lean_dec_ref(v___x_1343_);
v_snd_1345_ = lean_ctor_get(v_a_1344_, 1);
lean_inc(v_snd_1345_);
v_fst_1346_ = lean_ctor_get(v_a_1344_, 0);
lean_inc(v_fst_1346_);
lean_dec(v_a_1344_);
v_fst_1347_ = lean_ctor_get(v_snd_1345_, 0);
v_snd_1348_ = lean_ctor_get(v_snd_1345_, 1);
v_isSharedCheck_1363_ = !lean_is_exclusive(v_snd_1345_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1350_ = v_snd_1345_;
v_isShared_1351_ = v_isSharedCheck_1363_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_snd_1348_);
lean_inc(v_fst_1347_);
lean_dec(v_snd_1345_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1363_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___y_1353_; 
if (lean_obj_tag(v_fst_1347_) == 0)
{
lean_object* v___x_1359_; 
lean_inc(v_val_1336_);
v___x_1359_ = l_Lean_LocalDecl_setType(v_val_1336_, v_fst_1346_);
v___y_1353_ = v___x_1359_;
goto v___jp_1352_;
}
else
{
lean_object* v_val_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v_val_1360_ = lean_ctor_get(v_fst_1347_, 0);
lean_inc(v_val_1360_);
lean_dec_ref(v_fst_1347_);
lean_inc(v_val_1336_);
v___x_1361_ = l_Lean_LocalDecl_setType(v_val_1336_, v_fst_1346_);
v___x_1362_ = l_Lean_LocalDecl_setValue(v___x_1361_, v_val_1360_);
v___y_1353_ = v___x_1362_;
goto v___jp_1352_;
}
v___jp_1352_:
{
lean_object* v___x_1354_; lean_object* v___x_1356_; 
v___x_1354_ = lean_array_push(v_fst_1337_, v___y_1353_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 0, v___x_1354_);
v___x_1356_ = v___x_1350_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v___x_1354_);
lean_ctor_set(v_reuseFailAlloc_1358_, 1, v_snd_1348_);
v___x_1356_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
v_i_1323_ = v___x_1333_;
v_b_1325_ = v___x_1356_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
lean_dec(v_fst_1337_);
v_a_1364_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1366_ = v___x_1343_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1343_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
}
}
else
{
lean_object* v___x_1372_; 
v___x_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1372_, 0, v_b_1325_);
return v___x_1372_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___boxed(lean_object* v_as_1373_, lean_object* v_i_1374_, lean_object* v_stop_1375_, lean_object* v_b_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_){
_start:
{
size_t v_i_boxed_1382_; size_t v_stop_boxed_1383_; lean_object* v_res_1384_; 
v_i_boxed_1382_ = lean_unbox_usize(v_i_1374_);
lean_dec(v_i_1374_);
v_stop_boxed_1383_ = lean_unbox_usize(v_stop_1375_);
lean_dec(v_stop_1375_);
v_res_1384_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(v_as_1373_, v_i_boxed_1382_, v_stop_boxed_1383_, v_b_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
lean_dec(v___y_1378_);
lean_dec_ref(v___y_1377_);
lean_dec_ref(v_as_1373_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(lean_object* v_x_1385_, lean_object* v_x_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
if (lean_obj_tag(v_x_1385_) == 0)
{
lean_object* v_cs_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1405_; 
v_cs_1392_ = lean_ctor_get(v_x_1385_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v_x_1385_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1394_ = v_x_1385_;
v_isShared_1395_ = v_isSharedCheck_1405_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_cs_1392_);
lean_dec(v_x_1385_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1405_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; uint8_t v___x_1398_; 
v___x_1396_ = lean_array_get_size(v_cs_1392_);
v___x_1397_ = lean_unsigned_to_nat(0u);
v___x_1398_ = lean_nat_dec_lt(v___x_1397_, v___x_1396_);
if (v___x_1398_ == 0)
{
lean_object* v___x_1400_; 
lean_dec_ref(v_cs_1392_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 0, v_x_1386_);
v___x_1400_ = v___x_1394_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_x_1386_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
else
{
size_t v___x_1402_; size_t v___x_1403_; lean_object* v___x_1404_; 
lean_del_object(v___x_1394_);
v___x_1402_ = lean_usize_of_nat(v___x_1396_);
v___x_1403_ = ((size_t)0ULL);
v___x_1404_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(v_cs_1392_, v___x_1402_, v___x_1403_, v_x_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
lean_dec_ref(v_cs_1392_);
return v___x_1404_;
}
}
}
else
{
lean_object* v_vs_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1419_; 
v_vs_1406_ = lean_ctor_get(v_x_1385_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v_x_1385_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1408_ = v_x_1385_;
v_isShared_1409_ = v_isSharedCheck_1419_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_vs_1406_);
lean_dec(v_x_1385_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1419_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; uint8_t v___x_1412_; 
v___x_1410_ = lean_array_get_size(v_vs_1406_);
v___x_1411_ = lean_unsigned_to_nat(0u);
v___x_1412_ = lean_nat_dec_lt(v___x_1411_, v___x_1410_);
if (v___x_1412_ == 0)
{
lean_object* v___x_1414_; 
lean_dec_ref(v_vs_1406_);
if (v_isShared_1409_ == 0)
{
lean_ctor_set_tag(v___x_1408_, 0);
lean_ctor_set(v___x_1408_, 0, v_x_1386_);
v___x_1414_ = v___x_1408_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_x_1386_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
else
{
size_t v___x_1416_; size_t v___x_1417_; lean_object* v___x_1418_; 
lean_del_object(v___x_1408_);
v___x_1416_ = lean_usize_of_nat(v___x_1410_);
v___x_1417_ = ((size_t)0ULL);
v___x_1418_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(v_vs_1406_, v___x_1416_, v___x_1417_, v_x_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
lean_dec_ref(v_vs_1406_);
return v___x_1418_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(lean_object* v_as_1420_, size_t v_i_1421_, size_t v_stop_1422_, lean_object* v_b_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
uint8_t v___x_1429_; 
v___x_1429_ = lean_usize_dec_eq(v_i_1421_, v_stop_1422_);
if (v___x_1429_ == 0)
{
size_t v___x_1430_; size_t v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1430_ = ((size_t)1ULL);
v___x_1431_ = lean_usize_sub(v_i_1421_, v___x_1430_);
v___x_1432_ = lean_array_uget_borrowed(v_as_1420_, v___x_1431_);
lean_inc(v___x_1432_);
v___x_1433_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v___x_1432_, v_b_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_a_1434_);
lean_dec_ref(v___x_1433_);
v_i_1421_ = v___x_1431_;
v_b_1423_ = v_a_1434_;
goto _start;
}
else
{
return v___x_1433_;
}
}
else
{
lean_object* v___x_1436_; 
v___x_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1436_, 0, v_b_1423_);
return v___x_1436_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_as_1437_, lean_object* v_i_1438_, lean_object* v_stop_1439_, lean_object* v_b_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
size_t v_i_boxed_1446_; size_t v_stop_boxed_1447_; lean_object* v_res_1448_; 
v_i_boxed_1446_ = lean_unbox_usize(v_i_1438_);
lean_dec(v_i_1438_);
v_stop_boxed_1447_ = lean_unbox_usize(v_stop_1439_);
lean_dec(v_stop_1439_);
v_res_1448_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(v_as_1437_, v_i_boxed_1446_, v_stop_boxed_1447_, v_b_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec_ref(v_as_1437_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1___boxed(lean_object* v_x_1449_, lean_object* v_x_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v_x_1449_, v_x_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
lean_dec(v___y_1452_);
lean_dec_ref(v___y_1451_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(lean_object* v_t_1457_, lean_object* v_init_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
lean_object* v_root_1464_; lean_object* v_tail_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; uint8_t v___x_1468_; 
v_root_1464_ = lean_ctor_get(v_t_1457_, 0);
lean_inc_ref(v_root_1464_);
v_tail_1465_ = lean_ctor_get(v_t_1457_, 1);
lean_inc_ref(v_tail_1465_);
lean_dec_ref(v_t_1457_);
v___x_1466_ = lean_array_get_size(v_tail_1465_);
v___x_1467_ = lean_unsigned_to_nat(0u);
v___x_1468_ = lean_nat_dec_lt(v___x_1467_, v___x_1466_);
if (v___x_1468_ == 0)
{
lean_object* v___x_1469_; 
lean_dec_ref(v_tail_1465_);
v___x_1469_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v_root_1464_, v_init_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
return v___x_1469_;
}
else
{
size_t v___x_1470_; size_t v___x_1471_; lean_object* v___x_1472_; 
v___x_1470_ = lean_usize_of_nat(v___x_1466_);
v___x_1471_ = ((size_t)0ULL);
v___x_1472_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(v_tail_1465_, v___x_1470_, v___x_1471_, v_init_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
lean_dec_ref(v_tail_1465_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v_a_1473_; lean_object* v___x_1474_; 
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_a_1473_);
lean_dec_ref(v___x_1472_);
v___x_1474_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v_root_1464_, v_a_1473_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
return v___x_1474_;
}
else
{
lean_dec_ref(v_root_1464_);
return v___x_1472_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0___boxed(lean_object* v_t_1475_, lean_object* v_init_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(v_t_1475_, v_init_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(lean_object* v_lctx_1483_, lean_object* v_init_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
lean_object* v_decls_1490_; lean_object* v___x_1491_; 
v_decls_1490_ = lean_ctor_get(v_lctx_1483_, 1);
lean_inc_ref(v_decls_1490_);
lean_dec_ref(v_lctx_1483_);
v___x_1491_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(v_decls_1490_, v_init_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0___boxed(lean_object* v_lctx_1492_, lean_object* v_init_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(v_lctx_1492_, v_init_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(size_t v_sz_1500_, size_t v_i_1501_, lean_object* v_bs_1502_, lean_object* v___y_1503_){
_start:
{
uint8_t v___x_1505_; 
v___x_1505_ = lean_usize_dec_lt(v_i_1501_, v_sz_1500_);
if (v___x_1505_ == 0)
{
lean_object* v___x_1506_; 
v___x_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1506_, 0, v_bs_1502_);
return v___x_1506_;
}
else
{
lean_object* v_v_1507_; lean_object* v___x_1508_; lean_object* v_bs_x27_1509_; lean_object* v_a_1511_; 
v_v_1507_ = lean_array_uget(v_bs_1502_, v_i_1501_);
v___x_1508_ = lean_unsigned_to_nat(0u);
v_bs_x27_1509_ = lean_array_uset(v_bs_1502_, v_i_1501_, v___x_1508_);
if (lean_obj_tag(v_v_1507_) == 0)
{
v_a_1511_ = v_v_1507_;
goto v___jp_1510_;
}
else
{
lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1530_; 
v_isSharedCheck_1530_ = !lean_is_exclusive(v_v_1507_);
if (v_isSharedCheck_1530_ == 0)
{
lean_object* v_unused_1531_; 
v_unused_1531_ = lean_ctor_get(v_v_1507_, 0);
lean_dec(v_unused_1531_);
v___x_1517_ = v_v_1507_;
v_isShared_1518_ = v_isSharedCheck_1530_;
goto v_resetjp_1516_;
}
else
{
lean_dec(v_v_1507_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1530_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1528_; 
v___x_1519_ = lean_st_ref_take(v___y_1503_);
v___x_1520_ = l_Lean_instInhabitedLocalDecl_default;
v___x_1521_ = lean_array_get_size(v___x_1519_);
v___x_1522_ = lean_unsigned_to_nat(1u);
v___x_1523_ = lean_nat_sub(v___x_1521_, v___x_1522_);
v___x_1524_ = lean_array_get(v___x_1520_, v___x_1519_, v___x_1523_);
lean_dec(v___x_1523_);
v___x_1525_ = lean_array_pop(v___x_1519_);
v___x_1526_ = lean_st_ref_set(v___y_1503_, v___x_1525_);
if (v_isShared_1518_ == 0)
{
lean_ctor_set(v___x_1517_, 0, v___x_1524_);
v___x_1528_ = v___x_1517_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___x_1524_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
v_a_1511_ = v___x_1528_;
goto v___jp_1510_;
}
}
}
v___jp_1510_:
{
size_t v___x_1512_; size_t v___x_1513_; lean_object* v___x_1514_; 
v___x_1512_ = ((size_t)1ULL);
v___x_1513_ = lean_usize_add(v_i_1501_, v___x_1512_);
v___x_1514_ = lean_array_uset(v_bs_x27_1509_, v_i_1501_, v_a_1511_);
v_i_1501_ = v___x_1513_;
v_bs_1502_ = v___x_1514_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg___boxed(lean_object* v_sz_1532_, lean_object* v_i_1533_, lean_object* v_bs_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
size_t v_sz_boxed_1537_; size_t v_i_boxed_1538_; lean_object* v_res_1539_; 
v_sz_boxed_1537_ = lean_unbox_usize(v_sz_1532_);
lean_dec(v_sz_1532_);
v_i_boxed_1538_ = lean_unbox_usize(v_i_1533_);
lean_dec(v_i_1533_);
v_res_1539_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_boxed_1537_, v_i_boxed_1538_, v_bs_1534_, v___y_1535_);
lean_dec(v___y_1535_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(lean_object* v_x_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
if (lean_obj_tag(v_x_1540_) == 0)
{
lean_object* v_cs_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1573_; 
v_cs_1547_ = lean_ctor_get(v_x_1540_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v_x_1540_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1549_ = v_x_1540_;
v_isShared_1550_ = v_isSharedCheck_1573_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_cs_1547_);
lean_dec(v_x_1540_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1573_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
size_t v_sz_1551_; size_t v___x_1552_; lean_object* v___x_1553_; 
v_sz_1551_ = lean_array_size(v_cs_1547_);
v___x_1552_ = ((size_t)0ULL);
v___x_1553_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(v_sz_1551_, v___x_1552_, v_cs_1547_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_a_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1564_; 
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1556_ = v___x_1553_;
v_isShared_1557_ = v_isSharedCheck_1564_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_a_1554_);
lean_dec(v___x_1553_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1564_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1559_; 
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 0, v_a_1554_);
v___x_1559_ = v___x_1549_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1554_);
v___x_1559_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
lean_object* v___x_1561_; 
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 0, v___x_1559_);
v___x_1561_ = v___x_1556_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1559_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
else
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1572_; 
lean_del_object(v___x_1549_);
v_a_1565_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1567_ = v___x_1553_;
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1553_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1570_; 
if (v_isShared_1568_ == 0)
{
v___x_1570_ = v___x_1567_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_a_1565_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
}
else
{
lean_object* v_vs_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1600_; 
v_vs_1574_ = lean_ctor_get(v_x_1540_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v_x_1540_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1576_ = v_x_1540_;
v_isShared_1577_ = v_isSharedCheck_1600_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_vs_1574_);
lean_dec(v_x_1540_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1600_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
size_t v_sz_1578_; size_t v___x_1579_; lean_object* v___x_1580_; 
v_sz_1578_ = lean_array_size(v_vs_1574_);
v___x_1579_ = ((size_t)0ULL);
v___x_1580_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_1578_, v___x_1579_, v_vs_1574_, v___y_1541_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1591_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1583_ = v___x_1580_;
v_isShared_1584_ = v_isSharedCheck_1591_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1580_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1591_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1586_; 
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 0, v_a_1581_);
v___x_1586_ = v___x_1576_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1581_);
v___x_1586_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
lean_object* v___x_1588_; 
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 0, v___x_1586_);
v___x_1588_ = v___x_1583_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1586_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
else
{
lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1599_; 
lean_del_object(v___x_1576_);
v_a_1592_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1594_ = v___x_1580_;
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v___x_1580_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1597_; 
if (v_isShared_1595_ == 0)
{
v___x_1597_ = v___x_1594_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_a_1592_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(size_t v_sz_1601_, size_t v_i_1602_, lean_object* v_bs_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
uint8_t v___x_1610_; 
v___x_1610_ = lean_usize_dec_lt(v_i_1602_, v_sz_1601_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; 
v___x_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1611_, 0, v_bs_1603_);
return v___x_1611_;
}
else
{
lean_object* v_v_1612_; lean_object* v___x_1613_; 
v_v_1612_ = lean_array_uget_borrowed(v_bs_1603_, v_i_1602_);
lean_inc(v_v_1612_);
v___x_1613_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(v_v_1612_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; lean_object* v___x_1615_; lean_object* v_bs_x27_1616_; size_t v___x_1617_; size_t v___x_1618_; lean_object* v___x_1619_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_a_1614_);
lean_dec_ref(v___x_1613_);
v___x_1615_ = lean_unsigned_to_nat(0u);
v_bs_x27_1616_ = lean_array_uset(v_bs_1603_, v_i_1602_, v___x_1615_);
v___x_1617_ = ((size_t)1ULL);
v___x_1618_ = lean_usize_add(v_i_1602_, v___x_1617_);
v___x_1619_ = lean_array_uset(v_bs_x27_1616_, v_i_1602_, v_a_1614_);
v_i_1602_ = v___x_1618_;
v_bs_1603_ = v___x_1619_;
goto _start;
}
else
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1628_; 
lean_dec_ref(v_bs_1603_);
v_a_1621_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1623_ = v___x_1613_;
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1613_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1626_; 
if (v_isShared_1624_ == 0)
{
v___x_1626_ = v___x_1623_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5___boxed(lean_object* v_sz_1629_, lean_object* v_i_1630_, lean_object* v_bs_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
size_t v_sz_boxed_1638_; size_t v_i_boxed_1639_; lean_object* v_res_1640_; 
v_sz_boxed_1638_ = lean_unbox_usize(v_sz_1629_);
lean_dec(v_sz_1629_);
v_i_boxed_1639_ = lean_unbox_usize(v_i_1630_);
lean_dec(v_i_1630_);
v_res_1640_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(v_sz_boxed_1638_, v_i_boxed_1639_, v_bs_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec(v___y_1632_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2___boxed(lean_object* v_x_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(v_x_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(lean_object* v_t_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v_root_1656_; lean_object* v_tail_1657_; lean_object* v_size_1658_; size_t v_shift_1659_; lean_object* v_tailOff_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1696_; 
v_root_1656_ = lean_ctor_get(v_t_1649_, 0);
v_tail_1657_ = lean_ctor_get(v_t_1649_, 1);
v_size_1658_ = lean_ctor_get(v_t_1649_, 2);
v_shift_1659_ = lean_ctor_get_usize(v_t_1649_, 4);
v_tailOff_1660_ = lean_ctor_get(v_t_1649_, 3);
v_isSharedCheck_1696_ = !lean_is_exclusive(v_t_1649_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1662_ = v_t_1649_;
v_isShared_1663_ = v_isSharedCheck_1696_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_tailOff_1660_);
lean_inc(v_size_1658_);
lean_inc(v_tail_1657_);
lean_inc(v_root_1656_);
lean_dec(v_t_1649_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1696_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1664_; 
v___x_1664_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(v_root_1656_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_object* v_a_1665_; size_t v_sz_1666_; size_t v___x_1667_; lean_object* v___x_1668_; 
v_a_1665_ = lean_ctor_get(v___x_1664_, 0);
lean_inc(v_a_1665_);
lean_dec_ref(v___x_1664_);
v_sz_1666_ = lean_array_size(v_tail_1657_);
v___x_1667_ = ((size_t)0ULL);
v___x_1668_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_1666_, v___x_1667_, v_tail_1657_, v___y_1650_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1679_; 
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1671_ = v___x_1668_;
v_isShared_1672_ = v_isSharedCheck_1679_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1668_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1679_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 1, v_a_1669_);
lean_ctor_set(v___x_1662_, 0, v_a_1665_);
v___x_1674_ = v___x_1662_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_a_1665_);
lean_ctor_set(v_reuseFailAlloc_1678_, 1, v_a_1669_);
lean_ctor_set(v_reuseFailAlloc_1678_, 2, v_size_1658_);
lean_ctor_set(v_reuseFailAlloc_1678_, 3, v_tailOff_1660_);
lean_ctor_set_usize(v_reuseFailAlloc_1678_, 4, v_shift_1659_);
v___x_1674_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
lean_object* v___x_1676_; 
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 0, v___x_1674_);
v___x_1676_ = v___x_1671_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v___x_1674_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
}
else
{
lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1687_; 
lean_dec(v_a_1665_);
lean_del_object(v___x_1662_);
lean_dec(v_tailOff_1660_);
lean_dec(v_size_1658_);
v_a_1680_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1682_ = v___x_1668_;
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v___x_1668_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1685_; 
if (v_isShared_1683_ == 0)
{
v___x_1685_ = v___x_1682_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_a_1680_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
}
else
{
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1695_; 
lean_del_object(v___x_1662_);
lean_dec(v_tailOff_1660_);
lean_dec(v_size_1658_);
lean_dec_ref(v_tail_1657_);
v_a_1688_ = lean_ctor_get(v___x_1664_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1690_ = v___x_1664_;
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1664_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
if (v_isShared_1691_ == 0)
{
v___x_1693_ = v___x_1690_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_a_1688_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1___boxed(lean_object* v_t_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(v_t_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v___y_1698_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesLCtx(lean_object* v_ctx_1705_, lean_object* v_targetUses_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_){
_start:
{
lean_object* v_decls_1712_; lean_object* v_fvarIdToDecl_1713_; lean_object* v_auxDeclToFullName_1714_; lean_object* v_size_1715_; lean_object* v_decls_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v_decls_1712_ = lean_ctor_get(v_ctx_1705_, 1);
lean_inc_ref(v_decls_1712_);
v_fvarIdToDecl_1713_ = lean_ctor_get(v_ctx_1705_, 0);
lean_inc_ref(v_fvarIdToDecl_1713_);
v_auxDeclToFullName_1714_ = lean_ctor_get(v_ctx_1705_, 2);
lean_inc(v_auxDeclToFullName_1714_);
v_size_1715_ = lean_ctor_get(v_decls_1712_, 2);
v_decls_1716_ = lean_mk_empty_array_with_capacity(v_size_1715_);
v___x_1717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1717_, 0, v_decls_1716_);
lean_ctor_set(v___x_1717_, 1, v_targetUses_1706_);
v___x_1718_ = l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(v_ctx_1705_, v___x_1717_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1719_; lean_object* v_fst_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_a_1719_);
lean_dec_ref(v___x_1718_);
v_fst_1720_ = lean_ctor_get(v_a_1719_, 0);
lean_inc(v_fst_1720_);
lean_dec(v_a_1719_);
v___x_1721_ = lean_st_mk_ref(v_fst_1720_);
v___x_1722_ = l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(v_decls_1712_, v___x_1721_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1732_; 
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1725_ = v___x_1722_;
v_isShared_1726_ = v_isSharedCheck_1732_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1722_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1732_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1730_; 
v___x_1727_ = lean_st_ref_get(v___x_1721_);
lean_dec(v___x_1721_);
lean_dec(v___x_1727_);
v___x_1728_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1728_, 0, v_fvarIdToDecl_1713_);
lean_ctor_set(v___x_1728_, 1, v_a_1723_);
lean_ctor_set(v___x_1728_, 2, v_auxDeclToFullName_1714_);
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 0, v___x_1728_);
v___x_1730_ = v___x_1725_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1728_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
else
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1740_; 
lean_dec(v___x_1721_);
lean_dec(v_auxDeclToFullName_1714_);
lean_dec_ref(v_fvarIdToDecl_1713_);
v_a_1733_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1735_ = v___x_1722_;
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1722_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
if (v_isShared_1736_ == 0)
{
v___x_1738_ = v___x_1735_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1733_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
}
else
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1748_; 
lean_dec(v_auxDeclToFullName_1714_);
lean_dec_ref(v_fvarIdToDecl_1713_);
lean_dec_ref(v_decls_1712_);
v_a_1741_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1743_ = v___x_1718_;
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1718_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1746_; 
if (v_isShared_1744_ == 0)
{
v___x_1746_ = v___x_1743_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_a_1741_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesLCtx___boxed(lean_object* v_ctx_1749_, lean_object* v_targetUses_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Lean_Elab_Tactic_Do_countUsesLCtx(v_ctx_1749_, v_targetUses_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_);
lean_dec(v_a_1754_);
lean_dec_ref(v_a_1753_);
lean_dec(v_a_1752_);
lean_dec_ref(v_a_1751_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3(size_t v_sz_1757_, size_t v_i_1758_, lean_object* v_bs_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
lean_object* v___x_1766_; 
v___x_1766_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_1757_, v_i_1758_, v_bs_1759_, v___y_1760_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___boxed(lean_object* v_sz_1767_, lean_object* v_i_1768_, lean_object* v_bs_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
size_t v_sz_boxed_1776_; size_t v_i_boxed_1777_; lean_object* v_res_1778_; 
v_sz_boxed_1776_ = lean_unbox_usize(v_sz_1767_);
lean_dec(v_sz_1767_);
v_i_boxed_1777_ = lean_unbox_usize(v_i_1768_);
lean_dec(v_i_1768_);
v_res_1778_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3(v_sz_boxed_1776_, v_i_boxed_1777_, v_bs_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
lean_dec(v___y_1774_);
lean_dec_ref(v___y_1773_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec(v___y_1770_);
return v_res_1778_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_doNotDup(uint8_t v_u_1779_, lean_object* v_rhs_1780_, uint8_t v_elimTrivial_1781_){
_start:
{
uint8_t v___x_1782_; uint8_t v___x_1783_; 
v___x_1782_ = 2;
v___x_1783_ = l_Lean_Elab_Tactic_Do_instBEqUses_beq(v_u_1779_, v___x_1782_);
if (v___x_1783_ == 0)
{
return v___x_1783_;
}
else
{
if (v_elimTrivial_1781_ == 0)
{
return v___x_1783_;
}
else
{
uint8_t v___x_1784_; 
v___x_1784_ = l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup(v_rhs_1780_);
if (v___x_1784_ == 0)
{
return v___x_1783_;
}
else
{
uint8_t v___x_1785_; 
v___x_1785_ = 0;
return v___x_1785_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_doNotDup___boxed(lean_object* v_u_1786_, lean_object* v_rhs_1787_, lean_object* v_elimTrivial_1788_){
_start:
{
uint8_t v_u_boxed_1789_; uint8_t v_elimTrivial_boxed_1790_; uint8_t v_res_1791_; lean_object* v_r_1792_; 
v_u_boxed_1789_ = lean_unbox(v_u_1786_);
v_elimTrivial_boxed_1790_ = lean_unbox(v_elimTrivial_1788_);
v_res_1791_ = l_Lean_Elab_Tactic_Do_doNotDup(v_u_boxed_1789_, v_rhs_1787_, v_elimTrivial_boxed_1790_);
lean_dec_ref(v_rhs_1787_);
v_r_1792_ = lean_box(v_res_1791_);
return v_r_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0(uint8_t v_elimTrivial_1795_, lean_object* v_e_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
if (lean_obj_tag(v_e_1796_) == 8)
{
lean_object* v_type_1803_; 
v_type_1803_ = lean_ctor_get(v_e_1796_, 1);
if (lean_obj_tag(v_type_1803_) == 10)
{
lean_object* v_value_1804_; lean_object* v_body_1805_; lean_object* v_data_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; uint8_t v_uses_1810_; uint8_t v___x_1811_; 
v_value_1804_ = lean_ctor_get(v_e_1796_, 2);
v_body_1805_ = lean_ctor_get(v_e_1796_, 3);
v_data_1806_ = lean_ctor_get(v_type_1803_, 0);
v___x_1807_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_1808_ = lean_unsigned_to_nat(2u);
v___x_1809_ = l_Lean_KVMap_getNat(v_data_1806_, v___x_1807_, v___x_1808_);
v_uses_1810_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_1809_);
lean_dec(v___x_1809_);
v___x_1811_ = l_Lean_Elab_Tactic_Do_doNotDup(v_uses_1810_, v_value_1804_, v_elimTrivial_1795_);
if (v___x_1811_ == 0)
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1812_ = lean_expr_instantiate1(v_body_1805_, v_value_1804_);
v___x_1813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1812_);
v___x_1814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1813_);
return v___x_1814_;
}
else
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0));
v___x_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
return v___x_1816_;
}
}
else
{
lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1817_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0));
v___x_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1817_);
return v___x_1818_;
}
}
else
{
lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1819_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0));
v___x_1820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1819_);
return v___x_1820_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___boxed(lean_object* v_elimTrivial_1821_, lean_object* v_e_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_){
_start:
{
uint8_t v_elimTrivial_boxed_1829_; lean_object* v_res_1830_; 
v_elimTrivial_boxed_1829_ = lean_unbox(v_elimTrivial_1821_);
v_res_1830_ = l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0(v_elimTrivial_boxed_1829_, v_e_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec_ref(v_e_1822_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1(lean_object* v_e_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1838_, 0, v_e_1831_);
v___x_1839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1838_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1___boxed(lean_object* v_e_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1(v_e_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
lean_dec(v___y_1841_);
return v_res_1847_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1853_ = l_Lean_maxRecDepthErrorMessage;
v___x_1854_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1853_);
return v___x_1854_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4(void){
_start:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1855_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3);
v___x_1856_ = l_Lean_MessageData_ofFormat(v___x_1855_);
return v___x_1856_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1857_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4);
v___x_1858_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2));
v___x_1859_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1858_);
lean_ctor_set(v___x_1859_, 1, v___x_1857_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(lean_object* v_ref_1860_){
_start:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1862_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5);
v___x_1863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1863_, 0, v_ref_1860_);
lean_ctor_set(v___x_1863_, 1, v___x_1862_);
v___x_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1863_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___boxed(lean_object* v_ref_1865_, lean_object* v___y_1866_){
_start:
{
lean_object* v_res_1867_; 
v_res_1867_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_1865_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(lean_object* v_x_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v___y_1877_; lean_object* v_fileName_1886_; lean_object* v_fileMap_1887_; lean_object* v_options_1888_; lean_object* v_currRecDepth_1889_; lean_object* v_maxRecDepth_1890_; lean_object* v_ref_1891_; lean_object* v_currNamespace_1892_; lean_object* v_openDecls_1893_; lean_object* v_initHeartbeats_1894_; lean_object* v_maxHeartbeats_1895_; lean_object* v_quotContext_1896_; lean_object* v_currMacroScope_1897_; uint8_t v_diag_1898_; lean_object* v_cancelTk_x3f_1899_; uint8_t v_suppressElabErrors_1900_; lean_object* v_inheritedTraceOptions_1901_; lean_object* v___x_1907_; uint8_t v___x_1908_; 
v_fileName_1886_ = lean_ctor_get(v___y_1873_, 0);
v_fileMap_1887_ = lean_ctor_get(v___y_1873_, 1);
v_options_1888_ = lean_ctor_get(v___y_1873_, 2);
v_currRecDepth_1889_ = lean_ctor_get(v___y_1873_, 3);
v_maxRecDepth_1890_ = lean_ctor_get(v___y_1873_, 4);
v_ref_1891_ = lean_ctor_get(v___y_1873_, 5);
v_currNamespace_1892_ = lean_ctor_get(v___y_1873_, 6);
v_openDecls_1893_ = lean_ctor_get(v___y_1873_, 7);
v_initHeartbeats_1894_ = lean_ctor_get(v___y_1873_, 8);
v_maxHeartbeats_1895_ = lean_ctor_get(v___y_1873_, 9);
v_quotContext_1896_ = lean_ctor_get(v___y_1873_, 10);
v_currMacroScope_1897_ = lean_ctor_get(v___y_1873_, 11);
v_diag_1898_ = lean_ctor_get_uint8(v___y_1873_, sizeof(void*)*14);
v_cancelTk_x3f_1899_ = lean_ctor_get(v___y_1873_, 12);
v_suppressElabErrors_1900_ = lean_ctor_get_uint8(v___y_1873_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1901_ = lean_ctor_get(v___y_1873_, 13);
v___x_1907_ = lean_unsigned_to_nat(0u);
v___x_1908_ = lean_nat_dec_eq(v_maxRecDepth_1890_, v___x_1907_);
if (v___x_1908_ == 0)
{
uint8_t v___x_1909_; 
v___x_1909_ = lean_nat_dec_eq(v_currRecDepth_1889_, v_maxRecDepth_1890_);
if (v___x_1909_ == 0)
{
goto v___jp_1902_;
}
else
{
lean_object* v___x_1910_; 
lean_dec_ref(v_x_1868_);
lean_inc(v_ref_1891_);
v___x_1910_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_1891_);
v___y_1877_ = v___x_1910_;
goto v___jp_1876_;
}
}
else
{
goto v___jp_1902_;
}
v___jp_1876_:
{
if (lean_obj_tag(v___y_1877_) == 0)
{
return v___y_1877_;
}
else
{
lean_object* v_a_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1885_; 
v_a_1878_ = lean_ctor_get(v___y_1877_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___y_1877_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1880_ = v___y_1877_;
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_a_1878_);
lean_dec(v___y_1877_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1883_; 
if (v_isShared_1881_ == 0)
{
v___x_1883_ = v___x_1880_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_a_1878_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
}
}
v___jp_1902_:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1903_ = lean_unsigned_to_nat(1u);
v___x_1904_ = lean_nat_add(v_currRecDepth_1889_, v___x_1903_);
lean_inc_ref(v_inheritedTraceOptions_1901_);
lean_inc(v_cancelTk_x3f_1899_);
lean_inc(v_currMacroScope_1897_);
lean_inc(v_quotContext_1896_);
lean_inc(v_maxHeartbeats_1895_);
lean_inc(v_initHeartbeats_1894_);
lean_inc(v_openDecls_1893_);
lean_inc(v_currNamespace_1892_);
lean_inc(v_ref_1891_);
lean_inc(v_maxRecDepth_1890_);
lean_inc_ref(v_options_1888_);
lean_inc_ref(v_fileMap_1887_);
lean_inc_ref(v_fileName_1886_);
v___x_1905_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1905_, 0, v_fileName_1886_);
lean_ctor_set(v___x_1905_, 1, v_fileMap_1887_);
lean_ctor_set(v___x_1905_, 2, v_options_1888_);
lean_ctor_set(v___x_1905_, 3, v___x_1904_);
lean_ctor_set(v___x_1905_, 4, v_maxRecDepth_1890_);
lean_ctor_set(v___x_1905_, 5, v_ref_1891_);
lean_ctor_set(v___x_1905_, 6, v_currNamespace_1892_);
lean_ctor_set(v___x_1905_, 7, v_openDecls_1893_);
lean_ctor_set(v___x_1905_, 8, v_initHeartbeats_1894_);
lean_ctor_set(v___x_1905_, 9, v_maxHeartbeats_1895_);
lean_ctor_set(v___x_1905_, 10, v_quotContext_1896_);
lean_ctor_set(v___x_1905_, 11, v_currMacroScope_1897_);
lean_ctor_set(v___x_1905_, 12, v_cancelTk_x3f_1899_);
lean_ctor_set(v___x_1905_, 13, v_inheritedTraceOptions_1901_);
lean_ctor_set_uint8(v___x_1905_, sizeof(void*)*14, v_diag_1898_);
lean_ctor_set_uint8(v___x_1905_, sizeof(void*)*14 + 1, v_suppressElabErrors_1900_);
lean_inc(v___y_1874_);
lean_inc(v___y_1872_);
lean_inc_ref(v___y_1871_);
lean_inc(v___y_1870_);
lean_inc(v___y_1869_);
v___x_1906_ = lean_apply_7(v_x_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___x_1905_, v___y_1874_, lean_box(0));
v___y_1877_ = v___x_1906_;
goto v___jp_1876_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg___boxed(lean_object* v_x_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_){
_start:
{
lean_object* v_res_1919_; 
v_res_1919_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v_x_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1913_);
lean_dec(v___y_1912_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(lean_object* v_a_1920_, lean_object* v_x_1921_){
_start:
{
if (lean_obj_tag(v_x_1921_) == 0)
{
lean_object* v___x_1922_; 
v___x_1922_ = lean_box(0);
return v___x_1922_;
}
else
{
lean_object* v_key_1923_; lean_object* v_value_1924_; lean_object* v_tail_1925_; uint8_t v___x_1926_; 
v_key_1923_ = lean_ctor_get(v_x_1921_, 0);
v_value_1924_ = lean_ctor_get(v_x_1921_, 1);
v_tail_1925_ = lean_ctor_get(v_x_1921_, 2);
v___x_1926_ = l_Lean_ExprStructEq_beq(v_key_1923_, v_a_1920_);
if (v___x_1926_ == 0)
{
v_x_1921_ = v_tail_1925_;
goto _start;
}
else
{
lean_object* v___x_1928_; 
lean_inc(v_value_1924_);
v___x_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1928_, 0, v_value_1924_);
return v___x_1928_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg___boxed(lean_object* v_a_1929_, lean_object* v_x_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(v_a_1929_, v_x_1930_);
lean_dec(v_x_1930_);
lean_dec_ref(v_a_1929_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(lean_object* v_m_1932_, lean_object* v_a_1933_){
_start:
{
lean_object* v_buckets_1934_; lean_object* v___x_1935_; uint64_t v___x_1936_; uint64_t v___x_1937_; uint64_t v___x_1938_; uint64_t v_fold_1939_; uint64_t v___x_1940_; uint64_t v___x_1941_; uint64_t v___x_1942_; size_t v___x_1943_; size_t v___x_1944_; size_t v___x_1945_; size_t v___x_1946_; size_t v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
v_buckets_1934_ = lean_ctor_get(v_m_1932_, 1);
v___x_1935_ = lean_array_get_size(v_buckets_1934_);
v___x_1936_ = l_Lean_ExprStructEq_hash(v_a_1933_);
v___x_1937_ = 32ULL;
v___x_1938_ = lean_uint64_shift_right(v___x_1936_, v___x_1937_);
v_fold_1939_ = lean_uint64_xor(v___x_1936_, v___x_1938_);
v___x_1940_ = 16ULL;
v___x_1941_ = lean_uint64_shift_right(v_fold_1939_, v___x_1940_);
v___x_1942_ = lean_uint64_xor(v_fold_1939_, v___x_1941_);
v___x_1943_ = lean_uint64_to_usize(v___x_1942_);
v___x_1944_ = lean_usize_of_nat(v___x_1935_);
v___x_1945_ = ((size_t)1ULL);
v___x_1946_ = lean_usize_sub(v___x_1944_, v___x_1945_);
v___x_1947_ = lean_usize_land(v___x_1943_, v___x_1946_);
v___x_1948_ = lean_array_uget_borrowed(v_buckets_1934_, v___x_1947_);
v___x_1949_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(v_a_1933_, v___x_1948_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_m_1950_, lean_object* v_a_1951_){
_start:
{
lean_object* v_res_1952_; 
v_res_1952_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(v_m_1950_, v_a_1951_);
lean_dec_ref(v_a_1951_);
lean_dec_ref(v_m_1950_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(lean_object* v_k_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v_b_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
lean_object* v___x_1962_; 
lean_inc(v___y_1960_);
lean_inc_ref(v___y_1959_);
lean_inc(v___y_1958_);
lean_inc_ref(v___y_1957_);
lean_inc(v___y_1955_);
lean_inc(v___y_1954_);
v___x_1962_ = lean_apply_8(v_k_1953_, v_b_1956_, v___y_1954_, v___y_1955_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, lean_box(0));
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed(lean_object* v_k_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v_b_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(v_k_1963_, v___y_1964_, v___y_1965_, v_b_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec(v___y_1965_);
lean_dec(v___y_1964_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(lean_object* v_name_1973_, lean_object* v_type_1974_, lean_object* v_val_1975_, lean_object* v_k_1976_, uint8_t v_nondep_1977_, uint8_t v_kind_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_){
_start:
{
lean_object* v___f_1986_; lean_object* v___x_1987_; 
lean_inc(v___y_1980_);
lean_inc(v___y_1979_);
v___f_1986_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1986_, 0, v_k_1976_);
lean_closure_set(v___f_1986_, 1, v___y_1979_);
lean_closure_set(v___f_1986_, 2, v___y_1980_);
v___x_1987_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1973_, v_type_1974_, v_val_1975_, v___f_1986_, v_nondep_1977_, v_kind_1978_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
if (lean_obj_tag(v___x_1987_) == 0)
{
return v___x_1987_;
}
else
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1987_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1987_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1988_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg___boxed(lean_object* v_name_1996_, lean_object* v_type_1997_, lean_object* v_val_1998_, lean_object* v_k_1999_, lean_object* v_nondep_2000_, lean_object* v_kind_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
uint8_t v_nondep_boxed_2009_; uint8_t v_kind_boxed_2010_; lean_object* v_res_2011_; 
v_nondep_boxed_2009_ = lean_unbox(v_nondep_2000_);
v_kind_boxed_2010_ = lean_unbox(v_kind_2001_);
v_res_2011_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_name_1996_, v_type_1997_, v_val_1998_, v_k_1999_, v_nondep_boxed_2009_, v_kind_boxed_2010_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec(v___y_2003_);
lean_dec(v___y_2002_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_name_2012_, uint8_t v_bi_2013_, lean_object* v_type_2014_, lean_object* v_k_2015_, uint8_t v_kind_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_){
_start:
{
lean_object* v___f_2024_; lean_object* v___x_2025_; 
lean_inc(v___y_2018_);
lean_inc(v___y_2017_);
v___f_2024_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2024_, 0, v_k_2015_);
lean_closure_set(v___f_2024_, 1, v___y_2017_);
lean_closure_set(v___f_2024_, 2, v___y_2018_);
v___x_2025_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2012_, v_bi_2013_, v_type_2014_, v___f_2024_, v_kind_2016_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
if (lean_obj_tag(v___x_2025_) == 0)
{
return v___x_2025_;
}
else
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2033_; 
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2028_ = v___x_2025_;
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_2025_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_2029_ == 0)
{
v___x_2031_ = v___x_2028_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2026_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_name_2034_, lean_object* v_bi_2035_, lean_object* v_type_2036_, lean_object* v_k_2037_, lean_object* v_kind_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_){
_start:
{
uint8_t v_bi_boxed_2046_; uint8_t v_kind_boxed_2047_; lean_object* v_res_2048_; 
v_bi_boxed_2046_ = lean_unbox(v_bi_2035_);
v_kind_boxed_2047_ = lean_unbox(v_kind_2038_);
v_res_2048_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_name_2034_, v_bi_boxed_2046_, v_type_2036_, v_k_2037_, v_kind_boxed_2047_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v___y_2040_);
lean_dec(v___y_2039_);
return v_res_2048_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2(lean_object* v___x_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v___x_2056_; 
v___x_2056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2049_);
return v___x_2056_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2___boxed(lean_object* v___x_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_){
_start:
{
lean_object* v_res_2064_; 
v_res_2064_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2(v___x_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_);
lean_dec(v___y_2062_);
lean_dec_ref(v___y_2061_);
lean_dec(v___y_2060_);
lean_dec_ref(v___y_2059_);
lean_dec(v___y_2058_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_2065_, lean_object* v_x_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2073_ = lean_apply_1(v_x_2066_, lean_box(0));
v___x_2074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2073_);
return v___x_2074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_2075_, lean_object* v_x_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
lean_object* v_res_2083_; 
v_res_2083_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(v_00_u03b1_2075_, v_x_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
lean_dec(v___y_2079_);
lean_dec_ref(v___y_2078_);
lean_dec(v___y_2077_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(lean_object* v_x_2084_, lean_object* v_x_2085_){
_start:
{
if (lean_obj_tag(v_x_2085_) == 0)
{
return v_x_2084_;
}
else
{
lean_object* v_key_2086_; lean_object* v_value_2087_; lean_object* v_tail_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2111_; 
v_key_2086_ = lean_ctor_get(v_x_2085_, 0);
v_value_2087_ = lean_ctor_get(v_x_2085_, 1);
v_tail_2088_ = lean_ctor_get(v_x_2085_, 2);
v_isSharedCheck_2111_ = !lean_is_exclusive(v_x_2085_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2090_ = v_x_2085_;
v_isShared_2091_ = v_isSharedCheck_2111_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_tail_2088_);
lean_inc(v_value_2087_);
lean_inc(v_key_2086_);
lean_dec(v_x_2085_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2111_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2092_; uint64_t v___x_2093_; uint64_t v___x_2094_; uint64_t v___x_2095_; uint64_t v_fold_2096_; uint64_t v___x_2097_; uint64_t v___x_2098_; uint64_t v___x_2099_; size_t v___x_2100_; size_t v___x_2101_; size_t v___x_2102_; size_t v___x_2103_; size_t v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2107_; 
v___x_2092_ = lean_array_get_size(v_x_2084_);
v___x_2093_ = l_Lean_ExprStructEq_hash(v_key_2086_);
v___x_2094_ = 32ULL;
v___x_2095_ = lean_uint64_shift_right(v___x_2093_, v___x_2094_);
v_fold_2096_ = lean_uint64_xor(v___x_2093_, v___x_2095_);
v___x_2097_ = 16ULL;
v___x_2098_ = lean_uint64_shift_right(v_fold_2096_, v___x_2097_);
v___x_2099_ = lean_uint64_xor(v_fold_2096_, v___x_2098_);
v___x_2100_ = lean_uint64_to_usize(v___x_2099_);
v___x_2101_ = lean_usize_of_nat(v___x_2092_);
v___x_2102_ = ((size_t)1ULL);
v___x_2103_ = lean_usize_sub(v___x_2101_, v___x_2102_);
v___x_2104_ = lean_usize_land(v___x_2100_, v___x_2103_);
v___x_2105_ = lean_array_uget_borrowed(v_x_2084_, v___x_2104_);
lean_inc(v___x_2105_);
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 2, v___x_2105_);
v___x_2107_ = v___x_2090_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_key_2086_);
lean_ctor_set(v_reuseFailAlloc_2110_, 1, v_value_2087_);
lean_ctor_set(v_reuseFailAlloc_2110_, 2, v___x_2105_);
v___x_2107_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
lean_object* v___x_2108_; 
v___x_2108_ = lean_array_uset(v_x_2084_, v___x_2104_, v___x_2107_);
v_x_2084_ = v___x_2108_;
v_x_2085_ = v_tail_2088_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(lean_object* v_i_2112_, lean_object* v_source_2113_, lean_object* v_target_2114_){
_start:
{
lean_object* v___x_2115_; uint8_t v___x_2116_; 
v___x_2115_ = lean_array_get_size(v_source_2113_);
v___x_2116_ = lean_nat_dec_lt(v_i_2112_, v___x_2115_);
if (v___x_2116_ == 0)
{
lean_dec_ref(v_source_2113_);
lean_dec(v_i_2112_);
return v_target_2114_;
}
else
{
lean_object* v_es_2117_; lean_object* v___x_2118_; lean_object* v_source_2119_; lean_object* v_target_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v_es_2117_ = lean_array_fget(v_source_2113_, v_i_2112_);
v___x_2118_ = lean_box(0);
v_source_2119_ = lean_array_fset(v_source_2113_, v_i_2112_, v___x_2118_);
v_target_2120_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_target_2114_, v_es_2117_);
v___x_2121_ = lean_unsigned_to_nat(1u);
v___x_2122_ = lean_nat_add(v_i_2112_, v___x_2121_);
lean_dec(v_i_2112_);
v_i_2112_ = v___x_2122_;
v_source_2113_ = v_source_2119_;
v_target_2114_ = v_target_2120_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(lean_object* v_data_2124_){
_start:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v_nbuckets_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2125_ = lean_array_get_size(v_data_2124_);
v___x_2126_ = lean_unsigned_to_nat(2u);
v_nbuckets_2127_ = lean_nat_mul(v___x_2125_, v___x_2126_);
v___x_2128_ = lean_unsigned_to_nat(0u);
v___x_2129_ = lean_box(0);
v___x_2130_ = lean_mk_array(v_nbuckets_2127_, v___x_2129_);
v___x_2131_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v___x_2128_, v_data_2124_, v___x_2130_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(lean_object* v_a_2132_, lean_object* v_b_2133_, lean_object* v_x_2134_){
_start:
{
if (lean_obj_tag(v_x_2134_) == 0)
{
lean_dec(v_b_2133_);
lean_dec_ref(v_a_2132_);
return v_x_2134_;
}
else
{
lean_object* v_key_2135_; lean_object* v_value_2136_; lean_object* v_tail_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2149_; 
v_key_2135_ = lean_ctor_get(v_x_2134_, 0);
v_value_2136_ = lean_ctor_get(v_x_2134_, 1);
v_tail_2137_ = lean_ctor_get(v_x_2134_, 2);
v_isSharedCheck_2149_ = !lean_is_exclusive(v_x_2134_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2139_ = v_x_2134_;
v_isShared_2140_ = v_isSharedCheck_2149_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_tail_2137_);
lean_inc(v_value_2136_);
lean_inc(v_key_2135_);
lean_dec(v_x_2134_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2149_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
uint8_t v___x_2141_; 
v___x_2141_ = l_Lean_ExprStructEq_beq(v_key_2135_, v_a_2132_);
if (v___x_2141_ == 0)
{
lean_object* v___x_2142_; lean_object* v___x_2144_; 
v___x_2142_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(v_a_2132_, v_b_2133_, v_tail_2137_);
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 2, v___x_2142_);
v___x_2144_ = v___x_2139_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_key_2135_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v_value_2136_);
lean_ctor_set(v_reuseFailAlloc_2145_, 2, v___x_2142_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
else
{
lean_object* v___x_2147_; 
lean_dec(v_value_2136_);
lean_dec(v_key_2135_);
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 1, v_b_2133_);
lean_ctor_set(v___x_2139_, 0, v_a_2132_);
v___x_2147_ = v___x_2139_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_a_2132_);
lean_ctor_set(v_reuseFailAlloc_2148_, 1, v_b_2133_);
lean_ctor_set(v_reuseFailAlloc_2148_, 2, v_tail_2137_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(lean_object* v_a_2150_, lean_object* v_x_2151_){
_start:
{
if (lean_obj_tag(v_x_2151_) == 0)
{
uint8_t v___x_2152_; 
v___x_2152_ = 0;
return v___x_2152_;
}
else
{
lean_object* v_key_2153_; lean_object* v_tail_2154_; uint8_t v___x_2155_; 
v_key_2153_ = lean_ctor_get(v_x_2151_, 0);
v_tail_2154_ = lean_ctor_get(v_x_2151_, 2);
v___x_2155_ = l_Lean_ExprStructEq_beq(v_key_2153_, v_a_2150_);
if (v___x_2155_ == 0)
{
v_x_2151_ = v_tail_2154_;
goto _start;
}
else
{
return v___x_2155_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg___boxed(lean_object* v_a_2157_, lean_object* v_x_2158_){
_start:
{
uint8_t v_res_2159_; lean_object* v_r_2160_; 
v_res_2159_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_a_2157_, v_x_2158_);
lean_dec(v_x_2158_);
lean_dec_ref(v_a_2157_);
v_r_2160_ = lean_box(v_res_2159_);
return v_r_2160_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(lean_object* v_m_2161_, lean_object* v_a_2162_, lean_object* v_b_2163_){
_start:
{
lean_object* v_size_2164_; lean_object* v_buckets_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2208_; 
v_size_2164_ = lean_ctor_get(v_m_2161_, 0);
v_buckets_2165_ = lean_ctor_get(v_m_2161_, 1);
v_isSharedCheck_2208_ = !lean_is_exclusive(v_m_2161_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2167_ = v_m_2161_;
v_isShared_2168_ = v_isSharedCheck_2208_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_buckets_2165_);
lean_inc(v_size_2164_);
lean_dec(v_m_2161_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2208_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2169_; uint64_t v___x_2170_; uint64_t v___x_2171_; uint64_t v___x_2172_; uint64_t v_fold_2173_; uint64_t v___x_2174_; uint64_t v___x_2175_; uint64_t v___x_2176_; size_t v___x_2177_; size_t v___x_2178_; size_t v___x_2179_; size_t v___x_2180_; size_t v___x_2181_; lean_object* v_bkt_2182_; uint8_t v___x_2183_; 
v___x_2169_ = lean_array_get_size(v_buckets_2165_);
v___x_2170_ = l_Lean_ExprStructEq_hash(v_a_2162_);
v___x_2171_ = 32ULL;
v___x_2172_ = lean_uint64_shift_right(v___x_2170_, v___x_2171_);
v_fold_2173_ = lean_uint64_xor(v___x_2170_, v___x_2172_);
v___x_2174_ = 16ULL;
v___x_2175_ = lean_uint64_shift_right(v_fold_2173_, v___x_2174_);
v___x_2176_ = lean_uint64_xor(v_fold_2173_, v___x_2175_);
v___x_2177_ = lean_uint64_to_usize(v___x_2176_);
v___x_2178_ = lean_usize_of_nat(v___x_2169_);
v___x_2179_ = ((size_t)1ULL);
v___x_2180_ = lean_usize_sub(v___x_2178_, v___x_2179_);
v___x_2181_ = lean_usize_land(v___x_2177_, v___x_2180_);
v_bkt_2182_ = lean_array_uget_borrowed(v_buckets_2165_, v___x_2181_);
v___x_2183_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_a_2162_, v_bkt_2182_);
if (v___x_2183_ == 0)
{
lean_object* v___x_2184_; lean_object* v_size_x27_2185_; lean_object* v___x_2186_; lean_object* v_buckets_x27_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; uint8_t v___x_2193_; 
v___x_2184_ = lean_unsigned_to_nat(1u);
v_size_x27_2185_ = lean_nat_add(v_size_2164_, v___x_2184_);
lean_dec(v_size_2164_);
lean_inc(v_bkt_2182_);
v___x_2186_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2186_, 0, v_a_2162_);
lean_ctor_set(v___x_2186_, 1, v_b_2163_);
lean_ctor_set(v___x_2186_, 2, v_bkt_2182_);
v_buckets_x27_2187_ = lean_array_uset(v_buckets_2165_, v___x_2181_, v___x_2186_);
v___x_2188_ = lean_unsigned_to_nat(4u);
v___x_2189_ = lean_nat_mul(v_size_x27_2185_, v___x_2188_);
v___x_2190_ = lean_unsigned_to_nat(3u);
v___x_2191_ = lean_nat_div(v___x_2189_, v___x_2190_);
lean_dec(v___x_2189_);
v___x_2192_ = lean_array_get_size(v_buckets_x27_2187_);
v___x_2193_ = lean_nat_dec_le(v___x_2191_, v___x_2192_);
lean_dec(v___x_2191_);
if (v___x_2193_ == 0)
{
lean_object* v_val_2194_; lean_object* v___x_2196_; 
v_val_2194_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(v_buckets_x27_2187_);
if (v_isShared_2168_ == 0)
{
lean_ctor_set(v___x_2167_, 1, v_val_2194_);
lean_ctor_set(v___x_2167_, 0, v_size_x27_2185_);
v___x_2196_ = v___x_2167_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_size_x27_2185_);
lean_ctor_set(v_reuseFailAlloc_2197_, 1, v_val_2194_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
else
{
lean_object* v___x_2199_; 
if (v_isShared_2168_ == 0)
{
lean_ctor_set(v___x_2167_, 1, v_buckets_x27_2187_);
lean_ctor_set(v___x_2167_, 0, v_size_x27_2185_);
v___x_2199_ = v___x_2167_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_size_x27_2185_);
lean_ctor_set(v_reuseFailAlloc_2200_, 1, v_buckets_x27_2187_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
else
{
lean_object* v___x_2201_; lean_object* v_buckets_x27_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2206_; 
lean_inc(v_bkt_2182_);
v___x_2201_ = lean_box(0);
v_buckets_x27_2202_ = lean_array_uset(v_buckets_2165_, v___x_2181_, v___x_2201_);
v___x_2203_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(v_a_2162_, v_b_2163_, v_bkt_2182_);
v___x_2204_ = lean_array_uset(v_buckets_x27_2202_, v___x_2181_, v___x_2203_);
if (v_isShared_2168_ == 0)
{
lean_ctor_set(v___x_2167_, 1, v___x_2204_);
v___x_2206_ = v___x_2167_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_size_2164_);
lean_ctor_set(v_reuseFailAlloc_2207_, 1, v___x_2204_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2(lean_object* v_a_2209_, lean_object* v_e_2210_, lean_object* v_a_2211_){
_start:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2213_ = lean_st_ref_take(v_a_2209_);
v___x_2214_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(v___x_2213_, v_e_2210_, v_a_2211_);
v___x_2215_ = lean_st_ref_set(v_a_2209_, v___x_2214_);
v___x_2216_ = lean_box(0);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2___boxed(lean_object* v_a_2217_, lean_object* v_e_2218_, lean_object* v_a_2219_, lean_object* v___y_2220_){
_start:
{
lean_object* v_res_2221_; 
v_res_2221_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2(v_a_2217_, v_e_2218_, v_a_2219_);
lean_dec(v_a_2217_);
return v_res_2221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0(lean_object* v_fvars_2225_, lean_object* v_pre_2226_, lean_object* v_post_2227_, uint8_t v_usedLetOnly_2228_, uint8_t v_skipConstInApp_2229_, uint8_t v_skipInstances_2230_, lean_object* v_body_2231_, lean_object* v_x_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_){
_start:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2240_ = lean_array_push(v_fvars_2225_, v_x_2232_);
v___x_2241_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(v_pre_2226_, v_post_2227_, v_usedLetOnly_2228_, v_skipConstInApp_2229_, v_skipInstances_2230_, v___x_2240_, v_body_2231_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0___boxed(lean_object* v_fvars_2242_, lean_object* v_pre_2243_, lean_object* v_post_2244_, lean_object* v_usedLetOnly_2245_, lean_object* v_skipConstInApp_2246_, lean_object* v_skipInstances_2247_, lean_object* v_body_2248_, lean_object* v_x_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_){
_start:
{
uint8_t v_usedLetOnly_boxed_2257_; uint8_t v_skipConstInApp_boxed_2258_; uint8_t v_skipInstances_boxed_2259_; lean_object* v_res_2260_; 
v_usedLetOnly_boxed_2257_ = lean_unbox(v_usedLetOnly_2245_);
v_skipConstInApp_boxed_2258_ = lean_unbox(v_skipConstInApp_2246_);
v_skipInstances_boxed_2259_ = lean_unbox(v_skipInstances_2247_);
v_res_2260_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0(v_fvars_2242_, v_pre_2243_, v_post_2244_, v_usedLetOnly_boxed_2257_, v_skipConstInApp_boxed_2258_, v_skipInstances_boxed_2259_, v_body_2248_, v_x_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
lean_dec(v___y_2251_);
lean_dec(v___y_2250_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(lean_object* v_pre_2261_, lean_object* v_post_2262_, uint8_t v_usedLetOnly_2263_, uint8_t v_skipConstInApp_2264_, uint8_t v_skipInstances_2265_, lean_object* v_e_2266_, lean_object* v_a_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_){
_start:
{
lean_object* v___x_2274_; 
lean_inc_ref(v_post_2262_);
lean_inc(v___y_2272_);
lean_inc_ref(v___y_2271_);
lean_inc(v___y_2270_);
lean_inc_ref(v___y_2269_);
lean_inc(v___y_2268_);
lean_inc_ref(v_e_2266_);
v___x_2274_ = lean_apply_7(v_post_2262_, v_e_2266_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, lean_box(0));
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v_a_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2293_; 
v_a_2275_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2277_ = v___x_2274_;
v_isShared_2278_ = v_isSharedCheck_2293_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_a_2275_);
lean_dec(v___x_2274_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2293_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
switch(lean_obj_tag(v_a_2275_))
{
case 0:
{
lean_object* v_e_2279_; lean_object* v___x_2281_; 
lean_dec_ref(v_e_2266_);
lean_dec_ref(v_post_2262_);
lean_dec_ref(v_pre_2261_);
v_e_2279_ = lean_ctor_get(v_a_2275_, 0);
lean_inc_ref(v_e_2279_);
lean_dec_ref(v_a_2275_);
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 0, v_e_2279_);
v___x_2281_ = v___x_2277_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_e_2279_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
case 1:
{
lean_object* v_e_2283_; lean_object* v___x_2284_; 
lean_del_object(v___x_2277_);
lean_dec_ref(v_e_2266_);
v_e_2283_ = lean_ctor_get(v_a_2275_, 0);
lean_inc_ref(v_e_2283_);
lean_dec_ref(v_a_2275_);
v___x_2284_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2261_, v_post_2262_, v_usedLetOnly_2263_, v_skipConstInApp_2264_, v_skipInstances_2265_, v_e_2283_, v_a_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
return v___x_2284_;
}
default: 
{
lean_object* v_e_x3f_2285_; 
lean_dec_ref(v_post_2262_);
lean_dec_ref(v_pre_2261_);
v_e_x3f_2285_ = lean_ctor_get(v_a_2275_, 0);
lean_inc(v_e_x3f_2285_);
lean_dec_ref(v_a_2275_);
if (lean_obj_tag(v_e_x3f_2285_) == 0)
{
lean_object* v___x_2287_; 
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 0, v_e_2266_);
v___x_2287_ = v___x_2277_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_e_2266_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
else
{
lean_object* v_val_2289_; lean_object* v___x_2291_; 
lean_dec_ref(v_e_2266_);
v_val_2289_ = lean_ctor_get(v_e_x3f_2285_, 0);
lean_inc(v_val_2289_);
lean_dec_ref(v_e_x3f_2285_);
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 0, v_val_2289_);
v___x_2291_ = v___x_2277_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_val_2289_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
}
}
}
else
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2301_; 
lean_dec_ref(v_e_2266_);
lean_dec_ref(v_post_2262_);
lean_dec_ref(v_pre_2261_);
v_a_2294_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2296_ = v___x_2274_;
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2274_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2299_; 
if (v_isShared_2297_ == 0)
{
v___x_2299_ = v___x_2296_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_a_2294_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(lean_object* v_pre_2302_, lean_object* v_post_2303_, uint8_t v_usedLetOnly_2304_, uint8_t v_skipConstInApp_2305_, uint8_t v_skipInstances_2306_, lean_object* v_fvars_2307_, lean_object* v_e_2308_, lean_object* v_a_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
if (lean_obj_tag(v_e_2308_) == 6)
{
lean_object* v_binderName_2316_; lean_object* v_binderType_2317_; lean_object* v_body_2318_; uint8_t v_binderInfo_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v_binderName_2316_ = lean_ctor_get(v_e_2308_, 0);
lean_inc(v_binderName_2316_);
v_binderType_2317_ = lean_ctor_get(v_e_2308_, 1);
lean_inc_ref(v_binderType_2317_);
v_body_2318_ = lean_ctor_get(v_e_2308_, 2);
lean_inc_ref(v_body_2318_);
v_binderInfo_2319_ = lean_ctor_get_uint8(v_e_2308_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_2308_);
v___x_2320_ = lean_expr_instantiate_rev(v_binderType_2317_, v_fvars_2307_);
lean_dec_ref(v_binderType_2317_);
lean_inc_ref(v_post_2303_);
lean_inc_ref(v_pre_2302_);
v___x_2321_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2302_, v_post_2303_, v_usedLetOnly_2304_, v_skipConstInApp_2305_, v_skipInstances_2306_, v___x_2320_, v_a_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_object* v_a_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___f_2326_; uint8_t v___x_2327_; lean_object* v___x_2328_; 
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
lean_inc(v_a_2322_);
lean_dec_ref(v___x_2321_);
v___x_2323_ = lean_box(v_usedLetOnly_2304_);
v___x_2324_ = lean_box(v_skipConstInApp_2305_);
v___x_2325_ = lean_box(v_skipInstances_2306_);
v___f_2326_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0___boxed), 15, 7);
lean_closure_set(v___f_2326_, 0, v_fvars_2307_);
lean_closure_set(v___f_2326_, 1, v_pre_2302_);
lean_closure_set(v___f_2326_, 2, v_post_2303_);
lean_closure_set(v___f_2326_, 3, v___x_2323_);
lean_closure_set(v___f_2326_, 4, v___x_2324_);
lean_closure_set(v___f_2326_, 5, v___x_2325_);
lean_closure_set(v___f_2326_, 6, v_body_2318_);
v___x_2327_ = 0;
v___x_2328_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_2316_, v_binderInfo_2319_, v_a_2322_, v___f_2326_, v___x_2327_, v_a_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
return v___x_2328_;
}
else
{
lean_dec_ref(v_body_2318_);
lean_dec(v_binderName_2316_);
lean_dec_ref(v_fvars_2307_);
lean_dec_ref(v_post_2303_);
lean_dec_ref(v_pre_2302_);
return v___x_2321_;
}
}
else
{
lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2329_ = lean_expr_instantiate_rev(v_e_2308_, v_fvars_2307_);
lean_dec_ref(v_e_2308_);
lean_inc_ref(v_post_2303_);
lean_inc_ref(v_pre_2302_);
v___x_2330_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2302_, v_post_2303_, v_usedLetOnly_2304_, v_skipConstInApp_2305_, v_skipInstances_2306_, v___x_2329_, v_a_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v_a_2331_; uint8_t v___x_2332_; uint8_t v___x_2333_; uint8_t v___x_2334_; lean_object* v___x_2335_; 
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
lean_inc(v_a_2331_);
lean_dec_ref(v___x_2330_);
v___x_2332_ = 0;
v___x_2333_ = 1;
v___x_2334_ = 1;
v___x_2335_ = l_Lean_Meta_mkLambdaFVars(v_fvars_2307_, v_a_2331_, v___x_2332_, v_usedLetOnly_2304_, v___x_2332_, v___x_2333_, v___x_2334_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
lean_dec_ref(v_fvars_2307_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v_a_2336_; lean_object* v___x_2337_; 
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
lean_inc(v_a_2336_);
lean_dec_ref(v___x_2335_);
v___x_2337_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2302_, v_post_2303_, v_usedLetOnly_2304_, v_skipConstInApp_2305_, v_skipInstances_2306_, v_a_2336_, v_a_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
return v___x_2337_;
}
else
{
lean_dec_ref(v_post_2303_);
lean_dec_ref(v_pre_2302_);
return v___x_2335_;
}
}
else
{
lean_dec_ref(v_fvars_2307_);
lean_dec_ref(v_post_2303_);
lean_dec_ref(v_pre_2302_);
return v___x_2330_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0(lean_object* v_fvars_2338_, lean_object* v_pre_2339_, lean_object* v_post_2340_, uint8_t v_usedLetOnly_2341_, uint8_t v_skipConstInApp_2342_, uint8_t v_skipInstances_2343_, lean_object* v_body_2344_, lean_object* v_x_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___x_2353_ = lean_array_push(v_fvars_2338_, v_x_2345_);
v___x_2354_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(v_pre_2339_, v_post_2340_, v_usedLetOnly_2341_, v_skipConstInApp_2342_, v_skipInstances_2343_, v___x_2353_, v_body_2344_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
return v___x_2354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0___boxed(lean_object* v_fvars_2355_, lean_object* v_pre_2356_, lean_object* v_post_2357_, lean_object* v_usedLetOnly_2358_, lean_object* v_skipConstInApp_2359_, lean_object* v_skipInstances_2360_, lean_object* v_body_2361_, lean_object* v_x_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
uint8_t v_usedLetOnly_boxed_2370_; uint8_t v_skipConstInApp_boxed_2371_; uint8_t v_skipInstances_boxed_2372_; lean_object* v_res_2373_; 
v_usedLetOnly_boxed_2370_ = lean_unbox(v_usedLetOnly_2358_);
v_skipConstInApp_boxed_2371_ = lean_unbox(v_skipConstInApp_2359_);
v_skipInstances_boxed_2372_ = lean_unbox(v_skipInstances_2360_);
v_res_2373_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0(v_fvars_2355_, v_pre_2356_, v_post_2357_, v_usedLetOnly_boxed_2370_, v_skipConstInApp_boxed_2371_, v_skipInstances_boxed_2372_, v_body_2361_, v_x_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec(v___y_2363_);
return v_res_2373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(lean_object* v_pre_2374_, lean_object* v_post_2375_, uint8_t v_usedLetOnly_2376_, uint8_t v_skipConstInApp_2377_, uint8_t v_skipInstances_2378_, lean_object* v_fvars_2379_, lean_object* v_e_2380_, lean_object* v_a_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
if (lean_obj_tag(v_e_2380_) == 8)
{
lean_object* v_declName_2388_; lean_object* v_type_2389_; lean_object* v_value_2390_; lean_object* v_body_2391_; uint8_t v_nondep_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v_declName_2388_ = lean_ctor_get(v_e_2380_, 0);
lean_inc(v_declName_2388_);
v_type_2389_ = lean_ctor_get(v_e_2380_, 1);
lean_inc_ref(v_type_2389_);
v_value_2390_ = lean_ctor_get(v_e_2380_, 2);
lean_inc_ref(v_value_2390_);
v_body_2391_ = lean_ctor_get(v_e_2380_, 3);
lean_inc_ref(v_body_2391_);
v_nondep_2392_ = lean_ctor_get_uint8(v_e_2380_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_2380_);
v___x_2393_ = lean_expr_instantiate_rev(v_type_2389_, v_fvars_2379_);
lean_dec_ref(v_type_2389_);
lean_inc_ref(v_post_2375_);
lean_inc_ref(v_pre_2374_);
v___x_2394_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2374_, v_post_2375_, v_usedLetOnly_2376_, v_skipConstInApp_2377_, v_skipInstances_2378_, v___x_2393_, v_a_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_object* v_a_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
lean_inc(v_a_2395_);
lean_dec_ref(v___x_2394_);
v___x_2396_ = lean_expr_instantiate_rev(v_value_2390_, v_fvars_2379_);
lean_dec_ref(v_value_2390_);
lean_inc_ref(v_post_2375_);
lean_inc_ref(v_pre_2374_);
v___x_2397_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2374_, v_post_2375_, v_usedLetOnly_2376_, v_skipConstInApp_2377_, v_skipInstances_2378_, v___x_2396_, v_a_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
if (lean_obj_tag(v___x_2397_) == 0)
{
lean_object* v_a_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___f_2402_; uint8_t v___x_2403_; lean_object* v___x_2404_; 
v_a_2398_ = lean_ctor_get(v___x_2397_, 0);
lean_inc(v_a_2398_);
lean_dec_ref(v___x_2397_);
v___x_2399_ = lean_box(v_usedLetOnly_2376_);
v___x_2400_ = lean_box(v_skipConstInApp_2377_);
v___x_2401_ = lean_box(v_skipInstances_2378_);
v___f_2402_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0___boxed), 15, 7);
lean_closure_set(v___f_2402_, 0, v_fvars_2379_);
lean_closure_set(v___f_2402_, 1, v_pre_2374_);
lean_closure_set(v___f_2402_, 2, v_post_2375_);
lean_closure_set(v___f_2402_, 3, v___x_2399_);
lean_closure_set(v___f_2402_, 4, v___x_2400_);
lean_closure_set(v___f_2402_, 5, v___x_2401_);
lean_closure_set(v___f_2402_, 6, v_body_2391_);
v___x_2403_ = 0;
v___x_2404_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_declName_2388_, v_a_2395_, v_a_2398_, v___f_2402_, v_nondep_2392_, v___x_2403_, v_a_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
return v___x_2404_;
}
else
{
lean_dec(v_a_2395_);
lean_dec_ref(v_body_2391_);
lean_dec(v_declName_2388_);
lean_dec_ref(v_fvars_2379_);
lean_dec_ref(v_post_2375_);
lean_dec_ref(v_pre_2374_);
return v___x_2397_;
}
}
else
{
lean_dec_ref(v_body_2391_);
lean_dec_ref(v_value_2390_);
lean_dec(v_declName_2388_);
lean_dec_ref(v_fvars_2379_);
lean_dec_ref(v_post_2375_);
lean_dec_ref(v_pre_2374_);
return v___x_2394_;
}
}
else
{
lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2405_ = lean_expr_instantiate_rev(v_e_2380_, v_fvars_2379_);
lean_dec_ref(v_e_2380_);
lean_inc_ref(v_post_2375_);
lean_inc_ref(v_pre_2374_);
v___x_2406_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2374_, v_post_2375_, v_usedLetOnly_2376_, v_skipConstInApp_2377_, v_skipInstances_2378_, v___x_2405_, v_a_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v_a_2407_; uint8_t v___x_2408_; uint8_t v___x_2409_; lean_object* v___x_2410_; 
v_a_2407_ = lean_ctor_get(v___x_2406_, 0);
lean_inc(v_a_2407_);
lean_dec_ref(v___x_2406_);
v___x_2408_ = 0;
v___x_2409_ = 1;
v___x_2410_ = l_Lean_Meta_mkLetFVars(v_fvars_2379_, v_a_2407_, v_usedLetOnly_2376_, v___x_2408_, v___x_2409_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
lean_dec_ref(v_fvars_2379_);
if (lean_obj_tag(v___x_2410_) == 0)
{
lean_object* v_a_2411_; lean_object* v___x_2412_; 
v_a_2411_ = lean_ctor_get(v___x_2410_, 0);
lean_inc(v_a_2411_);
lean_dec_ref(v___x_2410_);
v___x_2412_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2374_, v_post_2375_, v_usedLetOnly_2376_, v_skipConstInApp_2377_, v_skipInstances_2378_, v_a_2411_, v_a_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
return v___x_2412_;
}
else
{
lean_dec_ref(v_post_2375_);
lean_dec_ref(v_pre_2374_);
return v___x_2410_;
}
}
else
{
lean_dec_ref(v_fvars_2379_);
lean_dec_ref(v_post_2375_);
lean_dec_ref(v_pre_2374_);
return v___x_2406_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2413_; lean_object* v_dummy_2414_; 
v___x_2413_ = lean_box(0);
v_dummy_2414_ = l_Lean_Expr_sort___override(v___x_2413_);
return v_dummy_2414_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(lean_object* v_pre_2415_, lean_object* v_post_2416_, uint8_t v_usedLetOnly_2417_, uint8_t v_skipConstInApp_2418_, uint8_t v_skipInstances_2419_, size_t v_sz_2420_, size_t v_i_2421_, lean_object* v_bs_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
uint8_t v___x_2430_; 
v___x_2430_ = lean_usize_dec_lt(v_i_2421_, v_sz_2420_);
if (v___x_2430_ == 0)
{
lean_object* v___x_2431_; 
lean_dec_ref(v_post_2416_);
lean_dec_ref(v_pre_2415_);
v___x_2431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2431_, 0, v_bs_2422_);
return v___x_2431_;
}
else
{
lean_object* v_v_2432_; lean_object* v___x_2433_; 
v_v_2432_ = lean_array_uget_borrowed(v_bs_2422_, v_i_2421_);
lean_inc(v_v_2432_);
lean_inc_ref(v_post_2416_);
lean_inc_ref(v_pre_2415_);
v___x_2433_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2415_, v_post_2416_, v_usedLetOnly_2417_, v_skipConstInApp_2418_, v_skipInstances_2419_, v_v_2432_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
if (lean_obj_tag(v___x_2433_) == 0)
{
lean_object* v_a_2434_; lean_object* v___x_2435_; lean_object* v_bs_x27_2436_; size_t v___x_2437_; size_t v___x_2438_; lean_object* v___x_2439_; 
v_a_2434_ = lean_ctor_get(v___x_2433_, 0);
lean_inc(v_a_2434_);
lean_dec_ref(v___x_2433_);
v___x_2435_ = lean_unsigned_to_nat(0u);
v_bs_x27_2436_ = lean_array_uset(v_bs_2422_, v_i_2421_, v___x_2435_);
v___x_2437_ = ((size_t)1ULL);
v___x_2438_ = lean_usize_add(v_i_2421_, v___x_2437_);
v___x_2439_ = lean_array_uset(v_bs_x27_2436_, v_i_2421_, v_a_2434_);
v_i_2421_ = v___x_2438_;
v_bs_2422_ = v___x_2439_;
goto _start;
}
else
{
lean_object* v_a_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2448_; 
lean_dec_ref(v_bs_2422_);
lean_dec_ref(v_post_2416_);
lean_dec_ref(v_pre_2415_);
v_a_2441_ = lean_ctor_get(v___x_2433_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2443_ = v___x_2433_;
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_a_2441_);
lean_dec(v___x_2433_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2446_; 
if (v_isShared_2444_ == 0)
{
v___x_2446_ = v___x_2443_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_a_2441_);
v___x_2446_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
return v___x_2446_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0(lean_object* v_pre_2449_, lean_object* v_post_2450_, uint8_t v_usedLetOnly_2451_, uint8_t v_skipConstInApp_2452_, uint8_t v_skipInstances_2453_, lean_object* v___x_2454_, lean_object* v___y_2455_, lean_object* v_b_2456_, lean_object* v_a_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_){
_start:
{
lean_object* v___x_2464_; 
v___x_2464_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2449_, v_post_2450_, v_usedLetOnly_2451_, v_skipConstInApp_2452_, v_skipInstances_2453_, v___x_2454_, v___y_2455_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_);
if (lean_obj_tag(v___x_2464_) == 0)
{
lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2474_; 
v_a_2465_ = lean_ctor_get(v___x_2464_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2467_ = v___x_2464_;
v_isShared_2468_ = v_isSharedCheck_2474_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_dec(v___x_2464_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2474_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2472_; 
v___x_2469_ = lean_array_fset(v_b_2456_, v_a_2457_, v_a_2465_);
v___x_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2469_);
if (v_isShared_2468_ == 0)
{
lean_ctor_set(v___x_2467_, 0, v___x_2470_);
v___x_2472_ = v___x_2467_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v___x_2470_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
else
{
lean_object* v_a_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2482_; 
lean_dec_ref(v_b_2456_);
v_a_2475_ = lean_ctor_get(v___x_2464_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2477_ = v___x_2464_;
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_a_2475_);
lean_dec(v___x_2464_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2480_; 
if (v_isShared_2478_ == 0)
{
v___x_2480_ = v___x_2477_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_a_2475_);
v___x_2480_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
return v___x_2480_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed(lean_object* v_pre_2483_, lean_object* v_post_2484_, lean_object* v_usedLetOnly_2485_, lean_object* v_skipConstInApp_2486_, lean_object* v_skipInstances_2487_, lean_object* v___x_2488_, lean_object* v___y_2489_, lean_object* v_b_2490_, lean_object* v_a_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_){
_start:
{
uint8_t v_usedLetOnly_boxed_2498_; uint8_t v_skipConstInApp_boxed_2499_; uint8_t v_skipInstances_boxed_2500_; lean_object* v_res_2501_; 
v_usedLetOnly_boxed_2498_ = lean_unbox(v_usedLetOnly_2485_);
v_skipConstInApp_boxed_2499_ = lean_unbox(v_skipConstInApp_2486_);
v_skipInstances_boxed_2500_ = lean_unbox(v_skipInstances_2487_);
v_res_2501_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0(v_pre_2483_, v_post_2484_, v_usedLetOnly_boxed_2498_, v_skipConstInApp_boxed_2499_, v_skipInstances_boxed_2500_, v___x_2488_, v___y_2489_, v_b_2490_, v_a_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_);
lean_dec(v___y_2496_);
lean_dec_ref(v___y_2495_);
lean_dec(v___y_2494_);
lean_dec_ref(v___y_2493_);
lean_dec(v___y_2492_);
lean_dec(v_a_2491_);
lean_dec(v___y_2489_);
return v_res_2501_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(lean_object* v_upperBound_2502_, lean_object* v___x_2503_, lean_object* v_pre_2504_, lean_object* v_post_2505_, uint8_t v_usedLetOnly_2506_, uint8_t v_skipConstInApp_2507_, uint8_t v_skipInstances_2508_, lean_object* v_a_2509_, lean_object* v_b_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
lean_object* v___y_2519_; uint8_t v___x_2542_; 
v___x_2542_ = lean_nat_dec_lt(v_a_2509_, v_upperBound_2502_);
if (v___x_2542_ == 0)
{
lean_object* v___x_2543_; 
lean_dec(v_a_2509_);
lean_dec_ref(v_post_2505_);
lean_dec_ref(v_pre_2504_);
v___x_2543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2543_, 0, v_b_2510_);
return v___x_2543_;
}
else
{
lean_object* v___x_2544_; lean_object* v___x_2545_; uint8_t v___x_2546_; 
v___x_2544_ = lean_array_fget_borrowed(v_b_2510_, v_a_2509_);
v___x_2545_ = lean_array_get_size(v___x_2503_);
v___x_2546_ = lean_nat_dec_lt(v_a_2509_, v___x_2545_);
if (v___x_2546_ == 0)
{
lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___f_2550_; 
lean_inc(v___x_2544_);
v___x_2547_ = lean_box(v_usedLetOnly_2506_);
v___x_2548_ = lean_box(v_skipConstInApp_2507_);
v___x_2549_ = lean_box(v_skipInstances_2508_);
lean_inc(v_a_2509_);
lean_inc(v___y_2511_);
lean_inc_ref(v_post_2505_);
lean_inc_ref(v_pre_2504_);
v___f_2550_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_2550_, 0, v_pre_2504_);
lean_closure_set(v___f_2550_, 1, v_post_2505_);
lean_closure_set(v___f_2550_, 2, v___x_2547_);
lean_closure_set(v___f_2550_, 3, v___x_2548_);
lean_closure_set(v___f_2550_, 4, v___x_2549_);
lean_closure_set(v___f_2550_, 5, v___x_2544_);
lean_closure_set(v___f_2550_, 6, v___y_2511_);
lean_closure_set(v___f_2550_, 7, v_b_2510_);
lean_closure_set(v___f_2550_, 8, v_a_2509_);
v___y_2519_ = v___f_2550_;
goto v___jp_2518_;
}
else
{
lean_object* v___x_2551_; uint8_t v_isInstance_2552_; 
v___x_2551_ = lean_array_fget_borrowed(v___x_2503_, v_a_2509_);
v_isInstance_2552_ = lean_ctor_get_uint8(v___x_2551_, sizeof(void*)*1 + 4);
if (v_isInstance_2552_ == 0)
{
lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___f_2556_; 
lean_inc(v___x_2544_);
v___x_2553_ = lean_box(v_usedLetOnly_2506_);
v___x_2554_ = lean_box(v_skipConstInApp_2507_);
v___x_2555_ = lean_box(v_skipInstances_2508_);
lean_inc(v_a_2509_);
lean_inc(v___y_2511_);
lean_inc_ref(v_post_2505_);
lean_inc_ref(v_pre_2504_);
v___f_2556_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_2556_, 0, v_pre_2504_);
lean_closure_set(v___f_2556_, 1, v_post_2505_);
lean_closure_set(v___f_2556_, 2, v___x_2553_);
lean_closure_set(v___f_2556_, 3, v___x_2554_);
lean_closure_set(v___f_2556_, 4, v___x_2555_);
lean_closure_set(v___f_2556_, 5, v___x_2544_);
lean_closure_set(v___f_2556_, 6, v___y_2511_);
lean_closure_set(v___f_2556_, 7, v_b_2510_);
lean_closure_set(v___f_2556_, 8, v_a_2509_);
v___y_2519_ = v___f_2556_;
goto v___jp_2518_;
}
else
{
lean_object* v___x_2557_; lean_object* v___f_2558_; 
v___x_2557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2557_, 0, v_b_2510_);
v___f_2558_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2558_, 0, v___x_2557_);
v___y_2519_ = v___f_2558_;
goto v___jp_2518_;
}
}
}
v___jp_2518_:
{
lean_object* v___x_2520_; 
lean_inc(v___y_2516_);
lean_inc_ref(v___y_2515_);
lean_inc(v___y_2514_);
lean_inc_ref(v___y_2513_);
lean_inc(v___y_2512_);
v___x_2520_ = lean_apply_6(v___y_2519_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, lean_box(0));
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v_a_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2533_; 
v_a_2521_ = lean_ctor_get(v___x_2520_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2523_ = v___x_2520_;
v_isShared_2524_ = v_isSharedCheck_2533_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_a_2521_);
lean_dec(v___x_2520_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2533_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
if (lean_obj_tag(v_a_2521_) == 0)
{
lean_object* v_a_2525_; lean_object* v___x_2527_; 
lean_dec(v_a_2509_);
lean_dec_ref(v_post_2505_);
lean_dec_ref(v_pre_2504_);
v_a_2525_ = lean_ctor_get(v_a_2521_, 0);
lean_inc(v_a_2525_);
lean_dec_ref(v_a_2521_);
if (v_isShared_2524_ == 0)
{
lean_ctor_set(v___x_2523_, 0, v_a_2525_);
v___x_2527_ = v___x_2523_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_a_2525_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
return v___x_2527_;
}
}
else
{
lean_object* v_a_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
lean_del_object(v___x_2523_);
v_a_2529_ = lean_ctor_get(v_a_2521_, 0);
lean_inc(v_a_2529_);
lean_dec_ref(v_a_2521_);
v___x_2530_ = lean_unsigned_to_nat(1u);
v___x_2531_ = lean_nat_add(v_a_2509_, v___x_2530_);
lean_dec(v_a_2509_);
v_a_2509_ = v___x_2531_;
v_b_2510_ = v_a_2529_;
goto _start;
}
}
}
else
{
lean_object* v_a_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2541_; 
lean_dec(v_a_2509_);
lean_dec_ref(v_post_2505_);
lean_dec_ref(v_pre_2504_);
v_a_2534_ = lean_ctor_get(v___x_2520_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2536_ = v___x_2520_;
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_a_2534_);
lean_dec(v___x_2520_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2539_; 
if (v_isShared_2537_ == 0)
{
v___x_2539_ = v___x_2536_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_a_2534_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(uint8_t v_skipInstances_2559_, lean_object* v_pre_2560_, lean_object* v_post_2561_, uint8_t v_usedLetOnly_2562_, uint8_t v_skipConstInApp_2563_, lean_object* v_x_2564_, lean_object* v_x_2565_, lean_object* v_x_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
lean_object* v_f_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; 
if (lean_obj_tag(v_x_2564_) == 5)
{
lean_object* v_fn_2624_; lean_object* v_arg_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
v_fn_2624_ = lean_ctor_get(v_x_2564_, 0);
lean_inc_ref(v_fn_2624_);
v_arg_2625_ = lean_ctor_get(v_x_2564_, 1);
lean_inc_ref(v_arg_2625_);
lean_dec_ref(v_x_2564_);
v___x_2626_ = lean_array_set(v_x_2565_, v_x_2566_, v_arg_2625_);
v___x_2627_ = lean_unsigned_to_nat(1u);
v___x_2628_ = lean_nat_sub(v_x_2566_, v___x_2627_);
lean_dec(v_x_2566_);
v_x_2564_ = v_fn_2624_;
v_x_2565_ = v___x_2626_;
v_x_2566_ = v___x_2628_;
goto _start;
}
else
{
lean_dec(v_x_2566_);
if (v_skipConstInApp_2563_ == 0)
{
goto v___jp_2621_;
}
else
{
uint8_t v___x_2630_; 
v___x_2630_ = l_Lean_Expr_isConst(v_x_2564_);
if (v___x_2630_ == 0)
{
goto v___jp_2621_;
}
else
{
v_f_2575_ = v_x_2564_;
v___y_2576_ = v___y_2567_;
v___y_2577_ = v___y_2568_;
v___y_2578_ = v___y_2569_;
v___y_2579_ = v___y_2570_;
v___y_2580_ = v___y_2571_;
v___y_2581_ = v___y_2572_;
goto v___jp_2574_;
}
}
}
v___jp_2574_:
{
if (v_skipInstances_2559_ == 0)
{
size_t v_sz_2582_; size_t v___x_2583_; lean_object* v___x_2584_; 
v_sz_2582_ = lean_array_size(v_x_2565_);
v___x_2583_ = ((size_t)0ULL);
lean_inc_ref(v_post_2561_);
lean_inc_ref(v_pre_2560_);
v___x_2584_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(v_pre_2560_, v_post_2561_, v_usedLetOnly_2562_, v_skipConstInApp_2563_, v_skipInstances_2559_, v_sz_2582_, v___x_2583_, v_x_2565_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_object* v_a_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; 
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
lean_inc(v_a_2585_);
lean_dec_ref(v___x_2584_);
v___x_2586_ = l_Lean_mkAppN(v_f_2575_, v_a_2585_);
lean_dec(v_a_2585_);
v___x_2587_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2560_, v_post_2561_, v_usedLetOnly_2562_, v_skipConstInApp_2563_, v_skipInstances_2559_, v___x_2586_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
return v___x_2587_;
}
else
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2595_; 
lean_dec_ref(v_f_2575_);
lean_dec_ref(v_post_2561_);
lean_dec_ref(v_pre_2560_);
v_a_2588_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2590_ = v___x_2584_;
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2584_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2593_; 
if (v_isShared_2591_ == 0)
{
v___x_2593_ = v___x_2590_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_a_2588_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
}
else
{
lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2596_ = lean_array_get_size(v_x_2565_);
lean_inc_ref(v_f_2575_);
v___x_2597_ = l_Lean_Meta_getFunInfoNArgs(v_f_2575_, v___x_2596_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2598_; lean_object* v_paramInfo_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
lean_inc(v_a_2598_);
lean_dec_ref(v___x_2597_);
v_paramInfo_2599_ = lean_ctor_get(v_a_2598_, 0);
lean_inc_ref(v_paramInfo_2599_);
lean_dec(v_a_2598_);
v___x_2600_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_2561_);
lean_inc_ref(v_pre_2560_);
v___x_2601_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(v___x_2596_, v_paramInfo_2599_, v_pre_2560_, v_post_2561_, v_usedLetOnly_2562_, v_skipConstInApp_2563_, v_skipInstances_2559_, v___x_2600_, v_x_2565_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
lean_dec_ref(v_paramInfo_2599_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v_a_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; 
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
lean_inc(v_a_2602_);
lean_dec_ref(v___x_2601_);
v___x_2603_ = l_Lean_mkAppN(v_f_2575_, v_a_2602_);
lean_dec(v_a_2602_);
v___x_2604_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2560_, v_post_2561_, v_usedLetOnly_2562_, v_skipConstInApp_2563_, v_skipInstances_2559_, v___x_2603_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
return v___x_2604_;
}
else
{
lean_object* v_a_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2612_; 
lean_dec_ref(v_f_2575_);
lean_dec_ref(v_post_2561_);
lean_dec_ref(v_pre_2560_);
v_a_2605_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2607_ = v___x_2601_;
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_a_2605_);
lean_dec(v___x_2601_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2610_; 
if (v_isShared_2608_ == 0)
{
v___x_2610_ = v___x_2607_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_a_2605_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
}
else
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2620_; 
lean_dec_ref(v_f_2575_);
lean_dec_ref(v_x_2565_);
lean_dec_ref(v_post_2561_);
lean_dec_ref(v_pre_2560_);
v_a_2613_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2615_ = v___x_2597_;
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2597_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2618_; 
if (v_isShared_2616_ == 0)
{
v___x_2618_ = v___x_2615_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_a_2613_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
}
v___jp_2621_:
{
lean_object* v___x_2622_; 
lean_inc_ref(v_post_2561_);
lean_inc_ref(v_pre_2560_);
v___x_2622_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2560_, v_post_2561_, v_usedLetOnly_2562_, v_skipConstInApp_2563_, v_skipInstances_2559_, v_x_2564_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_);
if (lean_obj_tag(v___x_2622_) == 0)
{
lean_object* v_a_2623_; 
v_a_2623_ = lean_ctor_get(v___x_2622_, 0);
lean_inc(v_a_2623_);
lean_dec_ref(v___x_2622_);
v_f_2575_ = v_a_2623_;
v___y_2576_ = v___y_2567_;
v___y_2577_ = v___y_2568_;
v___y_2578_ = v___y_2569_;
v___y_2579_ = v___y_2570_;
v___y_2580_ = v___y_2571_;
v___y_2581_ = v___y_2572_;
goto v___jp_2574_;
}
else
{
lean_dec_ref(v_x_2565_);
lean_dec_ref(v_post_2561_);
lean_dec_ref(v_pre_2560_);
return v___x_2622_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1(lean_object* v___x_2631_, lean_object* v_pre_2632_, lean_object* v_e_2633_, lean_object* v_post_2634_, uint8_t v_usedLetOnly_2635_, uint8_t v_skipConstInApp_2636_, uint8_t v_skipInstances_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_){
_start:
{
lean_object* v___x_2645_; 
v___x_2645_ = l_Lean_Core_checkSystem(v___x_2631_, v___y_2642_, v___y_2643_);
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_object* v___x_2646_; 
lean_dec_ref(v___x_2645_);
lean_inc_ref(v_pre_2632_);
lean_inc(v___y_2643_);
lean_inc_ref(v___y_2642_);
lean_inc(v___y_2641_);
lean_inc_ref(v___y_2640_);
lean_inc(v___y_2639_);
lean_inc_ref(v_e_2633_);
v___x_2646_ = lean_apply_7(v_pre_2632_, v_e_2633_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, lean_box(0));
if (lean_obj_tag(v___x_2646_) == 0)
{
lean_object* v_a_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2695_; 
v_a_2647_ = lean_ctor_get(v___x_2646_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2646_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2649_ = v___x_2646_;
v_isShared_2650_ = v_isSharedCheck_2695_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_a_2647_);
lean_dec(v___x_2646_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2695_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v___y_2652_; 
switch(lean_obj_tag(v_a_2647_))
{
case 0:
{
lean_object* v_e_2687_; lean_object* v___x_2689_; 
lean_dec_ref(v_post_2634_);
lean_dec_ref(v_e_2633_);
lean_dec_ref(v_pre_2632_);
v_e_2687_ = lean_ctor_get(v_a_2647_, 0);
lean_inc_ref(v_e_2687_);
lean_dec_ref(v_a_2647_);
if (v_isShared_2650_ == 0)
{
lean_ctor_set(v___x_2649_, 0, v_e_2687_);
v___x_2689_ = v___x_2649_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_e_2687_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
case 1:
{
lean_object* v_e_2691_; lean_object* v___x_2692_; 
lean_del_object(v___x_2649_);
lean_dec_ref(v_e_2633_);
v_e_2691_ = lean_ctor_get(v_a_2647_, 0);
lean_inc_ref(v_e_2691_);
lean_dec_ref(v_a_2647_);
v___x_2692_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2632_, v_post_2634_, v_usedLetOnly_2635_, v_skipConstInApp_2636_, v_skipInstances_2637_, v_e_2691_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
return v___x_2692_;
}
default: 
{
lean_object* v_e_x3f_2693_; 
lean_del_object(v___x_2649_);
v_e_x3f_2693_ = lean_ctor_get(v_a_2647_, 0);
lean_inc(v_e_x3f_2693_);
lean_dec_ref(v_a_2647_);
if (lean_obj_tag(v_e_x3f_2693_) == 0)
{
v___y_2652_ = v_e_2633_;
goto v___jp_2651_;
}
else
{
lean_object* v_val_2694_; 
lean_dec_ref(v_e_2633_);
v_val_2694_ = lean_ctor_get(v_e_x3f_2693_, 0);
lean_inc(v_val_2694_);
lean_dec_ref(v_e_x3f_2693_);
v___y_2652_ = v_val_2694_;
goto v___jp_2651_;
}
}
}
v___jp_2651_:
{
switch(lean_obj_tag(v___y_2652_))
{
case 7:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2653_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0));
v___x_2654_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(v_pre_2632_, v_post_2634_, v_usedLetOnly_2635_, v_skipConstInApp_2636_, v_skipInstances_2637_, v___x_2653_, v___y_2652_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
return v___x_2654_;
}
case 6:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2655_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0));
v___x_2656_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(v_pre_2632_, v_post_2634_, v_usedLetOnly_2635_, v_skipConstInApp_2636_, v_skipInstances_2637_, v___x_2655_, v___y_2652_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
return v___x_2656_;
}
case 8:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2657_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0));
v___x_2658_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(v_pre_2632_, v_post_2634_, v_usedLetOnly_2635_, v_skipConstInApp_2636_, v_skipInstances_2637_, v___x_2657_, v___y_2652_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
return v___x_2658_;
}
case 5:
{
lean_object* v_dummy_2659_; lean_object* v_nargs_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; 
v_dummy_2659_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1);
v_nargs_2660_ = l_Lean_Expr_getAppNumArgs(v___y_2652_);
lean_inc(v_nargs_2660_);
v___x_2661_ = lean_mk_array(v_nargs_2660_, v_dummy_2659_);
v___x_2662_ = lean_unsigned_to_nat(1u);
v___x_2663_ = lean_nat_sub(v_nargs_2660_, v___x_2662_);
lean_dec(v_nargs_2660_);
v___x_2664_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(v_skipInstances_2637_, v_pre_2632_, v_post_2634_, v_usedLetOnly_2635_, v_skipConstInApp_2636_, v___y_2652_, v___x_2661_, v___x_2663_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
return v___x_2664_;
}
case 10:
{
lean_object* v_data_2665_; lean_object* v_expr_2666_; lean_object* v___x_2667_; 
v_data_2665_ = lean_ctor_get(v___y_2652_, 0);
v_expr_2666_ = lean_ctor_get(v___y_2652_, 1);
lean_inc_ref(v_expr_2666_);
lean_inc_ref(v_post_2634_);
lean_inc_ref(v_pre_2632_);
v___x_2667_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2632_, v_post_2634_, v_usedLetOnly_2635_, v_skipConstInApp_2636_, v_skipInstances_2637_, v_expr_2666_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_object* v_a_2668_; size_t v___x_2669_; size_t v___x_2670_; uint8_t v___x_2671_; 
v_a_2668_ = lean_ctor_get(v___x_2667_, 0);
lean_inc(v_a_2668_);
lean_dec_ref(v___x_2667_);
v___x_2669_ = lean_ptr_addr(v_expr_2666_);
v___x_2670_ = lean_ptr_addr(v_a_2668_);
v___x_2671_ = lean_usize_dec_eq(v___x_2669_, v___x_2670_);
if (v___x_2671_ == 0)
{
lean_object* v___x_2672_; lean_object* v___x_2673_; 
lean_inc(v_data_2665_);
lean_dec_ref(v___y_2652_);
v___x_2672_ = l_Lean_Expr_mdata___override(v_data_2665_, v_a_2668_);
v___x_2673_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2632_, v_post_2634_, v_usedLetOnly_2635_, v_skipConstInApp_2636_, v_skipInstances_2637_, v___x_2672_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
return v___x_2673_;
}
else
{
lean_object* v___x_2674_; 
lean_dec(v_a_2668_);
v___x_2674_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2632_, v_post_2634_, v_usedLetOnly_2635_, v_skipConstInApp_2636_, v_skipInstances_2637_, v___y_2652_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
return v___x_2674_;
}
}
else
{
lean_dec_ref(v___y_2652_);
lean_dec_ref(v_post_2634_);
lean_dec_ref(v_pre_2632_);
return v___x_2667_;
}
}
case 11:
{
lean_object* v_typeName_2675_; lean_object* v_idx_2676_; lean_object* v_struct_2677_; lean_object* v___x_2678_; 
v_typeName_2675_ = lean_ctor_get(v___y_2652_, 0);
v_idx_2676_ = lean_ctor_get(v___y_2652_, 1);
v_struct_2677_ = lean_ctor_get(v___y_2652_, 2);
lean_inc_ref(v_struct_2677_);
lean_inc_ref(v_post_2634_);
lean_inc_ref(v_pre_2632_);
v___x_2678_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2632_, v_post_2634_, v_usedLetOnly_2635_, v_skipConstInApp_2636_, v_skipInstances_2637_, v_struct_2677_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v_a_2679_; size_t v___x_2680_; size_t v___x_2681_; uint8_t v___x_2682_; 
v_a_2679_ = lean_ctor_get(v___x_2678_, 0);
lean_inc(v_a_2679_);
lean_dec_ref(v___x_2678_);
v___x_2680_ = lean_ptr_addr(v_struct_2677_);
v___x_2681_ = lean_ptr_addr(v_a_2679_);
v___x_2682_ = lean_usize_dec_eq(v___x_2680_, v___x_2681_);
if (v___x_2682_ == 0)
{
lean_object* v___x_2683_; lean_object* v___x_2684_; 
lean_inc(v_idx_2676_);
lean_inc(v_typeName_2675_);
lean_dec_ref(v___y_2652_);
v___x_2683_ = l_Lean_Expr_proj___override(v_typeName_2675_, v_idx_2676_, v_a_2679_);
v___x_2684_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2632_, v_post_2634_, v_usedLetOnly_2635_, v_skipConstInApp_2636_, v_skipInstances_2637_, v___x_2683_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
return v___x_2684_;
}
else
{
lean_object* v___x_2685_; 
lean_dec(v_a_2679_);
v___x_2685_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2632_, v_post_2634_, v_usedLetOnly_2635_, v_skipConstInApp_2636_, v_skipInstances_2637_, v___y_2652_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
return v___x_2685_;
}
}
else
{
lean_dec_ref(v___y_2652_);
lean_dec_ref(v_post_2634_);
lean_dec_ref(v_pre_2632_);
return v___x_2678_;
}
}
default: 
{
lean_object* v___x_2686_; 
v___x_2686_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2632_, v_post_2634_, v_usedLetOnly_2635_, v_skipConstInApp_2636_, v_skipInstances_2637_, v___y_2652_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
return v___x_2686_;
}
}
}
}
}
else
{
lean_object* v_a_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2703_; 
lean_dec_ref(v_post_2634_);
lean_dec_ref(v_e_2633_);
lean_dec_ref(v_pre_2632_);
v_a_2696_ = lean_ctor_get(v___x_2646_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2646_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2698_ = v___x_2646_;
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_a_2696_);
lean_dec(v___x_2646_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2701_; 
if (v_isShared_2699_ == 0)
{
v___x_2701_ = v___x_2698_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_a_2696_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
}
else
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2711_; 
lean_dec_ref(v_post_2634_);
lean_dec_ref(v_e_2633_);
lean_dec_ref(v_pre_2632_);
v_a_2704_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2706_ = v___x_2645_;
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2645_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2709_; 
if (v_isShared_2707_ == 0)
{
v___x_2709_ = v___x_2706_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_a_2704_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___boxed(lean_object* v___x_2712_, lean_object* v_pre_2713_, lean_object* v_e_2714_, lean_object* v_post_2715_, lean_object* v_usedLetOnly_2716_, lean_object* v_skipConstInApp_2717_, lean_object* v_skipInstances_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_){
_start:
{
uint8_t v_usedLetOnly_boxed_2726_; uint8_t v_skipConstInApp_boxed_2727_; uint8_t v_skipInstances_boxed_2728_; lean_object* v_res_2729_; 
v_usedLetOnly_boxed_2726_ = lean_unbox(v_usedLetOnly_2716_);
v_skipConstInApp_boxed_2727_ = lean_unbox(v_skipConstInApp_2717_);
v_skipInstances_boxed_2728_ = lean_unbox(v_skipInstances_2718_);
v_res_2729_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1(v___x_2712_, v_pre_2713_, v_e_2714_, v_post_2715_, v_usedLetOnly_boxed_2726_, v_skipConstInApp_boxed_2727_, v_skipInstances_boxed_2728_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
lean_dec(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec(v___y_2719_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(lean_object* v_pre_2730_, lean_object* v_post_2731_, uint8_t v_usedLetOnly_2732_, uint8_t v_skipConstInApp_2733_, uint8_t v_skipInstances_2734_, lean_object* v_e_2735_, lean_object* v_a_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_){
_start:
{
lean_object* v___x_2743_; lean_object* v___x_2744_; 
lean_inc(v_a_2736_);
v___x_2743_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2743_, 0, lean_box(0));
lean_closure_set(v___x_2743_, 1, lean_box(0));
lean_closure_set(v___x_2743_, 2, v_a_2736_);
v___x_2744_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(lean_box(0), v___x_2743_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_);
if (lean_obj_tag(v___x_2744_) == 0)
{
lean_object* v_a_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2779_; 
v_a_2745_ = lean_ctor_get(v___x_2744_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2747_ = v___x_2744_;
v_isShared_2748_ = v_isSharedCheck_2779_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_a_2745_);
lean_dec(v___x_2744_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2779_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v___x_2749_; 
v___x_2749_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(v_a_2745_, v_e_2735_);
lean_dec(v_a_2745_);
if (lean_obj_tag(v___x_2749_) == 0)
{
lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___f_2754_; lean_object* v___x_2755_; 
lean_del_object(v___x_2747_);
v___x_2750_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___closed__0));
v___x_2751_ = lean_box(v_usedLetOnly_2732_);
v___x_2752_ = lean_box(v_skipConstInApp_2733_);
v___x_2753_ = lean_box(v_skipInstances_2734_);
lean_inc_ref(v_e_2735_);
v___f_2754_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___boxed), 14, 7);
lean_closure_set(v___f_2754_, 0, v___x_2750_);
lean_closure_set(v___f_2754_, 1, v_pre_2730_);
lean_closure_set(v___f_2754_, 2, v_e_2735_);
lean_closure_set(v___f_2754_, 3, v_post_2731_);
lean_closure_set(v___f_2754_, 4, v___x_2751_);
lean_closure_set(v___f_2754_, 5, v___x_2752_);
lean_closure_set(v___f_2754_, 6, v___x_2753_);
v___x_2755_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v___f_2754_, v_a_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_);
if (lean_obj_tag(v___x_2755_) == 0)
{
lean_object* v_a_2756_; lean_object* v___f_2757_; lean_object* v___x_2758_; 
v_a_2756_ = lean_ctor_get(v___x_2755_, 0);
lean_inc_n(v_a_2756_, 2);
lean_dec_ref(v___x_2755_);
lean_inc(v_a_2736_);
v___f_2757_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2757_, 0, v_a_2736_);
lean_closure_set(v___f_2757_, 1, v_e_2735_);
lean_closure_set(v___f_2757_, 2, v_a_2756_);
v___x_2758_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(lean_box(0), v___f_2757_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_);
if (lean_obj_tag(v___x_2758_) == 0)
{
lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2765_; 
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2758_);
if (v_isSharedCheck_2765_ == 0)
{
lean_object* v_unused_2766_; 
v_unused_2766_ = lean_ctor_get(v___x_2758_, 0);
lean_dec(v_unused_2766_);
v___x_2760_ = v___x_2758_;
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
else
{
lean_dec(v___x_2758_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2763_; 
if (v_isShared_2761_ == 0)
{
lean_ctor_set(v___x_2760_, 0, v_a_2756_);
v___x_2763_ = v___x_2760_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_a_2756_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
else
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2774_; 
lean_dec(v_a_2756_);
v_a_2767_ = lean_ctor_get(v___x_2758_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2758_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2769_ = v___x_2758_;
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v___x_2758_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2772_; 
if (v_isShared_2770_ == 0)
{
v___x_2772_ = v___x_2769_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_a_2767_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
}
}
else
{
lean_dec_ref(v_e_2735_);
return v___x_2755_;
}
}
else
{
lean_object* v_val_2775_; lean_object* v___x_2777_; 
lean_dec_ref(v_e_2735_);
lean_dec_ref(v_post_2731_);
lean_dec_ref(v_pre_2730_);
v_val_2775_ = lean_ctor_get(v___x_2749_, 0);
lean_inc(v_val_2775_);
lean_dec_ref(v___x_2749_);
if (v_isShared_2748_ == 0)
{
lean_ctor_set(v___x_2747_, 0, v_val_2775_);
v___x_2777_ = v___x_2747_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_val_2775_);
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
lean_dec_ref(v_e_2735_);
lean_dec_ref(v_post_2731_);
lean_dec_ref(v_pre_2730_);
v_a_2780_ = lean_ctor_get(v___x_2744_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2782_ = v___x_2744_;
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_a_2780_);
lean_dec(v___x_2744_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0___boxed(lean_object* v_fvars_2788_, lean_object* v_pre_2789_, lean_object* v_post_2790_, lean_object* v_usedLetOnly_2791_, lean_object* v_skipConstInApp_2792_, lean_object* v_skipInstances_2793_, lean_object* v_body_2794_, lean_object* v_x_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
uint8_t v_usedLetOnly_boxed_2803_; uint8_t v_skipConstInApp_boxed_2804_; uint8_t v_skipInstances_boxed_2805_; lean_object* v_res_2806_; 
v_usedLetOnly_boxed_2803_ = lean_unbox(v_usedLetOnly_2791_);
v_skipConstInApp_boxed_2804_ = lean_unbox(v_skipConstInApp_2792_);
v_skipInstances_boxed_2805_ = lean_unbox(v_skipInstances_2793_);
v_res_2806_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0(v_fvars_2788_, v_pre_2789_, v_post_2790_, v_usedLetOnly_boxed_2803_, v_skipConstInApp_boxed_2804_, v_skipInstances_boxed_2805_, v_body_2794_, v_x_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
lean_dec(v___y_2797_);
lean_dec(v___y_2796_);
return v_res_2806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(lean_object* v_pre_2807_, lean_object* v_post_2808_, uint8_t v_usedLetOnly_2809_, uint8_t v_skipConstInApp_2810_, uint8_t v_skipInstances_2811_, lean_object* v_fvars_2812_, lean_object* v_e_2813_, lean_object* v_a_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_){
_start:
{
if (lean_obj_tag(v_e_2813_) == 7)
{
lean_object* v_binderName_2821_; lean_object* v_binderType_2822_; lean_object* v_body_2823_; uint8_t v_binderInfo_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v_binderName_2821_ = lean_ctor_get(v_e_2813_, 0);
lean_inc(v_binderName_2821_);
v_binderType_2822_ = lean_ctor_get(v_e_2813_, 1);
lean_inc_ref(v_binderType_2822_);
v_body_2823_ = lean_ctor_get(v_e_2813_, 2);
lean_inc_ref(v_body_2823_);
v_binderInfo_2824_ = lean_ctor_get_uint8(v_e_2813_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_2813_);
v___x_2825_ = lean_expr_instantiate_rev(v_binderType_2822_, v_fvars_2812_);
lean_dec_ref(v_binderType_2822_);
lean_inc_ref(v_post_2808_);
lean_inc_ref(v_pre_2807_);
v___x_2826_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2807_, v_post_2808_, v_usedLetOnly_2809_, v_skipConstInApp_2810_, v_skipInstances_2811_, v___x_2825_, v_a_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v_a_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___f_2831_; uint8_t v___x_2832_; lean_object* v___x_2833_; 
v_a_2827_ = lean_ctor_get(v___x_2826_, 0);
lean_inc(v_a_2827_);
lean_dec_ref(v___x_2826_);
v___x_2828_ = lean_box(v_usedLetOnly_2809_);
v___x_2829_ = lean_box(v_skipConstInApp_2810_);
v___x_2830_ = lean_box(v_skipInstances_2811_);
v___f_2831_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0___boxed), 15, 7);
lean_closure_set(v___f_2831_, 0, v_fvars_2812_);
lean_closure_set(v___f_2831_, 1, v_pre_2807_);
lean_closure_set(v___f_2831_, 2, v_post_2808_);
lean_closure_set(v___f_2831_, 3, v___x_2828_);
lean_closure_set(v___f_2831_, 4, v___x_2829_);
lean_closure_set(v___f_2831_, 5, v___x_2830_);
lean_closure_set(v___f_2831_, 6, v_body_2823_);
v___x_2832_ = 0;
v___x_2833_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_2821_, v_binderInfo_2824_, v_a_2827_, v___f_2831_, v___x_2832_, v_a_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
return v___x_2833_;
}
else
{
lean_dec_ref(v_body_2823_);
lean_dec(v_binderName_2821_);
lean_dec_ref(v_fvars_2812_);
lean_dec_ref(v_post_2808_);
lean_dec_ref(v_pre_2807_);
return v___x_2826_;
}
}
else
{
lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2834_ = lean_expr_instantiate_rev(v_e_2813_, v_fvars_2812_);
lean_dec_ref(v_e_2813_);
lean_inc_ref(v_post_2808_);
lean_inc_ref(v_pre_2807_);
v___x_2835_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2807_, v_post_2808_, v_usedLetOnly_2809_, v_skipConstInApp_2810_, v_skipInstances_2811_, v___x_2834_, v_a_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
if (lean_obj_tag(v___x_2835_) == 0)
{
lean_object* v_a_2836_; uint8_t v___x_2837_; uint8_t v___x_2838_; uint8_t v___x_2839_; lean_object* v___x_2840_; 
v_a_2836_ = lean_ctor_get(v___x_2835_, 0);
lean_inc(v_a_2836_);
lean_dec_ref(v___x_2835_);
v___x_2837_ = 0;
v___x_2838_ = 1;
v___x_2839_ = 1;
v___x_2840_ = l_Lean_Meta_mkForallFVars(v_fvars_2812_, v_a_2836_, v___x_2837_, v_usedLetOnly_2809_, v___x_2838_, v___x_2839_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
lean_dec_ref(v_fvars_2812_);
if (lean_obj_tag(v___x_2840_) == 0)
{
lean_object* v_a_2841_; lean_object* v___x_2842_; 
v_a_2841_ = lean_ctor_get(v___x_2840_, 0);
lean_inc(v_a_2841_);
lean_dec_ref(v___x_2840_);
v___x_2842_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2807_, v_post_2808_, v_usedLetOnly_2809_, v_skipConstInApp_2810_, v_skipInstances_2811_, v_a_2841_, v_a_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
return v___x_2842_;
}
else
{
lean_dec_ref(v_post_2808_);
lean_dec_ref(v_pre_2807_);
return v___x_2840_;
}
}
else
{
lean_dec_ref(v_fvars_2812_);
lean_dec_ref(v_post_2808_);
lean_dec_ref(v_pre_2807_);
return v___x_2835_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0(lean_object* v_fvars_2843_, lean_object* v_pre_2844_, lean_object* v_post_2845_, uint8_t v_usedLetOnly_2846_, uint8_t v_skipConstInApp_2847_, uint8_t v_skipInstances_2848_, lean_object* v_body_2849_, lean_object* v_x_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_){
_start:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; 
v___x_2858_ = lean_array_push(v_fvars_2843_, v_x_2850_);
v___x_2859_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(v_pre_2844_, v_post_2845_, v_usedLetOnly_2846_, v_skipConstInApp_2847_, v_skipInstances_2848_, v___x_2858_, v_body_2849_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_);
return v___x_2859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_2860_, lean_object* v_post_2861_, lean_object* v_usedLetOnly_2862_, lean_object* v_skipConstInApp_2863_, lean_object* v_skipInstances_2864_, lean_object* v_e_2865_, lean_object* v_a_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_){
_start:
{
uint8_t v_usedLetOnly_boxed_2873_; uint8_t v_skipConstInApp_boxed_2874_; uint8_t v_skipInstances_boxed_2875_; lean_object* v_res_2876_; 
v_usedLetOnly_boxed_2873_ = lean_unbox(v_usedLetOnly_2862_);
v_skipConstInApp_boxed_2874_ = lean_unbox(v_skipConstInApp_2863_);
v_skipInstances_boxed_2875_ = lean_unbox(v_skipInstances_2864_);
v_res_2876_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2860_, v_post_2861_, v_usedLetOnly_boxed_2873_, v_skipConstInApp_boxed_2874_, v_skipInstances_boxed_2875_, v_e_2865_, v_a_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec(v___y_2867_);
lean_dec(v_a_2866_);
return v_res_2876_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_2877_, lean_object* v_post_2878_, lean_object* v_usedLetOnly_2879_, lean_object* v_skipConstInApp_2880_, lean_object* v_skipInstances_2881_, lean_object* v_sz_2882_, lean_object* v_i_2883_, lean_object* v_bs_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
uint8_t v_usedLetOnly_boxed_2892_; uint8_t v_skipConstInApp_boxed_2893_; uint8_t v_skipInstances_boxed_2894_; size_t v_sz_boxed_2895_; size_t v_i_boxed_2896_; lean_object* v_res_2897_; 
v_usedLetOnly_boxed_2892_ = lean_unbox(v_usedLetOnly_2879_);
v_skipConstInApp_boxed_2893_ = lean_unbox(v_skipConstInApp_2880_);
v_skipInstances_boxed_2894_ = lean_unbox(v_skipInstances_2881_);
v_sz_boxed_2895_ = lean_unbox_usize(v_sz_2882_);
lean_dec(v_sz_2882_);
v_i_boxed_2896_ = lean_unbox_usize(v_i_2883_);
lean_dec(v_i_2883_);
v_res_2897_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(v_pre_2877_, v_post_2878_, v_usedLetOnly_boxed_2892_, v_skipConstInApp_boxed_2893_, v_skipInstances_boxed_2894_, v_sz_boxed_2895_, v_i_boxed_2896_, v_bs_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2885_);
return v_res_2897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___boxed(lean_object* v_pre_2898_, lean_object* v_post_2899_, lean_object* v_usedLetOnly_2900_, lean_object* v_skipConstInApp_2901_, lean_object* v_skipInstances_2902_, lean_object* v_e_2903_, lean_object* v_a_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_){
_start:
{
uint8_t v_usedLetOnly_boxed_2911_; uint8_t v_skipConstInApp_boxed_2912_; uint8_t v_skipInstances_boxed_2913_; lean_object* v_res_2914_; 
v_usedLetOnly_boxed_2911_ = lean_unbox(v_usedLetOnly_2900_);
v_skipConstInApp_boxed_2912_ = lean_unbox(v_skipConstInApp_2901_);
v_skipInstances_boxed_2913_ = lean_unbox(v_skipInstances_2902_);
v_res_2914_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2898_, v_post_2899_, v_usedLetOnly_boxed_2911_, v_skipConstInApp_boxed_2912_, v_skipInstances_boxed_2913_, v_e_2903_, v_a_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_);
lean_dec(v___y_2909_);
lean_dec_ref(v___y_2908_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v___y_2905_);
lean_dec(v_a_2904_);
return v_res_2914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___boxed(lean_object* v_pre_2915_, lean_object* v_post_2916_, lean_object* v_usedLetOnly_2917_, lean_object* v_skipConstInApp_2918_, lean_object* v_skipInstances_2919_, lean_object* v_fvars_2920_, lean_object* v_e_2921_, lean_object* v_a_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_){
_start:
{
uint8_t v_usedLetOnly_boxed_2929_; uint8_t v_skipConstInApp_boxed_2930_; uint8_t v_skipInstances_boxed_2931_; lean_object* v_res_2932_; 
v_usedLetOnly_boxed_2929_ = lean_unbox(v_usedLetOnly_2917_);
v_skipConstInApp_boxed_2930_ = lean_unbox(v_skipConstInApp_2918_);
v_skipInstances_boxed_2931_ = lean_unbox(v_skipInstances_2919_);
v_res_2932_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(v_pre_2915_, v_post_2916_, v_usedLetOnly_boxed_2929_, v_skipConstInApp_boxed_2930_, v_skipInstances_boxed_2931_, v_fvars_2920_, v_e_2921_, v_a_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_);
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2926_);
lean_dec(v___y_2925_);
lean_dec_ref(v___y_2924_);
lean_dec(v___y_2923_);
lean_dec(v_a_2922_);
return v_res_2932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___boxed(lean_object* v_pre_2933_, lean_object* v_post_2934_, lean_object* v_usedLetOnly_2935_, lean_object* v_skipConstInApp_2936_, lean_object* v_skipInstances_2937_, lean_object* v_fvars_2938_, lean_object* v_e_2939_, lean_object* v_a_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
uint8_t v_usedLetOnly_boxed_2947_; uint8_t v_skipConstInApp_boxed_2948_; uint8_t v_skipInstances_boxed_2949_; lean_object* v_res_2950_; 
v_usedLetOnly_boxed_2947_ = lean_unbox(v_usedLetOnly_2935_);
v_skipConstInApp_boxed_2948_ = lean_unbox(v_skipConstInApp_2936_);
v_skipInstances_boxed_2949_ = lean_unbox(v_skipInstances_2937_);
v_res_2950_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(v_pre_2933_, v_post_2934_, v_usedLetOnly_boxed_2947_, v_skipConstInApp_boxed_2948_, v_skipInstances_boxed_2949_, v_fvars_2938_, v_e_2939_, v_a_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec(v___y_2943_);
lean_dec_ref(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec(v_a_2940_);
return v_res_2950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___boxed(lean_object* v_pre_2951_, lean_object* v_post_2952_, lean_object* v_usedLetOnly_2953_, lean_object* v_skipConstInApp_2954_, lean_object* v_skipInstances_2955_, lean_object* v_fvars_2956_, lean_object* v_e_2957_, lean_object* v_a_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_){
_start:
{
uint8_t v_usedLetOnly_boxed_2965_; uint8_t v_skipConstInApp_boxed_2966_; uint8_t v_skipInstances_boxed_2967_; lean_object* v_res_2968_; 
v_usedLetOnly_boxed_2965_ = lean_unbox(v_usedLetOnly_2953_);
v_skipConstInApp_boxed_2966_ = lean_unbox(v_skipConstInApp_2954_);
v_skipInstances_boxed_2967_ = lean_unbox(v_skipInstances_2955_);
v_res_2968_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(v_pre_2951_, v_post_2952_, v_usedLetOnly_boxed_2965_, v_skipConstInApp_boxed_2966_, v_skipInstances_boxed_2967_, v_fvars_2956_, v_e_2957_, v_a_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
lean_dec(v___y_2961_);
lean_dec_ref(v___y_2960_);
lean_dec(v___y_2959_);
lean_dec(v_a_2958_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_upperBound_2969_, lean_object* v___x_2970_, lean_object* v_pre_2971_, lean_object* v_post_2972_, lean_object* v_usedLetOnly_2973_, lean_object* v_skipConstInApp_2974_, lean_object* v_skipInstances_2975_, lean_object* v_a_2976_, lean_object* v_b_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_){
_start:
{
uint8_t v_usedLetOnly_boxed_2985_; uint8_t v_skipConstInApp_boxed_2986_; uint8_t v_skipInstances_boxed_2987_; lean_object* v_res_2988_; 
v_usedLetOnly_boxed_2985_ = lean_unbox(v_usedLetOnly_2973_);
v_skipConstInApp_boxed_2986_ = lean_unbox(v_skipConstInApp_2974_);
v_skipInstances_boxed_2987_ = lean_unbox(v_skipInstances_2975_);
v_res_2988_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(v_upperBound_2969_, v___x_2970_, v_pre_2971_, v_post_2972_, v_usedLetOnly_boxed_2985_, v_skipConstInApp_boxed_2986_, v_skipInstances_boxed_2987_, v_a_2976_, v_b_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_);
lean_dec(v___y_2983_);
lean_dec_ref(v___y_2982_);
lean_dec(v___y_2981_);
lean_dec_ref(v___y_2980_);
lean_dec(v___y_2979_);
lean_dec(v___y_2978_);
lean_dec_ref(v___x_2970_);
lean_dec(v_upperBound_2969_);
return v_res_2988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8___boxed(lean_object* v_skipInstances_2989_, lean_object* v_pre_2990_, lean_object* v_post_2991_, lean_object* v_usedLetOnly_2992_, lean_object* v_skipConstInApp_2993_, lean_object* v_x_2994_, lean_object* v_x_2995_, lean_object* v_x_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_){
_start:
{
uint8_t v_skipInstances_boxed_3004_; uint8_t v_usedLetOnly_boxed_3005_; uint8_t v_skipConstInApp_boxed_3006_; lean_object* v_res_3007_; 
v_skipInstances_boxed_3004_ = lean_unbox(v_skipInstances_2989_);
v_usedLetOnly_boxed_3005_ = lean_unbox(v_usedLetOnly_2992_);
v_skipConstInApp_boxed_3006_ = lean_unbox(v_skipConstInApp_2993_);
v_res_3007_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(v_skipInstances_boxed_3004_, v_pre_2990_, v_post_2991_, v_usedLetOnly_boxed_3005_, v_skipConstInApp_boxed_3006_, v_x_2994_, v_x_2995_, v_x_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_);
lean_dec(v___y_3002_);
lean_dec_ref(v___y_3001_);
lean_dec(v___y_3000_);
lean_dec_ref(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec(v___y_2997_);
return v_res_3007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_object* v_00_u03b1_3008_, lean_object* v_x_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_){
_start:
{
lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3016_ = lean_apply_1(v_x_3009_, lean_box(0));
v___x_3017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3017_, 0, v___x_3016_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0___boxed(lean_object* v_00_u03b1_3018_, lean_object* v_x_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_){
_start:
{
lean_object* v_res_3026_; 
v_res_3026_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(v_00_u03b1_3018_, v_x_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_);
lean_dec(v___y_3024_);
lean_dec_ref(v___y_3023_);
lean_dec(v___y_3022_);
lean_dec_ref(v___y_3021_);
lean_dec(v___y_3020_);
return v_res_3026_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3027_ = lean_box(0);
v___x_3028_ = lean_unsigned_to_nat(16u);
v___x_3029_ = lean_mk_array(v___x_3028_, v___x_3027_);
return v___x_3029_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3030_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0);
v___x_3031_ = lean_unsigned_to_nat(0u);
v___x_3032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3031_);
lean_ctor_set(v___x_3032_, 1, v___x_3030_);
return v___x_3032_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2(void){
_start:
{
lean_object* v___x_3033_; lean_object* v___x_3034_; 
v___x_3033_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1);
v___x_3034_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3034_, 0, lean_box(0));
lean_closure_set(v___x_3034_, 1, lean_box(0));
lean_closure_set(v___x_3034_, 2, v___x_3033_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(lean_object* v_input_3035_, lean_object* v_pre_3036_, lean_object* v_post_3037_, uint8_t v_usedLetOnly_3038_, uint8_t v_skipConstInApp_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_){
_start:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v_a_3048_; uint8_t v___x_3049_; lean_object* v___x_3050_; 
v___x_3046_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2);
v___x_3047_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_box(0), v___x_3046_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_);
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
lean_inc(v_a_3048_);
lean_dec_ref(v___x_3047_);
v___x_3049_ = 0;
v___x_3050_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_3036_, v_post_3037_, v_usedLetOnly_3038_, v_skipConstInApp_3039_, v___x_3049_, v_input_3035_, v_a_3048_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_);
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_object* v_a_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3060_; 
v_a_3051_ = lean_ctor_get(v___x_3050_, 0);
lean_inc(v_a_3051_);
lean_dec_ref(v___x_3050_);
v___x_3052_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3052_, 0, lean_box(0));
lean_closure_set(v___x_3052_, 1, lean_box(0));
lean_closure_set(v___x_3052_, 2, v_a_3048_);
v___x_3053_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_box(0), v___x_3052_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3053_);
if (v_isSharedCheck_3060_ == 0)
{
lean_object* v_unused_3061_; 
v_unused_3061_ = lean_ctor_get(v___x_3053_, 0);
lean_dec(v_unused_3061_);
v___x_3055_ = v___x_3053_;
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
else
{
lean_dec(v___x_3053_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3058_; 
if (v_isShared_3056_ == 0)
{
lean_ctor_set(v___x_3055_, 0, v_a_3051_);
v___x_3058_ = v___x_3055_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_a_3051_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
}
else
{
lean_dec(v_a_3048_);
return v___x_3050_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___boxed(lean_object* v_input_3062_, lean_object* v_pre_3063_, lean_object* v_post_3064_, lean_object* v_usedLetOnly_3065_, lean_object* v_skipConstInApp_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_){
_start:
{
uint8_t v_usedLetOnly_boxed_3073_; uint8_t v_skipConstInApp_boxed_3074_; lean_object* v_res_3075_; 
v_usedLetOnly_boxed_3073_ = lean_unbox(v_usedLetOnly_3065_);
v_skipConstInApp_boxed_3074_ = lean_unbox(v_skipConstInApp_3066_);
v_res_3075_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(v_input_3062_, v_pre_3063_, v_post_3064_, v_usedLetOnly_boxed_3073_, v_skipConstInApp_boxed_3074_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_);
lean_dec(v___y_3071_);
lean_dec_ref(v___y_3070_);
lean_dec(v___y_3069_);
lean_dec_ref(v___y_3068_);
lean_dec(v___y_3067_);
return v_res_3075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore(lean_object* v_e_3077_, uint8_t v_elimTrivial_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_){
_start:
{
lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v_pre_3087_; lean_object* v___f_3088_; uint8_t v___x_3089_; lean_object* v___x_3090_; 
v___x_3084_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3);
v___x_3085_ = lean_st_mk_ref(v___x_3084_);
v___x_3086_ = lean_box(v_elimTrivial_3078_);
v_pre_3087_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___boxed), 8, 1);
lean_closure_set(v_pre_3087_, 0, v___x_3086_);
v___f_3088_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___closed__0));
v___x_3089_ = 0;
v___x_3090_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(v_e_3077_, v_pre_3087_, v___f_3088_, v___x_3089_, v___x_3089_, v___x_3085_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_);
if (lean_obj_tag(v___x_3090_) == 0)
{
lean_object* v_a_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3099_; 
v_a_3091_ = lean_ctor_get(v___x_3090_, 0);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3090_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3093_ = v___x_3090_;
v_isShared_3094_ = v_isSharedCheck_3099_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_a_3091_);
lean_dec(v___x_3090_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3099_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3095_; lean_object* v___x_3097_; 
v___x_3095_ = lean_st_ref_get(v___x_3085_);
lean_dec(v___x_3085_);
lean_dec(v___x_3095_);
if (v_isShared_3094_ == 0)
{
v___x_3097_ = v___x_3093_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_a_3091_);
v___x_3097_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
return v___x_3097_;
}
}
}
else
{
lean_dec(v___x_3085_);
return v___x_3090_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___boxed(lean_object* v_e_3100_, lean_object* v_elimTrivial_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_){
_start:
{
uint8_t v_elimTrivial_boxed_3107_; lean_object* v_res_3108_; 
v_elimTrivial_boxed_3107_ = lean_unbox(v_elimTrivial_3101_);
v_res_3108_ = l_Lean_Elab_Tactic_Do_elimLetsCore(v_e_3100_, v_elimTrivial_boxed_3107_, v_a_3102_, v_a_3103_, v_a_3104_, v_a_3105_);
lean_dec(v_a_3105_);
lean_dec_ref(v_a_3104_);
lean_dec(v_a_3103_);
lean_dec_ref(v_a_3102_);
return v_res_3108_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(lean_object* v_upperBound_3109_, lean_object* v___x_3110_, lean_object* v_pre_3111_, lean_object* v_post_3112_, uint8_t v_usedLetOnly_3113_, uint8_t v_skipConstInApp_3114_, uint8_t v_skipInstances_3115_, lean_object* v___x_3116_, lean_object* v_inst_3117_, lean_object* v_R_3118_, lean_object* v_a_3119_, lean_object* v_b_3120_, lean_object* v_c_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_){
_start:
{
lean_object* v___x_3129_; 
v___x_3129_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(v_upperBound_3109_, v___x_3110_, v_pre_3111_, v_post_3112_, v_usedLetOnly_3113_, v_skipConstInApp_3114_, v_skipInstances_3115_, v_a_3119_, v_b_3120_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
return v___x_3129_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___boxed(lean_object** _args){
lean_object* v_upperBound_3130_ = _args[0];
lean_object* v___x_3131_ = _args[1];
lean_object* v_pre_3132_ = _args[2];
lean_object* v_post_3133_ = _args[3];
lean_object* v_usedLetOnly_3134_ = _args[4];
lean_object* v_skipConstInApp_3135_ = _args[5];
lean_object* v_skipInstances_3136_ = _args[6];
lean_object* v___x_3137_ = _args[7];
lean_object* v_inst_3138_ = _args[8];
lean_object* v_R_3139_ = _args[9];
lean_object* v_a_3140_ = _args[10];
lean_object* v_b_3141_ = _args[11];
lean_object* v_c_3142_ = _args[12];
lean_object* v___y_3143_ = _args[13];
lean_object* v___y_3144_ = _args[14];
lean_object* v___y_3145_ = _args[15];
lean_object* v___y_3146_ = _args[16];
lean_object* v___y_3147_ = _args[17];
lean_object* v___y_3148_ = _args[18];
lean_object* v___y_3149_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_3150_; uint8_t v_skipConstInApp_boxed_3151_; uint8_t v_skipInstances_boxed_3152_; lean_object* v_res_3153_; 
v_usedLetOnly_boxed_3150_ = lean_unbox(v_usedLetOnly_3134_);
v_skipConstInApp_boxed_3151_ = lean_unbox(v_skipConstInApp_3135_);
v_skipInstances_boxed_3152_ = lean_unbox(v_skipInstances_3136_);
v_res_3153_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(v_upperBound_3130_, v___x_3131_, v_pre_3132_, v_post_3133_, v_usedLetOnly_boxed_3150_, v_skipConstInApp_boxed_3151_, v_skipInstances_boxed_3152_, v___x_3137_, v_inst_3138_, v_R_3139_, v_a_3140_, v_b_3141_, v_c_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
lean_dec(v___y_3148_);
lean_dec_ref(v___y_3147_);
lean_dec(v___y_3146_);
lean_dec_ref(v___y_3145_);
lean_dec(v___y_3144_);
lean_dec(v___y_3143_);
lean_dec(v___x_3137_);
lean_dec_ref(v___x_3131_);
lean_dec(v_upperBound_3130_);
return v_res_3153_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_3154_, lean_object* v_m_3155_, lean_object* v_a_3156_){
_start:
{
lean_object* v___x_3157_; 
v___x_3157_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(v_m_3155_, v_a_3156_);
return v___x_3157_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b2_3158_, lean_object* v_m_3159_, lean_object* v_a_3160_){
_start:
{
lean_object* v_res_3161_; 
v_res_3161_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4(v_00_u03b2_3158_, v_m_3159_, v_a_3160_);
lean_dec_ref(v_a_3160_);
lean_dec_ref(v_m_3159_);
return v_res_3161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_3162_, lean_object* v_name_3163_, uint8_t v_bi_3164_, lean_object* v_type_3165_, lean_object* v_k_3166_, uint8_t v_kind_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_){
_start:
{
lean_object* v___x_3175_; 
v___x_3175_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_name_3163_, v_bi_3164_, v_type_3165_, v_k_3166_, v_kind_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
return v___x_3175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_3176_, lean_object* v_name_3177_, lean_object* v_bi_3178_, lean_object* v_type_3179_, lean_object* v_k_3180_, lean_object* v_kind_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_){
_start:
{
uint8_t v_bi_boxed_3189_; uint8_t v_kind_boxed_3190_; lean_object* v_res_3191_; 
v_bi_boxed_3189_ = lean_unbox(v_bi_3178_);
v_kind_boxed_3190_ = lean_unbox(v_kind_3181_);
v_res_3191_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_3176_, v_name_3177_, v_bi_boxed_3189_, v_type_3179_, v_k_3180_, v_kind_boxed_3190_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_dec(v___y_3183_);
lean_dec(v___y_3182_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10(lean_object* v_00_u03b1_3192_, lean_object* v_name_3193_, lean_object* v_type_3194_, lean_object* v_val_3195_, lean_object* v_k_3196_, uint8_t v_nondep_3197_, uint8_t v_kind_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_){
_start:
{
lean_object* v___x_3206_; 
v___x_3206_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_name_3193_, v_type_3194_, v_val_3195_, v_k_3196_, v_nondep_3197_, v_kind_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_);
return v___x_3206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___boxed(lean_object* v_00_u03b1_3207_, lean_object* v_name_3208_, lean_object* v_type_3209_, lean_object* v_val_3210_, lean_object* v_k_3211_, lean_object* v_nondep_3212_, lean_object* v_kind_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_){
_start:
{
uint8_t v_nondep_boxed_3221_; uint8_t v_kind_boxed_3222_; lean_object* v_res_3223_; 
v_nondep_boxed_3221_ = lean_unbox(v_nondep_3212_);
v_kind_boxed_3222_ = lean_unbox(v_kind_3213_);
v_res_3223_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10(v_00_u03b1_3207_, v_name_3208_, v_type_3209_, v_val_3210_, v_k_3211_, v_nondep_boxed_3221_, v_kind_boxed_3222_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
lean_dec(v___y_3219_);
lean_dec_ref(v___y_3218_);
lean_dec(v___y_3217_);
lean_dec_ref(v___y_3216_);
lean_dec(v___y_3215_);
lean_dec(v___y_3214_);
return v_res_3223_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13(lean_object* v_00_u03b1_3224_, lean_object* v_ref_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_){
_start:
{
lean_object* v___x_3231_; 
v___x_3231_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_3225_);
return v___x_3231_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___boxed(lean_object* v_00_u03b1_3232_, lean_object* v_ref_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_){
_start:
{
lean_object* v_res_3239_; 
v_res_3239_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13(v_00_u03b1_3232_, v_ref_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
lean_dec(v___y_3237_);
lean_dec_ref(v___y_3236_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
return v_res_3239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9(lean_object* v_00_u03b1_3240_, lean_object* v_x_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_){
_start:
{
lean_object* v___x_3249_; 
v___x_3249_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v_x_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
return v___x_3249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___boxed(lean_object* v_00_u03b1_3250_, lean_object* v_x_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_){
_start:
{
lean_object* v_res_3259_; 
v_res_3259_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9(v_00_u03b1_3250_, v_x_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_);
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3256_);
lean_dec(v___y_3255_);
lean_dec_ref(v___y_3254_);
lean_dec(v___y_3253_);
lean_dec(v___y_3252_);
return v_res_3259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10(lean_object* v_00_u03b2_3260_, lean_object* v_m_3261_, lean_object* v_a_3262_, lean_object* v_b_3263_){
_start:
{
lean_object* v___x_3264_; 
v___x_3264_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(v_m_3261_, v_a_3262_, v_b_3263_);
return v___x_3264_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5(lean_object* v_00_u03b2_3265_, lean_object* v_a_3266_, lean_object* v_x_3267_){
_start:
{
lean_object* v___x_3268_; 
v___x_3268_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(v_a_3266_, v_x_3267_);
return v___x_3268_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___boxed(lean_object* v_00_u03b2_3269_, lean_object* v_a_3270_, lean_object* v_x_3271_){
_start:
{
lean_object* v_res_3272_; 
v_res_3272_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5(v_00_u03b2_3269_, v_a_3270_, v_x_3271_);
lean_dec(v_x_3271_);
lean_dec_ref(v_a_3270_);
return v_res_3272_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15(lean_object* v_00_u03b2_3273_, lean_object* v_a_3274_, lean_object* v_x_3275_){
_start:
{
uint8_t v___x_3276_; 
v___x_3276_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_a_3274_, v_x_3275_);
return v___x_3276_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___boxed(lean_object* v_00_u03b2_3277_, lean_object* v_a_3278_, lean_object* v_x_3279_){
_start:
{
uint8_t v_res_3280_; lean_object* v_r_3281_; 
v_res_3280_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15(v_00_u03b2_3277_, v_a_3278_, v_x_3279_);
lean_dec(v_x_3279_);
lean_dec_ref(v_a_3278_);
v_r_3281_ = lean_box(v_res_3280_);
return v_r_3281_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16(lean_object* v_00_u03b2_3282_, lean_object* v_data_3283_){
_start:
{
lean_object* v___x_3284_; 
v___x_3284_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(v_data_3283_);
return v___x_3284_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17(lean_object* v_00_u03b2_3285_, lean_object* v_a_3286_, lean_object* v_b_3287_, lean_object* v_x_3288_){
_start:
{
lean_object* v___x_3289_; 
v___x_3289_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(v_a_3286_, v_b_3287_, v_x_3288_);
return v___x_3289_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17(lean_object* v_00_u03b2_3290_, lean_object* v_i_3291_, lean_object* v_source_3292_, lean_object* v_target_3293_){
_start:
{
lean_object* v___x_3294_; 
v___x_3294_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v_i_3291_, v_source_3292_, v_target_3293_);
return v___x_3294_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18(lean_object* v_00_u03b2_3295_, lean_object* v_x_3296_, lean_object* v_x_3297_){
_start:
{
lean_object* v___x_3298_; 
v___x_3298_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_x_3296_, v_x_3297_);
return v___x_3298_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(lean_object* v_mvarId_3299_, lean_object* v_x_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_){
_start:
{
lean_object* v___x_3306_; 
v___x_3306_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3299_, v_x_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_);
if (lean_obj_tag(v___x_3306_) == 0)
{
lean_object* v_a_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3314_; 
v_a_3307_ = lean_ctor_get(v___x_3306_, 0);
v_isSharedCheck_3314_ = !lean_is_exclusive(v___x_3306_);
if (v_isSharedCheck_3314_ == 0)
{
v___x_3309_ = v___x_3306_;
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_a_3307_);
lean_dec(v___x_3306_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3312_; 
if (v_isShared_3310_ == 0)
{
v___x_3312_ = v___x_3309_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v_a_3307_);
v___x_3312_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
return v___x_3312_;
}
}
}
else
{
lean_object* v_a_3315_; lean_object* v___x_3317_; uint8_t v_isShared_3318_; uint8_t v_isSharedCheck_3322_; 
v_a_3315_ = lean_ctor_get(v___x_3306_, 0);
v_isSharedCheck_3322_ = !lean_is_exclusive(v___x_3306_);
if (v_isSharedCheck_3322_ == 0)
{
v___x_3317_ = v___x_3306_;
v_isShared_3318_ = v_isSharedCheck_3322_;
goto v_resetjp_3316_;
}
else
{
lean_inc(v_a_3315_);
lean_dec(v___x_3306_);
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
v_reuseFailAlloc_3321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v_a_3315_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg___boxed(lean_object* v_mvarId_3323_, lean_object* v_x_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_){
_start:
{
lean_object* v_res_3330_; 
v_res_3330_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(v_mvarId_3323_, v_x_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
lean_dec(v___y_3328_);
lean_dec_ref(v___y_3327_);
lean_dec(v___y_3326_);
lean_dec_ref(v___y_3325_);
return v_res_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3(lean_object* v_00_u03b1_3331_, lean_object* v_mvarId_3332_, lean_object* v_x_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_){
_start:
{
lean_object* v___x_3339_; 
v___x_3339_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(v_mvarId_3332_, v_x_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
return v___x_3339_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___boxed(lean_object* v_00_u03b1_3340_, lean_object* v_mvarId_3341_, lean_object* v_x_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_){
_start:
{
lean_object* v_res_3348_; 
v_res_3348_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3(v_00_u03b1_3340_, v_mvarId_3341_, v_x_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
lean_dec(v___y_3346_);
lean_dec_ref(v___y_3345_);
lean_dec(v___y_3344_);
lean_dec_ref(v___y_3343_);
return v_res_3348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(uint8_t v_elimTrivial_3349_, lean_object* v_as_3350_, size_t v_sz_3351_, size_t v_i_3352_, lean_object* v_b_3353_){
_start:
{
uint8_t v___x_3355_; 
v___x_3355_ = lean_usize_dec_lt(v_i_3352_, v_sz_3351_);
if (v___x_3355_ == 0)
{
lean_object* v___x_3356_; 
v___x_3356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3356_, 0, v_b_3353_);
return v___x_3356_;
}
else
{
lean_object* v_snd_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3404_; 
v_snd_3357_ = lean_ctor_get(v_b_3353_, 1);
v_isSharedCheck_3404_ = !lean_is_exclusive(v_b_3353_);
if (v_isSharedCheck_3404_ == 0)
{
lean_object* v_unused_3405_; 
v_unused_3405_ = lean_ctor_get(v_b_3353_, 0);
lean_dec(v_unused_3405_);
v___x_3359_ = v_b_3353_;
v_isShared_3360_ = v_isSharedCheck_3404_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_snd_3357_);
lean_dec(v_b_3353_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3404_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v___x_3361_; lean_object* v_a_3363_; lean_object* v_a_3370_; 
v___x_3361_ = lean_box(0);
v_a_3370_ = lean_array_uget_borrowed(v_as_3350_, v_i_3352_);
if (lean_obj_tag(v_a_3370_) == 0)
{
v_a_3363_ = v_snd_3357_;
goto v___jp_3362_;
}
else
{
lean_object* v_val_3371_; lean_object* v_fst_3372_; lean_object* v_snd_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3403_; 
v_val_3371_ = lean_ctor_get(v_a_3370_, 0);
v_fst_3372_ = lean_ctor_get(v_snd_3357_, 0);
v_snd_3373_ = lean_ctor_get(v_snd_3357_, 1);
v_isSharedCheck_3403_ = !lean_is_exclusive(v_snd_3357_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3375_ = v_snd_3357_;
v_isShared_3376_ = v_isSharedCheck_3403_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_snd_3373_);
lean_inc(v_fst_3372_);
lean_dec(v_snd_3357_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3403_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
uint8_t v___x_3377_; lean_object* v___x_3378_; 
v___x_3377_ = 0;
v___x_3378_ = l_Lean_LocalDecl_value_x3f(v_val_3371_, v___x_3377_);
if (lean_obj_tag(v___x_3378_) == 1)
{
lean_object* v_val_3379_; lean_object* v___x_3380_; 
v_val_3379_ = lean_ctor_get(v___x_3378_, 0);
lean_inc(v_val_3379_);
lean_dec_ref(v___x_3378_);
v___x_3380_ = l_Lean_LocalDecl_type(v_val_3371_);
if (lean_obj_tag(v___x_3380_) == 10)
{
lean_object* v_data_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; uint8_t v___x_3385_; uint8_t v___x_3386_; 
v_data_3381_ = lean_ctor_get(v___x_3380_, 0);
lean_inc(v_data_3381_);
lean_dec_ref(v___x_3380_);
v___x_3382_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_3383_ = lean_unsigned_to_nat(2u);
v___x_3384_ = l_Lean_KVMap_getNat(v_data_3381_, v___x_3382_, v___x_3383_);
lean_dec(v_data_3381_);
v___x_3385_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3384_);
lean_dec(v___x_3384_);
v___x_3386_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3385_, v_val_3379_, v_elimTrivial_3349_);
if (v___x_3386_ == 0)
{
lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3392_; 
v___x_3387_ = l_Lean_LocalDecl_fvarId(v_val_3371_);
v___x_3388_ = l_Lean_mkFVar(v___x_3387_);
v___x_3389_ = lean_array_push(v_fst_3372_, v___x_3388_);
v___x_3390_ = lean_array_push(v_snd_3373_, v_val_3379_);
if (v_isShared_3376_ == 0)
{
lean_ctor_set(v___x_3375_, 1, v___x_3390_);
lean_ctor_set(v___x_3375_, 0, v___x_3389_);
v___x_3392_ = v___x_3375_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v___x_3389_);
lean_ctor_set(v_reuseFailAlloc_3393_, 1, v___x_3390_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
v_a_3363_ = v___x_3392_;
goto v___jp_3362_;
}
}
else
{
lean_object* v___x_3395_; 
lean_dec(v_val_3379_);
if (v_isShared_3376_ == 0)
{
v___x_3395_ = v___x_3375_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v_fst_3372_);
lean_ctor_set(v_reuseFailAlloc_3396_, 1, v_snd_3373_);
v___x_3395_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
v_a_3363_ = v___x_3395_;
goto v___jp_3362_;
}
}
}
else
{
lean_object* v___x_3398_; 
lean_dec_ref(v___x_3380_);
lean_dec(v_val_3379_);
if (v_isShared_3376_ == 0)
{
v___x_3398_ = v___x_3375_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v_fst_3372_);
lean_ctor_set(v_reuseFailAlloc_3399_, 1, v_snd_3373_);
v___x_3398_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
v_a_3363_ = v___x_3398_;
goto v___jp_3362_;
}
}
}
else
{
lean_object* v___x_3401_; 
lean_dec(v___x_3378_);
if (v_isShared_3376_ == 0)
{
v___x_3401_ = v___x_3375_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_fst_3372_);
lean_ctor_set(v_reuseFailAlloc_3402_, 1, v_snd_3373_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
v_a_3363_ = v___x_3401_;
goto v___jp_3362_;
}
}
}
}
v___jp_3362_:
{
lean_object* v___x_3365_; 
if (v_isShared_3360_ == 0)
{
lean_ctor_set(v___x_3359_, 1, v_a_3363_);
lean_ctor_set(v___x_3359_, 0, v___x_3361_);
v___x_3365_ = v___x_3359_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v___x_3361_);
lean_ctor_set(v_reuseFailAlloc_3369_, 1, v_a_3363_);
v___x_3365_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
size_t v___x_3366_; size_t v___x_3367_; 
v___x_3366_ = ((size_t)1ULL);
v___x_3367_ = lean_usize_add(v_i_3352_, v___x_3366_);
v_i_3352_ = v___x_3367_;
v_b_3353_ = v___x_3365_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_elimTrivial_3406_, lean_object* v_as_3407_, lean_object* v_sz_3408_, lean_object* v_i_3409_, lean_object* v_b_3410_, lean_object* v___y_3411_){
_start:
{
uint8_t v_elimTrivial_boxed_3412_; size_t v_sz_boxed_3413_; size_t v_i_boxed_3414_; lean_object* v_res_3415_; 
v_elimTrivial_boxed_3412_ = lean_unbox(v_elimTrivial_3406_);
v_sz_boxed_3413_ = lean_unbox_usize(v_sz_3408_);
lean_dec(v_sz_3408_);
v_i_boxed_3414_ = lean_unbox_usize(v_i_3409_);
lean_dec(v_i_3409_);
v_res_3415_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_boxed_3412_, v_as_3407_, v_sz_boxed_3413_, v_i_boxed_3414_, v_b_3410_);
lean_dec_ref(v_as_3407_);
return v_res_3415_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(uint8_t v_elimTrivial_3416_, lean_object* v_as_3417_, size_t v_sz_3418_, size_t v_i_3419_, lean_object* v_b_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_){
_start:
{
uint8_t v___x_3426_; 
v___x_3426_ = lean_usize_dec_lt(v_i_3419_, v_sz_3418_);
if (v___x_3426_ == 0)
{
lean_object* v___x_3427_; 
v___x_3427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3427_, 0, v_b_3420_);
return v___x_3427_;
}
else
{
lean_object* v_snd_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3475_; 
v_snd_3428_ = lean_ctor_get(v_b_3420_, 1);
v_isSharedCheck_3475_ = !lean_is_exclusive(v_b_3420_);
if (v_isSharedCheck_3475_ == 0)
{
lean_object* v_unused_3476_; 
v_unused_3476_ = lean_ctor_get(v_b_3420_, 0);
lean_dec(v_unused_3476_);
v___x_3430_ = v_b_3420_;
v_isShared_3431_ = v_isSharedCheck_3475_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_snd_3428_);
lean_dec(v_b_3420_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3475_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3432_; lean_object* v_a_3434_; lean_object* v_a_3441_; 
v___x_3432_ = lean_box(0);
v_a_3441_ = lean_array_uget_borrowed(v_as_3417_, v_i_3419_);
if (lean_obj_tag(v_a_3441_) == 0)
{
v_a_3434_ = v_snd_3428_;
goto v___jp_3433_;
}
else
{
lean_object* v_val_3442_; lean_object* v_fst_3443_; lean_object* v_snd_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3474_; 
v_val_3442_ = lean_ctor_get(v_a_3441_, 0);
v_fst_3443_ = lean_ctor_get(v_snd_3428_, 0);
v_snd_3444_ = lean_ctor_get(v_snd_3428_, 1);
v_isSharedCheck_3474_ = !lean_is_exclusive(v_snd_3428_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3446_ = v_snd_3428_;
v_isShared_3447_ = v_isSharedCheck_3474_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_snd_3444_);
lean_inc(v_fst_3443_);
lean_dec(v_snd_3428_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3474_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
uint8_t v___x_3448_; lean_object* v___x_3449_; 
v___x_3448_ = 0;
v___x_3449_ = l_Lean_LocalDecl_value_x3f(v_val_3442_, v___x_3448_);
if (lean_obj_tag(v___x_3449_) == 1)
{
lean_object* v_val_3450_; lean_object* v___x_3451_; 
v_val_3450_ = lean_ctor_get(v___x_3449_, 0);
lean_inc(v_val_3450_);
lean_dec_ref(v___x_3449_);
v___x_3451_ = l_Lean_LocalDecl_type(v_val_3442_);
if (lean_obj_tag(v___x_3451_) == 10)
{
lean_object* v_data_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; uint8_t v___x_3456_; uint8_t v___x_3457_; 
v_data_3452_ = lean_ctor_get(v___x_3451_, 0);
lean_inc(v_data_3452_);
lean_dec_ref(v___x_3451_);
v___x_3453_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_3454_ = lean_unsigned_to_nat(2u);
v___x_3455_ = l_Lean_KVMap_getNat(v_data_3452_, v___x_3453_, v___x_3454_);
lean_dec(v_data_3452_);
v___x_3456_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3455_);
lean_dec(v___x_3455_);
v___x_3457_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3456_, v_val_3450_, v_elimTrivial_3416_);
if (v___x_3457_ == 0)
{
lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3463_; 
v___x_3458_ = l_Lean_LocalDecl_fvarId(v_val_3442_);
v___x_3459_ = l_Lean_mkFVar(v___x_3458_);
v___x_3460_ = lean_array_push(v_fst_3443_, v___x_3459_);
v___x_3461_ = lean_array_push(v_snd_3444_, v_val_3450_);
if (v_isShared_3447_ == 0)
{
lean_ctor_set(v___x_3446_, 1, v___x_3461_);
lean_ctor_set(v___x_3446_, 0, v___x_3460_);
v___x_3463_ = v___x_3446_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v___x_3460_);
lean_ctor_set(v_reuseFailAlloc_3464_, 1, v___x_3461_);
v___x_3463_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
v_a_3434_ = v___x_3463_;
goto v___jp_3433_;
}
}
else
{
lean_object* v___x_3466_; 
lean_dec(v_val_3450_);
if (v_isShared_3447_ == 0)
{
v___x_3466_ = v___x_3446_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_fst_3443_);
lean_ctor_set(v_reuseFailAlloc_3467_, 1, v_snd_3444_);
v___x_3466_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
v_a_3434_ = v___x_3466_;
goto v___jp_3433_;
}
}
}
else
{
lean_object* v___x_3469_; 
lean_dec_ref(v___x_3451_);
lean_dec(v_val_3450_);
if (v_isShared_3447_ == 0)
{
v___x_3469_ = v___x_3446_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_fst_3443_);
lean_ctor_set(v_reuseFailAlloc_3470_, 1, v_snd_3444_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
v_a_3434_ = v___x_3469_;
goto v___jp_3433_;
}
}
}
else
{
lean_object* v___x_3472_; 
lean_dec(v___x_3449_);
if (v_isShared_3447_ == 0)
{
v___x_3472_ = v___x_3446_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v_fst_3443_);
lean_ctor_set(v_reuseFailAlloc_3473_, 1, v_snd_3444_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
v_a_3434_ = v___x_3472_;
goto v___jp_3433_;
}
}
}
}
v___jp_3433_:
{
lean_object* v___x_3436_; 
if (v_isShared_3431_ == 0)
{
lean_ctor_set(v___x_3430_, 1, v_a_3434_);
lean_ctor_set(v___x_3430_, 0, v___x_3432_);
v___x_3436_ = v___x_3430_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v___x_3432_);
lean_ctor_set(v_reuseFailAlloc_3440_, 1, v_a_3434_);
v___x_3436_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
size_t v___x_3437_; size_t v___x_3438_; lean_object* v___x_3439_; 
v___x_3437_ = ((size_t)1ULL);
v___x_3438_ = lean_usize_add(v_i_3419_, v___x_3437_);
v___x_3439_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_3416_, v_as_3417_, v_sz_3418_, v___x_3438_, v___x_3436_);
return v___x_3439_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1___boxed(lean_object* v_elimTrivial_3477_, lean_object* v_as_3478_, lean_object* v_sz_3479_, lean_object* v_i_3480_, lean_object* v_b_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_){
_start:
{
uint8_t v_elimTrivial_boxed_3487_; size_t v_sz_boxed_3488_; size_t v_i_boxed_3489_; lean_object* v_res_3490_; 
v_elimTrivial_boxed_3487_ = lean_unbox(v_elimTrivial_3477_);
v_sz_boxed_3488_ = lean_unbox_usize(v_sz_3479_);
lean_dec(v_sz_3479_);
v_i_boxed_3489_ = lean_unbox_usize(v_i_3480_);
lean_dec(v_i_3480_);
v_res_3490_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(v_elimTrivial_boxed_3487_, v_as_3478_, v_sz_boxed_3488_, v_i_boxed_3489_, v_b_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
lean_dec_ref(v_as_3478_);
return v_res_3490_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(uint8_t v_elimTrivial_3491_, lean_object* v_as_3492_, size_t v_sz_3493_, size_t v_i_3494_, lean_object* v_b_3495_){
_start:
{
uint8_t v___x_3497_; 
v___x_3497_ = lean_usize_dec_lt(v_i_3494_, v_sz_3493_);
if (v___x_3497_ == 0)
{
lean_object* v___x_3498_; 
v___x_3498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3498_, 0, v_b_3495_);
return v___x_3498_;
}
else
{
lean_object* v_snd_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3546_; 
v_snd_3499_ = lean_ctor_get(v_b_3495_, 1);
v_isSharedCheck_3546_ = !lean_is_exclusive(v_b_3495_);
if (v_isSharedCheck_3546_ == 0)
{
lean_object* v_unused_3547_; 
v_unused_3547_ = lean_ctor_get(v_b_3495_, 0);
lean_dec(v_unused_3547_);
v___x_3501_ = v_b_3495_;
v_isShared_3502_ = v_isSharedCheck_3546_;
goto v_resetjp_3500_;
}
else
{
lean_inc(v_snd_3499_);
lean_dec(v_b_3495_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3546_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
lean_object* v___x_3503_; lean_object* v_a_3505_; lean_object* v_a_3512_; 
v___x_3503_ = lean_box(0);
v_a_3512_ = lean_array_uget_borrowed(v_as_3492_, v_i_3494_);
if (lean_obj_tag(v_a_3512_) == 0)
{
v_a_3505_ = v_snd_3499_;
goto v___jp_3504_;
}
else
{
lean_object* v_val_3513_; lean_object* v_fst_3514_; lean_object* v_snd_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3545_; 
v_val_3513_ = lean_ctor_get(v_a_3512_, 0);
v_fst_3514_ = lean_ctor_get(v_snd_3499_, 0);
v_snd_3515_ = lean_ctor_get(v_snd_3499_, 1);
v_isSharedCheck_3545_ = !lean_is_exclusive(v_snd_3499_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3517_ = v_snd_3499_;
v_isShared_3518_ = v_isSharedCheck_3545_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_snd_3515_);
lean_inc(v_fst_3514_);
lean_dec(v_snd_3499_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3545_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
uint8_t v___x_3519_; lean_object* v___x_3520_; 
v___x_3519_ = 0;
v___x_3520_ = l_Lean_LocalDecl_value_x3f(v_val_3513_, v___x_3519_);
if (lean_obj_tag(v___x_3520_) == 1)
{
lean_object* v_val_3521_; lean_object* v___x_3522_; 
v_val_3521_ = lean_ctor_get(v___x_3520_, 0);
lean_inc(v_val_3521_);
lean_dec_ref(v___x_3520_);
v___x_3522_ = l_Lean_LocalDecl_type(v_val_3513_);
if (lean_obj_tag(v___x_3522_) == 10)
{
lean_object* v_data_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; uint8_t v___x_3527_; uint8_t v___x_3528_; 
v_data_3523_ = lean_ctor_get(v___x_3522_, 0);
lean_inc(v_data_3523_);
lean_dec_ref(v___x_3522_);
v___x_3524_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_3525_ = lean_unsigned_to_nat(2u);
v___x_3526_ = l_Lean_KVMap_getNat(v_data_3523_, v___x_3524_, v___x_3525_);
lean_dec(v_data_3523_);
v___x_3527_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3526_);
lean_dec(v___x_3526_);
v___x_3528_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3527_, v_val_3521_, v_elimTrivial_3491_);
if (v___x_3528_ == 0)
{
lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3534_; 
v___x_3529_ = l_Lean_LocalDecl_fvarId(v_val_3513_);
v___x_3530_ = l_Lean_mkFVar(v___x_3529_);
v___x_3531_ = lean_array_push(v_fst_3514_, v___x_3530_);
v___x_3532_ = lean_array_push(v_snd_3515_, v_val_3521_);
if (v_isShared_3518_ == 0)
{
lean_ctor_set(v___x_3517_, 1, v___x_3532_);
lean_ctor_set(v___x_3517_, 0, v___x_3531_);
v___x_3534_ = v___x_3517_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v___x_3531_);
lean_ctor_set(v_reuseFailAlloc_3535_, 1, v___x_3532_);
v___x_3534_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
v_a_3505_ = v___x_3534_;
goto v___jp_3504_;
}
}
else
{
lean_object* v___x_3537_; 
lean_dec(v_val_3521_);
if (v_isShared_3518_ == 0)
{
v___x_3537_ = v___x_3517_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_fst_3514_);
lean_ctor_set(v_reuseFailAlloc_3538_, 1, v_snd_3515_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
v_a_3505_ = v___x_3537_;
goto v___jp_3504_;
}
}
}
else
{
lean_object* v___x_3540_; 
lean_dec_ref(v___x_3522_);
lean_dec(v_val_3521_);
if (v_isShared_3518_ == 0)
{
v___x_3540_ = v___x_3517_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v_fst_3514_);
lean_ctor_set(v_reuseFailAlloc_3541_, 1, v_snd_3515_);
v___x_3540_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
v_a_3505_ = v___x_3540_;
goto v___jp_3504_;
}
}
}
else
{
lean_object* v___x_3543_; 
lean_dec(v___x_3520_);
if (v_isShared_3518_ == 0)
{
v___x_3543_ = v___x_3517_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_fst_3514_);
lean_ctor_set(v_reuseFailAlloc_3544_, 1, v_snd_3515_);
v___x_3543_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
v_a_3505_ = v___x_3543_;
goto v___jp_3504_;
}
}
}
}
v___jp_3504_:
{
lean_object* v___x_3507_; 
if (v_isShared_3502_ == 0)
{
lean_ctor_set(v___x_3501_, 1, v_a_3505_);
lean_ctor_set(v___x_3501_, 0, v___x_3503_);
v___x_3507_ = v___x_3501_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v___x_3503_);
lean_ctor_set(v_reuseFailAlloc_3511_, 1, v_a_3505_);
v___x_3507_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
size_t v___x_3508_; size_t v___x_3509_; 
v___x_3508_ = ((size_t)1ULL);
v___x_3509_ = lean_usize_add(v_i_3494_, v___x_3508_);
v_i_3494_ = v___x_3509_;
v_b_3495_ = v___x_3507_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg___boxed(lean_object* v_elimTrivial_3548_, lean_object* v_as_3549_, lean_object* v_sz_3550_, lean_object* v_i_3551_, lean_object* v_b_3552_, lean_object* v___y_3553_){
_start:
{
uint8_t v_elimTrivial_boxed_3554_; size_t v_sz_boxed_3555_; size_t v_i_boxed_3556_; lean_object* v_res_3557_; 
v_elimTrivial_boxed_3554_ = lean_unbox(v_elimTrivial_3548_);
v_sz_boxed_3555_ = lean_unbox_usize(v_sz_3550_);
lean_dec(v_sz_3550_);
v_i_boxed_3556_ = lean_unbox_usize(v_i_3551_);
lean_dec(v_i_3551_);
v_res_3557_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_boxed_3554_, v_as_3549_, v_sz_boxed_3555_, v_i_boxed_3556_, v_b_3552_);
lean_dec_ref(v_as_3549_);
return v_res_3557_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(uint8_t v_elimTrivial_3558_, lean_object* v_as_3559_, size_t v_sz_3560_, size_t v_i_3561_, lean_object* v_b_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_){
_start:
{
uint8_t v___x_3568_; 
v___x_3568_ = lean_usize_dec_lt(v_i_3561_, v_sz_3560_);
if (v___x_3568_ == 0)
{
lean_object* v___x_3569_; 
v___x_3569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3569_, 0, v_b_3562_);
return v___x_3569_;
}
else
{
lean_object* v_snd_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3617_; 
v_snd_3570_ = lean_ctor_get(v_b_3562_, 1);
v_isSharedCheck_3617_ = !lean_is_exclusive(v_b_3562_);
if (v_isSharedCheck_3617_ == 0)
{
lean_object* v_unused_3618_; 
v_unused_3618_ = lean_ctor_get(v_b_3562_, 0);
lean_dec(v_unused_3618_);
v___x_3572_ = v_b_3562_;
v_isShared_3573_ = v_isSharedCheck_3617_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_snd_3570_);
lean_dec(v_b_3562_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3617_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v___x_3574_; lean_object* v_a_3576_; lean_object* v_a_3583_; 
v___x_3574_ = lean_box(0);
v_a_3583_ = lean_array_uget_borrowed(v_as_3559_, v_i_3561_);
if (lean_obj_tag(v_a_3583_) == 0)
{
v_a_3576_ = v_snd_3570_;
goto v___jp_3575_;
}
else
{
lean_object* v_val_3584_; lean_object* v_fst_3585_; lean_object* v_snd_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3616_; 
v_val_3584_ = lean_ctor_get(v_a_3583_, 0);
v_fst_3585_ = lean_ctor_get(v_snd_3570_, 0);
v_snd_3586_ = lean_ctor_get(v_snd_3570_, 1);
v_isSharedCheck_3616_ = !lean_is_exclusive(v_snd_3570_);
if (v_isSharedCheck_3616_ == 0)
{
v___x_3588_ = v_snd_3570_;
v_isShared_3589_ = v_isSharedCheck_3616_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_snd_3586_);
lean_inc(v_fst_3585_);
lean_dec(v_snd_3570_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3616_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
uint8_t v___x_3590_; lean_object* v___x_3591_; 
v___x_3590_ = 0;
v___x_3591_ = l_Lean_LocalDecl_value_x3f(v_val_3584_, v___x_3590_);
if (lean_obj_tag(v___x_3591_) == 1)
{
lean_object* v_val_3592_; lean_object* v___x_3593_; 
v_val_3592_ = lean_ctor_get(v___x_3591_, 0);
lean_inc(v_val_3592_);
lean_dec_ref(v___x_3591_);
v___x_3593_ = l_Lean_LocalDecl_type(v_val_3584_);
if (lean_obj_tag(v___x_3593_) == 10)
{
lean_object* v_data_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; uint8_t v___x_3598_; uint8_t v___x_3599_; 
v_data_3594_ = lean_ctor_get(v___x_3593_, 0);
lean_inc(v_data_3594_);
lean_dec_ref(v___x_3593_);
v___x_3595_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_3596_ = lean_unsigned_to_nat(2u);
v___x_3597_ = l_Lean_KVMap_getNat(v_data_3594_, v___x_3595_, v___x_3596_);
lean_dec(v_data_3594_);
v___x_3598_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3597_);
lean_dec(v___x_3597_);
v___x_3599_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3598_, v_val_3592_, v_elimTrivial_3558_);
if (v___x_3599_ == 0)
{
lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3605_; 
v___x_3600_ = l_Lean_LocalDecl_fvarId(v_val_3584_);
v___x_3601_ = l_Lean_mkFVar(v___x_3600_);
v___x_3602_ = lean_array_push(v_fst_3585_, v___x_3601_);
v___x_3603_ = lean_array_push(v_snd_3586_, v_val_3592_);
if (v_isShared_3589_ == 0)
{
lean_ctor_set(v___x_3588_, 1, v___x_3603_);
lean_ctor_set(v___x_3588_, 0, v___x_3602_);
v___x_3605_ = v___x_3588_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v___x_3602_);
lean_ctor_set(v_reuseFailAlloc_3606_, 1, v___x_3603_);
v___x_3605_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
v_a_3576_ = v___x_3605_;
goto v___jp_3575_;
}
}
else
{
lean_object* v___x_3608_; 
lean_dec(v_val_3592_);
if (v_isShared_3589_ == 0)
{
v___x_3608_ = v___x_3588_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v_fst_3585_);
lean_ctor_set(v_reuseFailAlloc_3609_, 1, v_snd_3586_);
v___x_3608_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
v_a_3576_ = v___x_3608_;
goto v___jp_3575_;
}
}
}
else
{
lean_object* v___x_3611_; 
lean_dec_ref(v___x_3593_);
lean_dec(v_val_3592_);
if (v_isShared_3589_ == 0)
{
v___x_3611_ = v___x_3588_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v_fst_3585_);
lean_ctor_set(v_reuseFailAlloc_3612_, 1, v_snd_3586_);
v___x_3611_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
v_a_3576_ = v___x_3611_;
goto v___jp_3575_;
}
}
}
else
{
lean_object* v___x_3614_; 
lean_dec(v___x_3591_);
if (v_isShared_3589_ == 0)
{
v___x_3614_ = v___x_3588_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v_fst_3585_);
lean_ctor_set(v_reuseFailAlloc_3615_, 1, v_snd_3586_);
v___x_3614_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
v_a_3576_ = v___x_3614_;
goto v___jp_3575_;
}
}
}
}
v___jp_3575_:
{
lean_object* v___x_3578_; 
if (v_isShared_3573_ == 0)
{
lean_ctor_set(v___x_3572_, 1, v_a_3576_);
lean_ctor_set(v___x_3572_, 0, v___x_3574_);
v___x_3578_ = v___x_3572_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v___x_3574_);
lean_ctor_set(v_reuseFailAlloc_3582_, 1, v_a_3576_);
v___x_3578_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
size_t v___x_3579_; size_t v___x_3580_; lean_object* v___x_3581_; 
v___x_3579_ = ((size_t)1ULL);
v___x_3580_ = lean_usize_add(v_i_3561_, v___x_3579_);
v___x_3581_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_3558_, v_as_3559_, v_sz_3560_, v___x_3580_, v___x_3578_);
return v___x_3581_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3___boxed(lean_object* v_elimTrivial_3619_, lean_object* v_as_3620_, lean_object* v_sz_3621_, lean_object* v_i_3622_, lean_object* v_b_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_){
_start:
{
uint8_t v_elimTrivial_boxed_3629_; size_t v_sz_boxed_3630_; size_t v_i_boxed_3631_; lean_object* v_res_3632_; 
v_elimTrivial_boxed_3629_ = lean_unbox(v_elimTrivial_3619_);
v_sz_boxed_3630_ = lean_unbox_usize(v_sz_3621_);
lean_dec(v_sz_3621_);
v_i_boxed_3631_ = lean_unbox_usize(v_i_3622_);
lean_dec(v_i_3622_);
v_res_3632_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(v_elimTrivial_boxed_3629_, v_as_3620_, v_sz_boxed_3630_, v_i_boxed_3631_, v_b_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_);
lean_dec(v___y_3627_);
lean_dec_ref(v___y_3626_);
lean_dec(v___y_3625_);
lean_dec_ref(v___y_3624_);
lean_dec_ref(v_as_3620_);
return v_res_3632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(lean_object* v_init_3633_, uint8_t v_elimTrivial_3634_, lean_object* v_n_3635_, lean_object* v_b_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_){
_start:
{
if (lean_obj_tag(v_n_3635_) == 0)
{
lean_object* v_cs_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; size_t v_sz_3645_; size_t v___x_3646_; lean_object* v___x_3647_; 
v_cs_3642_ = lean_ctor_get(v_n_3635_, 0);
v___x_3643_ = lean_box(0);
v___x_3644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3644_, 0, v___x_3643_);
lean_ctor_set(v___x_3644_, 1, v_b_3636_);
v_sz_3645_ = lean_array_size(v_cs_3642_);
v___x_3646_ = ((size_t)0ULL);
v___x_3647_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(v_init_3633_, v_elimTrivial_3634_, v_cs_3642_, v_sz_3645_, v___x_3646_, v___x_3644_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_);
if (lean_obj_tag(v___x_3647_) == 0)
{
lean_object* v_a_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3662_; 
v_a_3648_ = lean_ctor_get(v___x_3647_, 0);
v_isSharedCheck_3662_ = !lean_is_exclusive(v___x_3647_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_3650_ = v___x_3647_;
v_isShared_3651_ = v_isSharedCheck_3662_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_a_3648_);
lean_dec(v___x_3647_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3662_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v_fst_3652_; 
v_fst_3652_ = lean_ctor_get(v_a_3648_, 0);
if (lean_obj_tag(v_fst_3652_) == 0)
{
lean_object* v_snd_3653_; lean_object* v___x_3654_; lean_object* v___x_3656_; 
v_snd_3653_ = lean_ctor_get(v_a_3648_, 1);
lean_inc(v_snd_3653_);
lean_dec(v_a_3648_);
v___x_3654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3654_, 0, v_snd_3653_);
if (v_isShared_3651_ == 0)
{
lean_ctor_set(v___x_3650_, 0, v___x_3654_);
v___x_3656_ = v___x_3650_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v___x_3654_);
v___x_3656_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
return v___x_3656_;
}
}
else
{
lean_object* v_val_3658_; lean_object* v___x_3660_; 
lean_inc_ref(v_fst_3652_);
lean_dec(v_a_3648_);
v_val_3658_ = lean_ctor_get(v_fst_3652_, 0);
lean_inc(v_val_3658_);
lean_dec_ref(v_fst_3652_);
if (v_isShared_3651_ == 0)
{
lean_ctor_set(v___x_3650_, 0, v_val_3658_);
v___x_3660_ = v___x_3650_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_val_3658_);
v___x_3660_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
return v___x_3660_;
}
}
}
}
else
{
lean_object* v_a_3663_; lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3670_; 
v_a_3663_ = lean_ctor_get(v___x_3647_, 0);
v_isSharedCheck_3670_ = !lean_is_exclusive(v___x_3647_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3665_ = v___x_3647_;
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
else
{
lean_inc(v_a_3663_);
lean_dec(v___x_3647_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
lean_object* v___x_3668_; 
if (v_isShared_3666_ == 0)
{
v___x_3668_ = v___x_3665_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_a_3663_);
v___x_3668_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
return v___x_3668_;
}
}
}
}
else
{
lean_object* v_vs_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; size_t v_sz_3674_; size_t v___x_3675_; lean_object* v___x_3676_; 
v_vs_3671_ = lean_ctor_get(v_n_3635_, 0);
v___x_3672_ = lean_box(0);
v___x_3673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3673_, 0, v___x_3672_);
lean_ctor_set(v___x_3673_, 1, v_b_3636_);
v_sz_3674_ = lean_array_size(v_vs_3671_);
v___x_3675_ = ((size_t)0ULL);
v___x_3676_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(v_elimTrivial_3634_, v_vs_3671_, v_sz_3674_, v___x_3675_, v___x_3673_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_);
if (lean_obj_tag(v___x_3676_) == 0)
{
lean_object* v_a_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3691_; 
v_a_3677_ = lean_ctor_get(v___x_3676_, 0);
v_isSharedCheck_3691_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3679_ = v___x_3676_;
v_isShared_3680_ = v_isSharedCheck_3691_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_a_3677_);
lean_dec(v___x_3676_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3691_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v_fst_3681_; 
v_fst_3681_ = lean_ctor_get(v_a_3677_, 0);
if (lean_obj_tag(v_fst_3681_) == 0)
{
lean_object* v_snd_3682_; lean_object* v___x_3683_; lean_object* v___x_3685_; 
v_snd_3682_ = lean_ctor_get(v_a_3677_, 1);
lean_inc(v_snd_3682_);
lean_dec(v_a_3677_);
v___x_3683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3683_, 0, v_snd_3682_);
if (v_isShared_3680_ == 0)
{
lean_ctor_set(v___x_3679_, 0, v___x_3683_);
v___x_3685_ = v___x_3679_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v___x_3683_);
v___x_3685_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
return v___x_3685_;
}
}
else
{
lean_object* v_val_3687_; lean_object* v___x_3689_; 
lean_inc_ref(v_fst_3681_);
lean_dec(v_a_3677_);
v_val_3687_ = lean_ctor_get(v_fst_3681_, 0);
lean_inc(v_val_3687_);
lean_dec_ref(v_fst_3681_);
if (v_isShared_3680_ == 0)
{
lean_ctor_set(v___x_3679_, 0, v_val_3687_);
v___x_3689_ = v___x_3679_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v_val_3687_);
v___x_3689_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
return v___x_3689_;
}
}
}
}
else
{
lean_object* v_a_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3699_; 
v_a_3692_ = lean_ctor_get(v___x_3676_, 0);
v_isSharedCheck_3699_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3699_ == 0)
{
v___x_3694_ = v___x_3676_;
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_a_3692_);
lean_dec(v___x_3676_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v___x_3697_; 
if (v_isShared_3695_ == 0)
{
v___x_3697_ = v___x_3694_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v_a_3692_);
v___x_3697_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
return v___x_3697_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(lean_object* v_init_3700_, uint8_t v_elimTrivial_3701_, lean_object* v_as_3702_, size_t v_sz_3703_, size_t v_i_3704_, lean_object* v_b_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_){
_start:
{
uint8_t v___x_3711_; 
v___x_3711_ = lean_usize_dec_lt(v_i_3704_, v_sz_3703_);
if (v___x_3711_ == 0)
{
lean_object* v___x_3712_; 
v___x_3712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3712_, 0, v_b_3705_);
return v___x_3712_;
}
else
{
lean_object* v_snd_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3747_; 
v_snd_3713_ = lean_ctor_get(v_b_3705_, 1);
v_isSharedCheck_3747_ = !lean_is_exclusive(v_b_3705_);
if (v_isSharedCheck_3747_ == 0)
{
lean_object* v_unused_3748_; 
v_unused_3748_ = lean_ctor_get(v_b_3705_, 0);
lean_dec(v_unused_3748_);
v___x_3715_ = v_b_3705_;
v_isShared_3716_ = v_isSharedCheck_3747_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_snd_3713_);
lean_dec(v_b_3705_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3747_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
lean_object* v_a_3717_; lean_object* v___x_3718_; 
v_a_3717_ = lean_array_uget_borrowed(v_as_3702_, v_i_3704_);
lean_inc(v_snd_3713_);
v___x_3718_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_3700_, v_elimTrivial_3701_, v_a_3717_, v_snd_3713_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_);
if (lean_obj_tag(v___x_3718_) == 0)
{
lean_object* v_a_3719_; lean_object* v___x_3721_; uint8_t v_isShared_3722_; uint8_t v_isSharedCheck_3738_; 
v_a_3719_ = lean_ctor_get(v___x_3718_, 0);
v_isSharedCheck_3738_ = !lean_is_exclusive(v___x_3718_);
if (v_isSharedCheck_3738_ == 0)
{
v___x_3721_ = v___x_3718_;
v_isShared_3722_ = v_isSharedCheck_3738_;
goto v_resetjp_3720_;
}
else
{
lean_inc(v_a_3719_);
lean_dec(v___x_3718_);
v___x_3721_ = lean_box(0);
v_isShared_3722_ = v_isSharedCheck_3738_;
goto v_resetjp_3720_;
}
v_resetjp_3720_:
{
if (lean_obj_tag(v_a_3719_) == 0)
{
lean_object* v___x_3723_; lean_object* v___x_3725_; 
v___x_3723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3723_, 0, v_a_3719_);
if (v_isShared_3716_ == 0)
{
lean_ctor_set(v___x_3715_, 0, v___x_3723_);
v___x_3725_ = v___x_3715_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v___x_3723_);
lean_ctor_set(v_reuseFailAlloc_3729_, 1, v_snd_3713_);
v___x_3725_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
lean_object* v___x_3727_; 
if (v_isShared_3722_ == 0)
{
lean_ctor_set(v___x_3721_, 0, v___x_3725_);
v___x_3727_ = v___x_3721_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v___x_3725_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
else
{
lean_object* v_a_3730_; lean_object* v___x_3731_; lean_object* v___x_3733_; 
lean_del_object(v___x_3721_);
lean_dec(v_snd_3713_);
v_a_3730_ = lean_ctor_get(v_a_3719_, 0);
lean_inc(v_a_3730_);
lean_dec_ref(v_a_3719_);
v___x_3731_ = lean_box(0);
if (v_isShared_3716_ == 0)
{
lean_ctor_set(v___x_3715_, 1, v_a_3730_);
lean_ctor_set(v___x_3715_, 0, v___x_3731_);
v___x_3733_ = v___x_3715_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v___x_3731_);
lean_ctor_set(v_reuseFailAlloc_3737_, 1, v_a_3730_);
v___x_3733_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
size_t v___x_3734_; size_t v___x_3735_; 
v___x_3734_ = ((size_t)1ULL);
v___x_3735_ = lean_usize_add(v_i_3704_, v___x_3734_);
v_i_3704_ = v___x_3735_;
v_b_3705_ = v___x_3733_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3746_; 
lean_del_object(v___x_3715_);
lean_dec(v_snd_3713_);
v_a_3739_ = lean_ctor_get(v___x_3718_, 0);
v_isSharedCheck_3746_ = !lean_is_exclusive(v___x_3718_);
if (v_isSharedCheck_3746_ == 0)
{
v___x_3741_ = v___x_3718_;
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_a_3739_);
lean_dec(v___x_3718_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___x_3744_; 
if (v_isShared_3742_ == 0)
{
v___x_3744_ = v___x_3741_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_a_3739_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
return v___x_3744_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2___boxed(lean_object* v_init_3749_, lean_object* v_elimTrivial_3750_, lean_object* v_as_3751_, lean_object* v_sz_3752_, lean_object* v_i_3753_, lean_object* v_b_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_){
_start:
{
uint8_t v_elimTrivial_boxed_3760_; size_t v_sz_boxed_3761_; size_t v_i_boxed_3762_; lean_object* v_res_3763_; 
v_elimTrivial_boxed_3760_ = lean_unbox(v_elimTrivial_3750_);
v_sz_boxed_3761_ = lean_unbox_usize(v_sz_3752_);
lean_dec(v_sz_3752_);
v_i_boxed_3762_ = lean_unbox_usize(v_i_3753_);
lean_dec(v_i_3753_);
v_res_3763_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(v_init_3749_, v_elimTrivial_boxed_3760_, v_as_3751_, v_sz_boxed_3761_, v_i_boxed_3762_, v_b_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3757_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec_ref(v_as_3751_);
lean_dec_ref(v_init_3749_);
return v_res_3763_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0___boxed(lean_object* v_init_3764_, lean_object* v_elimTrivial_3765_, lean_object* v_n_3766_, lean_object* v_b_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_){
_start:
{
uint8_t v_elimTrivial_boxed_3773_; lean_object* v_res_3774_; 
v_elimTrivial_boxed_3773_ = lean_unbox(v_elimTrivial_3765_);
v_res_3774_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_3764_, v_elimTrivial_boxed_3773_, v_n_3766_, v_b_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_);
lean_dec(v___y_3771_);
lean_dec_ref(v___y_3770_);
lean_dec(v___y_3769_);
lean_dec_ref(v___y_3768_);
lean_dec_ref(v_n_3766_);
lean_dec_ref(v_init_3764_);
return v_res_3774_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(uint8_t v_elimTrivial_3775_, lean_object* v_t_3776_, lean_object* v_init_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_){
_start:
{
lean_object* v_root_3783_; lean_object* v_tail_3784_; lean_object* v___x_3785_; 
v_root_3783_ = lean_ctor_get(v_t_3776_, 0);
v_tail_3784_ = lean_ctor_get(v_t_3776_, 1);
lean_inc_ref(v_init_3777_);
v___x_3785_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_3777_, v_elimTrivial_3775_, v_root_3783_, v_init_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_);
lean_dec_ref(v_init_3777_);
if (lean_obj_tag(v___x_3785_) == 0)
{
lean_object* v_a_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3822_; 
v_a_3786_ = lean_ctor_get(v___x_3785_, 0);
v_isSharedCheck_3822_ = !lean_is_exclusive(v___x_3785_);
if (v_isSharedCheck_3822_ == 0)
{
v___x_3788_ = v___x_3785_;
v_isShared_3789_ = v_isSharedCheck_3822_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_a_3786_);
lean_dec(v___x_3785_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3822_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
if (lean_obj_tag(v_a_3786_) == 0)
{
lean_object* v_a_3790_; lean_object* v___x_3792_; 
v_a_3790_ = lean_ctor_get(v_a_3786_, 0);
lean_inc(v_a_3790_);
lean_dec_ref(v_a_3786_);
if (v_isShared_3789_ == 0)
{
lean_ctor_set(v___x_3788_, 0, v_a_3790_);
v___x_3792_ = v___x_3788_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_a_3790_);
v___x_3792_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
return v___x_3792_;
}
}
else
{
lean_object* v_a_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; size_t v_sz_3797_; size_t v___x_3798_; lean_object* v___x_3799_; 
lean_del_object(v___x_3788_);
v_a_3794_ = lean_ctor_get(v_a_3786_, 0);
lean_inc(v_a_3794_);
lean_dec_ref(v_a_3786_);
v___x_3795_ = lean_box(0);
v___x_3796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3796_, 0, v___x_3795_);
lean_ctor_set(v___x_3796_, 1, v_a_3794_);
v_sz_3797_ = lean_array_size(v_tail_3784_);
v___x_3798_ = ((size_t)0ULL);
v___x_3799_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(v_elimTrivial_3775_, v_tail_3784_, v_sz_3797_, v___x_3798_, v___x_3796_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_);
if (lean_obj_tag(v___x_3799_) == 0)
{
lean_object* v_a_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3813_; 
v_a_3800_ = lean_ctor_get(v___x_3799_, 0);
v_isSharedCheck_3813_ = !lean_is_exclusive(v___x_3799_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3802_ = v___x_3799_;
v_isShared_3803_ = v_isSharedCheck_3813_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_a_3800_);
lean_dec(v___x_3799_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3813_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v_fst_3804_; 
v_fst_3804_ = lean_ctor_get(v_a_3800_, 0);
if (lean_obj_tag(v_fst_3804_) == 0)
{
lean_object* v_snd_3805_; lean_object* v___x_3807_; 
v_snd_3805_ = lean_ctor_get(v_a_3800_, 1);
lean_inc(v_snd_3805_);
lean_dec(v_a_3800_);
if (v_isShared_3803_ == 0)
{
lean_ctor_set(v___x_3802_, 0, v_snd_3805_);
v___x_3807_ = v___x_3802_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v_snd_3805_);
v___x_3807_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
return v___x_3807_;
}
}
else
{
lean_object* v_val_3809_; lean_object* v___x_3811_; 
lean_inc_ref(v_fst_3804_);
lean_dec(v_a_3800_);
v_val_3809_ = lean_ctor_get(v_fst_3804_, 0);
lean_inc(v_val_3809_);
lean_dec_ref(v_fst_3804_);
if (v_isShared_3803_ == 0)
{
lean_ctor_set(v___x_3802_, 0, v_val_3809_);
v___x_3811_ = v___x_3802_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_val_3809_);
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
else
{
lean_object* v_a_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3821_; 
v_a_3814_ = lean_ctor_get(v___x_3799_, 0);
v_isSharedCheck_3821_ = !lean_is_exclusive(v___x_3799_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3816_ = v___x_3799_;
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_a_3814_);
lean_dec(v___x_3799_);
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
}
}
else
{
lean_object* v_a_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3830_; 
v_a_3823_ = lean_ctor_get(v___x_3785_, 0);
v_isSharedCheck_3830_ = !lean_is_exclusive(v___x_3785_);
if (v_isSharedCheck_3830_ == 0)
{
v___x_3825_ = v___x_3785_;
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_a_3823_);
lean_dec(v___x_3785_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v___x_3828_; 
if (v_isShared_3826_ == 0)
{
v___x_3828_ = v___x_3825_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v_a_3823_);
v___x_3828_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
return v___x_3828_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0___boxed(lean_object* v_elimTrivial_3831_, lean_object* v_t_3832_, lean_object* v_init_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_){
_start:
{
uint8_t v_elimTrivial_boxed_3839_; lean_object* v_res_3840_; 
v_elimTrivial_boxed_3839_ = lean_unbox(v_elimTrivial_3831_);
v_res_3840_ = l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(v_elimTrivial_boxed_3839_, v_t_3832_, v_init_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_);
lean_dec(v___y_3837_);
lean_dec_ref(v___y_3836_);
lean_dec(v___y_3835_);
lean_dec_ref(v___y_3834_);
lean_dec_ref(v_t_3832_);
return v_res_3840_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(lean_object* v_as_3841_, size_t v_sz_3842_, size_t v_i_3843_, lean_object* v_b_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_){
_start:
{
uint8_t v___x_3850_; 
v___x_3850_ = lean_usize_dec_lt(v_i_3843_, v_sz_3842_);
if (v___x_3850_ == 0)
{
lean_object* v___x_3851_; 
v___x_3851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3851_, 0, v_b_3844_);
return v___x_3851_;
}
else
{
lean_object* v_a_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; 
v_a_3852_ = lean_array_uget_borrowed(v_as_3841_, v_i_3843_);
v___x_3853_ = l_Lean_Expr_fvarId_x21(v_a_3852_);
v___x_3854_ = l_Lean_MVarId_tryClear(v_b_3844_, v___x_3853_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_);
if (lean_obj_tag(v___x_3854_) == 0)
{
lean_object* v_a_3855_; size_t v___x_3856_; size_t v___x_3857_; 
v_a_3855_ = lean_ctor_get(v___x_3854_, 0);
lean_inc(v_a_3855_);
lean_dec_ref(v___x_3854_);
v___x_3856_ = ((size_t)1ULL);
v___x_3857_ = lean_usize_add(v_i_3843_, v___x_3856_);
v_i_3843_ = v___x_3857_;
v_b_3844_ = v_a_3855_;
goto _start;
}
else
{
return v___x_3854_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2___boxed(lean_object* v_as_3859_, lean_object* v_sz_3860_, lean_object* v_i_3861_, lean_object* v_b_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_){
_start:
{
size_t v_sz_boxed_3868_; size_t v_i_boxed_3869_; lean_object* v_res_3870_; 
v_sz_boxed_3868_ = lean_unbox_usize(v_sz_3860_);
lean_dec(v_sz_3860_);
v_i_boxed_3869_ = lean_unbox_usize(v_i_3861_);
lean_dec(v_i_3861_);
v_res_3870_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(v_as_3859_, v_sz_boxed_3868_, v_i_boxed_3869_, v_b_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_);
lean_dec(v___y_3866_);
lean_dec_ref(v___y_3865_);
lean_dec(v___y_3864_);
lean_dec_ref(v___y_3863_);
lean_dec_ref(v_as_3859_);
return v_res_3870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(lean_object* v_x_3871_, lean_object* v_x_3872_, lean_object* v_x_3873_, lean_object* v_x_3874_){
_start:
{
lean_object* v_ks_3875_; lean_object* v_vs_3876_; lean_object* v___x_3878_; uint8_t v_isShared_3879_; uint8_t v_isSharedCheck_3900_; 
v_ks_3875_ = lean_ctor_get(v_x_3871_, 0);
v_vs_3876_ = lean_ctor_get(v_x_3871_, 1);
v_isSharedCheck_3900_ = !lean_is_exclusive(v_x_3871_);
if (v_isSharedCheck_3900_ == 0)
{
v___x_3878_ = v_x_3871_;
v_isShared_3879_ = v_isSharedCheck_3900_;
goto v_resetjp_3877_;
}
else
{
lean_inc(v_vs_3876_);
lean_inc(v_ks_3875_);
lean_dec(v_x_3871_);
v___x_3878_ = lean_box(0);
v_isShared_3879_ = v_isSharedCheck_3900_;
goto v_resetjp_3877_;
}
v_resetjp_3877_:
{
lean_object* v___x_3880_; uint8_t v___x_3881_; 
v___x_3880_ = lean_array_get_size(v_ks_3875_);
v___x_3881_ = lean_nat_dec_lt(v_x_3872_, v___x_3880_);
if (v___x_3881_ == 0)
{
lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3885_; 
lean_dec(v_x_3872_);
v___x_3882_ = lean_array_push(v_ks_3875_, v_x_3873_);
v___x_3883_ = lean_array_push(v_vs_3876_, v_x_3874_);
if (v_isShared_3879_ == 0)
{
lean_ctor_set(v___x_3878_, 1, v___x_3883_);
lean_ctor_set(v___x_3878_, 0, v___x_3882_);
v___x_3885_ = v___x_3878_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v___x_3882_);
lean_ctor_set(v_reuseFailAlloc_3886_, 1, v___x_3883_);
v___x_3885_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
return v___x_3885_;
}
}
else
{
lean_object* v_k_x27_3887_; uint8_t v___x_3888_; 
v_k_x27_3887_ = lean_array_fget_borrowed(v_ks_3875_, v_x_3872_);
v___x_3888_ = l_Lean_instBEqMVarId_beq(v_x_3873_, v_k_x27_3887_);
if (v___x_3888_ == 0)
{
lean_object* v___x_3890_; 
if (v_isShared_3879_ == 0)
{
v___x_3890_ = v___x_3878_;
goto v_reusejp_3889_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v_ks_3875_);
lean_ctor_set(v_reuseFailAlloc_3894_, 1, v_vs_3876_);
v___x_3890_ = v_reuseFailAlloc_3894_;
goto v_reusejp_3889_;
}
v_reusejp_3889_:
{
lean_object* v___x_3891_; lean_object* v___x_3892_; 
v___x_3891_ = lean_unsigned_to_nat(1u);
v___x_3892_ = lean_nat_add(v_x_3872_, v___x_3891_);
lean_dec(v_x_3872_);
v_x_3871_ = v___x_3890_;
v_x_3872_ = v___x_3892_;
goto _start;
}
}
else
{
lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3898_; 
v___x_3895_ = lean_array_fset(v_ks_3875_, v_x_3872_, v_x_3873_);
v___x_3896_ = lean_array_fset(v_vs_3876_, v_x_3872_, v_x_3874_);
lean_dec(v_x_3872_);
if (v_isShared_3879_ == 0)
{
lean_ctor_set(v___x_3878_, 1, v___x_3896_);
lean_ctor_set(v___x_3878_, 0, v___x_3895_);
v___x_3898_ = v___x_3878_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v___x_3895_);
lean_ctor_set(v_reuseFailAlloc_3899_, 1, v___x_3896_);
v___x_3898_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
return v___x_3898_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(lean_object* v_n_3901_, lean_object* v_k_3902_, lean_object* v_v_3903_){
_start:
{
lean_object* v___x_3904_; lean_object* v___x_3905_; 
v___x_3904_ = lean_unsigned_to_nat(0u);
v___x_3905_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(v_n_3901_, v___x_3904_, v_k_3902_, v_v_3903_);
return v___x_3905_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0(void){
_start:
{
size_t v___x_3906_; size_t v___x_3907_; size_t v___x_3908_; 
v___x_3906_ = ((size_t)5ULL);
v___x_3907_ = ((size_t)1ULL);
v___x_3908_ = lean_usize_shift_left(v___x_3907_, v___x_3906_);
return v___x_3908_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__1(void){
_start:
{
size_t v___x_3909_; size_t v___x_3910_; size_t v___x_3911_; 
v___x_3909_ = ((size_t)1ULL);
v___x_3910_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0);
v___x_3911_ = lean_usize_sub(v___x_3910_, v___x_3909_);
return v___x_3911_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_3912_; 
v___x_3912_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_3912_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(lean_object* v_x_3913_, size_t v_x_3914_, size_t v_x_3915_, lean_object* v_x_3916_, lean_object* v_x_3917_){
_start:
{
if (lean_obj_tag(v_x_3913_) == 0)
{
lean_object* v_es_3918_; size_t v___x_3919_; size_t v___x_3920_; size_t v___x_3921_; size_t v___x_3922_; lean_object* v_j_3923_; lean_object* v___x_3924_; uint8_t v___x_3925_; 
v_es_3918_ = lean_ctor_get(v_x_3913_, 0);
v___x_3919_ = ((size_t)5ULL);
v___x_3920_ = ((size_t)1ULL);
v___x_3921_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__1);
v___x_3922_ = lean_usize_land(v_x_3914_, v___x_3921_);
v_j_3923_ = lean_usize_to_nat(v___x_3922_);
v___x_3924_ = lean_array_get_size(v_es_3918_);
v___x_3925_ = lean_nat_dec_lt(v_j_3923_, v___x_3924_);
if (v___x_3925_ == 0)
{
lean_dec(v_j_3923_);
lean_dec(v_x_3917_);
lean_dec(v_x_3916_);
return v_x_3913_;
}
else
{
lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3962_; 
lean_inc_ref(v_es_3918_);
v_isSharedCheck_3962_ = !lean_is_exclusive(v_x_3913_);
if (v_isSharedCheck_3962_ == 0)
{
lean_object* v_unused_3963_; 
v_unused_3963_ = lean_ctor_get(v_x_3913_, 0);
lean_dec(v_unused_3963_);
v___x_3927_ = v_x_3913_;
v_isShared_3928_ = v_isSharedCheck_3962_;
goto v_resetjp_3926_;
}
else
{
lean_dec(v_x_3913_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3962_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v_v_3929_; lean_object* v___x_3930_; lean_object* v_xs_x27_3931_; lean_object* v___y_3933_; 
v_v_3929_ = lean_array_fget(v_es_3918_, v_j_3923_);
v___x_3930_ = lean_box(0);
v_xs_x27_3931_ = lean_array_fset(v_es_3918_, v_j_3923_, v___x_3930_);
switch(lean_obj_tag(v_v_3929_))
{
case 0:
{
lean_object* v_key_3938_; lean_object* v_val_3939_; lean_object* v___x_3941_; uint8_t v_isShared_3942_; uint8_t v_isSharedCheck_3949_; 
v_key_3938_ = lean_ctor_get(v_v_3929_, 0);
v_val_3939_ = lean_ctor_get(v_v_3929_, 1);
v_isSharedCheck_3949_ = !lean_is_exclusive(v_v_3929_);
if (v_isSharedCheck_3949_ == 0)
{
v___x_3941_ = v_v_3929_;
v_isShared_3942_ = v_isSharedCheck_3949_;
goto v_resetjp_3940_;
}
else
{
lean_inc(v_val_3939_);
lean_inc(v_key_3938_);
lean_dec(v_v_3929_);
v___x_3941_ = lean_box(0);
v_isShared_3942_ = v_isSharedCheck_3949_;
goto v_resetjp_3940_;
}
v_resetjp_3940_:
{
uint8_t v___x_3943_; 
v___x_3943_ = l_Lean_instBEqMVarId_beq(v_x_3916_, v_key_3938_);
if (v___x_3943_ == 0)
{
lean_object* v___x_3944_; lean_object* v___x_3945_; 
lean_del_object(v___x_3941_);
v___x_3944_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3938_, v_val_3939_, v_x_3916_, v_x_3917_);
v___x_3945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3945_, 0, v___x_3944_);
v___y_3933_ = v___x_3945_;
goto v___jp_3932_;
}
else
{
lean_object* v___x_3947_; 
lean_dec(v_val_3939_);
lean_dec(v_key_3938_);
if (v_isShared_3942_ == 0)
{
lean_ctor_set(v___x_3941_, 1, v_x_3917_);
lean_ctor_set(v___x_3941_, 0, v_x_3916_);
v___x_3947_ = v___x_3941_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v_x_3916_);
lean_ctor_set(v_reuseFailAlloc_3948_, 1, v_x_3917_);
v___x_3947_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
v___y_3933_ = v___x_3947_;
goto v___jp_3932_;
}
}
}
}
case 1:
{
lean_object* v_node_3950_; lean_object* v___x_3952_; uint8_t v_isShared_3953_; uint8_t v_isSharedCheck_3960_; 
v_node_3950_ = lean_ctor_get(v_v_3929_, 0);
v_isSharedCheck_3960_ = !lean_is_exclusive(v_v_3929_);
if (v_isSharedCheck_3960_ == 0)
{
v___x_3952_ = v_v_3929_;
v_isShared_3953_ = v_isSharedCheck_3960_;
goto v_resetjp_3951_;
}
else
{
lean_inc(v_node_3950_);
lean_dec(v_v_3929_);
v___x_3952_ = lean_box(0);
v_isShared_3953_ = v_isSharedCheck_3960_;
goto v_resetjp_3951_;
}
v_resetjp_3951_:
{
size_t v___x_3954_; size_t v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3958_; 
v___x_3954_ = lean_usize_shift_right(v_x_3914_, v___x_3919_);
v___x_3955_ = lean_usize_add(v_x_3915_, v___x_3920_);
v___x_3956_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_node_3950_, v___x_3954_, v___x_3955_, v_x_3916_, v_x_3917_);
if (v_isShared_3953_ == 0)
{
lean_ctor_set(v___x_3952_, 0, v___x_3956_);
v___x_3958_ = v___x_3952_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3959_; 
v_reuseFailAlloc_3959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3959_, 0, v___x_3956_);
v___x_3958_ = v_reuseFailAlloc_3959_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
v___y_3933_ = v___x_3958_;
goto v___jp_3932_;
}
}
}
default: 
{
lean_object* v___x_3961_; 
v___x_3961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3961_, 0, v_x_3916_);
lean_ctor_set(v___x_3961_, 1, v_x_3917_);
v___y_3933_ = v___x_3961_;
goto v___jp_3932_;
}
}
v___jp_3932_:
{
lean_object* v___x_3934_; lean_object* v___x_3936_; 
v___x_3934_ = lean_array_fset(v_xs_x27_3931_, v_j_3923_, v___y_3933_);
lean_dec(v_j_3923_);
if (v_isShared_3928_ == 0)
{
lean_ctor_set(v___x_3927_, 0, v___x_3934_);
v___x_3936_ = v___x_3927_;
goto v_reusejp_3935_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v___x_3934_);
v___x_3936_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3935_;
}
v_reusejp_3935_:
{
return v___x_3936_;
}
}
}
}
}
else
{
lean_object* v_ks_3964_; lean_object* v_vs_3965_; lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_3985_; 
v_ks_3964_ = lean_ctor_get(v_x_3913_, 0);
v_vs_3965_ = lean_ctor_get(v_x_3913_, 1);
v_isSharedCheck_3985_ = !lean_is_exclusive(v_x_3913_);
if (v_isSharedCheck_3985_ == 0)
{
v___x_3967_ = v_x_3913_;
v_isShared_3968_ = v_isSharedCheck_3985_;
goto v_resetjp_3966_;
}
else
{
lean_inc(v_vs_3965_);
lean_inc(v_ks_3964_);
lean_dec(v_x_3913_);
v___x_3967_ = lean_box(0);
v_isShared_3968_ = v_isSharedCheck_3985_;
goto v_resetjp_3966_;
}
v_resetjp_3966_:
{
lean_object* v___x_3970_; 
if (v_isShared_3968_ == 0)
{
v___x_3970_ = v___x_3967_;
goto v_reusejp_3969_;
}
else
{
lean_object* v_reuseFailAlloc_3984_; 
v_reuseFailAlloc_3984_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3984_, 0, v_ks_3964_);
lean_ctor_set(v_reuseFailAlloc_3984_, 1, v_vs_3965_);
v___x_3970_ = v_reuseFailAlloc_3984_;
goto v_reusejp_3969_;
}
v_reusejp_3969_:
{
lean_object* v_newNode_3971_; uint8_t v___y_3973_; size_t v___x_3979_; uint8_t v___x_3980_; 
v_newNode_3971_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(v___x_3970_, v_x_3916_, v_x_3917_);
v___x_3979_ = ((size_t)7ULL);
v___x_3980_ = lean_usize_dec_le(v___x_3979_, v_x_3915_);
if (v___x_3980_ == 0)
{
lean_object* v___x_3981_; lean_object* v___x_3982_; uint8_t v___x_3983_; 
v___x_3981_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3971_);
v___x_3982_ = lean_unsigned_to_nat(4u);
v___x_3983_ = lean_nat_dec_lt(v___x_3981_, v___x_3982_);
lean_dec(v___x_3981_);
v___y_3973_ = v___x_3983_;
goto v___jp_3972_;
}
else
{
v___y_3973_ = v___x_3980_;
goto v___jp_3972_;
}
v___jp_3972_:
{
if (v___y_3973_ == 0)
{
lean_object* v_ks_3974_; lean_object* v_vs_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; 
v_ks_3974_ = lean_ctor_get(v_newNode_3971_, 0);
lean_inc_ref(v_ks_3974_);
v_vs_3975_ = lean_ctor_get(v_newNode_3971_, 1);
lean_inc_ref(v_vs_3975_);
lean_dec_ref(v_newNode_3971_);
v___x_3976_ = lean_unsigned_to_nat(0u);
v___x_3977_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__2);
v___x_3978_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_x_3915_, v_ks_3974_, v_vs_3975_, v___x_3976_, v___x_3977_);
lean_dec_ref(v_vs_3975_);
lean_dec_ref(v_ks_3974_);
return v___x_3978_;
}
else
{
return v_newNode_3971_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(size_t v_depth_3986_, lean_object* v_keys_3987_, lean_object* v_vals_3988_, lean_object* v_i_3989_, lean_object* v_entries_3990_){
_start:
{
lean_object* v___x_3991_; uint8_t v___x_3992_; 
v___x_3991_ = lean_array_get_size(v_keys_3987_);
v___x_3992_ = lean_nat_dec_lt(v_i_3989_, v___x_3991_);
if (v___x_3992_ == 0)
{
lean_dec(v_i_3989_);
return v_entries_3990_;
}
else
{
lean_object* v_k_3993_; lean_object* v_v_3994_; uint64_t v___x_3995_; size_t v_h_3996_; size_t v___x_3997_; lean_object* v___x_3998_; size_t v___x_3999_; size_t v___x_4000_; size_t v___x_4001_; size_t v_h_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; 
v_k_3993_ = lean_array_fget_borrowed(v_keys_3987_, v_i_3989_);
v_v_3994_ = lean_array_fget_borrowed(v_vals_3988_, v_i_3989_);
v___x_3995_ = l_Lean_instHashableMVarId_hash(v_k_3993_);
v_h_3996_ = lean_uint64_to_usize(v___x_3995_);
v___x_3997_ = ((size_t)5ULL);
v___x_3998_ = lean_unsigned_to_nat(1u);
v___x_3999_ = ((size_t)1ULL);
v___x_4000_ = lean_usize_sub(v_depth_3986_, v___x_3999_);
v___x_4001_ = lean_usize_mul(v___x_3997_, v___x_4000_);
v_h_4002_ = lean_usize_shift_right(v_h_3996_, v___x_4001_);
v___x_4003_ = lean_nat_add(v_i_3989_, v___x_3998_);
lean_dec(v_i_3989_);
lean_inc(v_v_3994_);
lean_inc(v_k_3993_);
v___x_4004_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_entries_3990_, v_h_4002_, v_depth_3986_, v_k_3993_, v_v_3994_);
v_i_3989_ = v___x_4003_;
v_entries_3990_ = v___x_4004_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg___boxed(lean_object* v_depth_4006_, lean_object* v_keys_4007_, lean_object* v_vals_4008_, lean_object* v_i_4009_, lean_object* v_entries_4010_){
_start:
{
size_t v_depth_boxed_4011_; lean_object* v_res_4012_; 
v_depth_boxed_4011_ = lean_unbox_usize(v_depth_4006_);
lean_dec(v_depth_4006_);
v_res_4012_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_depth_boxed_4011_, v_keys_4007_, v_vals_4008_, v_i_4009_, v_entries_4010_);
lean_dec_ref(v_vals_4008_);
lean_dec_ref(v_keys_4007_);
return v_res_4012_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___boxed(lean_object* v_x_4013_, lean_object* v_x_4014_, lean_object* v_x_4015_, lean_object* v_x_4016_, lean_object* v_x_4017_){
_start:
{
size_t v_x_7972__boxed_4018_; size_t v_x_7973__boxed_4019_; lean_object* v_res_4020_; 
v_x_7972__boxed_4018_ = lean_unbox_usize(v_x_4014_);
lean_dec(v_x_4014_);
v_x_7973__boxed_4019_ = lean_unbox_usize(v_x_4015_);
lean_dec(v_x_4015_);
v_res_4020_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_4013_, v_x_7972__boxed_4018_, v_x_7973__boxed_4019_, v_x_4016_, v_x_4017_);
return v_res_4020_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(lean_object* v_x_4021_, lean_object* v_x_4022_, lean_object* v_x_4023_){
_start:
{
uint64_t v___x_4024_; size_t v___x_4025_; size_t v___x_4026_; lean_object* v___x_4027_; 
v___x_4024_ = l_Lean_instHashableMVarId_hash(v_x_4022_);
v___x_4025_ = lean_uint64_to_usize(v___x_4024_);
v___x_4026_ = ((size_t)1ULL);
v___x_4027_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_4021_, v___x_4025_, v___x_4026_, v_x_4022_, v_x_4023_);
return v___x_4027_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(lean_object* v_mvarId_4028_, lean_object* v_val_4029_, lean_object* v___y_4030_){
_start:
{
lean_object* v___x_4032_; lean_object* v_mctx_4033_; lean_object* v_cache_4034_; lean_object* v_zetaDeltaFVarIds_4035_; lean_object* v_postponed_4036_; lean_object* v_diag_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4065_; 
v___x_4032_ = lean_st_ref_take(v___y_4030_);
v_mctx_4033_ = lean_ctor_get(v___x_4032_, 0);
v_cache_4034_ = lean_ctor_get(v___x_4032_, 1);
v_zetaDeltaFVarIds_4035_ = lean_ctor_get(v___x_4032_, 2);
v_postponed_4036_ = lean_ctor_get(v___x_4032_, 3);
v_diag_4037_ = lean_ctor_get(v___x_4032_, 4);
v_isSharedCheck_4065_ = !lean_is_exclusive(v___x_4032_);
if (v_isSharedCheck_4065_ == 0)
{
v___x_4039_ = v___x_4032_;
v_isShared_4040_ = v_isSharedCheck_4065_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_diag_4037_);
lean_inc(v_postponed_4036_);
lean_inc(v_zetaDeltaFVarIds_4035_);
lean_inc(v_cache_4034_);
lean_inc(v_mctx_4033_);
lean_dec(v___x_4032_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4065_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
lean_object* v_depth_4041_; lean_object* v_levelAssignDepth_4042_; lean_object* v_lmvarCounter_4043_; lean_object* v_mvarCounter_4044_; lean_object* v_lDecls_4045_; lean_object* v_decls_4046_; lean_object* v_userNames_4047_; lean_object* v_lAssignment_4048_; lean_object* v_eAssignment_4049_; lean_object* v_dAssignment_4050_; lean_object* v___x_4052_; uint8_t v_isShared_4053_; uint8_t v_isSharedCheck_4064_; 
v_depth_4041_ = lean_ctor_get(v_mctx_4033_, 0);
v_levelAssignDepth_4042_ = lean_ctor_get(v_mctx_4033_, 1);
v_lmvarCounter_4043_ = lean_ctor_get(v_mctx_4033_, 2);
v_mvarCounter_4044_ = lean_ctor_get(v_mctx_4033_, 3);
v_lDecls_4045_ = lean_ctor_get(v_mctx_4033_, 4);
v_decls_4046_ = lean_ctor_get(v_mctx_4033_, 5);
v_userNames_4047_ = lean_ctor_get(v_mctx_4033_, 6);
v_lAssignment_4048_ = lean_ctor_get(v_mctx_4033_, 7);
v_eAssignment_4049_ = lean_ctor_get(v_mctx_4033_, 8);
v_dAssignment_4050_ = lean_ctor_get(v_mctx_4033_, 9);
v_isSharedCheck_4064_ = !lean_is_exclusive(v_mctx_4033_);
if (v_isSharedCheck_4064_ == 0)
{
v___x_4052_ = v_mctx_4033_;
v_isShared_4053_ = v_isSharedCheck_4064_;
goto v_resetjp_4051_;
}
else
{
lean_inc(v_dAssignment_4050_);
lean_inc(v_eAssignment_4049_);
lean_inc(v_lAssignment_4048_);
lean_inc(v_userNames_4047_);
lean_inc(v_decls_4046_);
lean_inc(v_lDecls_4045_);
lean_inc(v_mvarCounter_4044_);
lean_inc(v_lmvarCounter_4043_);
lean_inc(v_levelAssignDepth_4042_);
lean_inc(v_depth_4041_);
lean_dec(v_mctx_4033_);
v___x_4052_ = lean_box(0);
v_isShared_4053_ = v_isSharedCheck_4064_;
goto v_resetjp_4051_;
}
v_resetjp_4051_:
{
lean_object* v___x_4054_; lean_object* v___x_4056_; 
v___x_4054_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(v_eAssignment_4049_, v_mvarId_4028_, v_val_4029_);
if (v_isShared_4053_ == 0)
{
lean_ctor_set(v___x_4052_, 8, v___x_4054_);
v___x_4056_ = v___x_4052_;
goto v_reusejp_4055_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v_depth_4041_);
lean_ctor_set(v_reuseFailAlloc_4063_, 1, v_levelAssignDepth_4042_);
lean_ctor_set(v_reuseFailAlloc_4063_, 2, v_lmvarCounter_4043_);
lean_ctor_set(v_reuseFailAlloc_4063_, 3, v_mvarCounter_4044_);
lean_ctor_set(v_reuseFailAlloc_4063_, 4, v_lDecls_4045_);
lean_ctor_set(v_reuseFailAlloc_4063_, 5, v_decls_4046_);
lean_ctor_set(v_reuseFailAlloc_4063_, 6, v_userNames_4047_);
lean_ctor_set(v_reuseFailAlloc_4063_, 7, v_lAssignment_4048_);
lean_ctor_set(v_reuseFailAlloc_4063_, 8, v___x_4054_);
lean_ctor_set(v_reuseFailAlloc_4063_, 9, v_dAssignment_4050_);
v___x_4056_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4055_;
}
v_reusejp_4055_:
{
lean_object* v___x_4058_; 
if (v_isShared_4040_ == 0)
{
lean_ctor_set(v___x_4039_, 0, v___x_4056_);
v___x_4058_ = v___x_4039_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v___x_4056_);
lean_ctor_set(v_reuseFailAlloc_4062_, 1, v_cache_4034_);
lean_ctor_set(v_reuseFailAlloc_4062_, 2, v_zetaDeltaFVarIds_4035_);
lean_ctor_set(v_reuseFailAlloc_4062_, 3, v_postponed_4036_);
lean_ctor_set(v_reuseFailAlloc_4062_, 4, v_diag_4037_);
v___x_4058_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; 
v___x_4059_ = lean_st_ref_set(v___y_4030_, v___x_4058_);
v___x_4060_ = lean_box(0);
v___x_4061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4061_, 0, v___x_4060_);
return v___x_4061_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg___boxed(lean_object* v_mvarId_4066_, lean_object* v_val_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_){
_start:
{
lean_object* v_res_4070_; 
v_res_4070_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(v_mvarId_4066_, v_val_4067_, v___y_4068_);
lean_dec(v___y_4068_);
return v_res_4070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___lam__0(lean_object* v_mvar_4073_, uint8_t v_elimTrivial_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_){
_start:
{
lean_object* v___x_4080_; 
lean_inc(v_mvar_4073_);
v___x_4080_ = l_Lean_MVarId_getType(v_mvar_4073_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_);
if (lean_obj_tag(v___x_4080_) == 0)
{
lean_object* v_a_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; 
v_a_4081_ = lean_ctor_get(v___x_4080_, 0);
lean_inc(v_a_4081_);
lean_dec_ref(v___x_4080_);
v___x_4082_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0));
v___x_4083_ = l_Lean_Elab_Tactic_Do_countUses(v_a_4081_, v___x_4082_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_);
if (lean_obj_tag(v___x_4083_) == 0)
{
lean_object* v_a_4084_; lean_object* v_fst_4085_; lean_object* v_snd_4086_; lean_object* v_lctx_4087_; lean_object* v___x_4088_; 
v_a_4084_ = lean_ctor_get(v___x_4083_, 0);
lean_inc(v_a_4084_);
lean_dec_ref(v___x_4083_);
v_fst_4085_ = lean_ctor_get(v_a_4084_, 0);
lean_inc(v_fst_4085_);
v_snd_4086_ = lean_ctor_get(v_a_4084_, 1);
lean_inc(v_snd_4086_);
lean_dec(v_a_4084_);
v_lctx_4087_ = lean_ctor_get(v___y_4075_, 2);
lean_inc_ref(v_lctx_4087_);
v___x_4088_ = l_Lean_Elab_Tactic_Do_countUsesLCtx(v_lctx_4087_, v_snd_4086_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_);
if (lean_obj_tag(v___x_4088_) == 0)
{
lean_object* v_a_4089_; lean_object* v___x_4090_; lean_object* v_decls_4091_; lean_object* v___x_4092_; 
v_a_4089_ = lean_ctor_get(v___x_4088_, 0);
lean_inc(v_a_4089_);
lean_dec_ref(v___x_4088_);
v___x_4090_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLets___lam__0___closed__0));
v_decls_4091_ = lean_ctor_get(v_a_4089_, 1);
lean_inc_ref(v_decls_4091_);
lean_dec(v_a_4089_);
v___x_4092_ = l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(v_elimTrivial_4074_, v_decls_4091_, v___x_4090_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_);
lean_dec_ref(v_decls_4091_);
if (lean_obj_tag(v___x_4092_) == 0)
{
lean_object* v_a_4093_; lean_object* v_fst_4094_; lean_object* v_snd_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; 
v_a_4093_ = lean_ctor_get(v___x_4092_, 0);
lean_inc(v_a_4093_);
lean_dec_ref(v___x_4092_);
v_fst_4094_ = lean_ctor_get(v_a_4093_, 0);
lean_inc(v_fst_4094_);
v_snd_4095_ = lean_ctor_get(v_a_4093_, 1);
lean_inc(v_snd_4095_);
lean_dec(v_a_4093_);
v___x_4096_ = l_Lean_Expr_replaceFVars(v_fst_4085_, v_fst_4094_, v_snd_4095_);
lean_dec(v_snd_4095_);
lean_dec(v_fst_4085_);
v___x_4097_ = l_Lean_Elab_Tactic_Do_elimLetsCore(v___x_4096_, v_elimTrivial_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_);
if (lean_obj_tag(v___x_4097_) == 0)
{
lean_object* v_a_4098_; lean_object* v___x_4099_; 
v_a_4098_ = lean_ctor_get(v___x_4097_, 0);
lean_inc(v_a_4098_);
lean_dec_ref(v___x_4097_);
lean_inc(v_mvar_4073_);
v___x_4099_ = l_Lean_MVarId_getTag(v_mvar_4073_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_);
if (lean_obj_tag(v___x_4099_) == 0)
{
lean_object* v_a_4100_; lean_object* v___x_4101_; 
v_a_4100_ = lean_ctor_get(v___x_4099_, 0);
lean_inc(v_a_4100_);
lean_dec_ref(v___x_4099_);
v___x_4101_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_4098_, v_a_4100_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_);
if (lean_obj_tag(v___x_4101_) == 0)
{
lean_object* v_a_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; size_t v_sz_4105_; size_t v___x_4106_; lean_object* v___x_4107_; 
v_a_4102_ = lean_ctor_get(v___x_4101_, 0);
lean_inc_n(v_a_4102_, 2);
lean_dec_ref(v___x_4101_);
v___x_4103_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(v_mvar_4073_, v_a_4102_, v___y_4076_);
lean_dec_ref(v___x_4103_);
v___x_4104_ = l_Lean_Expr_mvarId_x21(v_a_4102_);
lean_dec(v_a_4102_);
v_sz_4105_ = lean_array_size(v_fst_4094_);
v___x_4106_ = ((size_t)0ULL);
v___x_4107_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(v_fst_4094_, v_sz_4105_, v___x_4106_, v___x_4104_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_);
lean_dec_ref(v___y_4075_);
lean_dec(v_fst_4094_);
return v___x_4107_;
}
else
{
lean_object* v_a_4108_; lean_object* v___x_4110_; uint8_t v_isShared_4111_; uint8_t v_isSharedCheck_4115_; 
lean_dec(v_fst_4094_);
lean_dec_ref(v___y_4075_);
lean_dec(v_mvar_4073_);
v_a_4108_ = lean_ctor_get(v___x_4101_, 0);
v_isSharedCheck_4115_ = !lean_is_exclusive(v___x_4101_);
if (v_isSharedCheck_4115_ == 0)
{
v___x_4110_ = v___x_4101_;
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
else
{
lean_inc(v_a_4108_);
lean_dec(v___x_4101_);
v___x_4110_ = lean_box(0);
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
v_resetjp_4109_:
{
lean_object* v___x_4113_; 
if (v_isShared_4111_ == 0)
{
v___x_4113_ = v___x_4110_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v_a_4108_);
v___x_4113_ = v_reuseFailAlloc_4114_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
return v___x_4113_;
}
}
}
}
else
{
lean_object* v_a_4116_; lean_object* v___x_4118_; uint8_t v_isShared_4119_; uint8_t v_isSharedCheck_4123_; 
lean_dec(v_a_4098_);
lean_dec(v_fst_4094_);
lean_dec_ref(v___y_4075_);
lean_dec(v_mvar_4073_);
v_a_4116_ = lean_ctor_get(v___x_4099_, 0);
v_isSharedCheck_4123_ = !lean_is_exclusive(v___x_4099_);
if (v_isSharedCheck_4123_ == 0)
{
v___x_4118_ = v___x_4099_;
v_isShared_4119_ = v_isSharedCheck_4123_;
goto v_resetjp_4117_;
}
else
{
lean_inc(v_a_4116_);
lean_dec(v___x_4099_);
v___x_4118_ = lean_box(0);
v_isShared_4119_ = v_isSharedCheck_4123_;
goto v_resetjp_4117_;
}
v_resetjp_4117_:
{
lean_object* v___x_4121_; 
if (v_isShared_4119_ == 0)
{
v___x_4121_ = v___x_4118_;
goto v_reusejp_4120_;
}
else
{
lean_object* v_reuseFailAlloc_4122_; 
v_reuseFailAlloc_4122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4122_, 0, v_a_4116_);
v___x_4121_ = v_reuseFailAlloc_4122_;
goto v_reusejp_4120_;
}
v_reusejp_4120_:
{
return v___x_4121_;
}
}
}
}
else
{
lean_object* v_a_4124_; lean_object* v___x_4126_; uint8_t v_isShared_4127_; uint8_t v_isSharedCheck_4131_; 
lean_dec(v_fst_4094_);
lean_dec_ref(v___y_4075_);
lean_dec(v_mvar_4073_);
v_a_4124_ = lean_ctor_get(v___x_4097_, 0);
v_isSharedCheck_4131_ = !lean_is_exclusive(v___x_4097_);
if (v_isSharedCheck_4131_ == 0)
{
v___x_4126_ = v___x_4097_;
v_isShared_4127_ = v_isSharedCheck_4131_;
goto v_resetjp_4125_;
}
else
{
lean_inc(v_a_4124_);
lean_dec(v___x_4097_);
v___x_4126_ = lean_box(0);
v_isShared_4127_ = v_isSharedCheck_4131_;
goto v_resetjp_4125_;
}
v_resetjp_4125_:
{
lean_object* v___x_4129_; 
if (v_isShared_4127_ == 0)
{
v___x_4129_ = v___x_4126_;
goto v_reusejp_4128_;
}
else
{
lean_object* v_reuseFailAlloc_4130_; 
v_reuseFailAlloc_4130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4130_, 0, v_a_4124_);
v___x_4129_ = v_reuseFailAlloc_4130_;
goto v_reusejp_4128_;
}
v_reusejp_4128_:
{
return v___x_4129_;
}
}
}
}
else
{
lean_object* v_a_4132_; lean_object* v___x_4134_; uint8_t v_isShared_4135_; uint8_t v_isSharedCheck_4139_; 
lean_dec(v_fst_4085_);
lean_dec_ref(v___y_4075_);
lean_dec(v_mvar_4073_);
v_a_4132_ = lean_ctor_get(v___x_4092_, 0);
v_isSharedCheck_4139_ = !lean_is_exclusive(v___x_4092_);
if (v_isSharedCheck_4139_ == 0)
{
v___x_4134_ = v___x_4092_;
v_isShared_4135_ = v_isSharedCheck_4139_;
goto v_resetjp_4133_;
}
else
{
lean_inc(v_a_4132_);
lean_dec(v___x_4092_);
v___x_4134_ = lean_box(0);
v_isShared_4135_ = v_isSharedCheck_4139_;
goto v_resetjp_4133_;
}
v_resetjp_4133_:
{
lean_object* v___x_4137_; 
if (v_isShared_4135_ == 0)
{
v___x_4137_ = v___x_4134_;
goto v_reusejp_4136_;
}
else
{
lean_object* v_reuseFailAlloc_4138_; 
v_reuseFailAlloc_4138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4138_, 0, v_a_4132_);
v___x_4137_ = v_reuseFailAlloc_4138_;
goto v_reusejp_4136_;
}
v_reusejp_4136_:
{
return v___x_4137_;
}
}
}
}
else
{
lean_object* v_a_4140_; lean_object* v___x_4142_; uint8_t v_isShared_4143_; uint8_t v_isSharedCheck_4147_; 
lean_dec(v_fst_4085_);
lean_dec_ref(v___y_4075_);
lean_dec(v_mvar_4073_);
v_a_4140_ = lean_ctor_get(v___x_4088_, 0);
v_isSharedCheck_4147_ = !lean_is_exclusive(v___x_4088_);
if (v_isSharedCheck_4147_ == 0)
{
v___x_4142_ = v___x_4088_;
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
else
{
lean_inc(v_a_4140_);
lean_dec(v___x_4088_);
v___x_4142_ = lean_box(0);
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
v_resetjp_4141_:
{
lean_object* v___x_4145_; 
if (v_isShared_4143_ == 0)
{
v___x_4145_ = v___x_4142_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v_a_4140_);
v___x_4145_ = v_reuseFailAlloc_4146_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
return v___x_4145_;
}
}
}
}
else
{
lean_object* v_a_4148_; lean_object* v___x_4150_; uint8_t v_isShared_4151_; uint8_t v_isSharedCheck_4155_; 
lean_dec_ref(v___y_4075_);
lean_dec(v_mvar_4073_);
v_a_4148_ = lean_ctor_get(v___x_4083_, 0);
v_isSharedCheck_4155_ = !lean_is_exclusive(v___x_4083_);
if (v_isSharedCheck_4155_ == 0)
{
v___x_4150_ = v___x_4083_;
v_isShared_4151_ = v_isSharedCheck_4155_;
goto v_resetjp_4149_;
}
else
{
lean_inc(v_a_4148_);
lean_dec(v___x_4083_);
v___x_4150_ = lean_box(0);
v_isShared_4151_ = v_isSharedCheck_4155_;
goto v_resetjp_4149_;
}
v_resetjp_4149_:
{
lean_object* v___x_4153_; 
if (v_isShared_4151_ == 0)
{
v___x_4153_ = v___x_4150_;
goto v_reusejp_4152_;
}
else
{
lean_object* v_reuseFailAlloc_4154_; 
v_reuseFailAlloc_4154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4154_, 0, v_a_4148_);
v___x_4153_ = v_reuseFailAlloc_4154_;
goto v_reusejp_4152_;
}
v_reusejp_4152_:
{
return v___x_4153_;
}
}
}
}
else
{
lean_object* v_a_4156_; lean_object* v___x_4158_; uint8_t v_isShared_4159_; uint8_t v_isSharedCheck_4163_; 
lean_dec_ref(v___y_4075_);
lean_dec(v_mvar_4073_);
v_a_4156_ = lean_ctor_get(v___x_4080_, 0);
v_isSharedCheck_4163_ = !lean_is_exclusive(v___x_4080_);
if (v_isSharedCheck_4163_ == 0)
{
v___x_4158_ = v___x_4080_;
v_isShared_4159_ = v_isSharedCheck_4163_;
goto v_resetjp_4157_;
}
else
{
lean_inc(v_a_4156_);
lean_dec(v___x_4080_);
v___x_4158_ = lean_box(0);
v_isShared_4159_ = v_isSharedCheck_4163_;
goto v_resetjp_4157_;
}
v_resetjp_4157_:
{
lean_object* v___x_4161_; 
if (v_isShared_4159_ == 0)
{
v___x_4161_ = v___x_4158_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4162_; 
v_reuseFailAlloc_4162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4162_, 0, v_a_4156_);
v___x_4161_ = v_reuseFailAlloc_4162_;
goto v_reusejp_4160_;
}
v_reusejp_4160_:
{
return v___x_4161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___lam__0___boxed(lean_object* v_mvar_4164_, lean_object* v_elimTrivial_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_){
_start:
{
uint8_t v_elimTrivial_boxed_4171_; lean_object* v_res_4172_; 
v_elimTrivial_boxed_4171_ = lean_unbox(v_elimTrivial_4165_);
v_res_4172_ = l_Lean_Elab_Tactic_Do_elimLets___lam__0(v_mvar_4164_, v_elimTrivial_boxed_4171_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_);
lean_dec(v___y_4169_);
lean_dec_ref(v___y_4168_);
lean_dec(v___y_4167_);
return v_res_4172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets(lean_object* v_mvar_4173_, uint8_t v_elimTrivial_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_){
_start:
{
lean_object* v___x_4180_; lean_object* v___f_4181_; lean_object* v___x_4182_; 
v___x_4180_ = lean_box(v_elimTrivial_4174_);
lean_inc(v_mvar_4173_);
v___f_4181_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elimLets___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4181_, 0, v_mvar_4173_);
lean_closure_set(v___f_4181_, 1, v___x_4180_);
v___x_4182_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(v_mvar_4173_, v___f_4181_, v_a_4175_, v_a_4176_, v_a_4177_, v_a_4178_);
return v___x_4182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___boxed(lean_object* v_mvar_4183_, lean_object* v_elimTrivial_4184_, lean_object* v_a_4185_, lean_object* v_a_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_){
_start:
{
uint8_t v_elimTrivial_boxed_4190_; lean_object* v_res_4191_; 
v_elimTrivial_boxed_4190_ = lean_unbox(v_elimTrivial_4184_);
v_res_4191_ = l_Lean_Elab_Tactic_Do_elimLets(v_mvar_4183_, v_elimTrivial_boxed_4190_, v_a_4185_, v_a_4186_, v_a_4187_, v_a_4188_);
lean_dec(v_a_4188_);
lean_dec_ref(v_a_4187_);
lean_dec(v_a_4186_);
lean_dec_ref(v_a_4185_);
return v_res_4191_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1(lean_object* v_mvarId_4192_, lean_object* v_val_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_){
_start:
{
lean_object* v___x_4199_; 
v___x_4199_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(v_mvarId_4192_, v_val_4193_, v___y_4195_);
return v___x_4199_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___boxed(lean_object* v_mvarId_4200_, lean_object* v_val_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_){
_start:
{
lean_object* v_res_4207_; 
v_res_4207_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1(v_mvarId_4200_, v_val_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_);
lean_dec(v___y_4205_);
lean_dec_ref(v___y_4204_);
lean_dec(v___y_4203_);
lean_dec_ref(v___y_4202_);
return v_res_4207_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3(lean_object* v_00_u03b2_4208_, lean_object* v_x_4209_, lean_object* v_x_4210_, lean_object* v_x_4211_){
_start:
{
lean_object* v___x_4212_; 
v___x_4212_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(v_x_4209_, v_x_4210_, v_x_4211_);
return v___x_4212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5(uint8_t v_elimTrivial_4213_, lean_object* v_as_4214_, size_t v_sz_4215_, size_t v_i_4216_, lean_object* v_b_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_){
_start:
{
lean_object* v___x_4223_; 
v___x_4223_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_4213_, v_as_4214_, v_sz_4215_, v_i_4216_, v_b_4217_);
return v___x_4223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___boxed(lean_object* v_elimTrivial_4224_, lean_object* v_as_4225_, lean_object* v_sz_4226_, lean_object* v_i_4227_, lean_object* v_b_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_){
_start:
{
uint8_t v_elimTrivial_boxed_4234_; size_t v_sz_boxed_4235_; size_t v_i_boxed_4236_; lean_object* v_res_4237_; 
v_elimTrivial_boxed_4234_ = lean_unbox(v_elimTrivial_4224_);
v_sz_boxed_4235_ = lean_unbox_usize(v_sz_4226_);
lean_dec(v_sz_4226_);
v_i_boxed_4236_ = lean_unbox_usize(v_i_4227_);
lean_dec(v_i_4227_);
v_res_4237_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5(v_elimTrivial_boxed_4234_, v_as_4225_, v_sz_boxed_4235_, v_i_boxed_4236_, v_b_4228_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_);
lean_dec(v___y_4232_);
lean_dec_ref(v___y_4231_);
lean_dec(v___y_4230_);
lean_dec_ref(v___y_4229_);
lean_dec_ref(v_as_4225_);
return v_res_4237_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_4238_, lean_object* v_x_4239_, size_t v_x_4240_, size_t v_x_4241_, lean_object* v_x_4242_, lean_object* v_x_4243_){
_start:
{
lean_object* v___x_4244_; 
v___x_4244_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_4239_, v_x_4240_, v_x_4241_, v_x_4242_, v_x_4243_);
return v___x_4244_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___boxed(lean_object* v_00_u03b2_4245_, lean_object* v_x_4246_, lean_object* v_x_4247_, lean_object* v_x_4248_, lean_object* v_x_4249_, lean_object* v_x_4250_){
_start:
{
size_t v_x_8428__boxed_4251_; size_t v_x_8429__boxed_4252_; lean_object* v_res_4253_; 
v_x_8428__boxed_4251_ = lean_unbox_usize(v_x_4247_);
lean_dec(v_x_4247_);
v_x_8429__boxed_4252_ = lean_unbox_usize(v_x_4248_);
lean_dec(v_x_4248_);
v_res_4253_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8(v_00_u03b2_4245_, v_x_4246_, v_x_8428__boxed_4251_, v_x_8429__boxed_4252_, v_x_4249_, v_x_4250_);
return v_res_4253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6(uint8_t v_elimTrivial_4254_, lean_object* v_as_4255_, size_t v_sz_4256_, size_t v_i_4257_, lean_object* v_b_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_){
_start:
{
lean_object* v___x_4264_; 
v___x_4264_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_4254_, v_as_4255_, v_sz_4256_, v_i_4257_, v_b_4258_);
return v___x_4264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___boxed(lean_object* v_elimTrivial_4265_, lean_object* v_as_4266_, lean_object* v_sz_4267_, lean_object* v_i_4268_, lean_object* v_b_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_){
_start:
{
uint8_t v_elimTrivial_boxed_4275_; size_t v_sz_boxed_4276_; size_t v_i_boxed_4277_; lean_object* v_res_4278_; 
v_elimTrivial_boxed_4275_ = lean_unbox(v_elimTrivial_4265_);
v_sz_boxed_4276_ = lean_unbox_usize(v_sz_4267_);
lean_dec(v_sz_4267_);
v_i_boxed_4277_ = lean_unbox_usize(v_i_4268_);
lean_dec(v_i_4268_);
v_res_4278_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6(v_elimTrivial_boxed_4275_, v_as_4266_, v_sz_boxed_4276_, v_i_boxed_4277_, v_b_4269_, v___y_4270_, v___y_4271_, v___y_4272_, v___y_4273_);
lean_dec(v___y_4273_);
lean_dec_ref(v___y_4272_);
lean_dec(v___y_4271_);
lean_dec_ref(v___y_4270_);
lean_dec_ref(v_as_4266_);
return v_res_4278_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11(lean_object* v_00_u03b2_4279_, lean_object* v_n_4280_, lean_object* v_k_4281_, lean_object* v_v_4282_){
_start:
{
lean_object* v___x_4283_; 
v___x_4283_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(v_n_4280_, v_k_4281_, v_v_4282_);
return v___x_4283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12(lean_object* v_00_u03b2_4284_, size_t v_depth_4285_, lean_object* v_keys_4286_, lean_object* v_vals_4287_, lean_object* v_heq_4288_, lean_object* v_i_4289_, lean_object* v_entries_4290_){
_start:
{
lean_object* v___x_4291_; 
v___x_4291_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_depth_4285_, v_keys_4286_, v_vals_4287_, v_i_4289_, v_entries_4290_);
return v___x_4291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___boxed(lean_object* v_00_u03b2_4292_, lean_object* v_depth_4293_, lean_object* v_keys_4294_, lean_object* v_vals_4295_, lean_object* v_heq_4296_, lean_object* v_i_4297_, lean_object* v_entries_4298_){
_start:
{
size_t v_depth_boxed_4299_; lean_object* v_res_4300_; 
v_depth_boxed_4299_ = lean_unbox_usize(v_depth_4293_);
lean_dec(v_depth_4293_);
v_res_4300_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12(v_00_u03b2_4292_, v_depth_boxed_4299_, v_keys_4294_, v_vals_4295_, v_heq_4296_, v_i_4297_, v_entries_4298_);
lean_dec_ref(v_vals_4295_);
lean_dec_ref(v_keys_4294_);
return v_res_4300_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12(lean_object* v_00_u03b2_4301_, lean_object* v_x_4302_, lean_object* v_x_4303_, lean_object* v_x_4304_, lean_object* v_x_4305_){
_start:
{
lean_object* v___x_4306_; 
v___x_4306_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(v_x_4302_, v_x_4303_, v_x_4304_, v_x_4305_);
return v___x_4306_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_LetElim(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_Do_instInhabitedUses_default = _init_l_Lean_Elab_Tactic_Do_instInhabitedUses_default();
l_Lean_Elab_Tactic_Do_instInhabitedUses = _init_l_Lean_Elab_Tactic_Do_instInhabitedUses();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_LetElim(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1 = _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Simp(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_LetElim(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_LetElim(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_LetElim(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_LetElim(builtin);
}
#ifdef __cplusplus
}
#endif
