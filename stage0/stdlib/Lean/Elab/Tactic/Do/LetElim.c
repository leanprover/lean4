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
lean_object* v___x_752_; lean_object* v_ngen_753_; lean_object* v_namePrefix_754_; lean_object* v_idx_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_784_; 
v___x_752_ = lean_st_ref_get(v___y_750_);
v_ngen_753_ = lean_ctor_get(v___x_752_, 2);
lean_inc_ref(v_ngen_753_);
lean_dec(v___x_752_);
v_namePrefix_754_ = lean_ctor_get(v_ngen_753_, 0);
v_idx_755_ = lean_ctor_get(v_ngen_753_, 1);
v_isSharedCheck_784_ = !lean_is_exclusive(v_ngen_753_);
if (v_isSharedCheck_784_ == 0)
{
v___x_757_ = v_ngen_753_;
v_isShared_758_ = v_isSharedCheck_784_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_idx_755_);
lean_inc(v_namePrefix_754_);
lean_dec(v_ngen_753_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_784_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_759_; lean_object* v_env_760_; lean_object* v_nextMacroScope_761_; lean_object* v_auxDeclNGen_762_; lean_object* v_traceState_763_; lean_object* v_cache_764_; lean_object* v_messages_765_; lean_object* v_infoState_766_; lean_object* v_snapshotTasks_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_782_; 
v___x_759_ = lean_st_ref_take(v___y_750_);
v_env_760_ = lean_ctor_get(v___x_759_, 0);
v_nextMacroScope_761_ = lean_ctor_get(v___x_759_, 1);
v_auxDeclNGen_762_ = lean_ctor_get(v___x_759_, 3);
v_traceState_763_ = lean_ctor_get(v___x_759_, 4);
v_cache_764_ = lean_ctor_get(v___x_759_, 5);
v_messages_765_ = lean_ctor_get(v___x_759_, 6);
v_infoState_766_ = lean_ctor_get(v___x_759_, 7);
v_snapshotTasks_767_ = lean_ctor_get(v___x_759_, 8);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_782_ == 0)
{
lean_object* v_unused_783_; 
v_unused_783_ = lean_ctor_get(v___x_759_, 2);
lean_dec(v_unused_783_);
v___x_769_ = v___x_759_;
v_isShared_770_ = v_isSharedCheck_782_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_snapshotTasks_767_);
lean_inc(v_infoState_766_);
lean_inc(v_messages_765_);
lean_inc(v_cache_764_);
lean_inc(v_traceState_763_);
lean_inc(v_auxDeclNGen_762_);
lean_inc(v_nextMacroScope_761_);
lean_inc(v_env_760_);
lean_dec(v___x_759_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_782_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v_r_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_775_; 
lean_inc(v_idx_755_);
lean_inc(v_namePrefix_754_);
v_r_771_ = l_Lean_Name_num___override(v_namePrefix_754_, v_idx_755_);
v___x_772_ = lean_unsigned_to_nat(1u);
v___x_773_ = lean_nat_add(v_idx_755_, v___x_772_);
lean_dec(v_idx_755_);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 1, v___x_773_);
v___x_775_ = v___x_757_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_namePrefix_754_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v___x_773_);
v___x_775_ = v_reuseFailAlloc_781_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
lean_object* v___x_777_; 
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 2, v___x_775_);
v___x_777_ = v___x_769_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_env_760_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v_nextMacroScope_761_);
lean_ctor_set(v_reuseFailAlloc_780_, 2, v___x_775_);
lean_ctor_set(v_reuseFailAlloc_780_, 3, v_auxDeclNGen_762_);
lean_ctor_set(v_reuseFailAlloc_780_, 4, v_traceState_763_);
lean_ctor_set(v_reuseFailAlloc_780_, 5, v_cache_764_);
lean_ctor_set(v_reuseFailAlloc_780_, 6, v_messages_765_);
lean_ctor_set(v_reuseFailAlloc_780_, 7, v_infoState_766_);
lean_ctor_set(v_reuseFailAlloc_780_, 8, v_snapshotTasks_767_);
v___x_777_ = v_reuseFailAlloc_780_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = lean_st_ref_set(v___y_750_, v___x_777_);
v___x_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_779_, 0, v_r_771_);
return v___x_779_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg___boxed(lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(v___y_785_);
lean_dec(v___y_785_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v___x_793_; lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
v___x_793_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(v___y_791_);
v_a_794_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v___x_793_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_793_);
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
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5___boxed(lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(v___y_802_, v___y_803_, v___y_804_, v___y_805_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(lean_object* v_a_808_, lean_object* v_x_809_){
_start:
{
if (lean_obj_tag(v_x_809_) == 0)
{
return v_x_809_;
}
else
{
lean_object* v_key_810_; lean_object* v_value_811_; lean_object* v_tail_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_821_; 
v_key_810_ = lean_ctor_get(v_x_809_, 0);
v_value_811_ = lean_ctor_get(v_x_809_, 1);
v_tail_812_ = lean_ctor_get(v_x_809_, 2);
v_isSharedCheck_821_ = !lean_is_exclusive(v_x_809_);
if (v_isSharedCheck_821_ == 0)
{
v___x_814_ = v_x_809_;
v_isShared_815_ = v_isSharedCheck_821_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_tail_812_);
lean_inc(v_value_811_);
lean_inc(v_key_810_);
lean_dec(v_x_809_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_821_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
uint8_t v___x_816_; 
v___x_816_ = l_Lean_instBEqFVarId_beq(v_key_810_, v_a_808_);
if (v___x_816_ == 0)
{
lean_object* v___x_817_; lean_object* v___x_819_; 
v___x_817_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_808_, v_tail_812_);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 2, v___x_817_);
v___x_819_ = v___x_814_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_key_810_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v_value_811_);
lean_ctor_set(v_reuseFailAlloc_820_, 2, v___x_817_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
else
{
lean_del_object(v___x_814_);
lean_dec(v_value_811_);
lean_dec(v_key_810_);
return v_tail_812_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg___boxed(lean_object* v_a_822_, lean_object* v_x_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_822_, v_x_823_);
lean_dec(v_a_822_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(lean_object* v_m_825_, lean_object* v_a_826_){
_start:
{
lean_object* v_size_827_; lean_object* v_buckets_828_; lean_object* v___x_829_; uint64_t v___x_830_; uint64_t v___x_831_; uint64_t v___x_832_; uint64_t v_fold_833_; uint64_t v___x_834_; uint64_t v___x_835_; uint64_t v___x_836_; size_t v___x_837_; size_t v___x_838_; size_t v___x_839_; size_t v___x_840_; size_t v___x_841_; lean_object* v_bkt_842_; uint8_t v___x_843_; 
v_size_827_ = lean_ctor_get(v_m_825_, 0);
v_buckets_828_ = lean_ctor_get(v_m_825_, 1);
v___x_829_ = lean_array_get_size(v_buckets_828_);
v___x_830_ = l_Lean_instHashableFVarId_hash(v_a_826_);
v___x_831_ = 32ULL;
v___x_832_ = lean_uint64_shift_right(v___x_830_, v___x_831_);
v_fold_833_ = lean_uint64_xor(v___x_830_, v___x_832_);
v___x_834_ = 16ULL;
v___x_835_ = lean_uint64_shift_right(v_fold_833_, v___x_834_);
v___x_836_ = lean_uint64_xor(v_fold_833_, v___x_835_);
v___x_837_ = lean_uint64_to_usize(v___x_836_);
v___x_838_ = lean_usize_of_nat(v___x_829_);
v___x_839_ = ((size_t)1ULL);
v___x_840_ = lean_usize_sub(v___x_838_, v___x_839_);
v___x_841_ = lean_usize_land(v___x_837_, v___x_840_);
v_bkt_842_ = lean_array_uget_borrowed(v_buckets_828_, v___x_841_);
v___x_843_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_826_, v_bkt_842_);
if (v___x_843_ == 0)
{
return v_m_825_;
}
else
{
lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_856_; 
lean_inc(v_bkt_842_);
lean_inc_ref(v_buckets_828_);
lean_inc(v_size_827_);
v_isSharedCheck_856_ = !lean_is_exclusive(v_m_825_);
if (v_isSharedCheck_856_ == 0)
{
lean_object* v_unused_857_; lean_object* v_unused_858_; 
v_unused_857_ = lean_ctor_get(v_m_825_, 1);
lean_dec(v_unused_857_);
v_unused_858_ = lean_ctor_get(v_m_825_, 0);
lean_dec(v_unused_858_);
v___x_845_ = v_m_825_;
v_isShared_846_ = v_isSharedCheck_856_;
goto v_resetjp_844_;
}
else
{
lean_dec(v_m_825_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_856_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_847_; lean_object* v_buckets_x27_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_854_; 
v___x_847_ = lean_box(0);
v_buckets_x27_848_ = lean_array_uset(v_buckets_828_, v___x_841_, v___x_847_);
v___x_849_ = lean_unsigned_to_nat(1u);
v___x_850_ = lean_nat_sub(v_size_827_, v___x_849_);
lean_dec(v_size_827_);
v___x_851_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_826_, v_bkt_842_);
v___x_852_ = lean_array_uset(v_buckets_x27_848_, v___x_841_, v___x_851_);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 1, v___x_852_);
lean_ctor_set(v___x_845_, 0, v___x_850_);
v___x_854_ = v___x_845_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_850_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v___x_852_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg___boxed(lean_object* v_m_859_, lean_object* v_a_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v_m_859_, v_a_860_);
lean_dec(v_a_860_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(lean_object* v_a_862_, lean_object* v_fallback_863_, lean_object* v_x_864_){
_start:
{
if (lean_obj_tag(v_x_864_) == 0)
{
lean_inc(v_fallback_863_);
return v_fallback_863_;
}
else
{
lean_object* v_key_865_; lean_object* v_value_866_; lean_object* v_tail_867_; uint8_t v___x_868_; 
v_key_865_ = lean_ctor_get(v_x_864_, 0);
v_value_866_ = lean_ctor_get(v_x_864_, 1);
v_tail_867_ = lean_ctor_get(v_x_864_, 2);
v___x_868_ = l_Lean_instBEqFVarId_beq(v_key_865_, v_a_862_);
if (v___x_868_ == 0)
{
v_x_864_ = v_tail_867_;
goto _start;
}
else
{
lean_inc(v_value_866_);
return v_value_866_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg___boxed(lean_object* v_a_870_, lean_object* v_fallback_871_, lean_object* v_x_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(v_a_870_, v_fallback_871_, v_x_872_);
lean_dec(v_x_872_);
lean_dec(v_fallback_871_);
lean_dec(v_a_870_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(lean_object* v_m_874_, lean_object* v_a_875_, lean_object* v_fallback_876_){
_start:
{
lean_object* v_buckets_877_; lean_object* v___x_878_; uint64_t v___x_879_; uint64_t v___x_880_; uint64_t v___x_881_; uint64_t v_fold_882_; uint64_t v___x_883_; uint64_t v___x_884_; uint64_t v___x_885_; size_t v___x_886_; size_t v___x_887_; size_t v___x_888_; size_t v___x_889_; size_t v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v_buckets_877_ = lean_ctor_get(v_m_874_, 1);
v___x_878_ = lean_array_get_size(v_buckets_877_);
v___x_879_ = l_Lean_instHashableFVarId_hash(v_a_875_);
v___x_880_ = 32ULL;
v___x_881_ = lean_uint64_shift_right(v___x_879_, v___x_880_);
v_fold_882_ = lean_uint64_xor(v___x_879_, v___x_881_);
v___x_883_ = 16ULL;
v___x_884_ = lean_uint64_shift_right(v_fold_882_, v___x_883_);
v___x_885_ = lean_uint64_xor(v_fold_882_, v___x_884_);
v___x_886_ = lean_uint64_to_usize(v___x_885_);
v___x_887_ = lean_usize_of_nat(v___x_878_);
v___x_888_ = ((size_t)1ULL);
v___x_889_ = lean_usize_sub(v___x_887_, v___x_888_);
v___x_890_ = lean_usize_land(v___x_886_, v___x_889_);
v___x_891_ = lean_array_uget_borrowed(v_buckets_877_, v___x_890_);
v___x_892_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(v_a_875_, v_fallback_876_, v___x_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg___boxed(lean_object* v_m_893_, lean_object* v_a_894_, lean_object* v_fallback_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(v_m_893_, v_a_894_, v_fallback_895_);
lean_dec(v_fallback_895_);
lean_dec(v_a_894_);
lean_dec_ref(v_m_893_);
return v_res_896_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2(void){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_900_ = lean_box(0);
v___x_901_ = lean_unsigned_to_nat(16u);
v___x_902_ = lean_mk_array(v___x_901_, v___x_900_);
return v___x_902_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3(void){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_903_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2);
v___x_904_ = lean_unsigned_to_nat(0u);
v___x_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
lean_ctor_set(v___x_905_, 1, v___x_903_);
return v___x_905_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUses___closed__1(void){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUses___closed__0));
v___x_909_ = l_Lean_stringToMessageData(v___x_908_);
return v___x_909_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUses___closed__3(void){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUses___closed__2));
v___x_912_ = l_Lean_stringToMessageData(v___x_911_);
return v___x_912_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUses___closed__5(void){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_914_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUses___closed__4));
v___x_915_ = l_Lean_stringToMessageData(v___x_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses(lean_object* v_e_916_, lean_object* v_subst_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_){
_start:
{
switch(lean_obj_tag(v_e_916_))
{
case 0:
{
lean_object* v_deBruijnIndex_923_; lean_object* v___x_924_; uint8_t v___x_925_; 
v_deBruijnIndex_923_ = lean_ctor_get(v_e_916_, 0);
v___x_924_ = lean_array_get_size(v_subst_917_);
v___x_925_ = lean_nat_dec_lt(v_deBruijnIndex_923_, v___x_924_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
lean_inc(v_deBruijnIndex_923_);
lean_dec_ref(v_e_916_);
lean_dec_ref(v_subst_917_);
v___x_926_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__1, &l_Lean_Elab_Tactic_Do_countUses___closed__1_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__1);
v___x_927_ = l_Nat_reprFast(v_deBruijnIndex_923_);
v___x_928_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
v___x_929_ = l_Lean_MessageData_ofFormat(v___x_928_);
v___x_930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_926_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
v___x_931_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__3, &l_Lean_Elab_Tactic_Do_countUses___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__3);
v___x_932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_930_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
v___x_933_ = l_Nat_reprFast(v___x_924_);
v___x_934_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
v___x_935_ = l_Lean_MessageData_ofFormat(v___x_934_);
v___x_936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_932_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
v___x_937_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v___x_936_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
return v___x_937_;
}
else
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; uint8_t v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_938_ = lean_unsigned_to_nat(1u);
v___x_939_ = lean_nat_sub(v___x_924_, v___x_938_);
v___x_940_ = lean_nat_sub(v___x_939_, v_deBruijnIndex_923_);
lean_dec(v___x_939_);
v___x_941_ = lean_array_fget(v_subst_917_, v___x_940_);
lean_dec(v___x_940_);
lean_dec_ref(v_subst_917_);
v___x_942_ = 1;
v___x_943_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3);
v___x_944_ = lean_box(v___x_942_);
v___x_945_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(v___x_943_, v___x_941_, v___x_944_);
v___x_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_946_, 0, v_e_916_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
v___x_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
return v___x_947_;
}
}
case 1:
{
lean_object* v_fvarId_948_; uint8_t v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
lean_dec_ref(v_subst_917_);
v_fvarId_948_ = lean_ctor_get(v_e_916_, 0);
v___x_949_ = 1;
v___x_950_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3);
v___x_951_ = lean_box(v___x_949_);
lean_inc(v_fvarId_948_);
v___x_952_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(v___x_950_, v_fvarId_948_, v___x_951_);
v___x_953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_953_, 0, v_e_916_);
lean_ctor_set(v___x_953_, 1, v___x_952_);
v___x_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_954_, 0, v___x_953_);
return v___x_954_;
}
case 5:
{
lean_object* v_fn_955_; lean_object* v_arg_956_; lean_object* v___x_957_; 
v_fn_955_ = lean_ctor_get(v_e_916_, 0);
lean_inc_ref(v_fn_955_);
v_arg_956_ = lean_ctor_get(v_e_916_, 1);
lean_inc_ref(v_arg_956_);
lean_dec_ref(v_e_916_);
lean_inc_ref(v_subst_917_);
v___x_957_ = l_Lean_Elab_Tactic_Do_countUses(v_fn_955_, v_subst_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v_a_958_; lean_object* v_fst_959_; lean_object* v_snd_960_; lean_object* v___x_961_; 
v_a_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_a_958_);
lean_dec_ref(v___x_957_);
v_fst_959_ = lean_ctor_get(v_a_958_, 0);
lean_inc(v_fst_959_);
v_snd_960_ = lean_ctor_get(v_a_958_, 1);
lean_inc(v_snd_960_);
lean_dec(v_a_958_);
v___x_961_ = l_Lean_Elab_Tactic_Do_countUses(v_arg_956_, v_subst_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_980_; 
v_a_962_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_980_ == 0)
{
v___x_964_ = v___x_961_;
v_isShared_965_ = v_isSharedCheck_980_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_961_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_980_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v_fst_966_; lean_object* v_snd_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_979_; 
v_fst_966_ = lean_ctor_get(v_a_962_, 0);
v_snd_967_ = lean_ctor_get(v_a_962_, 1);
v_isSharedCheck_979_ = !lean_is_exclusive(v_a_962_);
if (v_isSharedCheck_979_ == 0)
{
v___x_969_ = v_a_962_;
v_isShared_970_ = v_isSharedCheck_979_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_snd_967_);
lean_inc(v_fst_966_);
lean_dec(v_a_962_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_979_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_974_; 
v___x_971_ = l_Lean_Expr_app___override(v_fst_959_, v_fst_966_);
v___x_972_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_snd_960_, v_snd_967_);
lean_dec(v_snd_960_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 1, v___x_972_);
lean_ctor_set(v___x_969_, 0, v___x_971_);
v___x_974_ = v___x_969_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_971_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v___x_972_);
v___x_974_ = v_reuseFailAlloc_978_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
lean_object* v___x_976_; 
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 0, v___x_974_);
v___x_976_ = v___x_964_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_974_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
}
else
{
lean_dec(v_snd_960_);
lean_dec(v_fst_959_);
return v___x_961_;
}
}
else
{
lean_dec_ref(v_arg_956_);
lean_dec_ref(v_subst_917_);
return v___x_957_;
}
}
case 6:
{
lean_object* v_binderName_981_; lean_object* v_binderType_982_; lean_object* v_body_983_; uint8_t v_binderInfo_984_; lean_object* v___x_985_; 
v_binderName_981_ = lean_ctor_get(v_e_916_, 0);
lean_inc(v_binderName_981_);
v_binderType_982_ = lean_ctor_get(v_e_916_, 1);
lean_inc_ref(v_binderType_982_);
v_body_983_ = lean_ctor_get(v_e_916_, 2);
lean_inc_ref(v_body_983_);
v_binderInfo_984_ = lean_ctor_get_uint8(v_e_916_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_916_);
v___x_985_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(v_a_918_, v_a_919_, v_a_920_, v_a_921_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v_a_986_; lean_object* v___x_987_; 
v_a_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_a_986_);
lean_dec_ref(v___x_985_);
lean_inc_ref(v_subst_917_);
v___x_987_ = l_Lean_Elab_Tactic_Do_countUses(v_binderType_982_, v_subst_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v_fst_989_; lean_object* v_snd_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_988_);
lean_dec_ref(v___x_987_);
v_fst_989_ = lean_ctor_get(v_a_988_, 0);
lean_inc(v_fst_989_);
v_snd_990_ = lean_ctor_get(v_a_988_, 1);
lean_inc(v_snd_990_);
lean_dec(v_a_988_);
lean_inc(v_a_986_);
v___x_991_ = lean_array_push(v_subst_917_, v_a_986_);
v___x_992_ = l_Lean_Elab_Tactic_Do_countUses(v_body_983_, v___x_991_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1012_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_995_ = v___x_992_;
v_isShared_996_ = v_isSharedCheck_1012_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_992_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1012_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v_fst_997_; lean_object* v_snd_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1011_; 
v_fst_997_ = lean_ctor_get(v_a_993_, 0);
v_snd_998_ = lean_ctor_get(v_a_993_, 1);
v_isSharedCheck_1011_ = !lean_is_exclusive(v_a_993_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1000_ = v_a_993_;
v_isShared_1001_ = v_isSharedCheck_1011_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_snd_998_);
lean_inc(v_fst_997_);
lean_dec(v_a_993_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1011_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1006_; 
v___x_1002_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_snd_990_, v_snd_998_);
lean_dec(v_snd_990_);
v___x_1003_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v___x_1002_, v_a_986_);
lean_dec(v_a_986_);
v___x_1004_ = l_Lean_Expr_lam___override(v_binderName_981_, v_fst_989_, v_fst_997_, v_binderInfo_984_);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 1, v___x_1003_);
lean_ctor_set(v___x_1000_, 0, v___x_1004_);
v___x_1006_ = v___x_1000_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1004_);
lean_ctor_set(v_reuseFailAlloc_1010_, 1, v___x_1003_);
v___x_1006_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
lean_object* v___x_1008_; 
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___x_1006_);
v___x_1008_ = v___x_995_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v___x_1006_);
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
}
else
{
lean_dec(v_snd_990_);
lean_dec(v_fst_989_);
lean_dec(v_a_986_);
lean_dec(v_binderName_981_);
return v___x_992_;
}
}
else
{
lean_dec(v_a_986_);
lean_dec_ref(v_body_983_);
lean_dec(v_binderName_981_);
lean_dec_ref(v_subst_917_);
return v___x_987_;
}
}
else
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
lean_dec_ref(v_body_983_);
lean_dec_ref(v_binderType_982_);
lean_dec(v_binderName_981_);
lean_dec_ref(v_subst_917_);
v_a_1013_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_985_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_985_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1013_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
case 7:
{
lean_object* v_binderName_1021_; lean_object* v_binderType_1022_; lean_object* v_body_1023_; uint8_t v_binderInfo_1024_; lean_object* v___x_1025_; 
v_binderName_1021_ = lean_ctor_get(v_e_916_, 0);
lean_inc(v_binderName_1021_);
v_binderType_1022_ = lean_ctor_get(v_e_916_, 1);
lean_inc_ref(v_binderType_1022_);
v_body_1023_ = lean_ctor_get(v_e_916_, 2);
lean_inc_ref(v_body_1023_);
v_binderInfo_1024_ = lean_ctor_get_uint8(v_e_916_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_916_);
v___x_1025_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(v_a_918_, v_a_919_, v_a_920_, v_a_921_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v___x_1027_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_a_1026_);
lean_dec_ref(v___x_1025_);
lean_inc_ref(v_subst_917_);
v___x_1027_ = l_Lean_Elab_Tactic_Do_countUses(v_binderType_1022_, v_subst_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; lean_object* v_fst_1029_; lean_object* v_snd_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
lean_inc(v_a_1028_);
lean_dec_ref(v___x_1027_);
v_fst_1029_ = lean_ctor_get(v_a_1028_, 0);
lean_inc(v_fst_1029_);
v_snd_1030_ = lean_ctor_get(v_a_1028_, 1);
lean_inc(v_snd_1030_);
lean_dec(v_a_1028_);
lean_inc(v_a_1026_);
v___x_1031_ = lean_array_push(v_subst_917_, v_a_1026_);
v___x_1032_ = l_Lean_Elab_Tactic_Do_countUses(v_body_1023_, v___x_1031_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1052_; 
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1035_ = v___x_1032_;
v_isShared_1036_ = v_isSharedCheck_1052_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_1032_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1052_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v_fst_1037_; lean_object* v_snd_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1051_; 
v_fst_1037_ = lean_ctor_get(v_a_1033_, 0);
v_snd_1038_ = lean_ctor_get(v_a_1033_, 1);
v_isSharedCheck_1051_ = !lean_is_exclusive(v_a_1033_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1040_ = v_a_1033_;
v_isShared_1041_ = v_isSharedCheck_1051_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_snd_1038_);
lean_inc(v_fst_1037_);
lean_dec(v_a_1033_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1051_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1046_; 
v___x_1042_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_snd_1030_, v_snd_1038_);
lean_dec(v_snd_1030_);
v___x_1043_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v___x_1042_, v_a_1026_);
lean_dec(v_a_1026_);
v___x_1044_ = l_Lean_Expr_forallE___override(v_binderName_1021_, v_fst_1029_, v_fst_1037_, v_binderInfo_1024_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 1, v___x_1043_);
lean_ctor_set(v___x_1040_, 0, v___x_1044_);
v___x_1046_ = v___x_1040_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v___x_1044_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v___x_1043_);
v___x_1046_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
lean_object* v___x_1048_; 
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 0, v___x_1046_);
v___x_1048_ = v___x_1035_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1046_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
}
else
{
lean_dec(v_snd_1030_);
lean_dec(v_fst_1029_);
lean_dec(v_a_1026_);
lean_dec(v_binderName_1021_);
return v___x_1032_;
}
}
else
{
lean_dec(v_a_1026_);
lean_dec_ref(v_body_1023_);
lean_dec(v_binderName_1021_);
lean_dec_ref(v_subst_917_);
return v___x_1027_;
}
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
lean_dec_ref(v_body_1023_);
lean_dec_ref(v_binderType_1022_);
lean_dec(v_binderName_1021_);
lean_dec_ref(v_subst_917_);
v_a_1053_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_1025_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1025_);
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
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
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
case 8:
{
lean_object* v_declName_1061_; lean_object* v_type_1062_; lean_object* v_value_1063_; lean_object* v_body_1064_; uint8_t v_nondep_1065_; lean_object* v___x_1066_; 
v_declName_1061_ = lean_ctor_get(v_e_916_, 0);
lean_inc(v_declName_1061_);
v_type_1062_ = lean_ctor_get(v_e_916_, 1);
lean_inc_ref(v_type_1062_);
v_value_1063_ = lean_ctor_get(v_e_916_, 2);
lean_inc_ref(v_value_1063_);
v_body_1064_ = lean_ctor_get(v_e_916_, 3);
lean_inc_ref(v_body_1064_);
v_nondep_1065_ = lean_ctor_get_uint8(v_e_916_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_916_);
v___x_1066_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(v_a_918_, v_a_919_, v_a_920_, v_a_921_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc_n(v_a_1067_, 2);
lean_dec_ref(v___x_1066_);
lean_inc_ref(v_subst_917_);
v___x_1068_ = lean_array_push(v_subst_917_, v_a_1067_);
v___x_1069_ = l_Lean_Elab_Tactic_Do_countUses(v_body_1064_, v___x_1068_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1112_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1072_ = v___x_1069_;
v_isShared_1073_ = v_isSharedCheck_1112_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1069_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1112_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v_fst_1074_; lean_object* v_snd_1075_; lean_object* v___x_1077_; 
v_fst_1074_ = lean_ctor_get(v_a_1070_, 0);
lean_inc(v_fst_1074_);
v_snd_1075_ = lean_ctor_get(v_a_1070_, 1);
lean_inc(v_snd_1075_);
lean_dec(v_a_1070_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set_tag(v___x_1072_, 1);
lean_ctor_set(v___x_1072_, 0, v_value_1063_);
v___x_1077_ = v___x_1072_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_value_1063_);
v___x_1077_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
lean_object* v___x_1078_; 
v___x_1078_ = l_Lean_Elab_Tactic_Do_countUsesDecl(v_a_1067_, v_type_1062_, v___x_1077_, v_snd_1075_, v_subst_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
lean_dec(v_a_1067_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1102_; 
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1081_ = v___x_1078_;
v_isShared_1082_ = v_isSharedCheck_1102_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1078_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1102_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v_snd_1083_; lean_object* v_fst_1084_; 
v_snd_1083_ = lean_ctor_get(v_a_1079_, 1);
lean_inc(v_snd_1083_);
v_fst_1084_ = lean_ctor_get(v_snd_1083_, 0);
lean_inc(v_fst_1084_);
if (lean_obj_tag(v_fst_1084_) == 1)
{
lean_object* v_fst_1085_; lean_object* v_snd_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1098_; 
v_fst_1085_ = lean_ctor_get(v_a_1079_, 0);
lean_inc(v_fst_1085_);
lean_dec(v_a_1079_);
v_snd_1086_ = lean_ctor_get(v_snd_1083_, 1);
v_isSharedCheck_1098_ = !lean_is_exclusive(v_snd_1083_);
if (v_isSharedCheck_1098_ == 0)
{
lean_object* v_unused_1099_; 
v_unused_1099_ = lean_ctor_get(v_snd_1083_, 0);
lean_dec(v_unused_1099_);
v___x_1088_ = v_snd_1083_;
v_isShared_1089_ = v_isSharedCheck_1098_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_snd_1086_);
lean_dec(v_snd_1083_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1098_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v_val_1090_; lean_object* v___x_1091_; lean_object* v___x_1093_; 
v_val_1090_ = lean_ctor_get(v_fst_1084_, 0);
lean_inc(v_val_1090_);
lean_dec_ref(v_fst_1084_);
v___x_1091_ = l_Lean_Expr_letE___override(v_declName_1061_, v_fst_1085_, v_val_1090_, v_fst_1074_, v_nondep_1065_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 0, v___x_1091_);
v___x_1093_ = v___x_1088_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1091_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v_snd_1086_);
v___x_1093_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
lean_object* v___x_1095_; 
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 0, v___x_1093_);
v___x_1095_ = v___x_1081_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1093_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
else
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
lean_dec(v_fst_1084_);
lean_dec(v_snd_1083_);
lean_del_object(v___x_1081_);
lean_dec(v_a_1079_);
lean_dec(v_fst_1074_);
lean_dec(v_declName_1061_);
v___x_1100_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__5, &l_Lean_Elab_Tactic_Do_countUses___closed__5_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__5);
v___x_1101_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v___x_1100_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
return v___x_1101_;
}
}
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
lean_dec(v_fst_1074_);
lean_dec(v_declName_1061_);
v_a_1103_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___x_1078_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1078_);
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
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1103_);
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
else
{
lean_dec(v_a_1067_);
lean_dec_ref(v_value_1063_);
lean_dec_ref(v_type_1062_);
lean_dec(v_declName_1061_);
lean_dec_ref(v_subst_917_);
return v___x_1069_;
}
}
else
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
lean_dec_ref(v_body_1064_);
lean_dec_ref(v_value_1063_);
lean_dec_ref(v_type_1062_);
lean_dec(v_declName_1061_);
lean_dec_ref(v_subst_917_);
v_a_1113_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1115_ = v___x_1066_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1066_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1113_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
case 10:
{
lean_object* v_data_1121_; lean_object* v_expr_1122_; lean_object* v___x_1123_; 
v_data_1121_ = lean_ctor_get(v_e_916_, 0);
lean_inc(v_data_1121_);
v_expr_1122_ = lean_ctor_get(v_e_916_, 1);
lean_inc_ref(v_expr_1122_);
lean_dec_ref(v_e_916_);
v___x_1123_ = l_Lean_Elab_Tactic_Do_countUses(v_expr_1122_, v_subst_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1133_; 
v_a_1124_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1126_ = v___x_1123_;
v_isShared_1127_ = v_isSharedCheck_1133_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_dec(v___x_1123_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1133_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___f_1128_; lean_object* v___x_1129_; lean_object* v___x_1131_; 
v___f_1128_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_countUses___lam__0), 2, 1);
lean_closure_set(v___f_1128_, 0, v_data_1121_);
v___x_1129_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v___f_1128_, v_a_1124_);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 0, v___x_1129_);
v___x_1131_ = v___x_1126_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v___x_1129_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
else
{
lean_dec(v_data_1121_);
return v___x_1123_;
}
}
case 11:
{
lean_object* v_typeName_1134_; lean_object* v_idx_1135_; lean_object* v_struct_1136_; lean_object* v___x_1137_; 
v_typeName_1134_ = lean_ctor_get(v_e_916_, 0);
lean_inc(v_typeName_1134_);
v_idx_1135_ = lean_ctor_get(v_e_916_, 1);
lean_inc(v_idx_1135_);
v_struct_1136_ = lean_ctor_get(v_e_916_, 2);
lean_inc_ref(v_struct_1136_);
lean_dec_ref(v_e_916_);
v___x_1137_ = l_Lean_Elab_Tactic_Do_countUses(v_struct_1136_, v_subst_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1147_; 
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1140_ = v___x_1137_;
v_isShared_1141_ = v_isSharedCheck_1147_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1137_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1147_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___f_1142_; lean_object* v___x_1143_; lean_object* v___x_1145_; 
v___f_1142_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_countUses___lam__1), 3, 2);
lean_closure_set(v___f_1142_, 0, v_typeName_1134_);
lean_closure_set(v___f_1142_, 1, v_idx_1135_);
v___x_1143_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v___f_1142_, v_a_1138_);
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 0, v___x_1143_);
v___x_1145_ = v___x_1140_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1143_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
else
{
lean_dec(v_idx_1135_);
lean_dec(v_typeName_1134_);
return v___x_1137_;
}
}
default: 
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
lean_dec_ref(v_subst_917_);
v___x_1148_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3);
v___x_1149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1149_, 0, v_e_916_);
lean_ctor_set(v___x_1149_, 1, v___x_1148_);
v___x_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1149_);
return v___x_1150_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl(lean_object* v_fvarId_1151_, lean_object* v_ty_1152_, lean_object* v_val_x3f_1153_, lean_object* v_bodyUses_1154_, lean_object* v_subst_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_){
_start:
{
lean_object* v___x_1161_; 
lean_inc_ref(v_subst_1155_);
v___x_1161_ = l_Lean_Elab_Tactic_Do_countUses(v_ty_1152_, v_subst_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1217_; 
v_a_1162_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1164_ = v___x_1161_;
v_isShared_1165_ = v_isSharedCheck_1217_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v___x_1161_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1217_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v_fst_1166_; lean_object* v_snd_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1216_; 
v_fst_1166_ = lean_ctor_get(v_a_1162_, 0);
v_snd_1167_ = lean_ctor_get(v_a_1162_, 1);
v_isSharedCheck_1216_ = !lean_is_exclusive(v_a_1162_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1169_ = v_a_1162_;
v_isShared_1170_ = v_isSharedCheck_1216_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_snd_1167_);
lean_inc(v_fst_1166_);
lean_dec(v_a_1162_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1216_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
uint8_t v___y_1172_; lean_object* v___y_1173_; lean_object* v___y_1174_; lean_object* v_fst_1189_; lean_object* v_snd_1190_; 
if (lean_obj_tag(v_val_x3f_1153_) == 0)
{
lean_object* v___x_1200_; 
lean_dec_ref(v_subst_1155_);
v___x_1200_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3);
v_fst_1189_ = v_val_x3f_1153_;
v_snd_1190_ = v___x_1200_;
goto v___jp_1188_;
}
else
{
lean_object* v_val_1201_; lean_object* v___x_1202_; 
v_val_1201_ = lean_ctor_get(v_val_x3f_1153_, 0);
lean_inc(v_val_1201_);
lean_dec_ref(v_val_x3f_1153_);
v___x_1202_ = l_Lean_Elab_Tactic_Do_countUses(v_val_1201_, v_subst_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v_a_1203_; lean_object* v___f_1204_; lean_object* v___x_1205_; lean_object* v_fst_1206_; lean_object* v_snd_1207_; 
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
lean_inc(v_a_1203_);
lean_dec_ref(v___x_1202_);
v___f_1204_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4));
v___x_1205_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v___f_1204_, v_a_1203_);
v_fst_1206_ = lean_ctor_get(v___x_1205_, 0);
lean_inc(v_fst_1206_);
v_snd_1207_ = lean_ctor_get(v___x_1205_, 1);
lean_inc(v_snd_1207_);
lean_dec_ref(v___x_1205_);
v_fst_1189_ = v_fst_1206_;
v_snd_1190_ = v_snd_1207_;
goto v___jp_1188_;
}
else
{
lean_object* v_a_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1215_; 
lean_del_object(v___x_1169_);
lean_dec(v_snd_1167_);
lean_dec(v_fst_1166_);
lean_del_object(v___x_1164_);
lean_dec_ref(v_bodyUses_1154_);
v_a_1208_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1210_ = v___x_1202_;
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_a_1208_);
lean_dec(v___x_1202_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
if (v_isShared_1211_ == 0)
{
v___x_1213_ = v___x_1210_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_a_1208_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
v___jp_1171_:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1182_; 
v___x_1175_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v___y_1174_, v_fvarId_1151_);
v___x_1176_ = lean_box(0);
v___x_1177_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_1178_ = l_Lean_Elab_Tactic_Do_Uses_toNat(v___y_1172_);
v___x_1179_ = l_Lean_KVMap_setNat(v___x_1176_, v___x_1177_, v___x_1178_);
v___x_1180_ = l_Lean_Elab_Tactic_Do_addMData(v___x_1179_, v_fst_1166_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 1, v___x_1175_);
lean_ctor_set(v___x_1169_, 0, v___y_1173_);
v___x_1182_ = v___x_1169_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___y_1173_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v___x_1175_);
v___x_1182_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
lean_object* v___x_1183_; lean_object* v___x_1185_; 
v___x_1183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1180_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 0, v___x_1183_);
v___x_1185_ = v___x_1164_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1183_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
v___jp_1188_:
{
uint8_t v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; uint8_t v___x_1194_; uint8_t v___x_1195_; 
v___x_1191_ = 0;
v___x_1192_ = lean_box(v___x_1191_);
v___x_1193_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(v_bodyUses_1154_, v_fvarId_1151_, v___x_1192_);
lean_dec(v___x_1192_);
v___x_1194_ = lean_unbox(v___x_1193_);
v___x_1195_ = l_Lean_Elab_Tactic_Do_instBEqUses_beq(v___x_1194_, v___x_1191_);
if (v___x_1195_ == 0)
{
lean_object* v___x_1196_; lean_object* v___x_1197_; uint8_t v___x_1198_; 
v___x_1196_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_bodyUses_1154_, v_snd_1167_);
lean_dec_ref(v_bodyUses_1154_);
v___x_1197_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v___x_1196_, v_snd_1190_);
lean_dec_ref(v___x_1196_);
v___x_1198_ = lean_unbox(v___x_1193_);
lean_dec(v___x_1193_);
v___y_1172_ = v___x_1198_;
v___y_1173_ = v_fst_1189_;
v___y_1174_ = v___x_1197_;
goto v___jp_1171_;
}
else
{
uint8_t v___x_1199_; 
lean_dec_ref(v_snd_1190_);
lean_dec(v_snd_1167_);
v___x_1199_ = lean_unbox(v___x_1193_);
lean_dec(v___x_1193_);
v___y_1172_ = v___x_1199_;
v___y_1173_ = v_fst_1189_;
v___y_1174_ = v_bodyUses_1154_;
goto v___jp_1171_;
}
}
}
}
}
else
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1225_; 
lean_dec_ref(v_subst_1155_);
lean_dec_ref(v_bodyUses_1154_);
lean_dec(v_val_x3f_1153_);
v_a_1218_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1220_ = v___x_1161_;
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1161_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1221_ == 0)
{
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1218_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___boxed(lean_object* v_fvarId_1226_, lean_object* v_ty_1227_, lean_object* v_val_x3f_1228_, lean_object* v_bodyUses_1229_, lean_object* v_subst_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Lean_Elab_Tactic_Do_countUsesDecl(v_fvarId_1226_, v_ty_1227_, v_val_x3f_1228_, v_bodyUses_1229_, v_subst_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_);
lean_dec(v_a_1234_);
lean_dec_ref(v_a_1233_);
lean_dec(v_a_1232_);
lean_dec_ref(v_a_1231_);
lean_dec(v_fvarId_1226_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses___boxed(lean_object* v_e_1237_, lean_object* v_subst_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_Lean_Elab_Tactic_Do_countUses(v_e_1237_, v_subst_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_);
lean_dec(v_a_1242_);
lean_dec_ref(v_a_1241_);
lean_dec(v_a_1240_);
lean_dec_ref(v_a_1239_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0(lean_object* v_00_u03b2_1245_, lean_object* v_m_1246_, lean_object* v_a_1247_, lean_object* v_fallback_1248_){
_start:
{
lean_object* v___x_1249_; 
v___x_1249_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(v_m_1246_, v_a_1247_, v_fallback_1248_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___boxed(lean_object* v_00_u03b2_1250_, lean_object* v_m_1251_, lean_object* v_a_1252_, lean_object* v_fallback_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0(v_00_u03b2_1250_, v_m_1251_, v_a_1252_, v_fallback_1253_);
lean_dec(v_fallback_1253_);
lean_dec(v_a_1252_);
lean_dec_ref(v_m_1251_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1(lean_object* v_00_u03b2_1255_, lean_object* v_m_1256_, lean_object* v_a_1257_){
_start:
{
lean_object* v___x_1258_; 
v___x_1258_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v_m_1256_, v_a_1257_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___boxed(lean_object* v_00_u03b2_1259_, lean_object* v_m_1260_, lean_object* v_a_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1(v_00_u03b2_1259_, v_m_1260_, v_a_1261_);
lean_dec(v_a_1261_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3(lean_object* v_00_u03b1_1263_, lean_object* v_msg_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
lean_object* v___x_1270_; 
v___x_1270_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v_msg_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___boxed(lean_object* v_00_u03b1_1271_, lean_object* v_msg_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3(v_00_u03b1_1271_, v_msg_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4(lean_object* v_00_u03b2_1279_, lean_object* v_m_1280_, lean_object* v_a_1281_, lean_object* v_b_1282_){
_start:
{
lean_object* v___x_1283_; 
v___x_1283_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(v_m_1280_, v_a_1281_, v_b_1282_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9(lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v___x_1289_; 
v___x_1289_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(v___y_1287_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___boxed(lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9(v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0(lean_object* v_00_u03b2_1296_, lean_object* v_a_1297_, lean_object* v_fallback_1298_, lean_object* v_x_1299_){
_start:
{
lean_object* v___x_1300_; 
v___x_1300_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(v_a_1297_, v_fallback_1298_, v_x_1299_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1301_, lean_object* v_a_1302_, lean_object* v_fallback_1303_, lean_object* v_x_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0(v_00_u03b2_1301_, v_a_1302_, v_fallback_1303_, v_x_1304_);
lean_dec(v_x_1304_);
lean_dec(v_fallback_1303_);
lean_dec(v_a_1302_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2(lean_object* v_00_u03b2_1306_, lean_object* v_a_1307_, lean_object* v_x_1308_){
_start:
{
lean_object* v___x_1309_; 
v___x_1309_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_1307_, v_x_1308_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1310_, lean_object* v_a_1311_, lean_object* v_x_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2(v_00_u03b2_1310_, v_a_1311_, v_x_1312_);
lean_dec(v_a_1311_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7(lean_object* v_00_u03b2_1314_, lean_object* v_a_1315_, lean_object* v_b_1316_, lean_object* v_x_1317_){
_start:
{
lean_object* v___x_1318_; 
v___x_1318_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(v_a_1315_, v_b_1316_, v_x_1317_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(lean_object* v_as_1321_, size_t v_i_1322_, size_t v_stop_1323_, lean_object* v_b_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
uint8_t v___x_1330_; 
v___x_1330_ = lean_usize_dec_eq(v_i_1322_, v_stop_1323_);
if (v___x_1330_ == 0)
{
size_t v___x_1331_; size_t v___x_1332_; lean_object* v___x_1333_; 
v___x_1331_ = ((size_t)1ULL);
v___x_1332_ = lean_usize_sub(v_i_1322_, v___x_1331_);
v___x_1333_ = lean_array_uget_borrowed(v_as_1321_, v___x_1332_);
if (lean_obj_tag(v___x_1333_) == 0)
{
v_i_1322_ = v___x_1332_;
goto _start;
}
else
{
lean_object* v_val_1335_; lean_object* v_fst_1336_; lean_object* v_snd_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v_val_1335_ = lean_ctor_get(v___x_1333_, 0);
v_fst_1336_ = lean_ctor_get(v_b_1324_, 0);
lean_inc(v_fst_1336_);
v_snd_1337_ = lean_ctor_get(v_b_1324_, 1);
lean_inc(v_snd_1337_);
lean_dec_ref(v_b_1324_);
v___x_1338_ = l_Lean_LocalDecl_fvarId(v_val_1335_);
v___x_1339_ = l_Lean_LocalDecl_type(v_val_1335_);
v___x_1340_ = l_Lean_LocalDecl_value_x3f(v_val_1335_, v___x_1330_);
v___x_1341_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0));
v___x_1342_ = l_Lean_Elab_Tactic_Do_countUsesDecl(v___x_1338_, v___x_1339_, v___x_1340_, v_snd_1337_, v___x_1341_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
lean_dec(v___x_1338_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v_a_1343_; lean_object* v_snd_1344_; lean_object* v_fst_1345_; lean_object* v_fst_1346_; lean_object* v_snd_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1362_; 
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
lean_inc(v_a_1343_);
lean_dec_ref(v___x_1342_);
v_snd_1344_ = lean_ctor_get(v_a_1343_, 1);
lean_inc(v_snd_1344_);
v_fst_1345_ = lean_ctor_get(v_a_1343_, 0);
lean_inc(v_fst_1345_);
lean_dec(v_a_1343_);
v_fst_1346_ = lean_ctor_get(v_snd_1344_, 0);
v_snd_1347_ = lean_ctor_get(v_snd_1344_, 1);
v_isSharedCheck_1362_ = !lean_is_exclusive(v_snd_1344_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1349_ = v_snd_1344_;
v_isShared_1350_ = v_isSharedCheck_1362_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_snd_1347_);
lean_inc(v_fst_1346_);
lean_dec(v_snd_1344_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1362_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___y_1352_; 
if (lean_obj_tag(v_fst_1346_) == 0)
{
lean_object* v___x_1358_; 
lean_inc(v_val_1335_);
v___x_1358_ = l_Lean_LocalDecl_setType(v_val_1335_, v_fst_1345_);
v___y_1352_ = v___x_1358_;
goto v___jp_1351_;
}
else
{
lean_object* v_val_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v_val_1359_ = lean_ctor_get(v_fst_1346_, 0);
lean_inc(v_val_1359_);
lean_dec_ref(v_fst_1346_);
lean_inc(v_val_1335_);
v___x_1360_ = l_Lean_LocalDecl_setType(v_val_1335_, v_fst_1345_);
v___x_1361_ = l_Lean_LocalDecl_setValue(v___x_1360_, v_val_1359_);
v___y_1352_ = v___x_1361_;
goto v___jp_1351_;
}
v___jp_1351_:
{
lean_object* v___x_1353_; lean_object* v___x_1355_; 
v___x_1353_ = lean_array_push(v_fst_1336_, v___y_1352_);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 0, v___x_1353_);
v___x_1355_ = v___x_1349_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v___x_1353_);
lean_ctor_set(v_reuseFailAlloc_1357_, 1, v_snd_1347_);
v___x_1355_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
v_i_1322_ = v___x_1332_;
v_b_1324_ = v___x_1355_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
lean_dec(v_fst_1336_);
v_a_1363_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1365_ = v___x_1342_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1342_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1368_; 
if (v_isShared_1366_ == 0)
{
v___x_1368_ = v___x_1365_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_a_1363_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
}
else
{
lean_object* v___x_1371_; 
v___x_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1371_, 0, v_b_1324_);
return v___x_1371_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___boxed(lean_object* v_as_1372_, lean_object* v_i_1373_, lean_object* v_stop_1374_, lean_object* v_b_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
size_t v_i_boxed_1381_; size_t v_stop_boxed_1382_; lean_object* v_res_1383_; 
v_i_boxed_1381_ = lean_unbox_usize(v_i_1373_);
lean_dec(v_i_1373_);
v_stop_boxed_1382_ = lean_unbox_usize(v_stop_1374_);
lean_dec(v_stop_1374_);
v_res_1383_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(v_as_1372_, v_i_boxed_1381_, v_stop_boxed_1382_, v_b_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec_ref(v_as_1372_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(lean_object* v_x_1384_, lean_object* v_x_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
if (lean_obj_tag(v_x_1384_) == 0)
{
lean_object* v_cs_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1404_; 
v_cs_1391_ = lean_ctor_get(v_x_1384_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v_x_1384_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1393_ = v_x_1384_;
v_isShared_1394_ = v_isSharedCheck_1404_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_cs_1391_);
lean_dec(v_x_1384_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1404_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; uint8_t v___x_1397_; 
v___x_1395_ = lean_array_get_size(v_cs_1391_);
v___x_1396_ = lean_unsigned_to_nat(0u);
v___x_1397_ = lean_nat_dec_lt(v___x_1396_, v___x_1395_);
if (v___x_1397_ == 0)
{
lean_object* v___x_1399_; 
lean_dec_ref(v_cs_1391_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 0, v_x_1385_);
v___x_1399_ = v___x_1393_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_x_1385_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
else
{
size_t v___x_1401_; size_t v___x_1402_; lean_object* v___x_1403_; 
lean_del_object(v___x_1393_);
v___x_1401_ = lean_usize_of_nat(v___x_1395_);
v___x_1402_ = ((size_t)0ULL);
v___x_1403_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(v_cs_1391_, v___x_1401_, v___x_1402_, v_x_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
lean_dec_ref(v_cs_1391_);
return v___x_1403_;
}
}
}
else
{
lean_object* v_vs_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1418_; 
v_vs_1405_ = lean_ctor_get(v_x_1384_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v_x_1384_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1407_ = v_x_1384_;
v_isShared_1408_ = v_isSharedCheck_1418_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_vs_1405_);
lean_dec(v_x_1384_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1418_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; uint8_t v___x_1411_; 
v___x_1409_ = lean_array_get_size(v_vs_1405_);
v___x_1410_ = lean_unsigned_to_nat(0u);
v___x_1411_ = lean_nat_dec_lt(v___x_1410_, v___x_1409_);
if (v___x_1411_ == 0)
{
lean_object* v___x_1413_; 
lean_dec_ref(v_vs_1405_);
if (v_isShared_1408_ == 0)
{
lean_ctor_set_tag(v___x_1407_, 0);
lean_ctor_set(v___x_1407_, 0, v_x_1385_);
v___x_1413_ = v___x_1407_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_x_1385_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
else
{
size_t v___x_1415_; size_t v___x_1416_; lean_object* v___x_1417_; 
lean_del_object(v___x_1407_);
v___x_1415_ = lean_usize_of_nat(v___x_1409_);
v___x_1416_ = ((size_t)0ULL);
v___x_1417_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(v_vs_1405_, v___x_1415_, v___x_1416_, v_x_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
lean_dec_ref(v_vs_1405_);
return v___x_1417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(lean_object* v_as_1419_, size_t v_i_1420_, size_t v_stop_1421_, lean_object* v_b_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
uint8_t v___x_1428_; 
v___x_1428_ = lean_usize_dec_eq(v_i_1420_, v_stop_1421_);
if (v___x_1428_ == 0)
{
size_t v___x_1429_; size_t v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1429_ = ((size_t)1ULL);
v___x_1430_ = lean_usize_sub(v_i_1420_, v___x_1429_);
v___x_1431_ = lean_array_uget_borrowed(v_as_1419_, v___x_1430_);
lean_inc(v___x_1431_);
v___x_1432_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v___x_1431_, v_b_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v_a_1433_; 
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_a_1433_);
lean_dec_ref(v___x_1432_);
v_i_1420_ = v___x_1430_;
v_b_1422_ = v_a_1433_;
goto _start;
}
else
{
return v___x_1432_;
}
}
else
{
lean_object* v___x_1435_; 
v___x_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1435_, 0, v_b_1422_);
return v___x_1435_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_as_1436_, lean_object* v_i_1437_, lean_object* v_stop_1438_, lean_object* v_b_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
size_t v_i_boxed_1445_; size_t v_stop_boxed_1446_; lean_object* v_res_1447_; 
v_i_boxed_1445_ = lean_unbox_usize(v_i_1437_);
lean_dec(v_i_1437_);
v_stop_boxed_1446_ = lean_unbox_usize(v_stop_1438_);
lean_dec(v_stop_1438_);
v_res_1447_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(v_as_1436_, v_i_boxed_1445_, v_stop_boxed_1446_, v_b_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec_ref(v_as_1436_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1___boxed(lean_object* v_x_1448_, lean_object* v_x_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v_x_1448_, v_x_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(lean_object* v_t_1456_, lean_object* v_init_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v_root_1463_; lean_object* v_tail_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; uint8_t v___x_1467_; 
v_root_1463_ = lean_ctor_get(v_t_1456_, 0);
lean_inc_ref(v_root_1463_);
v_tail_1464_ = lean_ctor_get(v_t_1456_, 1);
lean_inc_ref(v_tail_1464_);
lean_dec_ref(v_t_1456_);
v___x_1465_ = lean_array_get_size(v_tail_1464_);
v___x_1466_ = lean_unsigned_to_nat(0u);
v___x_1467_ = lean_nat_dec_lt(v___x_1466_, v___x_1465_);
if (v___x_1467_ == 0)
{
lean_object* v___x_1468_; 
lean_dec_ref(v_tail_1464_);
v___x_1468_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v_root_1463_, v_init_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
return v___x_1468_;
}
else
{
size_t v___x_1469_; size_t v___x_1470_; lean_object* v___x_1471_; 
v___x_1469_ = lean_usize_of_nat(v___x_1465_);
v___x_1470_ = ((size_t)0ULL);
v___x_1471_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(v_tail_1464_, v___x_1469_, v___x_1470_, v_init_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
lean_dec_ref(v_tail_1464_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_object* v_a_1472_; lean_object* v___x_1473_; 
v_a_1472_ = lean_ctor_get(v___x_1471_, 0);
lean_inc(v_a_1472_);
lean_dec_ref(v___x_1471_);
v___x_1473_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v_root_1463_, v_a_1472_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
return v___x_1473_;
}
else
{
lean_dec_ref(v_root_1463_);
return v___x_1471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0___boxed(lean_object* v_t_1474_, lean_object* v_init_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(v_t_1474_, v_init_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(lean_object* v_lctx_1482_, lean_object* v_init_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
lean_object* v_decls_1489_; lean_object* v___x_1490_; 
v_decls_1489_ = lean_ctor_get(v_lctx_1482_, 1);
lean_inc_ref(v_decls_1489_);
lean_dec_ref(v_lctx_1482_);
v___x_1490_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(v_decls_1489_, v_init_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0___boxed(lean_object* v_lctx_1491_, lean_object* v_init_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(v_lctx_1491_, v_init_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(size_t v_sz_1499_, size_t v_i_1500_, lean_object* v_bs_1501_, lean_object* v___y_1502_){
_start:
{
uint8_t v___x_1504_; 
v___x_1504_ = lean_usize_dec_lt(v_i_1500_, v_sz_1499_);
if (v___x_1504_ == 0)
{
lean_object* v___x_1505_; 
v___x_1505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1505_, 0, v_bs_1501_);
return v___x_1505_;
}
else
{
lean_object* v_v_1506_; lean_object* v___x_1507_; lean_object* v_bs_x27_1508_; lean_object* v_a_1510_; 
v_v_1506_ = lean_array_uget(v_bs_1501_, v_i_1500_);
v___x_1507_ = lean_unsigned_to_nat(0u);
v_bs_x27_1508_ = lean_array_uset(v_bs_1501_, v_i_1500_, v___x_1507_);
if (lean_obj_tag(v_v_1506_) == 0)
{
v_a_1510_ = v_v_1506_;
goto v___jp_1509_;
}
else
{
lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1529_; 
v_isSharedCheck_1529_ = !lean_is_exclusive(v_v_1506_);
if (v_isSharedCheck_1529_ == 0)
{
lean_object* v_unused_1530_; 
v_unused_1530_ = lean_ctor_get(v_v_1506_, 0);
lean_dec(v_unused_1530_);
v___x_1516_ = v_v_1506_;
v_isShared_1517_ = v_isSharedCheck_1529_;
goto v_resetjp_1515_;
}
else
{
lean_dec(v_v_1506_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1529_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1527_; 
v___x_1518_ = lean_st_ref_take(v___y_1502_);
v___x_1519_ = l_Lean_instInhabitedLocalDecl_default;
v___x_1520_ = lean_array_get_size(v___x_1518_);
v___x_1521_ = lean_unsigned_to_nat(1u);
v___x_1522_ = lean_nat_sub(v___x_1520_, v___x_1521_);
v___x_1523_ = lean_array_get(v___x_1519_, v___x_1518_, v___x_1522_);
lean_dec(v___x_1522_);
v___x_1524_ = lean_array_pop(v___x_1518_);
v___x_1525_ = lean_st_ref_set(v___y_1502_, v___x_1524_);
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 0, v___x_1523_);
v___x_1527_ = v___x_1516_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1523_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
v_a_1510_ = v___x_1527_;
goto v___jp_1509_;
}
}
}
v___jp_1509_:
{
size_t v___x_1511_; size_t v___x_1512_; lean_object* v___x_1513_; 
v___x_1511_ = ((size_t)1ULL);
v___x_1512_ = lean_usize_add(v_i_1500_, v___x_1511_);
v___x_1513_ = lean_array_uset(v_bs_x27_1508_, v_i_1500_, v_a_1510_);
v_i_1500_ = v___x_1512_;
v_bs_1501_ = v___x_1513_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg___boxed(lean_object* v_sz_1531_, lean_object* v_i_1532_, lean_object* v_bs_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
size_t v_sz_boxed_1536_; size_t v_i_boxed_1537_; lean_object* v_res_1538_; 
v_sz_boxed_1536_ = lean_unbox_usize(v_sz_1531_);
lean_dec(v_sz_1531_);
v_i_boxed_1537_ = lean_unbox_usize(v_i_1532_);
lean_dec(v_i_1532_);
v_res_1538_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_boxed_1536_, v_i_boxed_1537_, v_bs_1533_, v___y_1534_);
lean_dec(v___y_1534_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(lean_object* v_x_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
if (lean_obj_tag(v_x_1539_) == 0)
{
lean_object* v_cs_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1572_; 
v_cs_1546_ = lean_ctor_get(v_x_1539_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v_x_1539_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1548_ = v_x_1539_;
v_isShared_1549_ = v_isSharedCheck_1572_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_cs_1546_);
lean_dec(v_x_1539_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1572_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
size_t v_sz_1550_; size_t v___x_1551_; lean_object* v___x_1552_; 
v_sz_1550_ = lean_array_size(v_cs_1546_);
v___x_1551_ = ((size_t)0ULL);
v___x_1552_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(v_sz_1550_, v___x_1551_, v_cs_1546_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1563_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1555_ = v___x_1552_;
v_isShared_1556_ = v_isSharedCheck_1563_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1552_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1563_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 0, v_a_1553_);
v___x_1558_ = v___x_1548_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1553_);
v___x_1558_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
lean_object* v___x_1560_; 
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 0, v___x_1558_);
v___x_1560_ = v___x_1555_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v___x_1558_);
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
else
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
lean_del_object(v___x_1548_);
v_a_1564_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v___x_1552_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1552_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1564_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
}
else
{
lean_object* v_vs_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1599_; 
v_vs_1573_ = lean_ctor_get(v_x_1539_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v_x_1539_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1575_ = v_x_1539_;
v_isShared_1576_ = v_isSharedCheck_1599_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_vs_1573_);
lean_dec(v_x_1539_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1599_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
size_t v_sz_1577_; size_t v___x_1578_; lean_object* v___x_1579_; 
v_sz_1577_ = lean_array_size(v_vs_1573_);
v___x_1578_ = ((size_t)0ULL);
v___x_1579_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_1577_, v___x_1578_, v_vs_1573_, v___y_1540_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1590_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1582_ = v___x_1579_;
v_isShared_1583_ = v_isSharedCheck_1590_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1579_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1590_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 0, v_a_1580_);
v___x_1585_ = v___x_1575_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_a_1580_);
v___x_1585_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
lean_object* v___x_1587_; 
if (v_isShared_1583_ == 0)
{
lean_ctor_set(v___x_1582_, 0, v___x_1585_);
v___x_1587_ = v___x_1582_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v___x_1585_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
else
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1598_; 
lean_del_object(v___x_1575_);
v_a_1591_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1593_ = v___x_1579_;
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1579_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1596_; 
if (v_isShared_1594_ == 0)
{
v___x_1596_ = v___x_1593_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1591_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(size_t v_sz_1600_, size_t v_i_1601_, lean_object* v_bs_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
uint8_t v___x_1609_; 
v___x_1609_ = lean_usize_dec_lt(v_i_1601_, v_sz_1600_);
if (v___x_1609_ == 0)
{
lean_object* v___x_1610_; 
v___x_1610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1610_, 0, v_bs_1602_);
return v___x_1610_;
}
else
{
lean_object* v_v_1611_; lean_object* v___x_1612_; 
v_v_1611_ = lean_array_uget_borrowed(v_bs_1602_, v_i_1601_);
lean_inc(v_v_1611_);
v___x_1612_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(v_v_1611_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_object* v_a_1613_; lean_object* v___x_1614_; lean_object* v_bs_x27_1615_; size_t v___x_1616_; size_t v___x_1617_; lean_object* v___x_1618_; 
v_a_1613_ = lean_ctor_get(v___x_1612_, 0);
lean_inc(v_a_1613_);
lean_dec_ref(v___x_1612_);
v___x_1614_ = lean_unsigned_to_nat(0u);
v_bs_x27_1615_ = lean_array_uset(v_bs_1602_, v_i_1601_, v___x_1614_);
v___x_1616_ = ((size_t)1ULL);
v___x_1617_ = lean_usize_add(v_i_1601_, v___x_1616_);
v___x_1618_ = lean_array_uset(v_bs_x27_1615_, v_i_1601_, v_a_1613_);
v_i_1601_ = v___x_1617_;
v_bs_1602_ = v___x_1618_;
goto _start;
}
else
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
lean_dec_ref(v_bs_1602_);
v_a_1620_ = lean_ctor_get(v___x_1612_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v___x_1612_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1612_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5___boxed(lean_object* v_sz_1628_, lean_object* v_i_1629_, lean_object* v_bs_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
size_t v_sz_boxed_1637_; size_t v_i_boxed_1638_; lean_object* v_res_1639_; 
v_sz_boxed_1637_ = lean_unbox_usize(v_sz_1628_);
lean_dec(v_sz_1628_);
v_i_boxed_1638_ = lean_unbox_usize(v_i_1629_);
lean_dec(v_i_1629_);
v_res_1639_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(v_sz_boxed_1637_, v_i_boxed_1638_, v_bs_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec(v___y_1631_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2___boxed(lean_object* v_x_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(v_x_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v___y_1641_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(lean_object* v_t_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
lean_object* v_root_1655_; lean_object* v_tail_1656_; lean_object* v_size_1657_; size_t v_shift_1658_; lean_object* v_tailOff_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1695_; 
v_root_1655_ = lean_ctor_get(v_t_1648_, 0);
v_tail_1656_ = lean_ctor_get(v_t_1648_, 1);
v_size_1657_ = lean_ctor_get(v_t_1648_, 2);
v_shift_1658_ = lean_ctor_get_usize(v_t_1648_, 4);
v_tailOff_1659_ = lean_ctor_get(v_t_1648_, 3);
v_isSharedCheck_1695_ = !lean_is_exclusive(v_t_1648_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1661_ = v_t_1648_;
v_isShared_1662_ = v_isSharedCheck_1695_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_tailOff_1659_);
lean_inc(v_size_1657_);
lean_inc(v_tail_1656_);
lean_inc(v_root_1655_);
lean_dec(v_t_1648_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1695_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1663_; 
v___x_1663_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(v_root_1655_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v_a_1664_; size_t v_sz_1665_; size_t v___x_1666_; lean_object* v___x_1667_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_a_1664_);
lean_dec_ref(v___x_1663_);
v_sz_1665_ = lean_array_size(v_tail_1656_);
v___x_1666_ = ((size_t)0ULL);
v___x_1667_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_1665_, v___x_1666_, v_tail_1656_, v___y_1649_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1678_; 
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1670_ = v___x_1667_;
v_isShared_1671_ = v_isSharedCheck_1678_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1667_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1678_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1662_ == 0)
{
lean_ctor_set(v___x_1661_, 1, v_a_1668_);
lean_ctor_set(v___x_1661_, 0, v_a_1664_);
v___x_1673_ = v___x_1661_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_a_1664_);
lean_ctor_set(v_reuseFailAlloc_1677_, 1, v_a_1668_);
lean_ctor_set(v_reuseFailAlloc_1677_, 2, v_size_1657_);
lean_ctor_set(v_reuseFailAlloc_1677_, 3, v_tailOff_1659_);
lean_ctor_set_usize(v_reuseFailAlloc_1677_, 4, v_shift_1658_);
v___x_1673_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
lean_object* v___x_1675_; 
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 0, v___x_1673_);
v___x_1675_ = v___x_1670_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1673_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
else
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
lean_dec(v_a_1664_);
lean_del_object(v___x_1661_);
lean_dec(v_tailOff_1659_);
lean_dec(v_size_1657_);
v_a_1679_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v___x_1667_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1667_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_a_1679_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
}
else
{
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1694_; 
lean_del_object(v___x_1661_);
lean_dec(v_tailOff_1659_);
lean_dec(v_size_1657_);
lean_dec_ref(v_tail_1656_);
v_a_1687_ = lean_ctor_get(v___x_1663_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1689_ = v___x_1663_;
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___x_1663_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1692_; 
if (v_isShared_1690_ == 0)
{
v___x_1692_ = v___x_1689_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_a_1687_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1___boxed(lean_object* v_t_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(v_t_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v___y_1697_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesLCtx(lean_object* v_ctx_1704_, lean_object* v_targetUses_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_){
_start:
{
lean_object* v_decls_1711_; lean_object* v_fvarIdToDecl_1712_; lean_object* v_auxDeclToFullName_1713_; lean_object* v_size_1714_; lean_object* v_decls_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
v_decls_1711_ = lean_ctor_get(v_ctx_1704_, 1);
lean_inc_ref(v_decls_1711_);
v_fvarIdToDecl_1712_ = lean_ctor_get(v_ctx_1704_, 0);
lean_inc_ref(v_fvarIdToDecl_1712_);
v_auxDeclToFullName_1713_ = lean_ctor_get(v_ctx_1704_, 2);
lean_inc(v_auxDeclToFullName_1713_);
v_size_1714_ = lean_ctor_get(v_decls_1711_, 2);
v_decls_1715_ = lean_mk_empty_array_with_capacity(v_size_1714_);
v___x_1716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1716_, 0, v_decls_1715_);
lean_ctor_set(v___x_1716_, 1, v_targetUses_1705_);
v___x_1717_ = l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(v_ctx_1704_, v___x_1716_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v_a_1718_; lean_object* v_fst_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
lean_inc(v_a_1718_);
lean_dec_ref(v___x_1717_);
v_fst_1719_ = lean_ctor_get(v_a_1718_, 0);
lean_inc(v_fst_1719_);
lean_dec(v_a_1718_);
v___x_1720_ = lean_st_mk_ref(v_fst_1719_);
v___x_1721_ = l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(v_decls_1711_, v___x_1720_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1731_; 
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1724_ = v___x_1721_;
v_isShared_1725_ = v_isSharedCheck_1731_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v___x_1721_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1731_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1729_; 
v___x_1726_ = lean_st_ref_get(v___x_1720_);
lean_dec(v___x_1720_);
lean_dec(v___x_1726_);
v___x_1727_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1727_, 0, v_fvarIdToDecl_1712_);
lean_ctor_set(v___x_1727_, 1, v_a_1722_);
lean_ctor_set(v___x_1727_, 2, v_auxDeclToFullName_1713_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 0, v___x_1727_);
v___x_1729_ = v___x_1724_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___x_1727_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
else
{
lean_object* v_a_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1739_; 
lean_dec(v___x_1720_);
lean_dec(v_auxDeclToFullName_1713_);
lean_dec_ref(v_fvarIdToDecl_1712_);
v_a_1732_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1734_ = v___x_1721_;
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_a_1732_);
lean_dec(v___x_1721_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1737_; 
if (v_isShared_1735_ == 0)
{
v___x_1737_ = v___x_1734_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_a_1732_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
}
else
{
lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1747_; 
lean_dec(v_auxDeclToFullName_1713_);
lean_dec_ref(v_fvarIdToDecl_1712_);
lean_dec_ref(v_decls_1711_);
v_a_1740_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1742_ = v___x_1717_;
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_dec(v___x_1717_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1745_; 
if (v_isShared_1743_ == 0)
{
v___x_1745_ = v___x_1742_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_a_1740_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesLCtx___boxed(lean_object* v_ctx_1748_, lean_object* v_targetUses_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Lean_Elab_Tactic_Do_countUsesLCtx(v_ctx_1748_, v_targetUses_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_);
lean_dec(v_a_1753_);
lean_dec_ref(v_a_1752_);
lean_dec(v_a_1751_);
lean_dec_ref(v_a_1750_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3(size_t v_sz_1756_, size_t v_i_1757_, lean_object* v_bs_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
lean_object* v___x_1765_; 
v___x_1765_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_1756_, v_i_1757_, v_bs_1758_, v___y_1759_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___boxed(lean_object* v_sz_1766_, lean_object* v_i_1767_, lean_object* v_bs_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
size_t v_sz_boxed_1775_; size_t v_i_boxed_1776_; lean_object* v_res_1777_; 
v_sz_boxed_1775_ = lean_unbox_usize(v_sz_1766_);
lean_dec(v_sz_1766_);
v_i_boxed_1776_ = lean_unbox_usize(v_i_1767_);
lean_dec(v_i_1767_);
v_res_1777_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3(v_sz_boxed_1775_, v_i_boxed_1776_, v_bs_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v___y_1769_);
return v_res_1777_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_doNotDup(uint8_t v_u_1778_, lean_object* v_rhs_1779_, uint8_t v_elimTrivial_1780_){
_start:
{
uint8_t v___x_1781_; uint8_t v___x_1782_; 
v___x_1781_ = 2;
v___x_1782_ = l_Lean_Elab_Tactic_Do_instBEqUses_beq(v_u_1778_, v___x_1781_);
if (v___x_1782_ == 0)
{
return v___x_1782_;
}
else
{
if (v_elimTrivial_1780_ == 0)
{
return v___x_1782_;
}
else
{
uint8_t v___x_1783_; 
v___x_1783_ = l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup(v_rhs_1779_);
if (v___x_1783_ == 0)
{
return v___x_1782_;
}
else
{
uint8_t v___x_1784_; 
v___x_1784_ = 0;
return v___x_1784_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_doNotDup___boxed(lean_object* v_u_1785_, lean_object* v_rhs_1786_, lean_object* v_elimTrivial_1787_){
_start:
{
uint8_t v_u_boxed_1788_; uint8_t v_elimTrivial_boxed_1789_; uint8_t v_res_1790_; lean_object* v_r_1791_; 
v_u_boxed_1788_ = lean_unbox(v_u_1785_);
v_elimTrivial_boxed_1789_ = lean_unbox(v_elimTrivial_1787_);
v_res_1790_ = l_Lean_Elab_Tactic_Do_doNotDup(v_u_boxed_1788_, v_rhs_1786_, v_elimTrivial_boxed_1789_);
lean_dec_ref(v_rhs_1786_);
v_r_1791_ = lean_box(v_res_1790_);
return v_r_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0(uint8_t v_elimTrivial_1794_, lean_object* v_e_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
if (lean_obj_tag(v_e_1795_) == 8)
{
lean_object* v_type_1802_; 
v_type_1802_ = lean_ctor_get(v_e_1795_, 1);
if (lean_obj_tag(v_type_1802_) == 10)
{
lean_object* v_value_1803_; lean_object* v_body_1804_; lean_object* v_data_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; uint8_t v_uses_1809_; uint8_t v___x_1810_; 
v_value_1803_ = lean_ctor_get(v_e_1795_, 2);
v_body_1804_ = lean_ctor_get(v_e_1795_, 3);
v_data_1805_ = lean_ctor_get(v_type_1802_, 0);
v___x_1806_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_1807_ = lean_unsigned_to_nat(2u);
v___x_1808_ = l_Lean_KVMap_getNat(v_data_1805_, v___x_1806_, v___x_1807_);
v_uses_1809_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_1808_);
lean_dec(v___x_1808_);
v___x_1810_ = l_Lean_Elab_Tactic_Do_doNotDup(v_uses_1809_, v_value_1803_, v_elimTrivial_1794_);
if (v___x_1810_ == 0)
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1811_ = lean_expr_instantiate1(v_body_1804_, v_value_1803_);
v___x_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1811_);
v___x_1813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1812_);
return v___x_1813_;
}
else
{
lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1814_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0));
v___x_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1814_);
return v___x_1815_;
}
}
else
{
lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1816_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0));
v___x_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1816_);
return v___x_1817_;
}
}
else
{
lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1818_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0));
v___x_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1818_);
return v___x_1819_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___boxed(lean_object* v_elimTrivial_1820_, lean_object* v_e_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
uint8_t v_elimTrivial_boxed_1828_; lean_object* v_res_1829_; 
v_elimTrivial_boxed_1828_ = lean_unbox(v_elimTrivial_1820_);
v_res_1829_ = l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0(v_elimTrivial_boxed_1828_, v_e_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
lean_dec(v___y_1822_);
lean_dec_ref(v_e_1821_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1(lean_object* v_e_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_){
_start:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1837_, 0, v_e_1830_);
v___x_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1837_);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1___boxed(lean_object* v_e_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_){
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1(v_e_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
lean_dec(v___y_1840_);
return v_res_1846_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1852_ = l_Lean_maxRecDepthErrorMessage;
v___x_1853_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1852_);
return v___x_1853_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4(void){
_start:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1854_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3);
v___x_1855_ = l_Lean_MessageData_ofFormat(v___x_1854_);
return v___x_1855_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1856_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4);
v___x_1857_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2));
v___x_1858_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1857_);
lean_ctor_set(v___x_1858_, 1, v___x_1856_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(lean_object* v_ref_1859_){
_start:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1861_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5);
v___x_1862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1862_, 0, v_ref_1859_);
lean_ctor_set(v___x_1862_, 1, v___x_1861_);
v___x_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1862_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___boxed(lean_object* v_ref_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_1864_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(lean_object* v_x_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v___y_1876_; lean_object* v_fileName_1885_; lean_object* v_fileMap_1886_; lean_object* v_options_1887_; lean_object* v_currRecDepth_1888_; lean_object* v_maxRecDepth_1889_; lean_object* v_ref_1890_; lean_object* v_currNamespace_1891_; lean_object* v_openDecls_1892_; lean_object* v_initHeartbeats_1893_; lean_object* v_maxHeartbeats_1894_; lean_object* v_quotContext_1895_; lean_object* v_currMacroScope_1896_; uint8_t v_diag_1897_; lean_object* v_cancelTk_x3f_1898_; uint8_t v_suppressElabErrors_1899_; lean_object* v_inheritedTraceOptions_1900_; lean_object* v___x_1906_; uint8_t v___x_1907_; 
v_fileName_1885_ = lean_ctor_get(v___y_1872_, 0);
v_fileMap_1886_ = lean_ctor_get(v___y_1872_, 1);
v_options_1887_ = lean_ctor_get(v___y_1872_, 2);
v_currRecDepth_1888_ = lean_ctor_get(v___y_1872_, 3);
v_maxRecDepth_1889_ = lean_ctor_get(v___y_1872_, 4);
v_ref_1890_ = lean_ctor_get(v___y_1872_, 5);
v_currNamespace_1891_ = lean_ctor_get(v___y_1872_, 6);
v_openDecls_1892_ = lean_ctor_get(v___y_1872_, 7);
v_initHeartbeats_1893_ = lean_ctor_get(v___y_1872_, 8);
v_maxHeartbeats_1894_ = lean_ctor_get(v___y_1872_, 9);
v_quotContext_1895_ = lean_ctor_get(v___y_1872_, 10);
v_currMacroScope_1896_ = lean_ctor_get(v___y_1872_, 11);
v_diag_1897_ = lean_ctor_get_uint8(v___y_1872_, sizeof(void*)*14);
v_cancelTk_x3f_1898_ = lean_ctor_get(v___y_1872_, 12);
v_suppressElabErrors_1899_ = lean_ctor_get_uint8(v___y_1872_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1900_ = lean_ctor_get(v___y_1872_, 13);
v___x_1906_ = lean_unsigned_to_nat(0u);
v___x_1907_ = lean_nat_dec_eq(v_maxRecDepth_1889_, v___x_1906_);
if (v___x_1907_ == 0)
{
uint8_t v___x_1908_; 
v___x_1908_ = lean_nat_dec_eq(v_currRecDepth_1888_, v_maxRecDepth_1889_);
if (v___x_1908_ == 0)
{
goto v___jp_1901_;
}
else
{
lean_object* v___x_1909_; 
lean_dec_ref(v_x_1867_);
lean_inc(v_ref_1890_);
v___x_1909_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_1890_);
v___y_1876_ = v___x_1909_;
goto v___jp_1875_;
}
}
else
{
goto v___jp_1901_;
}
v___jp_1875_:
{
if (lean_obj_tag(v___y_1876_) == 0)
{
return v___y_1876_;
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
v_a_1877_ = lean_ctor_get(v___y_1876_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___y_1876_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___y_1876_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___y_1876_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
v___jp_1901_:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1902_ = lean_unsigned_to_nat(1u);
v___x_1903_ = lean_nat_add(v_currRecDepth_1888_, v___x_1902_);
lean_inc_ref(v_inheritedTraceOptions_1900_);
lean_inc(v_cancelTk_x3f_1898_);
lean_inc(v_currMacroScope_1896_);
lean_inc(v_quotContext_1895_);
lean_inc(v_maxHeartbeats_1894_);
lean_inc(v_initHeartbeats_1893_);
lean_inc(v_openDecls_1892_);
lean_inc(v_currNamespace_1891_);
lean_inc(v_ref_1890_);
lean_inc(v_maxRecDepth_1889_);
lean_inc_ref(v_options_1887_);
lean_inc_ref(v_fileMap_1886_);
lean_inc_ref(v_fileName_1885_);
v___x_1904_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1904_, 0, v_fileName_1885_);
lean_ctor_set(v___x_1904_, 1, v_fileMap_1886_);
lean_ctor_set(v___x_1904_, 2, v_options_1887_);
lean_ctor_set(v___x_1904_, 3, v___x_1903_);
lean_ctor_set(v___x_1904_, 4, v_maxRecDepth_1889_);
lean_ctor_set(v___x_1904_, 5, v_ref_1890_);
lean_ctor_set(v___x_1904_, 6, v_currNamespace_1891_);
lean_ctor_set(v___x_1904_, 7, v_openDecls_1892_);
lean_ctor_set(v___x_1904_, 8, v_initHeartbeats_1893_);
lean_ctor_set(v___x_1904_, 9, v_maxHeartbeats_1894_);
lean_ctor_set(v___x_1904_, 10, v_quotContext_1895_);
lean_ctor_set(v___x_1904_, 11, v_currMacroScope_1896_);
lean_ctor_set(v___x_1904_, 12, v_cancelTk_x3f_1898_);
lean_ctor_set(v___x_1904_, 13, v_inheritedTraceOptions_1900_);
lean_ctor_set_uint8(v___x_1904_, sizeof(void*)*14, v_diag_1897_);
lean_ctor_set_uint8(v___x_1904_, sizeof(void*)*14 + 1, v_suppressElabErrors_1899_);
lean_inc(v___y_1873_);
lean_inc(v___y_1871_);
lean_inc_ref(v___y_1870_);
lean_inc(v___y_1869_);
lean_inc(v___y_1868_);
v___x_1905_ = lean_apply_7(v_x_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___x_1904_, v___y_1873_, lean_box(0));
v___y_1876_ = v___x_1905_;
goto v___jp_1875_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg___boxed(lean_object* v_x_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v_x_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
lean_dec(v___y_1916_);
lean_dec_ref(v___y_1915_);
lean_dec(v___y_1914_);
lean_dec_ref(v___y_1913_);
lean_dec(v___y_1912_);
lean_dec(v___y_1911_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(lean_object* v_a_1919_, lean_object* v_x_1920_){
_start:
{
if (lean_obj_tag(v_x_1920_) == 0)
{
lean_object* v___x_1921_; 
v___x_1921_ = lean_box(0);
return v___x_1921_;
}
else
{
lean_object* v_key_1922_; lean_object* v_value_1923_; lean_object* v_tail_1924_; uint8_t v___x_1925_; 
v_key_1922_ = lean_ctor_get(v_x_1920_, 0);
v_value_1923_ = lean_ctor_get(v_x_1920_, 1);
v_tail_1924_ = lean_ctor_get(v_x_1920_, 2);
v___x_1925_ = l_Lean_ExprStructEq_beq(v_key_1922_, v_a_1919_);
if (v___x_1925_ == 0)
{
v_x_1920_ = v_tail_1924_;
goto _start;
}
else
{
lean_object* v___x_1927_; 
lean_inc(v_value_1923_);
v___x_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1927_, 0, v_value_1923_);
return v___x_1927_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg___boxed(lean_object* v_a_1928_, lean_object* v_x_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(v_a_1928_, v_x_1929_);
lean_dec(v_x_1929_);
lean_dec_ref(v_a_1928_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(lean_object* v_m_1931_, lean_object* v_a_1932_){
_start:
{
lean_object* v_buckets_1933_; lean_object* v___x_1934_; uint64_t v___x_1935_; uint64_t v___x_1936_; uint64_t v___x_1937_; uint64_t v_fold_1938_; uint64_t v___x_1939_; uint64_t v___x_1940_; uint64_t v___x_1941_; size_t v___x_1942_; size_t v___x_1943_; size_t v___x_1944_; size_t v___x_1945_; size_t v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
v_buckets_1933_ = lean_ctor_get(v_m_1931_, 1);
v___x_1934_ = lean_array_get_size(v_buckets_1933_);
v___x_1935_ = l_Lean_ExprStructEq_hash(v_a_1932_);
v___x_1936_ = 32ULL;
v___x_1937_ = lean_uint64_shift_right(v___x_1935_, v___x_1936_);
v_fold_1938_ = lean_uint64_xor(v___x_1935_, v___x_1937_);
v___x_1939_ = 16ULL;
v___x_1940_ = lean_uint64_shift_right(v_fold_1938_, v___x_1939_);
v___x_1941_ = lean_uint64_xor(v_fold_1938_, v___x_1940_);
v___x_1942_ = lean_uint64_to_usize(v___x_1941_);
v___x_1943_ = lean_usize_of_nat(v___x_1934_);
v___x_1944_ = ((size_t)1ULL);
v___x_1945_ = lean_usize_sub(v___x_1943_, v___x_1944_);
v___x_1946_ = lean_usize_land(v___x_1942_, v___x_1945_);
v___x_1947_ = lean_array_uget_borrowed(v_buckets_1933_, v___x_1946_);
v___x_1948_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(v_a_1932_, v___x_1947_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_m_1949_, lean_object* v_a_1950_){
_start:
{
lean_object* v_res_1951_; 
v_res_1951_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(v_m_1949_, v_a_1950_);
lean_dec_ref(v_a_1950_);
lean_dec_ref(v_m_1949_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(lean_object* v_k_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v_b_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
lean_object* v___x_1961_; 
lean_inc(v___y_1959_);
lean_inc_ref(v___y_1958_);
lean_inc(v___y_1957_);
lean_inc_ref(v___y_1956_);
lean_inc(v___y_1954_);
lean_inc(v___y_1953_);
v___x_1961_ = lean_apply_8(v_k_1952_, v_b_1955_, v___y_1953_, v___y_1954_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, lean_box(0));
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed(lean_object* v_k_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v_b_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(v_k_1962_, v___y_1963_, v___y_1964_, v_b_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
lean_dec(v___y_1964_);
lean_dec(v___y_1963_);
return v_res_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(lean_object* v_name_1972_, lean_object* v_type_1973_, lean_object* v_val_1974_, lean_object* v_k_1975_, uint8_t v_nondep_1976_, uint8_t v_kind_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_){
_start:
{
lean_object* v___f_1985_; lean_object* v___x_1986_; 
lean_inc(v___y_1979_);
lean_inc(v___y_1978_);
v___f_1985_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1985_, 0, v_k_1975_);
lean_closure_set(v___f_1985_, 1, v___y_1978_);
lean_closure_set(v___f_1985_, 2, v___y_1979_);
v___x_1986_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1972_, v_type_1973_, v_val_1974_, v___f_1985_, v_nondep_1976_, v_kind_1977_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_);
if (lean_obj_tag(v___x_1986_) == 0)
{
return v___x_1986_;
}
else
{
lean_object* v_a_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1994_; 
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1989_ = v___x_1986_;
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_a_1987_);
lean_dec(v___x_1986_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1992_; 
if (v_isShared_1990_ == 0)
{
v___x_1992_ = v___x_1989_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_a_1987_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg___boxed(lean_object* v_name_1995_, lean_object* v_type_1996_, lean_object* v_val_1997_, lean_object* v_k_1998_, lean_object* v_nondep_1999_, lean_object* v_kind_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_){
_start:
{
uint8_t v_nondep_boxed_2008_; uint8_t v_kind_boxed_2009_; lean_object* v_res_2010_; 
v_nondep_boxed_2008_ = lean_unbox(v_nondep_1999_);
v_kind_boxed_2009_ = lean_unbox(v_kind_2000_);
v_res_2010_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_name_1995_, v_type_1996_, v_val_1997_, v_k_1998_, v_nondep_boxed_2008_, v_kind_boxed_2009_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
lean_dec(v___y_2002_);
lean_dec(v___y_2001_);
return v_res_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_name_2011_, uint8_t v_bi_2012_, lean_object* v_type_2013_, lean_object* v_k_2014_, uint8_t v_kind_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_){
_start:
{
lean_object* v___f_2023_; lean_object* v___x_2024_; 
lean_inc(v___y_2017_);
lean_inc(v___y_2016_);
v___f_2023_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2023_, 0, v_k_2014_);
lean_closure_set(v___f_2023_, 1, v___y_2016_);
lean_closure_set(v___f_2023_, 2, v___y_2017_);
v___x_2024_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2011_, v_bi_2012_, v_type_2013_, v___f_2023_, v_kind_2015_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
if (lean_obj_tag(v___x_2024_) == 0)
{
return v___x_2024_;
}
else
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2032_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2027_ = v___x_2024_;
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_2024_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2030_; 
if (v_isShared_2028_ == 0)
{
v___x_2030_ = v___x_2027_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_a_2025_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_name_2033_, lean_object* v_bi_2034_, lean_object* v_type_2035_, lean_object* v_k_2036_, lean_object* v_kind_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
uint8_t v_bi_boxed_2045_; uint8_t v_kind_boxed_2046_; lean_object* v_res_2047_; 
v_bi_boxed_2045_ = lean_unbox(v_bi_2034_);
v_kind_boxed_2046_ = lean_unbox(v_kind_2037_);
v_res_2047_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_name_2033_, v_bi_boxed_2045_, v_type_2035_, v_k_2036_, v_kind_boxed_2046_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec(v___y_2038_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2(lean_object* v___x_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
lean_object* v___x_2055_; 
v___x_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2048_);
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2___boxed(lean_object* v___x_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2(v___x_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
lean_dec(v___y_2057_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_2064_, lean_object* v_x_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_){
_start:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2072_ = lean_apply_1(v_x_2065_, lean_box(0));
v___x_2073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2072_);
return v___x_2073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_2074_, lean_object* v_x_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
lean_object* v_res_2082_; 
v_res_2082_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(v_00_u03b1_2074_, v_x_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
lean_dec(v___y_2076_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(lean_object* v_x_2083_, lean_object* v_x_2084_){
_start:
{
if (lean_obj_tag(v_x_2084_) == 0)
{
return v_x_2083_;
}
else
{
lean_object* v_key_2085_; lean_object* v_value_2086_; lean_object* v_tail_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2110_; 
v_key_2085_ = lean_ctor_get(v_x_2084_, 0);
v_value_2086_ = lean_ctor_get(v_x_2084_, 1);
v_tail_2087_ = lean_ctor_get(v_x_2084_, 2);
v_isSharedCheck_2110_ = !lean_is_exclusive(v_x_2084_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2089_ = v_x_2084_;
v_isShared_2090_ = v_isSharedCheck_2110_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_tail_2087_);
lean_inc(v_value_2086_);
lean_inc(v_key_2085_);
lean_dec(v_x_2084_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2110_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2091_; uint64_t v___x_2092_; uint64_t v___x_2093_; uint64_t v___x_2094_; uint64_t v_fold_2095_; uint64_t v___x_2096_; uint64_t v___x_2097_; uint64_t v___x_2098_; size_t v___x_2099_; size_t v___x_2100_; size_t v___x_2101_; size_t v___x_2102_; size_t v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2106_; 
v___x_2091_ = lean_array_get_size(v_x_2083_);
v___x_2092_ = l_Lean_ExprStructEq_hash(v_key_2085_);
v___x_2093_ = 32ULL;
v___x_2094_ = lean_uint64_shift_right(v___x_2092_, v___x_2093_);
v_fold_2095_ = lean_uint64_xor(v___x_2092_, v___x_2094_);
v___x_2096_ = 16ULL;
v___x_2097_ = lean_uint64_shift_right(v_fold_2095_, v___x_2096_);
v___x_2098_ = lean_uint64_xor(v_fold_2095_, v___x_2097_);
v___x_2099_ = lean_uint64_to_usize(v___x_2098_);
v___x_2100_ = lean_usize_of_nat(v___x_2091_);
v___x_2101_ = ((size_t)1ULL);
v___x_2102_ = lean_usize_sub(v___x_2100_, v___x_2101_);
v___x_2103_ = lean_usize_land(v___x_2099_, v___x_2102_);
v___x_2104_ = lean_array_uget_borrowed(v_x_2083_, v___x_2103_);
lean_inc(v___x_2104_);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 2, v___x_2104_);
v___x_2106_ = v___x_2089_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_key_2085_);
lean_ctor_set(v_reuseFailAlloc_2109_, 1, v_value_2086_);
lean_ctor_set(v_reuseFailAlloc_2109_, 2, v___x_2104_);
v___x_2106_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
lean_object* v___x_2107_; 
v___x_2107_ = lean_array_uset(v_x_2083_, v___x_2103_, v___x_2106_);
v_x_2083_ = v___x_2107_;
v_x_2084_ = v_tail_2087_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(lean_object* v_i_2111_, lean_object* v_source_2112_, lean_object* v_target_2113_){
_start:
{
lean_object* v___x_2114_; uint8_t v___x_2115_; 
v___x_2114_ = lean_array_get_size(v_source_2112_);
v___x_2115_ = lean_nat_dec_lt(v_i_2111_, v___x_2114_);
if (v___x_2115_ == 0)
{
lean_dec_ref(v_source_2112_);
lean_dec(v_i_2111_);
return v_target_2113_;
}
else
{
lean_object* v_es_2116_; lean_object* v___x_2117_; lean_object* v_source_2118_; lean_object* v_target_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
v_es_2116_ = lean_array_fget(v_source_2112_, v_i_2111_);
v___x_2117_ = lean_box(0);
v_source_2118_ = lean_array_fset(v_source_2112_, v_i_2111_, v___x_2117_);
v_target_2119_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_target_2113_, v_es_2116_);
v___x_2120_ = lean_unsigned_to_nat(1u);
v___x_2121_ = lean_nat_add(v_i_2111_, v___x_2120_);
lean_dec(v_i_2111_);
v_i_2111_ = v___x_2121_;
v_source_2112_ = v_source_2118_;
v_target_2113_ = v_target_2119_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(lean_object* v_data_2123_){
_start:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v_nbuckets_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2124_ = lean_array_get_size(v_data_2123_);
v___x_2125_ = lean_unsigned_to_nat(2u);
v_nbuckets_2126_ = lean_nat_mul(v___x_2124_, v___x_2125_);
v___x_2127_ = lean_unsigned_to_nat(0u);
v___x_2128_ = lean_box(0);
v___x_2129_ = lean_mk_array(v_nbuckets_2126_, v___x_2128_);
v___x_2130_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v___x_2127_, v_data_2123_, v___x_2129_);
return v___x_2130_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(lean_object* v_a_2131_, lean_object* v_b_2132_, lean_object* v_x_2133_){
_start:
{
if (lean_obj_tag(v_x_2133_) == 0)
{
lean_dec(v_b_2132_);
lean_dec_ref(v_a_2131_);
return v_x_2133_;
}
else
{
lean_object* v_key_2134_; lean_object* v_value_2135_; lean_object* v_tail_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2148_; 
v_key_2134_ = lean_ctor_get(v_x_2133_, 0);
v_value_2135_ = lean_ctor_get(v_x_2133_, 1);
v_tail_2136_ = lean_ctor_get(v_x_2133_, 2);
v_isSharedCheck_2148_ = !lean_is_exclusive(v_x_2133_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2138_ = v_x_2133_;
v_isShared_2139_ = v_isSharedCheck_2148_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_tail_2136_);
lean_inc(v_value_2135_);
lean_inc(v_key_2134_);
lean_dec(v_x_2133_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2148_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
uint8_t v___x_2140_; 
v___x_2140_ = l_Lean_ExprStructEq_beq(v_key_2134_, v_a_2131_);
if (v___x_2140_ == 0)
{
lean_object* v___x_2141_; lean_object* v___x_2143_; 
v___x_2141_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(v_a_2131_, v_b_2132_, v_tail_2136_);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 2, v___x_2141_);
v___x_2143_ = v___x_2138_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_key_2134_);
lean_ctor_set(v_reuseFailAlloc_2144_, 1, v_value_2135_);
lean_ctor_set(v_reuseFailAlloc_2144_, 2, v___x_2141_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
else
{
lean_object* v___x_2146_; 
lean_dec(v_value_2135_);
lean_dec(v_key_2134_);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 1, v_b_2132_);
lean_ctor_set(v___x_2138_, 0, v_a_2131_);
v___x_2146_ = v___x_2138_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_a_2131_);
lean_ctor_set(v_reuseFailAlloc_2147_, 1, v_b_2132_);
lean_ctor_set(v_reuseFailAlloc_2147_, 2, v_tail_2136_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(lean_object* v_a_2149_, lean_object* v_x_2150_){
_start:
{
if (lean_obj_tag(v_x_2150_) == 0)
{
uint8_t v___x_2151_; 
v___x_2151_ = 0;
return v___x_2151_;
}
else
{
lean_object* v_key_2152_; lean_object* v_tail_2153_; uint8_t v___x_2154_; 
v_key_2152_ = lean_ctor_get(v_x_2150_, 0);
v_tail_2153_ = lean_ctor_get(v_x_2150_, 2);
v___x_2154_ = l_Lean_ExprStructEq_beq(v_key_2152_, v_a_2149_);
if (v___x_2154_ == 0)
{
v_x_2150_ = v_tail_2153_;
goto _start;
}
else
{
return v___x_2154_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg___boxed(lean_object* v_a_2156_, lean_object* v_x_2157_){
_start:
{
uint8_t v_res_2158_; lean_object* v_r_2159_; 
v_res_2158_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_a_2156_, v_x_2157_);
lean_dec(v_x_2157_);
lean_dec_ref(v_a_2156_);
v_r_2159_ = lean_box(v_res_2158_);
return v_r_2159_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(lean_object* v_m_2160_, lean_object* v_a_2161_, lean_object* v_b_2162_){
_start:
{
lean_object* v_size_2163_; lean_object* v_buckets_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2207_; 
v_size_2163_ = lean_ctor_get(v_m_2160_, 0);
v_buckets_2164_ = lean_ctor_get(v_m_2160_, 1);
v_isSharedCheck_2207_ = !lean_is_exclusive(v_m_2160_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2166_ = v_m_2160_;
v_isShared_2167_ = v_isSharedCheck_2207_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_buckets_2164_);
lean_inc(v_size_2163_);
lean_dec(v_m_2160_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2207_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2168_; uint64_t v___x_2169_; uint64_t v___x_2170_; uint64_t v___x_2171_; uint64_t v_fold_2172_; uint64_t v___x_2173_; uint64_t v___x_2174_; uint64_t v___x_2175_; size_t v___x_2176_; size_t v___x_2177_; size_t v___x_2178_; size_t v___x_2179_; size_t v___x_2180_; lean_object* v_bkt_2181_; uint8_t v___x_2182_; 
v___x_2168_ = lean_array_get_size(v_buckets_2164_);
v___x_2169_ = l_Lean_ExprStructEq_hash(v_a_2161_);
v___x_2170_ = 32ULL;
v___x_2171_ = lean_uint64_shift_right(v___x_2169_, v___x_2170_);
v_fold_2172_ = lean_uint64_xor(v___x_2169_, v___x_2171_);
v___x_2173_ = 16ULL;
v___x_2174_ = lean_uint64_shift_right(v_fold_2172_, v___x_2173_);
v___x_2175_ = lean_uint64_xor(v_fold_2172_, v___x_2174_);
v___x_2176_ = lean_uint64_to_usize(v___x_2175_);
v___x_2177_ = lean_usize_of_nat(v___x_2168_);
v___x_2178_ = ((size_t)1ULL);
v___x_2179_ = lean_usize_sub(v___x_2177_, v___x_2178_);
v___x_2180_ = lean_usize_land(v___x_2176_, v___x_2179_);
v_bkt_2181_ = lean_array_uget_borrowed(v_buckets_2164_, v___x_2180_);
v___x_2182_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_a_2161_, v_bkt_2181_);
if (v___x_2182_ == 0)
{
lean_object* v___x_2183_; lean_object* v_size_x27_2184_; lean_object* v___x_2185_; lean_object* v_buckets_x27_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; uint8_t v___x_2192_; 
v___x_2183_ = lean_unsigned_to_nat(1u);
v_size_x27_2184_ = lean_nat_add(v_size_2163_, v___x_2183_);
lean_dec(v_size_2163_);
lean_inc(v_bkt_2181_);
v___x_2185_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2185_, 0, v_a_2161_);
lean_ctor_set(v___x_2185_, 1, v_b_2162_);
lean_ctor_set(v___x_2185_, 2, v_bkt_2181_);
v_buckets_x27_2186_ = lean_array_uset(v_buckets_2164_, v___x_2180_, v___x_2185_);
v___x_2187_ = lean_unsigned_to_nat(4u);
v___x_2188_ = lean_nat_mul(v_size_x27_2184_, v___x_2187_);
v___x_2189_ = lean_unsigned_to_nat(3u);
v___x_2190_ = lean_nat_div(v___x_2188_, v___x_2189_);
lean_dec(v___x_2188_);
v___x_2191_ = lean_array_get_size(v_buckets_x27_2186_);
v___x_2192_ = lean_nat_dec_le(v___x_2190_, v___x_2191_);
lean_dec(v___x_2190_);
if (v___x_2192_ == 0)
{
lean_object* v_val_2193_; lean_object* v___x_2195_; 
v_val_2193_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(v_buckets_x27_2186_);
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 1, v_val_2193_);
lean_ctor_set(v___x_2166_, 0, v_size_x27_2184_);
v___x_2195_ = v___x_2166_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_size_x27_2184_);
lean_ctor_set(v_reuseFailAlloc_2196_, 1, v_val_2193_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
else
{
lean_object* v___x_2198_; 
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 1, v_buckets_x27_2186_);
lean_ctor_set(v___x_2166_, 0, v_size_x27_2184_);
v___x_2198_ = v___x_2166_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_size_x27_2184_);
lean_ctor_set(v_reuseFailAlloc_2199_, 1, v_buckets_x27_2186_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
else
{
lean_object* v___x_2200_; lean_object* v_buckets_x27_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2205_; 
lean_inc(v_bkt_2181_);
v___x_2200_ = lean_box(0);
v_buckets_x27_2201_ = lean_array_uset(v_buckets_2164_, v___x_2180_, v___x_2200_);
v___x_2202_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(v_a_2161_, v_b_2162_, v_bkt_2181_);
v___x_2203_ = lean_array_uset(v_buckets_x27_2201_, v___x_2180_, v___x_2202_);
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 1, v___x_2203_);
v___x_2205_ = v___x_2166_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_size_2163_);
lean_ctor_set(v_reuseFailAlloc_2206_, 1, v___x_2203_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2(lean_object* v_a_2208_, lean_object* v_e_2209_, lean_object* v_a_2210_){
_start:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2212_ = lean_st_ref_take(v_a_2208_);
v___x_2213_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(v___x_2212_, v_e_2209_, v_a_2210_);
v___x_2214_ = lean_st_ref_set(v_a_2208_, v___x_2213_);
v___x_2215_ = lean_box(0);
return v___x_2215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2___boxed(lean_object* v_a_2216_, lean_object* v_e_2217_, lean_object* v_a_2218_, lean_object* v___y_2219_){
_start:
{
lean_object* v_res_2220_; 
v_res_2220_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2(v_a_2216_, v_e_2217_, v_a_2218_);
lean_dec(v_a_2216_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0(lean_object* v_fvars_2224_, lean_object* v_pre_2225_, lean_object* v_post_2226_, uint8_t v_usedLetOnly_2227_, uint8_t v_skipConstInApp_2228_, uint8_t v_skipInstances_2229_, lean_object* v_body_2230_, lean_object* v_x_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2239_ = lean_array_push(v_fvars_2224_, v_x_2231_);
v___x_2240_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(v_pre_2225_, v_post_2226_, v_usedLetOnly_2227_, v_skipConstInApp_2228_, v_skipInstances_2229_, v___x_2239_, v_body_2230_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_);
return v___x_2240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0___boxed(lean_object* v_fvars_2241_, lean_object* v_pre_2242_, lean_object* v_post_2243_, lean_object* v_usedLetOnly_2244_, lean_object* v_skipConstInApp_2245_, lean_object* v_skipInstances_2246_, lean_object* v_body_2247_, lean_object* v_x_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_){
_start:
{
uint8_t v_usedLetOnly_boxed_2256_; uint8_t v_skipConstInApp_boxed_2257_; uint8_t v_skipInstances_boxed_2258_; lean_object* v_res_2259_; 
v_usedLetOnly_boxed_2256_ = lean_unbox(v_usedLetOnly_2244_);
v_skipConstInApp_boxed_2257_ = lean_unbox(v_skipConstInApp_2245_);
v_skipInstances_boxed_2258_ = lean_unbox(v_skipInstances_2246_);
v_res_2259_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0(v_fvars_2241_, v_pre_2242_, v_post_2243_, v_usedLetOnly_boxed_2256_, v_skipConstInApp_boxed_2257_, v_skipInstances_boxed_2258_, v_body_2247_, v_x_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec(v___y_2249_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(lean_object* v_pre_2260_, lean_object* v_post_2261_, uint8_t v_usedLetOnly_2262_, uint8_t v_skipConstInApp_2263_, uint8_t v_skipInstances_2264_, lean_object* v_e_2265_, lean_object* v_a_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v___x_2273_; 
lean_inc_ref(v_post_2261_);
lean_inc(v___y_2271_);
lean_inc_ref(v___y_2270_);
lean_inc(v___y_2269_);
lean_inc_ref(v___y_2268_);
lean_inc(v___y_2267_);
lean_inc_ref(v_e_2265_);
v___x_2273_ = lean_apply_7(v_post_2261_, v_e_2265_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, lean_box(0));
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2292_; 
v_a_2274_ = lean_ctor_get(v___x_2273_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2276_ = v___x_2273_;
v_isShared_2277_ = v_isSharedCheck_2292_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2273_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2292_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
switch(lean_obj_tag(v_a_2274_))
{
case 0:
{
lean_object* v_e_2278_; lean_object* v___x_2280_; 
lean_dec_ref(v_e_2265_);
lean_dec_ref(v_post_2261_);
lean_dec_ref(v_pre_2260_);
v_e_2278_ = lean_ctor_get(v_a_2274_, 0);
lean_inc_ref(v_e_2278_);
lean_dec_ref(v_a_2274_);
if (v_isShared_2277_ == 0)
{
lean_ctor_set(v___x_2276_, 0, v_e_2278_);
v___x_2280_ = v___x_2276_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_e_2278_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
case 1:
{
lean_object* v_e_2282_; lean_object* v___x_2283_; 
lean_del_object(v___x_2276_);
lean_dec_ref(v_e_2265_);
v_e_2282_ = lean_ctor_get(v_a_2274_, 0);
lean_inc_ref(v_e_2282_);
lean_dec_ref(v_a_2274_);
v___x_2283_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2260_, v_post_2261_, v_usedLetOnly_2262_, v_skipConstInApp_2263_, v_skipInstances_2264_, v_e_2282_, v_a_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
return v___x_2283_;
}
default: 
{
lean_object* v_e_x3f_2284_; 
lean_dec_ref(v_post_2261_);
lean_dec_ref(v_pre_2260_);
v_e_x3f_2284_ = lean_ctor_get(v_a_2274_, 0);
lean_inc(v_e_x3f_2284_);
lean_dec_ref(v_a_2274_);
if (lean_obj_tag(v_e_x3f_2284_) == 0)
{
lean_object* v___x_2286_; 
if (v_isShared_2277_ == 0)
{
lean_ctor_set(v___x_2276_, 0, v_e_2265_);
v___x_2286_ = v___x_2276_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_e_2265_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
else
{
lean_object* v_val_2288_; lean_object* v___x_2290_; 
lean_dec_ref(v_e_2265_);
v_val_2288_ = lean_ctor_get(v_e_x3f_2284_, 0);
lean_inc(v_val_2288_);
lean_dec_ref(v_e_x3f_2284_);
if (v_isShared_2277_ == 0)
{
lean_ctor_set(v___x_2276_, 0, v_val_2288_);
v___x_2290_ = v___x_2276_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_val_2288_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
}
}
}
else
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2300_; 
lean_dec_ref(v_e_2265_);
lean_dec_ref(v_post_2261_);
lean_dec_ref(v_pre_2260_);
v_a_2293_ = lean_ctor_get(v___x_2273_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2295_ = v___x_2273_;
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2273_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2298_; 
if (v_isShared_2296_ == 0)
{
v___x_2298_ = v___x_2295_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_a_2293_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(lean_object* v_pre_2301_, lean_object* v_post_2302_, uint8_t v_usedLetOnly_2303_, uint8_t v_skipConstInApp_2304_, uint8_t v_skipInstances_2305_, lean_object* v_fvars_2306_, lean_object* v_e_2307_, lean_object* v_a_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
if (lean_obj_tag(v_e_2307_) == 6)
{
lean_object* v_binderName_2315_; lean_object* v_binderType_2316_; lean_object* v_body_2317_; uint8_t v_binderInfo_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
v_binderName_2315_ = lean_ctor_get(v_e_2307_, 0);
lean_inc(v_binderName_2315_);
v_binderType_2316_ = lean_ctor_get(v_e_2307_, 1);
lean_inc_ref(v_binderType_2316_);
v_body_2317_ = lean_ctor_get(v_e_2307_, 2);
lean_inc_ref(v_body_2317_);
v_binderInfo_2318_ = lean_ctor_get_uint8(v_e_2307_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_2307_);
v___x_2319_ = lean_expr_instantiate_rev(v_binderType_2316_, v_fvars_2306_);
lean_dec_ref(v_binderType_2316_);
lean_inc_ref(v_post_2302_);
lean_inc_ref(v_pre_2301_);
v___x_2320_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2301_, v_post_2302_, v_usedLetOnly_2303_, v_skipConstInApp_2304_, v_skipInstances_2305_, v___x_2319_, v_a_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_a_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___f_2325_; uint8_t v___x_2326_; lean_object* v___x_2327_; 
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_a_2321_);
lean_dec_ref(v___x_2320_);
v___x_2322_ = lean_box(v_usedLetOnly_2303_);
v___x_2323_ = lean_box(v_skipConstInApp_2304_);
v___x_2324_ = lean_box(v_skipInstances_2305_);
v___f_2325_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0___boxed), 15, 7);
lean_closure_set(v___f_2325_, 0, v_fvars_2306_);
lean_closure_set(v___f_2325_, 1, v_pre_2301_);
lean_closure_set(v___f_2325_, 2, v_post_2302_);
lean_closure_set(v___f_2325_, 3, v___x_2322_);
lean_closure_set(v___f_2325_, 4, v___x_2323_);
lean_closure_set(v___f_2325_, 5, v___x_2324_);
lean_closure_set(v___f_2325_, 6, v_body_2317_);
v___x_2326_ = 0;
v___x_2327_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_2315_, v_binderInfo_2318_, v_a_2321_, v___f_2325_, v___x_2326_, v_a_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
return v___x_2327_;
}
else
{
lean_dec_ref(v_body_2317_);
lean_dec(v_binderName_2315_);
lean_dec_ref(v_fvars_2306_);
lean_dec_ref(v_post_2302_);
lean_dec_ref(v_pre_2301_);
return v___x_2320_;
}
}
else
{
lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2328_ = lean_expr_instantiate_rev(v_e_2307_, v_fvars_2306_);
lean_dec_ref(v_e_2307_);
lean_inc_ref(v_post_2302_);
lean_inc_ref(v_pre_2301_);
v___x_2329_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2301_, v_post_2302_, v_usedLetOnly_2303_, v_skipConstInApp_2304_, v_skipInstances_2305_, v___x_2328_, v_a_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; uint8_t v___x_2331_; uint8_t v___x_2332_; uint8_t v___x_2333_; lean_object* v___x_2334_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
lean_inc(v_a_2330_);
lean_dec_ref(v___x_2329_);
v___x_2331_ = 0;
v___x_2332_ = 1;
v___x_2333_ = 1;
v___x_2334_ = l_Lean_Meta_mkLambdaFVars(v_fvars_2306_, v_a_2330_, v___x_2331_, v_usedLetOnly_2303_, v___x_2331_, v___x_2332_, v___x_2333_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
lean_dec_ref(v_fvars_2306_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_a_2335_; lean_object* v___x_2336_; 
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_a_2335_);
lean_dec_ref(v___x_2334_);
v___x_2336_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2301_, v_post_2302_, v_usedLetOnly_2303_, v_skipConstInApp_2304_, v_skipInstances_2305_, v_a_2335_, v_a_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
return v___x_2336_;
}
else
{
lean_dec_ref(v_post_2302_);
lean_dec_ref(v_pre_2301_);
return v___x_2334_;
}
}
else
{
lean_dec_ref(v_fvars_2306_);
lean_dec_ref(v_post_2302_);
lean_dec_ref(v_pre_2301_);
return v___x_2329_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0(lean_object* v_fvars_2337_, lean_object* v_pre_2338_, lean_object* v_post_2339_, uint8_t v_usedLetOnly_2340_, uint8_t v_skipConstInApp_2341_, uint8_t v_skipInstances_2342_, lean_object* v_body_2343_, lean_object* v_x_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_){
_start:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2352_ = lean_array_push(v_fvars_2337_, v_x_2344_);
v___x_2353_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(v_pre_2338_, v_post_2339_, v_usedLetOnly_2340_, v_skipConstInApp_2341_, v_skipInstances_2342_, v___x_2352_, v_body_2343_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
return v___x_2353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0___boxed(lean_object* v_fvars_2354_, lean_object* v_pre_2355_, lean_object* v_post_2356_, lean_object* v_usedLetOnly_2357_, lean_object* v_skipConstInApp_2358_, lean_object* v_skipInstances_2359_, lean_object* v_body_2360_, lean_object* v_x_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_){
_start:
{
uint8_t v_usedLetOnly_boxed_2369_; uint8_t v_skipConstInApp_boxed_2370_; uint8_t v_skipInstances_boxed_2371_; lean_object* v_res_2372_; 
v_usedLetOnly_boxed_2369_ = lean_unbox(v_usedLetOnly_2357_);
v_skipConstInApp_boxed_2370_ = lean_unbox(v_skipConstInApp_2358_);
v_skipInstances_boxed_2371_ = lean_unbox(v_skipInstances_2359_);
v_res_2372_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0(v_fvars_2354_, v_pre_2355_, v_post_2356_, v_usedLetOnly_boxed_2369_, v_skipConstInApp_boxed_2370_, v_skipInstances_boxed_2371_, v_body_2360_, v_x_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec(v___y_2363_);
lean_dec(v___y_2362_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(lean_object* v_pre_2373_, lean_object* v_post_2374_, uint8_t v_usedLetOnly_2375_, uint8_t v_skipConstInApp_2376_, uint8_t v_skipInstances_2377_, lean_object* v_fvars_2378_, lean_object* v_e_2379_, lean_object* v_a_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_){
_start:
{
if (lean_obj_tag(v_e_2379_) == 8)
{
lean_object* v_declName_2387_; lean_object* v_type_2388_; lean_object* v_value_2389_; lean_object* v_body_2390_; uint8_t v_nondep_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v_declName_2387_ = lean_ctor_get(v_e_2379_, 0);
lean_inc(v_declName_2387_);
v_type_2388_ = lean_ctor_get(v_e_2379_, 1);
lean_inc_ref(v_type_2388_);
v_value_2389_ = lean_ctor_get(v_e_2379_, 2);
lean_inc_ref(v_value_2389_);
v_body_2390_ = lean_ctor_get(v_e_2379_, 3);
lean_inc_ref(v_body_2390_);
v_nondep_2391_ = lean_ctor_get_uint8(v_e_2379_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_2379_);
v___x_2392_ = lean_expr_instantiate_rev(v_type_2388_, v_fvars_2378_);
lean_dec_ref(v_type_2388_);
lean_inc_ref(v_post_2374_);
lean_inc_ref(v_pre_2373_);
v___x_2393_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2373_, v_post_2374_, v_usedLetOnly_2375_, v_skipConstInApp_2376_, v_skipInstances_2377_, v___x_2392_, v_a_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v_a_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
lean_inc(v_a_2394_);
lean_dec_ref(v___x_2393_);
v___x_2395_ = lean_expr_instantiate_rev(v_value_2389_, v_fvars_2378_);
lean_dec_ref(v_value_2389_);
lean_inc_ref(v_post_2374_);
lean_inc_ref(v_pre_2373_);
v___x_2396_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2373_, v_post_2374_, v_usedLetOnly_2375_, v_skipConstInApp_2376_, v_skipInstances_2377_, v___x_2395_, v_a_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v_a_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___f_2401_; uint8_t v___x_2402_; lean_object* v___x_2403_; 
v_a_2397_ = lean_ctor_get(v___x_2396_, 0);
lean_inc(v_a_2397_);
lean_dec_ref(v___x_2396_);
v___x_2398_ = lean_box(v_usedLetOnly_2375_);
v___x_2399_ = lean_box(v_skipConstInApp_2376_);
v___x_2400_ = lean_box(v_skipInstances_2377_);
v___f_2401_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0___boxed), 15, 7);
lean_closure_set(v___f_2401_, 0, v_fvars_2378_);
lean_closure_set(v___f_2401_, 1, v_pre_2373_);
lean_closure_set(v___f_2401_, 2, v_post_2374_);
lean_closure_set(v___f_2401_, 3, v___x_2398_);
lean_closure_set(v___f_2401_, 4, v___x_2399_);
lean_closure_set(v___f_2401_, 5, v___x_2400_);
lean_closure_set(v___f_2401_, 6, v_body_2390_);
v___x_2402_ = 0;
v___x_2403_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_declName_2387_, v_a_2394_, v_a_2397_, v___f_2401_, v_nondep_2391_, v___x_2402_, v_a_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
return v___x_2403_;
}
else
{
lean_dec(v_a_2394_);
lean_dec_ref(v_body_2390_);
lean_dec(v_declName_2387_);
lean_dec_ref(v_fvars_2378_);
lean_dec_ref(v_post_2374_);
lean_dec_ref(v_pre_2373_);
return v___x_2396_;
}
}
else
{
lean_dec_ref(v_body_2390_);
lean_dec_ref(v_value_2389_);
lean_dec(v_declName_2387_);
lean_dec_ref(v_fvars_2378_);
lean_dec_ref(v_post_2374_);
lean_dec_ref(v_pre_2373_);
return v___x_2393_;
}
}
else
{
lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2404_ = lean_expr_instantiate_rev(v_e_2379_, v_fvars_2378_);
lean_dec_ref(v_e_2379_);
lean_inc_ref(v_post_2374_);
lean_inc_ref(v_pre_2373_);
v___x_2405_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2373_, v_post_2374_, v_usedLetOnly_2375_, v_skipConstInApp_2376_, v_skipInstances_2377_, v___x_2404_, v_a_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_object* v_a_2406_; uint8_t v___x_2407_; uint8_t v___x_2408_; lean_object* v___x_2409_; 
v_a_2406_ = lean_ctor_get(v___x_2405_, 0);
lean_inc(v_a_2406_);
lean_dec_ref(v___x_2405_);
v___x_2407_ = 0;
v___x_2408_ = 1;
v___x_2409_ = l_Lean_Meta_mkLetFVars(v_fvars_2378_, v_a_2406_, v_usedLetOnly_2375_, v___x_2407_, v___x_2408_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
lean_dec_ref(v_fvars_2378_);
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_object* v_a_2410_; lean_object* v___x_2411_; 
v_a_2410_ = lean_ctor_get(v___x_2409_, 0);
lean_inc(v_a_2410_);
lean_dec_ref(v___x_2409_);
v___x_2411_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2373_, v_post_2374_, v_usedLetOnly_2375_, v_skipConstInApp_2376_, v_skipInstances_2377_, v_a_2410_, v_a_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
return v___x_2411_;
}
else
{
lean_dec_ref(v_post_2374_);
lean_dec_ref(v_pre_2373_);
return v___x_2409_;
}
}
else
{
lean_dec_ref(v_fvars_2378_);
lean_dec_ref(v_post_2374_);
lean_dec_ref(v_pre_2373_);
return v___x_2405_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2412_; lean_object* v_dummy_2413_; 
v___x_2412_ = lean_box(0);
v_dummy_2413_ = l_Lean_Expr_sort___override(v___x_2412_);
return v_dummy_2413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(lean_object* v_pre_2414_, lean_object* v_post_2415_, uint8_t v_usedLetOnly_2416_, uint8_t v_skipConstInApp_2417_, uint8_t v_skipInstances_2418_, size_t v_sz_2419_, size_t v_i_2420_, lean_object* v_bs_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
uint8_t v___x_2429_; 
v___x_2429_ = lean_usize_dec_lt(v_i_2420_, v_sz_2419_);
if (v___x_2429_ == 0)
{
lean_object* v___x_2430_; 
lean_dec_ref(v_post_2415_);
lean_dec_ref(v_pre_2414_);
v___x_2430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2430_, 0, v_bs_2421_);
return v___x_2430_;
}
else
{
lean_object* v_v_2431_; lean_object* v___x_2432_; 
v_v_2431_ = lean_array_uget_borrowed(v_bs_2421_, v_i_2420_);
lean_inc(v_v_2431_);
lean_inc_ref(v_post_2415_);
lean_inc_ref(v_pre_2414_);
v___x_2432_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2414_, v_post_2415_, v_usedLetOnly_2416_, v_skipConstInApp_2417_, v_skipInstances_2418_, v_v_2431_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_);
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_object* v_a_2433_; lean_object* v___x_2434_; lean_object* v_bs_x27_2435_; size_t v___x_2436_; size_t v___x_2437_; lean_object* v___x_2438_; 
v_a_2433_ = lean_ctor_get(v___x_2432_, 0);
lean_inc(v_a_2433_);
lean_dec_ref(v___x_2432_);
v___x_2434_ = lean_unsigned_to_nat(0u);
v_bs_x27_2435_ = lean_array_uset(v_bs_2421_, v_i_2420_, v___x_2434_);
v___x_2436_ = ((size_t)1ULL);
v___x_2437_ = lean_usize_add(v_i_2420_, v___x_2436_);
v___x_2438_ = lean_array_uset(v_bs_x27_2435_, v_i_2420_, v_a_2433_);
v_i_2420_ = v___x_2437_;
v_bs_2421_ = v___x_2438_;
goto _start;
}
else
{
lean_object* v_a_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2447_; 
lean_dec_ref(v_bs_2421_);
lean_dec_ref(v_post_2415_);
lean_dec_ref(v_pre_2414_);
v_a_2440_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2442_ = v___x_2432_;
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_a_2440_);
lean_dec(v___x_2432_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2445_; 
if (v_isShared_2443_ == 0)
{
v___x_2445_ = v___x_2442_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_a_2440_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0(lean_object* v_pre_2448_, lean_object* v_post_2449_, uint8_t v_usedLetOnly_2450_, uint8_t v_skipConstInApp_2451_, uint8_t v_skipInstances_2452_, lean_object* v___x_2453_, lean_object* v___y_2454_, lean_object* v_b_2455_, lean_object* v_a_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
lean_object* v___x_2463_; 
v___x_2463_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2448_, v_post_2449_, v_usedLetOnly_2450_, v_skipConstInApp_2451_, v_skipInstances_2452_, v___x_2453_, v___y_2454_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2473_; 
v_a_2464_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2466_ = v___x_2463_;
v_isShared_2467_ = v_isSharedCheck_2473_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2463_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2473_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2471_; 
v___x_2468_ = lean_array_fset(v_b_2455_, v_a_2456_, v_a_2464_);
v___x_2469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2468_);
if (v_isShared_2467_ == 0)
{
lean_ctor_set(v___x_2466_, 0, v___x_2469_);
v___x_2471_ = v___x_2466_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v___x_2469_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
else
{
lean_object* v_a_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2481_; 
lean_dec_ref(v_b_2455_);
v_a_2474_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2476_ = v___x_2463_;
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_a_2474_);
lean_dec(v___x_2463_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2479_; 
if (v_isShared_2477_ == 0)
{
v___x_2479_ = v___x_2476_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_a_2474_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed(lean_object* v_pre_2482_, lean_object* v_post_2483_, lean_object* v_usedLetOnly_2484_, lean_object* v_skipConstInApp_2485_, lean_object* v_skipInstances_2486_, lean_object* v___x_2487_, lean_object* v___y_2488_, lean_object* v_b_2489_, lean_object* v_a_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
uint8_t v_usedLetOnly_boxed_2497_; uint8_t v_skipConstInApp_boxed_2498_; uint8_t v_skipInstances_boxed_2499_; lean_object* v_res_2500_; 
v_usedLetOnly_boxed_2497_ = lean_unbox(v_usedLetOnly_2484_);
v_skipConstInApp_boxed_2498_ = lean_unbox(v_skipConstInApp_2485_);
v_skipInstances_boxed_2499_ = lean_unbox(v_skipInstances_2486_);
v_res_2500_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0(v_pre_2482_, v_post_2483_, v_usedLetOnly_boxed_2497_, v_skipConstInApp_boxed_2498_, v_skipInstances_boxed_2499_, v___x_2487_, v___y_2488_, v_b_2489_, v_a_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec(v_a_2490_);
lean_dec(v___y_2488_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(lean_object* v_upperBound_2501_, lean_object* v___x_2502_, lean_object* v_pre_2503_, lean_object* v_post_2504_, uint8_t v_usedLetOnly_2505_, uint8_t v_skipConstInApp_2506_, uint8_t v_skipInstances_2507_, lean_object* v_a_2508_, lean_object* v_b_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_){
_start:
{
lean_object* v___y_2518_; uint8_t v___x_2541_; 
v___x_2541_ = lean_nat_dec_lt(v_a_2508_, v_upperBound_2501_);
if (v___x_2541_ == 0)
{
lean_object* v___x_2542_; 
lean_dec(v_a_2508_);
lean_dec_ref(v_post_2504_);
lean_dec_ref(v_pre_2503_);
v___x_2542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2542_, 0, v_b_2509_);
return v___x_2542_;
}
else
{
lean_object* v___x_2543_; lean_object* v___x_2544_; uint8_t v___x_2545_; 
v___x_2543_ = lean_array_fget_borrowed(v_b_2509_, v_a_2508_);
v___x_2544_ = lean_array_get_size(v___x_2502_);
v___x_2545_ = lean_nat_dec_lt(v_a_2508_, v___x_2544_);
if (v___x_2545_ == 0)
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___f_2549_; 
lean_inc(v___x_2543_);
v___x_2546_ = lean_box(v_usedLetOnly_2505_);
v___x_2547_ = lean_box(v_skipConstInApp_2506_);
v___x_2548_ = lean_box(v_skipInstances_2507_);
lean_inc(v_a_2508_);
lean_inc(v___y_2510_);
lean_inc_ref(v_post_2504_);
lean_inc_ref(v_pre_2503_);
v___f_2549_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_2549_, 0, v_pre_2503_);
lean_closure_set(v___f_2549_, 1, v_post_2504_);
lean_closure_set(v___f_2549_, 2, v___x_2546_);
lean_closure_set(v___f_2549_, 3, v___x_2547_);
lean_closure_set(v___f_2549_, 4, v___x_2548_);
lean_closure_set(v___f_2549_, 5, v___x_2543_);
lean_closure_set(v___f_2549_, 6, v___y_2510_);
lean_closure_set(v___f_2549_, 7, v_b_2509_);
lean_closure_set(v___f_2549_, 8, v_a_2508_);
v___y_2518_ = v___f_2549_;
goto v___jp_2517_;
}
else
{
lean_object* v___x_2550_; uint8_t v_isInstance_2551_; 
v___x_2550_ = lean_array_fget_borrowed(v___x_2502_, v_a_2508_);
v_isInstance_2551_ = lean_ctor_get_uint8(v___x_2550_, sizeof(void*)*1 + 4);
if (v_isInstance_2551_ == 0)
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___f_2555_; 
lean_inc(v___x_2543_);
v___x_2552_ = lean_box(v_usedLetOnly_2505_);
v___x_2553_ = lean_box(v_skipConstInApp_2506_);
v___x_2554_ = lean_box(v_skipInstances_2507_);
lean_inc(v_a_2508_);
lean_inc(v___y_2510_);
lean_inc_ref(v_post_2504_);
lean_inc_ref(v_pre_2503_);
v___f_2555_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_2555_, 0, v_pre_2503_);
lean_closure_set(v___f_2555_, 1, v_post_2504_);
lean_closure_set(v___f_2555_, 2, v___x_2552_);
lean_closure_set(v___f_2555_, 3, v___x_2553_);
lean_closure_set(v___f_2555_, 4, v___x_2554_);
lean_closure_set(v___f_2555_, 5, v___x_2543_);
lean_closure_set(v___f_2555_, 6, v___y_2510_);
lean_closure_set(v___f_2555_, 7, v_b_2509_);
lean_closure_set(v___f_2555_, 8, v_a_2508_);
v___y_2518_ = v___f_2555_;
goto v___jp_2517_;
}
else
{
lean_object* v___x_2556_; lean_object* v___f_2557_; 
v___x_2556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2556_, 0, v_b_2509_);
v___f_2557_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2557_, 0, v___x_2556_);
v___y_2518_ = v___f_2557_;
goto v___jp_2517_;
}
}
}
v___jp_2517_:
{
lean_object* v___x_2519_; 
lean_inc(v___y_2515_);
lean_inc_ref(v___y_2514_);
lean_inc(v___y_2513_);
lean_inc_ref(v___y_2512_);
lean_inc(v___y_2511_);
v___x_2519_ = lean_apply_6(v___y_2518_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, lean_box(0));
if (lean_obj_tag(v___x_2519_) == 0)
{
lean_object* v_a_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2532_; 
v_a_2520_ = lean_ctor_get(v___x_2519_, 0);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2522_ = v___x_2519_;
v_isShared_2523_ = v_isSharedCheck_2532_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_a_2520_);
lean_dec(v___x_2519_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2532_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
if (lean_obj_tag(v_a_2520_) == 0)
{
lean_object* v_a_2524_; lean_object* v___x_2526_; 
lean_dec(v_a_2508_);
lean_dec_ref(v_post_2504_);
lean_dec_ref(v_pre_2503_);
v_a_2524_ = lean_ctor_get(v_a_2520_, 0);
lean_inc(v_a_2524_);
lean_dec_ref(v_a_2520_);
if (v_isShared_2523_ == 0)
{
lean_ctor_set(v___x_2522_, 0, v_a_2524_);
v___x_2526_ = v___x_2522_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_a_2524_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
return v___x_2526_;
}
}
else
{
lean_object* v_a_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
lean_del_object(v___x_2522_);
v_a_2528_ = lean_ctor_get(v_a_2520_, 0);
lean_inc(v_a_2528_);
lean_dec_ref(v_a_2520_);
v___x_2529_ = lean_unsigned_to_nat(1u);
v___x_2530_ = lean_nat_add(v_a_2508_, v___x_2529_);
lean_dec(v_a_2508_);
v_a_2508_ = v___x_2530_;
v_b_2509_ = v_a_2528_;
goto _start;
}
}
}
else
{
lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2540_; 
lean_dec(v_a_2508_);
lean_dec_ref(v_post_2504_);
lean_dec_ref(v_pre_2503_);
v_a_2533_ = lean_ctor_get(v___x_2519_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2535_ = v___x_2519_;
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_dec(v___x_2519_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2538_; 
if (v_isShared_2536_ == 0)
{
v___x_2538_ = v___x_2535_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_a_2533_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(uint8_t v_skipInstances_2558_, lean_object* v_pre_2559_, lean_object* v_post_2560_, uint8_t v_usedLetOnly_2561_, uint8_t v_skipConstInApp_2562_, lean_object* v_x_2563_, lean_object* v_x_2564_, lean_object* v_x_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_){
_start:
{
lean_object* v_f_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; 
if (lean_obj_tag(v_x_2563_) == 5)
{
lean_object* v_fn_2623_; lean_object* v_arg_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
v_fn_2623_ = lean_ctor_get(v_x_2563_, 0);
lean_inc_ref(v_fn_2623_);
v_arg_2624_ = lean_ctor_get(v_x_2563_, 1);
lean_inc_ref(v_arg_2624_);
lean_dec_ref(v_x_2563_);
v___x_2625_ = lean_array_set(v_x_2564_, v_x_2565_, v_arg_2624_);
v___x_2626_ = lean_unsigned_to_nat(1u);
v___x_2627_ = lean_nat_sub(v_x_2565_, v___x_2626_);
lean_dec(v_x_2565_);
v_x_2563_ = v_fn_2623_;
v_x_2564_ = v___x_2625_;
v_x_2565_ = v___x_2627_;
goto _start;
}
else
{
lean_dec(v_x_2565_);
if (v_skipConstInApp_2562_ == 0)
{
goto v___jp_2620_;
}
else
{
uint8_t v___x_2629_; 
v___x_2629_ = l_Lean_Expr_isConst(v_x_2563_);
if (v___x_2629_ == 0)
{
goto v___jp_2620_;
}
else
{
v_f_2574_ = v_x_2563_;
v___y_2575_ = v___y_2566_;
v___y_2576_ = v___y_2567_;
v___y_2577_ = v___y_2568_;
v___y_2578_ = v___y_2569_;
v___y_2579_ = v___y_2570_;
v___y_2580_ = v___y_2571_;
goto v___jp_2573_;
}
}
}
v___jp_2573_:
{
if (v_skipInstances_2558_ == 0)
{
size_t v_sz_2581_; size_t v___x_2582_; lean_object* v___x_2583_; 
v_sz_2581_ = lean_array_size(v_x_2564_);
v___x_2582_ = ((size_t)0ULL);
lean_inc_ref(v_post_2560_);
lean_inc_ref(v_pre_2559_);
v___x_2583_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(v_pre_2559_, v_post_2560_, v_usedLetOnly_2561_, v_skipConstInApp_2562_, v_skipInstances_2558_, v_sz_2581_, v___x_2582_, v_x_2564_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v_a_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v_a_2584_ = lean_ctor_get(v___x_2583_, 0);
lean_inc(v_a_2584_);
lean_dec_ref(v___x_2583_);
v___x_2585_ = l_Lean_mkAppN(v_f_2574_, v_a_2584_);
lean_dec(v_a_2584_);
v___x_2586_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2559_, v_post_2560_, v_usedLetOnly_2561_, v_skipConstInApp_2562_, v_skipInstances_2558_, v___x_2585_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
return v___x_2586_;
}
else
{
lean_object* v_a_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2594_; 
lean_dec_ref(v_f_2574_);
lean_dec_ref(v_post_2560_);
lean_dec_ref(v_pre_2559_);
v_a_2587_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2594_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2589_ = v___x_2583_;
v_isShared_2590_ = v_isSharedCheck_2594_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_a_2587_);
lean_dec(v___x_2583_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2594_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2592_; 
if (v_isShared_2590_ == 0)
{
v___x_2592_ = v___x_2589_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v_a_2587_);
v___x_2592_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
return v___x_2592_;
}
}
}
}
else
{
lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2595_ = lean_array_get_size(v_x_2564_);
lean_inc_ref(v_f_2574_);
v___x_2596_ = l_Lean_Meta_getFunInfoNArgs(v_f_2574_, v___x_2595_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
if (lean_obj_tag(v___x_2596_) == 0)
{
lean_object* v_a_2597_; lean_object* v_paramInfo_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
v_a_2597_ = lean_ctor_get(v___x_2596_, 0);
lean_inc(v_a_2597_);
lean_dec_ref(v___x_2596_);
v_paramInfo_2598_ = lean_ctor_get(v_a_2597_, 0);
lean_inc_ref(v_paramInfo_2598_);
lean_dec(v_a_2597_);
v___x_2599_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_2560_);
lean_inc_ref(v_pre_2559_);
v___x_2600_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(v___x_2595_, v_paramInfo_2598_, v_pre_2559_, v_post_2560_, v_usedLetOnly_2561_, v_skipConstInApp_2562_, v_skipInstances_2558_, v___x_2599_, v_x_2564_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
lean_dec_ref(v_paramInfo_2598_);
if (lean_obj_tag(v___x_2600_) == 0)
{
lean_object* v_a_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
v_a_2601_ = lean_ctor_get(v___x_2600_, 0);
lean_inc(v_a_2601_);
lean_dec_ref(v___x_2600_);
v___x_2602_ = l_Lean_mkAppN(v_f_2574_, v_a_2601_);
lean_dec(v_a_2601_);
v___x_2603_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2559_, v_post_2560_, v_usedLetOnly_2561_, v_skipConstInApp_2562_, v_skipInstances_2558_, v___x_2602_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
return v___x_2603_;
}
else
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2611_; 
lean_dec_ref(v_f_2574_);
lean_dec_ref(v_post_2560_);
lean_dec_ref(v_pre_2559_);
v_a_2604_ = lean_ctor_get(v___x_2600_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2606_ = v___x_2600_;
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2600_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2609_; 
if (v_isShared_2607_ == 0)
{
v___x_2609_ = v___x_2606_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_a_2604_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
}
}
else
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2619_; 
lean_dec_ref(v_f_2574_);
lean_dec_ref(v_x_2564_);
lean_dec_ref(v_post_2560_);
lean_dec_ref(v_pre_2559_);
v_a_2612_ = lean_ctor_get(v___x_2596_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2614_ = v___x_2596_;
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2596_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2617_; 
if (v_isShared_2615_ == 0)
{
v___x_2617_ = v___x_2614_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_a_2612_);
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
v___jp_2620_:
{
lean_object* v___x_2621_; 
lean_inc_ref(v_post_2560_);
lean_inc_ref(v_pre_2559_);
v___x_2621_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2559_, v_post_2560_, v_usedLetOnly_2561_, v_skipConstInApp_2562_, v_skipInstances_2558_, v_x_2563_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
if (lean_obj_tag(v___x_2621_) == 0)
{
lean_object* v_a_2622_; 
v_a_2622_ = lean_ctor_get(v___x_2621_, 0);
lean_inc(v_a_2622_);
lean_dec_ref(v___x_2621_);
v_f_2574_ = v_a_2622_;
v___y_2575_ = v___y_2566_;
v___y_2576_ = v___y_2567_;
v___y_2577_ = v___y_2568_;
v___y_2578_ = v___y_2569_;
v___y_2579_ = v___y_2570_;
v___y_2580_ = v___y_2571_;
goto v___jp_2573_;
}
else
{
lean_dec_ref(v_x_2564_);
lean_dec_ref(v_post_2560_);
lean_dec_ref(v_pre_2559_);
return v___x_2621_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1(lean_object* v___x_2630_, lean_object* v_pre_2631_, lean_object* v_e_2632_, lean_object* v_post_2633_, uint8_t v_usedLetOnly_2634_, uint8_t v_skipConstInApp_2635_, uint8_t v_skipInstances_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_){
_start:
{
lean_object* v___x_2644_; 
v___x_2644_ = l_Lean_Core_checkSystem(v___x_2630_, v___y_2641_, v___y_2642_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v___x_2645_; 
lean_dec_ref(v___x_2644_);
lean_inc_ref(v_pre_2631_);
lean_inc(v___y_2642_);
lean_inc_ref(v___y_2641_);
lean_inc(v___y_2640_);
lean_inc_ref(v___y_2639_);
lean_inc(v___y_2638_);
lean_inc_ref(v_e_2632_);
v___x_2645_ = lean_apply_7(v_pre_2631_, v_e_2632_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, lean_box(0));
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_object* v_a_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2694_; 
v_a_2646_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2648_ = v___x_2645_;
v_isShared_2649_ = v_isSharedCheck_2694_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_a_2646_);
lean_dec(v___x_2645_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2694_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___y_2651_; 
switch(lean_obj_tag(v_a_2646_))
{
case 0:
{
lean_object* v_e_2686_; lean_object* v___x_2688_; 
lean_dec_ref(v_post_2633_);
lean_dec_ref(v_e_2632_);
lean_dec_ref(v_pre_2631_);
v_e_2686_ = lean_ctor_get(v_a_2646_, 0);
lean_inc_ref(v_e_2686_);
lean_dec_ref(v_a_2646_);
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 0, v_e_2686_);
v___x_2688_ = v___x_2648_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v_e_2686_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
return v___x_2688_;
}
}
case 1:
{
lean_object* v_e_2690_; lean_object* v___x_2691_; 
lean_del_object(v___x_2648_);
lean_dec_ref(v_e_2632_);
v_e_2690_ = lean_ctor_get(v_a_2646_, 0);
lean_inc_ref(v_e_2690_);
lean_dec_ref(v_a_2646_);
v___x_2691_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2631_, v_post_2633_, v_usedLetOnly_2634_, v_skipConstInApp_2635_, v_skipInstances_2636_, v_e_2690_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_);
return v___x_2691_;
}
default: 
{
lean_object* v_e_x3f_2692_; 
lean_del_object(v___x_2648_);
v_e_x3f_2692_ = lean_ctor_get(v_a_2646_, 0);
lean_inc(v_e_x3f_2692_);
lean_dec_ref(v_a_2646_);
if (lean_obj_tag(v_e_x3f_2692_) == 0)
{
v___y_2651_ = v_e_2632_;
goto v___jp_2650_;
}
else
{
lean_object* v_val_2693_; 
lean_dec_ref(v_e_2632_);
v_val_2693_ = lean_ctor_get(v_e_x3f_2692_, 0);
lean_inc(v_val_2693_);
lean_dec_ref(v_e_x3f_2692_);
v___y_2651_ = v_val_2693_;
goto v___jp_2650_;
}
}
}
v___jp_2650_:
{
switch(lean_obj_tag(v___y_2651_))
{
case 7:
{
lean_object* v___x_2652_; lean_object* v___x_2653_; 
v___x_2652_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0));
v___x_2653_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(v_pre_2631_, v_post_2633_, v_usedLetOnly_2634_, v_skipConstInApp_2635_, v_skipInstances_2636_, v___x_2652_, v___y_2651_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_);
return v___x_2653_;
}
case 6:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2654_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0));
v___x_2655_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(v_pre_2631_, v_post_2633_, v_usedLetOnly_2634_, v_skipConstInApp_2635_, v_skipInstances_2636_, v___x_2654_, v___y_2651_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_);
return v___x_2655_;
}
case 8:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2656_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0));
v___x_2657_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(v_pre_2631_, v_post_2633_, v_usedLetOnly_2634_, v_skipConstInApp_2635_, v_skipInstances_2636_, v___x_2656_, v___y_2651_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_);
return v___x_2657_;
}
case 5:
{
lean_object* v_dummy_2658_; lean_object* v_nargs_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; 
v_dummy_2658_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1);
v_nargs_2659_ = l_Lean_Expr_getAppNumArgs(v___y_2651_);
lean_inc(v_nargs_2659_);
v___x_2660_ = lean_mk_array(v_nargs_2659_, v_dummy_2658_);
v___x_2661_ = lean_unsigned_to_nat(1u);
v___x_2662_ = lean_nat_sub(v_nargs_2659_, v___x_2661_);
lean_dec(v_nargs_2659_);
v___x_2663_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(v_skipInstances_2636_, v_pre_2631_, v_post_2633_, v_usedLetOnly_2634_, v_skipConstInApp_2635_, v___y_2651_, v___x_2660_, v___x_2662_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_);
return v___x_2663_;
}
case 10:
{
lean_object* v_data_2664_; lean_object* v_expr_2665_; lean_object* v___x_2666_; 
v_data_2664_ = lean_ctor_get(v___y_2651_, 0);
v_expr_2665_ = lean_ctor_get(v___y_2651_, 1);
lean_inc_ref(v_expr_2665_);
lean_inc_ref(v_post_2633_);
lean_inc_ref(v_pre_2631_);
v___x_2666_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2631_, v_post_2633_, v_usedLetOnly_2634_, v_skipConstInApp_2635_, v_skipInstances_2636_, v_expr_2665_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v_a_2667_; size_t v___x_2668_; size_t v___x_2669_; uint8_t v___x_2670_; 
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
lean_inc(v_a_2667_);
lean_dec_ref(v___x_2666_);
v___x_2668_ = lean_ptr_addr(v_expr_2665_);
v___x_2669_ = lean_ptr_addr(v_a_2667_);
v___x_2670_ = lean_usize_dec_eq(v___x_2668_, v___x_2669_);
if (v___x_2670_ == 0)
{
lean_object* v___x_2671_; lean_object* v___x_2672_; 
lean_inc(v_data_2664_);
lean_dec_ref(v___y_2651_);
v___x_2671_ = l_Lean_Expr_mdata___override(v_data_2664_, v_a_2667_);
v___x_2672_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2631_, v_post_2633_, v_usedLetOnly_2634_, v_skipConstInApp_2635_, v_skipInstances_2636_, v___x_2671_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_);
return v___x_2672_;
}
else
{
lean_object* v___x_2673_; 
lean_dec(v_a_2667_);
v___x_2673_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2631_, v_post_2633_, v_usedLetOnly_2634_, v_skipConstInApp_2635_, v_skipInstances_2636_, v___y_2651_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_);
return v___x_2673_;
}
}
else
{
lean_dec_ref(v___y_2651_);
lean_dec_ref(v_post_2633_);
lean_dec_ref(v_pre_2631_);
return v___x_2666_;
}
}
case 11:
{
lean_object* v_typeName_2674_; lean_object* v_idx_2675_; lean_object* v_struct_2676_; lean_object* v___x_2677_; 
v_typeName_2674_ = lean_ctor_get(v___y_2651_, 0);
v_idx_2675_ = lean_ctor_get(v___y_2651_, 1);
v_struct_2676_ = lean_ctor_get(v___y_2651_, 2);
lean_inc_ref(v_struct_2676_);
lean_inc_ref(v_post_2633_);
lean_inc_ref(v_pre_2631_);
v___x_2677_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2631_, v_post_2633_, v_usedLetOnly_2634_, v_skipConstInApp_2635_, v_skipInstances_2636_, v_struct_2676_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_object* v_a_2678_; size_t v___x_2679_; size_t v___x_2680_; uint8_t v___x_2681_; 
v_a_2678_ = lean_ctor_get(v___x_2677_, 0);
lean_inc(v_a_2678_);
lean_dec_ref(v___x_2677_);
v___x_2679_ = lean_ptr_addr(v_struct_2676_);
v___x_2680_ = lean_ptr_addr(v_a_2678_);
v___x_2681_ = lean_usize_dec_eq(v___x_2679_, v___x_2680_);
if (v___x_2681_ == 0)
{
lean_object* v___x_2682_; lean_object* v___x_2683_; 
lean_inc(v_idx_2675_);
lean_inc(v_typeName_2674_);
lean_dec_ref(v___y_2651_);
v___x_2682_ = l_Lean_Expr_proj___override(v_typeName_2674_, v_idx_2675_, v_a_2678_);
v___x_2683_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2631_, v_post_2633_, v_usedLetOnly_2634_, v_skipConstInApp_2635_, v_skipInstances_2636_, v___x_2682_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_);
return v___x_2683_;
}
else
{
lean_object* v___x_2684_; 
lean_dec(v_a_2678_);
v___x_2684_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2631_, v_post_2633_, v_usedLetOnly_2634_, v_skipConstInApp_2635_, v_skipInstances_2636_, v___y_2651_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_);
return v___x_2684_;
}
}
else
{
lean_dec_ref(v___y_2651_);
lean_dec_ref(v_post_2633_);
lean_dec_ref(v_pre_2631_);
return v___x_2677_;
}
}
default: 
{
lean_object* v___x_2685_; 
v___x_2685_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2631_, v_post_2633_, v_usedLetOnly_2634_, v_skipConstInApp_2635_, v_skipInstances_2636_, v___y_2651_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_);
return v___x_2685_;
}
}
}
}
}
else
{
lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2702_; 
lean_dec_ref(v_post_2633_);
lean_dec_ref(v_e_2632_);
lean_dec_ref(v_pre_2631_);
v_a_2695_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2697_ = v___x_2645_;
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v___x_2645_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2700_; 
if (v_isShared_2698_ == 0)
{
v___x_2700_ = v___x_2697_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_a_2695_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
}
else
{
lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2710_; 
lean_dec_ref(v_post_2633_);
lean_dec_ref(v_e_2632_);
lean_dec_ref(v_pre_2631_);
v_a_2703_ = lean_ctor_get(v___x_2644_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2705_ = v___x_2644_;
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_dec(v___x_2644_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2708_; 
if (v_isShared_2706_ == 0)
{
v___x_2708_ = v___x_2705_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_a_2703_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
return v___x_2708_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___boxed(lean_object* v___x_2711_, lean_object* v_pre_2712_, lean_object* v_e_2713_, lean_object* v_post_2714_, lean_object* v_usedLetOnly_2715_, lean_object* v_skipConstInApp_2716_, lean_object* v_skipInstances_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
uint8_t v_usedLetOnly_boxed_2725_; uint8_t v_skipConstInApp_boxed_2726_; uint8_t v_skipInstances_boxed_2727_; lean_object* v_res_2728_; 
v_usedLetOnly_boxed_2725_ = lean_unbox(v_usedLetOnly_2715_);
v_skipConstInApp_boxed_2726_ = lean_unbox(v_skipConstInApp_2716_);
v_skipInstances_boxed_2727_ = lean_unbox(v_skipInstances_2717_);
v_res_2728_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1(v___x_2711_, v_pre_2712_, v_e_2713_, v_post_2714_, v_usedLetOnly_boxed_2725_, v_skipConstInApp_boxed_2726_, v_skipInstances_boxed_2727_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
lean_dec(v___y_2719_);
lean_dec(v___y_2718_);
return v_res_2728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(lean_object* v_pre_2729_, lean_object* v_post_2730_, uint8_t v_usedLetOnly_2731_, uint8_t v_skipConstInApp_2732_, uint8_t v_skipInstances_2733_, lean_object* v_e_2734_, lean_object* v_a_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_){
_start:
{
lean_object* v___x_2742_; lean_object* v___x_2743_; 
lean_inc(v_a_2735_);
v___x_2742_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2742_, 0, lean_box(0));
lean_closure_set(v___x_2742_, 1, lean_box(0));
lean_closure_set(v___x_2742_, 2, v_a_2735_);
v___x_2743_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(lean_box(0), v___x_2742_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
if (lean_obj_tag(v___x_2743_) == 0)
{
lean_object* v_a_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2778_; 
v_a_2744_ = lean_ctor_get(v___x_2743_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2743_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2746_ = v___x_2743_;
v_isShared_2747_ = v_isSharedCheck_2778_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_a_2744_);
lean_dec(v___x_2743_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2778_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2748_; 
v___x_2748_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(v_a_2744_, v_e_2734_);
lean_dec(v_a_2744_);
if (lean_obj_tag(v___x_2748_) == 0)
{
lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___f_2753_; lean_object* v___x_2754_; 
lean_del_object(v___x_2746_);
v___x_2749_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___closed__0));
v___x_2750_ = lean_box(v_usedLetOnly_2731_);
v___x_2751_ = lean_box(v_skipConstInApp_2732_);
v___x_2752_ = lean_box(v_skipInstances_2733_);
lean_inc_ref(v_e_2734_);
v___f_2753_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___boxed), 14, 7);
lean_closure_set(v___f_2753_, 0, v___x_2749_);
lean_closure_set(v___f_2753_, 1, v_pre_2729_);
lean_closure_set(v___f_2753_, 2, v_e_2734_);
lean_closure_set(v___f_2753_, 3, v_post_2730_);
lean_closure_set(v___f_2753_, 4, v___x_2750_);
lean_closure_set(v___f_2753_, 5, v___x_2751_);
lean_closure_set(v___f_2753_, 6, v___x_2752_);
v___x_2754_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v___f_2753_, v_a_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_object* v_a_2755_; lean_object* v___f_2756_; lean_object* v___x_2757_; 
v_a_2755_ = lean_ctor_get(v___x_2754_, 0);
lean_inc_n(v_a_2755_, 2);
lean_dec_ref(v___x_2754_);
lean_inc(v_a_2735_);
v___f_2756_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2756_, 0, v_a_2735_);
lean_closure_set(v___f_2756_, 1, v_e_2734_);
lean_closure_set(v___f_2756_, 2, v_a_2755_);
v___x_2757_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(lean_box(0), v___f_2756_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
if (lean_obj_tag(v___x_2757_) == 0)
{
lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2764_; 
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2764_ == 0)
{
lean_object* v_unused_2765_; 
v_unused_2765_ = lean_ctor_get(v___x_2757_, 0);
lean_dec(v_unused_2765_);
v___x_2759_ = v___x_2757_;
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
else
{
lean_dec(v___x_2757_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2762_; 
if (v_isShared_2760_ == 0)
{
lean_ctor_set(v___x_2759_, 0, v_a_2755_);
v___x_2762_ = v___x_2759_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_a_2755_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
}
else
{
lean_object* v_a_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2773_; 
lean_dec(v_a_2755_);
v_a_2766_ = lean_ctor_get(v___x_2757_, 0);
v_isSharedCheck_2773_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2768_ = v___x_2757_;
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_a_2766_);
lean_dec(v___x_2757_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2771_; 
if (v_isShared_2769_ == 0)
{
v___x_2771_ = v___x_2768_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_a_2766_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
}
}
else
{
lean_dec_ref(v_e_2734_);
return v___x_2754_;
}
}
else
{
lean_object* v_val_2774_; lean_object* v___x_2776_; 
lean_dec_ref(v_e_2734_);
lean_dec_ref(v_post_2730_);
lean_dec_ref(v_pre_2729_);
v_val_2774_ = lean_ctor_get(v___x_2748_, 0);
lean_inc(v_val_2774_);
lean_dec_ref(v___x_2748_);
if (v_isShared_2747_ == 0)
{
lean_ctor_set(v___x_2746_, 0, v_val_2774_);
v___x_2776_ = v___x_2746_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_val_2774_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
}
else
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2786_; 
lean_dec_ref(v_e_2734_);
lean_dec_ref(v_post_2730_);
lean_dec_ref(v_pre_2729_);
v_a_2779_ = lean_ctor_get(v___x_2743_, 0);
v_isSharedCheck_2786_ = !lean_is_exclusive(v___x_2743_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2781_ = v___x_2743_;
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2743_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2784_; 
if (v_isShared_2782_ == 0)
{
v___x_2784_ = v___x_2781_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_a_2779_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0___boxed(lean_object* v_fvars_2787_, lean_object* v_pre_2788_, lean_object* v_post_2789_, lean_object* v_usedLetOnly_2790_, lean_object* v_skipConstInApp_2791_, lean_object* v_skipInstances_2792_, lean_object* v_body_2793_, lean_object* v_x_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_){
_start:
{
uint8_t v_usedLetOnly_boxed_2802_; uint8_t v_skipConstInApp_boxed_2803_; uint8_t v_skipInstances_boxed_2804_; lean_object* v_res_2805_; 
v_usedLetOnly_boxed_2802_ = lean_unbox(v_usedLetOnly_2790_);
v_skipConstInApp_boxed_2803_ = lean_unbox(v_skipConstInApp_2791_);
v_skipInstances_boxed_2804_ = lean_unbox(v_skipInstances_2792_);
v_res_2805_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0(v_fvars_2787_, v_pre_2788_, v_post_2789_, v_usedLetOnly_boxed_2802_, v_skipConstInApp_boxed_2803_, v_skipInstances_boxed_2804_, v_body_2793_, v_x_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec(v___y_2795_);
return v_res_2805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(lean_object* v_pre_2806_, lean_object* v_post_2807_, uint8_t v_usedLetOnly_2808_, uint8_t v_skipConstInApp_2809_, uint8_t v_skipInstances_2810_, lean_object* v_fvars_2811_, lean_object* v_e_2812_, lean_object* v_a_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_){
_start:
{
if (lean_obj_tag(v_e_2812_) == 7)
{
lean_object* v_binderName_2820_; lean_object* v_binderType_2821_; lean_object* v_body_2822_; uint8_t v_binderInfo_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; 
v_binderName_2820_ = lean_ctor_get(v_e_2812_, 0);
lean_inc(v_binderName_2820_);
v_binderType_2821_ = lean_ctor_get(v_e_2812_, 1);
lean_inc_ref(v_binderType_2821_);
v_body_2822_ = lean_ctor_get(v_e_2812_, 2);
lean_inc_ref(v_body_2822_);
v_binderInfo_2823_ = lean_ctor_get_uint8(v_e_2812_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_2812_);
v___x_2824_ = lean_expr_instantiate_rev(v_binderType_2821_, v_fvars_2811_);
lean_dec_ref(v_binderType_2821_);
lean_inc_ref(v_post_2807_);
lean_inc_ref(v_pre_2806_);
v___x_2825_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2806_, v_post_2807_, v_usedLetOnly_2808_, v_skipConstInApp_2809_, v_skipInstances_2810_, v___x_2824_, v_a_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v_a_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___f_2830_; uint8_t v___x_2831_; lean_object* v___x_2832_; 
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
lean_inc(v_a_2826_);
lean_dec_ref(v___x_2825_);
v___x_2827_ = lean_box(v_usedLetOnly_2808_);
v___x_2828_ = lean_box(v_skipConstInApp_2809_);
v___x_2829_ = lean_box(v_skipInstances_2810_);
v___f_2830_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0___boxed), 15, 7);
lean_closure_set(v___f_2830_, 0, v_fvars_2811_);
lean_closure_set(v___f_2830_, 1, v_pre_2806_);
lean_closure_set(v___f_2830_, 2, v_post_2807_);
lean_closure_set(v___f_2830_, 3, v___x_2827_);
lean_closure_set(v___f_2830_, 4, v___x_2828_);
lean_closure_set(v___f_2830_, 5, v___x_2829_);
lean_closure_set(v___f_2830_, 6, v_body_2822_);
v___x_2831_ = 0;
v___x_2832_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_2820_, v_binderInfo_2823_, v_a_2826_, v___f_2830_, v___x_2831_, v_a_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
return v___x_2832_;
}
else
{
lean_dec_ref(v_body_2822_);
lean_dec(v_binderName_2820_);
lean_dec_ref(v_fvars_2811_);
lean_dec_ref(v_post_2807_);
lean_dec_ref(v_pre_2806_);
return v___x_2825_;
}
}
else
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2833_ = lean_expr_instantiate_rev(v_e_2812_, v_fvars_2811_);
lean_dec_ref(v_e_2812_);
lean_inc_ref(v_post_2807_);
lean_inc_ref(v_pre_2806_);
v___x_2834_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2806_, v_post_2807_, v_usedLetOnly_2808_, v_skipConstInApp_2809_, v_skipInstances_2810_, v___x_2833_, v_a_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v_a_2835_; uint8_t v___x_2836_; uint8_t v___x_2837_; uint8_t v___x_2838_; lean_object* v___x_2839_; 
v_a_2835_ = lean_ctor_get(v___x_2834_, 0);
lean_inc(v_a_2835_);
lean_dec_ref(v___x_2834_);
v___x_2836_ = 0;
v___x_2837_ = 1;
v___x_2838_ = 1;
v___x_2839_ = l_Lean_Meta_mkForallFVars(v_fvars_2811_, v_a_2835_, v___x_2836_, v_usedLetOnly_2808_, v___x_2837_, v___x_2838_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
lean_dec_ref(v_fvars_2811_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v_a_2840_; lean_object* v___x_2841_; 
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
lean_inc(v_a_2840_);
lean_dec_ref(v___x_2839_);
v___x_2841_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2806_, v_post_2807_, v_usedLetOnly_2808_, v_skipConstInApp_2809_, v_skipInstances_2810_, v_a_2840_, v_a_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
return v___x_2841_;
}
else
{
lean_dec_ref(v_post_2807_);
lean_dec_ref(v_pre_2806_);
return v___x_2839_;
}
}
else
{
lean_dec_ref(v_fvars_2811_);
lean_dec_ref(v_post_2807_);
lean_dec_ref(v_pre_2806_);
return v___x_2834_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0(lean_object* v_fvars_2842_, lean_object* v_pre_2843_, lean_object* v_post_2844_, uint8_t v_usedLetOnly_2845_, uint8_t v_skipConstInApp_2846_, uint8_t v_skipInstances_2847_, lean_object* v_body_2848_, lean_object* v_x_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_){
_start:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; 
v___x_2857_ = lean_array_push(v_fvars_2842_, v_x_2849_);
v___x_2858_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(v_pre_2843_, v_post_2844_, v_usedLetOnly_2845_, v_skipConstInApp_2846_, v_skipInstances_2847_, v___x_2857_, v_body_2848_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_);
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_2859_, lean_object* v_post_2860_, lean_object* v_usedLetOnly_2861_, lean_object* v_skipConstInApp_2862_, lean_object* v_skipInstances_2863_, lean_object* v_e_2864_, lean_object* v_a_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_){
_start:
{
uint8_t v_usedLetOnly_boxed_2872_; uint8_t v_skipConstInApp_boxed_2873_; uint8_t v_skipInstances_boxed_2874_; lean_object* v_res_2875_; 
v_usedLetOnly_boxed_2872_ = lean_unbox(v_usedLetOnly_2861_);
v_skipConstInApp_boxed_2873_ = lean_unbox(v_skipConstInApp_2862_);
v_skipInstances_boxed_2874_ = lean_unbox(v_skipInstances_2863_);
v_res_2875_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2859_, v_post_2860_, v_usedLetOnly_boxed_2872_, v_skipConstInApp_boxed_2873_, v_skipInstances_boxed_2874_, v_e_2864_, v_a_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
lean_dec(v___y_2868_);
lean_dec_ref(v___y_2867_);
lean_dec(v___y_2866_);
lean_dec(v_a_2865_);
return v_res_2875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_2876_, lean_object* v_post_2877_, lean_object* v_usedLetOnly_2878_, lean_object* v_skipConstInApp_2879_, lean_object* v_skipInstances_2880_, lean_object* v_sz_2881_, lean_object* v_i_2882_, lean_object* v_bs_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_){
_start:
{
uint8_t v_usedLetOnly_boxed_2891_; uint8_t v_skipConstInApp_boxed_2892_; uint8_t v_skipInstances_boxed_2893_; size_t v_sz_boxed_2894_; size_t v_i_boxed_2895_; lean_object* v_res_2896_; 
v_usedLetOnly_boxed_2891_ = lean_unbox(v_usedLetOnly_2878_);
v_skipConstInApp_boxed_2892_ = lean_unbox(v_skipConstInApp_2879_);
v_skipInstances_boxed_2893_ = lean_unbox(v_skipInstances_2880_);
v_sz_boxed_2894_ = lean_unbox_usize(v_sz_2881_);
lean_dec(v_sz_2881_);
v_i_boxed_2895_ = lean_unbox_usize(v_i_2882_);
lean_dec(v_i_2882_);
v_res_2896_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(v_pre_2876_, v_post_2877_, v_usedLetOnly_boxed_2891_, v_skipConstInApp_boxed_2892_, v_skipInstances_boxed_2893_, v_sz_boxed_2894_, v_i_boxed_2895_, v_bs_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec(v___y_2884_);
return v_res_2896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___boxed(lean_object* v_pre_2897_, lean_object* v_post_2898_, lean_object* v_usedLetOnly_2899_, lean_object* v_skipConstInApp_2900_, lean_object* v_skipInstances_2901_, lean_object* v_e_2902_, lean_object* v_a_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_){
_start:
{
uint8_t v_usedLetOnly_boxed_2910_; uint8_t v_skipConstInApp_boxed_2911_; uint8_t v_skipInstances_boxed_2912_; lean_object* v_res_2913_; 
v_usedLetOnly_boxed_2910_ = lean_unbox(v_usedLetOnly_2899_);
v_skipConstInApp_boxed_2911_ = lean_unbox(v_skipConstInApp_2900_);
v_skipInstances_boxed_2912_ = lean_unbox(v_skipInstances_2901_);
v_res_2913_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2897_, v_post_2898_, v_usedLetOnly_boxed_2910_, v_skipConstInApp_boxed_2911_, v_skipInstances_boxed_2912_, v_e_2902_, v_a_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
lean_dec(v___y_2908_);
lean_dec_ref(v___y_2907_);
lean_dec(v___y_2906_);
lean_dec_ref(v___y_2905_);
lean_dec(v___y_2904_);
lean_dec(v_a_2903_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___boxed(lean_object* v_pre_2914_, lean_object* v_post_2915_, lean_object* v_usedLetOnly_2916_, lean_object* v_skipConstInApp_2917_, lean_object* v_skipInstances_2918_, lean_object* v_fvars_2919_, lean_object* v_e_2920_, lean_object* v_a_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
uint8_t v_usedLetOnly_boxed_2928_; uint8_t v_skipConstInApp_boxed_2929_; uint8_t v_skipInstances_boxed_2930_; lean_object* v_res_2931_; 
v_usedLetOnly_boxed_2928_ = lean_unbox(v_usedLetOnly_2916_);
v_skipConstInApp_boxed_2929_ = lean_unbox(v_skipConstInApp_2917_);
v_skipInstances_boxed_2930_ = lean_unbox(v_skipInstances_2918_);
v_res_2931_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(v_pre_2914_, v_post_2915_, v_usedLetOnly_boxed_2928_, v_skipConstInApp_boxed_2929_, v_skipInstances_boxed_2930_, v_fvars_2919_, v_e_2920_, v_a_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2923_);
lean_dec(v___y_2922_);
lean_dec(v_a_2921_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___boxed(lean_object* v_pre_2932_, lean_object* v_post_2933_, lean_object* v_usedLetOnly_2934_, lean_object* v_skipConstInApp_2935_, lean_object* v_skipInstances_2936_, lean_object* v_fvars_2937_, lean_object* v_e_2938_, lean_object* v_a_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_){
_start:
{
uint8_t v_usedLetOnly_boxed_2946_; uint8_t v_skipConstInApp_boxed_2947_; uint8_t v_skipInstances_boxed_2948_; lean_object* v_res_2949_; 
v_usedLetOnly_boxed_2946_ = lean_unbox(v_usedLetOnly_2934_);
v_skipConstInApp_boxed_2947_ = lean_unbox(v_skipConstInApp_2935_);
v_skipInstances_boxed_2948_ = lean_unbox(v_skipInstances_2936_);
v_res_2949_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(v_pre_2932_, v_post_2933_, v_usedLetOnly_boxed_2946_, v_skipConstInApp_boxed_2947_, v_skipInstances_boxed_2948_, v_fvars_2937_, v_e_2938_, v_a_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
lean_dec(v___y_2944_);
lean_dec_ref(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec_ref(v___y_2941_);
lean_dec(v___y_2940_);
lean_dec(v_a_2939_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___boxed(lean_object* v_pre_2950_, lean_object* v_post_2951_, lean_object* v_usedLetOnly_2952_, lean_object* v_skipConstInApp_2953_, lean_object* v_skipInstances_2954_, lean_object* v_fvars_2955_, lean_object* v_e_2956_, lean_object* v_a_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_){
_start:
{
uint8_t v_usedLetOnly_boxed_2964_; uint8_t v_skipConstInApp_boxed_2965_; uint8_t v_skipInstances_boxed_2966_; lean_object* v_res_2967_; 
v_usedLetOnly_boxed_2964_ = lean_unbox(v_usedLetOnly_2952_);
v_skipConstInApp_boxed_2965_ = lean_unbox(v_skipConstInApp_2953_);
v_skipInstances_boxed_2966_ = lean_unbox(v_skipInstances_2954_);
v_res_2967_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(v_pre_2950_, v_post_2951_, v_usedLetOnly_boxed_2964_, v_skipConstInApp_boxed_2965_, v_skipInstances_boxed_2966_, v_fvars_2955_, v_e_2956_, v_a_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
lean_dec(v___y_2962_);
lean_dec_ref(v___y_2961_);
lean_dec(v___y_2960_);
lean_dec_ref(v___y_2959_);
lean_dec(v___y_2958_);
lean_dec(v_a_2957_);
return v_res_2967_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_upperBound_2968_, lean_object* v___x_2969_, lean_object* v_pre_2970_, lean_object* v_post_2971_, lean_object* v_usedLetOnly_2972_, lean_object* v_skipConstInApp_2973_, lean_object* v_skipInstances_2974_, lean_object* v_a_2975_, lean_object* v_b_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_){
_start:
{
uint8_t v_usedLetOnly_boxed_2984_; uint8_t v_skipConstInApp_boxed_2985_; uint8_t v_skipInstances_boxed_2986_; lean_object* v_res_2987_; 
v_usedLetOnly_boxed_2984_ = lean_unbox(v_usedLetOnly_2972_);
v_skipConstInApp_boxed_2985_ = lean_unbox(v_skipConstInApp_2973_);
v_skipInstances_boxed_2986_ = lean_unbox(v_skipInstances_2974_);
v_res_2987_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(v_upperBound_2968_, v___x_2969_, v_pre_2970_, v_post_2971_, v_usedLetOnly_boxed_2984_, v_skipConstInApp_boxed_2985_, v_skipInstances_boxed_2986_, v_a_2975_, v_b_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2981_);
lean_dec(v___y_2980_);
lean_dec_ref(v___y_2979_);
lean_dec(v___y_2978_);
lean_dec(v___y_2977_);
lean_dec_ref(v___x_2969_);
lean_dec(v_upperBound_2968_);
return v_res_2987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8___boxed(lean_object* v_skipInstances_2988_, lean_object* v_pre_2989_, lean_object* v_post_2990_, lean_object* v_usedLetOnly_2991_, lean_object* v_skipConstInApp_2992_, lean_object* v_x_2993_, lean_object* v_x_2994_, lean_object* v_x_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_){
_start:
{
uint8_t v_skipInstances_boxed_3003_; uint8_t v_usedLetOnly_boxed_3004_; uint8_t v_skipConstInApp_boxed_3005_; lean_object* v_res_3006_; 
v_skipInstances_boxed_3003_ = lean_unbox(v_skipInstances_2988_);
v_usedLetOnly_boxed_3004_ = lean_unbox(v_usedLetOnly_2991_);
v_skipConstInApp_boxed_3005_ = lean_unbox(v_skipConstInApp_2992_);
v_res_3006_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(v_skipInstances_boxed_3003_, v_pre_2989_, v_post_2990_, v_usedLetOnly_boxed_3004_, v_skipConstInApp_boxed_3005_, v_x_2993_, v_x_2994_, v_x_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec_ref(v___y_2998_);
lean_dec(v___y_2997_);
lean_dec(v___y_2996_);
return v_res_3006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_object* v_00_u03b1_3007_, lean_object* v_x_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_){
_start:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3015_ = lean_apply_1(v_x_3008_, lean_box(0));
v___x_3016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3016_, 0, v___x_3015_);
return v___x_3016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0___boxed(lean_object* v_00_u03b1_3017_, lean_object* v_x_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_){
_start:
{
lean_object* v_res_3025_; 
v_res_3025_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(v_00_u03b1_3017_, v_x_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_);
lean_dec(v___y_3023_);
lean_dec_ref(v___y_3022_);
lean_dec(v___y_3021_);
lean_dec_ref(v___y_3020_);
lean_dec(v___y_3019_);
return v_res_3025_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___x_3026_ = lean_box(0);
v___x_3027_ = lean_unsigned_to_nat(16u);
v___x_3028_ = lean_mk_array(v___x_3027_, v___x_3026_);
return v___x_3028_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; 
v___x_3029_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0);
v___x_3030_ = lean_unsigned_to_nat(0u);
v___x_3031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3030_);
lean_ctor_set(v___x_3031_, 1, v___x_3029_);
return v___x_3031_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2(void){
_start:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3032_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1);
v___x_3033_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3033_, 0, lean_box(0));
lean_closure_set(v___x_3033_, 1, lean_box(0));
lean_closure_set(v___x_3033_, 2, v___x_3032_);
return v___x_3033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(lean_object* v_input_3034_, lean_object* v_pre_3035_, lean_object* v_post_3036_, uint8_t v_usedLetOnly_3037_, uint8_t v_skipConstInApp_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_){
_start:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v_a_3047_; uint8_t v___x_3048_; lean_object* v___x_3049_; 
v___x_3045_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2);
v___x_3046_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_box(0), v___x_3045_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_);
v_a_3047_ = lean_ctor_get(v___x_3046_, 0);
lean_inc(v_a_3047_);
lean_dec_ref(v___x_3046_);
v___x_3048_ = 0;
v___x_3049_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_3035_, v_post_3036_, v_usedLetOnly_3037_, v_skipConstInApp_3038_, v___x_3048_, v_input_3034_, v_a_3047_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_);
if (lean_obj_tag(v___x_3049_) == 0)
{
lean_object* v_a_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3059_; 
v_a_3050_ = lean_ctor_get(v___x_3049_, 0);
lean_inc(v_a_3050_);
lean_dec_ref(v___x_3049_);
v___x_3051_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3051_, 0, lean_box(0));
lean_closure_set(v___x_3051_, 1, lean_box(0));
lean_closure_set(v___x_3051_, 2, v_a_3047_);
v___x_3052_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_box(0), v___x_3051_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3059_ == 0)
{
lean_object* v_unused_3060_; 
v_unused_3060_ = lean_ctor_get(v___x_3052_, 0);
lean_dec(v_unused_3060_);
v___x_3054_ = v___x_3052_;
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
else
{
lean_dec(v___x_3052_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3057_; 
if (v_isShared_3055_ == 0)
{
lean_ctor_set(v___x_3054_, 0, v_a_3050_);
v___x_3057_ = v___x_3054_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_a_3050_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
return v___x_3057_;
}
}
}
else
{
lean_dec(v_a_3047_);
return v___x_3049_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___boxed(lean_object* v_input_3061_, lean_object* v_pre_3062_, lean_object* v_post_3063_, lean_object* v_usedLetOnly_3064_, lean_object* v_skipConstInApp_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_){
_start:
{
uint8_t v_usedLetOnly_boxed_3072_; uint8_t v_skipConstInApp_boxed_3073_; lean_object* v_res_3074_; 
v_usedLetOnly_boxed_3072_ = lean_unbox(v_usedLetOnly_3064_);
v_skipConstInApp_boxed_3073_ = lean_unbox(v_skipConstInApp_3065_);
v_res_3074_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(v_input_3061_, v_pre_3062_, v_post_3063_, v_usedLetOnly_boxed_3072_, v_skipConstInApp_boxed_3073_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec(v___y_3066_);
return v_res_3074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore(lean_object* v_e_3076_, uint8_t v_elimTrivial_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_){
_start:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v_pre_3086_; lean_object* v___f_3087_; uint8_t v___x_3088_; lean_object* v___x_3089_; 
v___x_3083_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3);
v___x_3084_ = lean_st_mk_ref(v___x_3083_);
v___x_3085_ = lean_box(v_elimTrivial_3077_);
v_pre_3086_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___boxed), 8, 1);
lean_closure_set(v_pre_3086_, 0, v___x_3085_);
v___f_3087_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___closed__0));
v___x_3088_ = 0;
v___x_3089_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(v_e_3076_, v_pre_3086_, v___f_3087_, v___x_3088_, v___x_3088_, v___x_3084_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_);
if (lean_obj_tag(v___x_3089_) == 0)
{
lean_object* v_a_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3098_; 
v_a_3090_ = lean_ctor_get(v___x_3089_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3092_ = v___x_3089_;
v_isShared_3093_ = v_isSharedCheck_3098_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_a_3090_);
lean_dec(v___x_3089_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3098_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3094_; lean_object* v___x_3096_; 
v___x_3094_ = lean_st_ref_get(v___x_3084_);
lean_dec(v___x_3084_);
lean_dec(v___x_3094_);
if (v_isShared_3093_ == 0)
{
v___x_3096_ = v___x_3092_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_a_3090_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
else
{
lean_dec(v___x_3084_);
return v___x_3089_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___boxed(lean_object* v_e_3099_, lean_object* v_elimTrivial_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_){
_start:
{
uint8_t v_elimTrivial_boxed_3106_; lean_object* v_res_3107_; 
v_elimTrivial_boxed_3106_ = lean_unbox(v_elimTrivial_3100_);
v_res_3107_ = l_Lean_Elab_Tactic_Do_elimLetsCore(v_e_3099_, v_elimTrivial_boxed_3106_, v_a_3101_, v_a_3102_, v_a_3103_, v_a_3104_);
lean_dec(v_a_3104_);
lean_dec_ref(v_a_3103_);
lean_dec(v_a_3102_);
lean_dec_ref(v_a_3101_);
return v_res_3107_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(lean_object* v_upperBound_3108_, lean_object* v___x_3109_, lean_object* v_pre_3110_, lean_object* v_post_3111_, uint8_t v_usedLetOnly_3112_, uint8_t v_skipConstInApp_3113_, uint8_t v_skipInstances_3114_, lean_object* v___x_3115_, lean_object* v_inst_3116_, lean_object* v_R_3117_, lean_object* v_a_3118_, lean_object* v_b_3119_, lean_object* v_c_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_){
_start:
{
lean_object* v___x_3128_; 
v___x_3128_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(v_upperBound_3108_, v___x_3109_, v_pre_3110_, v_post_3111_, v_usedLetOnly_3112_, v_skipConstInApp_3113_, v_skipInstances_3114_, v_a_3118_, v_b_3119_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_);
return v___x_3128_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___boxed(lean_object** _args){
lean_object* v_upperBound_3129_ = _args[0];
lean_object* v___x_3130_ = _args[1];
lean_object* v_pre_3131_ = _args[2];
lean_object* v_post_3132_ = _args[3];
lean_object* v_usedLetOnly_3133_ = _args[4];
lean_object* v_skipConstInApp_3134_ = _args[5];
lean_object* v_skipInstances_3135_ = _args[6];
lean_object* v___x_3136_ = _args[7];
lean_object* v_inst_3137_ = _args[8];
lean_object* v_R_3138_ = _args[9];
lean_object* v_a_3139_ = _args[10];
lean_object* v_b_3140_ = _args[11];
lean_object* v_c_3141_ = _args[12];
lean_object* v___y_3142_ = _args[13];
lean_object* v___y_3143_ = _args[14];
lean_object* v___y_3144_ = _args[15];
lean_object* v___y_3145_ = _args[16];
lean_object* v___y_3146_ = _args[17];
lean_object* v___y_3147_ = _args[18];
lean_object* v___y_3148_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_3149_; uint8_t v_skipConstInApp_boxed_3150_; uint8_t v_skipInstances_boxed_3151_; lean_object* v_res_3152_; 
v_usedLetOnly_boxed_3149_ = lean_unbox(v_usedLetOnly_3133_);
v_skipConstInApp_boxed_3150_ = lean_unbox(v_skipConstInApp_3134_);
v_skipInstances_boxed_3151_ = lean_unbox(v_skipInstances_3135_);
v_res_3152_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(v_upperBound_3129_, v___x_3130_, v_pre_3131_, v_post_3132_, v_usedLetOnly_boxed_3149_, v_skipConstInApp_boxed_3150_, v_skipInstances_boxed_3151_, v___x_3136_, v_inst_3137_, v_R_3138_, v_a_3139_, v_b_3140_, v_c_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_);
lean_dec(v___y_3147_);
lean_dec_ref(v___y_3146_);
lean_dec(v___y_3145_);
lean_dec_ref(v___y_3144_);
lean_dec(v___y_3143_);
lean_dec(v___y_3142_);
lean_dec(v___x_3136_);
lean_dec_ref(v___x_3130_);
lean_dec(v_upperBound_3129_);
return v_res_3152_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_3153_, lean_object* v_m_3154_, lean_object* v_a_3155_){
_start:
{
lean_object* v___x_3156_; 
v___x_3156_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(v_m_3154_, v_a_3155_);
return v___x_3156_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b2_3157_, lean_object* v_m_3158_, lean_object* v_a_3159_){
_start:
{
lean_object* v_res_3160_; 
v_res_3160_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4(v_00_u03b2_3157_, v_m_3158_, v_a_3159_);
lean_dec_ref(v_a_3159_);
lean_dec_ref(v_m_3158_);
return v_res_3160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_3161_, lean_object* v_name_3162_, uint8_t v_bi_3163_, lean_object* v_type_3164_, lean_object* v_k_3165_, uint8_t v_kind_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_){
_start:
{
lean_object* v___x_3174_; 
v___x_3174_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_name_3162_, v_bi_3163_, v_type_3164_, v_k_3165_, v_kind_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_);
return v___x_3174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_3175_, lean_object* v_name_3176_, lean_object* v_bi_3177_, lean_object* v_type_3178_, lean_object* v_k_3179_, lean_object* v_kind_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
uint8_t v_bi_boxed_3188_; uint8_t v_kind_boxed_3189_; lean_object* v_res_3190_; 
v_bi_boxed_3188_ = lean_unbox(v_bi_3177_);
v_kind_boxed_3189_ = lean_unbox(v_kind_3180_);
v_res_3190_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_3175_, v_name_3176_, v_bi_boxed_3188_, v_type_3178_, v_k_3179_, v_kind_boxed_3189_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
lean_dec(v___y_3182_);
lean_dec(v___y_3181_);
return v_res_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10(lean_object* v_00_u03b1_3191_, lean_object* v_name_3192_, lean_object* v_type_3193_, lean_object* v_val_3194_, lean_object* v_k_3195_, uint8_t v_nondep_3196_, uint8_t v_kind_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_){
_start:
{
lean_object* v___x_3205_; 
v___x_3205_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_name_3192_, v_type_3193_, v_val_3194_, v_k_3195_, v_nondep_3196_, v_kind_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_);
return v___x_3205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___boxed(lean_object* v_00_u03b1_3206_, lean_object* v_name_3207_, lean_object* v_type_3208_, lean_object* v_val_3209_, lean_object* v_k_3210_, lean_object* v_nondep_3211_, lean_object* v_kind_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_){
_start:
{
uint8_t v_nondep_boxed_3220_; uint8_t v_kind_boxed_3221_; lean_object* v_res_3222_; 
v_nondep_boxed_3220_ = lean_unbox(v_nondep_3211_);
v_kind_boxed_3221_ = lean_unbox(v_kind_3212_);
v_res_3222_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10(v_00_u03b1_3206_, v_name_3207_, v_type_3208_, v_val_3209_, v_k_3210_, v_nondep_boxed_3220_, v_kind_boxed_3221_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
lean_dec(v___y_3218_);
lean_dec_ref(v___y_3217_);
lean_dec(v___y_3216_);
lean_dec_ref(v___y_3215_);
lean_dec(v___y_3214_);
lean_dec(v___y_3213_);
return v_res_3222_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13(lean_object* v_00_u03b1_3223_, lean_object* v_ref_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_){
_start:
{
lean_object* v___x_3230_; 
v___x_3230_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_3224_);
return v___x_3230_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___boxed(lean_object* v_00_u03b1_3231_, lean_object* v_ref_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_){
_start:
{
lean_object* v_res_3238_; 
v_res_3238_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13(v_00_u03b1_3231_, v_ref_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
return v_res_3238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9(lean_object* v_00_u03b1_3239_, lean_object* v_x_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_){
_start:
{
lean_object* v___x_3248_; 
v___x_3248_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v_x_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_);
return v___x_3248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___boxed(lean_object* v_00_u03b1_3249_, lean_object* v_x_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_){
_start:
{
lean_object* v_res_3258_; 
v_res_3258_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9(v_00_u03b1_3249_, v_x_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_);
lean_dec(v___y_3256_);
lean_dec_ref(v___y_3255_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec(v___y_3251_);
return v_res_3258_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10(lean_object* v_00_u03b2_3259_, lean_object* v_m_3260_, lean_object* v_a_3261_, lean_object* v_b_3262_){
_start:
{
lean_object* v___x_3263_; 
v___x_3263_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(v_m_3260_, v_a_3261_, v_b_3262_);
return v___x_3263_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5(lean_object* v_00_u03b2_3264_, lean_object* v_a_3265_, lean_object* v_x_3266_){
_start:
{
lean_object* v___x_3267_; 
v___x_3267_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(v_a_3265_, v_x_3266_);
return v___x_3267_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___boxed(lean_object* v_00_u03b2_3268_, lean_object* v_a_3269_, lean_object* v_x_3270_){
_start:
{
lean_object* v_res_3271_; 
v_res_3271_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5(v_00_u03b2_3268_, v_a_3269_, v_x_3270_);
lean_dec(v_x_3270_);
lean_dec_ref(v_a_3269_);
return v_res_3271_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15(lean_object* v_00_u03b2_3272_, lean_object* v_a_3273_, lean_object* v_x_3274_){
_start:
{
uint8_t v___x_3275_; 
v___x_3275_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_a_3273_, v_x_3274_);
return v___x_3275_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___boxed(lean_object* v_00_u03b2_3276_, lean_object* v_a_3277_, lean_object* v_x_3278_){
_start:
{
uint8_t v_res_3279_; lean_object* v_r_3280_; 
v_res_3279_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15(v_00_u03b2_3276_, v_a_3277_, v_x_3278_);
lean_dec(v_x_3278_);
lean_dec_ref(v_a_3277_);
v_r_3280_ = lean_box(v_res_3279_);
return v_r_3280_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16(lean_object* v_00_u03b2_3281_, lean_object* v_data_3282_){
_start:
{
lean_object* v___x_3283_; 
v___x_3283_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(v_data_3282_);
return v___x_3283_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17(lean_object* v_00_u03b2_3284_, lean_object* v_a_3285_, lean_object* v_b_3286_, lean_object* v_x_3287_){
_start:
{
lean_object* v___x_3288_; 
v___x_3288_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(v_a_3285_, v_b_3286_, v_x_3287_);
return v___x_3288_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17(lean_object* v_00_u03b2_3289_, lean_object* v_i_3290_, lean_object* v_source_3291_, lean_object* v_target_3292_){
_start:
{
lean_object* v___x_3293_; 
v___x_3293_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v_i_3290_, v_source_3291_, v_target_3292_);
return v___x_3293_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18(lean_object* v_00_u03b2_3294_, lean_object* v_x_3295_, lean_object* v_x_3296_){
_start:
{
lean_object* v___x_3297_; 
v___x_3297_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_x_3295_, v_x_3296_);
return v___x_3297_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(lean_object* v_mvarId_3298_, lean_object* v_x_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_){
_start:
{
lean_object* v___x_3305_; 
v___x_3305_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3298_, v_x_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_);
if (lean_obj_tag(v___x_3305_) == 0)
{
lean_object* v_a_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3313_; 
v_a_3306_ = lean_ctor_get(v___x_3305_, 0);
v_isSharedCheck_3313_ = !lean_is_exclusive(v___x_3305_);
if (v_isSharedCheck_3313_ == 0)
{
v___x_3308_ = v___x_3305_;
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_a_3306_);
lean_dec(v___x_3305_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v___x_3311_; 
if (v_isShared_3309_ == 0)
{
v___x_3311_ = v___x_3308_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v_a_3306_);
v___x_3311_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
return v___x_3311_;
}
}
}
else
{
lean_object* v_a_3314_; lean_object* v___x_3316_; uint8_t v_isShared_3317_; uint8_t v_isSharedCheck_3321_; 
v_a_3314_ = lean_ctor_get(v___x_3305_, 0);
v_isSharedCheck_3321_ = !lean_is_exclusive(v___x_3305_);
if (v_isSharedCheck_3321_ == 0)
{
v___x_3316_ = v___x_3305_;
v_isShared_3317_ = v_isSharedCheck_3321_;
goto v_resetjp_3315_;
}
else
{
lean_inc(v_a_3314_);
lean_dec(v___x_3305_);
v___x_3316_ = lean_box(0);
v_isShared_3317_ = v_isSharedCheck_3321_;
goto v_resetjp_3315_;
}
v_resetjp_3315_:
{
lean_object* v___x_3319_; 
if (v_isShared_3317_ == 0)
{
v___x_3319_ = v___x_3316_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v_a_3314_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg___boxed(lean_object* v_mvarId_3322_, lean_object* v_x_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
lean_object* v_res_3329_; 
v_res_3329_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(v_mvarId_3322_, v_x_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3326_);
lean_dec(v___y_3325_);
lean_dec_ref(v___y_3324_);
return v_res_3329_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3(lean_object* v_00_u03b1_3330_, lean_object* v_mvarId_3331_, lean_object* v_x_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_){
_start:
{
lean_object* v___x_3338_; 
v___x_3338_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(v_mvarId_3331_, v_x_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_);
return v___x_3338_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___boxed(lean_object* v_00_u03b1_3339_, lean_object* v_mvarId_3340_, lean_object* v_x_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_){
_start:
{
lean_object* v_res_3347_; 
v_res_3347_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3(v_00_u03b1_3339_, v_mvarId_3340_, v_x_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_);
lean_dec(v___y_3345_);
lean_dec_ref(v___y_3344_);
lean_dec(v___y_3343_);
lean_dec_ref(v___y_3342_);
return v_res_3347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(uint8_t v_elimTrivial_3348_, lean_object* v_as_3349_, size_t v_sz_3350_, size_t v_i_3351_, lean_object* v_b_3352_){
_start:
{
uint8_t v___x_3354_; 
v___x_3354_ = lean_usize_dec_lt(v_i_3351_, v_sz_3350_);
if (v___x_3354_ == 0)
{
lean_object* v___x_3355_; 
v___x_3355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3355_, 0, v_b_3352_);
return v___x_3355_;
}
else
{
lean_object* v_snd_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3403_; 
v_snd_3356_ = lean_ctor_get(v_b_3352_, 1);
v_isSharedCheck_3403_ = !lean_is_exclusive(v_b_3352_);
if (v_isSharedCheck_3403_ == 0)
{
lean_object* v_unused_3404_; 
v_unused_3404_ = lean_ctor_get(v_b_3352_, 0);
lean_dec(v_unused_3404_);
v___x_3358_ = v_b_3352_;
v_isShared_3359_ = v_isSharedCheck_3403_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_snd_3356_);
lean_dec(v_b_3352_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3403_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
lean_object* v___x_3360_; lean_object* v_a_3362_; lean_object* v_a_3369_; 
v___x_3360_ = lean_box(0);
v_a_3369_ = lean_array_uget_borrowed(v_as_3349_, v_i_3351_);
if (lean_obj_tag(v_a_3369_) == 0)
{
v_a_3362_ = v_snd_3356_;
goto v___jp_3361_;
}
else
{
lean_object* v_val_3370_; lean_object* v_fst_3371_; lean_object* v_snd_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3402_; 
v_val_3370_ = lean_ctor_get(v_a_3369_, 0);
v_fst_3371_ = lean_ctor_get(v_snd_3356_, 0);
v_snd_3372_ = lean_ctor_get(v_snd_3356_, 1);
v_isSharedCheck_3402_ = !lean_is_exclusive(v_snd_3356_);
if (v_isSharedCheck_3402_ == 0)
{
v___x_3374_ = v_snd_3356_;
v_isShared_3375_ = v_isSharedCheck_3402_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_snd_3372_);
lean_inc(v_fst_3371_);
lean_dec(v_snd_3356_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3402_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
uint8_t v___x_3376_; lean_object* v___x_3377_; 
v___x_3376_ = 0;
v___x_3377_ = l_Lean_LocalDecl_value_x3f(v_val_3370_, v___x_3376_);
if (lean_obj_tag(v___x_3377_) == 1)
{
lean_object* v_val_3378_; lean_object* v___x_3379_; 
v_val_3378_ = lean_ctor_get(v___x_3377_, 0);
lean_inc(v_val_3378_);
lean_dec_ref(v___x_3377_);
v___x_3379_ = l_Lean_LocalDecl_type(v_val_3370_);
if (lean_obj_tag(v___x_3379_) == 10)
{
lean_object* v_data_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; uint8_t v___x_3384_; uint8_t v___x_3385_; 
v_data_3380_ = lean_ctor_get(v___x_3379_, 0);
lean_inc(v_data_3380_);
lean_dec_ref(v___x_3379_);
v___x_3381_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_3382_ = lean_unsigned_to_nat(2u);
v___x_3383_ = l_Lean_KVMap_getNat(v_data_3380_, v___x_3381_, v___x_3382_);
lean_dec(v_data_3380_);
v___x_3384_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3383_);
lean_dec(v___x_3383_);
v___x_3385_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3384_, v_val_3378_, v_elimTrivial_3348_);
if (v___x_3385_ == 0)
{
lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3391_; 
v___x_3386_ = l_Lean_LocalDecl_fvarId(v_val_3370_);
v___x_3387_ = l_Lean_mkFVar(v___x_3386_);
v___x_3388_ = lean_array_push(v_fst_3371_, v___x_3387_);
v___x_3389_ = lean_array_push(v_snd_3372_, v_val_3378_);
if (v_isShared_3375_ == 0)
{
lean_ctor_set(v___x_3374_, 1, v___x_3389_);
lean_ctor_set(v___x_3374_, 0, v___x_3388_);
v___x_3391_ = v___x_3374_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v___x_3388_);
lean_ctor_set(v_reuseFailAlloc_3392_, 1, v___x_3389_);
v___x_3391_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
v_a_3362_ = v___x_3391_;
goto v___jp_3361_;
}
}
else
{
lean_object* v___x_3394_; 
lean_dec(v_val_3378_);
if (v_isShared_3375_ == 0)
{
v___x_3394_ = v___x_3374_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_fst_3371_);
lean_ctor_set(v_reuseFailAlloc_3395_, 1, v_snd_3372_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
v_a_3362_ = v___x_3394_;
goto v___jp_3361_;
}
}
}
else
{
lean_object* v___x_3397_; 
lean_dec_ref(v___x_3379_);
lean_dec(v_val_3378_);
if (v_isShared_3375_ == 0)
{
v___x_3397_ = v___x_3374_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v_fst_3371_);
lean_ctor_set(v_reuseFailAlloc_3398_, 1, v_snd_3372_);
v___x_3397_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
v_a_3362_ = v___x_3397_;
goto v___jp_3361_;
}
}
}
else
{
lean_object* v___x_3400_; 
lean_dec(v___x_3377_);
if (v_isShared_3375_ == 0)
{
v___x_3400_ = v___x_3374_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v_fst_3371_);
lean_ctor_set(v_reuseFailAlloc_3401_, 1, v_snd_3372_);
v___x_3400_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
v_a_3362_ = v___x_3400_;
goto v___jp_3361_;
}
}
}
}
v___jp_3361_:
{
lean_object* v___x_3364_; 
if (v_isShared_3359_ == 0)
{
lean_ctor_set(v___x_3358_, 1, v_a_3362_);
lean_ctor_set(v___x_3358_, 0, v___x_3360_);
v___x_3364_ = v___x_3358_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v___x_3360_);
lean_ctor_set(v_reuseFailAlloc_3368_, 1, v_a_3362_);
v___x_3364_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
size_t v___x_3365_; size_t v___x_3366_; 
v___x_3365_ = ((size_t)1ULL);
v___x_3366_ = lean_usize_add(v_i_3351_, v___x_3365_);
v_i_3351_ = v___x_3366_;
v_b_3352_ = v___x_3364_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_elimTrivial_3405_, lean_object* v_as_3406_, lean_object* v_sz_3407_, lean_object* v_i_3408_, lean_object* v_b_3409_, lean_object* v___y_3410_){
_start:
{
uint8_t v_elimTrivial_boxed_3411_; size_t v_sz_boxed_3412_; size_t v_i_boxed_3413_; lean_object* v_res_3414_; 
v_elimTrivial_boxed_3411_ = lean_unbox(v_elimTrivial_3405_);
v_sz_boxed_3412_ = lean_unbox_usize(v_sz_3407_);
lean_dec(v_sz_3407_);
v_i_boxed_3413_ = lean_unbox_usize(v_i_3408_);
lean_dec(v_i_3408_);
v_res_3414_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_boxed_3411_, v_as_3406_, v_sz_boxed_3412_, v_i_boxed_3413_, v_b_3409_);
lean_dec_ref(v_as_3406_);
return v_res_3414_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(uint8_t v_elimTrivial_3415_, lean_object* v_as_3416_, size_t v_sz_3417_, size_t v_i_3418_, lean_object* v_b_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_){
_start:
{
uint8_t v___x_3425_; 
v___x_3425_ = lean_usize_dec_lt(v_i_3418_, v_sz_3417_);
if (v___x_3425_ == 0)
{
lean_object* v___x_3426_; 
v___x_3426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3426_, 0, v_b_3419_);
return v___x_3426_;
}
else
{
lean_object* v_snd_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3474_; 
v_snd_3427_ = lean_ctor_get(v_b_3419_, 1);
v_isSharedCheck_3474_ = !lean_is_exclusive(v_b_3419_);
if (v_isSharedCheck_3474_ == 0)
{
lean_object* v_unused_3475_; 
v_unused_3475_ = lean_ctor_get(v_b_3419_, 0);
lean_dec(v_unused_3475_);
v___x_3429_ = v_b_3419_;
v_isShared_3430_ = v_isSharedCheck_3474_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_snd_3427_);
lean_dec(v_b_3419_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3474_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3431_; lean_object* v_a_3433_; lean_object* v_a_3440_; 
v___x_3431_ = lean_box(0);
v_a_3440_ = lean_array_uget_borrowed(v_as_3416_, v_i_3418_);
if (lean_obj_tag(v_a_3440_) == 0)
{
v_a_3433_ = v_snd_3427_;
goto v___jp_3432_;
}
else
{
lean_object* v_val_3441_; lean_object* v_fst_3442_; lean_object* v_snd_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3473_; 
v_val_3441_ = lean_ctor_get(v_a_3440_, 0);
v_fst_3442_ = lean_ctor_get(v_snd_3427_, 0);
v_snd_3443_ = lean_ctor_get(v_snd_3427_, 1);
v_isSharedCheck_3473_ = !lean_is_exclusive(v_snd_3427_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3445_ = v_snd_3427_;
v_isShared_3446_ = v_isSharedCheck_3473_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_snd_3443_);
lean_inc(v_fst_3442_);
lean_dec(v_snd_3427_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3473_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
uint8_t v___x_3447_; lean_object* v___x_3448_; 
v___x_3447_ = 0;
v___x_3448_ = l_Lean_LocalDecl_value_x3f(v_val_3441_, v___x_3447_);
if (lean_obj_tag(v___x_3448_) == 1)
{
lean_object* v_val_3449_; lean_object* v___x_3450_; 
v_val_3449_ = lean_ctor_get(v___x_3448_, 0);
lean_inc(v_val_3449_);
lean_dec_ref(v___x_3448_);
v___x_3450_ = l_Lean_LocalDecl_type(v_val_3441_);
if (lean_obj_tag(v___x_3450_) == 10)
{
lean_object* v_data_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; uint8_t v___x_3455_; uint8_t v___x_3456_; 
v_data_3451_ = lean_ctor_get(v___x_3450_, 0);
lean_inc(v_data_3451_);
lean_dec_ref(v___x_3450_);
v___x_3452_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_3453_ = lean_unsigned_to_nat(2u);
v___x_3454_ = l_Lean_KVMap_getNat(v_data_3451_, v___x_3452_, v___x_3453_);
lean_dec(v_data_3451_);
v___x_3455_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3454_);
lean_dec(v___x_3454_);
v___x_3456_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3455_, v_val_3449_, v_elimTrivial_3415_);
if (v___x_3456_ == 0)
{
lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3462_; 
v___x_3457_ = l_Lean_LocalDecl_fvarId(v_val_3441_);
v___x_3458_ = l_Lean_mkFVar(v___x_3457_);
v___x_3459_ = lean_array_push(v_fst_3442_, v___x_3458_);
v___x_3460_ = lean_array_push(v_snd_3443_, v_val_3449_);
if (v_isShared_3446_ == 0)
{
lean_ctor_set(v___x_3445_, 1, v___x_3460_);
lean_ctor_set(v___x_3445_, 0, v___x_3459_);
v___x_3462_ = v___x_3445_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v___x_3459_);
lean_ctor_set(v_reuseFailAlloc_3463_, 1, v___x_3460_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
v_a_3433_ = v___x_3462_;
goto v___jp_3432_;
}
}
else
{
lean_object* v___x_3465_; 
lean_dec(v_val_3449_);
if (v_isShared_3446_ == 0)
{
v___x_3465_ = v___x_3445_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v_fst_3442_);
lean_ctor_set(v_reuseFailAlloc_3466_, 1, v_snd_3443_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
v_a_3433_ = v___x_3465_;
goto v___jp_3432_;
}
}
}
else
{
lean_object* v___x_3468_; 
lean_dec_ref(v___x_3450_);
lean_dec(v_val_3449_);
if (v_isShared_3446_ == 0)
{
v___x_3468_ = v___x_3445_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_fst_3442_);
lean_ctor_set(v_reuseFailAlloc_3469_, 1, v_snd_3443_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
v_a_3433_ = v___x_3468_;
goto v___jp_3432_;
}
}
}
else
{
lean_object* v___x_3471_; 
lean_dec(v___x_3448_);
if (v_isShared_3446_ == 0)
{
v___x_3471_ = v___x_3445_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v_fst_3442_);
lean_ctor_set(v_reuseFailAlloc_3472_, 1, v_snd_3443_);
v___x_3471_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
v_a_3433_ = v___x_3471_;
goto v___jp_3432_;
}
}
}
}
v___jp_3432_:
{
lean_object* v___x_3435_; 
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 1, v_a_3433_);
lean_ctor_set(v___x_3429_, 0, v___x_3431_);
v___x_3435_ = v___x_3429_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v___x_3431_);
lean_ctor_set(v_reuseFailAlloc_3439_, 1, v_a_3433_);
v___x_3435_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
size_t v___x_3436_; size_t v___x_3437_; lean_object* v___x_3438_; 
v___x_3436_ = ((size_t)1ULL);
v___x_3437_ = lean_usize_add(v_i_3418_, v___x_3436_);
v___x_3438_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_3415_, v_as_3416_, v_sz_3417_, v___x_3437_, v___x_3435_);
return v___x_3438_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1___boxed(lean_object* v_elimTrivial_3476_, lean_object* v_as_3477_, lean_object* v_sz_3478_, lean_object* v_i_3479_, lean_object* v_b_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_){
_start:
{
uint8_t v_elimTrivial_boxed_3486_; size_t v_sz_boxed_3487_; size_t v_i_boxed_3488_; lean_object* v_res_3489_; 
v_elimTrivial_boxed_3486_ = lean_unbox(v_elimTrivial_3476_);
v_sz_boxed_3487_ = lean_unbox_usize(v_sz_3478_);
lean_dec(v_sz_3478_);
v_i_boxed_3488_ = lean_unbox_usize(v_i_3479_);
lean_dec(v_i_3479_);
v_res_3489_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(v_elimTrivial_boxed_3486_, v_as_3477_, v_sz_boxed_3487_, v_i_boxed_3488_, v_b_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_);
lean_dec(v___y_3484_);
lean_dec_ref(v___y_3483_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec_ref(v_as_3477_);
return v_res_3489_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(uint8_t v_elimTrivial_3490_, lean_object* v_as_3491_, size_t v_sz_3492_, size_t v_i_3493_, lean_object* v_b_3494_){
_start:
{
uint8_t v___x_3496_; 
v___x_3496_ = lean_usize_dec_lt(v_i_3493_, v_sz_3492_);
if (v___x_3496_ == 0)
{
lean_object* v___x_3497_; 
v___x_3497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3497_, 0, v_b_3494_);
return v___x_3497_;
}
else
{
lean_object* v_snd_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3545_; 
v_snd_3498_ = lean_ctor_get(v_b_3494_, 1);
v_isSharedCheck_3545_ = !lean_is_exclusive(v_b_3494_);
if (v_isSharedCheck_3545_ == 0)
{
lean_object* v_unused_3546_; 
v_unused_3546_ = lean_ctor_get(v_b_3494_, 0);
lean_dec(v_unused_3546_);
v___x_3500_ = v_b_3494_;
v_isShared_3501_ = v_isSharedCheck_3545_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_snd_3498_);
lean_dec(v_b_3494_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3545_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3502_; lean_object* v_a_3504_; lean_object* v_a_3511_; 
v___x_3502_ = lean_box(0);
v_a_3511_ = lean_array_uget_borrowed(v_as_3491_, v_i_3493_);
if (lean_obj_tag(v_a_3511_) == 0)
{
v_a_3504_ = v_snd_3498_;
goto v___jp_3503_;
}
else
{
lean_object* v_val_3512_; lean_object* v_fst_3513_; lean_object* v_snd_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3544_; 
v_val_3512_ = lean_ctor_get(v_a_3511_, 0);
v_fst_3513_ = lean_ctor_get(v_snd_3498_, 0);
v_snd_3514_ = lean_ctor_get(v_snd_3498_, 1);
v_isSharedCheck_3544_ = !lean_is_exclusive(v_snd_3498_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3516_ = v_snd_3498_;
v_isShared_3517_ = v_isSharedCheck_3544_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_snd_3514_);
lean_inc(v_fst_3513_);
lean_dec(v_snd_3498_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3544_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
uint8_t v___x_3518_; lean_object* v___x_3519_; 
v___x_3518_ = 0;
v___x_3519_ = l_Lean_LocalDecl_value_x3f(v_val_3512_, v___x_3518_);
if (lean_obj_tag(v___x_3519_) == 1)
{
lean_object* v_val_3520_; lean_object* v___x_3521_; 
v_val_3520_ = lean_ctor_get(v___x_3519_, 0);
lean_inc(v_val_3520_);
lean_dec_ref(v___x_3519_);
v___x_3521_ = l_Lean_LocalDecl_type(v_val_3512_);
if (lean_obj_tag(v___x_3521_) == 10)
{
lean_object* v_data_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; uint8_t v___x_3526_; uint8_t v___x_3527_; 
v_data_3522_ = lean_ctor_get(v___x_3521_, 0);
lean_inc(v_data_3522_);
lean_dec_ref(v___x_3521_);
v___x_3523_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_3524_ = lean_unsigned_to_nat(2u);
v___x_3525_ = l_Lean_KVMap_getNat(v_data_3522_, v___x_3523_, v___x_3524_);
lean_dec(v_data_3522_);
v___x_3526_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3525_);
lean_dec(v___x_3525_);
v___x_3527_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3526_, v_val_3520_, v_elimTrivial_3490_);
if (v___x_3527_ == 0)
{
lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3533_; 
v___x_3528_ = l_Lean_LocalDecl_fvarId(v_val_3512_);
v___x_3529_ = l_Lean_mkFVar(v___x_3528_);
v___x_3530_ = lean_array_push(v_fst_3513_, v___x_3529_);
v___x_3531_ = lean_array_push(v_snd_3514_, v_val_3520_);
if (v_isShared_3517_ == 0)
{
lean_ctor_set(v___x_3516_, 1, v___x_3531_);
lean_ctor_set(v___x_3516_, 0, v___x_3530_);
v___x_3533_ = v___x_3516_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v___x_3530_);
lean_ctor_set(v_reuseFailAlloc_3534_, 1, v___x_3531_);
v___x_3533_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
v_a_3504_ = v___x_3533_;
goto v___jp_3503_;
}
}
else
{
lean_object* v___x_3536_; 
lean_dec(v_val_3520_);
if (v_isShared_3517_ == 0)
{
v___x_3536_ = v___x_3516_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_fst_3513_);
lean_ctor_set(v_reuseFailAlloc_3537_, 1, v_snd_3514_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
v_a_3504_ = v___x_3536_;
goto v___jp_3503_;
}
}
}
else
{
lean_object* v___x_3539_; 
lean_dec_ref(v___x_3521_);
lean_dec(v_val_3520_);
if (v_isShared_3517_ == 0)
{
v___x_3539_ = v___x_3516_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_fst_3513_);
lean_ctor_set(v_reuseFailAlloc_3540_, 1, v_snd_3514_);
v___x_3539_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
v_a_3504_ = v___x_3539_;
goto v___jp_3503_;
}
}
}
else
{
lean_object* v___x_3542_; 
lean_dec(v___x_3519_);
if (v_isShared_3517_ == 0)
{
v___x_3542_ = v___x_3516_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_fst_3513_);
lean_ctor_set(v_reuseFailAlloc_3543_, 1, v_snd_3514_);
v___x_3542_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
v_a_3504_ = v___x_3542_;
goto v___jp_3503_;
}
}
}
}
v___jp_3503_:
{
lean_object* v___x_3506_; 
if (v_isShared_3501_ == 0)
{
lean_ctor_set(v___x_3500_, 1, v_a_3504_);
lean_ctor_set(v___x_3500_, 0, v___x_3502_);
v___x_3506_ = v___x_3500_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v___x_3502_);
lean_ctor_set(v_reuseFailAlloc_3510_, 1, v_a_3504_);
v___x_3506_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
size_t v___x_3507_; size_t v___x_3508_; 
v___x_3507_ = ((size_t)1ULL);
v___x_3508_ = lean_usize_add(v_i_3493_, v___x_3507_);
v_i_3493_ = v___x_3508_;
v_b_3494_ = v___x_3506_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg___boxed(lean_object* v_elimTrivial_3547_, lean_object* v_as_3548_, lean_object* v_sz_3549_, lean_object* v_i_3550_, lean_object* v_b_3551_, lean_object* v___y_3552_){
_start:
{
uint8_t v_elimTrivial_boxed_3553_; size_t v_sz_boxed_3554_; size_t v_i_boxed_3555_; lean_object* v_res_3556_; 
v_elimTrivial_boxed_3553_ = lean_unbox(v_elimTrivial_3547_);
v_sz_boxed_3554_ = lean_unbox_usize(v_sz_3549_);
lean_dec(v_sz_3549_);
v_i_boxed_3555_ = lean_unbox_usize(v_i_3550_);
lean_dec(v_i_3550_);
v_res_3556_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_boxed_3553_, v_as_3548_, v_sz_boxed_3554_, v_i_boxed_3555_, v_b_3551_);
lean_dec_ref(v_as_3548_);
return v_res_3556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(uint8_t v_elimTrivial_3557_, lean_object* v_as_3558_, size_t v_sz_3559_, size_t v_i_3560_, lean_object* v_b_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_){
_start:
{
uint8_t v___x_3567_; 
v___x_3567_ = lean_usize_dec_lt(v_i_3560_, v_sz_3559_);
if (v___x_3567_ == 0)
{
lean_object* v___x_3568_; 
v___x_3568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3568_, 0, v_b_3561_);
return v___x_3568_;
}
else
{
lean_object* v_snd_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3616_; 
v_snd_3569_ = lean_ctor_get(v_b_3561_, 1);
v_isSharedCheck_3616_ = !lean_is_exclusive(v_b_3561_);
if (v_isSharedCheck_3616_ == 0)
{
lean_object* v_unused_3617_; 
v_unused_3617_ = lean_ctor_get(v_b_3561_, 0);
lean_dec(v_unused_3617_);
v___x_3571_ = v_b_3561_;
v_isShared_3572_ = v_isSharedCheck_3616_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_snd_3569_);
lean_dec(v_b_3561_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3616_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3573_; lean_object* v_a_3575_; lean_object* v_a_3582_; 
v___x_3573_ = lean_box(0);
v_a_3582_ = lean_array_uget_borrowed(v_as_3558_, v_i_3560_);
if (lean_obj_tag(v_a_3582_) == 0)
{
v_a_3575_ = v_snd_3569_;
goto v___jp_3574_;
}
else
{
lean_object* v_val_3583_; lean_object* v_fst_3584_; lean_object* v_snd_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3615_; 
v_val_3583_ = lean_ctor_get(v_a_3582_, 0);
v_fst_3584_ = lean_ctor_get(v_snd_3569_, 0);
v_snd_3585_ = lean_ctor_get(v_snd_3569_, 1);
v_isSharedCheck_3615_ = !lean_is_exclusive(v_snd_3569_);
if (v_isSharedCheck_3615_ == 0)
{
v___x_3587_ = v_snd_3569_;
v_isShared_3588_ = v_isSharedCheck_3615_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_snd_3585_);
lean_inc(v_fst_3584_);
lean_dec(v_snd_3569_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3615_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
uint8_t v___x_3589_; lean_object* v___x_3590_; 
v___x_3589_ = 0;
v___x_3590_ = l_Lean_LocalDecl_value_x3f(v_val_3583_, v___x_3589_);
if (lean_obj_tag(v___x_3590_) == 1)
{
lean_object* v_val_3591_; lean_object* v___x_3592_; 
v_val_3591_ = lean_ctor_get(v___x_3590_, 0);
lean_inc(v_val_3591_);
lean_dec_ref(v___x_3590_);
v___x_3592_ = l_Lean_LocalDecl_type(v_val_3583_);
if (lean_obj_tag(v___x_3592_) == 10)
{
lean_object* v_data_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; uint8_t v___x_3597_; uint8_t v___x_3598_; 
v_data_3593_ = lean_ctor_get(v___x_3592_, 0);
lean_inc(v_data_3593_);
lean_dec_ref(v___x_3592_);
v___x_3594_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_3595_ = lean_unsigned_to_nat(2u);
v___x_3596_ = l_Lean_KVMap_getNat(v_data_3593_, v___x_3594_, v___x_3595_);
lean_dec(v_data_3593_);
v___x_3597_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3596_);
lean_dec(v___x_3596_);
v___x_3598_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3597_, v_val_3591_, v_elimTrivial_3557_);
if (v___x_3598_ == 0)
{
lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3604_; 
v___x_3599_ = l_Lean_LocalDecl_fvarId(v_val_3583_);
v___x_3600_ = l_Lean_mkFVar(v___x_3599_);
v___x_3601_ = lean_array_push(v_fst_3584_, v___x_3600_);
v___x_3602_ = lean_array_push(v_snd_3585_, v_val_3591_);
if (v_isShared_3588_ == 0)
{
lean_ctor_set(v___x_3587_, 1, v___x_3602_);
lean_ctor_set(v___x_3587_, 0, v___x_3601_);
v___x_3604_ = v___x_3587_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v___x_3601_);
lean_ctor_set(v_reuseFailAlloc_3605_, 1, v___x_3602_);
v___x_3604_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
v_a_3575_ = v___x_3604_;
goto v___jp_3574_;
}
}
else
{
lean_object* v___x_3607_; 
lean_dec(v_val_3591_);
if (v_isShared_3588_ == 0)
{
v___x_3607_ = v___x_3587_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v_fst_3584_);
lean_ctor_set(v_reuseFailAlloc_3608_, 1, v_snd_3585_);
v___x_3607_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
v_a_3575_ = v___x_3607_;
goto v___jp_3574_;
}
}
}
else
{
lean_object* v___x_3610_; 
lean_dec_ref(v___x_3592_);
lean_dec(v_val_3591_);
if (v_isShared_3588_ == 0)
{
v___x_3610_ = v___x_3587_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_fst_3584_);
lean_ctor_set(v_reuseFailAlloc_3611_, 1, v_snd_3585_);
v___x_3610_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
v_a_3575_ = v___x_3610_;
goto v___jp_3574_;
}
}
}
else
{
lean_object* v___x_3613_; 
lean_dec(v___x_3590_);
if (v_isShared_3588_ == 0)
{
v___x_3613_ = v___x_3587_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v_fst_3584_);
lean_ctor_set(v_reuseFailAlloc_3614_, 1, v_snd_3585_);
v___x_3613_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
v_a_3575_ = v___x_3613_;
goto v___jp_3574_;
}
}
}
}
v___jp_3574_:
{
lean_object* v___x_3577_; 
if (v_isShared_3572_ == 0)
{
lean_ctor_set(v___x_3571_, 1, v_a_3575_);
lean_ctor_set(v___x_3571_, 0, v___x_3573_);
v___x_3577_ = v___x_3571_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v___x_3573_);
lean_ctor_set(v_reuseFailAlloc_3581_, 1, v_a_3575_);
v___x_3577_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
size_t v___x_3578_; size_t v___x_3579_; lean_object* v___x_3580_; 
v___x_3578_ = ((size_t)1ULL);
v___x_3579_ = lean_usize_add(v_i_3560_, v___x_3578_);
v___x_3580_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_3557_, v_as_3558_, v_sz_3559_, v___x_3579_, v___x_3577_);
return v___x_3580_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3___boxed(lean_object* v_elimTrivial_3618_, lean_object* v_as_3619_, lean_object* v_sz_3620_, lean_object* v_i_3621_, lean_object* v_b_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_){
_start:
{
uint8_t v_elimTrivial_boxed_3628_; size_t v_sz_boxed_3629_; size_t v_i_boxed_3630_; lean_object* v_res_3631_; 
v_elimTrivial_boxed_3628_ = lean_unbox(v_elimTrivial_3618_);
v_sz_boxed_3629_ = lean_unbox_usize(v_sz_3620_);
lean_dec(v_sz_3620_);
v_i_boxed_3630_ = lean_unbox_usize(v_i_3621_);
lean_dec(v_i_3621_);
v_res_3631_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(v_elimTrivial_boxed_3628_, v_as_3619_, v_sz_boxed_3629_, v_i_boxed_3630_, v_b_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_);
lean_dec(v___y_3626_);
lean_dec_ref(v___y_3625_);
lean_dec(v___y_3624_);
lean_dec_ref(v___y_3623_);
lean_dec_ref(v_as_3619_);
return v_res_3631_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(lean_object* v_init_3632_, uint8_t v_elimTrivial_3633_, lean_object* v_n_3634_, lean_object* v_b_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_){
_start:
{
if (lean_obj_tag(v_n_3634_) == 0)
{
lean_object* v_cs_3641_; lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3675_; 
v_cs_3641_ = lean_ctor_get(v_n_3634_, 0);
v_isSharedCheck_3675_ = !lean_is_exclusive(v_n_3634_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3643_ = v_n_3634_;
v_isShared_3644_ = v_isSharedCheck_3675_;
goto v_resetjp_3642_;
}
else
{
lean_inc(v_cs_3641_);
lean_dec(v_n_3634_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3675_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
lean_object* v___x_3645_; lean_object* v___x_3646_; size_t v_sz_3647_; size_t v___x_3648_; lean_object* v___x_3649_; 
v___x_3645_ = lean_box(0);
v___x_3646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3646_, 0, v___x_3645_);
lean_ctor_set(v___x_3646_, 1, v_b_3635_);
v_sz_3647_ = lean_array_size(v_cs_3641_);
v___x_3648_ = ((size_t)0ULL);
v___x_3649_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(v_init_3632_, v_elimTrivial_3633_, v_cs_3641_, v_sz_3647_, v___x_3648_, v___x_3646_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_);
lean_dec_ref(v_cs_3641_);
if (lean_obj_tag(v___x_3649_) == 0)
{
lean_object* v_a_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3666_; 
v_a_3650_ = lean_ctor_get(v___x_3649_, 0);
v_isSharedCheck_3666_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3666_ == 0)
{
v___x_3652_ = v___x_3649_;
v_isShared_3653_ = v_isSharedCheck_3666_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_a_3650_);
lean_dec(v___x_3649_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3666_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v_fst_3654_; 
v_fst_3654_ = lean_ctor_get(v_a_3650_, 0);
if (lean_obj_tag(v_fst_3654_) == 0)
{
lean_object* v_snd_3655_; lean_object* v___x_3657_; 
v_snd_3655_ = lean_ctor_get(v_a_3650_, 1);
lean_inc(v_snd_3655_);
lean_dec(v_a_3650_);
if (v_isShared_3644_ == 0)
{
lean_ctor_set_tag(v___x_3643_, 1);
lean_ctor_set(v___x_3643_, 0, v_snd_3655_);
v___x_3657_ = v___x_3643_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_snd_3655_);
v___x_3657_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
lean_object* v___x_3659_; 
if (v_isShared_3653_ == 0)
{
lean_ctor_set(v___x_3652_, 0, v___x_3657_);
v___x_3659_ = v___x_3652_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v___x_3657_);
v___x_3659_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
return v___x_3659_;
}
}
}
else
{
lean_object* v_val_3662_; lean_object* v___x_3664_; 
lean_inc_ref(v_fst_3654_);
lean_dec(v_a_3650_);
lean_del_object(v___x_3643_);
v_val_3662_ = lean_ctor_get(v_fst_3654_, 0);
lean_inc(v_val_3662_);
lean_dec_ref(v_fst_3654_);
if (v_isShared_3653_ == 0)
{
lean_ctor_set(v___x_3652_, 0, v_val_3662_);
v___x_3664_ = v___x_3652_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v_val_3662_);
v___x_3664_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
return v___x_3664_;
}
}
}
}
else
{
lean_object* v_a_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3674_; 
lean_del_object(v___x_3643_);
v_a_3667_ = lean_ctor_get(v___x_3649_, 0);
v_isSharedCheck_3674_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3674_ == 0)
{
v___x_3669_ = v___x_3649_;
v_isShared_3670_ = v_isSharedCheck_3674_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_a_3667_);
lean_dec(v___x_3649_);
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
v_reuseFailAlloc_3673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v_a_3667_);
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
else
{
lean_object* v_vs_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3710_; 
v_vs_3676_ = lean_ctor_get(v_n_3634_, 0);
v_isSharedCheck_3710_ = !lean_is_exclusive(v_n_3634_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3678_ = v_n_3634_;
v_isShared_3679_ = v_isSharedCheck_3710_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_vs_3676_);
lean_dec(v_n_3634_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3710_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v___x_3680_; lean_object* v___x_3681_; size_t v_sz_3682_; size_t v___x_3683_; lean_object* v___x_3684_; 
v___x_3680_ = lean_box(0);
v___x_3681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3680_);
lean_ctor_set(v___x_3681_, 1, v_b_3635_);
v_sz_3682_ = lean_array_size(v_vs_3676_);
v___x_3683_ = ((size_t)0ULL);
v___x_3684_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(v_elimTrivial_3633_, v_vs_3676_, v_sz_3682_, v___x_3683_, v___x_3681_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_);
lean_dec_ref(v_vs_3676_);
if (lean_obj_tag(v___x_3684_) == 0)
{
lean_object* v_a_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3701_; 
v_a_3685_ = lean_ctor_get(v___x_3684_, 0);
v_isSharedCheck_3701_ = !lean_is_exclusive(v___x_3684_);
if (v_isSharedCheck_3701_ == 0)
{
v___x_3687_ = v___x_3684_;
v_isShared_3688_ = v_isSharedCheck_3701_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_a_3685_);
lean_dec(v___x_3684_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3701_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v_fst_3689_; 
v_fst_3689_ = lean_ctor_get(v_a_3685_, 0);
if (lean_obj_tag(v_fst_3689_) == 0)
{
lean_object* v_snd_3690_; lean_object* v___x_3692_; 
v_snd_3690_ = lean_ctor_get(v_a_3685_, 1);
lean_inc(v_snd_3690_);
lean_dec(v_a_3685_);
if (v_isShared_3679_ == 0)
{
lean_ctor_set(v___x_3678_, 0, v_snd_3690_);
v___x_3692_ = v___x_3678_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v_snd_3690_);
v___x_3692_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
lean_object* v___x_3694_; 
if (v_isShared_3688_ == 0)
{
lean_ctor_set(v___x_3687_, 0, v___x_3692_);
v___x_3694_ = v___x_3687_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v___x_3692_);
v___x_3694_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
return v___x_3694_;
}
}
}
else
{
lean_object* v_val_3697_; lean_object* v___x_3699_; 
lean_inc_ref(v_fst_3689_);
lean_dec(v_a_3685_);
lean_del_object(v___x_3678_);
v_val_3697_ = lean_ctor_get(v_fst_3689_, 0);
lean_inc(v_val_3697_);
lean_dec_ref(v_fst_3689_);
if (v_isShared_3688_ == 0)
{
lean_ctor_set(v___x_3687_, 0, v_val_3697_);
v___x_3699_ = v___x_3687_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_val_3697_);
v___x_3699_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
return v___x_3699_;
}
}
}
}
else
{
lean_object* v_a_3702_; lean_object* v___x_3704_; uint8_t v_isShared_3705_; uint8_t v_isSharedCheck_3709_; 
lean_del_object(v___x_3678_);
v_a_3702_ = lean_ctor_get(v___x_3684_, 0);
v_isSharedCheck_3709_ = !lean_is_exclusive(v___x_3684_);
if (v_isSharedCheck_3709_ == 0)
{
v___x_3704_ = v___x_3684_;
v_isShared_3705_ = v_isSharedCheck_3709_;
goto v_resetjp_3703_;
}
else
{
lean_inc(v_a_3702_);
lean_dec(v___x_3684_);
v___x_3704_ = lean_box(0);
v_isShared_3705_ = v_isSharedCheck_3709_;
goto v_resetjp_3703_;
}
v_resetjp_3703_:
{
lean_object* v___x_3707_; 
if (v_isShared_3705_ == 0)
{
v___x_3707_ = v___x_3704_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v_a_3702_);
v___x_3707_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
return v___x_3707_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(lean_object* v_init_3711_, uint8_t v_elimTrivial_3712_, lean_object* v_as_3713_, size_t v_sz_3714_, size_t v_i_3715_, lean_object* v_b_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_){
_start:
{
uint8_t v___x_3722_; 
v___x_3722_ = lean_usize_dec_lt(v_i_3715_, v_sz_3714_);
if (v___x_3722_ == 0)
{
lean_object* v___x_3723_; 
v___x_3723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3723_, 0, v_b_3716_);
return v___x_3723_;
}
else
{
lean_object* v_snd_3724_; lean_object* v___x_3726_; uint8_t v_isShared_3727_; uint8_t v_isSharedCheck_3758_; 
v_snd_3724_ = lean_ctor_get(v_b_3716_, 1);
v_isSharedCheck_3758_ = !lean_is_exclusive(v_b_3716_);
if (v_isSharedCheck_3758_ == 0)
{
lean_object* v_unused_3759_; 
v_unused_3759_ = lean_ctor_get(v_b_3716_, 0);
lean_dec(v_unused_3759_);
v___x_3726_ = v_b_3716_;
v_isShared_3727_ = v_isSharedCheck_3758_;
goto v_resetjp_3725_;
}
else
{
lean_inc(v_snd_3724_);
lean_dec(v_b_3716_);
v___x_3726_ = lean_box(0);
v_isShared_3727_ = v_isSharedCheck_3758_;
goto v_resetjp_3725_;
}
v_resetjp_3725_:
{
lean_object* v_a_3728_; lean_object* v___x_3729_; 
v_a_3728_ = lean_array_uget_borrowed(v_as_3713_, v_i_3715_);
lean_inc(v_snd_3724_);
lean_inc(v_a_3728_);
v___x_3729_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_3711_, v_elimTrivial_3712_, v_a_3728_, v_snd_3724_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_);
if (lean_obj_tag(v___x_3729_) == 0)
{
lean_object* v_a_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3749_; 
v_a_3730_ = lean_ctor_get(v___x_3729_, 0);
v_isSharedCheck_3749_ = !lean_is_exclusive(v___x_3729_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3732_ = v___x_3729_;
v_isShared_3733_ = v_isSharedCheck_3749_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_a_3730_);
lean_dec(v___x_3729_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3749_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
if (lean_obj_tag(v_a_3730_) == 0)
{
lean_object* v___x_3734_; lean_object* v___x_3736_; 
v___x_3734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3734_, 0, v_a_3730_);
if (v_isShared_3727_ == 0)
{
lean_ctor_set(v___x_3726_, 0, v___x_3734_);
v___x_3736_ = v___x_3726_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v___x_3734_);
lean_ctor_set(v_reuseFailAlloc_3740_, 1, v_snd_3724_);
v___x_3736_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
lean_object* v___x_3738_; 
if (v_isShared_3733_ == 0)
{
lean_ctor_set(v___x_3732_, 0, v___x_3736_);
v___x_3738_ = v___x_3732_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v___x_3736_);
v___x_3738_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
return v___x_3738_;
}
}
}
else
{
lean_object* v_a_3741_; lean_object* v___x_3742_; lean_object* v___x_3744_; 
lean_del_object(v___x_3732_);
lean_dec(v_snd_3724_);
v_a_3741_ = lean_ctor_get(v_a_3730_, 0);
lean_inc(v_a_3741_);
lean_dec_ref(v_a_3730_);
v___x_3742_ = lean_box(0);
if (v_isShared_3727_ == 0)
{
lean_ctor_set(v___x_3726_, 1, v_a_3741_);
lean_ctor_set(v___x_3726_, 0, v___x_3742_);
v___x_3744_ = v___x_3726_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v___x_3742_);
lean_ctor_set(v_reuseFailAlloc_3748_, 1, v_a_3741_);
v___x_3744_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
size_t v___x_3745_; size_t v___x_3746_; 
v___x_3745_ = ((size_t)1ULL);
v___x_3746_ = lean_usize_add(v_i_3715_, v___x_3745_);
v_i_3715_ = v___x_3746_;
v_b_3716_ = v___x_3744_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3757_; 
lean_del_object(v___x_3726_);
lean_dec(v_snd_3724_);
v_a_3750_ = lean_ctor_get(v___x_3729_, 0);
v_isSharedCheck_3757_ = !lean_is_exclusive(v___x_3729_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3752_ = v___x_3729_;
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_a_3750_);
lean_dec(v___x_3729_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v___x_3755_; 
if (v_isShared_3753_ == 0)
{
v___x_3755_ = v___x_3752_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v_a_3750_);
v___x_3755_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
return v___x_3755_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2___boxed(lean_object* v_init_3760_, lean_object* v_elimTrivial_3761_, lean_object* v_as_3762_, lean_object* v_sz_3763_, lean_object* v_i_3764_, lean_object* v_b_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_){
_start:
{
uint8_t v_elimTrivial_boxed_3771_; size_t v_sz_boxed_3772_; size_t v_i_boxed_3773_; lean_object* v_res_3774_; 
v_elimTrivial_boxed_3771_ = lean_unbox(v_elimTrivial_3761_);
v_sz_boxed_3772_ = lean_unbox_usize(v_sz_3763_);
lean_dec(v_sz_3763_);
v_i_boxed_3773_ = lean_unbox_usize(v_i_3764_);
lean_dec(v_i_3764_);
v_res_3774_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(v_init_3760_, v_elimTrivial_boxed_3771_, v_as_3762_, v_sz_boxed_3772_, v_i_boxed_3773_, v_b_3765_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_);
lean_dec(v___y_3769_);
lean_dec_ref(v___y_3768_);
lean_dec(v___y_3767_);
lean_dec_ref(v___y_3766_);
lean_dec_ref(v_as_3762_);
lean_dec_ref(v_init_3760_);
return v_res_3774_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0___boxed(lean_object* v_init_3775_, lean_object* v_elimTrivial_3776_, lean_object* v_n_3777_, lean_object* v_b_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_){
_start:
{
uint8_t v_elimTrivial_boxed_3784_; lean_object* v_res_3785_; 
v_elimTrivial_boxed_3784_ = lean_unbox(v_elimTrivial_3776_);
v_res_3785_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_3775_, v_elimTrivial_boxed_3784_, v_n_3777_, v_b_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_);
lean_dec(v___y_3782_);
lean_dec_ref(v___y_3781_);
lean_dec(v___y_3780_);
lean_dec_ref(v___y_3779_);
lean_dec_ref(v_init_3775_);
return v_res_3785_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(uint8_t v_elimTrivial_3786_, lean_object* v_t_3787_, lean_object* v_init_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_){
_start:
{
lean_object* v_root_3794_; lean_object* v_tail_3795_; lean_object* v___x_3796_; 
v_root_3794_ = lean_ctor_get(v_t_3787_, 0);
lean_inc_ref(v_root_3794_);
v_tail_3795_ = lean_ctor_get(v_t_3787_, 1);
lean_inc_ref(v_tail_3795_);
lean_dec_ref(v_t_3787_);
lean_inc_ref(v_init_3788_);
v___x_3796_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_3788_, v_elimTrivial_3786_, v_root_3794_, v_init_3788_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_);
lean_dec_ref(v_init_3788_);
if (lean_obj_tag(v___x_3796_) == 0)
{
lean_object* v_a_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3833_; 
v_a_3797_ = lean_ctor_get(v___x_3796_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3796_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3799_ = v___x_3796_;
v_isShared_3800_ = v_isSharedCheck_3833_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_a_3797_);
lean_dec(v___x_3796_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3833_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
if (lean_obj_tag(v_a_3797_) == 0)
{
lean_object* v_a_3801_; lean_object* v___x_3803_; 
lean_dec_ref(v_tail_3795_);
v_a_3801_ = lean_ctor_get(v_a_3797_, 0);
lean_inc(v_a_3801_);
lean_dec_ref(v_a_3797_);
if (v_isShared_3800_ == 0)
{
lean_ctor_set(v___x_3799_, 0, v_a_3801_);
v___x_3803_ = v___x_3799_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v_a_3801_);
v___x_3803_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
return v___x_3803_;
}
}
else
{
lean_object* v_a_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; size_t v_sz_3808_; size_t v___x_3809_; lean_object* v___x_3810_; 
lean_del_object(v___x_3799_);
v_a_3805_ = lean_ctor_get(v_a_3797_, 0);
lean_inc(v_a_3805_);
lean_dec_ref(v_a_3797_);
v___x_3806_ = lean_box(0);
v___x_3807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3807_, 0, v___x_3806_);
lean_ctor_set(v___x_3807_, 1, v_a_3805_);
v_sz_3808_ = lean_array_size(v_tail_3795_);
v___x_3809_ = ((size_t)0ULL);
v___x_3810_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(v_elimTrivial_3786_, v_tail_3795_, v_sz_3808_, v___x_3809_, v___x_3807_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_);
lean_dec_ref(v_tail_3795_);
if (lean_obj_tag(v___x_3810_) == 0)
{
lean_object* v_a_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3824_; 
v_a_3811_ = lean_ctor_get(v___x_3810_, 0);
v_isSharedCheck_3824_ = !lean_is_exclusive(v___x_3810_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3813_ = v___x_3810_;
v_isShared_3814_ = v_isSharedCheck_3824_;
goto v_resetjp_3812_;
}
else
{
lean_inc(v_a_3811_);
lean_dec(v___x_3810_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3824_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v_fst_3815_; 
v_fst_3815_ = lean_ctor_get(v_a_3811_, 0);
if (lean_obj_tag(v_fst_3815_) == 0)
{
lean_object* v_snd_3816_; lean_object* v___x_3818_; 
v_snd_3816_ = lean_ctor_get(v_a_3811_, 1);
lean_inc(v_snd_3816_);
lean_dec(v_a_3811_);
if (v_isShared_3814_ == 0)
{
lean_ctor_set(v___x_3813_, 0, v_snd_3816_);
v___x_3818_ = v___x_3813_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v_snd_3816_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
else
{
lean_object* v_val_3820_; lean_object* v___x_3822_; 
lean_inc_ref(v_fst_3815_);
lean_dec(v_a_3811_);
v_val_3820_ = lean_ctor_get(v_fst_3815_, 0);
lean_inc(v_val_3820_);
lean_dec_ref(v_fst_3815_);
if (v_isShared_3814_ == 0)
{
lean_ctor_set(v___x_3813_, 0, v_val_3820_);
v___x_3822_ = v___x_3813_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v_val_3820_);
v___x_3822_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
return v___x_3822_;
}
}
}
}
else
{
lean_object* v_a_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3832_; 
v_a_3825_ = lean_ctor_get(v___x_3810_, 0);
v_isSharedCheck_3832_ = !lean_is_exclusive(v___x_3810_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3827_ = v___x_3810_;
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_a_3825_);
lean_dec(v___x_3810_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3830_; 
if (v_isShared_3828_ == 0)
{
v___x_3830_ = v___x_3827_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_a_3825_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
}
}
}
}
else
{
lean_object* v_a_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3841_; 
lean_dec_ref(v_tail_3795_);
v_a_3834_ = lean_ctor_get(v___x_3796_, 0);
v_isSharedCheck_3841_ = !lean_is_exclusive(v___x_3796_);
if (v_isSharedCheck_3841_ == 0)
{
v___x_3836_ = v___x_3796_;
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_a_3834_);
lean_dec(v___x_3796_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v___x_3839_; 
if (v_isShared_3837_ == 0)
{
v___x_3839_ = v___x_3836_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v_a_3834_);
v___x_3839_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
return v___x_3839_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0___boxed(lean_object* v_elimTrivial_3842_, lean_object* v_t_3843_, lean_object* v_init_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_){
_start:
{
uint8_t v_elimTrivial_boxed_3850_; lean_object* v_res_3851_; 
v_elimTrivial_boxed_3850_ = lean_unbox(v_elimTrivial_3842_);
v_res_3851_ = l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(v_elimTrivial_boxed_3850_, v_t_3843_, v_init_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_);
lean_dec(v___y_3848_);
lean_dec_ref(v___y_3847_);
lean_dec(v___y_3846_);
lean_dec_ref(v___y_3845_);
return v_res_3851_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(lean_object* v_as_3852_, size_t v_sz_3853_, size_t v_i_3854_, lean_object* v_b_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_){
_start:
{
uint8_t v___x_3861_; 
v___x_3861_ = lean_usize_dec_lt(v_i_3854_, v_sz_3853_);
if (v___x_3861_ == 0)
{
lean_object* v___x_3862_; 
v___x_3862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3862_, 0, v_b_3855_);
return v___x_3862_;
}
else
{
lean_object* v_a_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; 
v_a_3863_ = lean_array_uget_borrowed(v_as_3852_, v_i_3854_);
v___x_3864_ = l_Lean_Expr_fvarId_x21(v_a_3863_);
v___x_3865_ = l_Lean_MVarId_tryClear(v_b_3855_, v___x_3864_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_);
if (lean_obj_tag(v___x_3865_) == 0)
{
lean_object* v_a_3866_; size_t v___x_3867_; size_t v___x_3868_; 
v_a_3866_ = lean_ctor_get(v___x_3865_, 0);
lean_inc(v_a_3866_);
lean_dec_ref(v___x_3865_);
v___x_3867_ = ((size_t)1ULL);
v___x_3868_ = lean_usize_add(v_i_3854_, v___x_3867_);
v_i_3854_ = v___x_3868_;
v_b_3855_ = v_a_3866_;
goto _start;
}
else
{
return v___x_3865_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2___boxed(lean_object* v_as_3870_, lean_object* v_sz_3871_, lean_object* v_i_3872_, lean_object* v_b_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_){
_start:
{
size_t v_sz_boxed_3879_; size_t v_i_boxed_3880_; lean_object* v_res_3881_; 
v_sz_boxed_3879_ = lean_unbox_usize(v_sz_3871_);
lean_dec(v_sz_3871_);
v_i_boxed_3880_ = lean_unbox_usize(v_i_3872_);
lean_dec(v_i_3872_);
v_res_3881_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(v_as_3870_, v_sz_boxed_3879_, v_i_boxed_3880_, v_b_3873_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_);
lean_dec(v___y_3877_);
lean_dec_ref(v___y_3876_);
lean_dec(v___y_3875_);
lean_dec_ref(v___y_3874_);
lean_dec_ref(v_as_3870_);
return v_res_3881_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(lean_object* v_x_3882_, lean_object* v_x_3883_, lean_object* v_x_3884_, lean_object* v_x_3885_){
_start:
{
lean_object* v_ks_3886_; lean_object* v_vs_3887_; lean_object* v___x_3889_; uint8_t v_isShared_3890_; uint8_t v_isSharedCheck_3911_; 
v_ks_3886_ = lean_ctor_get(v_x_3882_, 0);
v_vs_3887_ = lean_ctor_get(v_x_3882_, 1);
v_isSharedCheck_3911_ = !lean_is_exclusive(v_x_3882_);
if (v_isSharedCheck_3911_ == 0)
{
v___x_3889_ = v_x_3882_;
v_isShared_3890_ = v_isSharedCheck_3911_;
goto v_resetjp_3888_;
}
else
{
lean_inc(v_vs_3887_);
lean_inc(v_ks_3886_);
lean_dec(v_x_3882_);
v___x_3889_ = lean_box(0);
v_isShared_3890_ = v_isSharedCheck_3911_;
goto v_resetjp_3888_;
}
v_resetjp_3888_:
{
lean_object* v___x_3891_; uint8_t v___x_3892_; 
v___x_3891_ = lean_array_get_size(v_ks_3886_);
v___x_3892_ = lean_nat_dec_lt(v_x_3883_, v___x_3891_);
if (v___x_3892_ == 0)
{
lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3896_; 
lean_dec(v_x_3883_);
v___x_3893_ = lean_array_push(v_ks_3886_, v_x_3884_);
v___x_3894_ = lean_array_push(v_vs_3887_, v_x_3885_);
if (v_isShared_3890_ == 0)
{
lean_ctor_set(v___x_3889_, 1, v___x_3894_);
lean_ctor_set(v___x_3889_, 0, v___x_3893_);
v___x_3896_ = v___x_3889_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v___x_3893_);
lean_ctor_set(v_reuseFailAlloc_3897_, 1, v___x_3894_);
v___x_3896_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
return v___x_3896_;
}
}
else
{
lean_object* v_k_x27_3898_; uint8_t v___x_3899_; 
v_k_x27_3898_ = lean_array_fget_borrowed(v_ks_3886_, v_x_3883_);
v___x_3899_ = l_Lean_instBEqMVarId_beq(v_x_3884_, v_k_x27_3898_);
if (v___x_3899_ == 0)
{
lean_object* v___x_3901_; 
if (v_isShared_3890_ == 0)
{
v___x_3901_ = v___x_3889_;
goto v_reusejp_3900_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v_ks_3886_);
lean_ctor_set(v_reuseFailAlloc_3905_, 1, v_vs_3887_);
v___x_3901_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3900_;
}
v_reusejp_3900_:
{
lean_object* v___x_3902_; lean_object* v___x_3903_; 
v___x_3902_ = lean_unsigned_to_nat(1u);
v___x_3903_ = lean_nat_add(v_x_3883_, v___x_3902_);
lean_dec(v_x_3883_);
v_x_3882_ = v___x_3901_;
v_x_3883_ = v___x_3903_;
goto _start;
}
}
else
{
lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3909_; 
v___x_3906_ = lean_array_fset(v_ks_3886_, v_x_3883_, v_x_3884_);
v___x_3907_ = lean_array_fset(v_vs_3887_, v_x_3883_, v_x_3885_);
lean_dec(v_x_3883_);
if (v_isShared_3890_ == 0)
{
lean_ctor_set(v___x_3889_, 1, v___x_3907_);
lean_ctor_set(v___x_3889_, 0, v___x_3906_);
v___x_3909_ = v___x_3889_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v___x_3906_);
lean_ctor_set(v_reuseFailAlloc_3910_, 1, v___x_3907_);
v___x_3909_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
return v___x_3909_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(lean_object* v_n_3912_, lean_object* v_k_3913_, lean_object* v_v_3914_){
_start:
{
lean_object* v___x_3915_; lean_object* v___x_3916_; 
v___x_3915_ = lean_unsigned_to_nat(0u);
v___x_3916_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(v_n_3912_, v___x_3915_, v_k_3913_, v_v_3914_);
return v___x_3916_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0(void){
_start:
{
size_t v___x_3917_; size_t v___x_3918_; size_t v___x_3919_; 
v___x_3917_ = ((size_t)5ULL);
v___x_3918_ = ((size_t)1ULL);
v___x_3919_ = lean_usize_shift_left(v___x_3918_, v___x_3917_);
return v___x_3919_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__1(void){
_start:
{
size_t v___x_3920_; size_t v___x_3921_; size_t v___x_3922_; 
v___x_3920_ = ((size_t)1ULL);
v___x_3921_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0);
v___x_3922_ = lean_usize_sub(v___x_3921_, v___x_3920_);
return v___x_3922_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_3923_; 
v___x_3923_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_3923_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(lean_object* v_x_3924_, size_t v_x_3925_, size_t v_x_3926_, lean_object* v_x_3927_, lean_object* v_x_3928_){
_start:
{
if (lean_obj_tag(v_x_3924_) == 0)
{
lean_object* v_es_3929_; size_t v___x_3930_; size_t v___x_3931_; size_t v___x_3932_; size_t v___x_3933_; lean_object* v_j_3934_; lean_object* v___x_3935_; uint8_t v___x_3936_; 
v_es_3929_ = lean_ctor_get(v_x_3924_, 0);
v___x_3930_ = ((size_t)5ULL);
v___x_3931_ = ((size_t)1ULL);
v___x_3932_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__1);
v___x_3933_ = lean_usize_land(v_x_3925_, v___x_3932_);
v_j_3934_ = lean_usize_to_nat(v___x_3933_);
v___x_3935_ = lean_array_get_size(v_es_3929_);
v___x_3936_ = lean_nat_dec_lt(v_j_3934_, v___x_3935_);
if (v___x_3936_ == 0)
{
lean_dec(v_j_3934_);
lean_dec(v_x_3928_);
lean_dec(v_x_3927_);
return v_x_3924_;
}
else
{
lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3973_; 
lean_inc_ref(v_es_3929_);
v_isSharedCheck_3973_ = !lean_is_exclusive(v_x_3924_);
if (v_isSharedCheck_3973_ == 0)
{
lean_object* v_unused_3974_; 
v_unused_3974_ = lean_ctor_get(v_x_3924_, 0);
lean_dec(v_unused_3974_);
v___x_3938_ = v_x_3924_;
v_isShared_3939_ = v_isSharedCheck_3973_;
goto v_resetjp_3937_;
}
else
{
lean_dec(v_x_3924_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_3973_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
lean_object* v_v_3940_; lean_object* v___x_3941_; lean_object* v_xs_x27_3942_; lean_object* v___y_3944_; 
v_v_3940_ = lean_array_fget(v_es_3929_, v_j_3934_);
v___x_3941_ = lean_box(0);
v_xs_x27_3942_ = lean_array_fset(v_es_3929_, v_j_3934_, v___x_3941_);
switch(lean_obj_tag(v_v_3940_))
{
case 0:
{
lean_object* v_key_3949_; lean_object* v_val_3950_; lean_object* v___x_3952_; uint8_t v_isShared_3953_; uint8_t v_isSharedCheck_3960_; 
v_key_3949_ = lean_ctor_get(v_v_3940_, 0);
v_val_3950_ = lean_ctor_get(v_v_3940_, 1);
v_isSharedCheck_3960_ = !lean_is_exclusive(v_v_3940_);
if (v_isSharedCheck_3960_ == 0)
{
v___x_3952_ = v_v_3940_;
v_isShared_3953_ = v_isSharedCheck_3960_;
goto v_resetjp_3951_;
}
else
{
lean_inc(v_val_3950_);
lean_inc(v_key_3949_);
lean_dec(v_v_3940_);
v___x_3952_ = lean_box(0);
v_isShared_3953_ = v_isSharedCheck_3960_;
goto v_resetjp_3951_;
}
v_resetjp_3951_:
{
uint8_t v___x_3954_; 
v___x_3954_ = l_Lean_instBEqMVarId_beq(v_x_3927_, v_key_3949_);
if (v___x_3954_ == 0)
{
lean_object* v___x_3955_; lean_object* v___x_3956_; 
lean_del_object(v___x_3952_);
v___x_3955_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3949_, v_val_3950_, v_x_3927_, v_x_3928_);
v___x_3956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3956_, 0, v___x_3955_);
v___y_3944_ = v___x_3956_;
goto v___jp_3943_;
}
else
{
lean_object* v___x_3958_; 
lean_dec(v_val_3950_);
lean_dec(v_key_3949_);
if (v_isShared_3953_ == 0)
{
lean_ctor_set(v___x_3952_, 1, v_x_3928_);
lean_ctor_set(v___x_3952_, 0, v_x_3927_);
v___x_3958_ = v___x_3952_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3959_; 
v_reuseFailAlloc_3959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3959_, 0, v_x_3927_);
lean_ctor_set(v_reuseFailAlloc_3959_, 1, v_x_3928_);
v___x_3958_ = v_reuseFailAlloc_3959_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
v___y_3944_ = v___x_3958_;
goto v___jp_3943_;
}
}
}
}
case 1:
{
lean_object* v_node_3961_; lean_object* v___x_3963_; uint8_t v_isShared_3964_; uint8_t v_isSharedCheck_3971_; 
v_node_3961_ = lean_ctor_get(v_v_3940_, 0);
v_isSharedCheck_3971_ = !lean_is_exclusive(v_v_3940_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3963_ = v_v_3940_;
v_isShared_3964_ = v_isSharedCheck_3971_;
goto v_resetjp_3962_;
}
else
{
lean_inc(v_node_3961_);
lean_dec(v_v_3940_);
v___x_3963_ = lean_box(0);
v_isShared_3964_ = v_isSharedCheck_3971_;
goto v_resetjp_3962_;
}
v_resetjp_3962_:
{
size_t v___x_3965_; size_t v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3969_; 
v___x_3965_ = lean_usize_shift_right(v_x_3925_, v___x_3930_);
v___x_3966_ = lean_usize_add(v_x_3926_, v___x_3931_);
v___x_3967_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_node_3961_, v___x_3965_, v___x_3966_, v_x_3927_, v_x_3928_);
if (v_isShared_3964_ == 0)
{
lean_ctor_set(v___x_3963_, 0, v___x_3967_);
v___x_3969_ = v___x_3963_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v___x_3967_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
v___y_3944_ = v___x_3969_;
goto v___jp_3943_;
}
}
}
default: 
{
lean_object* v___x_3972_; 
v___x_3972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3972_, 0, v_x_3927_);
lean_ctor_set(v___x_3972_, 1, v_x_3928_);
v___y_3944_ = v___x_3972_;
goto v___jp_3943_;
}
}
v___jp_3943_:
{
lean_object* v___x_3945_; lean_object* v___x_3947_; 
v___x_3945_ = lean_array_fset(v_xs_x27_3942_, v_j_3934_, v___y_3944_);
lean_dec(v_j_3934_);
if (v_isShared_3939_ == 0)
{
lean_ctor_set(v___x_3938_, 0, v___x_3945_);
v___x_3947_ = v___x_3938_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v___x_3945_);
v___x_3947_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
return v___x_3947_;
}
}
}
}
}
else
{
lean_object* v_ks_3975_; lean_object* v_vs_3976_; lean_object* v___x_3978_; uint8_t v_isShared_3979_; uint8_t v_isSharedCheck_3996_; 
v_ks_3975_ = lean_ctor_get(v_x_3924_, 0);
v_vs_3976_ = lean_ctor_get(v_x_3924_, 1);
v_isSharedCheck_3996_ = !lean_is_exclusive(v_x_3924_);
if (v_isSharedCheck_3996_ == 0)
{
v___x_3978_ = v_x_3924_;
v_isShared_3979_ = v_isSharedCheck_3996_;
goto v_resetjp_3977_;
}
else
{
lean_inc(v_vs_3976_);
lean_inc(v_ks_3975_);
lean_dec(v_x_3924_);
v___x_3978_ = lean_box(0);
v_isShared_3979_ = v_isSharedCheck_3996_;
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
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v_ks_3975_);
lean_ctor_set(v_reuseFailAlloc_3995_, 1, v_vs_3976_);
v___x_3981_ = v_reuseFailAlloc_3995_;
goto v_reusejp_3980_;
}
v_reusejp_3980_:
{
lean_object* v_newNode_3982_; uint8_t v___y_3984_; size_t v___x_3990_; uint8_t v___x_3991_; 
v_newNode_3982_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(v___x_3981_, v_x_3927_, v_x_3928_);
v___x_3990_ = ((size_t)7ULL);
v___x_3991_ = lean_usize_dec_le(v___x_3990_, v_x_3926_);
if (v___x_3991_ == 0)
{
lean_object* v___x_3992_; lean_object* v___x_3993_; uint8_t v___x_3994_; 
v___x_3992_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3982_);
v___x_3993_ = lean_unsigned_to_nat(4u);
v___x_3994_ = lean_nat_dec_lt(v___x_3992_, v___x_3993_);
lean_dec(v___x_3992_);
v___y_3984_ = v___x_3994_;
goto v___jp_3983_;
}
else
{
v___y_3984_ = v___x_3991_;
goto v___jp_3983_;
}
v___jp_3983_:
{
if (v___y_3984_ == 0)
{
lean_object* v_ks_3985_; lean_object* v_vs_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; 
v_ks_3985_ = lean_ctor_get(v_newNode_3982_, 0);
lean_inc_ref(v_ks_3985_);
v_vs_3986_ = lean_ctor_get(v_newNode_3982_, 1);
lean_inc_ref(v_vs_3986_);
lean_dec_ref(v_newNode_3982_);
v___x_3987_ = lean_unsigned_to_nat(0u);
v___x_3988_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__2);
v___x_3989_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_x_3926_, v_ks_3985_, v_vs_3986_, v___x_3987_, v___x_3988_);
lean_dec_ref(v_vs_3986_);
lean_dec_ref(v_ks_3985_);
return v___x_3989_;
}
else
{
return v_newNode_3982_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(size_t v_depth_3997_, lean_object* v_keys_3998_, lean_object* v_vals_3999_, lean_object* v_i_4000_, lean_object* v_entries_4001_){
_start:
{
lean_object* v___x_4002_; uint8_t v___x_4003_; 
v___x_4002_ = lean_array_get_size(v_keys_3998_);
v___x_4003_ = lean_nat_dec_lt(v_i_4000_, v___x_4002_);
if (v___x_4003_ == 0)
{
lean_dec(v_i_4000_);
return v_entries_4001_;
}
else
{
lean_object* v_k_4004_; lean_object* v_v_4005_; uint64_t v___x_4006_; size_t v_h_4007_; size_t v___x_4008_; lean_object* v___x_4009_; size_t v___x_4010_; size_t v___x_4011_; size_t v___x_4012_; size_t v_h_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; 
v_k_4004_ = lean_array_fget_borrowed(v_keys_3998_, v_i_4000_);
v_v_4005_ = lean_array_fget_borrowed(v_vals_3999_, v_i_4000_);
v___x_4006_ = l_Lean_instHashableMVarId_hash(v_k_4004_);
v_h_4007_ = lean_uint64_to_usize(v___x_4006_);
v___x_4008_ = ((size_t)5ULL);
v___x_4009_ = lean_unsigned_to_nat(1u);
v___x_4010_ = ((size_t)1ULL);
v___x_4011_ = lean_usize_sub(v_depth_3997_, v___x_4010_);
v___x_4012_ = lean_usize_mul(v___x_4008_, v___x_4011_);
v_h_4013_ = lean_usize_shift_right(v_h_4007_, v___x_4012_);
v___x_4014_ = lean_nat_add(v_i_4000_, v___x_4009_);
lean_dec(v_i_4000_);
lean_inc(v_v_4005_);
lean_inc(v_k_4004_);
v___x_4015_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_entries_4001_, v_h_4013_, v_depth_3997_, v_k_4004_, v_v_4005_);
v_i_4000_ = v___x_4014_;
v_entries_4001_ = v___x_4015_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg___boxed(lean_object* v_depth_4017_, lean_object* v_keys_4018_, lean_object* v_vals_4019_, lean_object* v_i_4020_, lean_object* v_entries_4021_){
_start:
{
size_t v_depth_boxed_4022_; lean_object* v_res_4023_; 
v_depth_boxed_4022_ = lean_unbox_usize(v_depth_4017_);
lean_dec(v_depth_4017_);
v_res_4023_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_depth_boxed_4022_, v_keys_4018_, v_vals_4019_, v_i_4020_, v_entries_4021_);
lean_dec_ref(v_vals_4019_);
lean_dec_ref(v_keys_4018_);
return v_res_4023_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___boxed(lean_object* v_x_4024_, lean_object* v_x_4025_, lean_object* v_x_4026_, lean_object* v_x_4027_, lean_object* v_x_4028_){
_start:
{
size_t v_x_7996__boxed_4029_; size_t v_x_7997__boxed_4030_; lean_object* v_res_4031_; 
v_x_7996__boxed_4029_ = lean_unbox_usize(v_x_4025_);
lean_dec(v_x_4025_);
v_x_7997__boxed_4030_ = lean_unbox_usize(v_x_4026_);
lean_dec(v_x_4026_);
v_res_4031_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_4024_, v_x_7996__boxed_4029_, v_x_7997__boxed_4030_, v_x_4027_, v_x_4028_);
return v_res_4031_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(lean_object* v_x_4032_, lean_object* v_x_4033_, lean_object* v_x_4034_){
_start:
{
uint64_t v___x_4035_; size_t v___x_4036_; size_t v___x_4037_; lean_object* v___x_4038_; 
v___x_4035_ = l_Lean_instHashableMVarId_hash(v_x_4033_);
v___x_4036_ = lean_uint64_to_usize(v___x_4035_);
v___x_4037_ = ((size_t)1ULL);
v___x_4038_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_4032_, v___x_4036_, v___x_4037_, v_x_4033_, v_x_4034_);
return v___x_4038_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(lean_object* v_mvarId_4039_, lean_object* v_val_4040_, lean_object* v___y_4041_){
_start:
{
lean_object* v___x_4043_; lean_object* v_mctx_4044_; lean_object* v_cache_4045_; lean_object* v_zetaDeltaFVarIds_4046_; lean_object* v_postponed_4047_; lean_object* v_diag_4048_; lean_object* v___x_4050_; uint8_t v_isShared_4051_; uint8_t v_isSharedCheck_4076_; 
v___x_4043_ = lean_st_ref_take(v___y_4041_);
v_mctx_4044_ = lean_ctor_get(v___x_4043_, 0);
v_cache_4045_ = lean_ctor_get(v___x_4043_, 1);
v_zetaDeltaFVarIds_4046_ = lean_ctor_get(v___x_4043_, 2);
v_postponed_4047_ = lean_ctor_get(v___x_4043_, 3);
v_diag_4048_ = lean_ctor_get(v___x_4043_, 4);
v_isSharedCheck_4076_ = !lean_is_exclusive(v___x_4043_);
if (v_isSharedCheck_4076_ == 0)
{
v___x_4050_ = v___x_4043_;
v_isShared_4051_ = v_isSharedCheck_4076_;
goto v_resetjp_4049_;
}
else
{
lean_inc(v_diag_4048_);
lean_inc(v_postponed_4047_);
lean_inc(v_zetaDeltaFVarIds_4046_);
lean_inc(v_cache_4045_);
lean_inc(v_mctx_4044_);
lean_dec(v___x_4043_);
v___x_4050_ = lean_box(0);
v_isShared_4051_ = v_isSharedCheck_4076_;
goto v_resetjp_4049_;
}
v_resetjp_4049_:
{
lean_object* v_depth_4052_; lean_object* v_levelAssignDepth_4053_; lean_object* v_lmvarCounter_4054_; lean_object* v_mvarCounter_4055_; lean_object* v_lDecls_4056_; lean_object* v_decls_4057_; lean_object* v_userNames_4058_; lean_object* v_lAssignment_4059_; lean_object* v_eAssignment_4060_; lean_object* v_dAssignment_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4075_; 
v_depth_4052_ = lean_ctor_get(v_mctx_4044_, 0);
v_levelAssignDepth_4053_ = lean_ctor_get(v_mctx_4044_, 1);
v_lmvarCounter_4054_ = lean_ctor_get(v_mctx_4044_, 2);
v_mvarCounter_4055_ = lean_ctor_get(v_mctx_4044_, 3);
v_lDecls_4056_ = lean_ctor_get(v_mctx_4044_, 4);
v_decls_4057_ = lean_ctor_get(v_mctx_4044_, 5);
v_userNames_4058_ = lean_ctor_get(v_mctx_4044_, 6);
v_lAssignment_4059_ = lean_ctor_get(v_mctx_4044_, 7);
v_eAssignment_4060_ = lean_ctor_get(v_mctx_4044_, 8);
v_dAssignment_4061_ = lean_ctor_get(v_mctx_4044_, 9);
v_isSharedCheck_4075_ = !lean_is_exclusive(v_mctx_4044_);
if (v_isSharedCheck_4075_ == 0)
{
v___x_4063_ = v_mctx_4044_;
v_isShared_4064_ = v_isSharedCheck_4075_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_dAssignment_4061_);
lean_inc(v_eAssignment_4060_);
lean_inc(v_lAssignment_4059_);
lean_inc(v_userNames_4058_);
lean_inc(v_decls_4057_);
lean_inc(v_lDecls_4056_);
lean_inc(v_mvarCounter_4055_);
lean_inc(v_lmvarCounter_4054_);
lean_inc(v_levelAssignDepth_4053_);
lean_inc(v_depth_4052_);
lean_dec(v_mctx_4044_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4075_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
lean_object* v___x_4065_; lean_object* v___x_4067_; 
v___x_4065_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(v_eAssignment_4060_, v_mvarId_4039_, v_val_4040_);
if (v_isShared_4064_ == 0)
{
lean_ctor_set(v___x_4063_, 8, v___x_4065_);
v___x_4067_ = v___x_4063_;
goto v_reusejp_4066_;
}
else
{
lean_object* v_reuseFailAlloc_4074_; 
v_reuseFailAlloc_4074_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4074_, 0, v_depth_4052_);
lean_ctor_set(v_reuseFailAlloc_4074_, 1, v_levelAssignDepth_4053_);
lean_ctor_set(v_reuseFailAlloc_4074_, 2, v_lmvarCounter_4054_);
lean_ctor_set(v_reuseFailAlloc_4074_, 3, v_mvarCounter_4055_);
lean_ctor_set(v_reuseFailAlloc_4074_, 4, v_lDecls_4056_);
lean_ctor_set(v_reuseFailAlloc_4074_, 5, v_decls_4057_);
lean_ctor_set(v_reuseFailAlloc_4074_, 6, v_userNames_4058_);
lean_ctor_set(v_reuseFailAlloc_4074_, 7, v_lAssignment_4059_);
lean_ctor_set(v_reuseFailAlloc_4074_, 8, v___x_4065_);
lean_ctor_set(v_reuseFailAlloc_4074_, 9, v_dAssignment_4061_);
v___x_4067_ = v_reuseFailAlloc_4074_;
goto v_reusejp_4066_;
}
v_reusejp_4066_:
{
lean_object* v___x_4069_; 
if (v_isShared_4051_ == 0)
{
lean_ctor_set(v___x_4050_, 0, v___x_4067_);
v___x_4069_ = v___x_4050_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4073_; 
v_reuseFailAlloc_4073_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4073_, 0, v___x_4067_);
lean_ctor_set(v_reuseFailAlloc_4073_, 1, v_cache_4045_);
lean_ctor_set(v_reuseFailAlloc_4073_, 2, v_zetaDeltaFVarIds_4046_);
lean_ctor_set(v_reuseFailAlloc_4073_, 3, v_postponed_4047_);
lean_ctor_set(v_reuseFailAlloc_4073_, 4, v_diag_4048_);
v___x_4069_ = v_reuseFailAlloc_4073_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; 
v___x_4070_ = lean_st_ref_set(v___y_4041_, v___x_4069_);
v___x_4071_ = lean_box(0);
v___x_4072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4072_, 0, v___x_4071_);
return v___x_4072_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg___boxed(lean_object* v_mvarId_4077_, lean_object* v_val_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_){
_start:
{
lean_object* v_res_4081_; 
v_res_4081_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(v_mvarId_4077_, v_val_4078_, v___y_4079_);
lean_dec(v___y_4079_);
return v_res_4081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___lam__0(lean_object* v_mvar_4084_, uint8_t v_elimTrivial_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_){
_start:
{
lean_object* v___x_4091_; 
lean_inc(v_mvar_4084_);
v___x_4091_ = l_Lean_MVarId_getType(v_mvar_4084_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_);
if (lean_obj_tag(v___x_4091_) == 0)
{
lean_object* v_a_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; 
v_a_4092_ = lean_ctor_get(v___x_4091_, 0);
lean_inc(v_a_4092_);
lean_dec_ref(v___x_4091_);
v___x_4093_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0));
v___x_4094_ = l_Lean_Elab_Tactic_Do_countUses(v_a_4092_, v___x_4093_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_);
if (lean_obj_tag(v___x_4094_) == 0)
{
lean_object* v_a_4095_; lean_object* v_fst_4096_; lean_object* v_snd_4097_; lean_object* v_lctx_4098_; lean_object* v___x_4099_; 
v_a_4095_ = lean_ctor_get(v___x_4094_, 0);
lean_inc(v_a_4095_);
lean_dec_ref(v___x_4094_);
v_fst_4096_ = lean_ctor_get(v_a_4095_, 0);
lean_inc(v_fst_4096_);
v_snd_4097_ = lean_ctor_get(v_a_4095_, 1);
lean_inc(v_snd_4097_);
lean_dec(v_a_4095_);
v_lctx_4098_ = lean_ctor_get(v___y_4086_, 2);
lean_inc_ref(v_lctx_4098_);
v___x_4099_ = l_Lean_Elab_Tactic_Do_countUsesLCtx(v_lctx_4098_, v_snd_4097_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_);
if (lean_obj_tag(v___x_4099_) == 0)
{
lean_object* v_a_4100_; lean_object* v___x_4101_; lean_object* v_decls_4102_; lean_object* v___x_4103_; 
v_a_4100_ = lean_ctor_get(v___x_4099_, 0);
lean_inc(v_a_4100_);
lean_dec_ref(v___x_4099_);
v___x_4101_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLets___lam__0___closed__0));
v_decls_4102_ = lean_ctor_get(v_a_4100_, 1);
lean_inc_ref(v_decls_4102_);
lean_dec(v_a_4100_);
v___x_4103_ = l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(v_elimTrivial_4085_, v_decls_4102_, v___x_4101_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_);
if (lean_obj_tag(v___x_4103_) == 0)
{
lean_object* v_a_4104_; lean_object* v_fst_4105_; lean_object* v_snd_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; 
v_a_4104_ = lean_ctor_get(v___x_4103_, 0);
lean_inc(v_a_4104_);
lean_dec_ref(v___x_4103_);
v_fst_4105_ = lean_ctor_get(v_a_4104_, 0);
lean_inc(v_fst_4105_);
v_snd_4106_ = lean_ctor_get(v_a_4104_, 1);
lean_inc(v_snd_4106_);
lean_dec(v_a_4104_);
v___x_4107_ = l_Lean_Expr_replaceFVars(v_fst_4096_, v_fst_4105_, v_snd_4106_);
lean_dec(v_snd_4106_);
lean_dec(v_fst_4096_);
v___x_4108_ = l_Lean_Elab_Tactic_Do_elimLetsCore(v___x_4107_, v_elimTrivial_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_);
if (lean_obj_tag(v___x_4108_) == 0)
{
lean_object* v_a_4109_; lean_object* v___x_4110_; 
v_a_4109_ = lean_ctor_get(v___x_4108_, 0);
lean_inc(v_a_4109_);
lean_dec_ref(v___x_4108_);
lean_inc(v_mvar_4084_);
v___x_4110_ = l_Lean_MVarId_getTag(v_mvar_4084_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_);
if (lean_obj_tag(v___x_4110_) == 0)
{
lean_object* v_a_4111_; lean_object* v___x_4112_; 
v_a_4111_ = lean_ctor_get(v___x_4110_, 0);
lean_inc(v_a_4111_);
lean_dec_ref(v___x_4110_);
v___x_4112_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_4109_, v_a_4111_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_);
if (lean_obj_tag(v___x_4112_) == 0)
{
lean_object* v_a_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; size_t v_sz_4116_; size_t v___x_4117_; lean_object* v___x_4118_; 
v_a_4113_ = lean_ctor_get(v___x_4112_, 0);
lean_inc_n(v_a_4113_, 2);
lean_dec_ref(v___x_4112_);
v___x_4114_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(v_mvar_4084_, v_a_4113_, v___y_4087_);
lean_dec_ref(v___x_4114_);
v___x_4115_ = l_Lean_Expr_mvarId_x21(v_a_4113_);
lean_dec(v_a_4113_);
v_sz_4116_ = lean_array_size(v_fst_4105_);
v___x_4117_ = ((size_t)0ULL);
v___x_4118_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(v_fst_4105_, v_sz_4116_, v___x_4117_, v___x_4115_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_);
lean_dec_ref(v___y_4086_);
lean_dec(v_fst_4105_);
return v___x_4118_;
}
else
{
lean_object* v_a_4119_; lean_object* v___x_4121_; uint8_t v_isShared_4122_; uint8_t v_isSharedCheck_4126_; 
lean_dec(v_fst_4105_);
lean_dec_ref(v___y_4086_);
lean_dec(v_mvar_4084_);
v_a_4119_ = lean_ctor_get(v___x_4112_, 0);
v_isSharedCheck_4126_ = !lean_is_exclusive(v___x_4112_);
if (v_isSharedCheck_4126_ == 0)
{
v___x_4121_ = v___x_4112_;
v_isShared_4122_ = v_isSharedCheck_4126_;
goto v_resetjp_4120_;
}
else
{
lean_inc(v_a_4119_);
lean_dec(v___x_4112_);
v___x_4121_ = lean_box(0);
v_isShared_4122_ = v_isSharedCheck_4126_;
goto v_resetjp_4120_;
}
v_resetjp_4120_:
{
lean_object* v___x_4124_; 
if (v_isShared_4122_ == 0)
{
v___x_4124_ = v___x_4121_;
goto v_reusejp_4123_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v_a_4119_);
v___x_4124_ = v_reuseFailAlloc_4125_;
goto v_reusejp_4123_;
}
v_reusejp_4123_:
{
return v___x_4124_;
}
}
}
}
else
{
lean_object* v_a_4127_; lean_object* v___x_4129_; uint8_t v_isShared_4130_; uint8_t v_isSharedCheck_4134_; 
lean_dec(v_a_4109_);
lean_dec(v_fst_4105_);
lean_dec_ref(v___y_4086_);
lean_dec(v_mvar_4084_);
v_a_4127_ = lean_ctor_get(v___x_4110_, 0);
v_isSharedCheck_4134_ = !lean_is_exclusive(v___x_4110_);
if (v_isSharedCheck_4134_ == 0)
{
v___x_4129_ = v___x_4110_;
v_isShared_4130_ = v_isSharedCheck_4134_;
goto v_resetjp_4128_;
}
else
{
lean_inc(v_a_4127_);
lean_dec(v___x_4110_);
v___x_4129_ = lean_box(0);
v_isShared_4130_ = v_isSharedCheck_4134_;
goto v_resetjp_4128_;
}
v_resetjp_4128_:
{
lean_object* v___x_4132_; 
if (v_isShared_4130_ == 0)
{
v___x_4132_ = v___x_4129_;
goto v_reusejp_4131_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v_a_4127_);
v___x_4132_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4131_;
}
v_reusejp_4131_:
{
return v___x_4132_;
}
}
}
}
else
{
lean_object* v_a_4135_; lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4142_; 
lean_dec(v_fst_4105_);
lean_dec_ref(v___y_4086_);
lean_dec(v_mvar_4084_);
v_a_4135_ = lean_ctor_get(v___x_4108_, 0);
v_isSharedCheck_4142_ = !lean_is_exclusive(v___x_4108_);
if (v_isSharedCheck_4142_ == 0)
{
v___x_4137_ = v___x_4108_;
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
else
{
lean_inc(v_a_4135_);
lean_dec(v___x_4108_);
v___x_4137_ = lean_box(0);
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
v_resetjp_4136_:
{
lean_object* v___x_4140_; 
if (v_isShared_4138_ == 0)
{
v___x_4140_ = v___x_4137_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v_a_4135_);
v___x_4140_ = v_reuseFailAlloc_4141_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
return v___x_4140_;
}
}
}
}
else
{
lean_object* v_a_4143_; lean_object* v___x_4145_; uint8_t v_isShared_4146_; uint8_t v_isSharedCheck_4150_; 
lean_dec(v_fst_4096_);
lean_dec_ref(v___y_4086_);
lean_dec(v_mvar_4084_);
v_a_4143_ = lean_ctor_get(v___x_4103_, 0);
v_isSharedCheck_4150_ = !lean_is_exclusive(v___x_4103_);
if (v_isSharedCheck_4150_ == 0)
{
v___x_4145_ = v___x_4103_;
v_isShared_4146_ = v_isSharedCheck_4150_;
goto v_resetjp_4144_;
}
else
{
lean_inc(v_a_4143_);
lean_dec(v___x_4103_);
v___x_4145_ = lean_box(0);
v_isShared_4146_ = v_isSharedCheck_4150_;
goto v_resetjp_4144_;
}
v_resetjp_4144_:
{
lean_object* v___x_4148_; 
if (v_isShared_4146_ == 0)
{
v___x_4148_ = v___x_4145_;
goto v_reusejp_4147_;
}
else
{
lean_object* v_reuseFailAlloc_4149_; 
v_reuseFailAlloc_4149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4149_, 0, v_a_4143_);
v___x_4148_ = v_reuseFailAlloc_4149_;
goto v_reusejp_4147_;
}
v_reusejp_4147_:
{
return v___x_4148_;
}
}
}
}
else
{
lean_object* v_a_4151_; lean_object* v___x_4153_; uint8_t v_isShared_4154_; uint8_t v_isSharedCheck_4158_; 
lean_dec(v_fst_4096_);
lean_dec_ref(v___y_4086_);
lean_dec(v_mvar_4084_);
v_a_4151_ = lean_ctor_get(v___x_4099_, 0);
v_isSharedCheck_4158_ = !lean_is_exclusive(v___x_4099_);
if (v_isSharedCheck_4158_ == 0)
{
v___x_4153_ = v___x_4099_;
v_isShared_4154_ = v_isSharedCheck_4158_;
goto v_resetjp_4152_;
}
else
{
lean_inc(v_a_4151_);
lean_dec(v___x_4099_);
v___x_4153_ = lean_box(0);
v_isShared_4154_ = v_isSharedCheck_4158_;
goto v_resetjp_4152_;
}
v_resetjp_4152_:
{
lean_object* v___x_4156_; 
if (v_isShared_4154_ == 0)
{
v___x_4156_ = v___x_4153_;
goto v_reusejp_4155_;
}
else
{
lean_object* v_reuseFailAlloc_4157_; 
v_reuseFailAlloc_4157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4157_, 0, v_a_4151_);
v___x_4156_ = v_reuseFailAlloc_4157_;
goto v_reusejp_4155_;
}
v_reusejp_4155_:
{
return v___x_4156_;
}
}
}
}
else
{
lean_object* v_a_4159_; lean_object* v___x_4161_; uint8_t v_isShared_4162_; uint8_t v_isSharedCheck_4166_; 
lean_dec_ref(v___y_4086_);
lean_dec(v_mvar_4084_);
v_a_4159_ = lean_ctor_get(v___x_4094_, 0);
v_isSharedCheck_4166_ = !lean_is_exclusive(v___x_4094_);
if (v_isSharedCheck_4166_ == 0)
{
v___x_4161_ = v___x_4094_;
v_isShared_4162_ = v_isSharedCheck_4166_;
goto v_resetjp_4160_;
}
else
{
lean_inc(v_a_4159_);
lean_dec(v___x_4094_);
v___x_4161_ = lean_box(0);
v_isShared_4162_ = v_isSharedCheck_4166_;
goto v_resetjp_4160_;
}
v_resetjp_4160_:
{
lean_object* v___x_4164_; 
if (v_isShared_4162_ == 0)
{
v___x_4164_ = v___x_4161_;
goto v_reusejp_4163_;
}
else
{
lean_object* v_reuseFailAlloc_4165_; 
v_reuseFailAlloc_4165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4165_, 0, v_a_4159_);
v___x_4164_ = v_reuseFailAlloc_4165_;
goto v_reusejp_4163_;
}
v_reusejp_4163_:
{
return v___x_4164_;
}
}
}
}
else
{
lean_object* v_a_4167_; lean_object* v___x_4169_; uint8_t v_isShared_4170_; uint8_t v_isSharedCheck_4174_; 
lean_dec_ref(v___y_4086_);
lean_dec(v_mvar_4084_);
v_a_4167_ = lean_ctor_get(v___x_4091_, 0);
v_isSharedCheck_4174_ = !lean_is_exclusive(v___x_4091_);
if (v_isSharedCheck_4174_ == 0)
{
v___x_4169_ = v___x_4091_;
v_isShared_4170_ = v_isSharedCheck_4174_;
goto v_resetjp_4168_;
}
else
{
lean_inc(v_a_4167_);
lean_dec(v___x_4091_);
v___x_4169_ = lean_box(0);
v_isShared_4170_ = v_isSharedCheck_4174_;
goto v_resetjp_4168_;
}
v_resetjp_4168_:
{
lean_object* v___x_4172_; 
if (v_isShared_4170_ == 0)
{
v___x_4172_ = v___x_4169_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4173_; 
v_reuseFailAlloc_4173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4173_, 0, v_a_4167_);
v___x_4172_ = v_reuseFailAlloc_4173_;
goto v_reusejp_4171_;
}
v_reusejp_4171_:
{
return v___x_4172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___lam__0___boxed(lean_object* v_mvar_4175_, lean_object* v_elimTrivial_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_){
_start:
{
uint8_t v_elimTrivial_boxed_4182_; lean_object* v_res_4183_; 
v_elimTrivial_boxed_4182_ = lean_unbox(v_elimTrivial_4176_);
v_res_4183_ = l_Lean_Elab_Tactic_Do_elimLets___lam__0(v_mvar_4175_, v_elimTrivial_boxed_4182_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_);
lean_dec(v___y_4180_);
lean_dec_ref(v___y_4179_);
lean_dec(v___y_4178_);
return v_res_4183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets(lean_object* v_mvar_4184_, uint8_t v_elimTrivial_4185_, lean_object* v_a_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_){
_start:
{
lean_object* v___x_4191_; lean_object* v___f_4192_; lean_object* v___x_4193_; 
v___x_4191_ = lean_box(v_elimTrivial_4185_);
lean_inc(v_mvar_4184_);
v___f_4192_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elimLets___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4192_, 0, v_mvar_4184_);
lean_closure_set(v___f_4192_, 1, v___x_4191_);
v___x_4193_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(v_mvar_4184_, v___f_4192_, v_a_4186_, v_a_4187_, v_a_4188_, v_a_4189_);
return v___x_4193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___boxed(lean_object* v_mvar_4194_, lean_object* v_elimTrivial_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_){
_start:
{
uint8_t v_elimTrivial_boxed_4201_; lean_object* v_res_4202_; 
v_elimTrivial_boxed_4201_ = lean_unbox(v_elimTrivial_4195_);
v_res_4202_ = l_Lean_Elab_Tactic_Do_elimLets(v_mvar_4194_, v_elimTrivial_boxed_4201_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_);
lean_dec(v_a_4199_);
lean_dec_ref(v_a_4198_);
lean_dec(v_a_4197_);
lean_dec_ref(v_a_4196_);
return v_res_4202_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1(lean_object* v_mvarId_4203_, lean_object* v_val_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_){
_start:
{
lean_object* v___x_4210_; 
v___x_4210_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(v_mvarId_4203_, v_val_4204_, v___y_4206_);
return v___x_4210_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___boxed(lean_object* v_mvarId_4211_, lean_object* v_val_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_){
_start:
{
lean_object* v_res_4218_; 
v_res_4218_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1(v_mvarId_4211_, v_val_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_);
lean_dec(v___y_4216_);
lean_dec_ref(v___y_4215_);
lean_dec(v___y_4214_);
lean_dec_ref(v___y_4213_);
return v_res_4218_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3(lean_object* v_00_u03b2_4219_, lean_object* v_x_4220_, lean_object* v_x_4221_, lean_object* v_x_4222_){
_start:
{
lean_object* v___x_4223_; 
v___x_4223_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(v_x_4220_, v_x_4221_, v_x_4222_);
return v___x_4223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5(uint8_t v_elimTrivial_4224_, lean_object* v_as_4225_, size_t v_sz_4226_, size_t v_i_4227_, lean_object* v_b_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_){
_start:
{
lean_object* v___x_4234_; 
v___x_4234_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_4224_, v_as_4225_, v_sz_4226_, v_i_4227_, v_b_4228_);
return v___x_4234_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___boxed(lean_object* v_elimTrivial_4235_, lean_object* v_as_4236_, lean_object* v_sz_4237_, lean_object* v_i_4238_, lean_object* v_b_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_){
_start:
{
uint8_t v_elimTrivial_boxed_4245_; size_t v_sz_boxed_4246_; size_t v_i_boxed_4247_; lean_object* v_res_4248_; 
v_elimTrivial_boxed_4245_ = lean_unbox(v_elimTrivial_4235_);
v_sz_boxed_4246_ = lean_unbox_usize(v_sz_4237_);
lean_dec(v_sz_4237_);
v_i_boxed_4247_ = lean_unbox_usize(v_i_4238_);
lean_dec(v_i_4238_);
v_res_4248_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5(v_elimTrivial_boxed_4245_, v_as_4236_, v_sz_boxed_4246_, v_i_boxed_4247_, v_b_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_);
lean_dec(v___y_4243_);
lean_dec_ref(v___y_4242_);
lean_dec(v___y_4241_);
lean_dec_ref(v___y_4240_);
lean_dec_ref(v_as_4236_);
return v_res_4248_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_4249_, lean_object* v_x_4250_, size_t v_x_4251_, size_t v_x_4252_, lean_object* v_x_4253_, lean_object* v_x_4254_){
_start:
{
lean_object* v___x_4255_; 
v___x_4255_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_4250_, v_x_4251_, v_x_4252_, v_x_4253_, v_x_4254_);
return v___x_4255_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___boxed(lean_object* v_00_u03b2_4256_, lean_object* v_x_4257_, lean_object* v_x_4258_, lean_object* v_x_4259_, lean_object* v_x_4260_, lean_object* v_x_4261_){
_start:
{
size_t v_x_8452__boxed_4262_; size_t v_x_8453__boxed_4263_; lean_object* v_res_4264_; 
v_x_8452__boxed_4262_ = lean_unbox_usize(v_x_4258_);
lean_dec(v_x_4258_);
v_x_8453__boxed_4263_ = lean_unbox_usize(v_x_4259_);
lean_dec(v_x_4259_);
v_res_4264_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8(v_00_u03b2_4256_, v_x_4257_, v_x_8452__boxed_4262_, v_x_8453__boxed_4263_, v_x_4260_, v_x_4261_);
return v_res_4264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6(uint8_t v_elimTrivial_4265_, lean_object* v_as_4266_, size_t v_sz_4267_, size_t v_i_4268_, lean_object* v_b_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_){
_start:
{
lean_object* v___x_4275_; 
v___x_4275_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_4265_, v_as_4266_, v_sz_4267_, v_i_4268_, v_b_4269_);
return v___x_4275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___boxed(lean_object* v_elimTrivial_4276_, lean_object* v_as_4277_, lean_object* v_sz_4278_, lean_object* v_i_4279_, lean_object* v_b_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_){
_start:
{
uint8_t v_elimTrivial_boxed_4286_; size_t v_sz_boxed_4287_; size_t v_i_boxed_4288_; lean_object* v_res_4289_; 
v_elimTrivial_boxed_4286_ = lean_unbox(v_elimTrivial_4276_);
v_sz_boxed_4287_ = lean_unbox_usize(v_sz_4278_);
lean_dec(v_sz_4278_);
v_i_boxed_4288_ = lean_unbox_usize(v_i_4279_);
lean_dec(v_i_4279_);
v_res_4289_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6(v_elimTrivial_boxed_4286_, v_as_4277_, v_sz_boxed_4287_, v_i_boxed_4288_, v_b_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_);
lean_dec(v___y_4284_);
lean_dec_ref(v___y_4283_);
lean_dec(v___y_4282_);
lean_dec_ref(v___y_4281_);
lean_dec_ref(v_as_4277_);
return v_res_4289_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11(lean_object* v_00_u03b2_4290_, lean_object* v_n_4291_, lean_object* v_k_4292_, lean_object* v_v_4293_){
_start:
{
lean_object* v___x_4294_; 
v___x_4294_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(v_n_4291_, v_k_4292_, v_v_4293_);
return v___x_4294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12(lean_object* v_00_u03b2_4295_, size_t v_depth_4296_, lean_object* v_keys_4297_, lean_object* v_vals_4298_, lean_object* v_heq_4299_, lean_object* v_i_4300_, lean_object* v_entries_4301_){
_start:
{
lean_object* v___x_4302_; 
v___x_4302_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_depth_4296_, v_keys_4297_, v_vals_4298_, v_i_4300_, v_entries_4301_);
return v___x_4302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___boxed(lean_object* v_00_u03b2_4303_, lean_object* v_depth_4304_, lean_object* v_keys_4305_, lean_object* v_vals_4306_, lean_object* v_heq_4307_, lean_object* v_i_4308_, lean_object* v_entries_4309_){
_start:
{
size_t v_depth_boxed_4310_; lean_object* v_res_4311_; 
v_depth_boxed_4310_ = lean_unbox_usize(v_depth_4304_);
lean_dec(v_depth_4304_);
v_res_4311_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12(v_00_u03b2_4303_, v_depth_boxed_4310_, v_keys_4305_, v_vals_4306_, v_heq_4307_, v_i_4308_, v_entries_4309_);
lean_dec_ref(v_vals_4306_);
lean_dec_ref(v_keys_4305_);
return v_res_4311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12(lean_object* v_00_u03b2_4312_, lean_object* v_x_4313_, lean_object* v_x_4314_, lean_object* v_x_4315_, lean_object* v_x_4316_){
_start:
{
lean_object* v___x_4317_; 
v___x_4317_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(v_x_4313_, v_x_4314_, v_x_4315_, v_x_4316_);
return v___x_4317_;
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
