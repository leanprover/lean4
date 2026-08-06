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
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Elab_Tactic_Do_Uses_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
uint8_t v_t_boxed_21_; lean_object* v_res_22_; 
v_t_boxed_21_ = lean_unbox(v_t_18_);
v_res_22_ = l_Lean_Elab_Tactic_Do_Uses_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_boxed_21_, v_h_19_, v_k_20_);
lean_dec(v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim___redArg(lean_object* v_zero_23_){
_start:
{
lean_inc(v_zero_23_);
return v_zero_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim___redArg___boxed(lean_object* v_zero_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_Elab_Tactic_Do_Uses_zero_elim___redArg(v_zero_24_);
lean_dec(v_zero_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim(lean_object* v_motive_26_, uint8_t v_t_27_, lean_object* v_h_28_, lean_object* v_zero_29_){
_start:
{
lean_inc(v_zero_29_);
return v_zero_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim___boxed(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_zero_33_){
_start:
{
uint8_t v_t_boxed_34_; lean_object* v_res_35_; 
v_t_boxed_34_ = lean_unbox(v_t_31_);
v_res_35_ = l_Lean_Elab_Tactic_Do_Uses_zero_elim(v_motive_30_, v_t_boxed_34_, v_h_32_, v_zero_33_);
lean_dec(v_zero_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim___redArg(lean_object* v_one_36_){
_start:
{
lean_inc(v_one_36_);
return v_one_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim___redArg___boxed(lean_object* v_one_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Elab_Tactic_Do_Uses_one_elim___redArg(v_one_37_);
lean_dec(v_one_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim(lean_object* v_motive_39_, uint8_t v_t_40_, lean_object* v_h_41_, lean_object* v_one_42_){
_start:
{
lean_inc(v_one_42_);
return v_one_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim___boxed(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_one_46_){
_start:
{
uint8_t v_t_boxed_47_; lean_object* v_res_48_; 
v_t_boxed_47_ = lean_unbox(v_t_44_);
v_res_48_ = l_Lean_Elab_Tactic_Do_Uses_one_elim(v_motive_43_, v_t_boxed_47_, v_h_45_, v_one_46_);
lean_dec(v_one_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim___redArg(lean_object* v_many_49_){
_start:
{
lean_inc(v_many_49_);
return v_many_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim___redArg___boxed(lean_object* v_many_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_Elab_Tactic_Do_Uses_many_elim___redArg(v_many_50_);
lean_dec(v_many_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim(lean_object* v_motive_52_, uint8_t v_t_53_, lean_object* v_h_54_, lean_object* v_many_55_){
_start:
{
lean_inc(v_many_55_);
return v_many_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim___boxed(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_many_59_){
_start:
{
uint8_t v_t_boxed_60_; lean_object* v_res_61_; 
v_t_boxed_60_ = lean_unbox(v_t_57_);
v_res_61_ = l_Lean_Elab_Tactic_Do_Uses_many_elim(v_motive_56_, v_t_boxed_60_, v_h_58_, v_many_59_);
lean_dec(v_many_59_);
return v_res_61_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_instBEqUses_beq(uint8_t v_x_62_, uint8_t v_y_63_){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; uint8_t v___x_66_; 
v___x_64_ = l_Lean_Elab_Tactic_Do_Uses_ctorIdx(v_x_62_);
v___x_65_ = l_Lean_Elab_Tactic_Do_Uses_ctorIdx(v_y_63_);
v___x_66_ = lean_nat_dec_eq(v___x_64_, v___x_65_);
lean_dec(v___x_65_);
lean_dec(v___x_64_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instBEqUses_beq___boxed(lean_object* v_x_67_, lean_object* v_y_68_){
_start:
{
uint8_t v_x_17__boxed_69_; uint8_t v_y_18__boxed_70_; uint8_t v_res_71_; lean_object* v_r_72_; 
v_x_17__boxed_69_ = lean_unbox(v_x_67_);
v_y_18__boxed_70_ = lean_unbox(v_y_68_);
v_res_71_ = l_Lean_Elab_Tactic_Do_instBEqUses_beq(v_x_17__boxed_69_, v_y_18__boxed_70_);
v_r_72_ = lean_box(v_res_71_);
return v_r_72_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_instOrdUses_ord(uint8_t v_x_75_, uint8_t v_y_76_){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_77_ = l_Lean_Elab_Tactic_Do_Uses_ctorIdx(v_x_75_);
v___x_78_ = l_Lean_Elab_Tactic_Do_Uses_ctorIdx(v_y_76_);
v___x_79_ = lean_nat_dec_lt(v___x_77_, v___x_78_);
if (v___x_79_ == 0)
{
uint8_t v___x_80_; 
v___x_80_ = lean_nat_dec_eq(v___x_77_, v___x_78_);
lean_dec(v___x_78_);
lean_dec(v___x_77_);
if (v___x_80_ == 0)
{
uint8_t v___x_81_; 
v___x_81_ = 2;
return v___x_81_;
}
else
{
uint8_t v___x_82_; 
v___x_82_ = 1;
return v___x_82_;
}
}
else
{
uint8_t v___x_83_; 
lean_dec(v___x_78_);
lean_dec(v___x_77_);
v___x_83_ = 0;
return v___x_83_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instOrdUses_ord___boxed(lean_object* v_x_84_, lean_object* v_y_85_){
_start:
{
uint8_t v_x_30__boxed_86_; uint8_t v_y_31__boxed_87_; uint8_t v_res_88_; lean_object* v_r_89_; 
v_x_30__boxed_86_ = lean_unbox(v_x_84_);
v_y_31__boxed_87_ = lean_unbox(v_y_85_);
v_res_88_ = l_Lean_Elab_Tactic_Do_instOrdUses_ord(v_x_30__boxed_86_, v_y_31__boxed_87_);
v_r_89_ = lean_box(v_res_88_);
return v_r_89_;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_Do_instInhabitedUses_default(void){
_start:
{
uint8_t v___x_92_; 
v___x_92_ = 0;
return v___x_92_;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_Do_instInhabitedUses(void){
_start:
{
uint8_t v___x_93_; 
v___x_93_ = 0;
return v___x_93_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_Uses_add(uint8_t v_x_94_, uint8_t v_x_95_){
_start:
{
if (v_x_94_ == 0)
{
return v_x_95_;
}
else
{
if (v_x_95_ == 0)
{
return v_x_94_;
}
else
{
uint8_t v___x_96_; 
v___x_96_ = 2;
return v___x_96_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_add___boxed(lean_object* v_x_97_, lean_object* v_x_98_){
_start:
{
uint8_t v_x_30__boxed_99_; uint8_t v_x_31__boxed_100_; uint8_t v_res_101_; lean_object* v_r_102_; 
v_x_30__boxed_99_ = lean_unbox(v_x_97_);
v_x_31__boxed_100_ = lean_unbox(v_x_98_);
v_res_101_ = l_Lean_Elab_Tactic_Do_Uses_add(v_x_30__boxed_99_, v_x_31__boxed_100_);
v_r_102_ = lean_box(v_res_101_);
return v_r_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_toNat(uint8_t v_x_103_){
_start:
{
switch(v_x_103_)
{
case 0:
{
lean_object* v___x_104_; 
v___x_104_ = lean_unsigned_to_nat(0u);
return v___x_104_;
}
case 1:
{
lean_object* v___x_105_; 
v___x_105_ = lean_unsigned_to_nat(1u);
return v___x_105_;
}
default: 
{
lean_object* v___x_106_; 
v___x_106_ = lean_unsigned_to_nat(2u);
return v___x_106_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_toNat___boxed(lean_object* v_x_107_){
_start:
{
uint8_t v_x_34__boxed_108_; lean_object* v_res_109_; 
v_x_34__boxed_108_ = lean_unbox(v_x_107_);
v_res_109_ = l_Lean_Elab_Tactic_Do_Uses_toNat(v_x_34__boxed_108_);
return v_res_109_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_Uses_fromNat(lean_object* v_x_110_){
_start:
{
lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_111_ = lean_unsigned_to_nat(0u);
v___x_112_ = lean_nat_dec_eq(v_x_110_, v___x_111_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_113_ = lean_unsigned_to_nat(1u);
v___x_114_ = lean_nat_dec_eq(v_x_110_, v___x_113_);
if (v___x_114_ == 0)
{
uint8_t v___x_115_; 
v___x_115_ = 2;
return v___x_115_;
}
else
{
uint8_t v___x_116_; 
v___x_116_ = 1;
return v___x_116_;
}
}
else
{
uint8_t v___x_117_; 
v___x_117_ = 0;
return v___x_117_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_fromNat___boxed(lean_object* v_x_118_){
_start:
{
uint8_t v_res_119_; lean_object* v_r_120_; 
v_res_119_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v_x_118_);
lean_dec(v_x_118_);
v_r_120_ = lean_box(v_res_119_);
return v_r_120_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_x_123_, lean_object* v_x_124_){
_start:
{
if (lean_obj_tag(v_x_124_) == 0)
{
return v_x_123_;
}
else
{
lean_object* v_key_125_; lean_object* v_value_126_; lean_object* v_tail_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_150_; 
v_key_125_ = lean_ctor_get(v_x_124_, 0);
v_value_126_ = lean_ctor_get(v_x_124_, 1);
v_tail_127_ = lean_ctor_get(v_x_124_, 2);
v_isSharedCheck_150_ = !lean_is_exclusive(v_x_124_);
if (v_isSharedCheck_150_ == 0)
{
v___x_129_ = v_x_124_;
v_isShared_130_ = v_isSharedCheck_150_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_tail_127_);
lean_inc(v_value_126_);
lean_inc(v_key_125_);
lean_dec(v_x_124_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_150_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_131_; uint64_t v___x_132_; uint64_t v___x_133_; uint64_t v___x_134_; uint64_t v_fold_135_; uint64_t v___x_136_; uint64_t v___x_137_; uint64_t v___x_138_; size_t v___x_139_; size_t v___x_140_; size_t v___x_141_; size_t v___x_142_; size_t v___x_143_; lean_object* v___x_144_; lean_object* v___x_146_; 
v___x_131_ = lean_array_get_size(v_x_123_);
v___x_132_ = l_Lean_instHashableFVarId_hash(v_key_125_);
v___x_133_ = 32ULL;
v___x_134_ = lean_uint64_shift_right(v___x_132_, v___x_133_);
v_fold_135_ = lean_uint64_xor(v___x_132_, v___x_134_);
v___x_136_ = 16ULL;
v___x_137_ = lean_uint64_shift_right(v_fold_135_, v___x_136_);
v___x_138_ = lean_uint64_xor(v_fold_135_, v___x_137_);
v___x_139_ = lean_uint64_to_usize(v___x_138_);
v___x_140_ = lean_usize_of_nat(v___x_131_);
v___x_141_ = ((size_t)1ULL);
v___x_142_ = lean_usize_sub(v___x_140_, v___x_141_);
v___x_143_ = lean_usize_land(v___x_139_, v___x_142_);
v___x_144_ = lean_array_uget_borrowed(v_x_123_, v___x_143_);
lean_inc(v___x_144_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 2, v___x_144_);
v___x_146_ = v___x_129_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_key_125_);
lean_ctor_set(v_reuseFailAlloc_149_, 1, v_value_126_);
lean_ctor_set(v_reuseFailAlloc_149_, 2, v___x_144_);
v___x_146_ = v_reuseFailAlloc_149_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
lean_object* v___x_147_; 
v___x_147_ = lean_array_uset(v_x_123_, v___x_143_, v___x_146_);
v_x_123_ = v___x_147_;
v_x_124_ = v_tail_127_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2___redArg(lean_object* v_i_151_, lean_object* v_source_152_, lean_object* v_target_153_){
_start:
{
lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_154_ = lean_array_get_size(v_source_152_);
v___x_155_ = lean_nat_dec_lt(v_i_151_, v___x_154_);
if (v___x_155_ == 0)
{
lean_dec_ref(v_source_152_);
lean_dec(v_i_151_);
return v_target_153_;
}
else
{
lean_object* v_es_156_; lean_object* v___x_157_; lean_object* v_source_158_; lean_object* v_target_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v_es_156_ = lean_array_fget(v_source_152_, v_i_151_);
v___x_157_ = lean_box(0);
v_source_158_ = lean_array_fset(v_source_152_, v_i_151_, v___x_157_);
v_target_159_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5___redArg(v_target_153_, v_es_156_);
v___x_160_ = lean_unsigned_to_nat(1u);
v___x_161_ = lean_nat_add(v_i_151_, v___x_160_);
lean_dec(v_i_151_);
v_i_151_ = v___x_161_;
v_source_152_ = v_source_158_;
v_target_153_ = v_target_159_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1___redArg(lean_object* v_data_163_){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v_nbuckets_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_164_ = lean_array_get_size(v_data_163_);
v___x_165_ = lean_unsigned_to_nat(2u);
v_nbuckets_166_ = lean_nat_mul(v___x_164_, v___x_165_);
v___x_167_ = lean_unsigned_to_nat(0u);
v___x_168_ = lean_box(0);
v___x_169_ = lean_mk_array(v_nbuckets_166_, v___x_168_);
v___x_170_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2___redArg(v___x_167_, v_data_163_, v___x_169_);
return v___x_170_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(lean_object* v_a_171_, lean_object* v_x_172_){
_start:
{
if (lean_obj_tag(v_x_172_) == 0)
{
uint8_t v___x_173_; 
v___x_173_ = 0;
return v___x_173_;
}
else
{
lean_object* v_key_174_; lean_object* v_tail_175_; uint8_t v___x_176_; 
v_key_174_ = lean_ctor_get(v_x_172_, 0);
v_tail_175_ = lean_ctor_get(v_x_172_, 2);
v___x_176_ = l_Lean_instBEqFVarId_beq(v_key_174_, v_a_171_);
if (v___x_176_ == 0)
{
v_x_172_ = v_tail_175_;
goto _start;
}
else
{
return v___x_176_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg___boxed(lean_object* v_a_178_, lean_object* v_x_179_){
_start:
{
uint8_t v_res_180_; lean_object* v_r_181_; 
v_res_180_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_178_, v_x_179_);
lean_dec(v_x_179_);
lean_dec(v_a_178_);
v_r_181_ = lean_box(v_res_180_);
return v_r_181_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0(uint8_t v_x3_182_, lean_object* v_x_183_){
_start:
{
if (lean_obj_tag(v_x_183_) == 0)
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = lean_box(v_x3_182_);
v___x_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
return v___x_185_;
}
else
{
lean_object* v_val_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_196_; 
v_val_186_ = lean_ctor_get(v_x_183_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v_x_183_);
if (v_isSharedCheck_196_ == 0)
{
v___x_188_ = v_x_183_;
v_isShared_189_ = v_isSharedCheck_196_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_val_186_);
lean_dec(v_x_183_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_196_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
uint8_t v___x_190_; uint8_t v___x_191_; lean_object* v___x_192_; lean_object* v___x_194_; 
v___x_190_ = lean_unbox(v_val_186_);
lean_dec(v_val_186_);
v___x_191_ = l_Lean_Elab_Tactic_Do_Uses_add(v_x3_182_, v___x_190_);
v___x_192_ = lean_box(v___x_191_);
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 0, v___x_192_);
v___x_194_ = v___x_188_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_192_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0___boxed(lean_object* v_x3_197_, lean_object* v_x_198_){
_start:
{
uint8_t v_x3_854__boxed_199_; lean_object* v_res_200_; 
v_x3_854__boxed_199_ = lean_unbox(v_x3_197_);
v_res_200_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0(v_x3_854__boxed_199_, v_x_198_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2(uint8_t v_x3_201_, lean_object* v_a_202_, lean_object* v_x_203_){
_start:
{
if (lean_obj_tag(v_x_203_) == 0)
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v_val_206_; lean_object* v___x_207_; 
v___x_204_ = lean_box(0);
v___x_205_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0(v_x3_201_, v___x_204_);
v_val_206_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_val_206_);
lean_dec(v___x_205_);
v___x_207_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_207_, 0, v_a_202_);
lean_ctor_set(v___x_207_, 1, v_val_206_);
lean_ctor_set(v___x_207_, 2, v_x_203_);
return v___x_207_;
}
else
{
lean_object* v_key_208_; lean_object* v_value_209_; lean_object* v_tail_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_225_; 
v_key_208_ = lean_ctor_get(v_x_203_, 0);
v_value_209_ = lean_ctor_get(v_x_203_, 1);
v_tail_210_ = lean_ctor_get(v_x_203_, 2);
v_isSharedCheck_225_ = !lean_is_exclusive(v_x_203_);
if (v_isSharedCheck_225_ == 0)
{
v___x_212_ = v_x_203_;
v_isShared_213_ = v_isSharedCheck_225_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_tail_210_);
lean_inc(v_value_209_);
lean_inc(v_key_208_);
lean_dec(v_x_203_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_225_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
uint8_t v___x_214_; 
v___x_214_ = l_Lean_instBEqFVarId_beq(v_key_208_, v_a_202_);
if (v___x_214_ == 0)
{
lean_object* v_tail_215_; lean_object* v___x_217_; 
v_tail_215_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2(v_x3_201_, v_a_202_, v_tail_210_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 2, v_tail_215_);
v___x_217_ = v___x_212_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_key_208_);
lean_ctor_set(v_reuseFailAlloc_218_, 1, v_value_209_);
lean_ctor_set(v_reuseFailAlloc_218_, 2, v_tail_215_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
else
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v_val_221_; lean_object* v___x_223_; 
lean_dec(v_key_208_);
v___x_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_219_, 0, v_value_209_);
v___x_220_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0(v_x3_201_, v___x_219_);
v_val_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_val_221_);
lean_dec(v___x_220_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 1, v_val_221_);
lean_ctor_set(v___x_212_, 0, v_a_202_);
v___x_223_ = v___x_212_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_a_202_);
lean_ctor_set(v_reuseFailAlloc_224_, 1, v_val_221_);
lean_ctor_set(v_reuseFailAlloc_224_, 2, v_tail_210_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___boxed(lean_object* v_x3_226_, lean_object* v_a_227_, lean_object* v_x_228_){
_start:
{
uint8_t v_x3_886__boxed_229_; lean_object* v_res_230_; 
v_x3_886__boxed_229_ = lean_unbox(v_x3_226_);
v_res_230_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2(v_x3_886__boxed_229_, v_a_227_, v_x_228_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0(uint8_t v_x3_231_, lean_object* v_m_232_, lean_object* v_a_233_){
_start:
{
lean_object* v_size_234_; lean_object* v_buckets_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_284_; 
v_size_234_ = lean_ctor_get(v_m_232_, 0);
v_buckets_235_ = lean_ctor_get(v_m_232_, 1);
v_isSharedCheck_284_ = !lean_is_exclusive(v_m_232_);
if (v_isSharedCheck_284_ == 0)
{
v___x_237_ = v_m_232_;
v_isShared_238_ = v_isSharedCheck_284_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_buckets_235_);
lean_inc(v_size_234_);
lean_dec(v_m_232_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_284_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_239_; uint64_t v___x_240_; uint64_t v___x_241_; uint64_t v___x_242_; uint64_t v_fold_243_; uint64_t v___x_244_; uint64_t v___x_245_; uint64_t v___x_246_; size_t v___x_247_; size_t v___x_248_; size_t v___x_249_; size_t v___x_250_; size_t v___x_251_; lean_object* v_bkt_252_; uint8_t v___x_253_; 
v___x_239_ = lean_array_get_size(v_buckets_235_);
v___x_240_ = l_Lean_instHashableFVarId_hash(v_a_233_);
v___x_241_ = 32ULL;
v___x_242_ = lean_uint64_shift_right(v___x_240_, v___x_241_);
v_fold_243_ = lean_uint64_xor(v___x_240_, v___x_242_);
v___x_244_ = 16ULL;
v___x_245_ = lean_uint64_shift_right(v_fold_243_, v___x_244_);
v___x_246_ = lean_uint64_xor(v_fold_243_, v___x_245_);
v___x_247_ = lean_uint64_to_usize(v___x_246_);
v___x_248_ = lean_usize_of_nat(v___x_239_);
v___x_249_ = ((size_t)1ULL);
v___x_250_ = lean_usize_sub(v___x_248_, v___x_249_);
v___x_251_ = lean_usize_land(v___x_247_, v___x_250_);
v_bkt_252_ = lean_array_uget_borrowed(v_buckets_235_, v___x_251_);
v___x_253_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_233_, v_bkt_252_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; lean_object* v_size_x27_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v_buckets_x27_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v___x_254_ = lean_unsigned_to_nat(1u);
v_size_x27_255_ = lean_nat_add(v_size_234_, v___x_254_);
lean_dec(v_size_234_);
v___x_256_ = lean_box(v_x3_231_);
lean_inc(v_bkt_252_);
v___x_257_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_257_, 0, v_a_233_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
lean_ctor_set(v___x_257_, 2, v_bkt_252_);
v_buckets_x27_258_ = lean_array_uset(v_buckets_235_, v___x_251_, v___x_257_);
v___x_259_ = lean_unsigned_to_nat(4u);
v___x_260_ = lean_nat_mul(v_size_x27_255_, v___x_259_);
v___x_261_ = lean_unsigned_to_nat(3u);
v___x_262_ = lean_nat_div(v___x_260_, v___x_261_);
lean_dec(v___x_260_);
v___x_263_ = lean_array_get_size(v_buckets_x27_258_);
v___x_264_ = lean_nat_dec_le(v___x_262_, v___x_263_);
lean_dec(v___x_262_);
if (v___x_264_ == 0)
{
lean_object* v_val_265_; lean_object* v___x_267_; 
v_val_265_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1___redArg(v_buckets_x27_258_);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 1, v_val_265_);
lean_ctor_set(v___x_237_, 0, v_size_x27_255_);
v___x_267_ = v___x_237_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_size_x27_255_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v_val_265_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
else
{
lean_object* v___x_270_; 
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 1, v_buckets_x27_258_);
lean_ctor_set(v___x_237_, 0, v_size_x27_255_);
v___x_270_ = v___x_237_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_size_x27_255_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v_buckets_x27_258_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
else
{
lean_object* v___x_272_; lean_object* v_buckets_x27_273_; lean_object* v_bkt_x27_274_; lean_object* v___y_276_; uint8_t v___x_281_; 
lean_inc(v_bkt_252_);
v___x_272_ = lean_box(0);
v_buckets_x27_273_ = lean_array_uset(v_buckets_235_, v___x_251_, v___x_272_);
lean_inc(v_a_233_);
v_bkt_x27_274_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2(v_x3_231_, v_a_233_, v_bkt_252_);
v___x_281_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_233_, v_bkt_x27_274_);
lean_dec(v_a_233_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = lean_unsigned_to_nat(1u);
v___x_283_ = lean_nat_sub(v_size_234_, v___x_282_);
lean_dec(v_size_234_);
v___y_276_ = v___x_283_;
goto v___jp_275_;
}
else
{
v___y_276_ = v_size_234_;
goto v___jp_275_;
}
v___jp_275_:
{
lean_object* v___x_277_; lean_object* v___x_279_; 
v___x_277_ = lean_array_uset(v_buckets_x27_273_, v___x_251_, v_bkt_x27_274_);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 1, v___x_277_);
lean_ctor_set(v___x_237_, 0, v___y_276_);
v___x_279_ = v___x_237_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___y_276_);
lean_ctor_set(v_reuseFailAlloc_280_, 1, v___x_277_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0___boxed(lean_object* v_x3_285_, lean_object* v_m_286_, lean_object* v_a_287_){
_start:
{
uint8_t v_x3_934__boxed_288_; lean_object* v_res_289_; 
v_x3_934__boxed_288_ = lean_unbox(v_x3_285_);
v_res_289_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0(v_x3_934__boxed_288_, v_m_286_, v_a_287_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1(lean_object* v_x_290_, lean_object* v_x_291_){
_start:
{
if (lean_obj_tag(v_x_291_) == 0)
{
return v_x_290_;
}
else
{
lean_object* v_key_292_; lean_object* v_value_293_; lean_object* v_tail_294_; uint8_t v___x_295_; lean_object* v___x_296_; 
v_key_292_ = lean_ctor_get(v_x_291_, 0);
lean_inc(v_key_292_);
v_value_293_ = lean_ctor_get(v_x_291_, 1);
lean_inc(v_value_293_);
v_tail_294_ = lean_ctor_get(v_x_291_, 2);
lean_inc(v_tail_294_);
lean_dec_ref_known(v_x_291_, 3);
v___x_295_ = lean_unbox(v_value_293_);
lean_dec(v_value_293_);
v___x_296_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0(v___x_295_, v_x_290_, v_key_292_);
v_x_290_ = v___x_296_;
v_x_291_ = v_tail_294_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(lean_object* v_as_298_, size_t v_i_299_, size_t v_stop_300_, lean_object* v_b_301_){
_start:
{
uint8_t v___x_302_; 
v___x_302_ = lean_usize_dec_eq(v_i_299_, v_stop_300_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; lean_object* v___x_304_; size_t v___x_305_; size_t v___x_306_; 
v___x_303_ = lean_array_uget_borrowed(v_as_298_, v_i_299_);
lean_inc(v___x_303_);
v___x_304_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1(v_b_301_, v___x_303_);
v___x_305_ = ((size_t)1ULL);
v___x_306_ = lean_usize_add(v_i_299_, v___x_305_);
v_i_299_ = v___x_306_;
v_b_301_ = v___x_304_;
goto _start;
}
else
{
return v_b_301_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2___boxed(lean_object* v_as_308_, lean_object* v_i_309_, lean_object* v_stop_310_, lean_object* v_b_311_){
_start:
{
size_t v_i_boxed_312_; size_t v_stop_boxed_313_; lean_object* v_res_314_; 
v_i_boxed_312_ = lean_unbox_usize(v_i_309_);
lean_dec(v_i_309_);
v_stop_boxed_313_ = lean_unbox_usize(v_stop_310_);
lean_dec(v_stop_310_);
v_res_314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(v_as_308_, v_i_boxed_312_, v_stop_boxed_313_, v_b_311_);
lean_dec_ref(v_as_308_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_FVarUses_add(lean_object* v_a_315_, lean_object* v_b_316_){
_start:
{
lean_object* v_buckets_317_; lean_object* v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; 
v_buckets_317_ = lean_ctor_get(v_a_315_, 1);
v___x_318_ = lean_unsigned_to_nat(0u);
v___x_319_ = lean_array_get_size(v_buckets_317_);
v___x_320_ = lean_nat_dec_lt(v___x_318_, v___x_319_);
if (v___x_320_ == 0)
{
return v_b_316_;
}
else
{
uint8_t v___x_321_; 
v___x_321_ = lean_nat_dec_le(v___x_319_, v___x_319_);
if (v___x_321_ == 0)
{
if (v___x_320_ == 0)
{
return v_b_316_;
}
else
{
size_t v___x_322_; size_t v___x_323_; lean_object* v___x_324_; 
v___x_322_ = ((size_t)0ULL);
v___x_323_ = lean_usize_of_nat(v___x_319_);
v___x_324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(v_buckets_317_, v___x_322_, v___x_323_, v_b_316_);
return v___x_324_;
}
}
else
{
size_t v___x_325_; size_t v___x_326_; lean_object* v___x_327_; 
v___x_325_ = ((size_t)0ULL);
v___x_326_ = lean_usize_of_nat(v___x_319_);
v___x_327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(v_buckets_317_, v___x_325_, v___x_326_, v_b_316_);
return v___x_327_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_FVarUses_add___boxed(lean_object* v_a_328_, lean_object* v_b_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_a_328_, v_b_329_);
lean_dec_ref(v_a_328_);
return v_res_330_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0(lean_object* v_00_u03b2_331_, lean_object* v_a_332_, lean_object* v_x_333_){
_start:
{
uint8_t v___x_334_; 
v___x_334_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_332_, v_x_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___boxed(lean_object* v_00_u03b2_335_, lean_object* v_a_336_, lean_object* v_x_337_){
_start:
{
uint8_t v_res_338_; lean_object* v_r_339_; 
v_res_338_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0(v_00_u03b2_335_, v_a_336_, v_x_337_);
lean_dec(v_x_337_);
lean_dec(v_a_336_);
v_r_339_ = lean_box(v_res_338_);
return v_r_339_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1(lean_object* v_00_u03b2_340_, lean_object* v_data_341_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1___redArg(v_data_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_343_, lean_object* v_i_344_, lean_object* v_source_345_, lean_object* v_target_346_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2___redArg(v_i_344_, v_source_345_, v_target_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_348_, lean_object* v_x_349_, lean_object* v_x_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5___redArg(v_x_349_, v_x_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___redArg(lean_object* v_x_354_){
_start:
{
if (lean_obj_tag(v_x_354_) == 0)
{
lean_object* v___x_355_; 
v___x_355_ = lean_unsigned_to_nat(0u);
return v___x_355_;
}
else
{
lean_object* v___x_356_; 
v___x_356_ = lean_unsigned_to_nat(1u);
return v___x_356_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___redArg___boxed(lean_object* v_x_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___redArg(v_x_357_);
lean_dec(v_x_357_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx(lean_object* v_n_359_, lean_object* v_x_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___redArg(v_x_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___boxed(lean_object* v_n_362_, lean_object* v_x_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx(v_n_362_, v_x_363_);
lean_dec(v_x_363_);
lean_dec(v_n_362_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(lean_object* v_t_365_, lean_object* v_k_366_){
_start:
{
if (lean_obj_tag(v_t_365_) == 0)
{
return v_k_366_;
}
else
{
lean_object* v_uses_367_; lean_object* v___x_368_; 
v_uses_367_ = lean_ctor_get(v_t_365_, 0);
lean_inc_ref(v_uses_367_);
lean_dec_ref_known(v_t_365_, 1);
v___x_368_ = lean_apply_1(v_k_366_, v_uses_367_);
return v___x_368_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorElim(lean_object* v_n_369_, lean_object* v_motive_370_, lean_object* v_ctorIdx_371_, lean_object* v_t_372_, lean_object* v_h_373_, lean_object* v_k_374_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_372_, v_k_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___boxed(lean_object* v_n_376_, lean_object* v_motive_377_, lean_object* v_ctorIdx_378_, lean_object* v_t_379_, lean_object* v_h_380_, lean_object* v_k_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim(v_n_376_, v_motive_377_, v_ctorIdx_378_, v_t_379_, v_h_380_, v_k_381_);
lean_dec(v_ctorIdx_378_);
lean_dec(v_n_376_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_none_elim___redArg(lean_object* v_t_383_, lean_object* v_none_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_383_, v_none_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_none_elim(lean_object* v_n_386_, lean_object* v_motive_387_, lean_object* v_t_388_, lean_object* v_h_389_, lean_object* v_none_390_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_388_, v_none_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_none_elim___boxed(lean_object* v_n_392_, lean_object* v_motive_393_, lean_object* v_t_394_, lean_object* v_h_395_, lean_object* v_none_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_Elab_Tactic_Do_BVarUses_none_elim(v_n_392_, v_motive_393_, v_t_394_, v_h_395_, v_none_396_);
lean_dec(v_n_392_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_some_elim___redArg(lean_object* v_t_398_, lean_object* v_some_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_398_, v_some_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_some_elim(lean_object* v_n_401_, lean_object* v_motive_402_, lean_object* v_t_403_, lean_object* v_h_404_, lean_object* v_some_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_403_, v_some_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_some_elim___boxed(lean_object* v_n_407_, lean_object* v_motive_408_, lean_object* v_t_409_, lean_object* v_h_410_, lean_object* v_some_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_Elab_Tactic_Do_BVarUses_some_elim(v_n_407_, v_motive_408_, v_t_409_, v_h_410_, v_some_411_);
lean_dec(v_n_407_);
return v_res_412_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__12));
v___x_438_ = l_Lean_mkAtom(v___x_437_);
return v___x_438_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14(void){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_439_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13);
v___x_440_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5));
v___x_441_ = lean_array_push(v___x_440_, v___x_439_);
return v___x_441_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_442_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14);
v___x_443_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__11));
v___x_444_ = lean_box(2);
v___x_445_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
lean_ctor_set(v___x_445_, 1, v___x_443_);
lean_ctor_set(v___x_445_, 2, v___x_442_);
return v___x_445_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16(void){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_446_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15);
v___x_447_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5));
v___x_448_ = lean_array_push(v___x_447_, v___x_446_);
return v___x_448_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17(void){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_449_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16);
v___x_450_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__9));
v___x_451_ = lean_box(2);
v___x_452_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
lean_ctor_set(v___x_452_, 1, v___x_450_);
lean_ctor_set(v___x_452_, 2, v___x_449_);
return v___x_452_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_453_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17);
v___x_454_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5));
v___x_455_ = lean_array_push(v___x_454_, v___x_453_);
return v___x_455_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_456_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18);
v___x_457_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7));
v___x_458_ = lean_box(2);
v___x_459_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
lean_ctor_set(v___x_459_, 1, v___x_457_);
lean_ctor_set(v___x_459_, 2, v___x_456_);
return v___x_459_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_460_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19);
v___x_461_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5));
v___x_462_ = lean_array_push(v___x_461_, v___x_460_);
return v___x_462_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21(void){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_463_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20);
v___x_464_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4));
v___x_465_ = lean_box(2);
v___x_466_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
lean_ctor_set(v___x_466_, 1, v___x_464_);
lean_ctor_set(v___x_466_, 2, v___x_463_);
return v___x_466_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1(void){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21);
return v___x_467_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0(lean_object* v_numBVars_468_, lean_object* v_n_469_, lean_object* v_i_470_){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; uint8_t v___x_474_; 
v___x_471_ = lean_unsigned_to_nat(1u);
v___x_472_ = lean_nat_sub(v_numBVars_468_, v___x_471_);
v___x_473_ = lean_nat_sub(v___x_472_, v_n_469_);
lean_dec(v___x_472_);
v___x_474_ = lean_nat_dec_eq(v_i_470_, v___x_473_);
lean_dec(v___x_473_);
if (v___x_474_ == 0)
{
uint8_t v___x_475_; 
v___x_475_ = 0;
return v___x_475_;
}
else
{
uint8_t v___x_476_; 
v___x_476_ = 1;
return v___x_476_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0___boxed(lean_object* v_numBVars_477_, lean_object* v_n_478_, lean_object* v_i_479_){
_start:
{
uint8_t v_res_480_; lean_object* v_r_481_; 
v_res_480_ = l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0(v_numBVars_477_, v_n_478_, v_i_479_);
lean_dec(v_i_479_);
lean_dec(v_n_478_);
lean_dec(v_numBVars_477_);
v_r_481_ = lean_box(v_res_480_);
return v_r_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___redArg(lean_object* v_numBVars_482_, lean_object* v_n_483_){
_start:
{
lean_object* v___f_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
lean_inc(v_numBVars_482_);
v___f_484_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_484_, 0, v_numBVars_482_);
lean_closure_set(v___f_484_, 1, v_n_483_);
v___x_485_ = l_Array_ofFn___redArg(v_numBVars_482_, v___f_484_);
v___x_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single(lean_object* v_numBVars_487_, lean_object* v_n_488_, lean_object* v_x_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Lean_Elab_Tactic_Do_BVarUses_single___redArg(v_numBVars_487_, v_n_488_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_pop(lean_object* v_numBVars_495_, lean_object* v_x_496_){
_start:
{
if (lean_obj_tag(v_x_496_) == 0)
{
lean_object* v___x_497_; 
v___x_497_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_pop___closed__0));
return v___x_497_;
}
else
{
lean_object* v_uses_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_511_; 
v_uses_498_ = lean_ctor_get(v_x_496_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v_x_496_);
if (v_isSharedCheck_511_ == 0)
{
v___x_500_ = v_x_496_;
v_isShared_501_ = v_isSharedCheck_511_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_uses_498_);
lean_dec(v_x_496_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_511_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_508_; 
v___x_502_ = lean_unsigned_to_nat(1u);
v___x_503_ = lean_nat_add(v_numBVars_495_, v___x_502_);
v___x_504_ = lean_nat_sub(v___x_503_, v___x_502_);
lean_dec(v___x_503_);
v___x_505_ = lean_array_fget(v_uses_498_, v___x_504_);
lean_dec(v___x_504_);
v___x_506_ = lean_array_pop(v_uses_498_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 0, v___x_506_);
v___x_508_ = v___x_500_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_506_);
v___x_508_ = v_reuseFailAlloc_510_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
lean_object* v___x_509_; 
v___x_509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_505_);
lean_ctor_set(v___x_509_, 1, v___x_508_);
return v___x_509_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_pop___boxed(lean_object* v_numBVars_512_, lean_object* v_x_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Lean_Elab_Tactic_Do_BVarUses_pop(v_numBVars_512_, v_x_513_);
lean_dec(v_numBVars_512_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0(lean_object* v_as_515_, lean_object* v_bs_516_, lean_object* v_i_517_, lean_object* v_cs_518_){
_start:
{
lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_519_ = lean_array_get_size(v_as_515_);
v___x_520_ = lean_nat_dec_lt(v_i_517_, v___x_519_);
if (v___x_520_ == 0)
{
lean_dec(v_i_517_);
return v_cs_518_;
}
else
{
lean_object* v___x_521_; uint8_t v___x_522_; 
v___x_521_ = lean_array_get_size(v_bs_516_);
v___x_522_ = lean_nat_dec_lt(v_i_517_, v___x_521_);
if (v___x_522_ == 0)
{
lean_dec(v_i_517_);
return v_cs_518_;
}
else
{
lean_object* v_a_523_; lean_object* v_b_524_; uint8_t v___x_525_; uint8_t v___x_526_; uint8_t v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v_a_523_ = lean_array_fget_borrowed(v_as_515_, v_i_517_);
v_b_524_ = lean_array_fget_borrowed(v_bs_516_, v_i_517_);
v___x_525_ = lean_unbox(v_a_523_);
v___x_526_ = lean_unbox(v_b_524_);
v___x_527_ = l_Lean_Elab_Tactic_Do_Uses_add(v___x_525_, v___x_526_);
v___x_528_ = lean_unsigned_to_nat(1u);
v___x_529_ = lean_nat_add(v_i_517_, v___x_528_);
lean_dec(v_i_517_);
v___x_530_ = lean_box(v___x_527_);
v___x_531_ = lean_array_push(v_cs_518_, v___x_530_);
v_i_517_ = v___x_529_;
v_cs_518_ = v___x_531_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0___boxed(lean_object* v_as_533_, lean_object* v_bs_534_, lean_object* v_i_535_, lean_object* v_cs_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0(v_as_533_, v_bs_534_, v_i_535_, v_cs_536_);
lean_dec_ref(v_bs_534_);
lean_dec_ref(v_as_533_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_add___redArg(lean_object* v_a_540_, lean_object* v_b_541_){
_start:
{
if (lean_obj_tag(v_a_540_) == 0)
{
return v_b_541_;
}
else
{
if (lean_obj_tag(v_b_541_) == 0)
{
lean_object* v_uses_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_549_; 
v_uses_542_ = lean_ctor_get(v_a_540_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v_a_540_);
if (v_isSharedCheck_549_ == 0)
{
v___x_544_ = v_a_540_;
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_uses_542_);
lean_dec(v_a_540_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
if (v_isShared_545_ == 0)
{
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_uses_542_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
else
{
lean_object* v_uses_550_; lean_object* v_uses_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_561_; 
v_uses_550_ = lean_ctor_get(v_a_540_, 0);
lean_inc_ref(v_uses_550_);
lean_dec_ref_known(v_a_540_, 1);
v_uses_551_ = lean_ctor_get(v_b_541_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v_b_541_);
if (v_isSharedCheck_561_ == 0)
{
v___x_553_ = v_b_541_;
v_isShared_554_ = v_isSharedCheck_561_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_uses_551_);
lean_dec(v_b_541_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_561_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_559_; 
v___x_555_ = lean_unsigned_to_nat(0u);
v___x_556_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_add___redArg___closed__0));
v___x_557_ = l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0(v_uses_550_, v_uses_551_, v___x_555_, v___x_556_);
lean_dec_ref(v_uses_551_);
lean_dec_ref(v_uses_550_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 0, v___x_557_);
v___x_559_ = v___x_553_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_add(lean_object* v_numBVars_562_, lean_object* v_a_563_, lean_object* v_b_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Lean_Elab_Tactic_Do_BVarUses_add___redArg(v_a_563_, v_b_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_add___boxed(lean_object* v_numBVars_566_, lean_object* v_a_567_, lean_object* v_b_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_Elab_Tactic_Do_BVarUses_add(v_numBVars_566_, v_a_567_, v_b_568_);
lean_dec(v_numBVars_566_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instAddBVarUses(lean_object* v_numBVars_570_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_BVarUses_add___boxed), 3, 1);
lean_closure_set(v___x_571_, 0, v_numBVars_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_over1Of2___redArg(lean_object* v_f_572_, lean_object* v_x_573_){
_start:
{
lean_object* v_fst_574_; lean_object* v_snd_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_583_; 
v_fst_574_ = lean_ctor_get(v_x_573_, 0);
v_snd_575_ = lean_ctor_get(v_x_573_, 1);
v_isSharedCheck_583_ = !lean_is_exclusive(v_x_573_);
if (v_isSharedCheck_583_ == 0)
{
v___x_577_ = v_x_573_;
v_isShared_578_ = v_isSharedCheck_583_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_snd_575_);
lean_inc(v_fst_574_);
lean_dec(v_x_573_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_583_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_579_; lean_object* v___x_581_; 
v___x_579_ = lean_apply_1(v_f_572_, v_fst_574_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 0, v___x_579_);
v___x_581_ = v___x_577_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_579_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v_snd_575_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_over1Of2(lean_object* v_00_u03b1_u2081_584_, lean_object* v_00_u03b1_u2082_585_, lean_object* v_00_u03b2_586_, lean_object* v_f_587_, lean_object* v_x_588_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v_f_587_, v_x_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addMData___lam__0(lean_object* v_x_590_, lean_object* v_new_591_, lean_object* v_x_592_){
_start:
{
lean_inc_ref(v_new_591_);
return v_new_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addMData___lam__0___boxed(lean_object* v_x_593_, lean_object* v_new_594_, lean_object* v_x_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lean_Elab_Tactic_Do_addMData___lam__0(v_x_593_, v_new_594_, v_x_595_);
lean_dec_ref(v_x_595_);
lean_dec_ref(v_new_594_);
lean_dec(v_x_593_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addMData(lean_object* v_d_598_, lean_object* v_e_599_){
_start:
{
if (lean_obj_tag(v_e_599_) == 10)
{
lean_object* v_data_600_; lean_object* v_expr_601_; lean_object* v___f_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v_data_600_ = lean_ctor_get(v_e_599_, 0);
lean_inc(v_data_600_);
v_expr_601_ = lean_ctor_get(v_e_599_, 1);
lean_inc_ref(v_expr_601_);
lean_dec_ref_known(v_e_599_, 2);
v___f_602_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_addMData___closed__0));
v___x_603_ = l_Lean_KVMap_mergeBy(v___f_602_, v_d_598_, v_data_600_);
lean_dec(v_data_600_);
v___x_604_ = l_Lean_Expr_mdata___override(v___x_603_, v_expr_601_);
return v___x_604_;
}
else
{
lean_object* v___x_605_; 
v___x_605_ = l_Lean_Expr_mdata___override(v_d_598_, v_e_599_);
return v___x_605_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup(lean_object* v_e_606_){
_start:
{
uint8_t v___y_608_; 
switch(lean_obj_tag(v_e_606_))
{
case 1:
{
uint8_t v___x_610_; 
v___x_610_ = 0;
return v___x_610_;
}
case 5:
{
uint8_t v___x_611_; 
v___x_611_ = l_Lean_Meta_Simp_isOfNatNatLit(v_e_606_);
if (v___x_611_ == 0)
{
uint8_t v___x_612_; 
v___x_612_ = l_Lean_Meta_Simp_isOfScientificLit(v_e_606_);
v___y_608_ = v___x_612_;
goto v___jp_607_;
}
else
{
v___y_608_ = v___x_611_;
goto v___jp_607_;
}
}
case 6:
{
uint8_t v___x_613_; 
v___x_613_ = 0;
return v___x_613_;
}
case 7:
{
uint8_t v___x_614_; 
v___x_614_ = 0;
return v___x_614_;
}
case 8:
{
uint8_t v___x_615_; 
v___x_615_ = 0;
return v___x_615_;
}
case 10:
{
lean_object* v_expr_616_; 
v_expr_616_ = lean_ctor_get(v_e_606_, 1);
v_e_606_ = v_expr_616_;
goto _start;
}
case 11:
{
lean_object* v_struct_618_; 
v_struct_618_ = lean_ctor_get(v_e_606_, 2);
v_e_606_ = v_struct_618_;
goto _start;
}
default: 
{
uint8_t v___x_620_; 
v___x_620_ = 1;
return v___x_620_;
}
}
v___jp_607_:
{
if (v___y_608_ == 0)
{
uint8_t v___x_609_; 
v___x_609_ = l_Lean_Meta_Simp_isCharLit(v_e_606_);
return v___x_609_;
}
else
{
return v___y_608_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup___boxed(lean_object* v_e_621_){
_start:
{
uint8_t v_res_622_; lean_object* v_r_623_; 
v_res_622_ = l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup(v_e_621_);
lean_dec_ref(v_e_621_);
v_r_623_ = lean_box(v_res_622_);
return v_r_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___lam__0(lean_object* v_val_624_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_625_, 0, v_val_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5(lean_object* v_msgData_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
lean_object* v___x_632_; lean_object* v_env_633_; lean_object* v___x_634_; lean_object* v_mctx_635_; lean_object* v_lctx_636_; lean_object* v_options_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_632_ = lean_st_ref_get(v___y_630_);
v_env_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc_ref(v_env_633_);
lean_dec(v___x_632_);
v___x_634_ = lean_st_ref_get(v___y_628_);
v_mctx_635_ = lean_ctor_get(v___x_634_, 0);
lean_inc_ref(v_mctx_635_);
lean_dec(v___x_634_);
v_lctx_636_ = lean_ctor_get(v___y_627_, 2);
v_options_637_ = lean_ctor_get(v___y_629_, 2);
lean_inc_ref(v_options_637_);
lean_inc_ref(v_lctx_636_);
v___x_638_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_638_, 0, v_env_633_);
lean_ctor_set(v___x_638_, 1, v_mctx_635_);
lean_ctor_set(v___x_638_, 2, v_lctx_636_);
lean_ctor_set(v___x_638_, 3, v_options_637_);
v___x_639_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
lean_ctor_set(v___x_639_, 1, v_msgData_626_);
v___x_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5___boxed(lean_object* v_msgData_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5(v_msgData_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(lean_object* v_msg_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v_ref_654_; lean_object* v___x_655_; lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_664_; 
v_ref_654_ = lean_ctor_get(v___y_651_, 5);
v___x_655_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5(v_msg_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_);
v_a_656_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_664_ == 0)
{
v___x_658_ = v___x_655_;
v_isShared_659_ = v_isSharedCheck_664_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_655_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_664_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_660_; lean_object* v___x_662_; 
lean_inc(v_ref_654_);
v___x_660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_660_, 0, v_ref_654_);
lean_ctor_set(v___x_660_, 1, v_a_656_);
if (v_isShared_659_ == 0)
{
lean_ctor_set_tag(v___x_658_, 1);
lean_ctor_set(v___x_658_, 0, v___x_660_);
v___x_662_ = v___x_658_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_660_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg___boxed(lean_object* v_msg_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v_msg_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses___lam__0(lean_object* v_data_672_, lean_object* v_expr_673_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = l_Lean_Expr_mdata___override(v_data_672_, v_expr_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses___lam__1(lean_object* v_typeName_675_, lean_object* v_idx_676_, lean_object* v_struct_677_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = l_Lean_Expr_proj___override(v_typeName_675_, v_idx_676_, v_struct_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(lean_object* v_a_679_, lean_object* v_b_680_, lean_object* v_x_681_){
_start:
{
if (lean_obj_tag(v_x_681_) == 0)
{
lean_dec(v_b_680_);
lean_dec(v_a_679_);
return v_x_681_;
}
else
{
lean_object* v_key_682_; lean_object* v_value_683_; lean_object* v_tail_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_696_; 
v_key_682_ = lean_ctor_get(v_x_681_, 0);
v_value_683_ = lean_ctor_get(v_x_681_, 1);
v_tail_684_ = lean_ctor_get(v_x_681_, 2);
v_isSharedCheck_696_ = !lean_is_exclusive(v_x_681_);
if (v_isSharedCheck_696_ == 0)
{
v___x_686_ = v_x_681_;
v_isShared_687_ = v_isSharedCheck_696_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_tail_684_);
lean_inc(v_value_683_);
lean_inc(v_key_682_);
lean_dec(v_x_681_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_696_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
uint8_t v___x_688_; 
v___x_688_ = l_Lean_instBEqFVarId_beq(v_key_682_, v_a_679_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_689_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(v_a_679_, v_b_680_, v_tail_684_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 2, v___x_689_);
v___x_691_ = v___x_686_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_key_682_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_value_683_);
lean_ctor_set(v_reuseFailAlloc_692_, 2, v___x_689_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
else
{
lean_object* v___x_694_; 
lean_dec(v_value_683_);
lean_dec(v_key_682_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 1, v_b_680_);
lean_ctor_set(v___x_686_, 0, v_a_679_);
v___x_694_ = v___x_686_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_679_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_b_680_);
lean_ctor_set(v_reuseFailAlloc_695_, 2, v_tail_684_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(lean_object* v_m_697_, lean_object* v_a_698_, lean_object* v_b_699_){
_start:
{
lean_object* v_size_700_; lean_object* v_buckets_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_744_; 
v_size_700_ = lean_ctor_get(v_m_697_, 0);
v_buckets_701_ = lean_ctor_get(v_m_697_, 1);
v_isSharedCheck_744_ = !lean_is_exclusive(v_m_697_);
if (v_isSharedCheck_744_ == 0)
{
v___x_703_ = v_m_697_;
v_isShared_704_ = v_isSharedCheck_744_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_buckets_701_);
lean_inc(v_size_700_);
lean_dec(v_m_697_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_744_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_705_; uint64_t v___x_706_; uint64_t v___x_707_; uint64_t v___x_708_; uint64_t v_fold_709_; uint64_t v___x_710_; uint64_t v___x_711_; uint64_t v___x_712_; size_t v___x_713_; size_t v___x_714_; size_t v___x_715_; size_t v___x_716_; size_t v___x_717_; lean_object* v_bkt_718_; uint8_t v___x_719_; 
v___x_705_ = lean_array_get_size(v_buckets_701_);
v___x_706_ = l_Lean_instHashableFVarId_hash(v_a_698_);
v___x_707_ = 32ULL;
v___x_708_ = lean_uint64_shift_right(v___x_706_, v___x_707_);
v_fold_709_ = lean_uint64_xor(v___x_706_, v___x_708_);
v___x_710_ = 16ULL;
v___x_711_ = lean_uint64_shift_right(v_fold_709_, v___x_710_);
v___x_712_ = lean_uint64_xor(v_fold_709_, v___x_711_);
v___x_713_ = lean_uint64_to_usize(v___x_712_);
v___x_714_ = lean_usize_of_nat(v___x_705_);
v___x_715_ = ((size_t)1ULL);
v___x_716_ = lean_usize_sub(v___x_714_, v___x_715_);
v___x_717_ = lean_usize_land(v___x_713_, v___x_716_);
v_bkt_718_ = lean_array_uget_borrowed(v_buckets_701_, v___x_717_);
v___x_719_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_698_, v_bkt_718_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; lean_object* v_size_x27_721_; lean_object* v___x_722_; lean_object* v_buckets_x27_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_720_ = lean_unsigned_to_nat(1u);
v_size_x27_721_ = lean_nat_add(v_size_700_, v___x_720_);
lean_dec(v_size_700_);
lean_inc(v_bkt_718_);
v___x_722_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_722_, 0, v_a_698_);
lean_ctor_set(v___x_722_, 1, v_b_699_);
lean_ctor_set(v___x_722_, 2, v_bkt_718_);
v_buckets_x27_723_ = lean_array_uset(v_buckets_701_, v___x_717_, v___x_722_);
v___x_724_ = lean_unsigned_to_nat(4u);
v___x_725_ = lean_nat_mul(v_size_x27_721_, v___x_724_);
v___x_726_ = lean_unsigned_to_nat(3u);
v___x_727_ = lean_nat_div(v___x_725_, v___x_726_);
lean_dec(v___x_725_);
v___x_728_ = lean_array_get_size(v_buckets_x27_723_);
v___x_729_ = lean_nat_dec_le(v___x_727_, v___x_728_);
lean_dec(v___x_727_);
if (v___x_729_ == 0)
{
lean_object* v_val_730_; lean_object* v___x_732_; 
v_val_730_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1___redArg(v_buckets_x27_723_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 1, v_val_730_);
lean_ctor_set(v___x_703_, 0, v_size_x27_721_);
v___x_732_ = v___x_703_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_size_x27_721_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v_val_730_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
else
{
lean_object* v___x_735_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 1, v_buckets_x27_723_);
lean_ctor_set(v___x_703_, 0, v_size_x27_721_);
v___x_735_ = v___x_703_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_size_x27_721_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v_buckets_x27_723_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
else
{
lean_object* v___x_737_; lean_object* v_buckets_x27_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_742_; 
lean_inc(v_bkt_718_);
v___x_737_ = lean_box(0);
v_buckets_x27_738_ = lean_array_uset(v_buckets_701_, v___x_717_, v___x_737_);
v___x_739_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(v_a_698_, v_b_699_, v_bkt_718_);
v___x_740_ = lean_array_uset(v_buckets_x27_738_, v___x_717_, v___x_739_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 1, v___x_740_);
v___x_742_ = v___x_703_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_size_700_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v___x_740_);
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
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(lean_object* v___y_745_){
_start:
{
lean_object* v___x_747_; lean_object* v_ngen_748_; lean_object* v_namePrefix_749_; lean_object* v_idx_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_779_; 
v___x_747_ = lean_st_ref_get(v___y_745_);
v_ngen_748_ = lean_ctor_get(v___x_747_, 2);
lean_inc_ref(v_ngen_748_);
lean_dec(v___x_747_);
v_namePrefix_749_ = lean_ctor_get(v_ngen_748_, 0);
v_idx_750_ = lean_ctor_get(v_ngen_748_, 1);
v_isSharedCheck_779_ = !lean_is_exclusive(v_ngen_748_);
if (v_isSharedCheck_779_ == 0)
{
v___x_752_ = v_ngen_748_;
v_isShared_753_ = v_isSharedCheck_779_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_idx_750_);
lean_inc(v_namePrefix_749_);
lean_dec(v_ngen_748_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_779_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_754_; lean_object* v_env_755_; lean_object* v_nextMacroScope_756_; lean_object* v_auxDeclNGen_757_; lean_object* v_traceState_758_; lean_object* v_cache_759_; lean_object* v_messages_760_; lean_object* v_infoState_761_; lean_object* v_snapshotTasks_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_777_; 
v___x_754_ = lean_st_ref_take(v___y_745_);
v_env_755_ = lean_ctor_get(v___x_754_, 0);
v_nextMacroScope_756_ = lean_ctor_get(v___x_754_, 1);
v_auxDeclNGen_757_ = lean_ctor_get(v___x_754_, 3);
v_traceState_758_ = lean_ctor_get(v___x_754_, 4);
v_cache_759_ = lean_ctor_get(v___x_754_, 5);
v_messages_760_ = lean_ctor_get(v___x_754_, 6);
v_infoState_761_ = lean_ctor_get(v___x_754_, 7);
v_snapshotTasks_762_ = lean_ctor_get(v___x_754_, 8);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_777_ == 0)
{
lean_object* v_unused_778_; 
v_unused_778_ = lean_ctor_get(v___x_754_, 2);
lean_dec(v_unused_778_);
v___x_764_ = v___x_754_;
v_isShared_765_ = v_isSharedCheck_777_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_snapshotTasks_762_);
lean_inc(v_infoState_761_);
lean_inc(v_messages_760_);
lean_inc(v_cache_759_);
lean_inc(v_traceState_758_);
lean_inc(v_auxDeclNGen_757_);
lean_inc(v_nextMacroScope_756_);
lean_inc(v_env_755_);
lean_dec(v___x_754_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_777_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v_r_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_770_; 
lean_inc(v_idx_750_);
lean_inc(v_namePrefix_749_);
v_r_766_ = l_Lean_Name_num___override(v_namePrefix_749_, v_idx_750_);
v___x_767_ = lean_unsigned_to_nat(1u);
v___x_768_ = lean_nat_add(v_idx_750_, v___x_767_);
lean_dec(v_idx_750_);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 1, v___x_768_);
v___x_770_ = v___x_752_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_namePrefix_749_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v___x_768_);
v___x_770_ = v_reuseFailAlloc_776_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
lean_object* v___x_772_; 
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 2, v___x_770_);
v___x_772_ = v___x_764_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_env_755_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v_nextMacroScope_756_);
lean_ctor_set(v_reuseFailAlloc_775_, 2, v___x_770_);
lean_ctor_set(v_reuseFailAlloc_775_, 3, v_auxDeclNGen_757_);
lean_ctor_set(v_reuseFailAlloc_775_, 4, v_traceState_758_);
lean_ctor_set(v_reuseFailAlloc_775_, 5, v_cache_759_);
lean_ctor_set(v_reuseFailAlloc_775_, 6, v_messages_760_);
lean_ctor_set(v_reuseFailAlloc_775_, 7, v_infoState_761_);
lean_ctor_set(v_reuseFailAlloc_775_, 8, v_snapshotTasks_762_);
v___x_772_ = v_reuseFailAlloc_775_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = lean_st_ref_set(v___y_745_, v___x_772_);
v___x_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_774_, 0, v_r_766_);
return v___x_774_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg___boxed(lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(v___y_780_);
lean_dec(v___y_780_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v___x_788_; lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_796_; 
v___x_788_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(v___y_786_);
v_a_789_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_796_ == 0)
{
v___x_791_ = v___x_788_;
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_788_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_794_; 
if (v_isShared_792_ == 0)
{
v___x_794_ = v___x_791_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_a_789_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5___boxed(lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(v___y_797_, v___y_798_, v___y_799_, v___y_800_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
lean_dec(v___y_798_);
lean_dec_ref(v___y_797_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(lean_object* v_a_803_, lean_object* v_x_804_){
_start:
{
if (lean_obj_tag(v_x_804_) == 0)
{
return v_x_804_;
}
else
{
lean_object* v_key_805_; lean_object* v_value_806_; lean_object* v_tail_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_816_; 
v_key_805_ = lean_ctor_get(v_x_804_, 0);
v_value_806_ = lean_ctor_get(v_x_804_, 1);
v_tail_807_ = lean_ctor_get(v_x_804_, 2);
v_isSharedCheck_816_ = !lean_is_exclusive(v_x_804_);
if (v_isSharedCheck_816_ == 0)
{
v___x_809_ = v_x_804_;
v_isShared_810_ = v_isSharedCheck_816_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_tail_807_);
lean_inc(v_value_806_);
lean_inc(v_key_805_);
lean_dec(v_x_804_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_816_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
uint8_t v___x_811_; 
v___x_811_ = l_Lean_instBEqFVarId_beq(v_key_805_, v_a_803_);
if (v___x_811_ == 0)
{
lean_object* v___x_812_; lean_object* v___x_814_; 
v___x_812_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_803_, v_tail_807_);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 2, v___x_812_);
v___x_814_ = v___x_809_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_key_805_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v_value_806_);
lean_ctor_set(v_reuseFailAlloc_815_, 2, v___x_812_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
else
{
lean_del_object(v___x_809_);
lean_dec(v_value_806_);
lean_dec(v_key_805_);
return v_tail_807_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg___boxed(lean_object* v_a_817_, lean_object* v_x_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_817_, v_x_818_);
lean_dec(v_a_817_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(lean_object* v_m_820_, lean_object* v_a_821_){
_start:
{
lean_object* v_size_822_; lean_object* v_buckets_823_; lean_object* v___x_824_; uint64_t v___x_825_; uint64_t v___x_826_; uint64_t v___x_827_; uint64_t v_fold_828_; uint64_t v___x_829_; uint64_t v___x_830_; uint64_t v___x_831_; size_t v___x_832_; size_t v___x_833_; size_t v___x_834_; size_t v___x_835_; size_t v___x_836_; lean_object* v_bkt_837_; uint8_t v___x_838_; 
v_size_822_ = lean_ctor_get(v_m_820_, 0);
v_buckets_823_ = lean_ctor_get(v_m_820_, 1);
v___x_824_ = lean_array_get_size(v_buckets_823_);
v___x_825_ = l_Lean_instHashableFVarId_hash(v_a_821_);
v___x_826_ = 32ULL;
v___x_827_ = lean_uint64_shift_right(v___x_825_, v___x_826_);
v_fold_828_ = lean_uint64_xor(v___x_825_, v___x_827_);
v___x_829_ = 16ULL;
v___x_830_ = lean_uint64_shift_right(v_fold_828_, v___x_829_);
v___x_831_ = lean_uint64_xor(v_fold_828_, v___x_830_);
v___x_832_ = lean_uint64_to_usize(v___x_831_);
v___x_833_ = lean_usize_of_nat(v___x_824_);
v___x_834_ = ((size_t)1ULL);
v___x_835_ = lean_usize_sub(v___x_833_, v___x_834_);
v___x_836_ = lean_usize_land(v___x_832_, v___x_835_);
v_bkt_837_ = lean_array_uget_borrowed(v_buckets_823_, v___x_836_);
v___x_838_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_821_, v_bkt_837_);
if (v___x_838_ == 0)
{
return v_m_820_;
}
else
{
lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_851_; 
lean_inc(v_bkt_837_);
lean_inc_ref(v_buckets_823_);
lean_inc(v_size_822_);
v_isSharedCheck_851_ = !lean_is_exclusive(v_m_820_);
if (v_isSharedCheck_851_ == 0)
{
lean_object* v_unused_852_; lean_object* v_unused_853_; 
v_unused_852_ = lean_ctor_get(v_m_820_, 1);
lean_dec(v_unused_852_);
v_unused_853_ = lean_ctor_get(v_m_820_, 0);
lean_dec(v_unused_853_);
v___x_840_ = v_m_820_;
v_isShared_841_ = v_isSharedCheck_851_;
goto v_resetjp_839_;
}
else
{
lean_dec(v_m_820_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_851_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_842_; lean_object* v_buckets_x27_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_849_; 
v___x_842_ = lean_box(0);
v_buckets_x27_843_ = lean_array_uset(v_buckets_823_, v___x_836_, v___x_842_);
v___x_844_ = lean_unsigned_to_nat(1u);
v___x_845_ = lean_nat_sub(v_size_822_, v___x_844_);
lean_dec(v_size_822_);
v___x_846_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_821_, v_bkt_837_);
v___x_847_ = lean_array_uset(v_buckets_x27_843_, v___x_836_, v___x_846_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 1, v___x_847_);
lean_ctor_set(v___x_840_, 0, v___x_845_);
v___x_849_ = v___x_840_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_845_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v___x_847_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg___boxed(lean_object* v_m_854_, lean_object* v_a_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v_m_854_, v_a_855_);
lean_dec(v_a_855_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(lean_object* v_a_857_, lean_object* v_fallback_858_, lean_object* v_x_859_){
_start:
{
if (lean_obj_tag(v_x_859_) == 0)
{
lean_inc(v_fallback_858_);
return v_fallback_858_;
}
else
{
lean_object* v_key_860_; lean_object* v_value_861_; lean_object* v_tail_862_; uint8_t v___x_863_; 
v_key_860_ = lean_ctor_get(v_x_859_, 0);
v_value_861_ = lean_ctor_get(v_x_859_, 1);
v_tail_862_ = lean_ctor_get(v_x_859_, 2);
v___x_863_ = l_Lean_instBEqFVarId_beq(v_key_860_, v_a_857_);
if (v___x_863_ == 0)
{
v_x_859_ = v_tail_862_;
goto _start;
}
else
{
lean_inc(v_value_861_);
return v_value_861_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg___boxed(lean_object* v_a_865_, lean_object* v_fallback_866_, lean_object* v_x_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(v_a_865_, v_fallback_866_, v_x_867_);
lean_dec(v_x_867_);
lean_dec(v_fallback_866_);
lean_dec(v_a_865_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(lean_object* v_m_869_, lean_object* v_a_870_, lean_object* v_fallback_871_){
_start:
{
lean_object* v_buckets_872_; lean_object* v___x_873_; uint64_t v___x_874_; uint64_t v___x_875_; uint64_t v___x_876_; uint64_t v_fold_877_; uint64_t v___x_878_; uint64_t v___x_879_; uint64_t v___x_880_; size_t v___x_881_; size_t v___x_882_; size_t v___x_883_; size_t v___x_884_; size_t v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v_buckets_872_ = lean_ctor_get(v_m_869_, 1);
v___x_873_ = lean_array_get_size(v_buckets_872_);
v___x_874_ = l_Lean_instHashableFVarId_hash(v_a_870_);
v___x_875_ = 32ULL;
v___x_876_ = lean_uint64_shift_right(v___x_874_, v___x_875_);
v_fold_877_ = lean_uint64_xor(v___x_874_, v___x_876_);
v___x_878_ = 16ULL;
v___x_879_ = lean_uint64_shift_right(v_fold_877_, v___x_878_);
v___x_880_ = lean_uint64_xor(v_fold_877_, v___x_879_);
v___x_881_ = lean_uint64_to_usize(v___x_880_);
v___x_882_ = lean_usize_of_nat(v___x_873_);
v___x_883_ = ((size_t)1ULL);
v___x_884_ = lean_usize_sub(v___x_882_, v___x_883_);
v___x_885_ = lean_usize_land(v___x_881_, v___x_884_);
v___x_886_ = lean_array_uget_borrowed(v_buckets_872_, v___x_885_);
v___x_887_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(v_a_870_, v_fallback_871_, v___x_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg___boxed(lean_object* v_m_888_, lean_object* v_a_889_, lean_object* v_fallback_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(v_m_888_, v_a_889_, v_fallback_890_);
lean_dec(v_fallback_890_);
lean_dec(v_a_889_);
lean_dec_ref(v_m_888_);
return v_res_891_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2(void){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_895_ = lean_box(0);
v___x_896_ = lean_unsigned_to_nat(16u);
v___x_897_ = lean_mk_array(v___x_896_, v___x_895_);
return v___x_897_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3(void){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_898_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2);
v___x_899_ = lean_unsigned_to_nat(0u);
v___x_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
lean_ctor_set(v___x_900_, 1, v___x_898_);
return v___x_900_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUses___closed__1(void){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUses___closed__0));
v___x_904_ = l_Lean_stringToMessageData(v___x_903_);
return v___x_904_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUses___closed__3(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_906_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUses___closed__2));
v___x_907_ = l_Lean_stringToMessageData(v___x_906_);
return v___x_907_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUses___closed__5(void){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_909_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUses___closed__4));
v___x_910_ = l_Lean_stringToMessageData(v___x_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses(lean_object* v_e_911_, lean_object* v_subst_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_){
_start:
{
switch(lean_obj_tag(v_e_911_))
{
case 0:
{
lean_object* v_deBruijnIndex_918_; lean_object* v___x_919_; uint8_t v___x_920_; 
v_deBruijnIndex_918_ = lean_ctor_get(v_e_911_, 0);
v___x_919_ = lean_array_get_size(v_subst_912_);
v___x_920_ = lean_nat_dec_lt(v_deBruijnIndex_918_, v___x_919_);
if (v___x_920_ == 0)
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
lean_inc(v_deBruijnIndex_918_);
lean_dec_ref_known(v_e_911_, 1);
lean_dec_ref(v_subst_912_);
v___x_921_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__1, &l_Lean_Elab_Tactic_Do_countUses___closed__1_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__1);
v___x_922_ = l_Nat_reprFast(v_deBruijnIndex_918_);
v___x_923_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
v___x_924_ = l_Lean_MessageData_ofFormat(v___x_923_);
v___x_925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_921_);
lean_ctor_set(v___x_925_, 1, v___x_924_);
v___x_926_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__3, &l_Lean_Elab_Tactic_Do_countUses___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__3);
v___x_927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_925_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
v___x_928_ = l_Nat_reprFast(v___x_919_);
v___x_929_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
v___x_930_ = l_Lean_MessageData_ofFormat(v___x_929_);
v___x_931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_927_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
v___x_932_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v___x_931_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
return v___x_932_;
}
else
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; uint8_t v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_933_ = lean_unsigned_to_nat(1u);
v___x_934_ = lean_nat_sub(v___x_919_, v___x_933_);
v___x_935_ = lean_nat_sub(v___x_934_, v_deBruijnIndex_918_);
lean_dec(v___x_934_);
v___x_936_ = lean_array_fget(v_subst_912_, v___x_935_);
lean_dec(v___x_935_);
lean_dec_ref(v_subst_912_);
v___x_937_ = 1;
v___x_938_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3);
v___x_939_ = lean_box(v___x_937_);
v___x_940_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(v___x_938_, v___x_936_, v___x_939_);
v___x_941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_941_, 0, v_e_911_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
v___x_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
return v___x_942_;
}
}
case 1:
{
lean_object* v_fvarId_943_; uint8_t v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
lean_dec_ref(v_subst_912_);
v_fvarId_943_ = lean_ctor_get(v_e_911_, 0);
v___x_944_ = 1;
v___x_945_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3);
v___x_946_ = lean_box(v___x_944_);
lean_inc(v_fvarId_943_);
v___x_947_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(v___x_945_, v_fvarId_943_, v___x_946_);
v___x_948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_948_, 0, v_e_911_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
return v___x_949_;
}
case 5:
{
lean_object* v_fn_950_; lean_object* v_arg_951_; lean_object* v___x_952_; 
v_fn_950_ = lean_ctor_get(v_e_911_, 0);
lean_inc_ref(v_fn_950_);
v_arg_951_ = lean_ctor_get(v_e_911_, 1);
lean_inc_ref(v_arg_951_);
lean_dec_ref_known(v_e_911_, 2);
lean_inc_ref(v_subst_912_);
v___x_952_ = l_Lean_Elab_Tactic_Do_countUses(v_fn_950_, v_subst_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v_a_953_; lean_object* v_fst_954_; lean_object* v_snd_955_; lean_object* v___x_956_; 
v_a_953_ = lean_ctor_get(v___x_952_, 0);
lean_inc(v_a_953_);
lean_dec_ref_known(v___x_952_, 1);
v_fst_954_ = lean_ctor_get(v_a_953_, 0);
lean_inc(v_fst_954_);
v_snd_955_ = lean_ctor_get(v_a_953_, 1);
lean_inc(v_snd_955_);
lean_dec(v_a_953_);
v___x_956_ = l_Lean_Elab_Tactic_Do_countUses(v_arg_951_, v_subst_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_975_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_975_ == 0)
{
v___x_959_ = v___x_956_;
v_isShared_960_ = v_isSharedCheck_975_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_956_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_975_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v_fst_961_; lean_object* v_snd_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_974_; 
v_fst_961_ = lean_ctor_get(v_a_957_, 0);
v_snd_962_ = lean_ctor_get(v_a_957_, 1);
v_isSharedCheck_974_ = !lean_is_exclusive(v_a_957_);
if (v_isSharedCheck_974_ == 0)
{
v___x_964_ = v_a_957_;
v_isShared_965_ = v_isSharedCheck_974_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_snd_962_);
lean_inc(v_fst_961_);
lean_dec(v_a_957_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_974_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_969_; 
v___x_966_ = l_Lean_Expr_app___override(v_fst_954_, v_fst_961_);
v___x_967_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_snd_955_, v_snd_962_);
lean_dec(v_snd_955_);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 1, v___x_967_);
lean_ctor_set(v___x_964_, 0, v___x_966_);
v___x_969_ = v___x_964_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v___x_966_);
lean_ctor_set(v_reuseFailAlloc_973_, 1, v___x_967_);
v___x_969_ = v_reuseFailAlloc_973_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
lean_object* v___x_971_; 
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 0, v___x_969_);
v___x_971_ = v___x_959_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_969_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
}
else
{
lean_dec(v_snd_955_);
lean_dec(v_fst_954_);
return v___x_956_;
}
}
else
{
lean_dec_ref(v_arg_951_);
lean_dec_ref(v_subst_912_);
return v___x_952_;
}
}
case 6:
{
lean_object* v_binderName_976_; lean_object* v_binderType_977_; lean_object* v_body_978_; uint8_t v_binderInfo_979_; lean_object* v___x_980_; 
v_binderName_976_ = lean_ctor_get(v_e_911_, 0);
lean_inc(v_binderName_976_);
v_binderType_977_ = lean_ctor_get(v_e_911_, 1);
lean_inc_ref(v_binderType_977_);
v_body_978_ = lean_ctor_get(v_e_911_, 2);
lean_inc_ref(v_body_978_);
v_binderInfo_979_ = lean_ctor_get_uint8(v_e_911_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_911_, 3);
v___x_980_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(v_a_913_, v_a_914_, v_a_915_, v_a_916_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; lean_object* v___x_982_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_a_981_);
lean_dec_ref_known(v___x_980_, 1);
lean_inc_ref(v_subst_912_);
v___x_982_ = l_Lean_Elab_Tactic_Do_countUses(v_binderType_977_, v_subst_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; lean_object* v_fst_984_; lean_object* v_snd_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_a_983_);
lean_dec_ref_known(v___x_982_, 1);
v_fst_984_ = lean_ctor_get(v_a_983_, 0);
lean_inc(v_fst_984_);
v_snd_985_ = lean_ctor_get(v_a_983_, 1);
lean_inc(v_snd_985_);
lean_dec(v_a_983_);
lean_inc(v_a_981_);
v___x_986_ = lean_array_push(v_subst_912_, v_a_981_);
v___x_987_ = l_Lean_Elab_Tactic_Do_countUses(v_body_978_, v___x_986_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_1007_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_990_ = v___x_987_;
v_isShared_991_ = v_isSharedCheck_1007_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_987_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_1007_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v_fst_992_; lean_object* v_snd_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1006_; 
v_fst_992_ = lean_ctor_get(v_a_988_, 0);
v_snd_993_ = lean_ctor_get(v_a_988_, 1);
v_isSharedCheck_1006_ = !lean_is_exclusive(v_a_988_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_995_ = v_a_988_;
v_isShared_996_ = v_isSharedCheck_1006_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_snd_993_);
lean_inc(v_fst_992_);
lean_dec(v_a_988_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1006_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1001_; 
v___x_997_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_snd_985_, v_snd_993_);
lean_dec(v_snd_985_);
v___x_998_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v___x_997_, v_a_981_);
lean_dec(v_a_981_);
v___x_999_ = l_Lean_Expr_lam___override(v_binderName_976_, v_fst_984_, v_fst_992_, v_binderInfo_979_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 1, v___x_998_);
lean_ctor_set(v___x_995_, 0, v___x_999_);
v___x_1001_ = v___x_995_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v___x_999_);
lean_ctor_set(v_reuseFailAlloc_1005_, 1, v___x_998_);
v___x_1001_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
lean_object* v___x_1003_; 
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 0, v___x_1001_);
v___x_1003_ = v___x_990_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v___x_1001_);
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
}
else
{
lean_dec(v_snd_985_);
lean_dec(v_fst_984_);
lean_dec(v_a_981_);
lean_dec(v_binderName_976_);
return v___x_987_;
}
}
else
{
lean_dec(v_a_981_);
lean_dec_ref(v_body_978_);
lean_dec(v_binderName_976_);
lean_dec_ref(v_subst_912_);
return v___x_982_;
}
}
else
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1015_; 
lean_dec_ref(v_body_978_);
lean_dec_ref(v_binderType_977_);
lean_dec(v_binderName_976_);
lean_dec_ref(v_subst_912_);
v_a_1008_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1010_ = v___x_980_;
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_980_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1013_; 
if (v_isShared_1011_ == 0)
{
v___x_1013_ = v___x_1010_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_a_1008_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
}
case 7:
{
lean_object* v_binderName_1016_; lean_object* v_binderType_1017_; lean_object* v_body_1018_; uint8_t v_binderInfo_1019_; lean_object* v___x_1020_; 
v_binderName_1016_ = lean_ctor_get(v_e_911_, 0);
lean_inc(v_binderName_1016_);
v_binderType_1017_ = lean_ctor_get(v_e_911_, 1);
lean_inc_ref(v_binderType_1017_);
v_body_1018_ = lean_ctor_get(v_e_911_, 2);
lean_inc_ref(v_body_1018_);
v_binderInfo_1019_ = lean_ctor_get_uint8(v_e_911_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_911_, 3);
v___x_1020_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(v_a_913_, v_a_914_, v_a_915_, v_a_916_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v___x_1022_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_a_1021_);
lean_dec_ref_known(v___x_1020_, 1);
lean_inc_ref(v_subst_912_);
v___x_1022_ = l_Lean_Elab_Tactic_Do_countUses(v_binderType_1017_, v_subst_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v_a_1023_; lean_object* v_fst_1024_; lean_object* v_snd_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
lean_inc(v_a_1023_);
lean_dec_ref_known(v___x_1022_, 1);
v_fst_1024_ = lean_ctor_get(v_a_1023_, 0);
lean_inc(v_fst_1024_);
v_snd_1025_ = lean_ctor_get(v_a_1023_, 1);
lean_inc(v_snd_1025_);
lean_dec(v_a_1023_);
lean_inc(v_a_1021_);
v___x_1026_ = lean_array_push(v_subst_912_, v_a_1021_);
v___x_1027_ = l_Lean_Elab_Tactic_Do_countUses(v_body_1018_, v___x_1026_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1047_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1030_ = v___x_1027_;
v_isShared_1031_ = v_isSharedCheck_1047_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1027_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1047_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v_fst_1032_; lean_object* v_snd_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1046_; 
v_fst_1032_ = lean_ctor_get(v_a_1028_, 0);
v_snd_1033_ = lean_ctor_get(v_a_1028_, 1);
v_isSharedCheck_1046_ = !lean_is_exclusive(v_a_1028_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1035_ = v_a_1028_;
v_isShared_1036_ = v_isSharedCheck_1046_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_snd_1033_);
lean_inc(v_fst_1032_);
lean_dec(v_a_1028_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1046_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1041_; 
v___x_1037_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_snd_1025_, v_snd_1033_);
lean_dec(v_snd_1025_);
v___x_1038_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v___x_1037_, v_a_1021_);
lean_dec(v_a_1021_);
v___x_1039_ = l_Lean_Expr_forallE___override(v_binderName_1016_, v_fst_1024_, v_fst_1032_, v_binderInfo_1019_);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 1, v___x_1038_);
lean_ctor_set(v___x_1035_, 0, v___x_1039_);
v___x_1041_ = v___x_1035_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1039_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v___x_1038_);
v___x_1041_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_object* v___x_1043_; 
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 0, v___x_1041_);
v___x_1043_ = v___x_1030_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1041_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
}
else
{
lean_dec(v_snd_1025_);
lean_dec(v_fst_1024_);
lean_dec(v_a_1021_);
lean_dec(v_binderName_1016_);
return v___x_1027_;
}
}
else
{
lean_dec(v_a_1021_);
lean_dec_ref(v_body_1018_);
lean_dec(v_binderName_1016_);
lean_dec_ref(v_subst_912_);
return v___x_1022_;
}
}
else
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1055_; 
lean_dec_ref(v_body_1018_);
lean_dec_ref(v_binderType_1017_);
lean_dec(v_binderName_1016_);
lean_dec_ref(v_subst_912_);
v_a_1048_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1050_ = v___x_1020_;
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_1020_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1053_; 
if (v_isShared_1051_ == 0)
{
v___x_1053_ = v___x_1050_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_a_1048_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
case 8:
{
lean_object* v_declName_1056_; lean_object* v_type_1057_; lean_object* v_value_1058_; lean_object* v_body_1059_; uint8_t v_nondep_1060_; lean_object* v___x_1061_; 
v_declName_1056_ = lean_ctor_get(v_e_911_, 0);
lean_inc(v_declName_1056_);
v_type_1057_ = lean_ctor_get(v_e_911_, 1);
lean_inc_ref(v_type_1057_);
v_value_1058_ = lean_ctor_get(v_e_911_, 2);
lean_inc_ref(v_value_1058_);
v_body_1059_ = lean_ctor_get(v_e_911_, 3);
lean_inc_ref(v_body_1059_);
v_nondep_1060_ = lean_ctor_get_uint8(v_e_911_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_911_, 4);
v___x_1061_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(v_a_913_, v_a_914_, v_a_915_, v_a_916_);
if (lean_obj_tag(v___x_1061_) == 0)
{
lean_object* v_a_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v_a_1062_ = lean_ctor_get(v___x_1061_, 0);
lean_inc_n(v_a_1062_, 2);
lean_dec_ref_known(v___x_1061_, 1);
lean_inc_ref(v_subst_912_);
v___x_1063_ = lean_array_push(v_subst_912_, v_a_1062_);
v___x_1064_ = l_Lean_Elab_Tactic_Do_countUses(v_body_1059_, v___x_1063_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1107_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1067_ = v___x_1064_;
v_isShared_1068_ = v_isSharedCheck_1107_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1064_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1107_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v_fst_1069_; lean_object* v_snd_1070_; lean_object* v___x_1072_; 
v_fst_1069_ = lean_ctor_get(v_a_1065_, 0);
lean_inc(v_fst_1069_);
v_snd_1070_ = lean_ctor_get(v_a_1065_, 1);
lean_inc(v_snd_1070_);
lean_dec(v_a_1065_);
if (v_isShared_1068_ == 0)
{
lean_ctor_set_tag(v___x_1067_, 1);
lean_ctor_set(v___x_1067_, 0, v_value_1058_);
v___x_1072_ = v___x_1067_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_value_1058_);
v___x_1072_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
lean_object* v___x_1073_; 
v___x_1073_ = l_Lean_Elab_Tactic_Do_countUsesDecl(v_a_1062_, v_type_1057_, v___x_1072_, v_snd_1070_, v_subst_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
lean_dec(v_a_1062_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1097_; 
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1076_ = v___x_1073_;
v_isShared_1077_ = v_isSharedCheck_1097_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1073_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1097_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v_snd_1078_; lean_object* v_fst_1079_; 
v_snd_1078_ = lean_ctor_get(v_a_1074_, 1);
lean_inc(v_snd_1078_);
v_fst_1079_ = lean_ctor_get(v_snd_1078_, 0);
lean_inc(v_fst_1079_);
if (lean_obj_tag(v_fst_1079_) == 1)
{
lean_object* v_fst_1080_; lean_object* v_snd_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1093_; 
v_fst_1080_ = lean_ctor_get(v_a_1074_, 0);
lean_inc(v_fst_1080_);
lean_dec(v_a_1074_);
v_snd_1081_ = lean_ctor_get(v_snd_1078_, 1);
v_isSharedCheck_1093_ = !lean_is_exclusive(v_snd_1078_);
if (v_isSharedCheck_1093_ == 0)
{
lean_object* v_unused_1094_; 
v_unused_1094_ = lean_ctor_get(v_snd_1078_, 0);
lean_dec(v_unused_1094_);
v___x_1083_ = v_snd_1078_;
v_isShared_1084_ = v_isSharedCheck_1093_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_snd_1081_);
lean_dec(v_snd_1078_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1093_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v_val_1085_; lean_object* v___x_1086_; lean_object* v___x_1088_; 
v_val_1085_ = lean_ctor_get(v_fst_1079_, 0);
lean_inc(v_val_1085_);
lean_dec_ref_known(v_fst_1079_, 1);
v___x_1086_ = l_Lean_Expr_letE___override(v_declName_1056_, v_fst_1080_, v_val_1085_, v_fst_1069_, v_nondep_1060_);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 0, v___x_1086_);
v___x_1088_ = v___x_1083_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1086_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v_snd_1081_);
v___x_1088_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
lean_object* v___x_1090_; 
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 0, v___x_1088_);
v___x_1090_ = v___x_1076_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1088_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
else
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
lean_dec(v_fst_1079_);
lean_dec(v_snd_1078_);
lean_del_object(v___x_1076_);
lean_dec(v_a_1074_);
lean_dec(v_fst_1069_);
lean_dec(v_declName_1056_);
v___x_1095_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__5, &l_Lean_Elab_Tactic_Do_countUses___closed__5_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__5);
v___x_1096_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v___x_1095_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
return v___x_1096_;
}
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
lean_dec(v_fst_1069_);
lean_dec(v_declName_1056_);
v_a_1098_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1073_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1073_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1062_);
lean_dec_ref(v_value_1058_);
lean_dec_ref(v_type_1057_);
lean_dec(v_declName_1056_);
lean_dec_ref(v_subst_912_);
return v___x_1064_;
}
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
lean_dec_ref(v_body_1059_);
lean_dec_ref(v_value_1058_);
lean_dec_ref(v_type_1057_);
lean_dec(v_declName_1056_);
lean_dec_ref(v_subst_912_);
v_a_1108_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1061_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1061_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
case 10:
{
lean_object* v_data_1116_; lean_object* v_expr_1117_; lean_object* v___x_1118_; 
v_data_1116_ = lean_ctor_get(v_e_911_, 0);
lean_inc(v_data_1116_);
v_expr_1117_ = lean_ctor_get(v_e_911_, 1);
lean_inc_ref(v_expr_1117_);
lean_dec_ref_known(v_e_911_, 2);
v___x_1118_ = l_Lean_Elab_Tactic_Do_countUses(v_expr_1117_, v_subst_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1128_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1121_ = v___x_1118_;
v_isShared_1122_ = v_isSharedCheck_1128_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1118_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1128_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___f_1123_; lean_object* v___x_1124_; lean_object* v___x_1126_; 
v___f_1123_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_countUses___lam__0), 2, 1);
lean_closure_set(v___f_1123_, 0, v_data_1116_);
v___x_1124_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v___f_1123_, v_a_1119_);
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 0, v___x_1124_);
v___x_1126_ = v___x_1121_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1124_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
else
{
lean_dec(v_data_1116_);
return v___x_1118_;
}
}
case 11:
{
lean_object* v_typeName_1129_; lean_object* v_idx_1130_; lean_object* v_struct_1131_; lean_object* v___x_1132_; 
v_typeName_1129_ = lean_ctor_get(v_e_911_, 0);
lean_inc(v_typeName_1129_);
v_idx_1130_ = lean_ctor_get(v_e_911_, 1);
lean_inc(v_idx_1130_);
v_struct_1131_ = lean_ctor_get(v_e_911_, 2);
lean_inc_ref(v_struct_1131_);
lean_dec_ref_known(v_e_911_, 3);
v___x_1132_ = l_Lean_Elab_Tactic_Do_countUses(v_struct_1131_, v_subst_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1142_; 
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1135_ = v___x_1132_;
v_isShared_1136_ = v_isSharedCheck_1142_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1132_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1142_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___f_1137_; lean_object* v___x_1138_; lean_object* v___x_1140_; 
v___f_1137_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_countUses___lam__1), 3, 2);
lean_closure_set(v___f_1137_, 0, v_typeName_1129_);
lean_closure_set(v___f_1137_, 1, v_idx_1130_);
v___x_1138_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v___f_1137_, v_a_1133_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v___x_1138_);
v___x_1140_ = v___x_1135_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1138_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
else
{
lean_dec(v_idx_1130_);
lean_dec(v_typeName_1129_);
return v___x_1132_;
}
}
default: 
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
lean_dec_ref(v_subst_912_);
v___x_1143_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3);
v___x_1144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1144_, 0, v_e_911_);
lean_ctor_set(v___x_1144_, 1, v___x_1143_);
v___x_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
return v___x_1145_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl(lean_object* v_fvarId_1146_, lean_object* v_ty_1147_, lean_object* v_val_x3f_1148_, lean_object* v_bodyUses_1149_, lean_object* v_subst_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_){
_start:
{
lean_object* v___x_1156_; 
lean_inc_ref(v_subst_1150_);
v___x_1156_ = l_Lean_Elab_Tactic_Do_countUses(v_ty_1147_, v_subst_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1212_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1159_ = v___x_1156_;
v_isShared_1160_ = v_isSharedCheck_1212_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1156_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1212_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v_fst_1161_; lean_object* v_snd_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1211_; 
v_fst_1161_ = lean_ctor_get(v_a_1157_, 0);
v_snd_1162_ = lean_ctor_get(v_a_1157_, 1);
v_isSharedCheck_1211_ = !lean_is_exclusive(v_a_1157_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1164_ = v_a_1157_;
v_isShared_1165_ = v_isSharedCheck_1211_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_snd_1162_);
lean_inc(v_fst_1161_);
lean_dec(v_a_1157_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1211_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___y_1167_; uint8_t v___y_1168_; lean_object* v___y_1169_; lean_object* v_fst_1184_; lean_object* v_snd_1185_; 
if (lean_obj_tag(v_val_x3f_1148_) == 0)
{
lean_object* v___x_1195_; 
lean_dec_ref(v_subst_1150_);
v___x_1195_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3);
v_fst_1184_ = v_val_x3f_1148_;
v_snd_1185_ = v___x_1195_;
goto v___jp_1183_;
}
else
{
lean_object* v_val_1196_; lean_object* v___x_1197_; 
v_val_1196_ = lean_ctor_get(v_val_x3f_1148_, 0);
lean_inc(v_val_1196_);
lean_dec_ref_known(v_val_x3f_1148_, 1);
v___x_1197_ = l_Lean_Elab_Tactic_Do_countUses(v_val_1196_, v_subst_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_object* v_a_1198_; lean_object* v___f_1199_; lean_object* v___x_1200_; lean_object* v_fst_1201_; lean_object* v_snd_1202_; 
v_a_1198_ = lean_ctor_get(v___x_1197_, 0);
lean_inc(v_a_1198_);
lean_dec_ref_known(v___x_1197_, 1);
v___f_1199_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4));
v___x_1200_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v___f_1199_, v_a_1198_);
v_fst_1201_ = lean_ctor_get(v___x_1200_, 0);
lean_inc(v_fst_1201_);
v_snd_1202_ = lean_ctor_get(v___x_1200_, 1);
lean_inc(v_snd_1202_);
lean_dec_ref(v___x_1200_);
v_fst_1184_ = v_fst_1201_;
v_snd_1185_ = v_snd_1202_;
goto v___jp_1183_;
}
else
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
lean_del_object(v___x_1164_);
lean_dec(v_snd_1162_);
lean_dec(v_fst_1161_);
lean_del_object(v___x_1159_);
lean_dec_ref(v_bodyUses_1149_);
v_a_1203_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1205_ = v___x_1197_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1197_);
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
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1203_);
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
v___jp_1166_:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1177_; 
v___x_1170_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v___y_1169_, v_fvarId_1146_);
v___x_1171_ = lean_box(0);
v___x_1172_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_1173_ = l_Lean_Elab_Tactic_Do_Uses_toNat(v___y_1168_);
v___x_1174_ = l_Lean_KVMap_setNat(v___x_1171_, v___x_1172_, v___x_1173_);
v___x_1175_ = l_Lean_Elab_Tactic_Do_addMData(v___x_1174_, v_fst_1161_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 1, v___x_1170_);
lean_ctor_set(v___x_1164_, 0, v___y_1167_);
v___x_1177_ = v___x_1164_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___y_1167_);
lean_ctor_set(v_reuseFailAlloc_1182_, 1, v___x_1170_);
v___x_1177_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
lean_object* v___x_1178_; lean_object* v___x_1180_; 
v___x_1178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1175_);
lean_ctor_set(v___x_1178_, 1, v___x_1177_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v___x_1178_);
v___x_1180_ = v___x_1159_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1178_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
v___jp_1183_:
{
uint8_t v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; uint8_t v___x_1189_; uint8_t v___x_1190_; 
v___x_1186_ = 0;
v___x_1187_ = lean_box(v___x_1186_);
v___x_1188_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(v_bodyUses_1149_, v_fvarId_1146_, v___x_1187_);
lean_dec(v___x_1187_);
v___x_1189_ = lean_unbox(v___x_1188_);
v___x_1190_ = l_Lean_Elab_Tactic_Do_instBEqUses_beq(v___x_1189_, v___x_1186_);
if (v___x_1190_ == 0)
{
lean_object* v___x_1191_; lean_object* v___x_1192_; uint8_t v___x_1193_; 
v___x_1191_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_bodyUses_1149_, v_snd_1162_);
lean_dec_ref(v_bodyUses_1149_);
v___x_1192_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v___x_1191_, v_snd_1185_);
lean_dec_ref(v___x_1191_);
v___x_1193_ = lean_unbox(v___x_1188_);
lean_dec(v___x_1188_);
v___y_1167_ = v_fst_1184_;
v___y_1168_ = v___x_1193_;
v___y_1169_ = v___x_1192_;
goto v___jp_1166_;
}
else
{
uint8_t v___x_1194_; 
lean_dec_ref(v_snd_1185_);
lean_dec(v_snd_1162_);
v___x_1194_ = lean_unbox(v___x_1188_);
lean_dec(v___x_1188_);
v___y_1167_ = v_fst_1184_;
v___y_1168_ = v___x_1194_;
v___y_1169_ = v_bodyUses_1149_;
goto v___jp_1166_;
}
}
}
}
}
else
{
lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1220_; 
lean_dec_ref(v_subst_1150_);
lean_dec_ref(v_bodyUses_1149_);
lean_dec(v_val_x3f_1148_);
v_a_1213_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1215_ = v___x_1156_;
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1156_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1218_; 
if (v_isShared_1216_ == 0)
{
v___x_1218_ = v___x_1215_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_a_1213_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___boxed(lean_object* v_fvarId_1221_, lean_object* v_ty_1222_, lean_object* v_val_x3f_1223_, lean_object* v_bodyUses_1224_, lean_object* v_subst_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Lean_Elab_Tactic_Do_countUsesDecl(v_fvarId_1221_, v_ty_1222_, v_val_x3f_1223_, v_bodyUses_1224_, v_subst_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_);
lean_dec(v_a_1229_);
lean_dec_ref(v_a_1228_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec(v_fvarId_1221_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses___boxed(lean_object* v_e_1232_, lean_object* v_subst_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l_Lean_Elab_Tactic_Do_countUses(v_e_1232_, v_subst_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_);
lean_dec(v_a_1237_);
lean_dec_ref(v_a_1236_);
lean_dec(v_a_1235_);
lean_dec_ref(v_a_1234_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0(lean_object* v_00_u03b2_1240_, lean_object* v_m_1241_, lean_object* v_a_1242_, lean_object* v_fallback_1243_){
_start:
{
lean_object* v___x_1244_; 
v___x_1244_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(v_m_1241_, v_a_1242_, v_fallback_1243_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___boxed(lean_object* v_00_u03b2_1245_, lean_object* v_m_1246_, lean_object* v_a_1247_, lean_object* v_fallback_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0(v_00_u03b2_1245_, v_m_1246_, v_a_1247_, v_fallback_1248_);
lean_dec(v_fallback_1248_);
lean_dec(v_a_1247_);
lean_dec_ref(v_m_1246_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1(lean_object* v_00_u03b2_1250_, lean_object* v_m_1251_, lean_object* v_a_1252_){
_start:
{
lean_object* v___x_1253_; 
v___x_1253_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v_m_1251_, v_a_1252_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___boxed(lean_object* v_00_u03b2_1254_, lean_object* v_m_1255_, lean_object* v_a_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1(v_00_u03b2_1254_, v_m_1255_, v_a_1256_);
lean_dec(v_a_1256_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3(lean_object* v_00_u03b1_1258_, lean_object* v_msg_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v_msg_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___boxed(lean_object* v_00_u03b1_1266_, lean_object* v_msg_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3(v_00_u03b1_1266_, v_msg_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4(lean_object* v_00_u03b2_1274_, lean_object* v_m_1275_, lean_object* v_a_1276_, lean_object* v_b_1277_){
_start:
{
lean_object* v___x_1278_; 
v___x_1278_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(v_m_1275_, v_a_1276_, v_b_1277_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9(lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
lean_object* v___x_1284_; 
v___x_1284_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(v___y_1282_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___boxed(lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9(v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0(lean_object* v_00_u03b2_1291_, lean_object* v_a_1292_, lean_object* v_fallback_1293_, lean_object* v_x_1294_){
_start:
{
lean_object* v___x_1295_; 
v___x_1295_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(v_a_1292_, v_fallback_1293_, v_x_1294_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1296_, lean_object* v_a_1297_, lean_object* v_fallback_1298_, lean_object* v_x_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0(v_00_u03b2_1296_, v_a_1297_, v_fallback_1298_, v_x_1299_);
lean_dec(v_x_1299_);
lean_dec(v_fallback_1298_);
lean_dec(v_a_1297_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2(lean_object* v_00_u03b2_1301_, lean_object* v_a_1302_, lean_object* v_x_1303_){
_start:
{
lean_object* v___x_1304_; 
v___x_1304_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_1302_, v_x_1303_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1305_, lean_object* v_a_1306_, lean_object* v_x_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2(v_00_u03b2_1305_, v_a_1306_, v_x_1307_);
lean_dec(v_a_1306_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7(lean_object* v_00_u03b2_1309_, lean_object* v_a_1310_, lean_object* v_b_1311_, lean_object* v_x_1312_){
_start:
{
lean_object* v___x_1313_; 
v___x_1313_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(v_a_1310_, v_b_1311_, v_x_1312_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(lean_object* v_as_1316_, size_t v_i_1317_, size_t v_stop_1318_, lean_object* v_b_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
uint8_t v___x_1325_; 
v___x_1325_ = lean_usize_dec_eq(v_i_1317_, v_stop_1318_);
if (v___x_1325_ == 0)
{
size_t v___x_1326_; size_t v___x_1327_; lean_object* v___x_1328_; 
v___x_1326_ = ((size_t)1ULL);
v___x_1327_ = lean_usize_sub(v_i_1317_, v___x_1326_);
v___x_1328_ = lean_array_uget_borrowed(v_as_1316_, v___x_1327_);
if (lean_obj_tag(v___x_1328_) == 0)
{
v_i_1317_ = v___x_1327_;
goto _start;
}
else
{
lean_object* v_val_1330_; lean_object* v_fst_1331_; lean_object* v_snd_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v_val_1330_ = lean_ctor_get(v___x_1328_, 0);
v_fst_1331_ = lean_ctor_get(v_b_1319_, 0);
lean_inc(v_fst_1331_);
v_snd_1332_ = lean_ctor_get(v_b_1319_, 1);
lean_inc(v_snd_1332_);
lean_dec_ref(v_b_1319_);
v___x_1333_ = l_Lean_LocalDecl_fvarId(v_val_1330_);
v___x_1334_ = l_Lean_LocalDecl_type(v_val_1330_);
v___x_1335_ = l_Lean_LocalDecl_value_x3f(v_val_1330_, v___x_1325_);
v___x_1336_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0));
v___x_1337_ = l_Lean_Elab_Tactic_Do_countUsesDecl(v___x_1333_, v___x_1334_, v___x_1335_, v_snd_1332_, v___x_1336_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
lean_dec(v___x_1333_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v_a_1338_; lean_object* v_snd_1339_; lean_object* v_fst_1340_; lean_object* v_fst_1341_; lean_object* v_snd_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1357_; 
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_a_1338_);
lean_dec_ref_known(v___x_1337_, 1);
v_snd_1339_ = lean_ctor_get(v_a_1338_, 1);
lean_inc(v_snd_1339_);
v_fst_1340_ = lean_ctor_get(v_a_1338_, 0);
lean_inc(v_fst_1340_);
lean_dec(v_a_1338_);
v_fst_1341_ = lean_ctor_get(v_snd_1339_, 0);
v_snd_1342_ = lean_ctor_get(v_snd_1339_, 1);
v_isSharedCheck_1357_ = !lean_is_exclusive(v_snd_1339_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1344_ = v_snd_1339_;
v_isShared_1345_ = v_isSharedCheck_1357_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_snd_1342_);
lean_inc(v_fst_1341_);
lean_dec(v_snd_1339_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1357_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___y_1347_; 
if (lean_obj_tag(v_fst_1341_) == 0)
{
lean_object* v___x_1353_; 
lean_inc(v_val_1330_);
v___x_1353_ = l_Lean_LocalDecl_setType(v_val_1330_, v_fst_1340_);
v___y_1347_ = v___x_1353_;
goto v___jp_1346_;
}
else
{
lean_object* v_val_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v_val_1354_ = lean_ctor_get(v_fst_1341_, 0);
lean_inc(v_val_1354_);
lean_dec_ref_known(v_fst_1341_, 1);
lean_inc(v_val_1330_);
v___x_1355_ = l_Lean_LocalDecl_setType(v_val_1330_, v_fst_1340_);
v___x_1356_ = l_Lean_LocalDecl_setValue(v___x_1355_, v_val_1354_);
v___y_1347_ = v___x_1356_;
goto v___jp_1346_;
}
v___jp_1346_:
{
lean_object* v___x_1348_; lean_object* v___x_1350_; 
v___x_1348_ = lean_array_push(v_fst_1331_, v___y_1347_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 0, v___x_1348_);
v___x_1350_ = v___x_1344_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v___x_1348_);
lean_ctor_set(v_reuseFailAlloc_1352_, 1, v_snd_1342_);
v___x_1350_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
v_i_1317_ = v___x_1327_;
v_b_1319_ = v___x_1350_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1365_; 
lean_dec(v_fst_1331_);
v_a_1358_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1360_ = v___x_1337_;
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1337_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1363_; 
if (v_isShared_1361_ == 0)
{
v___x_1363_ = v___x_1360_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_a_1358_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
}
else
{
lean_object* v___x_1366_; 
v___x_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1366_, 0, v_b_1319_);
return v___x_1366_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___boxed(lean_object* v_as_1367_, lean_object* v_i_1368_, lean_object* v_stop_1369_, lean_object* v_b_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
size_t v_i_boxed_1376_; size_t v_stop_boxed_1377_; lean_object* v_res_1378_; 
v_i_boxed_1376_ = lean_unbox_usize(v_i_1368_);
lean_dec(v_i_1368_);
v_stop_boxed_1377_ = lean_unbox_usize(v_stop_1369_);
lean_dec(v_stop_1369_);
v_res_1378_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(v_as_1367_, v_i_boxed_1376_, v_stop_boxed_1377_, v_b_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
lean_dec_ref(v_as_1367_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(lean_object* v_x_1379_, lean_object* v_x_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_){
_start:
{
if (lean_obj_tag(v_x_1379_) == 0)
{
lean_object* v_cs_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1399_; 
v_cs_1386_ = lean_ctor_get(v_x_1379_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v_x_1379_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1388_ = v_x_1379_;
v_isShared_1389_ = v_isSharedCheck_1399_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_cs_1386_);
lean_dec(v_x_1379_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1399_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; uint8_t v___x_1392_; 
v___x_1390_ = lean_array_get_size(v_cs_1386_);
v___x_1391_ = lean_unsigned_to_nat(0u);
v___x_1392_ = lean_nat_dec_lt(v___x_1391_, v___x_1390_);
if (v___x_1392_ == 0)
{
lean_object* v___x_1394_; 
lean_dec_ref(v_cs_1386_);
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 0, v_x_1380_);
v___x_1394_ = v___x_1388_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_x_1380_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
else
{
size_t v___x_1396_; size_t v___x_1397_; lean_object* v___x_1398_; 
lean_del_object(v___x_1388_);
v___x_1396_ = lean_usize_of_nat(v___x_1390_);
v___x_1397_ = ((size_t)0ULL);
v___x_1398_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(v_cs_1386_, v___x_1396_, v___x_1397_, v_x_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
lean_dec_ref(v_cs_1386_);
return v___x_1398_;
}
}
}
else
{
lean_object* v_vs_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1413_; 
v_vs_1400_ = lean_ctor_get(v_x_1379_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v_x_1379_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1402_ = v_x_1379_;
v_isShared_1403_ = v_isSharedCheck_1413_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_vs_1400_);
lean_dec(v_x_1379_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1413_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; uint8_t v___x_1406_; 
v___x_1404_ = lean_array_get_size(v_vs_1400_);
v___x_1405_ = lean_unsigned_to_nat(0u);
v___x_1406_ = lean_nat_dec_lt(v___x_1405_, v___x_1404_);
if (v___x_1406_ == 0)
{
lean_object* v___x_1408_; 
lean_dec_ref(v_vs_1400_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set_tag(v___x_1402_, 0);
lean_ctor_set(v___x_1402_, 0, v_x_1380_);
v___x_1408_ = v___x_1402_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_x_1380_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
else
{
size_t v___x_1410_; size_t v___x_1411_; lean_object* v___x_1412_; 
lean_del_object(v___x_1402_);
v___x_1410_ = lean_usize_of_nat(v___x_1404_);
v___x_1411_ = ((size_t)0ULL);
v___x_1412_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(v_vs_1400_, v___x_1410_, v___x_1411_, v_x_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
lean_dec_ref(v_vs_1400_);
return v___x_1412_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(lean_object* v_as_1414_, size_t v_i_1415_, size_t v_stop_1416_, lean_object* v_b_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
uint8_t v___x_1423_; 
v___x_1423_ = lean_usize_dec_eq(v_i_1415_, v_stop_1416_);
if (v___x_1423_ == 0)
{
size_t v___x_1424_; size_t v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1424_ = ((size_t)1ULL);
v___x_1425_ = lean_usize_sub(v_i_1415_, v___x_1424_);
v___x_1426_ = lean_array_uget_borrowed(v_as_1414_, v___x_1425_);
lean_inc(v___x_1426_);
v___x_1427_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v___x_1426_, v_b_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
lean_inc(v_a_1428_);
lean_dec_ref_known(v___x_1427_, 1);
v_i_1415_ = v___x_1425_;
v_b_1417_ = v_a_1428_;
goto _start;
}
else
{
return v___x_1427_;
}
}
else
{
lean_object* v___x_1430_; 
v___x_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1430_, 0, v_b_1417_);
return v___x_1430_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_as_1431_, lean_object* v_i_1432_, lean_object* v_stop_1433_, lean_object* v_b_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
size_t v_i_boxed_1440_; size_t v_stop_boxed_1441_; lean_object* v_res_1442_; 
v_i_boxed_1440_ = lean_unbox_usize(v_i_1432_);
lean_dec(v_i_1432_);
v_stop_boxed_1441_ = lean_unbox_usize(v_stop_1433_);
lean_dec(v_stop_1433_);
v_res_1442_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(v_as_1431_, v_i_boxed_1440_, v_stop_boxed_1441_, v_b_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
lean_dec_ref(v_as_1431_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1___boxed(lean_object* v_x_1443_, lean_object* v_x_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v_x_1443_, v_x_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(lean_object* v_t_1451_, lean_object* v_init_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v_root_1458_; lean_object* v_tail_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; uint8_t v___x_1462_; 
v_root_1458_ = lean_ctor_get(v_t_1451_, 0);
lean_inc_ref(v_root_1458_);
v_tail_1459_ = lean_ctor_get(v_t_1451_, 1);
lean_inc_ref(v_tail_1459_);
lean_dec_ref(v_t_1451_);
v___x_1460_ = lean_array_get_size(v_tail_1459_);
v___x_1461_ = lean_unsigned_to_nat(0u);
v___x_1462_ = lean_nat_dec_lt(v___x_1461_, v___x_1460_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1463_; 
lean_dec_ref(v_tail_1459_);
v___x_1463_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v_root_1458_, v_init_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
return v___x_1463_;
}
else
{
size_t v___x_1464_; size_t v___x_1465_; lean_object* v___x_1466_; 
v___x_1464_ = lean_usize_of_nat(v___x_1460_);
v___x_1465_ = ((size_t)0ULL);
v___x_1466_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(v_tail_1459_, v___x_1464_, v___x_1465_, v_init_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
lean_dec_ref(v_tail_1459_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v_a_1467_; lean_object* v___x_1468_; 
v_a_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc(v_a_1467_);
lean_dec_ref_known(v___x_1466_, 1);
v___x_1468_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v_root_1458_, v_a_1467_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
return v___x_1468_;
}
else
{
lean_dec_ref(v_root_1458_);
return v___x_1466_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0___boxed(lean_object* v_t_1469_, lean_object* v_init_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(v_t_1469_, v_init_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(lean_object* v_lctx_1477_, lean_object* v_init_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v_decls_1484_; lean_object* v___x_1485_; 
v_decls_1484_ = lean_ctor_get(v_lctx_1477_, 1);
lean_inc_ref(v_decls_1484_);
lean_dec_ref(v_lctx_1477_);
v___x_1485_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(v_decls_1484_, v_init_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0___boxed(lean_object* v_lctx_1486_, lean_object* v_init_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(v_lctx_1486_, v_init_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(size_t v_sz_1494_, size_t v_i_1495_, lean_object* v_bs_1496_, lean_object* v___y_1497_){
_start:
{
uint8_t v___x_1499_; 
v___x_1499_ = lean_usize_dec_lt(v_i_1495_, v_sz_1494_);
if (v___x_1499_ == 0)
{
lean_object* v___x_1500_; 
v___x_1500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1500_, 0, v_bs_1496_);
return v___x_1500_;
}
else
{
lean_object* v_v_1501_; lean_object* v___x_1502_; lean_object* v_bs_x27_1503_; lean_object* v_a_1505_; 
v_v_1501_ = lean_array_uget(v_bs_1496_, v_i_1495_);
v___x_1502_ = lean_unsigned_to_nat(0u);
v_bs_x27_1503_ = lean_array_uset(v_bs_1496_, v_i_1495_, v___x_1502_);
if (lean_obj_tag(v_v_1501_) == 0)
{
v_a_1505_ = v_v_1501_;
goto v___jp_1504_;
}
else
{
lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1524_; 
v_isSharedCheck_1524_ = !lean_is_exclusive(v_v_1501_);
if (v_isSharedCheck_1524_ == 0)
{
lean_object* v_unused_1525_; 
v_unused_1525_ = lean_ctor_get(v_v_1501_, 0);
lean_dec(v_unused_1525_);
v___x_1511_ = v_v_1501_;
v_isShared_1512_ = v_isSharedCheck_1524_;
goto v_resetjp_1510_;
}
else
{
lean_dec(v_v_1501_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1524_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1522_; 
v___x_1513_ = lean_st_ref_take(v___y_1497_);
v___x_1514_ = l_Lean_instInhabitedLocalDecl_default;
v___x_1515_ = lean_array_get_size(v___x_1513_);
v___x_1516_ = lean_unsigned_to_nat(1u);
v___x_1517_ = lean_nat_sub(v___x_1515_, v___x_1516_);
v___x_1518_ = lean_array_get(v___x_1514_, v___x_1513_, v___x_1517_);
lean_dec(v___x_1517_);
v___x_1519_ = lean_array_pop(v___x_1513_);
v___x_1520_ = lean_st_ref_set(v___y_1497_, v___x_1519_);
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 0, v___x_1518_);
v___x_1522_ = v___x_1511_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1518_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
v_a_1505_ = v___x_1522_;
goto v___jp_1504_;
}
}
}
v___jp_1504_:
{
size_t v___x_1506_; size_t v___x_1507_; lean_object* v___x_1508_; 
v___x_1506_ = ((size_t)1ULL);
v___x_1507_ = lean_usize_add(v_i_1495_, v___x_1506_);
v___x_1508_ = lean_array_uset(v_bs_x27_1503_, v_i_1495_, v_a_1505_);
v_i_1495_ = v___x_1507_;
v_bs_1496_ = v___x_1508_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg___boxed(lean_object* v_sz_1526_, lean_object* v_i_1527_, lean_object* v_bs_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
size_t v_sz_boxed_1531_; size_t v_i_boxed_1532_; lean_object* v_res_1533_; 
v_sz_boxed_1531_ = lean_unbox_usize(v_sz_1526_);
lean_dec(v_sz_1526_);
v_i_boxed_1532_ = lean_unbox_usize(v_i_1527_);
lean_dec(v_i_1527_);
v_res_1533_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_boxed_1531_, v_i_boxed_1532_, v_bs_1528_, v___y_1529_);
lean_dec(v___y_1529_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(lean_object* v_x_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
if (lean_obj_tag(v_x_1534_) == 0)
{
lean_object* v_cs_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1567_; 
v_cs_1541_ = lean_ctor_get(v_x_1534_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v_x_1534_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1543_ = v_x_1534_;
v_isShared_1544_ = v_isSharedCheck_1567_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_cs_1541_);
lean_dec(v_x_1534_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1567_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
size_t v_sz_1545_; size_t v___x_1546_; lean_object* v___x_1547_; 
v_sz_1545_ = lean_array_size(v_cs_1541_);
v___x_1546_ = ((size_t)0ULL);
v___x_1547_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(v_sz_1545_, v___x_1546_, v_cs_1541_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1558_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1550_ = v___x_1547_;
v_isShared_1551_ = v_isSharedCheck_1558_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1547_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1558_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1553_; 
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 0, v_a_1548_);
v___x_1553_ = v___x_1543_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_a_1548_);
v___x_1553_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
lean_object* v___x_1555_; 
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 0, v___x_1553_);
v___x_1555_ = v___x_1550_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1553_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
}
else
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1566_; 
lean_del_object(v___x_1543_);
v_a_1559_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1561_ = v___x_1547_;
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1547_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1559_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
}
else
{
lean_object* v_vs_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1594_; 
v_vs_1568_ = lean_ctor_get(v_x_1534_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v_x_1534_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1570_ = v_x_1534_;
v_isShared_1571_ = v_isSharedCheck_1594_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_vs_1568_);
lean_dec(v_x_1534_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1594_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
size_t v_sz_1572_; size_t v___x_1573_; lean_object* v___x_1574_; 
v_sz_1572_ = lean_array_size(v_vs_1568_);
v___x_1573_ = ((size_t)0ULL);
v___x_1574_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_1572_, v___x_1573_, v_vs_1568_, v___y_1535_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1585_; 
v_a_1575_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1577_ = v___x_1574_;
v_isShared_1578_ = v_isSharedCheck_1585_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1574_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1585_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1580_; 
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 0, v_a_1575_);
v___x_1580_ = v___x_1570_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_a_1575_);
v___x_1580_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
lean_object* v___x_1582_; 
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 0, v___x_1580_);
v___x_1582_ = v___x_1577_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1580_);
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
else
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1593_; 
lean_del_object(v___x_1570_);
v_a_1586_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1588_ = v___x_1574_;
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1574_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
if (v_isShared_1589_ == 0)
{
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1586_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(size_t v_sz_1595_, size_t v_i_1596_, lean_object* v_bs_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
uint8_t v___x_1604_; 
v___x_1604_ = lean_usize_dec_lt(v_i_1596_, v_sz_1595_);
if (v___x_1604_ == 0)
{
lean_object* v___x_1605_; 
v___x_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1605_, 0, v_bs_1597_);
return v___x_1605_;
}
else
{
lean_object* v_v_1606_; lean_object* v___x_1607_; 
v_v_1606_ = lean_array_uget_borrowed(v_bs_1597_, v_i_1596_);
lean_inc(v_v_1606_);
v___x_1607_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(v_v_1606_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v_a_1608_; lean_object* v___x_1609_; lean_object* v_bs_x27_1610_; size_t v___x_1611_; size_t v___x_1612_; lean_object* v___x_1613_; 
v_a_1608_ = lean_ctor_get(v___x_1607_, 0);
lean_inc(v_a_1608_);
lean_dec_ref_known(v___x_1607_, 1);
v___x_1609_ = lean_unsigned_to_nat(0u);
v_bs_x27_1610_ = lean_array_uset(v_bs_1597_, v_i_1596_, v___x_1609_);
v___x_1611_ = ((size_t)1ULL);
v___x_1612_ = lean_usize_add(v_i_1596_, v___x_1611_);
v___x_1613_ = lean_array_uset(v_bs_x27_1610_, v_i_1596_, v_a_1608_);
v_i_1596_ = v___x_1612_;
v_bs_1597_ = v___x_1613_;
goto _start;
}
else
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1622_; 
lean_dec_ref(v_bs_1597_);
v_a_1615_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1617_ = v___x_1607_;
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1607_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1620_; 
if (v_isShared_1618_ == 0)
{
v___x_1620_ = v___x_1617_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1615_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5___boxed(lean_object* v_sz_1623_, lean_object* v_i_1624_, lean_object* v_bs_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
size_t v_sz_boxed_1632_; size_t v_i_boxed_1633_; lean_object* v_res_1634_; 
v_sz_boxed_1632_ = lean_unbox_usize(v_sz_1623_);
lean_dec(v_sz_1623_);
v_i_boxed_1633_ = lean_unbox_usize(v_i_1624_);
lean_dec(v_i_1624_);
v_res_1634_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(v_sz_boxed_1632_, v_i_boxed_1633_, v_bs_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec(v___y_1626_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2___boxed(lean_object* v_x_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(v_x_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
lean_dec(v___y_1636_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(lean_object* v_t_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v_root_1650_; lean_object* v_tail_1651_; lean_object* v_size_1652_; size_t v_shift_1653_; lean_object* v_tailOff_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1690_; 
v_root_1650_ = lean_ctor_get(v_t_1643_, 0);
v_tail_1651_ = lean_ctor_get(v_t_1643_, 1);
v_size_1652_ = lean_ctor_get(v_t_1643_, 2);
v_shift_1653_ = lean_ctor_get_usize(v_t_1643_, 4);
v_tailOff_1654_ = lean_ctor_get(v_t_1643_, 3);
v_isSharedCheck_1690_ = !lean_is_exclusive(v_t_1643_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1656_ = v_t_1643_;
v_isShared_1657_ = v_isSharedCheck_1690_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_tailOff_1654_);
lean_inc(v_size_1652_);
lean_inc(v_tail_1651_);
lean_inc(v_root_1650_);
lean_dec(v_t_1643_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1690_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1658_; 
v___x_1658_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(v_root_1650_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; size_t v_sz_1660_; size_t v___x_1661_; lean_object* v___x_1662_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_a_1659_);
lean_dec_ref_known(v___x_1658_, 1);
v_sz_1660_ = lean_array_size(v_tail_1651_);
v___x_1661_ = ((size_t)0ULL);
v___x_1662_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_1660_, v___x_1661_, v_tail_1651_, v___y_1644_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1673_; 
v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1665_ = v___x_1662_;
v_isShared_1666_ = v_isSharedCheck_1673_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1662_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1673_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1668_; 
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 1, v_a_1663_);
lean_ctor_set(v___x_1656_, 0, v_a_1659_);
v___x_1668_ = v___x_1656_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_a_1659_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v_a_1663_);
lean_ctor_set(v_reuseFailAlloc_1672_, 2, v_size_1652_);
lean_ctor_set(v_reuseFailAlloc_1672_, 3, v_tailOff_1654_);
lean_ctor_set_usize(v_reuseFailAlloc_1672_, 4, v_shift_1653_);
v___x_1668_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
lean_object* v___x_1670_; 
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 0, v___x_1668_);
v___x_1670_ = v___x_1665_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1668_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
else
{
lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1681_; 
lean_dec(v_a_1659_);
lean_del_object(v___x_1656_);
lean_dec(v_tailOff_1654_);
lean_dec(v_size_1652_);
v_a_1674_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1676_ = v___x_1662_;
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_dec(v___x_1662_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1679_; 
if (v_isShared_1677_ == 0)
{
v___x_1679_ = v___x_1676_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_a_1674_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
}
else
{
lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1689_; 
lean_del_object(v___x_1656_);
lean_dec(v_tailOff_1654_);
lean_dec(v_size_1652_);
lean_dec_ref(v_tail_1651_);
v_a_1682_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1684_ = v___x_1658_;
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1658_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1687_; 
if (v_isShared_1685_ == 0)
{
v___x_1687_ = v___x_1684_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_a_1682_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1___boxed(lean_object* v_t_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(v_t_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v___y_1692_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesLCtx(lean_object* v_ctx_1699_, lean_object* v_targetUses_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_){
_start:
{
lean_object* v_decls_1706_; lean_object* v_fvarIdToDecl_1707_; lean_object* v_auxDeclToFullName_1708_; lean_object* v_size_1709_; lean_object* v_decls_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v_decls_1706_ = lean_ctor_get(v_ctx_1699_, 1);
lean_inc_ref(v_decls_1706_);
v_fvarIdToDecl_1707_ = lean_ctor_get(v_ctx_1699_, 0);
lean_inc_ref(v_fvarIdToDecl_1707_);
v_auxDeclToFullName_1708_ = lean_ctor_get(v_ctx_1699_, 2);
lean_inc(v_auxDeclToFullName_1708_);
v_size_1709_ = lean_ctor_get(v_decls_1706_, 2);
v_decls_1710_ = lean_mk_empty_array_with_capacity(v_size_1709_);
v___x_1711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1711_, 0, v_decls_1710_);
lean_ctor_set(v___x_1711_, 1, v_targetUses_1700_);
v___x_1712_ = l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(v_ctx_1699_, v___x_1711_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_object* v_a_1713_; lean_object* v_fst_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
lean_inc(v_a_1713_);
lean_dec_ref_known(v___x_1712_, 1);
v_fst_1714_ = lean_ctor_get(v_a_1713_, 0);
lean_inc(v_fst_1714_);
lean_dec(v_a_1713_);
v___x_1715_ = lean_st_mk_ref(v_fst_1714_);
v___x_1716_ = l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(v_decls_1706_, v___x_1715_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1726_; 
v_a_1717_ = lean_ctor_get(v___x_1716_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1719_ = v___x_1716_;
v_isShared_1720_ = v_isSharedCheck_1726_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1716_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1726_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1724_; 
v___x_1721_ = lean_st_ref_get(v___x_1715_);
lean_dec(v___x_1715_);
lean_dec(v___x_1721_);
v___x_1722_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1722_, 0, v_fvarIdToDecl_1707_);
lean_ctor_set(v___x_1722_, 1, v_a_1717_);
lean_ctor_set(v___x_1722_, 2, v_auxDeclToFullName_1708_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 0, v___x_1722_);
v___x_1724_ = v___x_1719_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1722_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
else
{
lean_object* v_a_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1734_; 
lean_dec(v___x_1715_);
lean_dec(v_auxDeclToFullName_1708_);
lean_dec_ref(v_fvarIdToDecl_1707_);
v_a_1727_ = lean_ctor_get(v___x_1716_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1729_ = v___x_1716_;
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_a_1727_);
lean_dec(v___x_1716_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1732_; 
if (v_isShared_1730_ == 0)
{
v___x_1732_ = v___x_1729_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_a_1727_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
}
else
{
lean_object* v_a_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1742_; 
lean_dec(v_auxDeclToFullName_1708_);
lean_dec_ref(v_fvarIdToDecl_1707_);
lean_dec_ref(v_decls_1706_);
v_a_1735_ = lean_ctor_get(v___x_1712_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1737_ = v___x_1712_;
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_a_1735_);
lean_dec(v___x_1712_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1740_; 
if (v_isShared_1738_ == 0)
{
v___x_1740_ = v___x_1737_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_a_1735_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesLCtx___boxed(lean_object* v_ctx_1743_, lean_object* v_targetUses_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Lean_Elab_Tactic_Do_countUsesLCtx(v_ctx_1743_, v_targetUses_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_);
lean_dec(v_a_1748_);
lean_dec_ref(v_a_1747_);
lean_dec(v_a_1746_);
lean_dec_ref(v_a_1745_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3(size_t v_sz_1751_, size_t v_i_1752_, lean_object* v_bs_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v___x_1760_; 
v___x_1760_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_1751_, v_i_1752_, v_bs_1753_, v___y_1754_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___boxed(lean_object* v_sz_1761_, lean_object* v_i_1762_, lean_object* v_bs_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
size_t v_sz_boxed_1770_; size_t v_i_boxed_1771_; lean_object* v_res_1772_; 
v_sz_boxed_1770_ = lean_unbox_usize(v_sz_1761_);
lean_dec(v_sz_1761_);
v_i_boxed_1771_ = lean_unbox_usize(v_i_1762_);
lean_dec(v_i_1762_);
v_res_1772_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3(v_sz_boxed_1770_, v_i_boxed_1771_, v_bs_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
return v_res_1772_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_doNotDup(uint8_t v_u_1773_, lean_object* v_rhs_1774_, uint8_t v_elimTrivial_1775_){
_start:
{
uint8_t v___x_1776_; uint8_t v___x_1777_; 
v___x_1776_ = 2;
v___x_1777_ = l_Lean_Elab_Tactic_Do_instBEqUses_beq(v_u_1773_, v___x_1776_);
if (v___x_1777_ == 0)
{
return v___x_1777_;
}
else
{
if (v_elimTrivial_1775_ == 0)
{
return v___x_1777_;
}
else
{
uint8_t v___x_1778_; 
v___x_1778_ = l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup(v_rhs_1774_);
if (v___x_1778_ == 0)
{
return v___x_1777_;
}
else
{
uint8_t v___x_1779_; 
v___x_1779_ = 0;
return v___x_1779_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_doNotDup___boxed(lean_object* v_u_1780_, lean_object* v_rhs_1781_, lean_object* v_elimTrivial_1782_){
_start:
{
uint8_t v_u_boxed_1783_; uint8_t v_elimTrivial_boxed_1784_; uint8_t v_res_1785_; lean_object* v_r_1786_; 
v_u_boxed_1783_ = lean_unbox(v_u_1780_);
v_elimTrivial_boxed_1784_ = lean_unbox(v_elimTrivial_1782_);
v_res_1785_ = l_Lean_Elab_Tactic_Do_doNotDup(v_u_boxed_1783_, v_rhs_1781_, v_elimTrivial_boxed_1784_);
lean_dec_ref(v_rhs_1781_);
v_r_1786_ = lean_box(v_res_1785_);
return v_r_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0(uint8_t v_elimTrivial_1789_, lean_object* v_e_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_){
_start:
{
if (lean_obj_tag(v_e_1790_) == 8)
{
lean_object* v_type_1797_; 
v_type_1797_ = lean_ctor_get(v_e_1790_, 1);
if (lean_obj_tag(v_type_1797_) == 10)
{
lean_object* v_value_1798_; lean_object* v_body_1799_; lean_object* v_data_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; uint8_t v_uses_1804_; uint8_t v___x_1805_; 
v_value_1798_ = lean_ctor_get(v_e_1790_, 2);
v_body_1799_ = lean_ctor_get(v_e_1790_, 3);
v_data_1800_ = lean_ctor_get(v_type_1797_, 0);
v___x_1801_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_1802_ = lean_unsigned_to_nat(2u);
v___x_1803_ = l_Lean_KVMap_getNat(v_data_1800_, v___x_1801_, v___x_1802_);
v_uses_1804_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_1803_);
lean_dec(v___x_1803_);
v___x_1805_ = l_Lean_Elab_Tactic_Do_doNotDup(v_uses_1804_, v_value_1798_, v_elimTrivial_1789_);
if (v___x_1805_ == 0)
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1806_ = lean_expr_instantiate1(v_body_1799_, v_value_1798_);
v___x_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1806_);
v___x_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1807_);
return v___x_1808_;
}
else
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1809_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0));
v___x_1810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1809_);
return v___x_1810_;
}
}
else
{
lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1811_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0));
v___x_1812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1811_);
return v___x_1812_;
}
}
else
{
lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1813_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0));
v___x_1814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1813_);
return v___x_1814_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___boxed(lean_object* v_elimTrivial_1815_, lean_object* v_e_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
uint8_t v_elimTrivial_boxed_1823_; lean_object* v_res_1824_; 
v_elimTrivial_boxed_1823_ = lean_unbox(v_elimTrivial_1815_);
v_res_1824_ = l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0(v_elimTrivial_boxed_1823_, v_e_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec_ref(v_e_1816_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1(lean_object* v_e_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1832_, 0, v_e_1825_);
v___x_1833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1832_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1___boxed(lean_object* v_e_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1(v_e_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
lean_dec(v___y_1835_);
return v_res_1841_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1847_ = l_Lean_maxRecDepthErrorMessage;
v___x_1848_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1847_);
return v___x_1848_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4(void){
_start:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1849_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3);
v___x_1850_ = l_Lean_MessageData_ofFormat(v___x_1849_);
return v___x_1850_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1851_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4);
v___x_1852_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2));
v___x_1853_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1852_);
lean_ctor_set(v___x_1853_, 1, v___x_1851_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(lean_object* v_ref_1854_){
_start:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1856_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5);
v___x_1857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1857_, 0, v_ref_1854_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
v___x_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___boxed(lean_object* v_ref_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_1859_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(lean_object* v_x_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
lean_object* v___y_1871_; lean_object* v_fileName_1880_; lean_object* v_fileMap_1881_; lean_object* v_options_1882_; lean_object* v_currRecDepth_1883_; lean_object* v_maxRecDepth_1884_; lean_object* v_ref_1885_; lean_object* v_currNamespace_1886_; lean_object* v_openDecls_1887_; lean_object* v_initHeartbeats_1888_; lean_object* v_maxHeartbeats_1889_; lean_object* v_quotContext_1890_; lean_object* v_currMacroScope_1891_; uint8_t v_diag_1892_; lean_object* v_cancelTk_x3f_1893_; uint8_t v_suppressElabErrors_1894_; lean_object* v_inheritedTraceOptions_1895_; lean_object* v___x_1901_; uint8_t v___x_1902_; 
v_fileName_1880_ = lean_ctor_get(v___y_1867_, 0);
v_fileMap_1881_ = lean_ctor_get(v___y_1867_, 1);
v_options_1882_ = lean_ctor_get(v___y_1867_, 2);
v_currRecDepth_1883_ = lean_ctor_get(v___y_1867_, 3);
v_maxRecDepth_1884_ = lean_ctor_get(v___y_1867_, 4);
v_ref_1885_ = lean_ctor_get(v___y_1867_, 5);
v_currNamespace_1886_ = lean_ctor_get(v___y_1867_, 6);
v_openDecls_1887_ = lean_ctor_get(v___y_1867_, 7);
v_initHeartbeats_1888_ = lean_ctor_get(v___y_1867_, 8);
v_maxHeartbeats_1889_ = lean_ctor_get(v___y_1867_, 9);
v_quotContext_1890_ = lean_ctor_get(v___y_1867_, 10);
v_currMacroScope_1891_ = lean_ctor_get(v___y_1867_, 11);
v_diag_1892_ = lean_ctor_get_uint8(v___y_1867_, sizeof(void*)*14);
v_cancelTk_x3f_1893_ = lean_ctor_get(v___y_1867_, 12);
v_suppressElabErrors_1894_ = lean_ctor_get_uint8(v___y_1867_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1895_ = lean_ctor_get(v___y_1867_, 13);
v___x_1901_ = lean_unsigned_to_nat(0u);
v___x_1902_ = lean_nat_dec_eq(v_maxRecDepth_1884_, v___x_1901_);
if (v___x_1902_ == 0)
{
uint8_t v___x_1903_; 
v___x_1903_ = lean_nat_dec_eq(v_currRecDepth_1883_, v_maxRecDepth_1884_);
if (v___x_1903_ == 0)
{
goto v___jp_1896_;
}
else
{
lean_object* v___x_1904_; 
lean_dec_ref(v_x_1862_);
lean_inc(v_ref_1885_);
v___x_1904_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_1885_);
v___y_1871_ = v___x_1904_;
goto v___jp_1870_;
}
}
else
{
goto v___jp_1896_;
}
v___jp_1870_:
{
if (lean_obj_tag(v___y_1871_) == 0)
{
return v___y_1871_;
}
else
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1879_; 
v_a_1872_ = lean_ctor_get(v___y_1871_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___y_1871_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1874_ = v___y_1871_;
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___y_1871_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1877_; 
if (v_isShared_1875_ == 0)
{
v___x_1877_ = v___x_1874_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_a_1872_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
}
v___jp_1896_:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1897_ = lean_unsigned_to_nat(1u);
v___x_1898_ = lean_nat_add(v_currRecDepth_1883_, v___x_1897_);
lean_inc_ref(v_inheritedTraceOptions_1895_);
lean_inc(v_cancelTk_x3f_1893_);
lean_inc(v_currMacroScope_1891_);
lean_inc(v_quotContext_1890_);
lean_inc(v_maxHeartbeats_1889_);
lean_inc(v_initHeartbeats_1888_);
lean_inc(v_openDecls_1887_);
lean_inc(v_currNamespace_1886_);
lean_inc(v_ref_1885_);
lean_inc(v_maxRecDepth_1884_);
lean_inc_ref(v_options_1882_);
lean_inc_ref(v_fileMap_1881_);
lean_inc_ref(v_fileName_1880_);
v___x_1899_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1899_, 0, v_fileName_1880_);
lean_ctor_set(v___x_1899_, 1, v_fileMap_1881_);
lean_ctor_set(v___x_1899_, 2, v_options_1882_);
lean_ctor_set(v___x_1899_, 3, v___x_1898_);
lean_ctor_set(v___x_1899_, 4, v_maxRecDepth_1884_);
lean_ctor_set(v___x_1899_, 5, v_ref_1885_);
lean_ctor_set(v___x_1899_, 6, v_currNamespace_1886_);
lean_ctor_set(v___x_1899_, 7, v_openDecls_1887_);
lean_ctor_set(v___x_1899_, 8, v_initHeartbeats_1888_);
lean_ctor_set(v___x_1899_, 9, v_maxHeartbeats_1889_);
lean_ctor_set(v___x_1899_, 10, v_quotContext_1890_);
lean_ctor_set(v___x_1899_, 11, v_currMacroScope_1891_);
lean_ctor_set(v___x_1899_, 12, v_cancelTk_x3f_1893_);
lean_ctor_set(v___x_1899_, 13, v_inheritedTraceOptions_1895_);
lean_ctor_set_uint8(v___x_1899_, sizeof(void*)*14, v_diag_1892_);
lean_ctor_set_uint8(v___x_1899_, sizeof(void*)*14 + 1, v_suppressElabErrors_1894_);
lean_inc(v___y_1868_);
lean_inc(v___y_1866_);
lean_inc_ref(v___y_1865_);
lean_inc(v___y_1864_);
lean_inc(v___y_1863_);
v___x_1900_ = lean_apply_7(v_x_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___x_1899_, v___y_1868_, lean_box(0));
v___y_1871_ = v___x_1900_;
goto v___jp_1870_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg___boxed(lean_object* v_x_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v_x_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec(v___y_1907_);
lean_dec(v___y_1906_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(lean_object* v_a_1914_, lean_object* v_x_1915_){
_start:
{
if (lean_obj_tag(v_x_1915_) == 0)
{
lean_object* v___x_1916_; 
v___x_1916_ = lean_box(0);
return v___x_1916_;
}
else
{
lean_object* v_key_1917_; lean_object* v_value_1918_; lean_object* v_tail_1919_; uint8_t v___x_1920_; 
v_key_1917_ = lean_ctor_get(v_x_1915_, 0);
v_value_1918_ = lean_ctor_get(v_x_1915_, 1);
v_tail_1919_ = lean_ctor_get(v_x_1915_, 2);
v___x_1920_ = l_Lean_ExprStructEq_beq(v_key_1917_, v_a_1914_);
if (v___x_1920_ == 0)
{
v_x_1915_ = v_tail_1919_;
goto _start;
}
else
{
lean_object* v___x_1922_; 
lean_inc(v_value_1918_);
v___x_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1922_, 0, v_value_1918_);
return v___x_1922_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg___boxed(lean_object* v_a_1923_, lean_object* v_x_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(v_a_1923_, v_x_1924_);
lean_dec(v_x_1924_);
lean_dec_ref(v_a_1923_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(lean_object* v_m_1926_, lean_object* v_a_1927_){
_start:
{
lean_object* v_buckets_1928_; lean_object* v___x_1929_; uint64_t v___x_1930_; uint64_t v___x_1931_; uint64_t v___x_1932_; uint64_t v_fold_1933_; uint64_t v___x_1934_; uint64_t v___x_1935_; uint64_t v___x_1936_; size_t v___x_1937_; size_t v___x_1938_; size_t v___x_1939_; size_t v___x_1940_; size_t v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
v_buckets_1928_ = lean_ctor_get(v_m_1926_, 1);
v___x_1929_ = lean_array_get_size(v_buckets_1928_);
v___x_1930_ = l_Lean_ExprStructEq_hash(v_a_1927_);
v___x_1931_ = 32ULL;
v___x_1932_ = lean_uint64_shift_right(v___x_1930_, v___x_1931_);
v_fold_1933_ = lean_uint64_xor(v___x_1930_, v___x_1932_);
v___x_1934_ = 16ULL;
v___x_1935_ = lean_uint64_shift_right(v_fold_1933_, v___x_1934_);
v___x_1936_ = lean_uint64_xor(v_fold_1933_, v___x_1935_);
v___x_1937_ = lean_uint64_to_usize(v___x_1936_);
v___x_1938_ = lean_usize_of_nat(v___x_1929_);
v___x_1939_ = ((size_t)1ULL);
v___x_1940_ = lean_usize_sub(v___x_1938_, v___x_1939_);
v___x_1941_ = lean_usize_land(v___x_1937_, v___x_1940_);
v___x_1942_ = lean_array_uget_borrowed(v_buckets_1928_, v___x_1941_);
v___x_1943_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(v_a_1927_, v___x_1942_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_m_1944_, lean_object* v_a_1945_){
_start:
{
lean_object* v_res_1946_; 
v_res_1946_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(v_m_1944_, v_a_1945_);
lean_dec_ref(v_a_1945_);
lean_dec_ref(v_m_1944_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(lean_object* v_k_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v_b_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v___x_1956_; 
lean_inc(v___y_1954_);
lean_inc_ref(v___y_1953_);
lean_inc(v___y_1952_);
lean_inc_ref(v___y_1951_);
lean_inc(v___y_1949_);
lean_inc(v___y_1948_);
v___x_1956_ = lean_apply_8(v_k_1947_, v_b_1950_, v___y_1948_, v___y_1949_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, lean_box(0));
return v___x_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed(lean_object* v_k_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v_b_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
lean_object* v_res_1966_; 
v_res_1966_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(v_k_1957_, v___y_1958_, v___y_1959_, v_b_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec(v___y_1959_);
lean_dec(v___y_1958_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(lean_object* v_name_1967_, lean_object* v_type_1968_, lean_object* v_val_1969_, lean_object* v_k_1970_, uint8_t v_nondep_1971_, uint8_t v_kind_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v___f_1980_; lean_object* v___x_1981_; 
lean_inc(v___y_1974_);
lean_inc(v___y_1973_);
v___f_1980_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1980_, 0, v_k_1970_);
lean_closure_set(v___f_1980_, 1, v___y_1973_);
lean_closure_set(v___f_1980_, 2, v___y_1974_);
v___x_1981_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1967_, v_type_1968_, v_val_1969_, v___f_1980_, v_nondep_1971_, v_kind_1972_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
if (lean_obj_tag(v___x_1981_) == 0)
{
return v___x_1981_;
}
else
{
lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1989_; 
v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1984_ = v___x_1981_;
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v___x_1981_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1987_; 
if (v_isShared_1985_ == 0)
{
v___x_1987_ = v___x_1984_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_a_1982_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg___boxed(lean_object* v_name_1990_, lean_object* v_type_1991_, lean_object* v_val_1992_, lean_object* v_k_1993_, lean_object* v_nondep_1994_, lean_object* v_kind_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
uint8_t v_nondep_boxed_2003_; uint8_t v_kind_boxed_2004_; lean_object* v_res_2005_; 
v_nondep_boxed_2003_ = lean_unbox(v_nondep_1994_);
v_kind_boxed_2004_ = lean_unbox(v_kind_1995_);
v_res_2005_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_name_1990_, v_type_1991_, v_val_1992_, v_k_1993_, v_nondep_boxed_2003_, v_kind_boxed_2004_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1997_);
lean_dec(v___y_1996_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_name_2006_, uint8_t v_bi_2007_, lean_object* v_type_2008_, lean_object* v_k_2009_, uint8_t v_kind_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v___f_2018_; lean_object* v___x_2019_; 
lean_inc(v___y_2012_);
lean_inc(v___y_2011_);
v___f_2018_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2018_, 0, v_k_2009_);
lean_closure_set(v___f_2018_, 1, v___y_2011_);
lean_closure_set(v___f_2018_, 2, v___y_2012_);
v___x_2019_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2006_, v_bi_2007_, v_type_2008_, v___f_2018_, v_kind_2010_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
if (lean_obj_tag(v___x_2019_) == 0)
{
return v___x_2019_;
}
else
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2027_; 
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2022_ = v___x_2019_;
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_2019_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2023_ == 0)
{
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_a_2020_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_name_2028_, lean_object* v_bi_2029_, lean_object* v_type_2030_, lean_object* v_k_2031_, lean_object* v_kind_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
uint8_t v_bi_boxed_2040_; uint8_t v_kind_boxed_2041_; lean_object* v_res_2042_; 
v_bi_boxed_2040_ = lean_unbox(v_bi_2029_);
v_kind_boxed_2041_ = lean_unbox(v_kind_2032_);
v_res_2042_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_name_2028_, v_bi_boxed_2040_, v_type_2030_, v_k_2031_, v_kind_boxed_2041_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
lean_dec(v___y_2036_);
lean_dec_ref(v___y_2035_);
lean_dec(v___y_2034_);
lean_dec(v___y_2033_);
return v_res_2042_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2(lean_object* v___x_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
lean_object* v___x_2050_; 
v___x_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2043_);
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2___boxed(lean_object* v___x_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
lean_object* v_res_2058_; 
v_res_2058_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2(v___x_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
lean_dec(v___y_2054_);
lean_dec_ref(v___y_2053_);
lean_dec(v___y_2052_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_2059_, lean_object* v_x_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2067_ = lean_apply_1(v_x_2060_, lean_box(0));
v___x_2068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2067_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_2069_, lean_object* v_x_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_){
_start:
{
lean_object* v_res_2077_; 
v_res_2077_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(v_00_u03b1_2069_, v_x_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
lean_dec(v___y_2071_);
return v_res_2077_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(lean_object* v_x_2078_, lean_object* v_x_2079_){
_start:
{
if (lean_obj_tag(v_x_2079_) == 0)
{
return v_x_2078_;
}
else
{
lean_object* v_key_2080_; lean_object* v_value_2081_; lean_object* v_tail_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2105_; 
v_key_2080_ = lean_ctor_get(v_x_2079_, 0);
v_value_2081_ = lean_ctor_get(v_x_2079_, 1);
v_tail_2082_ = lean_ctor_get(v_x_2079_, 2);
v_isSharedCheck_2105_ = !lean_is_exclusive(v_x_2079_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2084_ = v_x_2079_;
v_isShared_2085_ = v_isSharedCheck_2105_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_tail_2082_);
lean_inc(v_value_2081_);
lean_inc(v_key_2080_);
lean_dec(v_x_2079_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2105_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2086_; uint64_t v___x_2087_; uint64_t v___x_2088_; uint64_t v___x_2089_; uint64_t v_fold_2090_; uint64_t v___x_2091_; uint64_t v___x_2092_; uint64_t v___x_2093_; size_t v___x_2094_; size_t v___x_2095_; size_t v___x_2096_; size_t v___x_2097_; size_t v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2101_; 
v___x_2086_ = lean_array_get_size(v_x_2078_);
v___x_2087_ = l_Lean_ExprStructEq_hash(v_key_2080_);
v___x_2088_ = 32ULL;
v___x_2089_ = lean_uint64_shift_right(v___x_2087_, v___x_2088_);
v_fold_2090_ = lean_uint64_xor(v___x_2087_, v___x_2089_);
v___x_2091_ = 16ULL;
v___x_2092_ = lean_uint64_shift_right(v_fold_2090_, v___x_2091_);
v___x_2093_ = lean_uint64_xor(v_fold_2090_, v___x_2092_);
v___x_2094_ = lean_uint64_to_usize(v___x_2093_);
v___x_2095_ = lean_usize_of_nat(v___x_2086_);
v___x_2096_ = ((size_t)1ULL);
v___x_2097_ = lean_usize_sub(v___x_2095_, v___x_2096_);
v___x_2098_ = lean_usize_land(v___x_2094_, v___x_2097_);
v___x_2099_ = lean_array_uget_borrowed(v_x_2078_, v___x_2098_);
lean_inc(v___x_2099_);
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 2, v___x_2099_);
v___x_2101_ = v___x_2084_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_key_2080_);
lean_ctor_set(v_reuseFailAlloc_2104_, 1, v_value_2081_);
lean_ctor_set(v_reuseFailAlloc_2104_, 2, v___x_2099_);
v___x_2101_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
lean_object* v___x_2102_; 
v___x_2102_ = lean_array_uset(v_x_2078_, v___x_2098_, v___x_2101_);
v_x_2078_ = v___x_2102_;
v_x_2079_ = v_tail_2082_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(lean_object* v_i_2106_, lean_object* v_source_2107_, lean_object* v_target_2108_){
_start:
{
lean_object* v___x_2109_; uint8_t v___x_2110_; 
v___x_2109_ = lean_array_get_size(v_source_2107_);
v___x_2110_ = lean_nat_dec_lt(v_i_2106_, v___x_2109_);
if (v___x_2110_ == 0)
{
lean_dec_ref(v_source_2107_);
lean_dec(v_i_2106_);
return v_target_2108_;
}
else
{
lean_object* v_es_2111_; lean_object* v___x_2112_; lean_object* v_source_2113_; lean_object* v_target_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v_es_2111_ = lean_array_fget(v_source_2107_, v_i_2106_);
v___x_2112_ = lean_box(0);
v_source_2113_ = lean_array_fset(v_source_2107_, v_i_2106_, v___x_2112_);
v_target_2114_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_target_2108_, v_es_2111_);
v___x_2115_ = lean_unsigned_to_nat(1u);
v___x_2116_ = lean_nat_add(v_i_2106_, v___x_2115_);
lean_dec(v_i_2106_);
v_i_2106_ = v___x_2116_;
v_source_2107_ = v_source_2113_;
v_target_2108_ = v_target_2114_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(lean_object* v_data_2118_){
_start:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v_nbuckets_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2119_ = lean_array_get_size(v_data_2118_);
v___x_2120_ = lean_unsigned_to_nat(2u);
v_nbuckets_2121_ = lean_nat_mul(v___x_2119_, v___x_2120_);
v___x_2122_ = lean_unsigned_to_nat(0u);
v___x_2123_ = lean_box(0);
v___x_2124_ = lean_mk_array(v_nbuckets_2121_, v___x_2123_);
v___x_2125_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v___x_2122_, v_data_2118_, v___x_2124_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(lean_object* v_a_2126_, lean_object* v_b_2127_, lean_object* v_x_2128_){
_start:
{
if (lean_obj_tag(v_x_2128_) == 0)
{
lean_dec(v_b_2127_);
lean_dec_ref(v_a_2126_);
return v_x_2128_;
}
else
{
lean_object* v_key_2129_; lean_object* v_value_2130_; lean_object* v_tail_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2143_; 
v_key_2129_ = lean_ctor_get(v_x_2128_, 0);
v_value_2130_ = lean_ctor_get(v_x_2128_, 1);
v_tail_2131_ = lean_ctor_get(v_x_2128_, 2);
v_isSharedCheck_2143_ = !lean_is_exclusive(v_x_2128_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2133_ = v_x_2128_;
v_isShared_2134_ = v_isSharedCheck_2143_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_tail_2131_);
lean_inc(v_value_2130_);
lean_inc(v_key_2129_);
lean_dec(v_x_2128_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2143_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
uint8_t v___x_2135_; 
v___x_2135_ = l_Lean_ExprStructEq_beq(v_key_2129_, v_a_2126_);
if (v___x_2135_ == 0)
{
lean_object* v___x_2136_; lean_object* v___x_2138_; 
v___x_2136_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(v_a_2126_, v_b_2127_, v_tail_2131_);
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 2, v___x_2136_);
v___x_2138_ = v___x_2133_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_key_2129_);
lean_ctor_set(v_reuseFailAlloc_2139_, 1, v_value_2130_);
lean_ctor_set(v_reuseFailAlloc_2139_, 2, v___x_2136_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
else
{
lean_object* v___x_2141_; 
lean_dec(v_value_2130_);
lean_dec(v_key_2129_);
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 1, v_b_2127_);
lean_ctor_set(v___x_2133_, 0, v_a_2126_);
v___x_2141_ = v___x_2133_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_a_2126_);
lean_ctor_set(v_reuseFailAlloc_2142_, 1, v_b_2127_);
lean_ctor_set(v_reuseFailAlloc_2142_, 2, v_tail_2131_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(lean_object* v_a_2144_, lean_object* v_x_2145_){
_start:
{
if (lean_obj_tag(v_x_2145_) == 0)
{
uint8_t v___x_2146_; 
v___x_2146_ = 0;
return v___x_2146_;
}
else
{
lean_object* v_key_2147_; lean_object* v_tail_2148_; uint8_t v___x_2149_; 
v_key_2147_ = lean_ctor_get(v_x_2145_, 0);
v_tail_2148_ = lean_ctor_get(v_x_2145_, 2);
v___x_2149_ = l_Lean_ExprStructEq_beq(v_key_2147_, v_a_2144_);
if (v___x_2149_ == 0)
{
v_x_2145_ = v_tail_2148_;
goto _start;
}
else
{
return v___x_2149_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg___boxed(lean_object* v_a_2151_, lean_object* v_x_2152_){
_start:
{
uint8_t v_res_2153_; lean_object* v_r_2154_; 
v_res_2153_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_a_2151_, v_x_2152_);
lean_dec(v_x_2152_);
lean_dec_ref(v_a_2151_);
v_r_2154_ = lean_box(v_res_2153_);
return v_r_2154_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(lean_object* v_m_2155_, lean_object* v_a_2156_, lean_object* v_b_2157_){
_start:
{
lean_object* v_size_2158_; lean_object* v_buckets_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2202_; 
v_size_2158_ = lean_ctor_get(v_m_2155_, 0);
v_buckets_2159_ = lean_ctor_get(v_m_2155_, 1);
v_isSharedCheck_2202_ = !lean_is_exclusive(v_m_2155_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2161_ = v_m_2155_;
v_isShared_2162_ = v_isSharedCheck_2202_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_buckets_2159_);
lean_inc(v_size_2158_);
lean_dec(v_m_2155_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2202_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2163_; uint64_t v___x_2164_; uint64_t v___x_2165_; uint64_t v___x_2166_; uint64_t v_fold_2167_; uint64_t v___x_2168_; uint64_t v___x_2169_; uint64_t v___x_2170_; size_t v___x_2171_; size_t v___x_2172_; size_t v___x_2173_; size_t v___x_2174_; size_t v___x_2175_; lean_object* v_bkt_2176_; uint8_t v___x_2177_; 
v___x_2163_ = lean_array_get_size(v_buckets_2159_);
v___x_2164_ = l_Lean_ExprStructEq_hash(v_a_2156_);
v___x_2165_ = 32ULL;
v___x_2166_ = lean_uint64_shift_right(v___x_2164_, v___x_2165_);
v_fold_2167_ = lean_uint64_xor(v___x_2164_, v___x_2166_);
v___x_2168_ = 16ULL;
v___x_2169_ = lean_uint64_shift_right(v_fold_2167_, v___x_2168_);
v___x_2170_ = lean_uint64_xor(v_fold_2167_, v___x_2169_);
v___x_2171_ = lean_uint64_to_usize(v___x_2170_);
v___x_2172_ = lean_usize_of_nat(v___x_2163_);
v___x_2173_ = ((size_t)1ULL);
v___x_2174_ = lean_usize_sub(v___x_2172_, v___x_2173_);
v___x_2175_ = lean_usize_land(v___x_2171_, v___x_2174_);
v_bkt_2176_ = lean_array_uget_borrowed(v_buckets_2159_, v___x_2175_);
v___x_2177_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_a_2156_, v_bkt_2176_);
if (v___x_2177_ == 0)
{
lean_object* v___x_2178_; lean_object* v_size_x27_2179_; lean_object* v___x_2180_; lean_object* v_buckets_x27_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; uint8_t v___x_2187_; 
v___x_2178_ = lean_unsigned_to_nat(1u);
v_size_x27_2179_ = lean_nat_add(v_size_2158_, v___x_2178_);
lean_dec(v_size_2158_);
lean_inc(v_bkt_2176_);
v___x_2180_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2180_, 0, v_a_2156_);
lean_ctor_set(v___x_2180_, 1, v_b_2157_);
lean_ctor_set(v___x_2180_, 2, v_bkt_2176_);
v_buckets_x27_2181_ = lean_array_uset(v_buckets_2159_, v___x_2175_, v___x_2180_);
v___x_2182_ = lean_unsigned_to_nat(4u);
v___x_2183_ = lean_nat_mul(v_size_x27_2179_, v___x_2182_);
v___x_2184_ = lean_unsigned_to_nat(3u);
v___x_2185_ = lean_nat_div(v___x_2183_, v___x_2184_);
lean_dec(v___x_2183_);
v___x_2186_ = lean_array_get_size(v_buckets_x27_2181_);
v___x_2187_ = lean_nat_dec_le(v___x_2185_, v___x_2186_);
lean_dec(v___x_2185_);
if (v___x_2187_ == 0)
{
lean_object* v_val_2188_; lean_object* v___x_2190_; 
v_val_2188_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(v_buckets_x27_2181_);
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 1, v_val_2188_);
lean_ctor_set(v___x_2161_, 0, v_size_x27_2179_);
v___x_2190_ = v___x_2161_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_size_x27_2179_);
lean_ctor_set(v_reuseFailAlloc_2191_, 1, v_val_2188_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
else
{
lean_object* v___x_2193_; 
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 1, v_buckets_x27_2181_);
lean_ctor_set(v___x_2161_, 0, v_size_x27_2179_);
v___x_2193_ = v___x_2161_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_size_x27_2179_);
lean_ctor_set(v_reuseFailAlloc_2194_, 1, v_buckets_x27_2181_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
else
{
lean_object* v___x_2195_; lean_object* v_buckets_x27_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2200_; 
lean_inc(v_bkt_2176_);
v___x_2195_ = lean_box(0);
v_buckets_x27_2196_ = lean_array_uset(v_buckets_2159_, v___x_2175_, v___x_2195_);
v___x_2197_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(v_a_2156_, v_b_2157_, v_bkt_2176_);
v___x_2198_ = lean_array_uset(v_buckets_x27_2196_, v___x_2175_, v___x_2197_);
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 1, v___x_2198_);
v___x_2200_ = v___x_2161_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_size_2158_);
lean_ctor_set(v_reuseFailAlloc_2201_, 1, v___x_2198_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2(lean_object* v_a_2203_, lean_object* v_e_2204_, lean_object* v_a_2205_){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2207_ = lean_st_ref_take(v_a_2203_);
v___x_2208_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(v___x_2207_, v_e_2204_, v_a_2205_);
v___x_2209_ = lean_st_ref_set(v_a_2203_, v___x_2208_);
v___x_2210_ = lean_box(0);
return v___x_2210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2___boxed(lean_object* v_a_2211_, lean_object* v_e_2212_, lean_object* v_a_2213_, lean_object* v___y_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2(v_a_2211_, v_e_2212_, v_a_2213_);
lean_dec(v_a_2211_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0(lean_object* v_fvars_2219_, lean_object* v_pre_2220_, lean_object* v_post_2221_, uint8_t v_usedLetOnly_2222_, uint8_t v_skipConstInApp_2223_, uint8_t v_skipInstances_2224_, lean_object* v_body_2225_, lean_object* v_x_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2234_ = lean_array_push(v_fvars_2219_, v_x_2226_);
v___x_2235_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(v_pre_2220_, v_post_2221_, v_usedLetOnly_2222_, v_skipConstInApp_2223_, v_skipInstances_2224_, v___x_2234_, v_body_2225_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0___boxed(lean_object* v_fvars_2236_, lean_object* v_pre_2237_, lean_object* v_post_2238_, lean_object* v_usedLetOnly_2239_, lean_object* v_skipConstInApp_2240_, lean_object* v_skipInstances_2241_, lean_object* v_body_2242_, lean_object* v_x_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_){
_start:
{
uint8_t v_usedLetOnly_boxed_2251_; uint8_t v_skipConstInApp_boxed_2252_; uint8_t v_skipInstances_boxed_2253_; lean_object* v_res_2254_; 
v_usedLetOnly_boxed_2251_ = lean_unbox(v_usedLetOnly_2239_);
v_skipConstInApp_boxed_2252_ = lean_unbox(v_skipConstInApp_2240_);
v_skipInstances_boxed_2253_ = lean_unbox(v_skipInstances_2241_);
v_res_2254_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0(v_fvars_2236_, v_pre_2237_, v_post_2238_, v_usedLetOnly_boxed_2251_, v_skipConstInApp_boxed_2252_, v_skipInstances_boxed_2253_, v_body_2242_, v_x_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec(v___y_2244_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(lean_object* v_pre_2255_, lean_object* v_post_2256_, uint8_t v_usedLetOnly_2257_, uint8_t v_skipConstInApp_2258_, uint8_t v_skipInstances_2259_, lean_object* v_e_2260_, lean_object* v_a_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
lean_object* v___x_2268_; 
lean_inc_ref(v_post_2256_);
lean_inc(v___y_2266_);
lean_inc_ref(v___y_2265_);
lean_inc(v___y_2264_);
lean_inc_ref(v___y_2263_);
lean_inc(v___y_2262_);
lean_inc_ref(v_e_2260_);
v___x_2268_ = lean_apply_7(v_post_2256_, v_e_2260_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, lean_box(0));
if (lean_obj_tag(v___x_2268_) == 0)
{
lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2287_; 
v_a_2269_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2271_ = v___x_2268_;
v_isShared_2272_ = v_isSharedCheck_2287_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_dec(v___x_2268_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2287_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
switch(lean_obj_tag(v_a_2269_))
{
case 0:
{
lean_object* v_e_2273_; lean_object* v___x_2275_; 
lean_dec_ref(v_e_2260_);
lean_dec_ref(v_post_2256_);
lean_dec_ref(v_pre_2255_);
v_e_2273_ = lean_ctor_get(v_a_2269_, 0);
lean_inc_ref(v_e_2273_);
lean_dec_ref_known(v_a_2269_, 1);
if (v_isShared_2272_ == 0)
{
lean_ctor_set(v___x_2271_, 0, v_e_2273_);
v___x_2275_ = v___x_2271_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_e_2273_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
case 1:
{
lean_object* v_e_2277_; lean_object* v___x_2278_; 
lean_del_object(v___x_2271_);
lean_dec_ref(v_e_2260_);
v_e_2277_ = lean_ctor_get(v_a_2269_, 0);
lean_inc_ref(v_e_2277_);
lean_dec_ref_known(v_a_2269_, 1);
v___x_2278_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2255_, v_post_2256_, v_usedLetOnly_2257_, v_skipConstInApp_2258_, v_skipInstances_2259_, v_e_2277_, v_a_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
return v___x_2278_;
}
default: 
{
lean_object* v_e_x3f_2279_; 
lean_dec_ref(v_post_2256_);
lean_dec_ref(v_pre_2255_);
v_e_x3f_2279_ = lean_ctor_get(v_a_2269_, 0);
lean_inc(v_e_x3f_2279_);
lean_dec_ref_known(v_a_2269_, 1);
if (lean_obj_tag(v_e_x3f_2279_) == 0)
{
lean_object* v___x_2281_; 
if (v_isShared_2272_ == 0)
{
lean_ctor_set(v___x_2271_, 0, v_e_2260_);
v___x_2281_ = v___x_2271_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_e_2260_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
else
{
lean_object* v_val_2283_; lean_object* v___x_2285_; 
lean_dec_ref(v_e_2260_);
v_val_2283_ = lean_ctor_get(v_e_x3f_2279_, 0);
lean_inc(v_val_2283_);
lean_dec_ref_known(v_e_x3f_2279_, 1);
if (v_isShared_2272_ == 0)
{
lean_ctor_set(v___x_2271_, 0, v_val_2283_);
v___x_2285_ = v___x_2271_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_val_2283_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
}
}
}
}
else
{
lean_object* v_a_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2295_; 
lean_dec_ref(v_e_2260_);
lean_dec_ref(v_post_2256_);
lean_dec_ref(v_pre_2255_);
v_a_2288_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2290_ = v___x_2268_;
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_a_2288_);
lean_dec(v___x_2268_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2293_; 
if (v_isShared_2291_ == 0)
{
v___x_2293_ = v___x_2290_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_a_2288_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(lean_object* v_pre_2296_, lean_object* v_post_2297_, uint8_t v_usedLetOnly_2298_, uint8_t v_skipConstInApp_2299_, uint8_t v_skipInstances_2300_, lean_object* v_fvars_2301_, lean_object* v_e_2302_, lean_object* v_a_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
if (lean_obj_tag(v_e_2302_) == 6)
{
lean_object* v_binderName_2310_; lean_object* v_binderType_2311_; lean_object* v_body_2312_; uint8_t v_binderInfo_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
v_binderName_2310_ = lean_ctor_get(v_e_2302_, 0);
lean_inc(v_binderName_2310_);
v_binderType_2311_ = lean_ctor_get(v_e_2302_, 1);
lean_inc_ref(v_binderType_2311_);
v_body_2312_ = lean_ctor_get(v_e_2302_, 2);
lean_inc_ref(v_body_2312_);
v_binderInfo_2313_ = lean_ctor_get_uint8(v_e_2302_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2302_, 3);
v___x_2314_ = lean_expr_instantiate_rev(v_binderType_2311_, v_fvars_2301_);
lean_dec_ref(v_binderType_2311_);
lean_inc_ref(v_post_2297_);
lean_inc_ref(v_pre_2296_);
v___x_2315_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2296_, v_post_2297_, v_usedLetOnly_2298_, v_skipConstInApp_2299_, v_skipInstances_2300_, v___x_2314_, v_a_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___f_2320_; uint8_t v___x_2321_; lean_object* v___x_2322_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_a_2316_);
lean_dec_ref_known(v___x_2315_, 1);
v___x_2317_ = lean_box(v_usedLetOnly_2298_);
v___x_2318_ = lean_box(v_skipConstInApp_2299_);
v___x_2319_ = lean_box(v_skipInstances_2300_);
v___f_2320_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0___boxed), 15, 7);
lean_closure_set(v___f_2320_, 0, v_fvars_2301_);
lean_closure_set(v___f_2320_, 1, v_pre_2296_);
lean_closure_set(v___f_2320_, 2, v_post_2297_);
lean_closure_set(v___f_2320_, 3, v___x_2317_);
lean_closure_set(v___f_2320_, 4, v___x_2318_);
lean_closure_set(v___f_2320_, 5, v___x_2319_);
lean_closure_set(v___f_2320_, 6, v_body_2312_);
v___x_2321_ = 0;
v___x_2322_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_2310_, v_binderInfo_2313_, v_a_2316_, v___f_2320_, v___x_2321_, v_a_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
return v___x_2322_;
}
else
{
lean_dec_ref(v_body_2312_);
lean_dec(v_binderName_2310_);
lean_dec_ref(v_fvars_2301_);
lean_dec_ref(v_post_2297_);
lean_dec_ref(v_pre_2296_);
return v___x_2315_;
}
}
else
{
lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2323_ = lean_expr_instantiate_rev(v_e_2302_, v_fvars_2301_);
lean_dec_ref(v_e_2302_);
lean_inc_ref(v_post_2297_);
lean_inc_ref(v_pre_2296_);
v___x_2324_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2296_, v_post_2297_, v_usedLetOnly_2298_, v_skipConstInApp_2299_, v_skipInstances_2300_, v___x_2323_, v_a_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_object* v_a_2325_; uint8_t v___x_2326_; uint8_t v___x_2327_; uint8_t v___x_2328_; lean_object* v___x_2329_; 
v_a_2325_ = lean_ctor_get(v___x_2324_, 0);
lean_inc(v_a_2325_);
lean_dec_ref_known(v___x_2324_, 1);
v___x_2326_ = 0;
v___x_2327_ = 1;
v___x_2328_ = 1;
v___x_2329_ = l_Lean_Meta_mkLambdaFVars(v_fvars_2301_, v_a_2325_, v___x_2326_, v_usedLetOnly_2298_, v___x_2326_, v___x_2327_, v___x_2328_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
lean_dec_ref(v_fvars_2301_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; lean_object* v___x_2331_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
lean_inc(v_a_2330_);
lean_dec_ref_known(v___x_2329_, 1);
v___x_2331_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2296_, v_post_2297_, v_usedLetOnly_2298_, v_skipConstInApp_2299_, v_skipInstances_2300_, v_a_2330_, v_a_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
return v___x_2331_;
}
else
{
lean_dec_ref(v_post_2297_);
lean_dec_ref(v_pre_2296_);
return v___x_2329_;
}
}
else
{
lean_dec_ref(v_fvars_2301_);
lean_dec_ref(v_post_2297_);
lean_dec_ref(v_pre_2296_);
return v___x_2324_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0(lean_object* v_fvars_2332_, lean_object* v_pre_2333_, lean_object* v_post_2334_, uint8_t v_usedLetOnly_2335_, uint8_t v_skipConstInApp_2336_, uint8_t v_skipInstances_2337_, lean_object* v_body_2338_, lean_object* v_x_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2347_ = lean_array_push(v_fvars_2332_, v_x_2339_);
v___x_2348_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(v_pre_2333_, v_post_2334_, v_usedLetOnly_2335_, v_skipConstInApp_2336_, v_skipInstances_2337_, v___x_2347_, v_body_2338_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0___boxed(lean_object* v_fvars_2349_, lean_object* v_pre_2350_, lean_object* v_post_2351_, lean_object* v_usedLetOnly_2352_, lean_object* v_skipConstInApp_2353_, lean_object* v_skipInstances_2354_, lean_object* v_body_2355_, lean_object* v_x_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
uint8_t v_usedLetOnly_boxed_2364_; uint8_t v_skipConstInApp_boxed_2365_; uint8_t v_skipInstances_boxed_2366_; lean_object* v_res_2367_; 
v_usedLetOnly_boxed_2364_ = lean_unbox(v_usedLetOnly_2352_);
v_skipConstInApp_boxed_2365_ = lean_unbox(v_skipConstInApp_2353_);
v_skipInstances_boxed_2366_ = lean_unbox(v_skipInstances_2354_);
v_res_2367_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0(v_fvars_2349_, v_pre_2350_, v_post_2351_, v_usedLetOnly_boxed_2364_, v_skipConstInApp_boxed_2365_, v_skipInstances_boxed_2366_, v_body_2355_, v_x_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
lean_dec(v___y_2358_);
lean_dec(v___y_2357_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(lean_object* v_pre_2368_, lean_object* v_post_2369_, uint8_t v_usedLetOnly_2370_, uint8_t v_skipConstInApp_2371_, uint8_t v_skipInstances_2372_, lean_object* v_fvars_2373_, lean_object* v_e_2374_, lean_object* v_a_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_){
_start:
{
if (lean_obj_tag(v_e_2374_) == 8)
{
lean_object* v_declName_2382_; lean_object* v_type_2383_; lean_object* v_value_2384_; lean_object* v_body_2385_; uint8_t v_nondep_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v_declName_2382_ = lean_ctor_get(v_e_2374_, 0);
lean_inc(v_declName_2382_);
v_type_2383_ = lean_ctor_get(v_e_2374_, 1);
lean_inc_ref(v_type_2383_);
v_value_2384_ = lean_ctor_get(v_e_2374_, 2);
lean_inc_ref(v_value_2384_);
v_body_2385_ = lean_ctor_get(v_e_2374_, 3);
lean_inc_ref(v_body_2385_);
v_nondep_2386_ = lean_ctor_get_uint8(v_e_2374_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2374_, 4);
v___x_2387_ = lean_expr_instantiate_rev(v_type_2383_, v_fvars_2373_);
lean_dec_ref(v_type_2383_);
lean_inc_ref(v_post_2369_);
lean_inc_ref(v_pre_2368_);
v___x_2388_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2368_, v_post_2369_, v_usedLetOnly_2370_, v_skipConstInApp_2371_, v_skipInstances_2372_, v___x_2387_, v_a_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_object* v_a_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
lean_inc(v_a_2389_);
lean_dec_ref_known(v___x_2388_, 1);
v___x_2390_ = lean_expr_instantiate_rev(v_value_2384_, v_fvars_2373_);
lean_dec_ref(v_value_2384_);
lean_inc_ref(v_post_2369_);
lean_inc_ref(v_pre_2368_);
v___x_2391_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2368_, v_post_2369_, v_usedLetOnly_2370_, v_skipConstInApp_2371_, v_skipInstances_2372_, v___x_2390_, v_a_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v_a_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___f_2396_; uint8_t v___x_2397_; lean_object* v___x_2398_; 
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
lean_inc(v_a_2392_);
lean_dec_ref_known(v___x_2391_, 1);
v___x_2393_ = lean_box(v_usedLetOnly_2370_);
v___x_2394_ = lean_box(v_skipConstInApp_2371_);
v___x_2395_ = lean_box(v_skipInstances_2372_);
v___f_2396_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0___boxed), 15, 7);
lean_closure_set(v___f_2396_, 0, v_fvars_2373_);
lean_closure_set(v___f_2396_, 1, v_pre_2368_);
lean_closure_set(v___f_2396_, 2, v_post_2369_);
lean_closure_set(v___f_2396_, 3, v___x_2393_);
lean_closure_set(v___f_2396_, 4, v___x_2394_);
lean_closure_set(v___f_2396_, 5, v___x_2395_);
lean_closure_set(v___f_2396_, 6, v_body_2385_);
v___x_2397_ = 0;
v___x_2398_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_declName_2382_, v_a_2389_, v_a_2392_, v___f_2396_, v_nondep_2386_, v___x_2397_, v_a_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
return v___x_2398_;
}
else
{
lean_dec(v_a_2389_);
lean_dec_ref(v_body_2385_);
lean_dec(v_declName_2382_);
lean_dec_ref(v_fvars_2373_);
lean_dec_ref(v_post_2369_);
lean_dec_ref(v_pre_2368_);
return v___x_2391_;
}
}
else
{
lean_dec_ref(v_body_2385_);
lean_dec_ref(v_value_2384_);
lean_dec(v_declName_2382_);
lean_dec_ref(v_fvars_2373_);
lean_dec_ref(v_post_2369_);
lean_dec_ref(v_pre_2368_);
return v___x_2388_;
}
}
else
{
lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___x_2399_ = lean_expr_instantiate_rev(v_e_2374_, v_fvars_2373_);
lean_dec_ref(v_e_2374_);
lean_inc_ref(v_post_2369_);
lean_inc_ref(v_pre_2368_);
v___x_2400_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2368_, v_post_2369_, v_usedLetOnly_2370_, v_skipConstInApp_2371_, v_skipInstances_2372_, v___x_2399_, v_a_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_object* v_a_2401_; uint8_t v___x_2402_; uint8_t v___x_2403_; lean_object* v___x_2404_; 
v_a_2401_ = lean_ctor_get(v___x_2400_, 0);
lean_inc(v_a_2401_);
lean_dec_ref_known(v___x_2400_, 1);
v___x_2402_ = 0;
v___x_2403_ = 1;
v___x_2404_ = l_Lean_Meta_mkLetFVars(v_fvars_2373_, v_a_2401_, v_usedLetOnly_2370_, v___x_2402_, v___x_2403_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
lean_dec_ref(v_fvars_2373_);
if (lean_obj_tag(v___x_2404_) == 0)
{
lean_object* v_a_2405_; lean_object* v___x_2406_; 
v_a_2405_ = lean_ctor_get(v___x_2404_, 0);
lean_inc(v_a_2405_);
lean_dec_ref_known(v___x_2404_, 1);
v___x_2406_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2368_, v_post_2369_, v_usedLetOnly_2370_, v_skipConstInApp_2371_, v_skipInstances_2372_, v_a_2405_, v_a_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
return v___x_2406_;
}
else
{
lean_dec_ref(v_post_2369_);
lean_dec_ref(v_pre_2368_);
return v___x_2404_;
}
}
else
{
lean_dec_ref(v_fvars_2373_);
lean_dec_ref(v_post_2369_);
lean_dec_ref(v_pre_2368_);
return v___x_2400_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2407_; lean_object* v_dummy_2408_; 
v___x_2407_ = lean_box(0);
v_dummy_2408_ = l_Lean_Expr_sort___override(v___x_2407_);
return v_dummy_2408_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(lean_object* v_pre_2409_, lean_object* v_post_2410_, uint8_t v_usedLetOnly_2411_, uint8_t v_skipConstInApp_2412_, uint8_t v_skipInstances_2413_, size_t v_sz_2414_, size_t v_i_2415_, lean_object* v_bs_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
uint8_t v___x_2424_; 
v___x_2424_ = lean_usize_dec_lt(v_i_2415_, v_sz_2414_);
if (v___x_2424_ == 0)
{
lean_object* v___x_2425_; 
lean_dec_ref(v_post_2410_);
lean_dec_ref(v_pre_2409_);
v___x_2425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2425_, 0, v_bs_2416_);
return v___x_2425_;
}
else
{
lean_object* v_v_2426_; lean_object* v___x_2427_; 
v_v_2426_ = lean_array_uget_borrowed(v_bs_2416_, v_i_2415_);
lean_inc(v_v_2426_);
lean_inc_ref(v_post_2410_);
lean_inc_ref(v_pre_2409_);
v___x_2427_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2409_, v_post_2410_, v_usedLetOnly_2411_, v_skipConstInApp_2412_, v_skipInstances_2413_, v_v_2426_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
if (lean_obj_tag(v___x_2427_) == 0)
{
lean_object* v_a_2428_; lean_object* v___x_2429_; lean_object* v_bs_x27_2430_; size_t v___x_2431_; size_t v___x_2432_; lean_object* v___x_2433_; 
v_a_2428_ = lean_ctor_get(v___x_2427_, 0);
lean_inc(v_a_2428_);
lean_dec_ref_known(v___x_2427_, 1);
v___x_2429_ = lean_unsigned_to_nat(0u);
v_bs_x27_2430_ = lean_array_uset(v_bs_2416_, v_i_2415_, v___x_2429_);
v___x_2431_ = ((size_t)1ULL);
v___x_2432_ = lean_usize_add(v_i_2415_, v___x_2431_);
v___x_2433_ = lean_array_uset(v_bs_x27_2430_, v_i_2415_, v_a_2428_);
v_i_2415_ = v___x_2432_;
v_bs_2416_ = v___x_2433_;
goto _start;
}
else
{
lean_object* v_a_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2442_; 
lean_dec_ref(v_bs_2416_);
lean_dec_ref(v_post_2410_);
lean_dec_ref(v_pre_2409_);
v_a_2435_ = lean_ctor_get(v___x_2427_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2437_ = v___x_2427_;
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_a_2435_);
lean_dec(v___x_2427_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2440_; 
if (v_isShared_2438_ == 0)
{
v___x_2440_ = v___x_2437_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_a_2435_);
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
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0(lean_object* v_pre_2443_, lean_object* v_post_2444_, uint8_t v_usedLetOnly_2445_, uint8_t v_skipConstInApp_2446_, uint8_t v_skipInstances_2447_, lean_object* v___x_2448_, lean_object* v___y_2449_, lean_object* v_b_2450_, lean_object* v_a_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
lean_object* v___x_2458_; 
v___x_2458_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2443_, v_post_2444_, v_usedLetOnly_2445_, v_skipConstInApp_2446_, v_skipInstances_2447_, v___x_2448_, v___y_2449_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2468_; 
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2461_ = v___x_2458_;
v_isShared_2462_ = v_isSharedCheck_2468_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2458_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2468_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2466_; 
v___x_2463_ = lean_array_fset(v_b_2450_, v_a_2451_, v_a_2459_);
v___x_2464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2463_);
if (v_isShared_2462_ == 0)
{
lean_ctor_set(v___x_2461_, 0, v___x_2464_);
v___x_2466_ = v___x_2461_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v___x_2464_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
else
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2476_; 
lean_dec_ref(v_b_2450_);
v_a_2469_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2471_ = v___x_2458_;
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2458_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2474_; 
if (v_isShared_2472_ == 0)
{
v___x_2474_ = v___x_2471_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_a_2469_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed(lean_object* v_pre_2477_, lean_object* v_post_2478_, lean_object* v_usedLetOnly_2479_, lean_object* v_skipConstInApp_2480_, lean_object* v_skipInstances_2481_, lean_object* v___x_2482_, lean_object* v___y_2483_, lean_object* v_b_2484_, lean_object* v_a_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_){
_start:
{
uint8_t v_usedLetOnly_boxed_2492_; uint8_t v_skipConstInApp_boxed_2493_; uint8_t v_skipInstances_boxed_2494_; lean_object* v_res_2495_; 
v_usedLetOnly_boxed_2492_ = lean_unbox(v_usedLetOnly_2479_);
v_skipConstInApp_boxed_2493_ = lean_unbox(v_skipConstInApp_2480_);
v_skipInstances_boxed_2494_ = lean_unbox(v_skipInstances_2481_);
v_res_2495_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0(v_pre_2477_, v_post_2478_, v_usedLetOnly_boxed_2492_, v_skipConstInApp_boxed_2493_, v_skipInstances_boxed_2494_, v___x_2482_, v___y_2483_, v_b_2484_, v_a_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
lean_dec(v___y_2486_);
lean_dec(v_a_2485_);
lean_dec(v___y_2483_);
return v_res_2495_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(lean_object* v_upperBound_2496_, lean_object* v___x_2497_, lean_object* v_pre_2498_, lean_object* v_post_2499_, uint8_t v_usedLetOnly_2500_, uint8_t v_skipConstInApp_2501_, uint8_t v_skipInstances_2502_, lean_object* v_a_2503_, lean_object* v_b_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_){
_start:
{
lean_object* v___y_2513_; uint8_t v___x_2536_; 
v___x_2536_ = lean_nat_dec_lt(v_a_2503_, v_upperBound_2496_);
if (v___x_2536_ == 0)
{
lean_object* v___x_2537_; 
lean_dec(v_a_2503_);
lean_dec_ref(v_post_2499_);
lean_dec_ref(v_pre_2498_);
v___x_2537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2537_, 0, v_b_2504_);
return v___x_2537_;
}
else
{
lean_object* v___x_2538_; lean_object* v___x_2539_; uint8_t v___x_2540_; 
v___x_2538_ = lean_array_fget_borrowed(v_b_2504_, v_a_2503_);
v___x_2539_ = lean_array_get_size(v___x_2497_);
v___x_2540_ = lean_nat_dec_lt(v_a_2503_, v___x_2539_);
if (v___x_2540_ == 0)
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___f_2544_; 
lean_inc(v___x_2538_);
v___x_2541_ = lean_box(v_usedLetOnly_2500_);
v___x_2542_ = lean_box(v_skipConstInApp_2501_);
v___x_2543_ = lean_box(v_skipInstances_2502_);
lean_inc(v_a_2503_);
lean_inc(v___y_2505_);
lean_inc_ref(v_post_2499_);
lean_inc_ref(v_pre_2498_);
v___f_2544_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_2544_, 0, v_pre_2498_);
lean_closure_set(v___f_2544_, 1, v_post_2499_);
lean_closure_set(v___f_2544_, 2, v___x_2541_);
lean_closure_set(v___f_2544_, 3, v___x_2542_);
lean_closure_set(v___f_2544_, 4, v___x_2543_);
lean_closure_set(v___f_2544_, 5, v___x_2538_);
lean_closure_set(v___f_2544_, 6, v___y_2505_);
lean_closure_set(v___f_2544_, 7, v_b_2504_);
lean_closure_set(v___f_2544_, 8, v_a_2503_);
v___y_2513_ = v___f_2544_;
goto v___jp_2512_;
}
else
{
lean_object* v___x_2545_; uint8_t v_isInstance_2546_; 
v___x_2545_ = lean_array_fget_borrowed(v___x_2497_, v_a_2503_);
v_isInstance_2546_ = lean_ctor_get_uint8(v___x_2545_, sizeof(void*)*1 + 4);
if (v_isInstance_2546_ == 0)
{
lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___f_2550_; 
lean_inc(v___x_2538_);
v___x_2547_ = lean_box(v_usedLetOnly_2500_);
v___x_2548_ = lean_box(v_skipConstInApp_2501_);
v___x_2549_ = lean_box(v_skipInstances_2502_);
lean_inc(v_a_2503_);
lean_inc(v___y_2505_);
lean_inc_ref(v_post_2499_);
lean_inc_ref(v_pre_2498_);
v___f_2550_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_2550_, 0, v_pre_2498_);
lean_closure_set(v___f_2550_, 1, v_post_2499_);
lean_closure_set(v___f_2550_, 2, v___x_2547_);
lean_closure_set(v___f_2550_, 3, v___x_2548_);
lean_closure_set(v___f_2550_, 4, v___x_2549_);
lean_closure_set(v___f_2550_, 5, v___x_2538_);
lean_closure_set(v___f_2550_, 6, v___y_2505_);
lean_closure_set(v___f_2550_, 7, v_b_2504_);
lean_closure_set(v___f_2550_, 8, v_a_2503_);
v___y_2513_ = v___f_2550_;
goto v___jp_2512_;
}
else
{
lean_object* v___x_2551_; lean_object* v___f_2552_; 
v___x_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2551_, 0, v_b_2504_);
v___f_2552_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2552_, 0, v___x_2551_);
v___y_2513_ = v___f_2552_;
goto v___jp_2512_;
}
}
}
v___jp_2512_:
{
lean_object* v___x_2514_; 
lean_inc(v___y_2510_);
lean_inc_ref(v___y_2509_);
lean_inc(v___y_2508_);
lean_inc_ref(v___y_2507_);
lean_inc(v___y_2506_);
v___x_2514_ = lean_apply_6(v___y_2513_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, lean_box(0));
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_object* v_a_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2527_; 
v_a_2515_ = lean_ctor_get(v___x_2514_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2514_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2517_ = v___x_2514_;
v_isShared_2518_ = v_isSharedCheck_2527_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_a_2515_);
lean_dec(v___x_2514_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2527_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
if (lean_obj_tag(v_a_2515_) == 0)
{
lean_object* v_a_2519_; lean_object* v___x_2521_; 
lean_dec(v_a_2503_);
lean_dec_ref(v_post_2499_);
lean_dec_ref(v_pre_2498_);
v_a_2519_ = lean_ctor_get(v_a_2515_, 0);
lean_inc(v_a_2519_);
lean_dec_ref_known(v_a_2515_, 1);
if (v_isShared_2518_ == 0)
{
lean_ctor_set(v___x_2517_, 0, v_a_2519_);
v___x_2521_ = v___x_2517_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_a_2519_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
else
{
lean_object* v_a_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
lean_del_object(v___x_2517_);
v_a_2523_ = lean_ctor_get(v_a_2515_, 0);
lean_inc(v_a_2523_);
lean_dec_ref_known(v_a_2515_, 1);
v___x_2524_ = lean_unsigned_to_nat(1u);
v___x_2525_ = lean_nat_add(v_a_2503_, v___x_2524_);
lean_dec(v_a_2503_);
v_a_2503_ = v___x_2525_;
v_b_2504_ = v_a_2523_;
goto _start;
}
}
}
else
{
lean_object* v_a_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2535_; 
lean_dec(v_a_2503_);
lean_dec_ref(v_post_2499_);
lean_dec_ref(v_pre_2498_);
v_a_2528_ = lean_ctor_get(v___x_2514_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2514_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2530_ = v___x_2514_;
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_a_2528_);
lean_dec(v___x_2514_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2533_; 
if (v_isShared_2531_ == 0)
{
v___x_2533_ = v___x_2530_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_a_2528_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(uint8_t v_skipInstances_2553_, lean_object* v_pre_2554_, lean_object* v_post_2555_, uint8_t v_usedLetOnly_2556_, uint8_t v_skipConstInApp_2557_, lean_object* v_x_2558_, lean_object* v_x_2559_, lean_object* v_x_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_){
_start:
{
lean_object* v_f_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; 
if (lean_obj_tag(v_x_2558_) == 5)
{
lean_object* v_fn_2618_; lean_object* v_arg_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; 
v_fn_2618_ = lean_ctor_get(v_x_2558_, 0);
lean_inc_ref(v_fn_2618_);
v_arg_2619_ = lean_ctor_get(v_x_2558_, 1);
lean_inc_ref(v_arg_2619_);
lean_dec_ref_known(v_x_2558_, 2);
v___x_2620_ = lean_array_set(v_x_2559_, v_x_2560_, v_arg_2619_);
v___x_2621_ = lean_unsigned_to_nat(1u);
v___x_2622_ = lean_nat_sub(v_x_2560_, v___x_2621_);
lean_dec(v_x_2560_);
v_x_2558_ = v_fn_2618_;
v_x_2559_ = v___x_2620_;
v_x_2560_ = v___x_2622_;
goto _start;
}
else
{
lean_dec(v_x_2560_);
if (v_skipConstInApp_2557_ == 0)
{
goto v___jp_2615_;
}
else
{
uint8_t v___x_2624_; 
v___x_2624_ = l_Lean_Expr_isConst(v_x_2558_);
if (v___x_2624_ == 0)
{
goto v___jp_2615_;
}
else
{
v_f_2569_ = v_x_2558_;
v___y_2570_ = v___y_2561_;
v___y_2571_ = v___y_2562_;
v___y_2572_ = v___y_2563_;
v___y_2573_ = v___y_2564_;
v___y_2574_ = v___y_2565_;
v___y_2575_ = v___y_2566_;
goto v___jp_2568_;
}
}
}
v___jp_2568_:
{
if (v_skipInstances_2553_ == 0)
{
size_t v_sz_2576_; size_t v___x_2577_; lean_object* v___x_2578_; 
v_sz_2576_ = lean_array_size(v_x_2559_);
v___x_2577_ = ((size_t)0ULL);
lean_inc_ref(v_post_2555_);
lean_inc_ref(v_pre_2554_);
v___x_2578_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(v_pre_2554_, v_post_2555_, v_usedLetOnly_2556_, v_skipConstInApp_2557_, v_skipInstances_2553_, v_sz_2576_, v___x_2577_, v_x_2559_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
if (lean_obj_tag(v___x_2578_) == 0)
{
lean_object* v_a_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
v_a_2579_ = lean_ctor_get(v___x_2578_, 0);
lean_inc(v_a_2579_);
lean_dec_ref_known(v___x_2578_, 1);
v___x_2580_ = l_Lean_mkAppN(v_f_2569_, v_a_2579_);
lean_dec(v_a_2579_);
v___x_2581_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2554_, v_post_2555_, v_usedLetOnly_2556_, v_skipConstInApp_2557_, v_skipInstances_2553_, v___x_2580_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
return v___x_2581_;
}
else
{
lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2589_; 
lean_dec_ref(v_f_2569_);
lean_dec_ref(v_post_2555_);
lean_dec_ref(v_pre_2554_);
v_a_2582_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2584_ = v___x_2578_;
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v___x_2578_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2587_; 
if (v_isShared_2585_ == 0)
{
v___x_2587_ = v___x_2584_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_a_2582_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
}
else
{
lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2590_ = lean_array_get_size(v_x_2559_);
lean_inc_ref(v_f_2569_);
v___x_2591_ = l_Lean_Meta_getFunInfoNArgs(v_f_2569_, v___x_2590_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; lean_object* v_paramInfo_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
lean_inc(v_a_2592_);
lean_dec_ref_known(v___x_2591_, 1);
v_paramInfo_2593_ = lean_ctor_get(v_a_2592_, 0);
lean_inc_ref(v_paramInfo_2593_);
lean_dec(v_a_2592_);
v___x_2594_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_2555_);
lean_inc_ref(v_pre_2554_);
v___x_2595_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(v___x_2590_, v_paramInfo_2593_, v_pre_2554_, v_post_2555_, v_usedLetOnly_2556_, v_skipConstInApp_2557_, v_skipInstances_2553_, v___x_2594_, v_x_2559_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
lean_dec_ref(v_paramInfo_2593_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_a_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
lean_inc(v_a_2596_);
lean_dec_ref_known(v___x_2595_, 1);
v___x_2597_ = l_Lean_mkAppN(v_f_2569_, v_a_2596_);
lean_dec(v_a_2596_);
v___x_2598_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2554_, v_post_2555_, v_usedLetOnly_2556_, v_skipConstInApp_2557_, v_skipInstances_2553_, v___x_2597_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
return v___x_2598_;
}
else
{
lean_object* v_a_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2606_; 
lean_dec_ref(v_f_2569_);
lean_dec_ref(v_post_2555_);
lean_dec_ref(v_pre_2554_);
v_a_2599_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2601_ = v___x_2595_;
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_a_2599_);
lean_dec(v___x_2595_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2604_; 
if (v_isShared_2602_ == 0)
{
v___x_2604_ = v___x_2601_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_a_2599_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
}
}
else
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2614_; 
lean_dec_ref(v_f_2569_);
lean_dec_ref(v_x_2559_);
lean_dec_ref(v_post_2555_);
lean_dec_ref(v_pre_2554_);
v_a_2607_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2609_ = v___x_2591_;
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2591_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2612_; 
if (v_isShared_2610_ == 0)
{
v___x_2612_ = v___x_2609_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2607_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
}
}
v___jp_2615_:
{
lean_object* v___x_2616_; 
lean_inc_ref(v_post_2555_);
lean_inc_ref(v_pre_2554_);
v___x_2616_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2554_, v_post_2555_, v_usedLetOnly_2556_, v_skipConstInApp_2557_, v_skipInstances_2553_, v_x_2558_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
if (lean_obj_tag(v___x_2616_) == 0)
{
lean_object* v_a_2617_; 
v_a_2617_ = lean_ctor_get(v___x_2616_, 0);
lean_inc(v_a_2617_);
lean_dec_ref_known(v___x_2616_, 1);
v_f_2569_ = v_a_2617_;
v___y_2570_ = v___y_2561_;
v___y_2571_ = v___y_2562_;
v___y_2572_ = v___y_2563_;
v___y_2573_ = v___y_2564_;
v___y_2574_ = v___y_2565_;
v___y_2575_ = v___y_2566_;
goto v___jp_2568_;
}
else
{
lean_dec_ref(v_x_2559_);
lean_dec_ref(v_post_2555_);
lean_dec_ref(v_pre_2554_);
return v___x_2616_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1(lean_object* v___x_2625_, lean_object* v_pre_2626_, lean_object* v_e_2627_, lean_object* v_post_2628_, uint8_t v_usedLetOnly_2629_, uint8_t v_skipConstInApp_2630_, uint8_t v_skipInstances_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
lean_object* v___x_2639_; 
v___x_2639_ = l_Lean_Core_checkSystem(v___x_2625_, v___y_2636_, v___y_2637_);
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_object* v___x_2640_; 
lean_dec_ref_known(v___x_2639_, 1);
lean_inc_ref(v_pre_2626_);
lean_inc(v___y_2637_);
lean_inc_ref(v___y_2636_);
lean_inc(v___y_2635_);
lean_inc_ref(v___y_2634_);
lean_inc(v___y_2633_);
lean_inc_ref(v_e_2627_);
v___x_2640_ = lean_apply_7(v_pre_2626_, v_e_2627_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, lean_box(0));
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2689_; 
v_a_2641_ = lean_ctor_get(v___x_2640_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2643_ = v___x_2640_;
v_isShared_2644_ = v_isSharedCheck_2689_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v___x_2640_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2689_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___y_2646_; 
switch(lean_obj_tag(v_a_2641_))
{
case 0:
{
lean_object* v_e_2681_; lean_object* v___x_2683_; 
lean_dec_ref(v_post_2628_);
lean_dec_ref(v_e_2627_);
lean_dec_ref(v_pre_2626_);
v_e_2681_ = lean_ctor_get(v_a_2641_, 0);
lean_inc_ref(v_e_2681_);
lean_dec_ref_known(v_a_2641_, 1);
if (v_isShared_2644_ == 0)
{
lean_ctor_set(v___x_2643_, 0, v_e_2681_);
v___x_2683_ = v___x_2643_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_e_2681_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
case 1:
{
lean_object* v_e_2685_; lean_object* v___x_2686_; 
lean_del_object(v___x_2643_);
lean_dec_ref(v_e_2627_);
v_e_2685_ = lean_ctor_get(v_a_2641_, 0);
lean_inc_ref(v_e_2685_);
lean_dec_ref_known(v_a_2641_, 1);
v___x_2686_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2626_, v_post_2628_, v_usedLetOnly_2629_, v_skipConstInApp_2630_, v_skipInstances_2631_, v_e_2685_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
return v___x_2686_;
}
default: 
{
lean_object* v_e_x3f_2687_; 
lean_del_object(v___x_2643_);
v_e_x3f_2687_ = lean_ctor_get(v_a_2641_, 0);
lean_inc(v_e_x3f_2687_);
lean_dec_ref_known(v_a_2641_, 1);
if (lean_obj_tag(v_e_x3f_2687_) == 0)
{
v___y_2646_ = v_e_2627_;
goto v___jp_2645_;
}
else
{
lean_object* v_val_2688_; 
lean_dec_ref(v_e_2627_);
v_val_2688_ = lean_ctor_get(v_e_x3f_2687_, 0);
lean_inc(v_val_2688_);
lean_dec_ref_known(v_e_x3f_2687_, 1);
v___y_2646_ = v_val_2688_;
goto v___jp_2645_;
}
}
}
v___jp_2645_:
{
switch(lean_obj_tag(v___y_2646_))
{
case 7:
{
lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2647_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0));
v___x_2648_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(v_pre_2626_, v_post_2628_, v_usedLetOnly_2629_, v_skipConstInApp_2630_, v_skipInstances_2631_, v___x_2647_, v___y_2646_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
return v___x_2648_;
}
case 6:
{
lean_object* v___x_2649_; lean_object* v___x_2650_; 
v___x_2649_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0));
v___x_2650_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(v_pre_2626_, v_post_2628_, v_usedLetOnly_2629_, v_skipConstInApp_2630_, v_skipInstances_2631_, v___x_2649_, v___y_2646_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
return v___x_2650_;
}
case 8:
{
lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___x_2651_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0));
v___x_2652_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(v_pre_2626_, v_post_2628_, v_usedLetOnly_2629_, v_skipConstInApp_2630_, v_skipInstances_2631_, v___x_2651_, v___y_2646_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
return v___x_2652_;
}
case 5:
{
lean_object* v_dummy_2653_; lean_object* v_nargs_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; 
v_dummy_2653_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1);
v_nargs_2654_ = l_Lean_Expr_getAppNumArgs(v___y_2646_);
lean_inc(v_nargs_2654_);
v___x_2655_ = lean_mk_array(v_nargs_2654_, v_dummy_2653_);
v___x_2656_ = lean_unsigned_to_nat(1u);
v___x_2657_ = lean_nat_sub(v_nargs_2654_, v___x_2656_);
lean_dec(v_nargs_2654_);
v___x_2658_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(v_skipInstances_2631_, v_pre_2626_, v_post_2628_, v_usedLetOnly_2629_, v_skipConstInApp_2630_, v___y_2646_, v___x_2655_, v___x_2657_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
return v___x_2658_;
}
case 10:
{
lean_object* v_data_2659_; lean_object* v_expr_2660_; lean_object* v___x_2661_; 
v_data_2659_ = lean_ctor_get(v___y_2646_, 0);
v_expr_2660_ = lean_ctor_get(v___y_2646_, 1);
lean_inc_ref(v_expr_2660_);
lean_inc_ref(v_post_2628_);
lean_inc_ref(v_pre_2626_);
v___x_2661_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2626_, v_post_2628_, v_usedLetOnly_2629_, v_skipConstInApp_2630_, v_skipInstances_2631_, v_expr_2660_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v_a_2662_; size_t v___x_2663_; size_t v___x_2664_; uint8_t v___x_2665_; 
v_a_2662_ = lean_ctor_get(v___x_2661_, 0);
lean_inc(v_a_2662_);
lean_dec_ref_known(v___x_2661_, 1);
v___x_2663_ = lean_ptr_addr(v_expr_2660_);
v___x_2664_ = lean_ptr_addr(v_a_2662_);
v___x_2665_ = lean_usize_dec_eq(v___x_2663_, v___x_2664_);
if (v___x_2665_ == 0)
{
lean_object* v___x_2666_; lean_object* v___x_2667_; 
lean_inc(v_data_2659_);
lean_dec_ref_known(v___y_2646_, 2);
v___x_2666_ = l_Lean_Expr_mdata___override(v_data_2659_, v_a_2662_);
v___x_2667_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2626_, v_post_2628_, v_usedLetOnly_2629_, v_skipConstInApp_2630_, v_skipInstances_2631_, v___x_2666_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
return v___x_2667_;
}
else
{
lean_object* v___x_2668_; 
lean_dec(v_a_2662_);
v___x_2668_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2626_, v_post_2628_, v_usedLetOnly_2629_, v_skipConstInApp_2630_, v_skipInstances_2631_, v___y_2646_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
return v___x_2668_;
}
}
else
{
lean_dec_ref_known(v___y_2646_, 2);
lean_dec_ref(v_post_2628_);
lean_dec_ref(v_pre_2626_);
return v___x_2661_;
}
}
case 11:
{
lean_object* v_typeName_2669_; lean_object* v_idx_2670_; lean_object* v_struct_2671_; lean_object* v___x_2672_; 
v_typeName_2669_ = lean_ctor_get(v___y_2646_, 0);
v_idx_2670_ = lean_ctor_get(v___y_2646_, 1);
v_struct_2671_ = lean_ctor_get(v___y_2646_, 2);
lean_inc_ref(v_struct_2671_);
lean_inc_ref(v_post_2628_);
lean_inc_ref(v_pre_2626_);
v___x_2672_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2626_, v_post_2628_, v_usedLetOnly_2629_, v_skipConstInApp_2630_, v_skipInstances_2631_, v_struct_2671_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v_a_2673_; size_t v___x_2674_; size_t v___x_2675_; uint8_t v___x_2676_; 
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
lean_inc(v_a_2673_);
lean_dec_ref_known(v___x_2672_, 1);
v___x_2674_ = lean_ptr_addr(v_struct_2671_);
v___x_2675_ = lean_ptr_addr(v_a_2673_);
v___x_2676_ = lean_usize_dec_eq(v___x_2674_, v___x_2675_);
if (v___x_2676_ == 0)
{
lean_object* v___x_2677_; lean_object* v___x_2678_; 
lean_inc(v_idx_2670_);
lean_inc(v_typeName_2669_);
lean_dec_ref_known(v___y_2646_, 3);
v___x_2677_ = l_Lean_Expr_proj___override(v_typeName_2669_, v_idx_2670_, v_a_2673_);
v___x_2678_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2626_, v_post_2628_, v_usedLetOnly_2629_, v_skipConstInApp_2630_, v_skipInstances_2631_, v___x_2677_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
return v___x_2678_;
}
else
{
lean_object* v___x_2679_; 
lean_dec(v_a_2673_);
v___x_2679_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2626_, v_post_2628_, v_usedLetOnly_2629_, v_skipConstInApp_2630_, v_skipInstances_2631_, v___y_2646_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
return v___x_2679_;
}
}
else
{
lean_dec_ref_known(v___y_2646_, 3);
lean_dec_ref(v_post_2628_);
lean_dec_ref(v_pre_2626_);
return v___x_2672_;
}
}
default: 
{
lean_object* v___x_2680_; 
v___x_2680_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2626_, v_post_2628_, v_usedLetOnly_2629_, v_skipConstInApp_2630_, v_skipInstances_2631_, v___y_2646_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
return v___x_2680_;
}
}
}
}
}
else
{
lean_object* v_a_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2697_; 
lean_dec_ref(v_post_2628_);
lean_dec_ref(v_e_2627_);
lean_dec_ref(v_pre_2626_);
v_a_2690_ = lean_ctor_get(v___x_2640_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2692_ = v___x_2640_;
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_a_2690_);
lean_dec(v___x_2640_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2695_; 
if (v_isShared_2693_ == 0)
{
v___x_2695_ = v___x_2692_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_a_2690_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
}
}
else
{
lean_object* v_a_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2705_; 
lean_dec_ref(v_post_2628_);
lean_dec_ref(v_e_2627_);
lean_dec_ref(v_pre_2626_);
v_a_2698_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2700_ = v___x_2639_;
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_dec(v___x_2639_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2703_; 
if (v_isShared_2701_ == 0)
{
v___x_2703_ = v___x_2700_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_a_2698_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___boxed(lean_object* v___x_2706_, lean_object* v_pre_2707_, lean_object* v_e_2708_, lean_object* v_post_2709_, lean_object* v_usedLetOnly_2710_, lean_object* v_skipConstInApp_2711_, lean_object* v_skipInstances_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
uint8_t v_usedLetOnly_boxed_2720_; uint8_t v_skipConstInApp_boxed_2721_; uint8_t v_skipInstances_boxed_2722_; lean_object* v_res_2723_; 
v_usedLetOnly_boxed_2720_ = lean_unbox(v_usedLetOnly_2710_);
v_skipConstInApp_boxed_2721_ = lean_unbox(v_skipConstInApp_2711_);
v_skipInstances_boxed_2722_ = lean_unbox(v_skipInstances_2712_);
v_res_2723_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1(v___x_2706_, v_pre_2707_, v_e_2708_, v_post_2709_, v_usedLetOnly_boxed_2720_, v_skipConstInApp_boxed_2721_, v_skipInstances_boxed_2722_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
lean_dec(v___y_2716_);
lean_dec_ref(v___y_2715_);
lean_dec(v___y_2714_);
lean_dec(v___y_2713_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(lean_object* v_pre_2724_, lean_object* v_post_2725_, uint8_t v_usedLetOnly_2726_, uint8_t v_skipConstInApp_2727_, uint8_t v_skipInstances_2728_, lean_object* v_e_2729_, lean_object* v_a_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; 
lean_inc(v_a_2730_);
v___x_2737_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2737_, 0, lean_box(0));
lean_closure_set(v___x_2737_, 1, lean_box(0));
lean_closure_set(v___x_2737_, 2, v_a_2730_);
v___x_2738_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(lean_box(0), v___x_2737_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
if (lean_obj_tag(v___x_2738_) == 0)
{
lean_object* v_a_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2773_; 
v_a_2739_ = lean_ctor_get(v___x_2738_, 0);
v_isSharedCheck_2773_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2741_ = v___x_2738_;
v_isShared_2742_ = v_isSharedCheck_2773_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_a_2739_);
lean_dec(v___x_2738_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2773_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v___x_2743_; 
v___x_2743_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(v_a_2739_, v_e_2729_);
lean_dec(v_a_2739_);
if (lean_obj_tag(v___x_2743_) == 0)
{
lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___f_2748_; lean_object* v___x_2749_; 
lean_del_object(v___x_2741_);
v___x_2744_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___closed__0));
v___x_2745_ = lean_box(v_usedLetOnly_2726_);
v___x_2746_ = lean_box(v_skipConstInApp_2727_);
v___x_2747_ = lean_box(v_skipInstances_2728_);
lean_inc_ref(v_e_2729_);
v___f_2748_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___boxed), 14, 7);
lean_closure_set(v___f_2748_, 0, v___x_2744_);
lean_closure_set(v___f_2748_, 1, v_pre_2724_);
lean_closure_set(v___f_2748_, 2, v_e_2729_);
lean_closure_set(v___f_2748_, 3, v_post_2725_);
lean_closure_set(v___f_2748_, 4, v___x_2745_);
lean_closure_set(v___f_2748_, 5, v___x_2746_);
lean_closure_set(v___f_2748_, 6, v___x_2747_);
v___x_2749_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v___f_2748_, v_a_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
if (lean_obj_tag(v___x_2749_) == 0)
{
lean_object* v_a_2750_; lean_object* v___f_2751_; lean_object* v___x_2752_; 
v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
lean_inc_n(v_a_2750_, 2);
lean_dec_ref_known(v___x_2749_, 1);
lean_inc(v_a_2730_);
v___f_2751_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2751_, 0, v_a_2730_);
lean_closure_set(v___f_2751_, 1, v_e_2729_);
lean_closure_set(v___f_2751_, 2, v_a_2750_);
v___x_2752_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(lean_box(0), v___f_2751_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
if (lean_obj_tag(v___x_2752_) == 0)
{
lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2759_; 
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2752_);
if (v_isSharedCheck_2759_ == 0)
{
lean_object* v_unused_2760_; 
v_unused_2760_ = lean_ctor_get(v___x_2752_, 0);
lean_dec(v_unused_2760_);
v___x_2754_ = v___x_2752_;
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
else
{
lean_dec(v___x_2752_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2757_; 
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 0, v_a_2750_);
v___x_2757_ = v___x_2754_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_a_2750_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
else
{
lean_object* v_a_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2768_; 
lean_dec(v_a_2750_);
v_a_2761_ = lean_ctor_get(v___x_2752_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2752_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2763_ = v___x_2752_;
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_a_2761_);
lean_dec(v___x_2752_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2766_; 
if (v_isShared_2764_ == 0)
{
v___x_2766_ = v___x_2763_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_a_2761_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
}
else
{
lean_dec_ref(v_e_2729_);
return v___x_2749_;
}
}
else
{
lean_object* v_val_2769_; lean_object* v___x_2771_; 
lean_dec_ref(v_e_2729_);
lean_dec_ref(v_post_2725_);
lean_dec_ref(v_pre_2724_);
v_val_2769_ = lean_ctor_get(v___x_2743_, 0);
lean_inc(v_val_2769_);
lean_dec_ref_known(v___x_2743_, 1);
if (v_isShared_2742_ == 0)
{
lean_ctor_set(v___x_2741_, 0, v_val_2769_);
v___x_2771_ = v___x_2741_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_val_2769_);
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
lean_object* v_a_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2781_; 
lean_dec_ref(v_e_2729_);
lean_dec_ref(v_post_2725_);
lean_dec_ref(v_pre_2724_);
v_a_2774_ = lean_ctor_get(v___x_2738_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2776_ = v___x_2738_;
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_a_2774_);
lean_dec(v___x_2738_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2779_; 
if (v_isShared_2777_ == 0)
{
v___x_2779_ = v___x_2776_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_a_2774_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0___boxed(lean_object* v_fvars_2782_, lean_object* v_pre_2783_, lean_object* v_post_2784_, lean_object* v_usedLetOnly_2785_, lean_object* v_skipConstInApp_2786_, lean_object* v_skipInstances_2787_, lean_object* v_body_2788_, lean_object* v_x_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_){
_start:
{
uint8_t v_usedLetOnly_boxed_2797_; uint8_t v_skipConstInApp_boxed_2798_; uint8_t v_skipInstances_boxed_2799_; lean_object* v_res_2800_; 
v_usedLetOnly_boxed_2797_ = lean_unbox(v_usedLetOnly_2785_);
v_skipConstInApp_boxed_2798_ = lean_unbox(v_skipConstInApp_2786_);
v_skipInstances_boxed_2799_ = lean_unbox(v_skipInstances_2787_);
v_res_2800_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0(v_fvars_2782_, v_pre_2783_, v_post_2784_, v_usedLetOnly_boxed_2797_, v_skipConstInApp_boxed_2798_, v_skipInstances_boxed_2799_, v_body_2788_, v_x_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
lean_dec(v___y_2793_);
lean_dec_ref(v___y_2792_);
lean_dec(v___y_2791_);
lean_dec(v___y_2790_);
return v_res_2800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(lean_object* v_pre_2801_, lean_object* v_post_2802_, uint8_t v_usedLetOnly_2803_, uint8_t v_skipConstInApp_2804_, uint8_t v_skipInstances_2805_, lean_object* v_fvars_2806_, lean_object* v_e_2807_, lean_object* v_a_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_){
_start:
{
if (lean_obj_tag(v_e_2807_) == 7)
{
lean_object* v_binderName_2815_; lean_object* v_binderType_2816_; lean_object* v_body_2817_; uint8_t v_binderInfo_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; 
v_binderName_2815_ = lean_ctor_get(v_e_2807_, 0);
lean_inc(v_binderName_2815_);
v_binderType_2816_ = lean_ctor_get(v_e_2807_, 1);
lean_inc_ref(v_binderType_2816_);
v_body_2817_ = lean_ctor_get(v_e_2807_, 2);
lean_inc_ref(v_body_2817_);
v_binderInfo_2818_ = lean_ctor_get_uint8(v_e_2807_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2807_, 3);
v___x_2819_ = lean_expr_instantiate_rev(v_binderType_2816_, v_fvars_2806_);
lean_dec_ref(v_binderType_2816_);
lean_inc_ref(v_post_2802_);
lean_inc_ref(v_pre_2801_);
v___x_2820_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2801_, v_post_2802_, v_usedLetOnly_2803_, v_skipConstInApp_2804_, v_skipInstances_2805_, v___x_2819_, v_a_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___f_2825_; uint8_t v___x_2826_; lean_object* v___x_2827_; 
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_a_2821_);
lean_dec_ref_known(v___x_2820_, 1);
v___x_2822_ = lean_box(v_usedLetOnly_2803_);
v___x_2823_ = lean_box(v_skipConstInApp_2804_);
v___x_2824_ = lean_box(v_skipInstances_2805_);
v___f_2825_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0___boxed), 15, 7);
lean_closure_set(v___f_2825_, 0, v_fvars_2806_);
lean_closure_set(v___f_2825_, 1, v_pre_2801_);
lean_closure_set(v___f_2825_, 2, v_post_2802_);
lean_closure_set(v___f_2825_, 3, v___x_2822_);
lean_closure_set(v___f_2825_, 4, v___x_2823_);
lean_closure_set(v___f_2825_, 5, v___x_2824_);
lean_closure_set(v___f_2825_, 6, v_body_2817_);
v___x_2826_ = 0;
v___x_2827_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_2815_, v_binderInfo_2818_, v_a_2821_, v___f_2825_, v___x_2826_, v_a_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
return v___x_2827_;
}
else
{
lean_dec_ref(v_body_2817_);
lean_dec(v_binderName_2815_);
lean_dec_ref(v_fvars_2806_);
lean_dec_ref(v_post_2802_);
lean_dec_ref(v_pre_2801_);
return v___x_2820_;
}
}
else
{
lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2828_ = lean_expr_instantiate_rev(v_e_2807_, v_fvars_2806_);
lean_dec_ref(v_e_2807_);
lean_inc_ref(v_post_2802_);
lean_inc_ref(v_pre_2801_);
v___x_2829_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2801_, v_post_2802_, v_usedLetOnly_2803_, v_skipConstInApp_2804_, v_skipInstances_2805_, v___x_2828_, v_a_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_object* v_a_2830_; uint8_t v___x_2831_; uint8_t v___x_2832_; uint8_t v___x_2833_; lean_object* v___x_2834_; 
v_a_2830_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_a_2830_);
lean_dec_ref_known(v___x_2829_, 1);
v___x_2831_ = 0;
v___x_2832_ = 1;
v___x_2833_ = 1;
v___x_2834_ = l_Lean_Meta_mkForallFVars(v_fvars_2806_, v_a_2830_, v___x_2831_, v_usedLetOnly_2803_, v___x_2832_, v___x_2833_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
lean_dec_ref(v_fvars_2806_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v_a_2835_; lean_object* v___x_2836_; 
v_a_2835_ = lean_ctor_get(v___x_2834_, 0);
lean_inc(v_a_2835_);
lean_dec_ref_known(v___x_2834_, 1);
v___x_2836_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2801_, v_post_2802_, v_usedLetOnly_2803_, v_skipConstInApp_2804_, v_skipInstances_2805_, v_a_2835_, v_a_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
return v___x_2836_;
}
else
{
lean_dec_ref(v_post_2802_);
lean_dec_ref(v_pre_2801_);
return v___x_2834_;
}
}
else
{
lean_dec_ref(v_fvars_2806_);
lean_dec_ref(v_post_2802_);
lean_dec_ref(v_pre_2801_);
return v___x_2829_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0(lean_object* v_fvars_2837_, lean_object* v_pre_2838_, lean_object* v_post_2839_, uint8_t v_usedLetOnly_2840_, uint8_t v_skipConstInApp_2841_, uint8_t v_skipInstances_2842_, lean_object* v_body_2843_, lean_object* v_x_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_){
_start:
{
lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___x_2852_ = lean_array_push(v_fvars_2837_, v_x_2844_);
v___x_2853_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(v_pre_2838_, v_post_2839_, v_usedLetOnly_2840_, v_skipConstInApp_2841_, v_skipInstances_2842_, v___x_2852_, v_body_2843_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_);
return v___x_2853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_2854_, lean_object* v_post_2855_, lean_object* v_usedLetOnly_2856_, lean_object* v_skipConstInApp_2857_, lean_object* v_skipInstances_2858_, lean_object* v_e_2859_, lean_object* v_a_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_){
_start:
{
uint8_t v_usedLetOnly_boxed_2867_; uint8_t v_skipConstInApp_boxed_2868_; uint8_t v_skipInstances_boxed_2869_; lean_object* v_res_2870_; 
v_usedLetOnly_boxed_2867_ = lean_unbox(v_usedLetOnly_2856_);
v_skipConstInApp_boxed_2868_ = lean_unbox(v_skipConstInApp_2857_);
v_skipInstances_boxed_2869_ = lean_unbox(v_skipInstances_2858_);
v_res_2870_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2854_, v_post_2855_, v_usedLetOnly_boxed_2867_, v_skipConstInApp_boxed_2868_, v_skipInstances_boxed_2869_, v_e_2859_, v_a_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec_ref(v___y_2862_);
lean_dec(v___y_2861_);
lean_dec(v_a_2860_);
return v_res_2870_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_2871_, lean_object* v_post_2872_, lean_object* v_usedLetOnly_2873_, lean_object* v_skipConstInApp_2874_, lean_object* v_skipInstances_2875_, lean_object* v_sz_2876_, lean_object* v_i_2877_, lean_object* v_bs_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_){
_start:
{
uint8_t v_usedLetOnly_boxed_2886_; uint8_t v_skipConstInApp_boxed_2887_; uint8_t v_skipInstances_boxed_2888_; size_t v_sz_boxed_2889_; size_t v_i_boxed_2890_; lean_object* v_res_2891_; 
v_usedLetOnly_boxed_2886_ = lean_unbox(v_usedLetOnly_2873_);
v_skipConstInApp_boxed_2887_ = lean_unbox(v_skipConstInApp_2874_);
v_skipInstances_boxed_2888_ = lean_unbox(v_skipInstances_2875_);
v_sz_boxed_2889_ = lean_unbox_usize(v_sz_2876_);
lean_dec(v_sz_2876_);
v_i_boxed_2890_ = lean_unbox_usize(v_i_2877_);
lean_dec(v_i_2877_);
v_res_2891_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(v_pre_2871_, v_post_2872_, v_usedLetOnly_boxed_2886_, v_skipConstInApp_boxed_2887_, v_skipInstances_boxed_2888_, v_sz_boxed_2889_, v_i_boxed_2890_, v_bs_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2883_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec(v___y_2879_);
return v_res_2891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___boxed(lean_object* v_pre_2892_, lean_object* v_post_2893_, lean_object* v_usedLetOnly_2894_, lean_object* v_skipConstInApp_2895_, lean_object* v_skipInstances_2896_, lean_object* v_e_2897_, lean_object* v_a_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_){
_start:
{
uint8_t v_usedLetOnly_boxed_2905_; uint8_t v_skipConstInApp_boxed_2906_; uint8_t v_skipInstances_boxed_2907_; lean_object* v_res_2908_; 
v_usedLetOnly_boxed_2905_ = lean_unbox(v_usedLetOnly_2894_);
v_skipConstInApp_boxed_2906_ = lean_unbox(v_skipConstInApp_2895_);
v_skipInstances_boxed_2907_ = lean_unbox(v_skipInstances_2896_);
v_res_2908_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2892_, v_post_2893_, v_usedLetOnly_boxed_2905_, v_skipConstInApp_boxed_2906_, v_skipInstances_boxed_2907_, v_e_2897_, v_a_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
lean_dec(v___y_2903_);
lean_dec_ref(v___y_2902_);
lean_dec(v___y_2901_);
lean_dec_ref(v___y_2900_);
lean_dec(v___y_2899_);
lean_dec(v_a_2898_);
return v_res_2908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___boxed(lean_object* v_pre_2909_, lean_object* v_post_2910_, lean_object* v_usedLetOnly_2911_, lean_object* v_skipConstInApp_2912_, lean_object* v_skipInstances_2913_, lean_object* v_fvars_2914_, lean_object* v_e_2915_, lean_object* v_a_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_){
_start:
{
uint8_t v_usedLetOnly_boxed_2923_; uint8_t v_skipConstInApp_boxed_2924_; uint8_t v_skipInstances_boxed_2925_; lean_object* v_res_2926_; 
v_usedLetOnly_boxed_2923_ = lean_unbox(v_usedLetOnly_2911_);
v_skipConstInApp_boxed_2924_ = lean_unbox(v_skipConstInApp_2912_);
v_skipInstances_boxed_2925_ = lean_unbox(v_skipInstances_2913_);
v_res_2926_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(v_pre_2909_, v_post_2910_, v_usedLetOnly_boxed_2923_, v_skipConstInApp_boxed_2924_, v_skipInstances_boxed_2925_, v_fvars_2914_, v_e_2915_, v_a_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
lean_dec(v___y_2917_);
lean_dec(v_a_2916_);
return v_res_2926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___boxed(lean_object* v_pre_2927_, lean_object* v_post_2928_, lean_object* v_usedLetOnly_2929_, lean_object* v_skipConstInApp_2930_, lean_object* v_skipInstances_2931_, lean_object* v_fvars_2932_, lean_object* v_e_2933_, lean_object* v_a_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_){
_start:
{
uint8_t v_usedLetOnly_boxed_2941_; uint8_t v_skipConstInApp_boxed_2942_; uint8_t v_skipInstances_boxed_2943_; lean_object* v_res_2944_; 
v_usedLetOnly_boxed_2941_ = lean_unbox(v_usedLetOnly_2929_);
v_skipConstInApp_boxed_2942_ = lean_unbox(v_skipConstInApp_2930_);
v_skipInstances_boxed_2943_ = lean_unbox(v_skipInstances_2931_);
v_res_2944_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(v_pre_2927_, v_post_2928_, v_usedLetOnly_boxed_2941_, v_skipConstInApp_boxed_2942_, v_skipInstances_boxed_2943_, v_fvars_2932_, v_e_2933_, v_a_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2935_);
lean_dec(v_a_2934_);
return v_res_2944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___boxed(lean_object* v_pre_2945_, lean_object* v_post_2946_, lean_object* v_usedLetOnly_2947_, lean_object* v_skipConstInApp_2948_, lean_object* v_skipInstances_2949_, lean_object* v_fvars_2950_, lean_object* v_e_2951_, lean_object* v_a_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_){
_start:
{
uint8_t v_usedLetOnly_boxed_2959_; uint8_t v_skipConstInApp_boxed_2960_; uint8_t v_skipInstances_boxed_2961_; lean_object* v_res_2962_; 
v_usedLetOnly_boxed_2959_ = lean_unbox(v_usedLetOnly_2947_);
v_skipConstInApp_boxed_2960_ = lean_unbox(v_skipConstInApp_2948_);
v_skipInstances_boxed_2961_ = lean_unbox(v_skipInstances_2949_);
v_res_2962_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(v_pre_2945_, v_post_2946_, v_usedLetOnly_boxed_2959_, v_skipConstInApp_boxed_2960_, v_skipInstances_boxed_2961_, v_fvars_2950_, v_e_2951_, v_a_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
lean_dec(v___y_2953_);
lean_dec(v_a_2952_);
return v_res_2962_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_upperBound_2963_, lean_object* v___x_2964_, lean_object* v_pre_2965_, lean_object* v_post_2966_, lean_object* v_usedLetOnly_2967_, lean_object* v_skipConstInApp_2968_, lean_object* v_skipInstances_2969_, lean_object* v_a_2970_, lean_object* v_b_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_){
_start:
{
uint8_t v_usedLetOnly_boxed_2979_; uint8_t v_skipConstInApp_boxed_2980_; uint8_t v_skipInstances_boxed_2981_; lean_object* v_res_2982_; 
v_usedLetOnly_boxed_2979_ = lean_unbox(v_usedLetOnly_2967_);
v_skipConstInApp_boxed_2980_ = lean_unbox(v_skipConstInApp_2968_);
v_skipInstances_boxed_2981_ = lean_unbox(v_skipInstances_2969_);
v_res_2982_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(v_upperBound_2963_, v___x_2964_, v_pre_2965_, v_post_2966_, v_usedLetOnly_boxed_2979_, v_skipConstInApp_boxed_2980_, v_skipInstances_boxed_2981_, v_a_2970_, v_b_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2973_);
lean_dec(v___y_2972_);
lean_dec_ref(v___x_2964_);
lean_dec(v_upperBound_2963_);
return v_res_2982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8___boxed(lean_object* v_skipInstances_2983_, lean_object* v_pre_2984_, lean_object* v_post_2985_, lean_object* v_usedLetOnly_2986_, lean_object* v_skipConstInApp_2987_, lean_object* v_x_2988_, lean_object* v_x_2989_, lean_object* v_x_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_){
_start:
{
uint8_t v_skipInstances_boxed_2998_; uint8_t v_usedLetOnly_boxed_2999_; uint8_t v_skipConstInApp_boxed_3000_; lean_object* v_res_3001_; 
v_skipInstances_boxed_2998_ = lean_unbox(v_skipInstances_2983_);
v_usedLetOnly_boxed_2999_ = lean_unbox(v_usedLetOnly_2986_);
v_skipConstInApp_boxed_3000_ = lean_unbox(v_skipConstInApp_2987_);
v_res_3001_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(v_skipInstances_boxed_2998_, v_pre_2984_, v_post_2985_, v_usedLetOnly_boxed_2999_, v_skipConstInApp_boxed_3000_, v_x_2988_, v_x_2989_, v_x_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec(v___y_2992_);
lean_dec(v___y_2991_);
return v_res_3001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_object* v_00_u03b1_3002_, lean_object* v_x_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_){
_start:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___x_3010_ = lean_apply_1(v_x_3003_, lean_box(0));
v___x_3011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3011_, 0, v___x_3010_);
return v___x_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0___boxed(lean_object* v_00_u03b1_3012_, lean_object* v_x_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_){
_start:
{
lean_object* v_res_3020_; 
v_res_3020_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(v_00_u03b1_3012_, v_x_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec(v___y_3016_);
lean_dec_ref(v___y_3015_);
lean_dec(v___y_3014_);
return v_res_3020_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3021_ = lean_box(0);
v___x_3022_ = lean_unsigned_to_nat(16u);
v___x_3023_ = lean_mk_array(v___x_3022_, v___x_3021_);
return v___x_3023_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3024_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0);
v___x_3025_ = lean_unsigned_to_nat(0u);
v___x_3026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3025_);
lean_ctor_set(v___x_3026_, 1, v___x_3024_);
return v___x_3026_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2(void){
_start:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___x_3027_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1);
v___x_3028_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3028_, 0, lean_box(0));
lean_closure_set(v___x_3028_, 1, lean_box(0));
lean_closure_set(v___x_3028_, 2, v___x_3027_);
return v___x_3028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(lean_object* v_input_3029_, lean_object* v_pre_3030_, lean_object* v_post_3031_, uint8_t v_usedLetOnly_3032_, uint8_t v_skipConstInApp_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_){
_start:
{
lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v_a_3042_; uint8_t v___x_3043_; lean_object* v___x_3044_; 
v___x_3040_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2);
v___x_3041_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_box(0), v___x_3040_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_);
v_a_3042_ = lean_ctor_get(v___x_3041_, 0);
lean_inc(v_a_3042_);
lean_dec_ref(v___x_3041_);
v___x_3043_ = 0;
v___x_3044_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_3030_, v_post_3031_, v_usedLetOnly_3032_, v_skipConstInApp_3033_, v___x_3043_, v_input_3029_, v_a_3042_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v_a_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3054_; 
v_a_3045_ = lean_ctor_get(v___x_3044_, 0);
lean_inc(v_a_3045_);
lean_dec_ref_known(v___x_3044_, 1);
v___x_3046_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3046_, 0, lean_box(0));
lean_closure_set(v___x_3046_, 1, lean_box(0));
lean_closure_set(v___x_3046_, 2, v_a_3042_);
v___x_3047_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_box(0), v___x_3046_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3054_ == 0)
{
lean_object* v_unused_3055_; 
v_unused_3055_ = lean_ctor_get(v___x_3047_, 0);
lean_dec(v_unused_3055_);
v___x_3049_ = v___x_3047_;
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
else
{
lean_dec(v___x_3047_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v___x_3052_; 
if (v_isShared_3050_ == 0)
{
lean_ctor_set(v___x_3049_, 0, v_a_3045_);
v___x_3052_ = v___x_3049_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_a_3045_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
}
else
{
lean_dec(v_a_3042_);
return v___x_3044_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___boxed(lean_object* v_input_3056_, lean_object* v_pre_3057_, lean_object* v_post_3058_, lean_object* v_usedLetOnly_3059_, lean_object* v_skipConstInApp_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_){
_start:
{
uint8_t v_usedLetOnly_boxed_3067_; uint8_t v_skipConstInApp_boxed_3068_; lean_object* v_res_3069_; 
v_usedLetOnly_boxed_3067_ = lean_unbox(v_usedLetOnly_3059_);
v_skipConstInApp_boxed_3068_ = lean_unbox(v_skipConstInApp_3060_);
v_res_3069_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(v_input_3056_, v_pre_3057_, v_post_3058_, v_usedLetOnly_boxed_3067_, v_skipConstInApp_boxed_3068_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_);
lean_dec(v___y_3065_);
lean_dec_ref(v___y_3064_);
lean_dec(v___y_3063_);
lean_dec_ref(v___y_3062_);
lean_dec(v___y_3061_);
return v_res_3069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore(lean_object* v_e_3071_, uint8_t v_elimTrivial_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_){
_start:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v_pre_3081_; lean_object* v___f_3082_; uint8_t v___x_3083_; lean_object* v___x_3084_; 
v___x_3078_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3);
v___x_3079_ = lean_st_mk_ref(v___x_3078_);
v___x_3080_ = lean_box(v_elimTrivial_3072_);
v_pre_3081_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___boxed), 8, 1);
lean_closure_set(v_pre_3081_, 0, v___x_3080_);
v___f_3082_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___closed__0));
v___x_3083_ = 0;
v___x_3084_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(v_e_3071_, v_pre_3081_, v___f_3082_, v___x_3083_, v___x_3083_, v___x_3079_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_);
if (lean_obj_tag(v___x_3084_) == 0)
{
lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3093_; 
v_a_3085_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3087_ = v___x_3084_;
v_isShared_3088_ = v_isSharedCheck_3093_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3084_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3093_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3089_; lean_object* v___x_3091_; 
v___x_3089_ = lean_st_ref_get(v___x_3079_);
lean_dec(v___x_3079_);
lean_dec(v___x_3089_);
if (v_isShared_3088_ == 0)
{
v___x_3091_ = v___x_3087_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_a_3085_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
}
}
}
else
{
lean_dec(v___x_3079_);
return v___x_3084_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___boxed(lean_object* v_e_3094_, lean_object* v_elimTrivial_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_){
_start:
{
uint8_t v_elimTrivial_boxed_3101_; lean_object* v_res_3102_; 
v_elimTrivial_boxed_3101_ = lean_unbox(v_elimTrivial_3095_);
v_res_3102_ = l_Lean_Elab_Tactic_Do_elimLetsCore(v_e_3094_, v_elimTrivial_boxed_3101_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_);
lean_dec(v_a_3099_);
lean_dec_ref(v_a_3098_);
lean_dec(v_a_3097_);
lean_dec_ref(v_a_3096_);
return v_res_3102_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(lean_object* v_upperBound_3103_, lean_object* v___x_3104_, lean_object* v_pre_3105_, lean_object* v_post_3106_, uint8_t v_usedLetOnly_3107_, uint8_t v_skipConstInApp_3108_, uint8_t v_skipInstances_3109_, lean_object* v___x_3110_, lean_object* v_inst_3111_, lean_object* v_R_3112_, lean_object* v_a_3113_, lean_object* v_b_3114_, lean_object* v_c_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_){
_start:
{
lean_object* v___x_3123_; 
v___x_3123_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(v_upperBound_3103_, v___x_3104_, v_pre_3105_, v_post_3106_, v_usedLetOnly_3107_, v_skipConstInApp_3108_, v_skipInstances_3109_, v_a_3113_, v_b_3114_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_);
return v___x_3123_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___boxed(lean_object** _args){
lean_object* v_upperBound_3124_ = _args[0];
lean_object* v___x_3125_ = _args[1];
lean_object* v_pre_3126_ = _args[2];
lean_object* v_post_3127_ = _args[3];
lean_object* v_usedLetOnly_3128_ = _args[4];
lean_object* v_skipConstInApp_3129_ = _args[5];
lean_object* v_skipInstances_3130_ = _args[6];
lean_object* v___x_3131_ = _args[7];
lean_object* v_inst_3132_ = _args[8];
lean_object* v_R_3133_ = _args[9];
lean_object* v_a_3134_ = _args[10];
lean_object* v_b_3135_ = _args[11];
lean_object* v_c_3136_ = _args[12];
lean_object* v___y_3137_ = _args[13];
lean_object* v___y_3138_ = _args[14];
lean_object* v___y_3139_ = _args[15];
lean_object* v___y_3140_ = _args[16];
lean_object* v___y_3141_ = _args[17];
lean_object* v___y_3142_ = _args[18];
lean_object* v___y_3143_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_3144_; uint8_t v_skipConstInApp_boxed_3145_; uint8_t v_skipInstances_boxed_3146_; lean_object* v_res_3147_; 
v_usedLetOnly_boxed_3144_ = lean_unbox(v_usedLetOnly_3128_);
v_skipConstInApp_boxed_3145_ = lean_unbox(v_skipConstInApp_3129_);
v_skipInstances_boxed_3146_ = lean_unbox(v_skipInstances_3130_);
v_res_3147_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(v_upperBound_3124_, v___x_3125_, v_pre_3126_, v_post_3127_, v_usedLetOnly_boxed_3144_, v_skipConstInApp_boxed_3145_, v_skipInstances_boxed_3146_, v___x_3131_, v_inst_3132_, v_R_3133_, v_a_3134_, v_b_3135_, v_c_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_);
lean_dec(v___y_3142_);
lean_dec_ref(v___y_3141_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec(v___y_3137_);
lean_dec(v___x_3131_);
lean_dec_ref(v___x_3125_);
lean_dec(v_upperBound_3124_);
return v_res_3147_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_3148_, lean_object* v_m_3149_, lean_object* v_a_3150_){
_start:
{
lean_object* v___x_3151_; 
v___x_3151_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(v_m_3149_, v_a_3150_);
return v___x_3151_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b2_3152_, lean_object* v_m_3153_, lean_object* v_a_3154_){
_start:
{
lean_object* v_res_3155_; 
v_res_3155_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4(v_00_u03b2_3152_, v_m_3153_, v_a_3154_);
lean_dec_ref(v_a_3154_);
lean_dec_ref(v_m_3153_);
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_3156_, lean_object* v_name_3157_, uint8_t v_bi_3158_, lean_object* v_type_3159_, lean_object* v_k_3160_, uint8_t v_kind_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_){
_start:
{
lean_object* v___x_3169_; 
v___x_3169_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_name_3157_, v_bi_3158_, v_type_3159_, v_k_3160_, v_kind_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
return v___x_3169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_3170_, lean_object* v_name_3171_, lean_object* v_bi_3172_, lean_object* v_type_3173_, lean_object* v_k_3174_, lean_object* v_kind_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_){
_start:
{
uint8_t v_bi_boxed_3183_; uint8_t v_kind_boxed_3184_; lean_object* v_res_3185_; 
v_bi_boxed_3183_ = lean_unbox(v_bi_3172_);
v_kind_boxed_3184_ = lean_unbox(v_kind_3175_);
v_res_3185_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_3170_, v_name_3171_, v_bi_boxed_3183_, v_type_3173_, v_k_3174_, v_kind_boxed_3184_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
lean_dec(v___y_3179_);
lean_dec_ref(v___y_3178_);
lean_dec(v___y_3177_);
lean_dec(v___y_3176_);
return v_res_3185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10(lean_object* v_00_u03b1_3186_, lean_object* v_name_3187_, lean_object* v_type_3188_, lean_object* v_val_3189_, lean_object* v_k_3190_, uint8_t v_nondep_3191_, uint8_t v_kind_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_){
_start:
{
lean_object* v___x_3200_; 
v___x_3200_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_name_3187_, v_type_3188_, v_val_3189_, v_k_3190_, v_nondep_3191_, v_kind_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_);
return v___x_3200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___boxed(lean_object* v_00_u03b1_3201_, lean_object* v_name_3202_, lean_object* v_type_3203_, lean_object* v_val_3204_, lean_object* v_k_3205_, lean_object* v_nondep_3206_, lean_object* v_kind_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_){
_start:
{
uint8_t v_nondep_boxed_3215_; uint8_t v_kind_boxed_3216_; lean_object* v_res_3217_; 
v_nondep_boxed_3215_ = lean_unbox(v_nondep_3206_);
v_kind_boxed_3216_ = lean_unbox(v_kind_3207_);
v_res_3217_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10(v_00_u03b1_3201_, v_name_3202_, v_type_3203_, v_val_3204_, v_k_3205_, v_nondep_boxed_3215_, v_kind_boxed_3216_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_);
lean_dec(v___y_3213_);
lean_dec_ref(v___y_3212_);
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3210_);
lean_dec(v___y_3209_);
lean_dec(v___y_3208_);
return v_res_3217_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13(lean_object* v_00_u03b1_3218_, lean_object* v_ref_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_){
_start:
{
lean_object* v___x_3225_; 
v___x_3225_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_3219_);
return v___x_3225_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___boxed(lean_object* v_00_u03b1_3226_, lean_object* v_ref_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_){
_start:
{
lean_object* v_res_3233_; 
v_res_3233_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13(v_00_u03b1_3226_, v_ref_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_);
lean_dec(v___y_3231_);
lean_dec_ref(v___y_3230_);
lean_dec(v___y_3229_);
lean_dec_ref(v___y_3228_);
return v_res_3233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9(lean_object* v_00_u03b1_3234_, lean_object* v_x_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_){
_start:
{
lean_object* v___x_3243_; 
v___x_3243_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v_x_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_);
return v___x_3243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___boxed(lean_object* v_00_u03b1_3244_, lean_object* v_x_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_){
_start:
{
lean_object* v_res_3253_; 
v_res_3253_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9(v_00_u03b1_3244_, v_x_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3247_);
lean_dec(v___y_3246_);
return v_res_3253_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10(lean_object* v_00_u03b2_3254_, lean_object* v_m_3255_, lean_object* v_a_3256_, lean_object* v_b_3257_){
_start:
{
lean_object* v___x_3258_; 
v___x_3258_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(v_m_3255_, v_a_3256_, v_b_3257_);
return v___x_3258_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5(lean_object* v_00_u03b2_3259_, lean_object* v_a_3260_, lean_object* v_x_3261_){
_start:
{
lean_object* v___x_3262_; 
v___x_3262_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(v_a_3260_, v_x_3261_);
return v___x_3262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___boxed(lean_object* v_00_u03b2_3263_, lean_object* v_a_3264_, lean_object* v_x_3265_){
_start:
{
lean_object* v_res_3266_; 
v_res_3266_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5(v_00_u03b2_3263_, v_a_3264_, v_x_3265_);
lean_dec(v_x_3265_);
lean_dec_ref(v_a_3264_);
return v_res_3266_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15(lean_object* v_00_u03b2_3267_, lean_object* v_a_3268_, lean_object* v_x_3269_){
_start:
{
uint8_t v___x_3270_; 
v___x_3270_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_a_3268_, v_x_3269_);
return v___x_3270_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___boxed(lean_object* v_00_u03b2_3271_, lean_object* v_a_3272_, lean_object* v_x_3273_){
_start:
{
uint8_t v_res_3274_; lean_object* v_r_3275_; 
v_res_3274_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15(v_00_u03b2_3271_, v_a_3272_, v_x_3273_);
lean_dec(v_x_3273_);
lean_dec_ref(v_a_3272_);
v_r_3275_ = lean_box(v_res_3274_);
return v_r_3275_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16(lean_object* v_00_u03b2_3276_, lean_object* v_data_3277_){
_start:
{
lean_object* v___x_3278_; 
v___x_3278_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(v_data_3277_);
return v___x_3278_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17(lean_object* v_00_u03b2_3279_, lean_object* v_a_3280_, lean_object* v_b_3281_, lean_object* v_x_3282_){
_start:
{
lean_object* v___x_3283_; 
v___x_3283_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(v_a_3280_, v_b_3281_, v_x_3282_);
return v___x_3283_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17(lean_object* v_00_u03b2_3284_, lean_object* v_i_3285_, lean_object* v_source_3286_, lean_object* v_target_3287_){
_start:
{
lean_object* v___x_3288_; 
v___x_3288_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v_i_3285_, v_source_3286_, v_target_3287_);
return v___x_3288_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18(lean_object* v_00_u03b2_3289_, lean_object* v_x_3290_, lean_object* v_x_3291_){
_start:
{
lean_object* v___x_3292_; 
v___x_3292_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_x_3290_, v_x_3291_);
return v___x_3292_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(lean_object* v_mvarId_3293_, lean_object* v_x_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_){
_start:
{
lean_object* v___x_3300_; 
v___x_3300_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3293_, v_x_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_);
if (lean_obj_tag(v___x_3300_) == 0)
{
lean_object* v_a_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3308_; 
v_a_3301_ = lean_ctor_get(v___x_3300_, 0);
v_isSharedCheck_3308_ = !lean_is_exclusive(v___x_3300_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3303_ = v___x_3300_;
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_a_3301_);
lean_dec(v___x_3300_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
lean_object* v___x_3306_; 
if (v_isShared_3304_ == 0)
{
v___x_3306_ = v___x_3303_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v_a_3301_);
v___x_3306_ = v_reuseFailAlloc_3307_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
return v___x_3306_;
}
}
}
else
{
lean_object* v_a_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3316_; 
v_a_3309_ = lean_ctor_get(v___x_3300_, 0);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___x_3300_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3311_ = v___x_3300_;
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_a_3309_);
lean_dec(v___x_3300_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3314_; 
if (v_isShared_3312_ == 0)
{
v___x_3314_ = v___x_3311_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_a_3309_);
v___x_3314_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
return v___x_3314_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg___boxed(lean_object* v_mvarId_3317_, lean_object* v_x_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_){
_start:
{
lean_object* v_res_3324_; 
v_res_3324_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(v_mvarId_3317_, v_x_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
lean_dec(v___y_3322_);
lean_dec_ref(v___y_3321_);
lean_dec(v___y_3320_);
lean_dec_ref(v___y_3319_);
return v_res_3324_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3(lean_object* v_00_u03b1_3325_, lean_object* v_mvarId_3326_, lean_object* v_x_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_){
_start:
{
lean_object* v___x_3333_; 
v___x_3333_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(v_mvarId_3326_, v_x_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_);
return v___x_3333_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___boxed(lean_object* v_00_u03b1_3334_, lean_object* v_mvarId_3335_, lean_object* v_x_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3(v_00_u03b1_3334_, v_mvarId_3335_, v_x_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(uint8_t v_elimTrivial_3343_, lean_object* v_as_3344_, size_t v_sz_3345_, size_t v_i_3346_, lean_object* v_b_3347_){
_start:
{
uint8_t v___x_3349_; 
v___x_3349_ = lean_usize_dec_lt(v_i_3346_, v_sz_3345_);
if (v___x_3349_ == 0)
{
lean_object* v___x_3350_; 
v___x_3350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3350_, 0, v_b_3347_);
return v___x_3350_;
}
else
{
lean_object* v_snd_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3398_; 
v_snd_3351_ = lean_ctor_get(v_b_3347_, 1);
v_isSharedCheck_3398_ = !lean_is_exclusive(v_b_3347_);
if (v_isSharedCheck_3398_ == 0)
{
lean_object* v_unused_3399_; 
v_unused_3399_ = lean_ctor_get(v_b_3347_, 0);
lean_dec(v_unused_3399_);
v___x_3353_ = v_b_3347_;
v_isShared_3354_ = v_isSharedCheck_3398_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_snd_3351_);
lean_dec(v_b_3347_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3398_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v___x_3355_; lean_object* v_a_3357_; lean_object* v_a_3364_; 
v___x_3355_ = lean_box(0);
v_a_3364_ = lean_array_uget_borrowed(v_as_3344_, v_i_3346_);
if (lean_obj_tag(v_a_3364_) == 0)
{
v_a_3357_ = v_snd_3351_;
goto v___jp_3356_;
}
else
{
lean_object* v_val_3365_; lean_object* v_fst_3366_; lean_object* v_snd_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3397_; 
v_val_3365_ = lean_ctor_get(v_a_3364_, 0);
v_fst_3366_ = lean_ctor_get(v_snd_3351_, 0);
v_snd_3367_ = lean_ctor_get(v_snd_3351_, 1);
v_isSharedCheck_3397_ = !lean_is_exclusive(v_snd_3351_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3369_ = v_snd_3351_;
v_isShared_3370_ = v_isSharedCheck_3397_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_snd_3367_);
lean_inc(v_fst_3366_);
lean_dec(v_snd_3351_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3397_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
uint8_t v___x_3371_; lean_object* v___x_3372_; 
v___x_3371_ = 0;
v___x_3372_ = l_Lean_LocalDecl_value_x3f(v_val_3365_, v___x_3371_);
if (lean_obj_tag(v___x_3372_) == 1)
{
lean_object* v_val_3373_; lean_object* v___x_3374_; 
v_val_3373_ = lean_ctor_get(v___x_3372_, 0);
lean_inc(v_val_3373_);
lean_dec_ref_known(v___x_3372_, 1);
v___x_3374_ = l_Lean_LocalDecl_type(v_val_3365_);
if (lean_obj_tag(v___x_3374_) == 10)
{
lean_object* v_data_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; uint8_t v___x_3379_; uint8_t v___x_3380_; 
v_data_3375_ = lean_ctor_get(v___x_3374_, 0);
lean_inc(v_data_3375_);
lean_dec_ref_known(v___x_3374_, 2);
v___x_3376_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_3377_ = lean_unsigned_to_nat(2u);
v___x_3378_ = l_Lean_KVMap_getNat(v_data_3375_, v___x_3376_, v___x_3377_);
lean_dec(v_data_3375_);
v___x_3379_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3378_);
lean_dec(v___x_3378_);
v___x_3380_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3379_, v_val_3373_, v_elimTrivial_3343_);
if (v___x_3380_ == 0)
{
lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3386_; 
v___x_3381_ = l_Lean_LocalDecl_fvarId(v_val_3365_);
v___x_3382_ = l_Lean_mkFVar(v___x_3381_);
v___x_3383_ = lean_array_push(v_fst_3366_, v___x_3382_);
v___x_3384_ = lean_array_push(v_snd_3367_, v_val_3373_);
if (v_isShared_3370_ == 0)
{
lean_ctor_set(v___x_3369_, 1, v___x_3384_);
lean_ctor_set(v___x_3369_, 0, v___x_3383_);
v___x_3386_ = v___x_3369_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v___x_3383_);
lean_ctor_set(v_reuseFailAlloc_3387_, 1, v___x_3384_);
v___x_3386_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
v_a_3357_ = v___x_3386_;
goto v___jp_3356_;
}
}
else
{
lean_object* v___x_3389_; 
lean_dec(v_val_3373_);
if (v_isShared_3370_ == 0)
{
v___x_3389_ = v___x_3369_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v_fst_3366_);
lean_ctor_set(v_reuseFailAlloc_3390_, 1, v_snd_3367_);
v___x_3389_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
v_a_3357_ = v___x_3389_;
goto v___jp_3356_;
}
}
}
else
{
lean_object* v___x_3392_; 
lean_dec_ref(v___x_3374_);
lean_dec(v_val_3373_);
if (v_isShared_3370_ == 0)
{
v___x_3392_ = v___x_3369_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_fst_3366_);
lean_ctor_set(v_reuseFailAlloc_3393_, 1, v_snd_3367_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
v_a_3357_ = v___x_3392_;
goto v___jp_3356_;
}
}
}
else
{
lean_object* v___x_3395_; 
lean_dec(v___x_3372_);
if (v_isShared_3370_ == 0)
{
v___x_3395_ = v___x_3369_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v_fst_3366_);
lean_ctor_set(v_reuseFailAlloc_3396_, 1, v_snd_3367_);
v___x_3395_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
v_a_3357_ = v___x_3395_;
goto v___jp_3356_;
}
}
}
}
v___jp_3356_:
{
lean_object* v___x_3359_; 
if (v_isShared_3354_ == 0)
{
lean_ctor_set(v___x_3353_, 1, v_a_3357_);
lean_ctor_set(v___x_3353_, 0, v___x_3355_);
v___x_3359_ = v___x_3353_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v___x_3355_);
lean_ctor_set(v_reuseFailAlloc_3363_, 1, v_a_3357_);
v___x_3359_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
size_t v___x_3360_; size_t v___x_3361_; 
v___x_3360_ = ((size_t)1ULL);
v___x_3361_ = lean_usize_add(v_i_3346_, v___x_3360_);
v_i_3346_ = v___x_3361_;
v_b_3347_ = v___x_3359_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_elimTrivial_3400_, lean_object* v_as_3401_, lean_object* v_sz_3402_, lean_object* v_i_3403_, lean_object* v_b_3404_, lean_object* v___y_3405_){
_start:
{
uint8_t v_elimTrivial_boxed_3406_; size_t v_sz_boxed_3407_; size_t v_i_boxed_3408_; lean_object* v_res_3409_; 
v_elimTrivial_boxed_3406_ = lean_unbox(v_elimTrivial_3400_);
v_sz_boxed_3407_ = lean_unbox_usize(v_sz_3402_);
lean_dec(v_sz_3402_);
v_i_boxed_3408_ = lean_unbox_usize(v_i_3403_);
lean_dec(v_i_3403_);
v_res_3409_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_boxed_3406_, v_as_3401_, v_sz_boxed_3407_, v_i_boxed_3408_, v_b_3404_);
lean_dec_ref(v_as_3401_);
return v_res_3409_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(uint8_t v_elimTrivial_3410_, lean_object* v_as_3411_, size_t v_sz_3412_, size_t v_i_3413_, lean_object* v_b_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_){
_start:
{
uint8_t v___x_3420_; 
v___x_3420_ = lean_usize_dec_lt(v_i_3413_, v_sz_3412_);
if (v___x_3420_ == 0)
{
lean_object* v___x_3421_; 
v___x_3421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3421_, 0, v_b_3414_);
return v___x_3421_;
}
else
{
lean_object* v_snd_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3469_; 
v_snd_3422_ = lean_ctor_get(v_b_3414_, 1);
v_isSharedCheck_3469_ = !lean_is_exclusive(v_b_3414_);
if (v_isSharedCheck_3469_ == 0)
{
lean_object* v_unused_3470_; 
v_unused_3470_ = lean_ctor_get(v_b_3414_, 0);
lean_dec(v_unused_3470_);
v___x_3424_ = v_b_3414_;
v_isShared_3425_ = v_isSharedCheck_3469_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_snd_3422_);
lean_dec(v_b_3414_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3469_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v___x_3426_; lean_object* v_a_3428_; lean_object* v_a_3435_; 
v___x_3426_ = lean_box(0);
v_a_3435_ = lean_array_uget_borrowed(v_as_3411_, v_i_3413_);
if (lean_obj_tag(v_a_3435_) == 0)
{
v_a_3428_ = v_snd_3422_;
goto v___jp_3427_;
}
else
{
lean_object* v_val_3436_; lean_object* v_fst_3437_; lean_object* v_snd_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3468_; 
v_val_3436_ = lean_ctor_get(v_a_3435_, 0);
v_fst_3437_ = lean_ctor_get(v_snd_3422_, 0);
v_snd_3438_ = lean_ctor_get(v_snd_3422_, 1);
v_isSharedCheck_3468_ = !lean_is_exclusive(v_snd_3422_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3440_ = v_snd_3422_;
v_isShared_3441_ = v_isSharedCheck_3468_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_snd_3438_);
lean_inc(v_fst_3437_);
lean_dec(v_snd_3422_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3468_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
uint8_t v___x_3442_; lean_object* v___x_3443_; 
v___x_3442_ = 0;
v___x_3443_ = l_Lean_LocalDecl_value_x3f(v_val_3436_, v___x_3442_);
if (lean_obj_tag(v___x_3443_) == 1)
{
lean_object* v_val_3444_; lean_object* v___x_3445_; 
v_val_3444_ = lean_ctor_get(v___x_3443_, 0);
lean_inc(v_val_3444_);
lean_dec_ref_known(v___x_3443_, 1);
v___x_3445_ = l_Lean_LocalDecl_type(v_val_3436_);
if (lean_obj_tag(v___x_3445_) == 10)
{
lean_object* v_data_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; uint8_t v___x_3450_; uint8_t v___x_3451_; 
v_data_3446_ = lean_ctor_get(v___x_3445_, 0);
lean_inc(v_data_3446_);
lean_dec_ref_known(v___x_3445_, 2);
v___x_3447_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_3448_ = lean_unsigned_to_nat(2u);
v___x_3449_ = l_Lean_KVMap_getNat(v_data_3446_, v___x_3447_, v___x_3448_);
lean_dec(v_data_3446_);
v___x_3450_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3449_);
lean_dec(v___x_3449_);
v___x_3451_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3450_, v_val_3444_, v_elimTrivial_3410_);
if (v___x_3451_ == 0)
{
lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3457_; 
v___x_3452_ = l_Lean_LocalDecl_fvarId(v_val_3436_);
v___x_3453_ = l_Lean_mkFVar(v___x_3452_);
v___x_3454_ = lean_array_push(v_fst_3437_, v___x_3453_);
v___x_3455_ = lean_array_push(v_snd_3438_, v_val_3444_);
if (v_isShared_3441_ == 0)
{
lean_ctor_set(v___x_3440_, 1, v___x_3455_);
lean_ctor_set(v___x_3440_, 0, v___x_3454_);
v___x_3457_ = v___x_3440_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v___x_3454_);
lean_ctor_set(v_reuseFailAlloc_3458_, 1, v___x_3455_);
v___x_3457_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
v_a_3428_ = v___x_3457_;
goto v___jp_3427_;
}
}
else
{
lean_object* v___x_3460_; 
lean_dec(v_val_3444_);
if (v_isShared_3441_ == 0)
{
v___x_3460_ = v___x_3440_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_fst_3437_);
lean_ctor_set(v_reuseFailAlloc_3461_, 1, v_snd_3438_);
v___x_3460_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
v_a_3428_ = v___x_3460_;
goto v___jp_3427_;
}
}
}
else
{
lean_object* v___x_3463_; 
lean_dec_ref(v___x_3445_);
lean_dec(v_val_3444_);
if (v_isShared_3441_ == 0)
{
v___x_3463_ = v___x_3440_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_fst_3437_);
lean_ctor_set(v_reuseFailAlloc_3464_, 1, v_snd_3438_);
v___x_3463_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
v_a_3428_ = v___x_3463_;
goto v___jp_3427_;
}
}
}
else
{
lean_object* v___x_3466_; 
lean_dec(v___x_3443_);
if (v_isShared_3441_ == 0)
{
v___x_3466_ = v___x_3440_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_fst_3437_);
lean_ctor_set(v_reuseFailAlloc_3467_, 1, v_snd_3438_);
v___x_3466_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
v_a_3428_ = v___x_3466_;
goto v___jp_3427_;
}
}
}
}
v___jp_3427_:
{
lean_object* v___x_3430_; 
if (v_isShared_3425_ == 0)
{
lean_ctor_set(v___x_3424_, 1, v_a_3428_);
lean_ctor_set(v___x_3424_, 0, v___x_3426_);
v___x_3430_ = v___x_3424_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v___x_3426_);
lean_ctor_set(v_reuseFailAlloc_3434_, 1, v_a_3428_);
v___x_3430_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
size_t v___x_3431_; size_t v___x_3432_; lean_object* v___x_3433_; 
v___x_3431_ = ((size_t)1ULL);
v___x_3432_ = lean_usize_add(v_i_3413_, v___x_3431_);
v___x_3433_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_3410_, v_as_3411_, v_sz_3412_, v___x_3432_, v___x_3430_);
return v___x_3433_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1___boxed(lean_object* v_elimTrivial_3471_, lean_object* v_as_3472_, lean_object* v_sz_3473_, lean_object* v_i_3474_, lean_object* v_b_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_){
_start:
{
uint8_t v_elimTrivial_boxed_3481_; size_t v_sz_boxed_3482_; size_t v_i_boxed_3483_; lean_object* v_res_3484_; 
v_elimTrivial_boxed_3481_ = lean_unbox(v_elimTrivial_3471_);
v_sz_boxed_3482_ = lean_unbox_usize(v_sz_3473_);
lean_dec(v_sz_3473_);
v_i_boxed_3483_ = lean_unbox_usize(v_i_3474_);
lean_dec(v_i_3474_);
v_res_3484_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(v_elimTrivial_boxed_3481_, v_as_3472_, v_sz_boxed_3482_, v_i_boxed_3483_, v_b_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
lean_dec(v___y_3479_);
lean_dec_ref(v___y_3478_);
lean_dec(v___y_3477_);
lean_dec_ref(v___y_3476_);
lean_dec_ref(v_as_3472_);
return v_res_3484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(uint8_t v_elimTrivial_3485_, lean_object* v_as_3486_, size_t v_sz_3487_, size_t v_i_3488_, lean_object* v_b_3489_){
_start:
{
uint8_t v___x_3491_; 
v___x_3491_ = lean_usize_dec_lt(v_i_3488_, v_sz_3487_);
if (v___x_3491_ == 0)
{
lean_object* v___x_3492_; 
v___x_3492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3492_, 0, v_b_3489_);
return v___x_3492_;
}
else
{
lean_object* v_snd_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3540_; 
v_snd_3493_ = lean_ctor_get(v_b_3489_, 1);
v_isSharedCheck_3540_ = !lean_is_exclusive(v_b_3489_);
if (v_isSharedCheck_3540_ == 0)
{
lean_object* v_unused_3541_; 
v_unused_3541_ = lean_ctor_get(v_b_3489_, 0);
lean_dec(v_unused_3541_);
v___x_3495_ = v_b_3489_;
v_isShared_3496_ = v_isSharedCheck_3540_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_snd_3493_);
lean_dec(v_b_3489_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3540_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v___x_3497_; lean_object* v_a_3499_; lean_object* v_a_3506_; 
v___x_3497_ = lean_box(0);
v_a_3506_ = lean_array_uget_borrowed(v_as_3486_, v_i_3488_);
if (lean_obj_tag(v_a_3506_) == 0)
{
v_a_3499_ = v_snd_3493_;
goto v___jp_3498_;
}
else
{
lean_object* v_val_3507_; lean_object* v_fst_3508_; lean_object* v_snd_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3539_; 
v_val_3507_ = lean_ctor_get(v_a_3506_, 0);
v_fst_3508_ = lean_ctor_get(v_snd_3493_, 0);
v_snd_3509_ = lean_ctor_get(v_snd_3493_, 1);
v_isSharedCheck_3539_ = !lean_is_exclusive(v_snd_3493_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3511_ = v_snd_3493_;
v_isShared_3512_ = v_isSharedCheck_3539_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_snd_3509_);
lean_inc(v_fst_3508_);
lean_dec(v_snd_3493_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3539_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
uint8_t v___x_3513_; lean_object* v___x_3514_; 
v___x_3513_ = 0;
v___x_3514_ = l_Lean_LocalDecl_value_x3f(v_val_3507_, v___x_3513_);
if (lean_obj_tag(v___x_3514_) == 1)
{
lean_object* v_val_3515_; lean_object* v___x_3516_; 
v_val_3515_ = lean_ctor_get(v___x_3514_, 0);
lean_inc(v_val_3515_);
lean_dec_ref_known(v___x_3514_, 1);
v___x_3516_ = l_Lean_LocalDecl_type(v_val_3507_);
if (lean_obj_tag(v___x_3516_) == 10)
{
lean_object* v_data_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; uint8_t v___x_3521_; uint8_t v___x_3522_; 
v_data_3517_ = lean_ctor_get(v___x_3516_, 0);
lean_inc(v_data_3517_);
lean_dec_ref_known(v___x_3516_, 2);
v___x_3518_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_3519_ = lean_unsigned_to_nat(2u);
v___x_3520_ = l_Lean_KVMap_getNat(v_data_3517_, v___x_3518_, v___x_3519_);
lean_dec(v_data_3517_);
v___x_3521_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3520_);
lean_dec(v___x_3520_);
v___x_3522_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3521_, v_val_3515_, v_elimTrivial_3485_);
if (v___x_3522_ == 0)
{
lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3528_; 
v___x_3523_ = l_Lean_LocalDecl_fvarId(v_val_3507_);
v___x_3524_ = l_Lean_mkFVar(v___x_3523_);
v___x_3525_ = lean_array_push(v_fst_3508_, v___x_3524_);
v___x_3526_ = lean_array_push(v_snd_3509_, v_val_3515_);
if (v_isShared_3512_ == 0)
{
lean_ctor_set(v___x_3511_, 1, v___x_3526_);
lean_ctor_set(v___x_3511_, 0, v___x_3525_);
v___x_3528_ = v___x_3511_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v___x_3525_);
lean_ctor_set(v_reuseFailAlloc_3529_, 1, v___x_3526_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
v_a_3499_ = v___x_3528_;
goto v___jp_3498_;
}
}
else
{
lean_object* v___x_3531_; 
lean_dec(v_val_3515_);
if (v_isShared_3512_ == 0)
{
v___x_3531_ = v___x_3511_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v_fst_3508_);
lean_ctor_set(v_reuseFailAlloc_3532_, 1, v_snd_3509_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
v_a_3499_ = v___x_3531_;
goto v___jp_3498_;
}
}
}
else
{
lean_object* v___x_3534_; 
lean_dec_ref(v___x_3516_);
lean_dec(v_val_3515_);
if (v_isShared_3512_ == 0)
{
v___x_3534_ = v___x_3511_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_fst_3508_);
lean_ctor_set(v_reuseFailAlloc_3535_, 1, v_snd_3509_);
v___x_3534_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
v_a_3499_ = v___x_3534_;
goto v___jp_3498_;
}
}
}
else
{
lean_object* v___x_3537_; 
lean_dec(v___x_3514_);
if (v_isShared_3512_ == 0)
{
v___x_3537_ = v___x_3511_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_fst_3508_);
lean_ctor_set(v_reuseFailAlloc_3538_, 1, v_snd_3509_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
v_a_3499_ = v___x_3537_;
goto v___jp_3498_;
}
}
}
}
v___jp_3498_:
{
lean_object* v___x_3501_; 
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 1, v_a_3499_);
lean_ctor_set(v___x_3495_, 0, v___x_3497_);
v___x_3501_ = v___x_3495_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v___x_3497_);
lean_ctor_set(v_reuseFailAlloc_3505_, 1, v_a_3499_);
v___x_3501_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
size_t v___x_3502_; size_t v___x_3503_; 
v___x_3502_ = ((size_t)1ULL);
v___x_3503_ = lean_usize_add(v_i_3488_, v___x_3502_);
v_i_3488_ = v___x_3503_;
v_b_3489_ = v___x_3501_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg___boxed(lean_object* v_elimTrivial_3542_, lean_object* v_as_3543_, lean_object* v_sz_3544_, lean_object* v_i_3545_, lean_object* v_b_3546_, lean_object* v___y_3547_){
_start:
{
uint8_t v_elimTrivial_boxed_3548_; size_t v_sz_boxed_3549_; size_t v_i_boxed_3550_; lean_object* v_res_3551_; 
v_elimTrivial_boxed_3548_ = lean_unbox(v_elimTrivial_3542_);
v_sz_boxed_3549_ = lean_unbox_usize(v_sz_3544_);
lean_dec(v_sz_3544_);
v_i_boxed_3550_ = lean_unbox_usize(v_i_3545_);
lean_dec(v_i_3545_);
v_res_3551_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_boxed_3548_, v_as_3543_, v_sz_boxed_3549_, v_i_boxed_3550_, v_b_3546_);
lean_dec_ref(v_as_3543_);
return v_res_3551_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(uint8_t v_elimTrivial_3552_, lean_object* v_as_3553_, size_t v_sz_3554_, size_t v_i_3555_, lean_object* v_b_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_){
_start:
{
uint8_t v___x_3562_; 
v___x_3562_ = lean_usize_dec_lt(v_i_3555_, v_sz_3554_);
if (v___x_3562_ == 0)
{
lean_object* v___x_3563_; 
v___x_3563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3563_, 0, v_b_3556_);
return v___x_3563_;
}
else
{
lean_object* v_snd_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3611_; 
v_snd_3564_ = lean_ctor_get(v_b_3556_, 1);
v_isSharedCheck_3611_ = !lean_is_exclusive(v_b_3556_);
if (v_isSharedCheck_3611_ == 0)
{
lean_object* v_unused_3612_; 
v_unused_3612_ = lean_ctor_get(v_b_3556_, 0);
lean_dec(v_unused_3612_);
v___x_3566_ = v_b_3556_;
v_isShared_3567_ = v_isSharedCheck_3611_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_snd_3564_);
lean_dec(v_b_3556_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3611_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
lean_object* v___x_3568_; lean_object* v_a_3570_; lean_object* v_a_3577_; 
v___x_3568_ = lean_box(0);
v_a_3577_ = lean_array_uget_borrowed(v_as_3553_, v_i_3555_);
if (lean_obj_tag(v_a_3577_) == 0)
{
v_a_3570_ = v_snd_3564_;
goto v___jp_3569_;
}
else
{
lean_object* v_val_3578_; lean_object* v_fst_3579_; lean_object* v_snd_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3610_; 
v_val_3578_ = lean_ctor_get(v_a_3577_, 0);
v_fst_3579_ = lean_ctor_get(v_snd_3564_, 0);
v_snd_3580_ = lean_ctor_get(v_snd_3564_, 1);
v_isSharedCheck_3610_ = !lean_is_exclusive(v_snd_3564_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3582_ = v_snd_3564_;
v_isShared_3583_ = v_isSharedCheck_3610_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_snd_3580_);
lean_inc(v_fst_3579_);
lean_dec(v_snd_3564_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3610_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
uint8_t v___x_3584_; lean_object* v___x_3585_; 
v___x_3584_ = 0;
v___x_3585_ = l_Lean_LocalDecl_value_x3f(v_val_3578_, v___x_3584_);
if (lean_obj_tag(v___x_3585_) == 1)
{
lean_object* v_val_3586_; lean_object* v___x_3587_; 
v_val_3586_ = lean_ctor_get(v___x_3585_, 0);
lean_inc(v_val_3586_);
lean_dec_ref_known(v___x_3585_, 1);
v___x_3587_ = l_Lean_LocalDecl_type(v_val_3578_);
if (lean_obj_tag(v___x_3587_) == 10)
{
lean_object* v_data_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; uint8_t v___x_3592_; uint8_t v___x_3593_; 
v_data_3588_ = lean_ctor_get(v___x_3587_, 0);
lean_inc(v_data_3588_);
lean_dec_ref_known(v___x_3587_, 2);
v___x_3589_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_3590_ = lean_unsigned_to_nat(2u);
v___x_3591_ = l_Lean_KVMap_getNat(v_data_3588_, v___x_3589_, v___x_3590_);
lean_dec(v_data_3588_);
v___x_3592_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3591_);
lean_dec(v___x_3591_);
v___x_3593_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3592_, v_val_3586_, v_elimTrivial_3552_);
if (v___x_3593_ == 0)
{
lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3599_; 
v___x_3594_ = l_Lean_LocalDecl_fvarId(v_val_3578_);
v___x_3595_ = l_Lean_mkFVar(v___x_3594_);
v___x_3596_ = lean_array_push(v_fst_3579_, v___x_3595_);
v___x_3597_ = lean_array_push(v_snd_3580_, v_val_3586_);
if (v_isShared_3583_ == 0)
{
lean_ctor_set(v___x_3582_, 1, v___x_3597_);
lean_ctor_set(v___x_3582_, 0, v___x_3596_);
v___x_3599_ = v___x_3582_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v___x_3596_);
lean_ctor_set(v_reuseFailAlloc_3600_, 1, v___x_3597_);
v___x_3599_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
v_a_3570_ = v___x_3599_;
goto v___jp_3569_;
}
}
else
{
lean_object* v___x_3602_; 
lean_dec(v_val_3586_);
if (v_isShared_3583_ == 0)
{
v___x_3602_ = v___x_3582_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v_fst_3579_);
lean_ctor_set(v_reuseFailAlloc_3603_, 1, v_snd_3580_);
v___x_3602_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
v_a_3570_ = v___x_3602_;
goto v___jp_3569_;
}
}
}
else
{
lean_object* v___x_3605_; 
lean_dec_ref(v___x_3587_);
lean_dec(v_val_3586_);
if (v_isShared_3583_ == 0)
{
v___x_3605_ = v___x_3582_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v_fst_3579_);
lean_ctor_set(v_reuseFailAlloc_3606_, 1, v_snd_3580_);
v___x_3605_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
v_a_3570_ = v___x_3605_;
goto v___jp_3569_;
}
}
}
else
{
lean_object* v___x_3608_; 
lean_dec(v___x_3585_);
if (v_isShared_3583_ == 0)
{
v___x_3608_ = v___x_3582_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v_fst_3579_);
lean_ctor_set(v_reuseFailAlloc_3609_, 1, v_snd_3580_);
v___x_3608_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
v_a_3570_ = v___x_3608_;
goto v___jp_3569_;
}
}
}
}
v___jp_3569_:
{
lean_object* v___x_3572_; 
if (v_isShared_3567_ == 0)
{
lean_ctor_set(v___x_3566_, 1, v_a_3570_);
lean_ctor_set(v___x_3566_, 0, v___x_3568_);
v___x_3572_ = v___x_3566_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v___x_3568_);
lean_ctor_set(v_reuseFailAlloc_3576_, 1, v_a_3570_);
v___x_3572_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
size_t v___x_3573_; size_t v___x_3574_; lean_object* v___x_3575_; 
v___x_3573_ = ((size_t)1ULL);
v___x_3574_ = lean_usize_add(v_i_3555_, v___x_3573_);
v___x_3575_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_3552_, v_as_3553_, v_sz_3554_, v___x_3574_, v___x_3572_);
return v___x_3575_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3___boxed(lean_object* v_elimTrivial_3613_, lean_object* v_as_3614_, lean_object* v_sz_3615_, lean_object* v_i_3616_, lean_object* v_b_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_){
_start:
{
uint8_t v_elimTrivial_boxed_3623_; size_t v_sz_boxed_3624_; size_t v_i_boxed_3625_; lean_object* v_res_3626_; 
v_elimTrivial_boxed_3623_ = lean_unbox(v_elimTrivial_3613_);
v_sz_boxed_3624_ = lean_unbox_usize(v_sz_3615_);
lean_dec(v_sz_3615_);
v_i_boxed_3625_ = lean_unbox_usize(v_i_3616_);
lean_dec(v_i_3616_);
v_res_3626_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(v_elimTrivial_boxed_3623_, v_as_3614_, v_sz_boxed_3624_, v_i_boxed_3625_, v_b_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_);
lean_dec(v___y_3621_);
lean_dec_ref(v___y_3620_);
lean_dec(v___y_3619_);
lean_dec_ref(v___y_3618_);
lean_dec_ref(v_as_3614_);
return v_res_3626_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(lean_object* v_init_3627_, uint8_t v_elimTrivial_3628_, lean_object* v_n_3629_, lean_object* v_b_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_){
_start:
{
if (lean_obj_tag(v_n_3629_) == 0)
{
lean_object* v_cs_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; size_t v_sz_3639_; size_t v___x_3640_; lean_object* v___x_3641_; 
v_cs_3636_ = lean_ctor_get(v_n_3629_, 0);
v___x_3637_ = lean_box(0);
v___x_3638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3638_, 0, v___x_3637_);
lean_ctor_set(v___x_3638_, 1, v_b_3630_);
v_sz_3639_ = lean_array_size(v_cs_3636_);
v___x_3640_ = ((size_t)0ULL);
v___x_3641_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(v_init_3627_, v_elimTrivial_3628_, v_cs_3636_, v_sz_3639_, v___x_3640_, v___x_3638_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_);
if (lean_obj_tag(v___x_3641_) == 0)
{
lean_object* v_a_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3656_; 
v_a_3642_ = lean_ctor_get(v___x_3641_, 0);
v_isSharedCheck_3656_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3656_ == 0)
{
v___x_3644_ = v___x_3641_;
v_isShared_3645_ = v_isSharedCheck_3656_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_a_3642_);
lean_dec(v___x_3641_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3656_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v_fst_3646_; 
v_fst_3646_ = lean_ctor_get(v_a_3642_, 0);
if (lean_obj_tag(v_fst_3646_) == 0)
{
lean_object* v_snd_3647_; lean_object* v___x_3648_; lean_object* v___x_3650_; 
v_snd_3647_ = lean_ctor_get(v_a_3642_, 1);
lean_inc(v_snd_3647_);
lean_dec(v_a_3642_);
v___x_3648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3648_, 0, v_snd_3647_);
if (v_isShared_3645_ == 0)
{
lean_ctor_set(v___x_3644_, 0, v___x_3648_);
v___x_3650_ = v___x_3644_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v___x_3648_);
v___x_3650_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
return v___x_3650_;
}
}
else
{
lean_object* v_val_3652_; lean_object* v___x_3654_; 
lean_inc_ref(v_fst_3646_);
lean_dec(v_a_3642_);
v_val_3652_ = lean_ctor_get(v_fst_3646_, 0);
lean_inc(v_val_3652_);
lean_dec_ref_known(v_fst_3646_, 1);
if (v_isShared_3645_ == 0)
{
lean_ctor_set(v___x_3644_, 0, v_val_3652_);
v___x_3654_ = v___x_3644_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3655_; 
v_reuseFailAlloc_3655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3655_, 0, v_val_3652_);
v___x_3654_ = v_reuseFailAlloc_3655_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
return v___x_3654_;
}
}
}
}
else
{
lean_object* v_a_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3664_; 
v_a_3657_ = lean_ctor_get(v___x_3641_, 0);
v_isSharedCheck_3664_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3664_ == 0)
{
v___x_3659_ = v___x_3641_;
v_isShared_3660_ = v_isSharedCheck_3664_;
goto v_resetjp_3658_;
}
else
{
lean_inc(v_a_3657_);
lean_dec(v___x_3641_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3664_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
lean_object* v___x_3662_; 
if (v_isShared_3660_ == 0)
{
v___x_3662_ = v___x_3659_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_a_3657_);
v___x_3662_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
return v___x_3662_;
}
}
}
}
else
{
lean_object* v_vs_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; size_t v_sz_3668_; size_t v___x_3669_; lean_object* v___x_3670_; 
v_vs_3665_ = lean_ctor_get(v_n_3629_, 0);
v___x_3666_ = lean_box(0);
v___x_3667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3667_, 0, v___x_3666_);
lean_ctor_set(v___x_3667_, 1, v_b_3630_);
v_sz_3668_ = lean_array_size(v_vs_3665_);
v___x_3669_ = ((size_t)0ULL);
v___x_3670_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(v_elimTrivial_3628_, v_vs_3665_, v_sz_3668_, v___x_3669_, v___x_3667_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_);
if (lean_obj_tag(v___x_3670_) == 0)
{
lean_object* v_a_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3685_; 
v_a_3671_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3673_ = v___x_3670_;
v_isShared_3674_ = v_isSharedCheck_3685_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_a_3671_);
lean_dec(v___x_3670_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3685_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
lean_object* v_fst_3675_; 
v_fst_3675_ = lean_ctor_get(v_a_3671_, 0);
if (lean_obj_tag(v_fst_3675_) == 0)
{
lean_object* v_snd_3676_; lean_object* v___x_3677_; lean_object* v___x_3679_; 
v_snd_3676_ = lean_ctor_get(v_a_3671_, 1);
lean_inc(v_snd_3676_);
lean_dec(v_a_3671_);
v___x_3677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3677_, 0, v_snd_3676_);
if (v_isShared_3674_ == 0)
{
lean_ctor_set(v___x_3673_, 0, v___x_3677_);
v___x_3679_ = v___x_3673_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v___x_3677_);
v___x_3679_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
return v___x_3679_;
}
}
else
{
lean_object* v_val_3681_; lean_object* v___x_3683_; 
lean_inc_ref(v_fst_3675_);
lean_dec(v_a_3671_);
v_val_3681_ = lean_ctor_get(v_fst_3675_, 0);
lean_inc(v_val_3681_);
lean_dec_ref_known(v_fst_3675_, 1);
if (v_isShared_3674_ == 0)
{
lean_ctor_set(v___x_3673_, 0, v_val_3681_);
v___x_3683_ = v___x_3673_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_val_3681_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
}
}
}
}
else
{
lean_object* v_a_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3693_; 
v_a_3686_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3693_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3688_ = v___x_3670_;
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_a_3686_);
lean_dec(v___x_3670_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
lean_object* v___x_3691_; 
if (v_isShared_3689_ == 0)
{
v___x_3691_ = v___x_3688_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_a_3686_);
v___x_3691_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
return v___x_3691_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(lean_object* v_init_3694_, uint8_t v_elimTrivial_3695_, lean_object* v_as_3696_, size_t v_sz_3697_, size_t v_i_3698_, lean_object* v_b_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_){
_start:
{
uint8_t v___x_3705_; 
v___x_3705_ = lean_usize_dec_lt(v_i_3698_, v_sz_3697_);
if (v___x_3705_ == 0)
{
lean_object* v___x_3706_; 
v___x_3706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3706_, 0, v_b_3699_);
return v___x_3706_;
}
else
{
lean_object* v_snd_3707_; lean_object* v___x_3709_; uint8_t v_isShared_3710_; uint8_t v_isSharedCheck_3741_; 
v_snd_3707_ = lean_ctor_get(v_b_3699_, 1);
v_isSharedCheck_3741_ = !lean_is_exclusive(v_b_3699_);
if (v_isSharedCheck_3741_ == 0)
{
lean_object* v_unused_3742_; 
v_unused_3742_ = lean_ctor_get(v_b_3699_, 0);
lean_dec(v_unused_3742_);
v___x_3709_ = v_b_3699_;
v_isShared_3710_ = v_isSharedCheck_3741_;
goto v_resetjp_3708_;
}
else
{
lean_inc(v_snd_3707_);
lean_dec(v_b_3699_);
v___x_3709_ = lean_box(0);
v_isShared_3710_ = v_isSharedCheck_3741_;
goto v_resetjp_3708_;
}
v_resetjp_3708_:
{
lean_object* v_a_3711_; lean_object* v___x_3712_; 
v_a_3711_ = lean_array_uget_borrowed(v_as_3696_, v_i_3698_);
lean_inc(v_snd_3707_);
v___x_3712_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_3694_, v_elimTrivial_3695_, v_a_3711_, v_snd_3707_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_);
if (lean_obj_tag(v___x_3712_) == 0)
{
lean_object* v_a_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3732_; 
v_a_3713_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3732_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3715_ = v___x_3712_;
v_isShared_3716_ = v_isSharedCheck_3732_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_a_3713_);
lean_dec(v___x_3712_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3732_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
if (lean_obj_tag(v_a_3713_) == 0)
{
lean_object* v___x_3717_; lean_object* v___x_3719_; 
v___x_3717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3717_, 0, v_a_3713_);
if (v_isShared_3710_ == 0)
{
lean_ctor_set(v___x_3709_, 0, v___x_3717_);
v___x_3719_ = v___x_3709_;
goto v_reusejp_3718_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v___x_3717_);
lean_ctor_set(v_reuseFailAlloc_3723_, 1, v_snd_3707_);
v___x_3719_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3718_;
}
v_reusejp_3718_:
{
lean_object* v___x_3721_; 
if (v_isShared_3716_ == 0)
{
lean_ctor_set(v___x_3715_, 0, v___x_3719_);
v___x_3721_ = v___x_3715_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v___x_3719_);
v___x_3721_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
return v___x_3721_;
}
}
}
else
{
lean_object* v_a_3724_; lean_object* v___x_3725_; lean_object* v___x_3727_; 
lean_del_object(v___x_3715_);
lean_dec(v_snd_3707_);
v_a_3724_ = lean_ctor_get(v_a_3713_, 0);
lean_inc(v_a_3724_);
lean_dec_ref_known(v_a_3713_, 1);
v___x_3725_ = lean_box(0);
if (v_isShared_3710_ == 0)
{
lean_ctor_set(v___x_3709_, 1, v_a_3724_);
lean_ctor_set(v___x_3709_, 0, v___x_3725_);
v___x_3727_ = v___x_3709_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v___x_3725_);
lean_ctor_set(v_reuseFailAlloc_3731_, 1, v_a_3724_);
v___x_3727_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
size_t v___x_3728_; size_t v___x_3729_; 
v___x_3728_ = ((size_t)1ULL);
v___x_3729_ = lean_usize_add(v_i_3698_, v___x_3728_);
v_i_3698_ = v___x_3729_;
v_b_3699_ = v___x_3727_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3740_; 
lean_del_object(v___x_3709_);
lean_dec(v_snd_3707_);
v_a_3733_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3735_ = v___x_3712_;
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_a_3733_);
lean_dec(v___x_3712_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v___x_3738_; 
if (v_isShared_3736_ == 0)
{
v___x_3738_ = v___x_3735_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v_a_3733_);
v___x_3738_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
return v___x_3738_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2___boxed(lean_object* v_init_3743_, lean_object* v_elimTrivial_3744_, lean_object* v_as_3745_, lean_object* v_sz_3746_, lean_object* v_i_3747_, lean_object* v_b_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_){
_start:
{
uint8_t v_elimTrivial_boxed_3754_; size_t v_sz_boxed_3755_; size_t v_i_boxed_3756_; lean_object* v_res_3757_; 
v_elimTrivial_boxed_3754_ = lean_unbox(v_elimTrivial_3744_);
v_sz_boxed_3755_ = lean_unbox_usize(v_sz_3746_);
lean_dec(v_sz_3746_);
v_i_boxed_3756_ = lean_unbox_usize(v_i_3747_);
lean_dec(v_i_3747_);
v_res_3757_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(v_init_3743_, v_elimTrivial_boxed_3754_, v_as_3745_, v_sz_boxed_3755_, v_i_boxed_3756_, v_b_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_);
lean_dec(v___y_3752_);
lean_dec_ref(v___y_3751_);
lean_dec(v___y_3750_);
lean_dec_ref(v___y_3749_);
lean_dec_ref(v_as_3745_);
lean_dec_ref(v_init_3743_);
return v_res_3757_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0___boxed(lean_object* v_init_3758_, lean_object* v_elimTrivial_3759_, lean_object* v_n_3760_, lean_object* v_b_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_){
_start:
{
uint8_t v_elimTrivial_boxed_3767_; lean_object* v_res_3768_; 
v_elimTrivial_boxed_3767_ = lean_unbox(v_elimTrivial_3759_);
v_res_3768_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_3758_, v_elimTrivial_boxed_3767_, v_n_3760_, v_b_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_);
lean_dec(v___y_3765_);
lean_dec_ref(v___y_3764_);
lean_dec(v___y_3763_);
lean_dec_ref(v___y_3762_);
lean_dec_ref(v_n_3760_);
lean_dec_ref(v_init_3758_);
return v_res_3768_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(uint8_t v_elimTrivial_3769_, lean_object* v_t_3770_, lean_object* v_init_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_){
_start:
{
lean_object* v_root_3777_; lean_object* v_tail_3778_; lean_object* v___x_3779_; 
v_root_3777_ = lean_ctor_get(v_t_3770_, 0);
v_tail_3778_ = lean_ctor_get(v_t_3770_, 1);
lean_inc_ref(v_init_3771_);
v___x_3779_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_3771_, v_elimTrivial_3769_, v_root_3777_, v_init_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_);
lean_dec_ref(v_init_3771_);
if (lean_obj_tag(v___x_3779_) == 0)
{
lean_object* v_a_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3816_; 
v_a_3780_ = lean_ctor_get(v___x_3779_, 0);
v_isSharedCheck_3816_ = !lean_is_exclusive(v___x_3779_);
if (v_isSharedCheck_3816_ == 0)
{
v___x_3782_ = v___x_3779_;
v_isShared_3783_ = v_isSharedCheck_3816_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_a_3780_);
lean_dec(v___x_3779_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3816_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
if (lean_obj_tag(v_a_3780_) == 0)
{
lean_object* v_a_3784_; lean_object* v___x_3786_; 
v_a_3784_ = lean_ctor_get(v_a_3780_, 0);
lean_inc(v_a_3784_);
lean_dec_ref_known(v_a_3780_, 1);
if (v_isShared_3783_ == 0)
{
lean_ctor_set(v___x_3782_, 0, v_a_3784_);
v___x_3786_ = v___x_3782_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v_a_3784_);
v___x_3786_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
return v___x_3786_;
}
}
else
{
lean_object* v_a_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; size_t v_sz_3791_; size_t v___x_3792_; lean_object* v___x_3793_; 
lean_del_object(v___x_3782_);
v_a_3788_ = lean_ctor_get(v_a_3780_, 0);
lean_inc(v_a_3788_);
lean_dec_ref_known(v_a_3780_, 1);
v___x_3789_ = lean_box(0);
v___x_3790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3790_, 0, v___x_3789_);
lean_ctor_set(v___x_3790_, 1, v_a_3788_);
v_sz_3791_ = lean_array_size(v_tail_3778_);
v___x_3792_ = ((size_t)0ULL);
v___x_3793_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(v_elimTrivial_3769_, v_tail_3778_, v_sz_3791_, v___x_3792_, v___x_3790_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_);
if (lean_obj_tag(v___x_3793_) == 0)
{
lean_object* v_a_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3807_; 
v_a_3794_ = lean_ctor_get(v___x_3793_, 0);
v_isSharedCheck_3807_ = !lean_is_exclusive(v___x_3793_);
if (v_isSharedCheck_3807_ == 0)
{
v___x_3796_ = v___x_3793_;
v_isShared_3797_ = v_isSharedCheck_3807_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_a_3794_);
lean_dec(v___x_3793_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3807_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
lean_object* v_fst_3798_; 
v_fst_3798_ = lean_ctor_get(v_a_3794_, 0);
if (lean_obj_tag(v_fst_3798_) == 0)
{
lean_object* v_snd_3799_; lean_object* v___x_3801_; 
v_snd_3799_ = lean_ctor_get(v_a_3794_, 1);
lean_inc(v_snd_3799_);
lean_dec(v_a_3794_);
if (v_isShared_3797_ == 0)
{
lean_ctor_set(v___x_3796_, 0, v_snd_3799_);
v___x_3801_ = v___x_3796_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v_snd_3799_);
v___x_3801_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
return v___x_3801_;
}
}
else
{
lean_object* v_val_3803_; lean_object* v___x_3805_; 
lean_inc_ref(v_fst_3798_);
lean_dec(v_a_3794_);
v_val_3803_ = lean_ctor_get(v_fst_3798_, 0);
lean_inc(v_val_3803_);
lean_dec_ref_known(v_fst_3798_, 1);
if (v_isShared_3797_ == 0)
{
lean_ctor_set(v___x_3796_, 0, v_val_3803_);
v___x_3805_ = v___x_3796_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v_val_3803_);
v___x_3805_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
return v___x_3805_;
}
}
}
}
else
{
lean_object* v_a_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3815_; 
v_a_3808_ = lean_ctor_get(v___x_3793_, 0);
v_isSharedCheck_3815_ = !lean_is_exclusive(v___x_3793_);
if (v_isSharedCheck_3815_ == 0)
{
v___x_3810_ = v___x_3793_;
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_a_3808_);
lean_dec(v___x_3793_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v___x_3813_; 
if (v_isShared_3811_ == 0)
{
v___x_3813_ = v___x_3810_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v_a_3808_);
v___x_3813_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
return v___x_3813_;
}
}
}
}
}
}
else
{
lean_object* v_a_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3824_; 
v_a_3817_ = lean_ctor_get(v___x_3779_, 0);
v_isSharedCheck_3824_ = !lean_is_exclusive(v___x_3779_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3819_ = v___x_3779_;
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_a_3817_);
lean_dec(v___x_3779_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v___x_3822_; 
if (v_isShared_3820_ == 0)
{
v___x_3822_ = v___x_3819_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v_a_3817_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0___boxed(lean_object* v_elimTrivial_3825_, lean_object* v_t_3826_, lean_object* v_init_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_){
_start:
{
uint8_t v_elimTrivial_boxed_3833_; lean_object* v_res_3834_; 
v_elimTrivial_boxed_3833_ = lean_unbox(v_elimTrivial_3825_);
v_res_3834_ = l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(v_elimTrivial_boxed_3833_, v_t_3826_, v_init_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3830_);
lean_dec(v___y_3829_);
lean_dec_ref(v___y_3828_);
lean_dec_ref(v_t_3826_);
return v_res_3834_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(lean_object* v_as_3835_, size_t v_sz_3836_, size_t v_i_3837_, lean_object* v_b_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_){
_start:
{
uint8_t v___x_3844_; 
v___x_3844_ = lean_usize_dec_lt(v_i_3837_, v_sz_3836_);
if (v___x_3844_ == 0)
{
lean_object* v___x_3845_; 
v___x_3845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3845_, 0, v_b_3838_);
return v___x_3845_;
}
else
{
lean_object* v_a_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; 
v_a_3846_ = lean_array_uget_borrowed(v_as_3835_, v_i_3837_);
v___x_3847_ = l_Lean_Expr_fvarId_x21(v_a_3846_);
v___x_3848_ = l_Lean_MVarId_tryClear(v_b_3838_, v___x_3847_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_);
if (lean_obj_tag(v___x_3848_) == 0)
{
lean_object* v_a_3849_; size_t v___x_3850_; size_t v___x_3851_; 
v_a_3849_ = lean_ctor_get(v___x_3848_, 0);
lean_inc(v_a_3849_);
lean_dec_ref_known(v___x_3848_, 1);
v___x_3850_ = ((size_t)1ULL);
v___x_3851_ = lean_usize_add(v_i_3837_, v___x_3850_);
v_i_3837_ = v___x_3851_;
v_b_3838_ = v_a_3849_;
goto _start;
}
else
{
return v___x_3848_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2___boxed(lean_object* v_as_3853_, lean_object* v_sz_3854_, lean_object* v_i_3855_, lean_object* v_b_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_){
_start:
{
size_t v_sz_boxed_3862_; size_t v_i_boxed_3863_; lean_object* v_res_3864_; 
v_sz_boxed_3862_ = lean_unbox_usize(v_sz_3854_);
lean_dec(v_sz_3854_);
v_i_boxed_3863_ = lean_unbox_usize(v_i_3855_);
lean_dec(v_i_3855_);
v_res_3864_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(v_as_3853_, v_sz_boxed_3862_, v_i_boxed_3863_, v_b_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_);
lean_dec(v___y_3860_);
lean_dec_ref(v___y_3859_);
lean_dec(v___y_3858_);
lean_dec_ref(v___y_3857_);
lean_dec_ref(v_as_3853_);
return v_res_3864_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(lean_object* v_x_3865_, lean_object* v_x_3866_, lean_object* v_x_3867_, lean_object* v_x_3868_){
_start:
{
lean_object* v_ks_3869_; lean_object* v_vs_3870_; lean_object* v___x_3872_; uint8_t v_isShared_3873_; uint8_t v_isSharedCheck_3894_; 
v_ks_3869_ = lean_ctor_get(v_x_3865_, 0);
v_vs_3870_ = lean_ctor_get(v_x_3865_, 1);
v_isSharedCheck_3894_ = !lean_is_exclusive(v_x_3865_);
if (v_isSharedCheck_3894_ == 0)
{
v___x_3872_ = v_x_3865_;
v_isShared_3873_ = v_isSharedCheck_3894_;
goto v_resetjp_3871_;
}
else
{
lean_inc(v_vs_3870_);
lean_inc(v_ks_3869_);
lean_dec(v_x_3865_);
v___x_3872_ = lean_box(0);
v_isShared_3873_ = v_isSharedCheck_3894_;
goto v_resetjp_3871_;
}
v_resetjp_3871_:
{
lean_object* v___x_3874_; uint8_t v___x_3875_; 
v___x_3874_ = lean_array_get_size(v_ks_3869_);
v___x_3875_ = lean_nat_dec_lt(v_x_3866_, v___x_3874_);
if (v___x_3875_ == 0)
{
lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3879_; 
lean_dec(v_x_3866_);
v___x_3876_ = lean_array_push(v_ks_3869_, v_x_3867_);
v___x_3877_ = lean_array_push(v_vs_3870_, v_x_3868_);
if (v_isShared_3873_ == 0)
{
lean_ctor_set(v___x_3872_, 1, v___x_3877_);
lean_ctor_set(v___x_3872_, 0, v___x_3876_);
v___x_3879_ = v___x_3872_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v___x_3876_);
lean_ctor_set(v_reuseFailAlloc_3880_, 1, v___x_3877_);
v___x_3879_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
return v___x_3879_;
}
}
else
{
lean_object* v_k_x27_3881_; uint8_t v___x_3882_; 
v_k_x27_3881_ = lean_array_fget_borrowed(v_ks_3869_, v_x_3866_);
v___x_3882_ = l_Lean_instBEqMVarId_beq(v_x_3867_, v_k_x27_3881_);
if (v___x_3882_ == 0)
{
lean_object* v___x_3884_; 
if (v_isShared_3873_ == 0)
{
v___x_3884_ = v___x_3872_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v_ks_3869_);
lean_ctor_set(v_reuseFailAlloc_3888_, 1, v_vs_3870_);
v___x_3884_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
lean_object* v___x_3885_; lean_object* v___x_3886_; 
v___x_3885_ = lean_unsigned_to_nat(1u);
v___x_3886_ = lean_nat_add(v_x_3866_, v___x_3885_);
lean_dec(v_x_3866_);
v_x_3865_ = v___x_3884_;
v_x_3866_ = v___x_3886_;
goto _start;
}
}
else
{
lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3892_; 
v___x_3889_ = lean_array_fset(v_ks_3869_, v_x_3866_, v_x_3867_);
v___x_3890_ = lean_array_fset(v_vs_3870_, v_x_3866_, v_x_3868_);
lean_dec(v_x_3866_);
if (v_isShared_3873_ == 0)
{
lean_ctor_set(v___x_3872_, 1, v___x_3890_);
lean_ctor_set(v___x_3872_, 0, v___x_3889_);
v___x_3892_ = v___x_3872_;
goto v_reusejp_3891_;
}
else
{
lean_object* v_reuseFailAlloc_3893_; 
v_reuseFailAlloc_3893_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3893_, 0, v___x_3889_);
lean_ctor_set(v_reuseFailAlloc_3893_, 1, v___x_3890_);
v___x_3892_ = v_reuseFailAlloc_3893_;
goto v_reusejp_3891_;
}
v_reusejp_3891_:
{
return v___x_3892_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(lean_object* v_n_3895_, lean_object* v_k_3896_, lean_object* v_v_3897_){
_start:
{
lean_object* v___x_3898_; lean_object* v___x_3899_; 
v___x_3898_ = lean_unsigned_to_nat(0u);
v___x_3899_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(v_n_3895_, v___x_3898_, v_k_3896_, v_v_3897_);
return v___x_3899_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_3900_; 
v___x_3900_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_3900_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(lean_object* v_x_3901_, size_t v_x_3902_, size_t v_x_3903_, lean_object* v_x_3904_, lean_object* v_x_3905_){
_start:
{
if (lean_obj_tag(v_x_3901_) == 0)
{
lean_object* v_es_3906_; size_t v___x_3907_; size_t v___x_3908_; lean_object* v_j_3909_; lean_object* v___x_3910_; uint8_t v___x_3911_; 
v_es_3906_ = lean_ctor_get(v_x_3901_, 0);
v___x_3907_ = ((size_t)31ULL);
v___x_3908_ = lean_usize_land(v_x_3902_, v___x_3907_);
v_j_3909_ = lean_usize_to_nat(v___x_3908_);
v___x_3910_ = lean_array_get_size(v_es_3906_);
v___x_3911_ = lean_nat_dec_lt(v_j_3909_, v___x_3910_);
if (v___x_3911_ == 0)
{
lean_dec(v_j_3909_);
lean_dec(v_x_3905_);
lean_dec(v_x_3904_);
return v_x_3901_;
}
else
{
lean_object* v___x_3913_; uint8_t v_isShared_3914_; uint8_t v_isSharedCheck_3950_; 
lean_inc_ref(v_es_3906_);
v_isSharedCheck_3950_ = !lean_is_exclusive(v_x_3901_);
if (v_isSharedCheck_3950_ == 0)
{
lean_object* v_unused_3951_; 
v_unused_3951_ = lean_ctor_get(v_x_3901_, 0);
lean_dec(v_unused_3951_);
v___x_3913_ = v_x_3901_;
v_isShared_3914_ = v_isSharedCheck_3950_;
goto v_resetjp_3912_;
}
else
{
lean_dec(v_x_3901_);
v___x_3913_ = lean_box(0);
v_isShared_3914_ = v_isSharedCheck_3950_;
goto v_resetjp_3912_;
}
v_resetjp_3912_:
{
lean_object* v_v_3915_; lean_object* v___x_3916_; lean_object* v_xs_x27_3917_; lean_object* v___y_3919_; 
v_v_3915_ = lean_array_fget(v_es_3906_, v_j_3909_);
v___x_3916_ = lean_box(0);
v_xs_x27_3917_ = lean_array_fset(v_es_3906_, v_j_3909_, v___x_3916_);
switch(lean_obj_tag(v_v_3915_))
{
case 0:
{
lean_object* v_key_3924_; lean_object* v_val_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3935_; 
v_key_3924_ = lean_ctor_get(v_v_3915_, 0);
v_val_3925_ = lean_ctor_get(v_v_3915_, 1);
v_isSharedCheck_3935_ = !lean_is_exclusive(v_v_3915_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3927_ = v_v_3915_;
v_isShared_3928_ = v_isSharedCheck_3935_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_val_3925_);
lean_inc(v_key_3924_);
lean_dec(v_v_3915_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3935_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
uint8_t v___x_3929_; 
v___x_3929_ = l_Lean_instBEqMVarId_beq(v_x_3904_, v_key_3924_);
if (v___x_3929_ == 0)
{
lean_object* v___x_3930_; lean_object* v___x_3931_; 
lean_del_object(v___x_3927_);
v___x_3930_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3924_, v_val_3925_, v_x_3904_, v_x_3905_);
v___x_3931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3931_, 0, v___x_3930_);
v___y_3919_ = v___x_3931_;
goto v___jp_3918_;
}
else
{
lean_object* v___x_3933_; 
lean_dec(v_val_3925_);
lean_dec(v_key_3924_);
if (v_isShared_3928_ == 0)
{
lean_ctor_set(v___x_3927_, 1, v_x_3905_);
lean_ctor_set(v___x_3927_, 0, v_x_3904_);
v___x_3933_ = v___x_3927_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_x_3904_);
lean_ctor_set(v_reuseFailAlloc_3934_, 1, v_x_3905_);
v___x_3933_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
v___y_3919_ = v___x_3933_;
goto v___jp_3918_;
}
}
}
}
case 1:
{
lean_object* v_node_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3948_; 
v_node_3936_ = lean_ctor_get(v_v_3915_, 0);
v_isSharedCheck_3948_ = !lean_is_exclusive(v_v_3915_);
if (v_isSharedCheck_3948_ == 0)
{
v___x_3938_ = v_v_3915_;
v_isShared_3939_ = v_isSharedCheck_3948_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_node_3936_);
lean_dec(v_v_3915_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_3948_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
size_t v___x_3940_; size_t v___x_3941_; size_t v___x_3942_; size_t v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3946_; 
v___x_3940_ = ((size_t)5ULL);
v___x_3941_ = lean_usize_shift_right(v_x_3902_, v___x_3940_);
v___x_3942_ = ((size_t)1ULL);
v___x_3943_ = lean_usize_add(v_x_3903_, v___x_3942_);
v___x_3944_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_node_3936_, v___x_3941_, v___x_3943_, v_x_3904_, v_x_3905_);
if (v_isShared_3939_ == 0)
{
lean_ctor_set(v___x_3938_, 0, v___x_3944_);
v___x_3946_ = v___x_3938_;
goto v_reusejp_3945_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v___x_3944_);
v___x_3946_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3945_;
}
v_reusejp_3945_:
{
v___y_3919_ = v___x_3946_;
goto v___jp_3918_;
}
}
}
default: 
{
lean_object* v___x_3949_; 
v___x_3949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3949_, 0, v_x_3904_);
lean_ctor_set(v___x_3949_, 1, v_x_3905_);
v___y_3919_ = v___x_3949_;
goto v___jp_3918_;
}
}
v___jp_3918_:
{
lean_object* v___x_3920_; lean_object* v___x_3922_; 
v___x_3920_ = lean_array_fset(v_xs_x27_3917_, v_j_3909_, v___y_3919_);
lean_dec(v_j_3909_);
if (v_isShared_3914_ == 0)
{
lean_ctor_set(v___x_3913_, 0, v___x_3920_);
v___x_3922_ = v___x_3913_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(0, 1, 0);
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
}
else
{
lean_object* v_ks_3952_; lean_object* v_vs_3953_; lean_object* v___x_3955_; uint8_t v_isShared_3956_; uint8_t v_isSharedCheck_3973_; 
v_ks_3952_ = lean_ctor_get(v_x_3901_, 0);
v_vs_3953_ = lean_ctor_get(v_x_3901_, 1);
v_isSharedCheck_3973_ = !lean_is_exclusive(v_x_3901_);
if (v_isSharedCheck_3973_ == 0)
{
v___x_3955_ = v_x_3901_;
v_isShared_3956_ = v_isSharedCheck_3973_;
goto v_resetjp_3954_;
}
else
{
lean_inc(v_vs_3953_);
lean_inc(v_ks_3952_);
lean_dec(v_x_3901_);
v___x_3955_ = lean_box(0);
v_isShared_3956_ = v_isSharedCheck_3973_;
goto v_resetjp_3954_;
}
v_resetjp_3954_:
{
lean_object* v___x_3958_; 
if (v_isShared_3956_ == 0)
{
v___x_3958_ = v___x_3955_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3972_; 
v_reuseFailAlloc_3972_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3972_, 0, v_ks_3952_);
lean_ctor_set(v_reuseFailAlloc_3972_, 1, v_vs_3953_);
v___x_3958_ = v_reuseFailAlloc_3972_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
lean_object* v_newNode_3959_; uint8_t v___y_3961_; size_t v___x_3967_; uint8_t v___x_3968_; 
v_newNode_3959_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(v___x_3958_, v_x_3904_, v_x_3905_);
v___x_3967_ = ((size_t)7ULL);
v___x_3968_ = lean_usize_dec_le(v___x_3967_, v_x_3903_);
if (v___x_3968_ == 0)
{
lean_object* v___x_3969_; lean_object* v___x_3970_; uint8_t v___x_3971_; 
v___x_3969_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3959_);
v___x_3970_ = lean_unsigned_to_nat(4u);
v___x_3971_ = lean_nat_dec_lt(v___x_3969_, v___x_3970_);
lean_dec(v___x_3969_);
v___y_3961_ = v___x_3971_;
goto v___jp_3960_;
}
else
{
v___y_3961_ = v___x_3968_;
goto v___jp_3960_;
}
v___jp_3960_:
{
if (v___y_3961_ == 0)
{
lean_object* v_ks_3962_; lean_object* v_vs_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; 
v_ks_3962_ = lean_ctor_get(v_newNode_3959_, 0);
lean_inc_ref(v_ks_3962_);
v_vs_3963_ = lean_ctor_get(v_newNode_3959_, 1);
lean_inc_ref(v_vs_3963_);
lean_dec_ref(v_newNode_3959_);
v___x_3964_ = lean_unsigned_to_nat(0u);
v___x_3965_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0);
v___x_3966_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_x_3903_, v_ks_3962_, v_vs_3963_, v___x_3964_, v___x_3965_);
lean_dec_ref(v_vs_3963_);
lean_dec_ref(v_ks_3962_);
return v___x_3966_;
}
else
{
return v_newNode_3959_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(size_t v_depth_3974_, lean_object* v_keys_3975_, lean_object* v_vals_3976_, lean_object* v_i_3977_, lean_object* v_entries_3978_){
_start:
{
lean_object* v___x_3979_; uint8_t v___x_3980_; 
v___x_3979_ = lean_array_get_size(v_keys_3975_);
v___x_3980_ = lean_nat_dec_lt(v_i_3977_, v___x_3979_);
if (v___x_3980_ == 0)
{
lean_dec(v_i_3977_);
return v_entries_3978_;
}
else
{
lean_object* v_k_3981_; lean_object* v_v_3982_; uint64_t v___x_3983_; size_t v_h_3984_; size_t v___x_3985_; lean_object* v___x_3986_; size_t v___x_3987_; size_t v___x_3988_; size_t v___x_3989_; size_t v_h_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; 
v_k_3981_ = lean_array_fget_borrowed(v_keys_3975_, v_i_3977_);
v_v_3982_ = lean_array_fget_borrowed(v_vals_3976_, v_i_3977_);
v___x_3983_ = l_Lean_instHashableMVarId_hash(v_k_3981_);
v_h_3984_ = lean_uint64_to_usize(v___x_3983_);
v___x_3985_ = ((size_t)5ULL);
v___x_3986_ = lean_unsigned_to_nat(1u);
v___x_3987_ = ((size_t)1ULL);
v___x_3988_ = lean_usize_sub(v_depth_3974_, v___x_3987_);
v___x_3989_ = lean_usize_mul(v___x_3985_, v___x_3988_);
v_h_3990_ = lean_usize_shift_right(v_h_3984_, v___x_3989_);
v___x_3991_ = lean_nat_add(v_i_3977_, v___x_3986_);
lean_dec(v_i_3977_);
lean_inc(v_v_3982_);
lean_inc(v_k_3981_);
v___x_3992_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_entries_3978_, v_h_3990_, v_depth_3974_, v_k_3981_, v_v_3982_);
v_i_3977_ = v___x_3991_;
v_entries_3978_ = v___x_3992_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg___boxed(lean_object* v_depth_3994_, lean_object* v_keys_3995_, lean_object* v_vals_3996_, lean_object* v_i_3997_, lean_object* v_entries_3998_){
_start:
{
size_t v_depth_boxed_3999_; lean_object* v_res_4000_; 
v_depth_boxed_3999_ = lean_unbox_usize(v_depth_3994_);
lean_dec(v_depth_3994_);
v_res_4000_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_depth_boxed_3999_, v_keys_3995_, v_vals_3996_, v_i_3997_, v_entries_3998_);
lean_dec_ref(v_vals_3996_);
lean_dec_ref(v_keys_3995_);
return v_res_4000_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___boxed(lean_object* v_x_4001_, lean_object* v_x_4002_, lean_object* v_x_4003_, lean_object* v_x_4004_, lean_object* v_x_4005_){
_start:
{
size_t v_x_7958__boxed_4006_; size_t v_x_7959__boxed_4007_; lean_object* v_res_4008_; 
v_x_7958__boxed_4006_ = lean_unbox_usize(v_x_4002_);
lean_dec(v_x_4002_);
v_x_7959__boxed_4007_ = lean_unbox_usize(v_x_4003_);
lean_dec(v_x_4003_);
v_res_4008_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_4001_, v_x_7958__boxed_4006_, v_x_7959__boxed_4007_, v_x_4004_, v_x_4005_);
return v_res_4008_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(lean_object* v_x_4009_, lean_object* v_x_4010_, lean_object* v_x_4011_){
_start:
{
uint64_t v___x_4012_; size_t v___x_4013_; size_t v___x_4014_; lean_object* v___x_4015_; 
v___x_4012_ = l_Lean_instHashableMVarId_hash(v_x_4010_);
v___x_4013_ = lean_uint64_to_usize(v___x_4012_);
v___x_4014_ = ((size_t)1ULL);
v___x_4015_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_4009_, v___x_4013_, v___x_4014_, v_x_4010_, v_x_4011_);
return v___x_4015_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(lean_object* v_mvarId_4016_, lean_object* v_val_4017_, lean_object* v___y_4018_){
_start:
{
lean_object* v___x_4020_; lean_object* v_mctx_4021_; lean_object* v_cache_4022_; lean_object* v_zetaDeltaFVarIds_4023_; lean_object* v_postponed_4024_; lean_object* v_diag_4025_; lean_object* v___x_4027_; uint8_t v_isShared_4028_; uint8_t v_isSharedCheck_4053_; 
v___x_4020_ = lean_st_ref_take(v___y_4018_);
v_mctx_4021_ = lean_ctor_get(v___x_4020_, 0);
v_cache_4022_ = lean_ctor_get(v___x_4020_, 1);
v_zetaDeltaFVarIds_4023_ = lean_ctor_get(v___x_4020_, 2);
v_postponed_4024_ = lean_ctor_get(v___x_4020_, 3);
v_diag_4025_ = lean_ctor_get(v___x_4020_, 4);
v_isSharedCheck_4053_ = !lean_is_exclusive(v___x_4020_);
if (v_isSharedCheck_4053_ == 0)
{
v___x_4027_ = v___x_4020_;
v_isShared_4028_ = v_isSharedCheck_4053_;
goto v_resetjp_4026_;
}
else
{
lean_inc(v_diag_4025_);
lean_inc(v_postponed_4024_);
lean_inc(v_zetaDeltaFVarIds_4023_);
lean_inc(v_cache_4022_);
lean_inc(v_mctx_4021_);
lean_dec(v___x_4020_);
v___x_4027_ = lean_box(0);
v_isShared_4028_ = v_isSharedCheck_4053_;
goto v_resetjp_4026_;
}
v_resetjp_4026_:
{
lean_object* v_depth_4029_; lean_object* v_levelAssignDepth_4030_; lean_object* v_lmvarCounter_4031_; lean_object* v_mvarCounter_4032_; lean_object* v_lDecls_4033_; lean_object* v_decls_4034_; lean_object* v_userNames_4035_; lean_object* v_lAssignment_4036_; lean_object* v_eAssignment_4037_; lean_object* v_dAssignment_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4052_; 
v_depth_4029_ = lean_ctor_get(v_mctx_4021_, 0);
v_levelAssignDepth_4030_ = lean_ctor_get(v_mctx_4021_, 1);
v_lmvarCounter_4031_ = lean_ctor_get(v_mctx_4021_, 2);
v_mvarCounter_4032_ = lean_ctor_get(v_mctx_4021_, 3);
v_lDecls_4033_ = lean_ctor_get(v_mctx_4021_, 4);
v_decls_4034_ = lean_ctor_get(v_mctx_4021_, 5);
v_userNames_4035_ = lean_ctor_get(v_mctx_4021_, 6);
v_lAssignment_4036_ = lean_ctor_get(v_mctx_4021_, 7);
v_eAssignment_4037_ = lean_ctor_get(v_mctx_4021_, 8);
v_dAssignment_4038_ = lean_ctor_get(v_mctx_4021_, 9);
v_isSharedCheck_4052_ = !lean_is_exclusive(v_mctx_4021_);
if (v_isSharedCheck_4052_ == 0)
{
v___x_4040_ = v_mctx_4021_;
v_isShared_4041_ = v_isSharedCheck_4052_;
goto v_resetjp_4039_;
}
else
{
lean_inc(v_dAssignment_4038_);
lean_inc(v_eAssignment_4037_);
lean_inc(v_lAssignment_4036_);
lean_inc(v_userNames_4035_);
lean_inc(v_decls_4034_);
lean_inc(v_lDecls_4033_);
lean_inc(v_mvarCounter_4032_);
lean_inc(v_lmvarCounter_4031_);
lean_inc(v_levelAssignDepth_4030_);
lean_inc(v_depth_4029_);
lean_dec(v_mctx_4021_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4052_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
lean_object* v___x_4042_; lean_object* v___x_4044_; 
v___x_4042_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(v_eAssignment_4037_, v_mvarId_4016_, v_val_4017_);
if (v_isShared_4041_ == 0)
{
lean_ctor_set(v___x_4040_, 8, v___x_4042_);
v___x_4044_ = v___x_4040_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4051_; 
v_reuseFailAlloc_4051_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4051_, 0, v_depth_4029_);
lean_ctor_set(v_reuseFailAlloc_4051_, 1, v_levelAssignDepth_4030_);
lean_ctor_set(v_reuseFailAlloc_4051_, 2, v_lmvarCounter_4031_);
lean_ctor_set(v_reuseFailAlloc_4051_, 3, v_mvarCounter_4032_);
lean_ctor_set(v_reuseFailAlloc_4051_, 4, v_lDecls_4033_);
lean_ctor_set(v_reuseFailAlloc_4051_, 5, v_decls_4034_);
lean_ctor_set(v_reuseFailAlloc_4051_, 6, v_userNames_4035_);
lean_ctor_set(v_reuseFailAlloc_4051_, 7, v_lAssignment_4036_);
lean_ctor_set(v_reuseFailAlloc_4051_, 8, v___x_4042_);
lean_ctor_set(v_reuseFailAlloc_4051_, 9, v_dAssignment_4038_);
v___x_4044_ = v_reuseFailAlloc_4051_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
lean_object* v___x_4046_; 
if (v_isShared_4028_ == 0)
{
lean_ctor_set(v___x_4027_, 0, v___x_4044_);
v___x_4046_ = v___x_4027_;
goto v_reusejp_4045_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v___x_4044_);
lean_ctor_set(v_reuseFailAlloc_4050_, 1, v_cache_4022_);
lean_ctor_set(v_reuseFailAlloc_4050_, 2, v_zetaDeltaFVarIds_4023_);
lean_ctor_set(v_reuseFailAlloc_4050_, 3, v_postponed_4024_);
lean_ctor_set(v_reuseFailAlloc_4050_, 4, v_diag_4025_);
v___x_4046_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4045_;
}
v_reusejp_4045_:
{
lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; 
v___x_4047_ = lean_st_ref_set(v___y_4018_, v___x_4046_);
v___x_4048_ = lean_box(0);
v___x_4049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4049_, 0, v___x_4048_);
return v___x_4049_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg___boxed(lean_object* v_mvarId_4054_, lean_object* v_val_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_){
_start:
{
lean_object* v_res_4058_; 
v_res_4058_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(v_mvarId_4054_, v_val_4055_, v___y_4056_);
lean_dec(v___y_4056_);
return v_res_4058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___lam__0(lean_object* v_mvar_4061_, uint8_t v_elimTrivial_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_){
_start:
{
lean_object* v___x_4068_; 
lean_inc(v_mvar_4061_);
v___x_4068_ = l_Lean_MVarId_getType(v_mvar_4061_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
if (lean_obj_tag(v___x_4068_) == 0)
{
lean_object* v_a_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; 
v_a_4069_ = lean_ctor_get(v___x_4068_, 0);
lean_inc(v_a_4069_);
lean_dec_ref_known(v___x_4068_, 1);
v___x_4070_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0));
v___x_4071_ = l_Lean_Elab_Tactic_Do_countUses(v_a_4069_, v___x_4070_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
if (lean_obj_tag(v___x_4071_) == 0)
{
lean_object* v_a_4072_; lean_object* v_fst_4073_; lean_object* v_snd_4074_; lean_object* v_lctx_4075_; lean_object* v___x_4076_; 
v_a_4072_ = lean_ctor_get(v___x_4071_, 0);
lean_inc(v_a_4072_);
lean_dec_ref_known(v___x_4071_, 1);
v_fst_4073_ = lean_ctor_get(v_a_4072_, 0);
lean_inc(v_fst_4073_);
v_snd_4074_ = lean_ctor_get(v_a_4072_, 1);
lean_inc(v_snd_4074_);
lean_dec(v_a_4072_);
v_lctx_4075_ = lean_ctor_get(v___y_4063_, 2);
lean_inc_ref(v_lctx_4075_);
v___x_4076_ = l_Lean_Elab_Tactic_Do_countUsesLCtx(v_lctx_4075_, v_snd_4074_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
if (lean_obj_tag(v___x_4076_) == 0)
{
lean_object* v_a_4077_; lean_object* v___x_4078_; lean_object* v_decls_4079_; lean_object* v___x_4080_; 
v_a_4077_ = lean_ctor_get(v___x_4076_, 0);
lean_inc(v_a_4077_);
lean_dec_ref_known(v___x_4076_, 1);
v___x_4078_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLets___lam__0___closed__0));
v_decls_4079_ = lean_ctor_get(v_a_4077_, 1);
lean_inc_ref(v_decls_4079_);
lean_dec(v_a_4077_);
v___x_4080_ = l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(v_elimTrivial_4062_, v_decls_4079_, v___x_4078_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
lean_dec_ref(v_decls_4079_);
if (lean_obj_tag(v___x_4080_) == 0)
{
lean_object* v_a_4081_; lean_object* v_fst_4082_; lean_object* v_snd_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; 
v_a_4081_ = lean_ctor_get(v___x_4080_, 0);
lean_inc(v_a_4081_);
lean_dec_ref_known(v___x_4080_, 1);
v_fst_4082_ = lean_ctor_get(v_a_4081_, 0);
lean_inc(v_fst_4082_);
v_snd_4083_ = lean_ctor_get(v_a_4081_, 1);
lean_inc(v_snd_4083_);
lean_dec(v_a_4081_);
v___x_4084_ = l_Lean_Expr_replaceFVars(v_fst_4073_, v_fst_4082_, v_snd_4083_);
lean_dec(v_snd_4083_);
lean_dec(v_fst_4073_);
v___x_4085_ = l_Lean_Elab_Tactic_Do_elimLetsCore(v___x_4084_, v_elimTrivial_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
if (lean_obj_tag(v___x_4085_) == 0)
{
lean_object* v_a_4086_; lean_object* v___x_4087_; 
v_a_4086_ = lean_ctor_get(v___x_4085_, 0);
lean_inc(v_a_4086_);
lean_dec_ref_known(v___x_4085_, 1);
lean_inc(v_mvar_4061_);
v___x_4087_ = l_Lean_MVarId_getTag(v_mvar_4061_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
if (lean_obj_tag(v___x_4087_) == 0)
{
lean_object* v_a_4088_; lean_object* v___x_4089_; 
v_a_4088_ = lean_ctor_get(v___x_4087_, 0);
lean_inc(v_a_4088_);
lean_dec_ref_known(v___x_4087_, 1);
v___x_4089_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_4086_, v_a_4088_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
if (lean_obj_tag(v___x_4089_) == 0)
{
lean_object* v_a_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; size_t v_sz_4093_; size_t v___x_4094_; lean_object* v___x_4095_; 
v_a_4090_ = lean_ctor_get(v___x_4089_, 0);
lean_inc_n(v_a_4090_, 2);
lean_dec_ref_known(v___x_4089_, 1);
v___x_4091_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(v_mvar_4061_, v_a_4090_, v___y_4064_);
lean_dec_ref(v___x_4091_);
v___x_4092_ = l_Lean_Expr_mvarId_x21(v_a_4090_);
lean_dec(v_a_4090_);
v_sz_4093_ = lean_array_size(v_fst_4082_);
v___x_4094_ = ((size_t)0ULL);
v___x_4095_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(v_fst_4082_, v_sz_4093_, v___x_4094_, v___x_4092_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
lean_dec_ref(v___y_4063_);
lean_dec(v_fst_4082_);
return v___x_4095_;
}
else
{
lean_object* v_a_4096_; lean_object* v___x_4098_; uint8_t v_isShared_4099_; uint8_t v_isSharedCheck_4103_; 
lean_dec(v_fst_4082_);
lean_dec_ref(v___y_4063_);
lean_dec(v_mvar_4061_);
v_a_4096_ = lean_ctor_get(v___x_4089_, 0);
v_isSharedCheck_4103_ = !lean_is_exclusive(v___x_4089_);
if (v_isSharedCheck_4103_ == 0)
{
v___x_4098_ = v___x_4089_;
v_isShared_4099_ = v_isSharedCheck_4103_;
goto v_resetjp_4097_;
}
else
{
lean_inc(v_a_4096_);
lean_dec(v___x_4089_);
v___x_4098_ = lean_box(0);
v_isShared_4099_ = v_isSharedCheck_4103_;
goto v_resetjp_4097_;
}
v_resetjp_4097_:
{
lean_object* v___x_4101_; 
if (v_isShared_4099_ == 0)
{
v___x_4101_ = v___x_4098_;
goto v_reusejp_4100_;
}
else
{
lean_object* v_reuseFailAlloc_4102_; 
v_reuseFailAlloc_4102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4102_, 0, v_a_4096_);
v___x_4101_ = v_reuseFailAlloc_4102_;
goto v_reusejp_4100_;
}
v_reusejp_4100_:
{
return v___x_4101_;
}
}
}
}
else
{
lean_object* v_a_4104_; lean_object* v___x_4106_; uint8_t v_isShared_4107_; uint8_t v_isSharedCheck_4111_; 
lean_dec(v_a_4086_);
lean_dec(v_fst_4082_);
lean_dec_ref(v___y_4063_);
lean_dec(v_mvar_4061_);
v_a_4104_ = lean_ctor_get(v___x_4087_, 0);
v_isSharedCheck_4111_ = !lean_is_exclusive(v___x_4087_);
if (v_isSharedCheck_4111_ == 0)
{
v___x_4106_ = v___x_4087_;
v_isShared_4107_ = v_isSharedCheck_4111_;
goto v_resetjp_4105_;
}
else
{
lean_inc(v_a_4104_);
lean_dec(v___x_4087_);
v___x_4106_ = lean_box(0);
v_isShared_4107_ = v_isSharedCheck_4111_;
goto v_resetjp_4105_;
}
v_resetjp_4105_:
{
lean_object* v___x_4109_; 
if (v_isShared_4107_ == 0)
{
v___x_4109_ = v___x_4106_;
goto v_reusejp_4108_;
}
else
{
lean_object* v_reuseFailAlloc_4110_; 
v_reuseFailAlloc_4110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4110_, 0, v_a_4104_);
v___x_4109_ = v_reuseFailAlloc_4110_;
goto v_reusejp_4108_;
}
v_reusejp_4108_:
{
return v___x_4109_;
}
}
}
}
else
{
lean_object* v_a_4112_; lean_object* v___x_4114_; uint8_t v_isShared_4115_; uint8_t v_isSharedCheck_4119_; 
lean_dec(v_fst_4082_);
lean_dec_ref(v___y_4063_);
lean_dec(v_mvar_4061_);
v_a_4112_ = lean_ctor_get(v___x_4085_, 0);
v_isSharedCheck_4119_ = !lean_is_exclusive(v___x_4085_);
if (v_isSharedCheck_4119_ == 0)
{
v___x_4114_ = v___x_4085_;
v_isShared_4115_ = v_isSharedCheck_4119_;
goto v_resetjp_4113_;
}
else
{
lean_inc(v_a_4112_);
lean_dec(v___x_4085_);
v___x_4114_ = lean_box(0);
v_isShared_4115_ = v_isSharedCheck_4119_;
goto v_resetjp_4113_;
}
v_resetjp_4113_:
{
lean_object* v___x_4117_; 
if (v_isShared_4115_ == 0)
{
v___x_4117_ = v___x_4114_;
goto v_reusejp_4116_;
}
else
{
lean_object* v_reuseFailAlloc_4118_; 
v_reuseFailAlloc_4118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4118_, 0, v_a_4112_);
v___x_4117_ = v_reuseFailAlloc_4118_;
goto v_reusejp_4116_;
}
v_reusejp_4116_:
{
return v___x_4117_;
}
}
}
}
else
{
lean_object* v_a_4120_; lean_object* v___x_4122_; uint8_t v_isShared_4123_; uint8_t v_isSharedCheck_4127_; 
lean_dec(v_fst_4073_);
lean_dec_ref(v___y_4063_);
lean_dec(v_mvar_4061_);
v_a_4120_ = lean_ctor_get(v___x_4080_, 0);
v_isSharedCheck_4127_ = !lean_is_exclusive(v___x_4080_);
if (v_isSharedCheck_4127_ == 0)
{
v___x_4122_ = v___x_4080_;
v_isShared_4123_ = v_isSharedCheck_4127_;
goto v_resetjp_4121_;
}
else
{
lean_inc(v_a_4120_);
lean_dec(v___x_4080_);
v___x_4122_ = lean_box(0);
v_isShared_4123_ = v_isSharedCheck_4127_;
goto v_resetjp_4121_;
}
v_resetjp_4121_:
{
lean_object* v___x_4125_; 
if (v_isShared_4123_ == 0)
{
v___x_4125_ = v___x_4122_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v_a_4120_);
v___x_4125_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
return v___x_4125_;
}
}
}
}
else
{
lean_object* v_a_4128_; lean_object* v___x_4130_; uint8_t v_isShared_4131_; uint8_t v_isSharedCheck_4135_; 
lean_dec(v_fst_4073_);
lean_dec_ref(v___y_4063_);
lean_dec(v_mvar_4061_);
v_a_4128_ = lean_ctor_get(v___x_4076_, 0);
v_isSharedCheck_4135_ = !lean_is_exclusive(v___x_4076_);
if (v_isSharedCheck_4135_ == 0)
{
v___x_4130_ = v___x_4076_;
v_isShared_4131_ = v_isSharedCheck_4135_;
goto v_resetjp_4129_;
}
else
{
lean_inc(v_a_4128_);
lean_dec(v___x_4076_);
v___x_4130_ = lean_box(0);
v_isShared_4131_ = v_isSharedCheck_4135_;
goto v_resetjp_4129_;
}
v_resetjp_4129_:
{
lean_object* v___x_4133_; 
if (v_isShared_4131_ == 0)
{
v___x_4133_ = v___x_4130_;
goto v_reusejp_4132_;
}
else
{
lean_object* v_reuseFailAlloc_4134_; 
v_reuseFailAlloc_4134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4134_, 0, v_a_4128_);
v___x_4133_ = v_reuseFailAlloc_4134_;
goto v_reusejp_4132_;
}
v_reusejp_4132_:
{
return v___x_4133_;
}
}
}
}
else
{
lean_object* v_a_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4143_; 
lean_dec_ref(v___y_4063_);
lean_dec(v_mvar_4061_);
v_a_4136_ = lean_ctor_get(v___x_4071_, 0);
v_isSharedCheck_4143_ = !lean_is_exclusive(v___x_4071_);
if (v_isSharedCheck_4143_ == 0)
{
v___x_4138_ = v___x_4071_;
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
else
{
lean_inc(v_a_4136_);
lean_dec(v___x_4071_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
lean_object* v___x_4141_; 
if (v_isShared_4139_ == 0)
{
v___x_4141_ = v___x_4138_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v_a_4136_);
v___x_4141_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
return v___x_4141_;
}
}
}
}
else
{
lean_object* v_a_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4151_; 
lean_dec_ref(v___y_4063_);
lean_dec(v_mvar_4061_);
v_a_4144_ = lean_ctor_get(v___x_4068_, 0);
v_isSharedCheck_4151_ = !lean_is_exclusive(v___x_4068_);
if (v_isSharedCheck_4151_ == 0)
{
v___x_4146_ = v___x_4068_;
v_isShared_4147_ = v_isSharedCheck_4151_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_a_4144_);
lean_dec(v___x_4068_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4151_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
lean_object* v___x_4149_; 
if (v_isShared_4147_ == 0)
{
v___x_4149_ = v___x_4146_;
goto v_reusejp_4148_;
}
else
{
lean_object* v_reuseFailAlloc_4150_; 
v_reuseFailAlloc_4150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4150_, 0, v_a_4144_);
v___x_4149_ = v_reuseFailAlloc_4150_;
goto v_reusejp_4148_;
}
v_reusejp_4148_:
{
return v___x_4149_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___lam__0___boxed(lean_object* v_mvar_4152_, lean_object* v_elimTrivial_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_){
_start:
{
uint8_t v_elimTrivial_boxed_4159_; lean_object* v_res_4160_; 
v_elimTrivial_boxed_4159_ = lean_unbox(v_elimTrivial_4153_);
v_res_4160_ = l_Lean_Elab_Tactic_Do_elimLets___lam__0(v_mvar_4152_, v_elimTrivial_boxed_4159_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_);
lean_dec(v___y_4157_);
lean_dec_ref(v___y_4156_);
lean_dec(v___y_4155_);
return v_res_4160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets(lean_object* v_mvar_4161_, uint8_t v_elimTrivial_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_){
_start:
{
lean_object* v___x_4168_; lean_object* v___f_4169_; lean_object* v___x_4170_; 
v___x_4168_ = lean_box(v_elimTrivial_4162_);
lean_inc(v_mvar_4161_);
v___f_4169_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elimLets___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4169_, 0, v_mvar_4161_);
lean_closure_set(v___f_4169_, 1, v___x_4168_);
v___x_4170_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(v_mvar_4161_, v___f_4169_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_);
return v___x_4170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___boxed(lean_object* v_mvar_4171_, lean_object* v_elimTrivial_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_){
_start:
{
uint8_t v_elimTrivial_boxed_4178_; lean_object* v_res_4179_; 
v_elimTrivial_boxed_4178_ = lean_unbox(v_elimTrivial_4172_);
v_res_4179_ = l_Lean_Elab_Tactic_Do_elimLets(v_mvar_4171_, v_elimTrivial_boxed_4178_, v_a_4173_, v_a_4174_, v_a_4175_, v_a_4176_);
lean_dec(v_a_4176_);
lean_dec_ref(v_a_4175_);
lean_dec(v_a_4174_);
lean_dec_ref(v_a_4173_);
return v_res_4179_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1(lean_object* v_mvarId_4180_, lean_object* v_val_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_){
_start:
{
lean_object* v___x_4187_; 
v___x_4187_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(v_mvarId_4180_, v_val_4181_, v___y_4183_);
return v___x_4187_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___boxed(lean_object* v_mvarId_4188_, lean_object* v_val_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_){
_start:
{
lean_object* v_res_4195_; 
v_res_4195_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1(v_mvarId_4188_, v_val_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_);
lean_dec(v___y_4193_);
lean_dec_ref(v___y_4192_);
lean_dec(v___y_4191_);
lean_dec_ref(v___y_4190_);
return v_res_4195_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3(lean_object* v_00_u03b2_4196_, lean_object* v_x_4197_, lean_object* v_x_4198_, lean_object* v_x_4199_){
_start:
{
lean_object* v___x_4200_; 
v___x_4200_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(v_x_4197_, v_x_4198_, v_x_4199_);
return v___x_4200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5(uint8_t v_elimTrivial_4201_, lean_object* v_as_4202_, size_t v_sz_4203_, size_t v_i_4204_, lean_object* v_b_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_){
_start:
{
lean_object* v___x_4211_; 
v___x_4211_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_4201_, v_as_4202_, v_sz_4203_, v_i_4204_, v_b_4205_);
return v___x_4211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___boxed(lean_object* v_elimTrivial_4212_, lean_object* v_as_4213_, lean_object* v_sz_4214_, lean_object* v_i_4215_, lean_object* v_b_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_){
_start:
{
uint8_t v_elimTrivial_boxed_4222_; size_t v_sz_boxed_4223_; size_t v_i_boxed_4224_; lean_object* v_res_4225_; 
v_elimTrivial_boxed_4222_ = lean_unbox(v_elimTrivial_4212_);
v_sz_boxed_4223_ = lean_unbox_usize(v_sz_4214_);
lean_dec(v_sz_4214_);
v_i_boxed_4224_ = lean_unbox_usize(v_i_4215_);
lean_dec(v_i_4215_);
v_res_4225_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5(v_elimTrivial_boxed_4222_, v_as_4213_, v_sz_boxed_4223_, v_i_boxed_4224_, v_b_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_);
lean_dec(v___y_4220_);
lean_dec_ref(v___y_4219_);
lean_dec(v___y_4218_);
lean_dec_ref(v___y_4217_);
lean_dec_ref(v_as_4213_);
return v_res_4225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_4226_, lean_object* v_x_4227_, size_t v_x_4228_, size_t v_x_4229_, lean_object* v_x_4230_, lean_object* v_x_4231_){
_start:
{
lean_object* v___x_4232_; 
v___x_4232_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_4227_, v_x_4228_, v_x_4229_, v_x_4230_, v_x_4231_);
return v___x_4232_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___boxed(lean_object* v_00_u03b2_4233_, lean_object* v_x_4234_, lean_object* v_x_4235_, lean_object* v_x_4236_, lean_object* v_x_4237_, lean_object* v_x_4238_){
_start:
{
size_t v_x_8408__boxed_4239_; size_t v_x_8409__boxed_4240_; lean_object* v_res_4241_; 
v_x_8408__boxed_4239_ = lean_unbox_usize(v_x_4235_);
lean_dec(v_x_4235_);
v_x_8409__boxed_4240_ = lean_unbox_usize(v_x_4236_);
lean_dec(v_x_4236_);
v_res_4241_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8(v_00_u03b2_4233_, v_x_4234_, v_x_8408__boxed_4239_, v_x_8409__boxed_4240_, v_x_4237_, v_x_4238_);
return v_res_4241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6(uint8_t v_elimTrivial_4242_, lean_object* v_as_4243_, size_t v_sz_4244_, size_t v_i_4245_, lean_object* v_b_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_){
_start:
{
lean_object* v___x_4252_; 
v___x_4252_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_4242_, v_as_4243_, v_sz_4244_, v_i_4245_, v_b_4246_);
return v___x_4252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___boxed(lean_object* v_elimTrivial_4253_, lean_object* v_as_4254_, lean_object* v_sz_4255_, lean_object* v_i_4256_, lean_object* v_b_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_){
_start:
{
uint8_t v_elimTrivial_boxed_4263_; size_t v_sz_boxed_4264_; size_t v_i_boxed_4265_; lean_object* v_res_4266_; 
v_elimTrivial_boxed_4263_ = lean_unbox(v_elimTrivial_4253_);
v_sz_boxed_4264_ = lean_unbox_usize(v_sz_4255_);
lean_dec(v_sz_4255_);
v_i_boxed_4265_ = lean_unbox_usize(v_i_4256_);
lean_dec(v_i_4256_);
v_res_4266_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6(v_elimTrivial_boxed_4263_, v_as_4254_, v_sz_boxed_4264_, v_i_boxed_4265_, v_b_4257_, v___y_4258_, v___y_4259_, v___y_4260_, v___y_4261_);
lean_dec(v___y_4261_);
lean_dec_ref(v___y_4260_);
lean_dec(v___y_4259_);
lean_dec_ref(v___y_4258_);
lean_dec_ref(v_as_4254_);
return v_res_4266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11(lean_object* v_00_u03b2_4267_, lean_object* v_n_4268_, lean_object* v_k_4269_, lean_object* v_v_4270_){
_start:
{
lean_object* v___x_4271_; 
v___x_4271_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(v_n_4268_, v_k_4269_, v_v_4270_);
return v___x_4271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12(lean_object* v_00_u03b2_4272_, size_t v_depth_4273_, lean_object* v_keys_4274_, lean_object* v_vals_4275_, lean_object* v_heq_4276_, lean_object* v_i_4277_, lean_object* v_entries_4278_){
_start:
{
lean_object* v___x_4279_; 
v___x_4279_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_depth_4273_, v_keys_4274_, v_vals_4275_, v_i_4277_, v_entries_4278_);
return v___x_4279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___boxed(lean_object* v_00_u03b2_4280_, lean_object* v_depth_4281_, lean_object* v_keys_4282_, lean_object* v_vals_4283_, lean_object* v_heq_4284_, lean_object* v_i_4285_, lean_object* v_entries_4286_){
_start:
{
size_t v_depth_boxed_4287_; lean_object* v_res_4288_; 
v_depth_boxed_4287_ = lean_unbox_usize(v_depth_4281_);
lean_dec(v_depth_4281_);
v_res_4288_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12(v_00_u03b2_4280_, v_depth_boxed_4287_, v_keys_4282_, v_vals_4283_, v_heq_4284_, v_i_4285_, v_entries_4286_);
lean_dec_ref(v_vals_4283_);
lean_dec_ref(v_keys_4282_);
return v_res_4288_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12(lean_object* v_00_u03b2_4289_, lean_object* v_x_4290_, lean_object* v_x_4291_, lean_object* v_x_4292_, lean_object* v_x_4293_){
_start:
{
lean_object* v___x_4294_; 
v___x_4294_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(v_x_4290_, v_x_4291_, v_x_4292_, v_x_4293_);
return v___x_4294_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_LetElim(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
