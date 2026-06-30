// Lean compiler output
// Module: Lean.LocalContext
// Imports: public import Init.Data.Nat.Control public import Lean.Data.PersistentArray public import Lean.Expr import Init.Data.ToString.Macro import Init.Omega
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_forM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVarId(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_anyM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_set___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_pop___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
lean_object* lean_expr_lower_loose_bvars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instBEqFVarId_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instHashableFVarId_hash___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_Node_isEmpty___redArg(lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_sanitizeName(lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Nat_foldRev___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_getSanitizeNames(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instInhabitedLocalDeclKind_default;
LEAN_EXPORT uint8_t l_Lean_instInhabitedLocalDeclKind;
static const lean_string_object l_Lean_instReprLocalDeclKind_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.LocalDeclKind.default"};
static const lean_object* l_Lean_instReprLocalDeclKind_repr___closed__0 = (const lean_object*)&l_Lean_instReprLocalDeclKind_repr___closed__0_value;
static const lean_ctor_object l_Lean_instReprLocalDeclKind_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprLocalDeclKind_repr___closed__0_value)}};
static const lean_object* l_Lean_instReprLocalDeclKind_repr___closed__1 = (const lean_object*)&l_Lean_instReprLocalDeclKind_repr___closed__1_value;
static const lean_string_object l_Lean_instReprLocalDeclKind_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.LocalDeclKind.implDetail"};
static const lean_object* l_Lean_instReprLocalDeclKind_repr___closed__2 = (const lean_object*)&l_Lean_instReprLocalDeclKind_repr___closed__2_value;
static const lean_ctor_object l_Lean_instReprLocalDeclKind_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprLocalDeclKind_repr___closed__2_value)}};
static const lean_object* l_Lean_instReprLocalDeclKind_repr___closed__3 = (const lean_object*)&l_Lean_instReprLocalDeclKind_repr___closed__3_value;
static const lean_string_object l_Lean_instReprLocalDeclKind_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.LocalDeclKind.auxDecl"};
static const lean_object* l_Lean_instReprLocalDeclKind_repr___closed__4 = (const lean_object*)&l_Lean_instReprLocalDeclKind_repr___closed__4_value;
static const lean_ctor_object l_Lean_instReprLocalDeclKind_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprLocalDeclKind_repr___closed__4_value)}};
static const lean_object* l_Lean_instReprLocalDeclKind_repr___closed__5 = (const lean_object*)&l_Lean_instReprLocalDeclKind_repr___closed__5_value;
static lean_once_cell_t l_Lean_instReprLocalDeclKind_repr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprLocalDeclKind_repr___closed__6;
static lean_once_cell_t l_Lean_instReprLocalDeclKind_repr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprLocalDeclKind_repr___closed__7;
LEAN_EXPORT lean_object* l_Lean_instReprLocalDeclKind_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprLocalDeclKind_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprLocalDeclKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprLocalDeclKind_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprLocalDeclKind___closed__0 = (const lean_object*)&l_Lean_instReprLocalDeclKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprLocalDeclKind = (const lean_object*)&l_Lean_instReprLocalDeclKind___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_LocalDeclKind_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_instDecidableEqLocalDeclKind(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instDecidableEqLocalDeclKind___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_instHashableLocalDeclKind_hash(uint8_t);
LEAN_EXPORT lean_object* l_Lean_instHashableLocalDeclKind_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_instHashableLocalDeclKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableLocalDeclKind_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instHashableLocalDeclKind___closed__0 = (const lean_object*)&l_Lean_instHashableLocalDeclKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instHashableLocalDeclKind = (const lean_object*)&l_Lean_instHashableLocalDeclKind___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_cdecl_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_cdecl_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ldecl_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ldecl_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_instInhabitedLocalDecl_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_instInhabitedLocalDecl_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedLocalDecl_default___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedLocalDecl_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instInhabitedLocalDecl_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_instInhabitedLocalDecl_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedLocalDecl_default___closed__1_value;
static lean_once_cell_t l_Lean_instInhabitedLocalDecl_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedLocalDecl_default___closed__2;
static lean_once_cell_t l_Lean_instInhabitedLocalDecl_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedLocalDecl_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_instInhabitedLocalDecl_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedLocalDecl;
LEAN_EXPORT lean_object* lean_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkLocalDeclEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_mk_let_decl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_local_decl_binder_info(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_binderInfoEx___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isLet(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isLet___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_index(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_index___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setIndex(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_fvarId___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_userName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_userName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_type___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setType(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_binderInfo___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalDecl_kind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_kind___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isAuxDecl___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isImplementationDetail___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_LocalDecl_value_spec__0(lean_object*);
static const lean_string_object l_Lean_LocalDecl_value___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.LocalContext"};
static const lean_object* l_Lean_LocalDecl_value___closed__0 = (const lean_object*)&l_Lean_LocalDecl_value___closed__0_value;
static const lean_string_object l_Lean_LocalDecl_value___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.LocalDecl.value"};
static const lean_object* l_Lean_LocalDecl_value___closed__1 = (const lean_object*)&l_Lean_LocalDecl_value___closed__1_value;
static const lean_string_object l_Lean_LocalDecl_value___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "let declaration expected"};
static const lean_object* l_Lean_LocalDecl_value___closed__2 = (const lean_object*)&l_Lean_LocalDecl_value___closed__2_value;
static lean_once_cell_t l_Lean_LocalDecl_value___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LocalDecl_value___closed__3;
static const lean_string_object l_Lean_LocalDecl_value___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "dependent let declaration expected"};
static const lean_object* l_Lean_LocalDecl_value___closed__4 = (const lean_object*)&l_Lean_LocalDecl_value___closed__4_value;
static lean_once_cell_t l_Lean_LocalDecl_value___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LocalDecl_value___closed__5;
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalDecl_hasValue(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_hasValue___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setValue(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setNondep(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setNondep___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isNondep(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isNondep___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setUserName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(lean_object*);
static const lean_string_object l_Lean_LocalDecl_setBinderInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.LocalDecl.setBinderInfo"};
static const lean_object* l_Lean_LocalDecl_setBinderInfo___closed__0 = (const lean_object*)&l_Lean_LocalDecl_setBinderInfo___closed__0_value;
static const lean_string_object l_Lean_LocalDecl_setBinderInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "unexpected let declaration"};
static const lean_object* l_Lean_LocalDecl_setBinderInfo___closed__1 = (const lean_object*)&l_Lean_LocalDecl_setBinderInfo___closed__1_value;
static lean_once_cell_t l_Lean_LocalDecl_setBinderInfo___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LocalDecl_setBinderInfo___closed__2;
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setBinderInfo(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setBinderInfo___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalDecl_hasExprMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_hasExprMVar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setKind(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setKind___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_instInhabitedLocalContext_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedLocalContext_default___closed__0;
static lean_once_cell_t l_Lean_instInhabitedLocalContext_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedLocalContext_default___closed__1;
static lean_once_cell_t l_Lean_instInhabitedLocalContext_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedLocalContext_default___closed__2;
static lean_once_cell_t l_Lean_instInhabitedLocalContext_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedLocalContext_default___closed__3;
static lean_once_cell_t l_Lean_instInhabitedLocalContext_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedLocalContext_default___closed__4;
LEAN_EXPORT lean_object* l_Lean_instInhabitedLocalContext_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedLocalContext;
LEAN_EXPORT lean_object* lean_mk_empty_local_ctx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_empty;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_local_ctx_is_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_isEmpty___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_mkLocalDeclExported___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_local_ctx_mk_let_decl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_mkLetDeclExported___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkAuxDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_addDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_local_ctx_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFVar_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFVar_x3f___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_LocalContext_get_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.LocalContext.get!"};
static const lean_object* l_Lean_LocalContext_get_x21___closed__0 = (const lean_object*)&l_Lean_LocalContext_get_x21___closed__0_value;
static const lean_string_object l_Lean_LocalContext_get_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unknown free variable"};
static const lean_object* l_Lean_LocalContext_get_x21___closed__1 = (const lean_object*)&l_Lean_LocalContext_get_x21___closed__1_value;
static lean_once_cell_t l_Lean_LocalContext_get_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LocalContext_get_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_LocalContext_get_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVar_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVar_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_containsFVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_containsFVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_LocalContext_getFVarIds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_LocalContext_getFVarIds___closed__0 = (const lean_object*)&l_Lean_LocalContext_getFVarIds___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVarIds(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVarIds___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVars(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVars___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_local_ctx_erase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_pop(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserName_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_LocalContext_getFromUserName_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.LocalContext.getFromUserName!"};
static const lean_object* l_Lean_LocalContext_getFromUserName_x21___closed__0 = (const lean_object*)&l_Lean_LocalContext_getFromUserName_x21___closed__0_value;
static const lean_string_object l_Lean_LocalContext_getFromUserName_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "unknown local declaration `"};
static const lean_object* l_Lean_LocalContext_getFromUserName_x21___closed__1 = (const lean_object*)&l_Lean_LocalContext_getFromUserName_x21___closed__1_value;
static const lean_string_object l_Lean_LocalContext_getFromUserName_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_LocalContext_getFromUserName_x21___closed__2 = (const lean_object*)&l_Lean_LocalContext_getFromUserName_x21___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFromUserName_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFromUserName_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_usesUserName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_usesUserName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getUnusedName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getUnusedName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_lastDecl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_lastDecl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_setUserName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_renameUserName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_renameUserName___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_LocalContext_modifyLocalDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqFVarId_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LocalContext_modifyLocalDecl___closed__0 = (const lean_object*)&l_Lean_LocalContext_modifyLocalDecl___closed__0_value;
static const lean_closure_object l_Lean_LocalContext_modifyLocalDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableFVarId_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LocalContext_modifyLocalDecl___closed__1 = (const lean_object*)&l_Lean_LocalContext_modifyLocalDecl___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_LocalContext_modifyLocalDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_modifyLocalDecls(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_setKind(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_setKind___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_setBinderInfo(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_setBinderInfo___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_setType(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_local_ctx_num_indices(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getAt_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getAt_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_LocalContext_foldl___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LocalContext_foldl___redArg___closed__0 = (const lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__0_value;
static const lean_closure_object l_Lean_LocalContext_foldl___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LocalContext_foldl___redArg___closed__1 = (const lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__1_value;
static const lean_closure_object l_Lean_LocalContext_foldl___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LocalContext_foldl___redArg___closed__2 = (const lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__2_value;
static const lean_closure_object l_Lean_LocalContext_foldl___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LocalContext_foldl___redArg___closed__3 = (const lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__3_value;
static const lean_closure_object l_Lean_LocalContext_foldl___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LocalContext_foldl___redArg___closed__4 = (const lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__4_value;
static const lean_closure_object l_Lean_LocalContext_foldl___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LocalContext_foldl___redArg___closed__5 = (const lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__5_value;
static const lean_closure_object l_Lean_LocalContext_foldl___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LocalContext_foldl___redArg___closed__6 = (const lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__6_value;
static const lean_ctor_object l_Lean_LocalContext_foldl___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__0_value),((lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__1_value)}};
static const lean_object* l_Lean_LocalContext_foldl___redArg___closed__7 = (const lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__7_value;
static const lean_ctor_object l_Lean_LocalContext_foldl___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__7_value),((lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__2_value),((lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__3_value),((lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__4_value),((lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__5_value)}};
static const lean_object* l_Lean_LocalContext_foldl___redArg___closed__8 = (const lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__8_value;
static const lean_ctor_object l_Lean_LocalContext_foldl___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__8_value),((lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__6_value)}};
static const lean_object* l_Lean_LocalContext_foldl___redArg___closed__9 = (const lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_size___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRev_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRev_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_isSubPrefixOfAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_isSubPrefixOfAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_isSubPrefixOf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_isSubPrefixOf___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_LocalContext_mkBinding___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.LocalContext.mkBinding"};
static const lean_object* l_Lean_LocalContext_mkBinding___lam__0___closed__0 = (const lean_object*)&l_Lean_LocalContext_mkBinding___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_LocalContext_mkBinding___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LocalContext_mkBinding___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLambda(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkForall(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_any___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_any___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_any(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_any___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_all___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_all___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_all(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_all___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_sanitizeNames(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getRoundtrippingUserName_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_sortFVarsByContextOrder(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_sortFVarsByContextOrder___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_LocalContext_findFromUserNames___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_LocalContext_findFromUserNames___redArg___closed__0 = (const lean_object*)&l_Lean_LocalContext_findFromUserNames___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadLCtxOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadLCtxOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_getLocalHyps___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_getLocalHyps___redArg___closed__0 = (const lean_object*)&l_Lean_getLocalHyps___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getLocalHyps(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_replaceFVarId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_replaceFVarId___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorIdx(uint8_t v_x_1_){
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
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_LocalDeclKind_ctorIdx(v_x_boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_toCtorIdx(uint8_t v_x_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_LocalDeclKind_ctorIdx(v_x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_toCtorIdx___boxed(lean_object* v_x_10_){
_start:
{
uint8_t v_x_4__boxed_11_; lean_object* v_res_12_; 
v_x_4__boxed_11_ = lean_unbox(v_x_10_);
v_res_12_ = l_Lean_LocalDeclKind_toCtorIdx(v_x_4__boxed_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim___redArg(lean_object* v_k_13_){
_start:
{
lean_inc(v_k_13_);
return v_k_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim___redArg___boxed(lean_object* v_k_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lean_LocalDeclKind_ctorElim___redArg(v_k_14_);
lean_dec(v_k_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, uint8_t v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_inc(v_k_20_);
return v_k_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
uint8_t v_t_boxed_26_; lean_object* v_res_27_; 
v_t_boxed_26_ = lean_unbox(v_t_23_);
v_res_27_ = l_Lean_LocalDeclKind_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_boxed_26_, v_h_24_, v_k_25_);
lean_dec(v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim___redArg(lean_object* v_default_28_){
_start:
{
lean_inc(v_default_28_);
return v_default_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim___redArg___boxed(lean_object* v_default_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_LocalDeclKind_default_elim___redArg(v_default_29_);
lean_dec(v_default_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim(lean_object* v_motive_31_, uint8_t v_t_32_, lean_object* v_h_33_, lean_object* v_default_34_){
_start:
{
lean_inc(v_default_34_);
return v_default_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim___boxed(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_default_38_){
_start:
{
uint8_t v_t_boxed_39_; lean_object* v_res_40_; 
v_t_boxed_39_ = lean_unbox(v_t_36_);
v_res_40_ = l_Lean_LocalDeclKind_default_elim(v_motive_35_, v_t_boxed_39_, v_h_37_, v_default_38_);
lean_dec(v_default_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim___redArg(lean_object* v_implDetail_41_){
_start:
{
lean_inc(v_implDetail_41_);
return v_implDetail_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim___redArg___boxed(lean_object* v_implDetail_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_LocalDeclKind_implDetail_elim___redArg(v_implDetail_42_);
lean_dec(v_implDetail_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim(lean_object* v_motive_44_, uint8_t v_t_45_, lean_object* v_h_46_, lean_object* v_implDetail_47_){
_start:
{
lean_inc(v_implDetail_47_);
return v_implDetail_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim___boxed(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_implDetail_51_){
_start:
{
uint8_t v_t_boxed_52_; lean_object* v_res_53_; 
v_t_boxed_52_ = lean_unbox(v_t_49_);
v_res_53_ = l_Lean_LocalDeclKind_implDetail_elim(v_motive_48_, v_t_boxed_52_, v_h_50_, v_implDetail_51_);
lean_dec(v_implDetail_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim___redArg(lean_object* v_auxDecl_54_){
_start:
{
lean_inc(v_auxDecl_54_);
return v_auxDecl_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim___redArg___boxed(lean_object* v_auxDecl_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_LocalDeclKind_auxDecl_elim___redArg(v_auxDecl_55_);
lean_dec(v_auxDecl_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim(lean_object* v_motive_57_, uint8_t v_t_58_, lean_object* v_h_59_, lean_object* v_auxDecl_60_){
_start:
{
lean_inc(v_auxDecl_60_);
return v_auxDecl_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim___boxed(lean_object* v_motive_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_auxDecl_64_){
_start:
{
uint8_t v_t_boxed_65_; lean_object* v_res_66_; 
v_t_boxed_65_ = lean_unbox(v_t_62_);
v_res_66_ = l_Lean_LocalDeclKind_auxDecl_elim(v_motive_61_, v_t_boxed_65_, v_h_63_, v_auxDecl_64_);
lean_dec(v_auxDecl_64_);
return v_res_66_;
}
}
static uint8_t _init_l_Lean_instInhabitedLocalDeclKind_default(void){
_start:
{
uint8_t v___x_67_; 
v___x_67_ = 0;
return v___x_67_;
}
}
static uint8_t _init_l_Lean_instInhabitedLocalDeclKind(void){
_start:
{
uint8_t v___x_68_; 
v___x_68_ = 0;
return v___x_68_;
}
}
static lean_object* _init_l_Lean_instReprLocalDeclKind_repr___closed__6(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = lean_unsigned_to_nat(2u);
v___x_79_ = lean_nat_to_int(v___x_78_);
return v___x_79_;
}
}
static lean_object* _init_l_Lean_instReprLocalDeclKind_repr___closed__7(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = lean_unsigned_to_nat(1u);
v___x_81_ = lean_nat_to_int(v___x_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLocalDeclKind_repr(uint8_t v_x_82_, lean_object* v_prec_83_){
_start:
{
lean_object* v___y_85_; lean_object* v___y_92_; lean_object* v___y_99_; 
switch(v_x_82_)
{
case 0:
{
lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_105_ = lean_unsigned_to_nat(1024u);
v___x_106_ = lean_nat_dec_le(v___x_105_, v_prec_83_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; 
v___x_107_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__6, &l_Lean_instReprLocalDeclKind_repr___closed__6_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__6);
v___y_85_ = v___x_107_;
goto v___jp_84_;
}
else
{
lean_object* v___x_108_; 
v___x_108_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__7, &l_Lean_instReprLocalDeclKind_repr___closed__7_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__7);
v___y_85_ = v___x_108_;
goto v___jp_84_;
}
}
case 1:
{
lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_109_ = lean_unsigned_to_nat(1024u);
v___x_110_ = lean_nat_dec_le(v___x_109_, v_prec_83_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; 
v___x_111_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__6, &l_Lean_instReprLocalDeclKind_repr___closed__6_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__6);
v___y_92_ = v___x_111_;
goto v___jp_91_;
}
else
{
lean_object* v___x_112_; 
v___x_112_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__7, &l_Lean_instReprLocalDeclKind_repr___closed__7_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__7);
v___y_92_ = v___x_112_;
goto v___jp_91_;
}
}
default: 
{
lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_113_ = lean_unsigned_to_nat(1024u);
v___x_114_ = lean_nat_dec_le(v___x_113_, v_prec_83_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; 
v___x_115_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__6, &l_Lean_instReprLocalDeclKind_repr___closed__6_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__6);
v___y_99_ = v___x_115_;
goto v___jp_98_;
}
else
{
lean_object* v___x_116_; 
v___x_116_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__7, &l_Lean_instReprLocalDeclKind_repr___closed__7_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__7);
v___y_99_ = v___x_116_;
goto v___jp_98_;
}
}
}
v___jp_84_:
{
lean_object* v___x_86_; lean_object* v___x_87_; uint8_t v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_86_ = ((lean_object*)(l_Lean_instReprLocalDeclKind_repr___closed__1));
lean_inc(v___y_85_);
v___x_87_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_87_, 0, v___y_85_);
lean_ctor_set(v___x_87_, 1, v___x_86_);
v___x_88_ = 0;
v___x_89_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_89_, 0, v___x_87_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*1, v___x_88_);
v___x_90_ = l_Repr_addAppParen(v___x_89_, v_prec_83_);
return v___x_90_;
}
v___jp_91_:
{
lean_object* v___x_93_; lean_object* v___x_94_; uint8_t v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_93_ = ((lean_object*)(l_Lean_instReprLocalDeclKind_repr___closed__3));
lean_inc(v___y_92_);
v___x_94_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_94_, 0, v___y_92_);
lean_ctor_set(v___x_94_, 1, v___x_93_);
v___x_95_ = 0;
v___x_96_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_96_, 0, v___x_94_);
lean_ctor_set_uint8(v___x_96_, sizeof(void*)*1, v___x_95_);
v___x_97_ = l_Repr_addAppParen(v___x_96_, v_prec_83_);
return v___x_97_;
}
v___jp_98_:
{
lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_100_ = ((lean_object*)(l_Lean_instReprLocalDeclKind_repr___closed__5));
lean_inc(v___y_99_);
v___x_101_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_101_, 0, v___y_99_);
lean_ctor_set(v___x_101_, 1, v___x_100_);
v___x_102_ = 0;
v___x_103_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_103_, 0, v___x_101_);
lean_ctor_set_uint8(v___x_103_, sizeof(void*)*1, v___x_102_);
v___x_104_ = l_Repr_addAppParen(v___x_103_, v_prec_83_);
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLocalDeclKind_repr___boxed(lean_object* v_x_117_, lean_object* v_prec_118_){
_start:
{
uint8_t v_x_177__boxed_119_; lean_object* v_res_120_; 
v_x_177__boxed_119_ = lean_unbox(v_x_117_);
v_res_120_ = l_Lean_instReprLocalDeclKind_repr(v_x_177__boxed_119_, v_prec_118_);
lean_dec(v_prec_118_);
return v_res_120_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDeclKind_ofNat(lean_object* v_n_123_){
_start:
{
lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_124_ = lean_unsigned_to_nat(0u);
v___x_125_ = lean_nat_dec_le(v_n_123_, v___x_124_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_126_ = lean_unsigned_to_nat(1u);
v___x_127_ = lean_nat_dec_le(v_n_123_, v___x_126_);
if (v___x_127_ == 0)
{
uint8_t v___x_128_; 
v___x_128_ = 2;
return v___x_128_;
}
else
{
uint8_t v___x_129_; 
v___x_129_ = 1;
return v___x_129_;
}
}
else
{
uint8_t v___x_130_; 
v___x_130_ = 0;
return v___x_130_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ofNat___boxed(lean_object* v_n_131_){
_start:
{
uint8_t v_res_132_; lean_object* v_r_133_; 
v_res_132_ = l_Lean_LocalDeclKind_ofNat(v_n_131_);
lean_dec(v_n_131_);
v_r_133_ = lean_box(v_res_132_);
return v_r_133_;
}
}
LEAN_EXPORT uint8_t l_Lean_instDecidableEqLocalDeclKind(uint8_t v_x_134_, uint8_t v_y_135_){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; uint8_t v___x_138_; 
v___x_136_ = l_Lean_LocalDeclKind_ctorIdx(v_x_134_);
v___x_137_ = l_Lean_LocalDeclKind_ctorIdx(v_y_135_);
v___x_138_ = lean_nat_dec_eq(v___x_136_, v___x_137_);
lean_dec(v___x_137_);
lean_dec(v___x_136_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_instDecidableEqLocalDeclKind___boxed(lean_object* v_x_139_, lean_object* v_y_140_){
_start:
{
uint8_t v_x_13__boxed_141_; uint8_t v_y_14__boxed_142_; uint8_t v_res_143_; lean_object* v_r_144_; 
v_x_13__boxed_141_ = lean_unbox(v_x_139_);
v_y_14__boxed_142_ = lean_unbox(v_y_140_);
v_res_143_ = l_Lean_instDecidableEqLocalDeclKind(v_x_13__boxed_141_, v_y_14__boxed_142_);
v_r_144_ = lean_box(v_res_143_);
return v_r_144_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableLocalDeclKind_hash(uint8_t v_x_145_){
_start:
{
switch(v_x_145_)
{
case 0:
{
uint64_t v___x_146_; 
v___x_146_ = 0ULL;
return v___x_146_;
}
case 1:
{
uint64_t v___x_147_; 
v___x_147_ = 1ULL;
return v___x_147_;
}
default: 
{
uint64_t v___x_148_; 
v___x_148_ = 2ULL;
return v___x_148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableLocalDeclKind_hash___boxed(lean_object* v_x_149_){
_start:
{
uint8_t v_x_40__boxed_150_; uint64_t v_res_151_; lean_object* v_r_152_; 
v_x_40__boxed_150_ = lean_unbox(v_x_149_);
v_res_151_ = l_Lean_instHashableLocalDeclKind_hash(v_x_40__boxed_150_);
v_r_152_ = lean_box_uint64(v_res_151_);
return v_r_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorIdx(lean_object* v_x_155_){
_start:
{
if (lean_obj_tag(v_x_155_) == 0)
{
lean_object* v___x_156_; 
v___x_156_ = lean_unsigned_to_nat(0u);
return v___x_156_;
}
else
{
lean_object* v___x_157_; 
v___x_157_ = lean_unsigned_to_nat(1u);
return v___x_157_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorIdx___boxed(lean_object* v_x_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Lean_LocalDecl_ctorIdx(v_x_158_);
lean_dec_ref(v_x_158_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim___redArg(lean_object* v_t_160_, lean_object* v_k_161_){
_start:
{
if (lean_obj_tag(v_t_160_) == 0)
{
lean_object* v_index_162_; lean_object* v_fvarId_163_; lean_object* v_userName_164_; lean_object* v_type_165_; uint8_t v_bi_166_; uint8_t v_kind_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v_index_162_ = lean_ctor_get(v_t_160_, 0);
lean_inc(v_index_162_);
v_fvarId_163_ = lean_ctor_get(v_t_160_, 1);
lean_inc(v_fvarId_163_);
v_userName_164_ = lean_ctor_get(v_t_160_, 2);
lean_inc(v_userName_164_);
v_type_165_ = lean_ctor_get(v_t_160_, 3);
lean_inc_ref(v_type_165_);
v_bi_166_ = lean_ctor_get_uint8(v_t_160_, sizeof(void*)*4);
v_kind_167_ = lean_ctor_get_uint8(v_t_160_, sizeof(void*)*4 + 1);
lean_dec_ref_known(v_t_160_, 4);
v___x_168_ = lean_box(v_bi_166_);
v___x_169_ = lean_box(v_kind_167_);
v___x_170_ = lean_apply_6(v_k_161_, v_index_162_, v_fvarId_163_, v_userName_164_, v_type_165_, v___x_168_, v___x_169_);
return v___x_170_;
}
else
{
lean_object* v_index_171_; lean_object* v_fvarId_172_; lean_object* v_userName_173_; lean_object* v_type_174_; lean_object* v_value_175_; uint8_t v_nondep_176_; uint8_t v_kind_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v_index_171_ = lean_ctor_get(v_t_160_, 0);
lean_inc(v_index_171_);
v_fvarId_172_ = lean_ctor_get(v_t_160_, 1);
lean_inc(v_fvarId_172_);
v_userName_173_ = lean_ctor_get(v_t_160_, 2);
lean_inc(v_userName_173_);
v_type_174_ = lean_ctor_get(v_t_160_, 3);
lean_inc_ref(v_type_174_);
v_value_175_ = lean_ctor_get(v_t_160_, 4);
lean_inc_ref(v_value_175_);
v_nondep_176_ = lean_ctor_get_uint8(v_t_160_, sizeof(void*)*5);
v_kind_177_ = lean_ctor_get_uint8(v_t_160_, sizeof(void*)*5 + 1);
lean_dec_ref_known(v_t_160_, 5);
v___x_178_ = lean_box(v_nondep_176_);
v___x_179_ = lean_box(v_kind_177_);
v___x_180_ = lean_apply_7(v_k_161_, v_index_171_, v_fvarId_172_, v_userName_173_, v_type_174_, v_value_175_, v___x_178_, v___x_179_);
return v___x_180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim(lean_object* v_motive_181_, lean_object* v_ctorIdx_182_, lean_object* v_t_183_, lean_object* v_h_184_, lean_object* v_k_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_183_, v_k_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim___boxed(lean_object* v_motive_187_, lean_object* v_ctorIdx_188_, lean_object* v_t_189_, lean_object* v_h_190_, lean_object* v_k_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_LocalDecl_ctorElim(v_motive_187_, v_ctorIdx_188_, v_t_189_, v_h_190_, v_k_191_);
lean_dec(v_ctorIdx_188_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_cdecl_elim___redArg(lean_object* v_t_193_, lean_object* v_cdecl_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_193_, v_cdecl_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_cdecl_elim(lean_object* v_motive_196_, lean_object* v_t_197_, lean_object* v_h_198_, lean_object* v_cdecl_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_197_, v_cdecl_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ldecl_elim___redArg(lean_object* v_t_201_, lean_object* v_ldecl_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_201_, v_ldecl_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ldecl_elim(lean_object* v_motive_204_, lean_object* v_t_205_, lean_object* v_h_206_, lean_object* v_ldecl_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_205_, v_ldecl_207_);
return v___x_208_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl_default___closed__2(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_212_ = lean_box(0);
v___x_213_ = ((lean_object*)(l_Lean_instInhabitedLocalDecl_default___closed__1));
v___x_214_ = l_Lean_Expr_const___override(v___x_213_, v___x_212_);
return v___x_214_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl_default___closed__3(void){
_start:
{
uint8_t v___x_215_; uint8_t v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_215_ = 0;
v___x_216_ = 0;
v___x_217_ = lean_obj_once(&l_Lean_instInhabitedLocalDecl_default___closed__2, &l_Lean_instInhabitedLocalDecl_default___closed__2_once, _init_l_Lean_instInhabitedLocalDecl_default___closed__2);
v___x_218_ = lean_box(0);
v___x_219_ = lean_unsigned_to_nat(0u);
v___x_220_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_220_, 0, v___x_219_);
lean_ctor_set(v___x_220_, 1, v___x_218_);
lean_ctor_set(v___x_220_, 2, v___x_218_);
lean_ctor_set(v___x_220_, 3, v___x_217_);
lean_ctor_set_uint8(v___x_220_, sizeof(void*)*4, v___x_216_);
lean_ctor_set_uint8(v___x_220_, sizeof(void*)*4 + 1, v___x_215_);
return v___x_220_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl_default(void){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = lean_obj_once(&l_Lean_instInhabitedLocalDecl_default___closed__3, &l_Lean_instInhabitedLocalDecl_default___closed__3_once, _init_l_Lean_instInhabitedLocalDecl_default___closed__3);
return v___x_221_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl(void){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_Lean_instInhabitedLocalDecl_default;
return v___x_222_;
}
}
LEAN_EXPORT lean_object* lean_mk_local_decl(lean_object* v_index_223_, lean_object* v_fvarId_224_, lean_object* v_userName_225_, lean_object* v_type_226_, uint8_t v_bi_227_){
_start:
{
uint8_t v___x_228_; lean_object* v___x_229_; 
v___x_228_ = 0;
v___x_229_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_229_, 0, v_index_223_);
lean_ctor_set(v___x_229_, 1, v_fvarId_224_);
lean_ctor_set(v___x_229_, 2, v_userName_225_);
lean_ctor_set(v___x_229_, 3, v_type_226_);
lean_ctor_set_uint8(v___x_229_, sizeof(void*)*4, v_bi_227_);
lean_ctor_set_uint8(v___x_229_, sizeof(void*)*4 + 1, v___x_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLocalDeclEx___boxed(lean_object* v_index_230_, lean_object* v_fvarId_231_, lean_object* v_userName_232_, lean_object* v_type_233_, lean_object* v_bi_234_){
_start:
{
uint8_t v_bi_boxed_235_; lean_object* v_res_236_; 
v_bi_boxed_235_ = lean_unbox(v_bi_234_);
v_res_236_ = lean_mk_local_decl(v_index_230_, v_fvarId_231_, v_userName_232_, v_type_233_, v_bi_boxed_235_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* lean_mk_let_decl(lean_object* v_index_237_, lean_object* v_fvarId_238_, lean_object* v_userName_239_, lean_object* v_type_240_, lean_object* v_val_241_){
_start:
{
uint8_t v___x_242_; uint8_t v___x_243_; lean_object* v___x_244_; 
v___x_242_ = 0;
v___x_243_ = 0;
v___x_244_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v___x_244_, 0, v_index_237_);
lean_ctor_set(v___x_244_, 1, v_fvarId_238_);
lean_ctor_set(v___x_244_, 2, v_userName_239_);
lean_ctor_set(v___x_244_, 3, v_type_240_);
lean_ctor_set(v___x_244_, 4, v_val_241_);
lean_ctor_set_uint8(v___x_244_, sizeof(void*)*5, v___x_242_);
lean_ctor_set_uint8(v___x_244_, sizeof(void*)*5 + 1, v___x_243_);
return v___x_244_;
}
}
LEAN_EXPORT uint8_t lean_local_decl_binder_info(lean_object* v_x_245_){
_start:
{
if (lean_obj_tag(v_x_245_) == 0)
{
uint8_t v_bi_246_; 
v_bi_246_ = lean_ctor_get_uint8(v_x_245_, sizeof(void*)*4);
lean_dec_ref_known(v_x_245_, 4);
return v_bi_246_;
}
else
{
uint8_t v___x_247_; 
lean_dec_ref(v_x_245_);
v___x_247_ = 0;
return v___x_247_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_binderInfoEx___boxed(lean_object* v_x_248_){
_start:
{
uint8_t v_res_249_; lean_object* v_r_250_; 
v_res_249_ = lean_local_decl_binder_info(v_x_248_);
v_r_250_ = lean_box(v_res_249_);
return v_r_250_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isLet(lean_object* v_x_251_, uint8_t v_x_252_){
_start:
{
if (lean_obj_tag(v_x_251_) == 0)
{
uint8_t v___x_253_; 
v___x_253_ = 0;
return v___x_253_;
}
else
{
uint8_t v_nondep_254_; 
v_nondep_254_ = lean_ctor_get_uint8(v_x_251_, sizeof(void*)*5);
if (v_nondep_254_ == 0)
{
uint8_t v___x_255_; 
v___x_255_ = 1;
return v___x_255_;
}
else
{
return v_x_252_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isLet___boxed(lean_object* v_x_256_, lean_object* v_x_257_){
_start:
{
uint8_t v_x_53__boxed_258_; uint8_t v_res_259_; lean_object* v_r_260_; 
v_x_53__boxed_258_ = lean_unbox(v_x_257_);
v_res_259_ = l_Lean_LocalDecl_isLet(v_x_256_, v_x_53__boxed_258_);
lean_dec_ref(v_x_256_);
v_r_260_ = lean_box(v_res_259_);
return v_r_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_index(lean_object* v_x_261_){
_start:
{
lean_object* v_index_262_; 
v_index_262_ = lean_ctor_get(v_x_261_, 0);
lean_inc(v_index_262_);
return v_index_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_index___boxed(lean_object* v_x_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_LocalDecl_index(v_x_263_);
lean_dec_ref(v_x_263_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setIndex(lean_object* v_x_265_, lean_object* v_x_266_){
_start:
{
if (lean_obj_tag(v_x_265_) == 0)
{
lean_object* v_fvarId_267_; lean_object* v_userName_268_; lean_object* v_type_269_; uint8_t v_bi_270_; uint8_t v_kind_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_278_; 
v_fvarId_267_ = lean_ctor_get(v_x_265_, 1);
v_userName_268_ = lean_ctor_get(v_x_265_, 2);
v_type_269_ = lean_ctor_get(v_x_265_, 3);
v_bi_270_ = lean_ctor_get_uint8(v_x_265_, sizeof(void*)*4);
v_kind_271_ = lean_ctor_get_uint8(v_x_265_, sizeof(void*)*4 + 1);
v_isSharedCheck_278_ = !lean_is_exclusive(v_x_265_);
if (v_isSharedCheck_278_ == 0)
{
lean_object* v_unused_279_; 
v_unused_279_ = lean_ctor_get(v_x_265_, 0);
lean_dec(v_unused_279_);
v___x_273_ = v_x_265_;
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_type_269_);
lean_inc(v_userName_268_);
lean_inc(v_fvarId_267_);
lean_dec(v_x_265_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_276_; 
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 0, v_x_266_);
v___x_276_ = v___x_273_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_x_266_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v_fvarId_267_);
lean_ctor_set(v_reuseFailAlloc_277_, 2, v_userName_268_);
lean_ctor_set(v_reuseFailAlloc_277_, 3, v_type_269_);
lean_ctor_set_uint8(v_reuseFailAlloc_277_, sizeof(void*)*4, v_bi_270_);
lean_ctor_set_uint8(v_reuseFailAlloc_277_, sizeof(void*)*4 + 1, v_kind_271_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
else
{
lean_object* v_fvarId_280_; lean_object* v_userName_281_; lean_object* v_type_282_; lean_object* v_value_283_; uint8_t v_nondep_284_; uint8_t v_kind_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_292_; 
v_fvarId_280_ = lean_ctor_get(v_x_265_, 1);
v_userName_281_ = lean_ctor_get(v_x_265_, 2);
v_type_282_ = lean_ctor_get(v_x_265_, 3);
v_value_283_ = lean_ctor_get(v_x_265_, 4);
v_nondep_284_ = lean_ctor_get_uint8(v_x_265_, sizeof(void*)*5);
v_kind_285_ = lean_ctor_get_uint8(v_x_265_, sizeof(void*)*5 + 1);
v_isSharedCheck_292_ = !lean_is_exclusive(v_x_265_);
if (v_isSharedCheck_292_ == 0)
{
lean_object* v_unused_293_; 
v_unused_293_ = lean_ctor_get(v_x_265_, 0);
lean_dec(v_unused_293_);
v___x_287_ = v_x_265_;
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_value_283_);
lean_inc(v_type_282_);
lean_inc(v_userName_281_);
lean_inc(v_fvarId_280_);
lean_dec(v_x_265_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_290_; 
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 0, v_x_266_);
v___x_290_ = v___x_287_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_x_266_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v_fvarId_280_);
lean_ctor_set(v_reuseFailAlloc_291_, 2, v_userName_281_);
lean_ctor_set(v_reuseFailAlloc_291_, 3, v_type_282_);
lean_ctor_set(v_reuseFailAlloc_291_, 4, v_value_283_);
lean_ctor_set_uint8(v_reuseFailAlloc_291_, sizeof(void*)*5, v_nondep_284_);
lean_ctor_set_uint8(v_reuseFailAlloc_291_, sizeof(void*)*5 + 1, v_kind_285_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_fvarId(lean_object* v_x_294_){
_start:
{
lean_object* v_fvarId_295_; 
v_fvarId_295_ = lean_ctor_get(v_x_294_, 1);
lean_inc(v_fvarId_295_);
return v_fvarId_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_fvarId___boxed(lean_object* v_x_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_LocalDecl_fvarId(v_x_296_);
lean_dec_ref(v_x_296_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_userName(lean_object* v_x_298_){
_start:
{
lean_object* v_userName_299_; 
v_userName_299_ = lean_ctor_get(v_x_298_, 2);
lean_inc(v_userName_299_);
return v_userName_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_userName___boxed(lean_object* v_x_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_LocalDecl_userName(v_x_300_);
lean_dec_ref(v_x_300_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_type(lean_object* v_x_302_){
_start:
{
lean_object* v_type_303_; 
v_type_303_ = lean_ctor_get(v_x_302_, 3);
lean_inc_ref(v_type_303_);
return v_type_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_type___boxed(lean_object* v_x_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_LocalDecl_type(v_x_304_);
lean_dec_ref(v_x_304_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setType(lean_object* v_x_306_, lean_object* v_x_307_){
_start:
{
if (lean_obj_tag(v_x_306_) == 0)
{
lean_object* v_index_308_; lean_object* v_fvarId_309_; lean_object* v_userName_310_; uint8_t v_bi_311_; uint8_t v_kind_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_319_; 
v_index_308_ = lean_ctor_get(v_x_306_, 0);
v_fvarId_309_ = lean_ctor_get(v_x_306_, 1);
v_userName_310_ = lean_ctor_get(v_x_306_, 2);
v_bi_311_ = lean_ctor_get_uint8(v_x_306_, sizeof(void*)*4);
v_kind_312_ = lean_ctor_get_uint8(v_x_306_, sizeof(void*)*4 + 1);
v_isSharedCheck_319_ = !lean_is_exclusive(v_x_306_);
if (v_isSharedCheck_319_ == 0)
{
lean_object* v_unused_320_; 
v_unused_320_ = lean_ctor_get(v_x_306_, 3);
lean_dec(v_unused_320_);
v___x_314_ = v_x_306_;
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_userName_310_);
lean_inc(v_fvarId_309_);
lean_inc(v_index_308_);
lean_dec(v_x_306_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_317_; 
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 3, v_x_307_);
v___x_317_ = v___x_314_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_index_308_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v_fvarId_309_);
lean_ctor_set(v_reuseFailAlloc_318_, 2, v_userName_310_);
lean_ctor_set(v_reuseFailAlloc_318_, 3, v_x_307_);
lean_ctor_set_uint8(v_reuseFailAlloc_318_, sizeof(void*)*4, v_bi_311_);
lean_ctor_set_uint8(v_reuseFailAlloc_318_, sizeof(void*)*4 + 1, v_kind_312_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
else
{
lean_object* v_index_321_; lean_object* v_fvarId_322_; lean_object* v_userName_323_; lean_object* v_value_324_; uint8_t v_nondep_325_; uint8_t v_kind_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_333_; 
v_index_321_ = lean_ctor_get(v_x_306_, 0);
v_fvarId_322_ = lean_ctor_get(v_x_306_, 1);
v_userName_323_ = lean_ctor_get(v_x_306_, 2);
v_value_324_ = lean_ctor_get(v_x_306_, 4);
v_nondep_325_ = lean_ctor_get_uint8(v_x_306_, sizeof(void*)*5);
v_kind_326_ = lean_ctor_get_uint8(v_x_306_, sizeof(void*)*5 + 1);
v_isSharedCheck_333_ = !lean_is_exclusive(v_x_306_);
if (v_isSharedCheck_333_ == 0)
{
lean_object* v_unused_334_; 
v_unused_334_ = lean_ctor_get(v_x_306_, 3);
lean_dec(v_unused_334_);
v___x_328_ = v_x_306_;
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_value_324_);
lean_inc(v_userName_323_);
lean_inc(v_fvarId_322_);
lean_inc(v_index_321_);
lean_dec(v_x_306_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 3, v_x_307_);
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_index_321_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v_fvarId_322_);
lean_ctor_set(v_reuseFailAlloc_332_, 2, v_userName_323_);
lean_ctor_set(v_reuseFailAlloc_332_, 3, v_x_307_);
lean_ctor_set(v_reuseFailAlloc_332_, 4, v_value_324_);
lean_ctor_set_uint8(v_reuseFailAlloc_332_, sizeof(void*)*5, v_nondep_325_);
lean_ctor_set_uint8(v_reuseFailAlloc_332_, sizeof(void*)*5 + 1, v_kind_326_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_binderInfo(lean_object* v_x_335_){
_start:
{
if (lean_obj_tag(v_x_335_) == 0)
{
uint8_t v_bi_336_; 
v_bi_336_ = lean_ctor_get_uint8(v_x_335_, sizeof(void*)*4);
return v_bi_336_;
}
else
{
uint8_t v___x_337_; 
v___x_337_ = 0;
return v___x_337_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_binderInfo___boxed(lean_object* v_x_338_){
_start:
{
uint8_t v_res_339_; lean_object* v_r_340_; 
v_res_339_ = l_Lean_LocalDecl_binderInfo(v_x_338_);
lean_dec_ref(v_x_338_);
v_r_340_ = lean_box(v_res_339_);
return v_r_340_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_kind(lean_object* v_x_341_){
_start:
{
if (lean_obj_tag(v_x_341_) == 0)
{
uint8_t v_kind_342_; 
v_kind_342_ = lean_ctor_get_uint8(v_x_341_, sizeof(void*)*4 + 1);
return v_kind_342_;
}
else
{
uint8_t v_kind_343_; 
v_kind_343_ = lean_ctor_get_uint8(v_x_341_, sizeof(void*)*5 + 1);
return v_kind_343_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_kind___boxed(lean_object* v_x_344_){
_start:
{
uint8_t v_res_345_; lean_object* v_r_346_; 
v_res_345_ = l_Lean_LocalDecl_kind(v_x_344_);
lean_dec_ref(v_x_344_);
v_r_346_ = lean_box(v_res_345_);
return v_r_346_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object* v_d_347_){
_start:
{
uint8_t v___y_349_; 
if (lean_obj_tag(v_d_347_) == 0)
{
uint8_t v_kind_352_; 
v_kind_352_ = lean_ctor_get_uint8(v_d_347_, sizeof(void*)*4 + 1);
v___y_349_ = v_kind_352_;
goto v___jp_348_;
}
else
{
uint8_t v_kind_353_; 
v_kind_353_ = lean_ctor_get_uint8(v_d_347_, sizeof(void*)*5 + 1);
v___y_349_ = v_kind_353_;
goto v___jp_348_;
}
v___jp_348_:
{
uint8_t v___x_350_; uint8_t v___x_351_; 
v___x_350_ = 2;
v___x_351_ = l_Lean_instDecidableEqLocalDeclKind(v___y_349_, v___x_350_);
return v___x_351_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isAuxDecl___boxed(lean_object* v_d_354_){
_start:
{
uint8_t v_res_355_; lean_object* v_r_356_; 
v_res_355_ = l_Lean_LocalDecl_isAuxDecl(v_d_354_);
lean_dec_ref(v_d_354_);
v_r_356_ = lean_box(v_res_355_);
return v_r_356_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object* v_d_357_){
_start:
{
uint8_t v___y_359_; 
if (lean_obj_tag(v_d_357_) == 0)
{
uint8_t v_kind_364_; 
v_kind_364_ = lean_ctor_get_uint8(v_d_357_, sizeof(void*)*4 + 1);
v___y_359_ = v_kind_364_;
goto v___jp_358_;
}
else
{
uint8_t v_kind_365_; 
v_kind_365_ = lean_ctor_get_uint8(v_d_357_, sizeof(void*)*5 + 1);
v___y_359_ = v_kind_365_;
goto v___jp_358_;
}
v___jp_358_:
{
uint8_t v___x_360_; uint8_t v___x_361_; 
v___x_360_ = 0;
v___x_361_ = l_Lean_instDecidableEqLocalDeclKind(v___y_359_, v___x_360_);
if (v___x_361_ == 0)
{
uint8_t v___x_362_; 
v___x_362_ = 1;
return v___x_362_;
}
else
{
uint8_t v___x_363_; 
v___x_363_ = 0;
return v___x_363_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isImplementationDetail___boxed(lean_object* v_d_366_){
_start:
{
uint8_t v_res_367_; lean_object* v_r_368_; 
v_res_367_ = l_Lean_LocalDecl_isImplementationDetail(v_d_366_);
lean_dec_ref(v_d_366_);
v_r_368_ = lean_box(v_res_367_);
return v_r_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value_x3f(lean_object* v_x_369_, uint8_t v_x_370_){
_start:
{
if (lean_obj_tag(v_x_369_) == 1)
{
uint8_t v_nondep_371_; 
v_nondep_371_ = lean_ctor_get_uint8(v_x_369_, sizeof(void*)*5);
if (v_nondep_371_ == 0)
{
lean_object* v_value_372_; lean_object* v___x_373_; 
v_value_372_ = lean_ctor_get(v_x_369_, 4);
lean_inc_ref(v_value_372_);
v___x_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_373_, 0, v_value_372_);
return v___x_373_;
}
else
{
if (v_x_370_ == 1)
{
lean_object* v_value_374_; lean_object* v___x_375_; 
v_value_374_ = lean_ctor_get(v_x_369_, 4);
lean_inc_ref(v_value_374_);
v___x_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_375_, 0, v_value_374_);
return v___x_375_;
}
else
{
lean_object* v___x_376_; 
v___x_376_ = lean_box(0);
return v___x_376_;
}
}
}
else
{
lean_object* v___x_377_; 
v___x_377_ = lean_box(0);
return v___x_377_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value_x3f___boxed(lean_object* v_x_378_, lean_object* v_x_379_){
_start:
{
uint8_t v_x_57__boxed_380_; lean_object* v_res_381_; 
v_x_57__boxed_380_ = lean_unbox(v_x_379_);
v_res_381_ = l_Lean_LocalDecl_value_x3f(v_x_378_, v_x_57__boxed_380_);
lean_dec_ref(v_x_378_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_LocalDecl_value_spec__0(lean_object* v_msg_382_){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = l_Lean_instInhabitedExpr;
v___x_384_ = lean_panic_fn_borrowed(v___x_383_, v_msg_382_);
return v___x_384_;
}
}
static lean_object* _init_l_Lean_LocalDecl_value___closed__3(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_388_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__2));
v___x_389_ = lean_unsigned_to_nat(54u);
v___x_390_ = lean_unsigned_to_nat(172u);
v___x_391_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__1));
v___x_392_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_393_ = l_mkPanicMessageWithDecl(v___x_392_, v___x_391_, v___x_390_, v___x_389_, v___x_388_);
return v___x_393_;
}
}
static lean_object* _init_l_Lean_LocalDecl_value___closed__5(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_395_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__4));
v___x_396_ = lean_unsigned_to_nat(54u);
v___x_397_ = lean_unsigned_to_nat(175u);
v___x_398_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__1));
v___x_399_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_400_ = l_mkPanicMessageWithDecl(v___x_399_, v___x_398_, v___x_397_, v___x_396_, v___x_395_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value(lean_object* v_x_401_, uint8_t v_x_402_){
_start:
{
if (lean_obj_tag(v_x_401_) == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = lean_obj_once(&l_Lean_LocalDecl_value___closed__3, &l_Lean_LocalDecl_value___closed__3_once, _init_l_Lean_LocalDecl_value___closed__3);
v___x_404_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_403_);
return v___x_404_;
}
else
{
uint8_t v_nondep_405_; 
v_nondep_405_ = lean_ctor_get_uint8(v_x_401_, sizeof(void*)*5);
if (v_nondep_405_ == 0)
{
lean_object* v_value_406_; 
v_value_406_ = lean_ctor_get(v_x_401_, 4);
lean_inc_ref(v_value_406_);
return v_value_406_;
}
else
{
if (v_x_402_ == 0)
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = lean_obj_once(&l_Lean_LocalDecl_value___closed__5, &l_Lean_LocalDecl_value___closed__5_once, _init_l_Lean_LocalDecl_value___closed__5);
v___x_408_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_407_);
return v___x_408_;
}
else
{
lean_object* v_value_409_; 
v_value_409_ = lean_ctor_get(v_x_401_, 4);
lean_inc_ref(v_value_409_);
return v_value_409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value___boxed(lean_object* v_x_410_, lean_object* v_x_411_){
_start:
{
uint8_t v_x_143__boxed_412_; lean_object* v_res_413_; 
v_x_143__boxed_412_ = lean_unbox(v_x_411_);
v_res_413_ = l_Lean_LocalDecl_value(v_x_410_, v_x_143__boxed_412_);
lean_dec_ref(v_x_410_);
return v_res_413_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_hasValue(lean_object* v_x_414_, uint8_t v_x_415_){
_start:
{
if (lean_obj_tag(v_x_414_) == 0)
{
uint8_t v___x_416_; 
v___x_416_ = 0;
return v___x_416_;
}
else
{
uint8_t v_nondep_417_; 
v_nondep_417_ = lean_ctor_get_uint8(v_x_414_, sizeof(void*)*5);
if (v_nondep_417_ == 0)
{
uint8_t v___x_418_; 
v___x_418_ = 1;
return v___x_418_;
}
else
{
return v_x_415_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_hasValue___boxed(lean_object* v_x_419_, lean_object* v_x_420_){
_start:
{
uint8_t v_x_72__boxed_421_; uint8_t v_res_422_; lean_object* v_r_423_; 
v_x_72__boxed_421_ = lean_unbox(v_x_420_);
v_res_422_ = l_Lean_LocalDecl_hasValue(v_x_419_, v_x_72__boxed_421_);
lean_dec_ref(v_x_419_);
v_r_423_ = lean_box(v_res_422_);
return v_r_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setValue(lean_object* v_x_424_, lean_object* v_x_425_){
_start:
{
if (lean_obj_tag(v_x_424_) == 1)
{
lean_object* v_index_426_; lean_object* v_fvarId_427_; lean_object* v_userName_428_; lean_object* v_type_429_; uint8_t v_nondep_430_; uint8_t v_kind_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_438_; 
v_index_426_ = lean_ctor_get(v_x_424_, 0);
v_fvarId_427_ = lean_ctor_get(v_x_424_, 1);
v_userName_428_ = lean_ctor_get(v_x_424_, 2);
v_type_429_ = lean_ctor_get(v_x_424_, 3);
v_nondep_430_ = lean_ctor_get_uint8(v_x_424_, sizeof(void*)*5);
v_kind_431_ = lean_ctor_get_uint8(v_x_424_, sizeof(void*)*5 + 1);
v_isSharedCheck_438_ = !lean_is_exclusive(v_x_424_);
if (v_isSharedCheck_438_ == 0)
{
lean_object* v_unused_439_; 
v_unused_439_ = lean_ctor_get(v_x_424_, 4);
lean_dec(v_unused_439_);
v___x_433_ = v_x_424_;
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_type_429_);
lean_inc(v_userName_428_);
lean_inc(v_fvarId_427_);
lean_inc(v_index_426_);
lean_dec(v_x_424_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_436_; 
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 4, v_x_425_);
v___x_436_ = v___x_433_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_index_426_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v_fvarId_427_);
lean_ctor_set(v_reuseFailAlloc_437_, 2, v_userName_428_);
lean_ctor_set(v_reuseFailAlloc_437_, 3, v_type_429_);
lean_ctor_set(v_reuseFailAlloc_437_, 4, v_x_425_);
lean_ctor_set_uint8(v_reuseFailAlloc_437_, sizeof(void*)*5, v_nondep_430_);
lean_ctor_set_uint8(v_reuseFailAlloc_437_, sizeof(void*)*5 + 1, v_kind_431_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
else
{
lean_dec_ref(v_x_425_);
return v_x_424_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setNondep(lean_object* v_x_440_, uint8_t v_x_441_){
_start:
{
if (lean_obj_tag(v_x_440_) == 1)
{
lean_object* v_index_442_; lean_object* v_fvarId_443_; lean_object* v_userName_444_; lean_object* v_type_445_; lean_object* v_value_446_; uint8_t v_kind_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
v_index_442_ = lean_ctor_get(v_x_440_, 0);
v_fvarId_443_ = lean_ctor_get(v_x_440_, 1);
v_userName_444_ = lean_ctor_get(v_x_440_, 2);
v_type_445_ = lean_ctor_get(v_x_440_, 3);
v_value_446_ = lean_ctor_get(v_x_440_, 4);
v_kind_447_ = lean_ctor_get_uint8(v_x_440_, sizeof(void*)*5 + 1);
v_isSharedCheck_454_ = !lean_is_exclusive(v_x_440_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v_x_440_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_value_446_);
lean_inc(v_type_445_);
lean_inc(v_userName_444_);
lean_inc(v_fvarId_443_);
lean_inc(v_index_442_);
lean_dec(v_x_440_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_index_442_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v_fvarId_443_);
lean_ctor_set(v_reuseFailAlloc_453_, 2, v_userName_444_);
lean_ctor_set(v_reuseFailAlloc_453_, 3, v_type_445_);
lean_ctor_set(v_reuseFailAlloc_453_, 4, v_value_446_);
lean_ctor_set_uint8(v_reuseFailAlloc_453_, sizeof(void*)*5 + 1, v_kind_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
lean_ctor_set_uint8(v___x_452_, sizeof(void*)*5, v_x_441_);
return v___x_452_;
}
}
}
else
{
return v_x_440_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setNondep___boxed(lean_object* v_x_455_, lean_object* v_x_456_){
_start:
{
uint8_t v_x_27__boxed_457_; lean_object* v_res_458_; 
v_x_27__boxed_457_ = lean_unbox(v_x_456_);
v_res_458_ = l_Lean_LocalDecl_setNondep(v_x_455_, v_x_27__boxed_457_);
return v_res_458_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isNondep(lean_object* v_x_459_){
_start:
{
if (lean_obj_tag(v_x_459_) == 1)
{
uint8_t v_nondep_460_; 
v_nondep_460_ = lean_ctor_get_uint8(v_x_459_, sizeof(void*)*5);
return v_nondep_460_;
}
else
{
uint8_t v___x_461_; 
v___x_461_ = 0;
return v___x_461_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isNondep___boxed(lean_object* v_x_462_){
_start:
{
uint8_t v_res_463_; lean_object* v_r_464_; 
v_res_463_ = l_Lean_LocalDecl_isNondep(v_x_462_);
lean_dec_ref(v_x_462_);
v_r_464_ = lean_box(v_res_463_);
return v_r_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setUserName(lean_object* v_x_465_, lean_object* v_x_466_){
_start:
{
if (lean_obj_tag(v_x_465_) == 0)
{
lean_object* v_index_467_; lean_object* v_fvarId_468_; lean_object* v_type_469_; uint8_t v_bi_470_; uint8_t v_kind_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
v_index_467_ = lean_ctor_get(v_x_465_, 0);
v_fvarId_468_ = lean_ctor_get(v_x_465_, 1);
v_type_469_ = lean_ctor_get(v_x_465_, 3);
v_bi_470_ = lean_ctor_get_uint8(v_x_465_, sizeof(void*)*4);
v_kind_471_ = lean_ctor_get_uint8(v_x_465_, sizeof(void*)*4 + 1);
v_isSharedCheck_478_ = !lean_is_exclusive(v_x_465_);
if (v_isSharedCheck_478_ == 0)
{
lean_object* v_unused_479_; 
v_unused_479_ = lean_ctor_get(v_x_465_, 2);
lean_dec(v_unused_479_);
v___x_473_ = v_x_465_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_type_469_);
lean_inc(v_fvarId_468_);
lean_inc(v_index_467_);
lean_dec(v_x_465_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 2, v_x_466_);
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_index_467_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v_fvarId_468_);
lean_ctor_set(v_reuseFailAlloc_477_, 2, v_x_466_);
lean_ctor_set(v_reuseFailAlloc_477_, 3, v_type_469_);
lean_ctor_set_uint8(v_reuseFailAlloc_477_, sizeof(void*)*4, v_bi_470_);
lean_ctor_set_uint8(v_reuseFailAlloc_477_, sizeof(void*)*4 + 1, v_kind_471_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
else
{
lean_object* v_index_480_; lean_object* v_fvarId_481_; lean_object* v_type_482_; lean_object* v_value_483_; uint8_t v_nondep_484_; uint8_t v_kind_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_492_; 
v_index_480_ = lean_ctor_get(v_x_465_, 0);
v_fvarId_481_ = lean_ctor_get(v_x_465_, 1);
v_type_482_ = lean_ctor_get(v_x_465_, 3);
v_value_483_ = lean_ctor_get(v_x_465_, 4);
v_nondep_484_ = lean_ctor_get_uint8(v_x_465_, sizeof(void*)*5);
v_kind_485_ = lean_ctor_get_uint8(v_x_465_, sizeof(void*)*5 + 1);
v_isSharedCheck_492_ = !lean_is_exclusive(v_x_465_);
if (v_isSharedCheck_492_ == 0)
{
lean_object* v_unused_493_; 
v_unused_493_ = lean_ctor_get(v_x_465_, 2);
lean_dec(v_unused_493_);
v___x_487_ = v_x_465_;
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_value_483_);
lean_inc(v_type_482_);
lean_inc(v_fvarId_481_);
lean_inc(v_index_480_);
lean_dec(v_x_465_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_490_; 
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 2, v_x_466_);
v___x_490_ = v___x_487_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_index_480_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_fvarId_481_);
lean_ctor_set(v_reuseFailAlloc_491_, 2, v_x_466_);
lean_ctor_set(v_reuseFailAlloc_491_, 3, v_type_482_);
lean_ctor_set(v_reuseFailAlloc_491_, 4, v_value_483_);
lean_ctor_set_uint8(v_reuseFailAlloc_491_, sizeof(void*)*5, v_nondep_484_);
lean_ctor_set_uint8(v_reuseFailAlloc_491_, sizeof(void*)*5 + 1, v_kind_485_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(lean_object* v_msg_494_){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = l_Lean_instInhabitedLocalDecl_default;
v___x_496_ = lean_panic_fn_borrowed(v___x_495_, v_msg_494_);
return v___x_496_;
}
}
static lean_object* _init_l_Lean_LocalDecl_setBinderInfo___closed__2(void){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_499_ = ((lean_object*)(l_Lean_LocalDecl_setBinderInfo___closed__1));
v___x_500_ = lean_unsigned_to_nat(38u);
v___x_501_ = lean_unsigned_to_nat(237u);
v___x_502_ = ((lean_object*)(l_Lean_LocalDecl_setBinderInfo___closed__0));
v___x_503_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_504_ = l_mkPanicMessageWithDecl(v___x_503_, v___x_502_, v___x_501_, v___x_500_, v___x_499_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setBinderInfo(lean_object* v_x_505_, uint8_t v_x_506_){
_start:
{
if (lean_obj_tag(v_x_505_) == 0)
{
lean_object* v_index_507_; lean_object* v_fvarId_508_; lean_object* v_userName_509_; lean_object* v_type_510_; uint8_t v_kind_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_518_; 
v_index_507_ = lean_ctor_get(v_x_505_, 0);
v_fvarId_508_ = lean_ctor_get(v_x_505_, 1);
v_userName_509_ = lean_ctor_get(v_x_505_, 2);
v_type_510_ = lean_ctor_get(v_x_505_, 3);
v_kind_511_ = lean_ctor_get_uint8(v_x_505_, sizeof(void*)*4 + 1);
v_isSharedCheck_518_ = !lean_is_exclusive(v_x_505_);
if (v_isSharedCheck_518_ == 0)
{
v___x_513_ = v_x_505_;
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_type_510_);
lean_inc(v_userName_509_);
lean_inc(v_fvarId_508_);
lean_inc(v_index_507_);
lean_dec(v_x_505_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
if (v_isShared_514_ == 0)
{
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_index_507_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_fvarId_508_);
lean_ctor_set(v_reuseFailAlloc_517_, 2, v_userName_509_);
lean_ctor_set(v_reuseFailAlloc_517_, 3, v_type_510_);
lean_ctor_set_uint8(v_reuseFailAlloc_517_, sizeof(void*)*4 + 1, v_kind_511_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
lean_ctor_set_uint8(v___x_516_, sizeof(void*)*4, v_x_506_);
return v___x_516_;
}
}
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; 
lean_dec_ref_known(v_x_505_, 5);
v___x_519_ = lean_obj_once(&l_Lean_LocalDecl_setBinderInfo___closed__2, &l_Lean_LocalDecl_setBinderInfo___closed__2_once, _init_l_Lean_LocalDecl_setBinderInfo___closed__2);
v___x_520_ = l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(v___x_519_);
return v___x_520_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setBinderInfo___boxed(lean_object* v_x_521_, lean_object* v_x_522_){
_start:
{
uint8_t v_x_84__boxed_523_; lean_object* v_res_524_; 
v_x_84__boxed_523_ = lean_unbox(v_x_522_);
v_res_524_ = l_Lean_LocalDecl_setBinderInfo(v_x_521_, v_x_84__boxed_523_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_toExpr(lean_object* v_decl_525_){
_start:
{
lean_object* v_fvarId_526_; lean_object* v___x_527_; 
v_fvarId_526_ = lean_ctor_get(v_decl_525_, 1);
lean_inc(v_fvarId_526_);
lean_dec_ref(v_decl_525_);
v___x_527_ = l_Lean_mkFVar(v_fvarId_526_);
return v___x_527_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_hasExprMVar(lean_object* v_x_528_){
_start:
{
if (lean_obj_tag(v_x_528_) == 0)
{
lean_object* v_type_529_; uint8_t v___x_530_; 
v_type_529_ = lean_ctor_get(v_x_528_, 3);
v___x_530_ = l_Lean_Expr_hasExprMVar(v_type_529_);
return v___x_530_;
}
else
{
lean_object* v_type_531_; lean_object* v_value_532_; uint8_t v___x_533_; 
v_type_531_ = lean_ctor_get(v_x_528_, 3);
v_value_532_ = lean_ctor_get(v_x_528_, 4);
v___x_533_ = l_Lean_Expr_hasExprMVar(v_type_531_);
if (v___x_533_ == 0)
{
uint8_t v___x_534_; 
v___x_534_ = l_Lean_Expr_hasExprMVar(v_value_532_);
return v___x_534_;
}
else
{
return v___x_533_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_hasExprMVar___boxed(lean_object* v_x_535_){
_start:
{
uint8_t v_res_536_; lean_object* v_r_537_; 
v_res_536_ = l_Lean_LocalDecl_hasExprMVar(v_x_535_);
lean_dec_ref(v_x_535_);
v_r_537_ = lean_box(v_res_536_);
return v_r_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setKind(lean_object* v_x_538_, uint8_t v_x_539_){
_start:
{
if (lean_obj_tag(v_x_538_) == 0)
{
lean_object* v_index_540_; lean_object* v_fvarId_541_; lean_object* v_userName_542_; lean_object* v_type_543_; uint8_t v_bi_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
v_index_540_ = lean_ctor_get(v_x_538_, 0);
v_fvarId_541_ = lean_ctor_get(v_x_538_, 1);
v_userName_542_ = lean_ctor_get(v_x_538_, 2);
v_type_543_ = lean_ctor_get(v_x_538_, 3);
v_bi_544_ = lean_ctor_get_uint8(v_x_538_, sizeof(void*)*4);
v_isSharedCheck_551_ = !lean_is_exclusive(v_x_538_);
if (v_isSharedCheck_551_ == 0)
{
v___x_546_ = v_x_538_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_type_543_);
lean_inc(v_userName_542_);
lean_inc(v_fvarId_541_);
lean_inc(v_index_540_);
lean_dec(v_x_538_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_index_540_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v_fvarId_541_);
lean_ctor_set(v_reuseFailAlloc_550_, 2, v_userName_542_);
lean_ctor_set(v_reuseFailAlloc_550_, 3, v_type_543_);
lean_ctor_set_uint8(v_reuseFailAlloc_550_, sizeof(void*)*4, v_bi_544_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
lean_ctor_set_uint8(v___x_549_, sizeof(void*)*4 + 1, v_x_539_);
return v___x_549_;
}
}
}
else
{
lean_object* v_index_552_; lean_object* v_fvarId_553_; lean_object* v_userName_554_; lean_object* v_type_555_; lean_object* v_value_556_; uint8_t v_nondep_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_564_; 
v_index_552_ = lean_ctor_get(v_x_538_, 0);
v_fvarId_553_ = lean_ctor_get(v_x_538_, 1);
v_userName_554_ = lean_ctor_get(v_x_538_, 2);
v_type_555_ = lean_ctor_get(v_x_538_, 3);
v_value_556_ = lean_ctor_get(v_x_538_, 4);
v_nondep_557_ = lean_ctor_get_uint8(v_x_538_, sizeof(void*)*5);
v_isSharedCheck_564_ = !lean_is_exclusive(v_x_538_);
if (v_isSharedCheck_564_ == 0)
{
v___x_559_ = v_x_538_;
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_value_556_);
lean_inc(v_type_555_);
lean_inc(v_userName_554_);
lean_inc(v_fvarId_553_);
lean_inc(v_index_552_);
lean_dec(v_x_538_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_562_; 
if (v_isShared_560_ == 0)
{
v___x_562_ = v___x_559_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_index_552_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v_fvarId_553_);
lean_ctor_set(v_reuseFailAlloc_563_, 2, v_userName_554_);
lean_ctor_set(v_reuseFailAlloc_563_, 3, v_type_555_);
lean_ctor_set(v_reuseFailAlloc_563_, 4, v_value_556_);
lean_ctor_set_uint8(v_reuseFailAlloc_563_, sizeof(void*)*5, v_nondep_557_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
lean_ctor_set_uint8(v___x_562_, sizeof(void*)*5 + 1, v_x_539_);
return v___x_562_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setKind___boxed(lean_object* v_x_565_, lean_object* v_x_566_){
_start:
{
uint8_t v_x_31__boxed_567_; lean_object* v_res_568_; 
v_x_31__boxed_567_ = lean_unbox(v_x_566_);
v_res_568_ = l_Lean_LocalDecl_setKind(v_x_565_, v_x_31__boxed_567_);
return v_res_568_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__0(void){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_569_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__1(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__0, &l_Lean_instInhabitedLocalContext_default___closed__0_once, _init_l_Lean_instInhabitedLocalContext_default___closed__0);
v___x_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
return v___x_571_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__2(void){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_572_ = lean_unsigned_to_nat(32u);
v___x_573_ = lean_mk_empty_array_with_capacity(v___x_572_);
v___x_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
return v___x_574_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__3(void){
_start:
{
size_t v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_575_ = ((size_t)5ULL);
v___x_576_ = lean_unsigned_to_nat(0u);
v___x_577_ = lean_unsigned_to_nat(32u);
v___x_578_ = lean_mk_empty_array_with_capacity(v___x_577_);
v___x_579_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__2, &l_Lean_instInhabitedLocalContext_default___closed__2_once, _init_l_Lean_instInhabitedLocalContext_default___closed__2);
v___x_580_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_580_, 0, v___x_579_);
lean_ctor_set(v___x_580_, 1, v___x_578_);
lean_ctor_set(v___x_580_, 2, v___x_576_);
lean_ctor_set(v___x_580_, 3, v___x_576_);
lean_ctor_set_usize(v___x_580_, 4, v___x_575_);
return v___x_580_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__4(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_581_ = lean_box(1);
v___x_582_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__3, &l_Lean_instInhabitedLocalContext_default___closed__3_once, _init_l_Lean_instInhabitedLocalContext_default___closed__3);
v___x_583_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__1, &l_Lean_instInhabitedLocalContext_default___closed__1_once, _init_l_Lean_instInhabitedLocalContext_default___closed__1);
v___x_584_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
lean_ctor_set(v___x_584_, 1, v___x_582_);
lean_ctor_set(v___x_584_, 2, v___x_581_);
return v___x_584_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default(void){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__4, &l_Lean_instInhabitedLocalContext_default___closed__4_once, _init_l_Lean_instInhabitedLocalContext_default___closed__4);
return v___x_585_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext(void){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Lean_instInhabitedLocalContext_default;
return v___x_586_;
}
}
LEAN_EXPORT lean_object* lean_mk_empty_local_ctx(lean_object* v_x_587_){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_588_ = lean_unsigned_to_nat(32u);
v___x_589_ = lean_mk_empty_array_with_capacity(v___x_588_);
lean_dec_ref(v___x_589_);
v___x_590_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__4, &l_Lean_instInhabitedLocalContext_default___closed__4_once, _init_l_Lean_instInhabitedLocalContext_default___closed__4);
return v___x_590_;
}
}
static lean_object* _init_l_Lean_LocalContext_empty(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_591_ = lean_unsigned_to_nat(32u);
v___x_592_ = lean_mk_empty_array_with_capacity(v___x_591_);
lean_dec_ref(v___x_592_);
v___x_593_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__4, &l_Lean_instInhabitedLocalContext_default___closed__4_once, _init_l_Lean_instInhabitedLocalContext_default___closed__4);
return v___x_593_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg(lean_object* v_x_594_){
_start:
{
uint8_t v___x_595_; 
v___x_595_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg___boxed(lean_object* v_x_596_){
_start:
{
uint8_t v_res_597_; lean_object* v_r_598_; 
v_res_597_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg(v_x_596_);
lean_dec_ref(v_x_596_);
v_r_598_ = lean_box(v_res_597_);
return v_r_598_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0(lean_object* v_00_u03b2_599_, lean_object* v_x_600_){
_start:
{
uint8_t v___x_601_; 
v___x_601_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___boxed(lean_object* v_00_u03b2_602_, lean_object* v_x_603_){
_start:
{
uint8_t v_res_604_; lean_object* v_r_605_; 
v_res_604_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0(v_00_u03b2_602_, v_x_603_);
lean_dec_ref(v_x_603_);
v_r_605_ = lean_box(v_res_604_);
return v_r_605_;
}
}
LEAN_EXPORT uint8_t lean_local_ctx_is_empty(lean_object* v_lctx_606_){
_start:
{
lean_object* v_fvarIdToDecl_607_; uint8_t v___x_608_; 
v_fvarIdToDecl_607_ = lean_ctor_get(v_lctx_606_, 0);
lean_inc_ref(v_fvarIdToDecl_607_);
lean_dec_ref(v_lctx_606_);
v___x_608_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_fvarIdToDecl_607_);
lean_dec_ref(v_fvarIdToDecl_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_isEmpty___boxed(lean_object* v_lctx_609_){
_start:
{
uint8_t v_res_610_; lean_object* v_r_611_; 
v_res_610_ = lean_local_ctx_is_empty(v_lctx_609_);
v_r_611_ = lean_box(v_res_610_);
return v_r_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_612_, lean_object* v_x_613_, lean_object* v_x_614_, lean_object* v_x_615_){
_start:
{
lean_object* v_ks_616_; lean_object* v_vs_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_641_; 
v_ks_616_ = lean_ctor_get(v_x_612_, 0);
v_vs_617_ = lean_ctor_get(v_x_612_, 1);
v_isSharedCheck_641_ = !lean_is_exclusive(v_x_612_);
if (v_isSharedCheck_641_ == 0)
{
v___x_619_ = v_x_612_;
v_isShared_620_ = v_isSharedCheck_641_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_vs_617_);
lean_inc(v_ks_616_);
lean_dec(v_x_612_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_641_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_621_ = lean_array_get_size(v_ks_616_);
v___x_622_ = lean_nat_dec_lt(v_x_613_, v___x_621_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_626_; 
lean_dec(v_x_613_);
v___x_623_ = lean_array_push(v_ks_616_, v_x_614_);
v___x_624_ = lean_array_push(v_vs_617_, v_x_615_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 1, v___x_624_);
lean_ctor_set(v___x_619_, 0, v___x_623_);
v___x_626_ = v___x_619_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v___x_624_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
else
{
lean_object* v_k_x27_628_; uint8_t v___x_629_; 
v_k_x27_628_ = lean_array_fget_borrowed(v_ks_616_, v_x_613_);
v___x_629_ = l_Lean_instBEqFVarId_beq(v_x_614_, v_k_x27_628_);
if (v___x_629_ == 0)
{
lean_object* v___x_631_; 
if (v_isShared_620_ == 0)
{
v___x_631_ = v___x_619_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_ks_616_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v_vs_617_);
v___x_631_ = v_reuseFailAlloc_635_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = lean_unsigned_to_nat(1u);
v___x_633_ = lean_nat_add(v_x_613_, v___x_632_);
lean_dec(v_x_613_);
v_x_612_ = v___x_631_;
v_x_613_ = v___x_633_;
goto _start;
}
}
else
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_639_; 
v___x_636_ = lean_array_fset(v_ks_616_, v_x_613_, v_x_614_);
v___x_637_ = lean_array_fset(v_vs_617_, v_x_613_, v_x_615_);
lean_dec(v_x_613_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 1, v___x_637_);
lean_ctor_set(v___x_619_, 0, v___x_636_);
v___x_639_ = v___x_619_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_636_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v___x_637_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1___redArg(lean_object* v_n_642_, lean_object* v_k_643_, lean_object* v_v_644_){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = lean_unsigned_to_nat(0u);
v___x_646_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2___redArg(v_n_642_, v___x_645_, v_k_643_, v_v_644_);
return v___x_646_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(lean_object* v_x_648_, size_t v_x_649_, size_t v_x_650_, lean_object* v_x_651_, lean_object* v_x_652_){
_start:
{
if (lean_obj_tag(v_x_648_) == 0)
{
lean_object* v_es_653_; size_t v___x_654_; size_t v___x_655_; lean_object* v_j_656_; lean_object* v___x_657_; uint8_t v___x_658_; 
v_es_653_ = lean_ctor_get(v_x_648_, 0);
v___x_654_ = ((size_t)31ULL);
v___x_655_ = lean_usize_land(v_x_649_, v___x_654_);
v_j_656_ = lean_usize_to_nat(v___x_655_);
v___x_657_ = lean_array_get_size(v_es_653_);
v___x_658_ = lean_nat_dec_lt(v_j_656_, v___x_657_);
if (v___x_658_ == 0)
{
lean_dec(v_j_656_);
lean_dec(v_x_652_);
lean_dec(v_x_651_);
return v_x_648_;
}
else
{
lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_697_; 
lean_inc_ref(v_es_653_);
v_isSharedCheck_697_ = !lean_is_exclusive(v_x_648_);
if (v_isSharedCheck_697_ == 0)
{
lean_object* v_unused_698_; 
v_unused_698_ = lean_ctor_get(v_x_648_, 0);
lean_dec(v_unused_698_);
v___x_660_ = v_x_648_;
v_isShared_661_ = v_isSharedCheck_697_;
goto v_resetjp_659_;
}
else
{
lean_dec(v_x_648_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_697_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v_v_662_; lean_object* v___x_663_; lean_object* v_xs_x27_664_; lean_object* v___y_666_; 
v_v_662_ = lean_array_fget(v_es_653_, v_j_656_);
v___x_663_ = lean_box(0);
v_xs_x27_664_ = lean_array_fset(v_es_653_, v_j_656_, v___x_663_);
switch(lean_obj_tag(v_v_662_))
{
case 0:
{
lean_object* v_key_671_; lean_object* v_val_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_682_; 
v_key_671_ = lean_ctor_get(v_v_662_, 0);
v_val_672_ = lean_ctor_get(v_v_662_, 1);
v_isSharedCheck_682_ = !lean_is_exclusive(v_v_662_);
if (v_isSharedCheck_682_ == 0)
{
v___x_674_ = v_v_662_;
v_isShared_675_ = v_isSharedCheck_682_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_val_672_);
lean_inc(v_key_671_);
lean_dec(v_v_662_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_682_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
uint8_t v___x_676_; 
v___x_676_ = l_Lean_instBEqFVarId_beq(v_x_651_, v_key_671_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; lean_object* v___x_678_; 
lean_del_object(v___x_674_);
v___x_677_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_671_, v_val_672_, v_x_651_, v_x_652_);
v___x_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
v___y_666_ = v___x_678_;
goto v___jp_665_;
}
else
{
lean_object* v___x_680_; 
lean_dec(v_val_672_);
lean_dec(v_key_671_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 1, v_x_652_);
lean_ctor_set(v___x_674_, 0, v_x_651_);
v___x_680_ = v___x_674_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_x_651_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_x_652_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
v___y_666_ = v___x_680_;
goto v___jp_665_;
}
}
}
}
case 1:
{
lean_object* v_node_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_695_; 
v_node_683_ = lean_ctor_get(v_v_662_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v_v_662_);
if (v_isSharedCheck_695_ == 0)
{
v___x_685_ = v_v_662_;
v_isShared_686_ = v_isSharedCheck_695_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_node_683_);
lean_dec(v_v_662_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_695_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
size_t v___x_687_; size_t v___x_688_; size_t v___x_689_; size_t v___x_690_; lean_object* v___x_691_; lean_object* v___x_693_; 
v___x_687_ = ((size_t)5ULL);
v___x_688_ = lean_usize_shift_right(v_x_649_, v___x_687_);
v___x_689_ = ((size_t)1ULL);
v___x_690_ = lean_usize_add(v_x_650_, v___x_689_);
v___x_691_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_node_683_, v___x_688_, v___x_690_, v_x_651_, v_x_652_);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 0, v___x_691_);
v___x_693_ = v___x_685_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_691_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
v___y_666_ = v___x_693_;
goto v___jp_665_;
}
}
}
default: 
{
lean_object* v___x_696_; 
v___x_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_696_, 0, v_x_651_);
lean_ctor_set(v___x_696_, 1, v_x_652_);
v___y_666_ = v___x_696_;
goto v___jp_665_;
}
}
v___jp_665_:
{
lean_object* v___x_667_; lean_object* v___x_669_; 
v___x_667_ = lean_array_fset(v_xs_x27_664_, v_j_656_, v___y_666_);
lean_dec(v_j_656_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 0, v___x_667_);
v___x_669_ = v___x_660_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_667_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
}
else
{
lean_object* v_ks_699_; lean_object* v_vs_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_720_; 
v_ks_699_ = lean_ctor_get(v_x_648_, 0);
v_vs_700_ = lean_ctor_get(v_x_648_, 1);
v_isSharedCheck_720_ = !lean_is_exclusive(v_x_648_);
if (v_isSharedCheck_720_ == 0)
{
v___x_702_ = v_x_648_;
v_isShared_703_ = v_isSharedCheck_720_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_vs_700_);
lean_inc(v_ks_699_);
lean_dec(v_x_648_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_720_;
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
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_ks_699_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v_vs_700_);
v___x_705_ = v_reuseFailAlloc_719_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
lean_object* v_newNode_706_; uint8_t v___y_708_; size_t v___x_714_; uint8_t v___x_715_; 
v_newNode_706_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1___redArg(v___x_705_, v_x_651_, v_x_652_);
v___x_714_ = ((size_t)7ULL);
v___x_715_ = lean_usize_dec_le(v___x_714_, v_x_650_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; lean_object* v___x_717_; uint8_t v___x_718_; 
v___x_716_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_706_);
v___x_717_ = lean_unsigned_to_nat(4u);
v___x_718_ = lean_nat_dec_lt(v___x_716_, v___x_717_);
lean_dec(v___x_716_);
v___y_708_ = v___x_718_;
goto v___jp_707_;
}
else
{
v___y_708_ = v___x_715_;
goto v___jp_707_;
}
v___jp_707_:
{
if (v___y_708_ == 0)
{
lean_object* v_ks_709_; lean_object* v_vs_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v_ks_709_ = lean_ctor_get(v_newNode_706_, 0);
lean_inc_ref(v_ks_709_);
v_vs_710_ = lean_ctor_get(v_newNode_706_, 1);
lean_inc_ref(v_vs_710_);
lean_dec_ref(v_newNode_706_);
v___x_711_ = lean_unsigned_to_nat(0u);
v___x_712_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0);
v___x_713_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(v_x_650_, v_ks_709_, v_vs_710_, v___x_711_, v___x_712_);
lean_dec_ref(v_vs_710_);
lean_dec_ref(v_ks_709_);
return v___x_713_;
}
else
{
return v_newNode_706_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(size_t v_depth_721_, lean_object* v_keys_722_, lean_object* v_vals_723_, lean_object* v_i_724_, lean_object* v_entries_725_){
_start:
{
lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_726_ = lean_array_get_size(v_keys_722_);
v___x_727_ = lean_nat_dec_lt(v_i_724_, v___x_726_);
if (v___x_727_ == 0)
{
lean_dec(v_i_724_);
return v_entries_725_;
}
else
{
lean_object* v_k_728_; lean_object* v_v_729_; uint64_t v___x_730_; size_t v_h_731_; size_t v___x_732_; lean_object* v___x_733_; size_t v___x_734_; size_t v___x_735_; size_t v___x_736_; size_t v_h_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v_k_728_ = lean_array_fget_borrowed(v_keys_722_, v_i_724_);
v_v_729_ = lean_array_fget_borrowed(v_vals_723_, v_i_724_);
v___x_730_ = l_Lean_instHashableFVarId_hash(v_k_728_);
v_h_731_ = lean_uint64_to_usize(v___x_730_);
v___x_732_ = ((size_t)5ULL);
v___x_733_ = lean_unsigned_to_nat(1u);
v___x_734_ = ((size_t)1ULL);
v___x_735_ = lean_usize_sub(v_depth_721_, v___x_734_);
v___x_736_ = lean_usize_mul(v___x_732_, v___x_735_);
v_h_737_ = lean_usize_shift_right(v_h_731_, v___x_736_);
v___x_738_ = lean_nat_add(v_i_724_, v___x_733_);
lean_dec(v_i_724_);
lean_inc(v_v_729_);
lean_inc(v_k_728_);
v___x_739_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_entries_725_, v_h_737_, v_depth_721_, v_k_728_, v_v_729_);
v_i_724_ = v___x_738_;
v_entries_725_ = v___x_739_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_741_, lean_object* v_keys_742_, lean_object* v_vals_743_, lean_object* v_i_744_, lean_object* v_entries_745_){
_start:
{
size_t v_depth_boxed_746_; lean_object* v_res_747_; 
v_depth_boxed_746_ = lean_unbox_usize(v_depth_741_);
lean_dec(v_depth_741_);
v_res_747_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(v_depth_boxed_746_, v_keys_742_, v_vals_743_, v_i_744_, v_entries_745_);
lean_dec_ref(v_vals_743_);
lean_dec_ref(v_keys_742_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___boxed(lean_object* v_x_748_, lean_object* v_x_749_, lean_object* v_x_750_, lean_object* v_x_751_, lean_object* v_x_752_){
_start:
{
size_t v_x_357__boxed_753_; size_t v_x_358__boxed_754_; lean_object* v_res_755_; 
v_x_357__boxed_753_ = lean_unbox_usize(v_x_749_);
lean_dec(v_x_749_);
v_x_358__boxed_754_ = lean_unbox_usize(v_x_750_);
lean_dec(v_x_750_);
v_res_755_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_x_748_, v_x_357__boxed_753_, v_x_358__boxed_754_, v_x_751_, v_x_752_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(lean_object* v_x_756_, lean_object* v_x_757_, lean_object* v_x_758_){
_start:
{
uint64_t v___x_759_; size_t v___x_760_; size_t v___x_761_; lean_object* v___x_762_; 
v___x_759_ = l_Lean_instHashableFVarId_hash(v_x_757_);
v___x_760_ = lean_uint64_to_usize(v___x_759_);
v___x_761_ = ((size_t)1ULL);
v___x_762_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_x_756_, v___x_760_, v___x_761_, v_x_757_, v_x_758_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object* v_lctx_763_, lean_object* v_fvarId_764_, lean_object* v_userName_765_, lean_object* v_type_766_, uint8_t v_bi_767_, uint8_t v_kind_768_){
_start:
{
lean_object* v_decls_769_; lean_object* v_fvarIdToDecl_770_; lean_object* v_auxDeclToFullName_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_783_; 
v_decls_769_ = lean_ctor_get(v_lctx_763_, 1);
v_fvarIdToDecl_770_ = lean_ctor_get(v_lctx_763_, 0);
v_auxDeclToFullName_771_ = lean_ctor_get(v_lctx_763_, 2);
v_isSharedCheck_783_ = !lean_is_exclusive(v_lctx_763_);
if (v_isSharedCheck_783_ == 0)
{
v___x_773_ = v_lctx_763_;
v_isShared_774_ = v_isSharedCheck_783_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_auxDeclToFullName_771_);
lean_inc(v_decls_769_);
lean_inc(v_fvarIdToDecl_770_);
lean_dec(v_lctx_763_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_783_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v_size_775_; lean_object* v_decl_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_781_; 
v_size_775_ = lean_ctor_get(v_decls_769_, 2);
lean_inc(v_fvarId_764_);
lean_inc(v_size_775_);
v_decl_776_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_decl_776_, 0, v_size_775_);
lean_ctor_set(v_decl_776_, 1, v_fvarId_764_);
lean_ctor_set(v_decl_776_, 2, v_userName_765_);
lean_ctor_set(v_decl_776_, 3, v_type_766_);
lean_ctor_set_uint8(v_decl_776_, sizeof(void*)*4, v_bi_767_);
lean_ctor_set_uint8(v_decl_776_, sizeof(void*)*4 + 1, v_kind_768_);
lean_inc_ref(v_decl_776_);
v___x_777_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_770_, v_fvarId_764_, v_decl_776_);
v___x_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_778_, 0, v_decl_776_);
v___x_779_ = l_Lean_PersistentArray_push___redArg(v_decls_769_, v___x_778_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 1, v___x_779_);
lean_ctor_set(v___x_773_, 0, v___x_777_);
v___x_781_ = v___x_773_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_777_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v___x_779_);
lean_ctor_set(v_reuseFailAlloc_782_, 2, v_auxDeclToFullName_771_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLocalDecl___boxed(lean_object* v_lctx_784_, lean_object* v_fvarId_785_, lean_object* v_userName_786_, lean_object* v_type_787_, lean_object* v_bi_788_, lean_object* v_kind_789_){
_start:
{
uint8_t v_bi_boxed_790_; uint8_t v_kind_boxed_791_; lean_object* v_res_792_; 
v_bi_boxed_790_ = lean_unbox(v_bi_788_);
v_kind_boxed_791_ = lean_unbox(v_kind_789_);
v_res_792_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_784_, v_fvarId_785_, v_userName_786_, v_type_787_, v_bi_boxed_790_, v_kind_boxed_791_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0(lean_object* v_00_u03b2_793_, lean_object* v_x_794_, lean_object* v_x_795_, lean_object* v_x_796_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_x_794_, v_x_795_, v_x_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0(lean_object* v_00_u03b2_798_, lean_object* v_x_799_, size_t v_x_800_, size_t v_x_801_, lean_object* v_x_802_, lean_object* v_x_803_){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_x_799_, v_x_800_, v_x_801_, v_x_802_, v_x_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_805_, lean_object* v_x_806_, lean_object* v_x_807_, lean_object* v_x_808_, lean_object* v_x_809_, lean_object* v_x_810_){
_start:
{
size_t v_x_561__boxed_811_; size_t v_x_562__boxed_812_; lean_object* v_res_813_; 
v_x_561__boxed_811_ = lean_unbox_usize(v_x_807_);
lean_dec(v_x_807_);
v_x_562__boxed_812_ = lean_unbox_usize(v_x_808_);
lean_dec(v_x_808_);
v_res_813_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0(v_00_u03b2_805_, v_x_806_, v_x_561__boxed_811_, v_x_562__boxed_812_, v_x_809_, v_x_810_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_814_, lean_object* v_n_815_, lean_object* v_k_816_, lean_object* v_v_817_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1___redArg(v_n_815_, v_k_816_, v_v_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_819_, size_t v_depth_820_, lean_object* v_keys_821_, lean_object* v_vals_822_, lean_object* v_heq_823_, lean_object* v_i_824_, lean_object* v_entries_825_){
_start:
{
lean_object* v___x_826_; 
v___x_826_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(v_depth_820_, v_keys_821_, v_vals_822_, v_i_824_, v_entries_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_827_, lean_object* v_depth_828_, lean_object* v_keys_829_, lean_object* v_vals_830_, lean_object* v_heq_831_, lean_object* v_i_832_, lean_object* v_entries_833_){
_start:
{
size_t v_depth_boxed_834_; lean_object* v_res_835_; 
v_depth_boxed_834_ = lean_unbox_usize(v_depth_828_);
lean_dec(v_depth_828_);
v_res_835_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2(v_00_u03b2_827_, v_depth_boxed_834_, v_keys_829_, v_vals_830_, v_heq_831_, v_i_832_, v_entries_833_);
lean_dec_ref(v_vals_830_);
lean_dec_ref(v_keys_829_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_836_, lean_object* v_x_837_, lean_object* v_x_838_, lean_object* v_x_839_, lean_object* v_x_840_){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2___redArg(v_x_837_, v_x_838_, v_x_839_, v_x_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_mk_local_decl(lean_object* v_lctx_842_, lean_object* v_fvarId_843_, lean_object* v_userName_844_, lean_object* v_type_845_, uint8_t v_bi_846_){
_start:
{
uint8_t v___x_847_; lean_object* v___x_848_; 
v___x_847_ = 0;
v___x_848_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_842_, v_fvarId_843_, v_userName_844_, v_type_845_, v_bi_846_, v___x_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_mkLocalDeclExported___boxed(lean_object* v_lctx_849_, lean_object* v_fvarId_850_, lean_object* v_userName_851_, lean_object* v_type_852_, lean_object* v_bi_853_){
_start:
{
uint8_t v_bi_boxed_854_; lean_object* v_res_855_; 
v_bi_boxed_854_ = lean_unbox(v_bi_853_);
v_res_855_ = lean_local_ctx_mk_local_decl(v_lctx_849_, v_fvarId_850_, v_userName_851_, v_type_852_, v_bi_boxed_854_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLetDecl(lean_object* v_lctx_856_, lean_object* v_fvarId_857_, lean_object* v_userName_858_, lean_object* v_type_859_, lean_object* v_value_860_, uint8_t v_nondep_861_, uint8_t v_kind_862_){
_start:
{
lean_object* v_decls_863_; lean_object* v_fvarIdToDecl_864_; lean_object* v_auxDeclToFullName_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_877_; 
v_decls_863_ = lean_ctor_get(v_lctx_856_, 1);
v_fvarIdToDecl_864_ = lean_ctor_get(v_lctx_856_, 0);
v_auxDeclToFullName_865_ = lean_ctor_get(v_lctx_856_, 2);
v_isSharedCheck_877_ = !lean_is_exclusive(v_lctx_856_);
if (v_isSharedCheck_877_ == 0)
{
v___x_867_ = v_lctx_856_;
v_isShared_868_ = v_isSharedCheck_877_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_auxDeclToFullName_865_);
lean_inc(v_decls_863_);
lean_inc(v_fvarIdToDecl_864_);
lean_dec(v_lctx_856_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_877_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v_size_869_; lean_object* v_decl_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_875_; 
v_size_869_ = lean_ctor_get(v_decls_863_, 2);
lean_inc(v_fvarId_857_);
lean_inc(v_size_869_);
v_decl_870_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_decl_870_, 0, v_size_869_);
lean_ctor_set(v_decl_870_, 1, v_fvarId_857_);
lean_ctor_set(v_decl_870_, 2, v_userName_858_);
lean_ctor_set(v_decl_870_, 3, v_type_859_);
lean_ctor_set(v_decl_870_, 4, v_value_860_);
lean_ctor_set_uint8(v_decl_870_, sizeof(void*)*5, v_nondep_861_);
lean_ctor_set_uint8(v_decl_870_, sizeof(void*)*5 + 1, v_kind_862_);
lean_inc_ref(v_decl_870_);
v___x_871_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_864_, v_fvarId_857_, v_decl_870_);
v___x_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_872_, 0, v_decl_870_);
v___x_873_ = l_Lean_PersistentArray_push___redArg(v_decls_863_, v___x_872_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 1, v___x_873_);
lean_ctor_set(v___x_867_, 0, v___x_871_);
v___x_875_ = v___x_867_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_871_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v___x_873_);
lean_ctor_set(v_reuseFailAlloc_876_, 2, v_auxDeclToFullName_865_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLetDecl___boxed(lean_object* v_lctx_878_, lean_object* v_fvarId_879_, lean_object* v_userName_880_, lean_object* v_type_881_, lean_object* v_value_882_, lean_object* v_nondep_883_, lean_object* v_kind_884_){
_start:
{
uint8_t v_nondep_boxed_885_; uint8_t v_kind_boxed_886_; lean_object* v_res_887_; 
v_nondep_boxed_885_ = lean_unbox(v_nondep_883_);
v_kind_boxed_886_ = lean_unbox(v_kind_884_);
v_res_887_ = l_Lean_LocalContext_mkLetDecl(v_lctx_878_, v_fvarId_879_, v_userName_880_, v_type_881_, v_value_882_, v_nondep_boxed_885_, v_kind_boxed_886_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_mk_let_decl(lean_object* v_lctx_888_, lean_object* v_fvarId_889_, lean_object* v_userName_890_, lean_object* v_type_891_, lean_object* v_value_892_, uint8_t v_nondep_893_){
_start:
{
uint8_t v___x_894_; lean_object* v___x_895_; 
v___x_894_ = 0;
v___x_895_ = l_Lean_LocalContext_mkLetDecl(v_lctx_888_, v_fvarId_889_, v_userName_890_, v_type_891_, v_value_892_, v_nondep_893_, v___x_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_mkLetDeclExported___boxed(lean_object* v_lctx_896_, lean_object* v_fvarId_897_, lean_object* v_userName_898_, lean_object* v_type_899_, lean_object* v_value_900_, lean_object* v_nondep_901_){
_start:
{
uint8_t v_nondep_boxed_902_; lean_object* v_res_903_; 
v_nondep_boxed_902_ = lean_unbox(v_nondep_901_);
v_res_903_ = lean_local_ctx_mk_let_decl(v_lctx_896_, v_fvarId_897_, v_userName_898_, v_type_899_, v_value_900_, v_nondep_boxed_902_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkAuxDecl(lean_object* v_lctx_904_, lean_object* v_fvarId_905_, lean_object* v_userName_906_, lean_object* v_type_907_, lean_object* v_fullName_908_){
_start:
{
lean_object* v_decls_909_; lean_object* v_fvarIdToDecl_910_; lean_object* v_auxDeclToFullName_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_926_; 
v_decls_909_ = lean_ctor_get(v_lctx_904_, 1);
v_fvarIdToDecl_910_ = lean_ctor_get(v_lctx_904_, 0);
v_auxDeclToFullName_911_ = lean_ctor_get(v_lctx_904_, 2);
v_isSharedCheck_926_ = !lean_is_exclusive(v_lctx_904_);
if (v_isSharedCheck_926_ == 0)
{
v___x_913_ = v_lctx_904_;
v_isShared_914_ = v_isSharedCheck_926_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_auxDeclToFullName_911_);
lean_inc(v_decls_909_);
lean_inc(v_fvarIdToDecl_910_);
lean_dec(v_lctx_904_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_926_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v_size_915_; uint8_t v___x_916_; uint8_t v___x_917_; lean_object* v_decl_918_; lean_object* v_auxDeclToFullName_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_924_; 
v_size_915_ = lean_ctor_get(v_decls_909_, 2);
v___x_916_ = 0;
v___x_917_ = 2;
lean_inc_n(v_fvarId_905_, 2);
lean_inc(v_size_915_);
v_decl_918_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_decl_918_, 0, v_size_915_);
lean_ctor_set(v_decl_918_, 1, v_fvarId_905_);
lean_ctor_set(v_decl_918_, 2, v_userName_906_);
lean_ctor_set(v_decl_918_, 3, v_type_907_);
lean_ctor_set_uint8(v_decl_918_, sizeof(void*)*4, v___x_916_);
lean_ctor_set_uint8(v_decl_918_, sizeof(void*)*4 + 1, v___x_917_);
v_auxDeclToFullName_919_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_905_, v_fullName_908_, v_auxDeclToFullName_911_);
lean_inc_ref(v_decl_918_);
v___x_920_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_910_, v_fvarId_905_, v_decl_918_);
v___x_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_921_, 0, v_decl_918_);
v___x_922_ = l_Lean_PersistentArray_push___redArg(v_decls_909_, v___x_921_);
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 2, v_auxDeclToFullName_919_);
lean_ctor_set(v___x_913_, 1, v___x_922_);
lean_ctor_set(v___x_913_, 0, v___x_920_);
v___x_924_ = v___x_913_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_920_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v___x_922_);
lean_ctor_set(v_reuseFailAlloc_925_, 2, v_auxDeclToFullName_919_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_addDecl(lean_object* v_lctx_927_, lean_object* v_newDecl_928_){
_start:
{
lean_object* v_decls_929_; lean_object* v_fvarIdToDecl_930_; lean_object* v_auxDeclToFullName_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_946_; 
v_decls_929_ = lean_ctor_get(v_lctx_927_, 1);
v_fvarIdToDecl_930_ = lean_ctor_get(v_lctx_927_, 0);
v_auxDeclToFullName_931_ = lean_ctor_get(v_lctx_927_, 2);
v_isSharedCheck_946_ = !lean_is_exclusive(v_lctx_927_);
if (v_isSharedCheck_946_ == 0)
{
v___x_933_ = v_lctx_927_;
v_isShared_934_ = v_isSharedCheck_946_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_auxDeclToFullName_931_);
lean_inc(v_decls_929_);
lean_inc(v_fvarIdToDecl_930_);
lean_dec(v_lctx_927_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_946_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v_size_935_; lean_object* v_newDecl_936_; lean_object* v___y_938_; lean_object* v_fvarId_945_; 
v_size_935_ = lean_ctor_get(v_decls_929_, 2);
lean_inc(v_size_935_);
v_newDecl_936_ = l_Lean_LocalDecl_setIndex(v_newDecl_928_, v_size_935_);
v_fvarId_945_ = lean_ctor_get(v_newDecl_936_, 1);
lean_inc(v_fvarId_945_);
v___y_938_ = v_fvarId_945_;
goto v___jp_937_;
v___jp_937_:
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_943_; 
lean_inc_ref(v_newDecl_936_);
v___x_939_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_930_, v___y_938_, v_newDecl_936_);
v___x_940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_940_, 0, v_newDecl_936_);
v___x_941_ = l_Lean_PersistentArray_push___redArg(v_decls_929_, v___x_940_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 1, v___x_941_);
lean_ctor_set(v___x_933_, 0, v___x_939_);
v___x_943_ = v___x_933_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_939_);
lean_ctor_set(v_reuseFailAlloc_944_, 1, v___x_941_);
lean_ctor_set(v_reuseFailAlloc_944_, 2, v_auxDeclToFullName_931_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_947_, lean_object* v_vals_948_, lean_object* v_i_949_, lean_object* v_k_950_){
_start:
{
lean_object* v___x_951_; uint8_t v___x_952_; 
v___x_951_ = lean_array_get_size(v_keys_947_);
v___x_952_ = lean_nat_dec_lt(v_i_949_, v___x_951_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; 
lean_dec(v_i_949_);
v___x_953_ = lean_box(0);
return v___x_953_;
}
else
{
lean_object* v_k_x27_954_; uint8_t v___x_955_; 
v_k_x27_954_ = lean_array_fget_borrowed(v_keys_947_, v_i_949_);
v___x_955_ = l_Lean_instBEqFVarId_beq(v_k_950_, v_k_x27_954_);
if (v___x_955_ == 0)
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = lean_unsigned_to_nat(1u);
v___x_957_ = lean_nat_add(v_i_949_, v___x_956_);
lean_dec(v_i_949_);
v_i_949_ = v___x_957_;
goto _start;
}
else
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = lean_array_fget_borrowed(v_vals_948_, v_i_949_);
lean_dec(v_i_949_);
lean_inc(v___x_959_);
v___x_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
return v___x_960_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_961_, lean_object* v_vals_962_, lean_object* v_i_963_, lean_object* v_k_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_961_, v_vals_962_, v_i_963_, v_k_964_);
lean_dec(v_k_964_);
lean_dec_ref(v_vals_962_);
lean_dec_ref(v_keys_961_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(lean_object* v_x_966_, size_t v_x_967_, lean_object* v_x_968_){
_start:
{
if (lean_obj_tag(v_x_966_) == 0)
{
lean_object* v_es_969_; lean_object* v___x_970_; size_t v___x_971_; size_t v___x_972_; lean_object* v_j_973_; lean_object* v___x_974_; 
v_es_969_ = lean_ctor_get(v_x_966_, 0);
v___x_970_ = lean_box(2);
v___x_971_ = ((size_t)31ULL);
v___x_972_ = lean_usize_land(v_x_967_, v___x_971_);
v_j_973_ = lean_usize_to_nat(v___x_972_);
v___x_974_ = lean_array_get_borrowed(v___x_970_, v_es_969_, v_j_973_);
lean_dec(v_j_973_);
switch(lean_obj_tag(v___x_974_))
{
case 0:
{
lean_object* v_key_975_; lean_object* v_val_976_; uint8_t v___x_977_; 
v_key_975_ = lean_ctor_get(v___x_974_, 0);
v_val_976_ = lean_ctor_get(v___x_974_, 1);
v___x_977_ = l_Lean_instBEqFVarId_beq(v_x_968_, v_key_975_);
if (v___x_977_ == 0)
{
lean_object* v___x_978_; 
v___x_978_ = lean_box(0);
return v___x_978_;
}
else
{
lean_object* v___x_979_; 
lean_inc(v_val_976_);
v___x_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_979_, 0, v_val_976_);
return v___x_979_;
}
}
case 1:
{
lean_object* v_node_980_; size_t v___x_981_; size_t v___x_982_; 
v_node_980_ = lean_ctor_get(v___x_974_, 0);
v___x_981_ = ((size_t)5ULL);
v___x_982_ = lean_usize_shift_right(v_x_967_, v___x_981_);
v_x_966_ = v_node_980_;
v_x_967_ = v___x_982_;
goto _start;
}
default: 
{
lean_object* v___x_984_; 
v___x_984_ = lean_box(0);
return v___x_984_;
}
}
}
else
{
lean_object* v_ks_985_; lean_object* v_vs_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v_ks_985_ = lean_ctor_get(v_x_966_, 0);
v_vs_986_ = lean_ctor_get(v_x_966_, 1);
v___x_987_ = lean_unsigned_to_nat(0u);
v___x_988_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(v_ks_985_, v_vs_986_, v___x_987_, v_x_968_);
return v___x_988_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_989_, lean_object* v_x_990_, lean_object* v_x_991_){
_start:
{
size_t v_x_133__boxed_992_; lean_object* v_res_993_; 
v_x_133__boxed_992_ = lean_unbox_usize(v_x_990_);
lean_dec(v_x_990_);
v_res_993_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(v_x_989_, v_x_133__boxed_992_, v_x_991_);
lean_dec(v_x_991_);
lean_dec_ref(v_x_989_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(lean_object* v_x_994_, lean_object* v_x_995_){
_start:
{
uint64_t v___x_996_; size_t v___x_997_; lean_object* v___x_998_; 
v___x_996_ = l_Lean_instHashableFVarId_hash(v_x_995_);
v___x_997_ = lean_uint64_to_usize(v___x_996_);
v___x_998_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(v_x_994_, v___x_997_, v_x_995_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg___boxed(lean_object* v_x_999_, lean_object* v_x_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_x_999_, v_x_1000_);
lean_dec(v_x_1000_);
lean_dec_ref(v_x_999_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_find(lean_object* v_lctx_1002_, lean_object* v_fvarId_1003_){
_start:
{
lean_object* v_fvarIdToDecl_1004_; lean_object* v___x_1005_; 
v_fvarIdToDecl_1004_ = lean_ctor_get(v_lctx_1002_, 0);
lean_inc_ref(v_fvarIdToDecl_1004_);
lean_dec_ref(v_lctx_1002_);
v___x_1005_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_fvarIdToDecl_1004_, v_fvarId_1003_);
lean_dec(v_fvarId_1003_);
lean_dec_ref(v_fvarIdToDecl_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0(lean_object* v_00_u03b2_1006_, lean_object* v_x_1007_, lean_object* v_x_1008_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_x_1007_, v_x_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___boxed(lean_object* v_00_u03b2_1010_, lean_object* v_x_1011_, lean_object* v_x_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0(v_00_u03b2_1010_, v_x_1011_, v_x_1012_);
lean_dec(v_x_1012_);
lean_dec_ref(v_x_1011_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1014_, lean_object* v_x_1015_, size_t v_x_1016_, lean_object* v_x_1017_){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(v_x_1015_, v_x_1016_, v_x_1017_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1019_, lean_object* v_x_1020_, lean_object* v_x_1021_, lean_object* v_x_1022_){
_start:
{
size_t v_x_202__boxed_1023_; lean_object* v_res_1024_; 
v_x_202__boxed_1023_ = lean_unbox_usize(v_x_1021_);
lean_dec(v_x_1021_);
v_res_1024_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0(v_00_u03b2_1019_, v_x_1020_, v_x_202__boxed_1023_, v_x_1022_);
lean_dec(v_x_1022_);
lean_dec_ref(v_x_1020_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1025_, lean_object* v_keys_1026_, lean_object* v_vals_1027_, lean_object* v_heq_1028_, lean_object* v_i_1029_, lean_object* v_k_1030_){
_start:
{
lean_object* v___x_1031_; 
v___x_1031_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1026_, v_vals_1027_, v_i_1029_, v_k_1030_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1032_, lean_object* v_keys_1033_, lean_object* v_vals_1034_, lean_object* v_heq_1035_, lean_object* v_i_1036_, lean_object* v_k_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1032_, v_keys_1033_, v_vals_1034_, v_heq_1035_, v_i_1036_, v_k_1037_);
lean_dec(v_k_1037_);
lean_dec_ref(v_vals_1034_);
lean_dec_ref(v_keys_1033_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFVar_x3f(lean_object* v_lctx_1039_, lean_object* v_e_1040_){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = l_Lean_Expr_fvarId_x21(v_e_1040_);
v___x_1042_ = lean_local_ctx_find(v_lctx_1039_, v___x_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFVar_x3f___boxed(lean_object* v_lctx_1043_, lean_object* v_e_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_1043_, v_e_1044_);
lean_dec_ref(v_e_1044_);
return v_res_1045_;
}
}
static lean_object* _init_l_Lean_LocalContext_get_x21___closed__2(void){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1048_ = ((lean_object*)(l_Lean_LocalContext_get_x21___closed__1));
v___x_1049_ = lean_unsigned_to_nat(14u);
v___x_1050_ = lean_unsigned_to_nat(340u);
v___x_1051_ = ((lean_object*)(l_Lean_LocalContext_get_x21___closed__0));
v___x_1052_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_1053_ = l_mkPanicMessageWithDecl(v___x_1052_, v___x_1051_, v___x_1050_, v___x_1049_, v___x_1048_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_get_x21(lean_object* v_lctx_1054_, lean_object* v_fvarId_1055_){
_start:
{
lean_object* v___x_1056_; 
v___x_1056_ = lean_local_ctx_find(v_lctx_1054_, v_fvarId_1055_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = lean_obj_once(&l_Lean_LocalContext_get_x21___closed__2, &l_Lean_LocalContext_get_x21___closed__2_once, _init_l_Lean_LocalContext_get_x21___closed__2);
v___x_1058_ = l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(v___x_1057_);
return v___x_1058_;
}
else
{
lean_object* v_val_1059_; 
v_val_1059_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_val_1059_);
lean_dec_ref_known(v___x_1056_, 1);
return v_val_1059_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVar_x21(lean_object* v_lctx_1060_, lean_object* v_e_1061_){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = l_Lean_Expr_fvarId_x21(v_e_1061_);
v___x_1063_ = l_Lean_LocalContext_get_x21(v_lctx_1060_, v___x_1062_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVar_x21___boxed(lean_object* v_lctx_1064_, lean_object* v_e_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_Lean_LocalContext_getFVar_x21(v_lctx_1064_, v_e_1065_);
lean_dec_ref(v_e_1065_);
return v_res_1066_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1067_, lean_object* v_i_1068_, lean_object* v_k_1069_){
_start:
{
lean_object* v___x_1070_; uint8_t v___x_1071_; 
v___x_1070_ = lean_array_get_size(v_keys_1067_);
v___x_1071_ = lean_nat_dec_lt(v_i_1068_, v___x_1070_);
if (v___x_1071_ == 0)
{
lean_dec(v_i_1068_);
return v___x_1071_;
}
else
{
lean_object* v_k_x27_1072_; uint8_t v___x_1073_; 
v_k_x27_1072_ = lean_array_fget_borrowed(v_keys_1067_, v_i_1068_);
v___x_1073_ = l_Lean_instBEqFVarId_beq(v_k_1069_, v_k_x27_1072_);
if (v___x_1073_ == 0)
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = lean_unsigned_to_nat(1u);
v___x_1075_ = lean_nat_add(v_i_1068_, v___x_1074_);
lean_dec(v_i_1068_);
v_i_1068_ = v___x_1075_;
goto _start;
}
else
{
lean_dec(v_i_1068_);
return v___x_1073_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1077_, lean_object* v_i_1078_, lean_object* v_k_1079_){
_start:
{
uint8_t v_res_1080_; lean_object* v_r_1081_; 
v_res_1080_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(v_keys_1077_, v_i_1078_, v_k_1079_);
lean_dec(v_k_1079_);
lean_dec_ref(v_keys_1077_);
v_r_1081_ = lean_box(v_res_1080_);
return v_r_1081_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(lean_object* v_x_1082_, size_t v_x_1083_, lean_object* v_x_1084_){
_start:
{
if (lean_obj_tag(v_x_1082_) == 0)
{
lean_object* v_es_1085_; lean_object* v___x_1086_; size_t v___x_1087_; size_t v___x_1088_; lean_object* v_j_1089_; lean_object* v___x_1090_; 
v_es_1085_ = lean_ctor_get(v_x_1082_, 0);
v___x_1086_ = lean_box(2);
v___x_1087_ = ((size_t)31ULL);
v___x_1088_ = lean_usize_land(v_x_1083_, v___x_1087_);
v_j_1089_ = lean_usize_to_nat(v___x_1088_);
v___x_1090_ = lean_array_get_borrowed(v___x_1086_, v_es_1085_, v_j_1089_);
lean_dec(v_j_1089_);
switch(lean_obj_tag(v___x_1090_))
{
case 0:
{
lean_object* v_key_1091_; uint8_t v___x_1092_; 
v_key_1091_ = lean_ctor_get(v___x_1090_, 0);
v___x_1092_ = l_Lean_instBEqFVarId_beq(v_x_1084_, v_key_1091_);
return v___x_1092_;
}
case 1:
{
lean_object* v_node_1093_; size_t v___x_1094_; size_t v___x_1095_; 
v_node_1093_ = lean_ctor_get(v___x_1090_, 0);
v___x_1094_ = ((size_t)5ULL);
v___x_1095_ = lean_usize_shift_right(v_x_1083_, v___x_1094_);
v_x_1082_ = v_node_1093_;
v_x_1083_ = v___x_1095_;
goto _start;
}
default: 
{
uint8_t v___x_1097_; 
v___x_1097_ = 0;
return v___x_1097_;
}
}
}
else
{
lean_object* v_ks_1098_; lean_object* v___x_1099_; uint8_t v___x_1100_; 
v_ks_1098_ = lean_ctor_get(v_x_1082_, 0);
v___x_1099_ = lean_unsigned_to_nat(0u);
v___x_1100_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(v_ks_1098_, v___x_1099_, v_x_1084_);
return v___x_1100_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg___boxed(lean_object* v_x_1101_, lean_object* v_x_1102_, lean_object* v_x_1103_){
_start:
{
size_t v_x_119__boxed_1104_; uint8_t v_res_1105_; lean_object* v_r_1106_; 
v_x_119__boxed_1104_ = lean_unbox_usize(v_x_1102_);
lean_dec(v_x_1102_);
v_res_1105_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(v_x_1101_, v_x_119__boxed_1104_, v_x_1103_);
lean_dec(v_x_1103_);
lean_dec_ref(v_x_1101_);
v_r_1106_ = lean_box(v_res_1105_);
return v_r_1106_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(lean_object* v_x_1107_, lean_object* v_x_1108_){
_start:
{
uint64_t v___x_1109_; size_t v___x_1110_; uint8_t v___x_1111_; 
v___x_1109_ = l_Lean_instHashableFVarId_hash(v_x_1108_);
v___x_1110_ = lean_uint64_to_usize(v___x_1109_);
v___x_1111_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(v_x_1107_, v___x_1110_, v_x_1108_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg___boxed(lean_object* v_x_1112_, lean_object* v_x_1113_){
_start:
{
uint8_t v_res_1114_; lean_object* v_r_1115_; 
v_res_1114_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(v_x_1112_, v_x_1113_);
lean_dec(v_x_1113_);
lean_dec_ref(v_x_1112_);
v_r_1115_ = lean_box(v_res_1114_);
return v_r_1115_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_contains(lean_object* v_lctx_1116_, lean_object* v_fvarId_1117_){
_start:
{
lean_object* v_fvarIdToDecl_1118_; uint8_t v___x_1119_; 
v_fvarIdToDecl_1118_ = lean_ctor_get(v_lctx_1116_, 0);
v___x_1119_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(v_fvarIdToDecl_1118_, v_fvarId_1117_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_contains___boxed(lean_object* v_lctx_1120_, lean_object* v_fvarId_1121_){
_start:
{
uint8_t v_res_1122_; lean_object* v_r_1123_; 
v_res_1122_ = l_Lean_LocalContext_contains(v_lctx_1120_, v_fvarId_1121_);
lean_dec(v_fvarId_1121_);
lean_dec_ref(v_lctx_1120_);
v_r_1123_ = lean_box(v_res_1122_);
return v_r_1123_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0(lean_object* v_00_u03b2_1124_, lean_object* v_x_1125_, lean_object* v_x_1126_){
_start:
{
uint8_t v___x_1127_; 
v___x_1127_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(v_x_1125_, v_x_1126_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___boxed(lean_object* v_00_u03b2_1128_, lean_object* v_x_1129_, lean_object* v_x_1130_){
_start:
{
uint8_t v_res_1131_; lean_object* v_r_1132_; 
v_res_1131_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0(v_00_u03b2_1128_, v_x_1129_, v_x_1130_);
lean_dec(v_x_1130_);
lean_dec_ref(v_x_1129_);
v_r_1132_ = lean_box(v_res_1131_);
return v_r_1132_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0(lean_object* v_00_u03b2_1133_, lean_object* v_x_1134_, size_t v_x_1135_, lean_object* v_x_1136_){
_start:
{
uint8_t v___x_1137_; 
v___x_1137_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(v_x_1134_, v_x_1135_, v_x_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1138_, lean_object* v_x_1139_, lean_object* v_x_1140_, lean_object* v_x_1141_){
_start:
{
size_t v_x_182__boxed_1142_; uint8_t v_res_1143_; lean_object* v_r_1144_; 
v_x_182__boxed_1142_ = lean_unbox_usize(v_x_1140_);
lean_dec(v_x_1140_);
v_res_1143_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0(v_00_u03b2_1138_, v_x_1139_, v_x_182__boxed_1142_, v_x_1141_);
lean_dec(v_x_1141_);
lean_dec_ref(v_x_1139_);
v_r_1144_ = lean_box(v_res_1143_);
return v_r_1144_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1145_, lean_object* v_keys_1146_, lean_object* v_vals_1147_, lean_object* v_heq_1148_, lean_object* v_i_1149_, lean_object* v_k_1150_){
_start:
{
uint8_t v___x_1151_; 
v___x_1151_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(v_keys_1146_, v_i_1149_, v_k_1150_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1152_, lean_object* v_keys_1153_, lean_object* v_vals_1154_, lean_object* v_heq_1155_, lean_object* v_i_1156_, lean_object* v_k_1157_){
_start:
{
uint8_t v_res_1158_; lean_object* v_r_1159_; 
v_res_1158_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1(v_00_u03b2_1152_, v_keys_1153_, v_vals_1154_, v_heq_1155_, v_i_1156_, v_k_1157_);
lean_dec(v_k_1157_);
lean_dec_ref(v_vals_1154_);
lean_dec_ref(v_keys_1153_);
v_r_1159_ = lean_box(v_res_1158_);
return v_r_1159_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_containsFVar(lean_object* v_lctx_1160_, lean_object* v_e_1161_){
_start:
{
lean_object* v___x_1162_; uint8_t v___x_1163_; 
v___x_1162_ = l_Lean_Expr_fvarId_x21(v_e_1161_);
v___x_1163_ = l_Lean_LocalContext_contains(v_lctx_1160_, v___x_1162_);
lean_dec(v___x_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_containsFVar___boxed(lean_object* v_lctx_1164_, lean_object* v_e_1165_){
_start:
{
uint8_t v_res_1166_; lean_object* v_r_1167_; 
v_res_1166_ = l_Lean_LocalContext_containsFVar(v_lctx_1164_, v_e_1165_);
lean_dec_ref(v_e_1165_);
lean_dec_ref(v_lctx_1164_);
v_r_1167_ = lean_box(v_res_1166_);
return v_r_1167_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(lean_object* v_as_1168_, size_t v_i_1169_, size_t v_stop_1170_, lean_object* v_b_1171_){
_start:
{
lean_object* v___y_1173_; uint8_t v___x_1177_; 
v___x_1177_ = lean_usize_dec_eq(v_i_1169_, v_stop_1170_);
if (v___x_1177_ == 0)
{
lean_object* v___x_1178_; 
v___x_1178_ = lean_array_uget_borrowed(v_as_1168_, v_i_1169_);
if (lean_obj_tag(v___x_1178_) == 0)
{
v___y_1173_ = v_b_1171_;
goto v___jp_1172_;
}
else
{
lean_object* v_val_1179_; lean_object* v_fvarId_1180_; lean_object* v___x_1181_; 
v_val_1179_ = lean_ctor_get(v___x_1178_, 0);
v_fvarId_1180_ = lean_ctor_get(v_val_1179_, 1);
lean_inc(v_fvarId_1180_);
v___x_1181_ = lean_array_push(v_b_1171_, v_fvarId_1180_);
v___y_1173_ = v___x_1181_;
goto v___jp_1172_;
}
}
else
{
return v_b_1171_;
}
v___jp_1172_:
{
size_t v___x_1174_; size_t v___x_1175_; 
v___x_1174_ = ((size_t)1ULL);
v___x_1175_ = lean_usize_add(v_i_1169_, v___x_1174_);
v_i_1169_ = v___x_1175_;
v_b_1171_ = v___y_1173_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1___boxed(lean_object* v_as_1182_, lean_object* v_i_1183_, lean_object* v_stop_1184_, lean_object* v_b_1185_){
_start:
{
size_t v_i_boxed_1186_; size_t v_stop_boxed_1187_; lean_object* v_res_1188_; 
v_i_boxed_1186_ = lean_unbox_usize(v_i_1183_);
lean_dec(v_i_1183_);
v_stop_boxed_1187_ = lean_unbox_usize(v_stop_1184_);
lean_dec(v_stop_1184_);
v_res_1188_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_as_1182_, v_i_boxed_1186_, v_stop_boxed_1187_, v_b_1185_);
lean_dec_ref(v_as_1182_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(lean_object* v_x_1189_, lean_object* v_x_1190_){
_start:
{
if (lean_obj_tag(v_x_1189_) == 0)
{
lean_object* v_cs_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; uint8_t v___x_1194_; 
v_cs_1191_ = lean_ctor_get(v_x_1189_, 0);
v___x_1192_ = lean_unsigned_to_nat(0u);
v___x_1193_ = lean_array_get_size(v_cs_1191_);
v___x_1194_ = lean_nat_dec_lt(v___x_1192_, v___x_1193_);
if (v___x_1194_ == 0)
{
return v_x_1190_;
}
else
{
uint8_t v___x_1195_; 
v___x_1195_ = lean_nat_dec_le(v___x_1193_, v___x_1193_);
if (v___x_1195_ == 0)
{
if (v___x_1194_ == 0)
{
return v_x_1190_;
}
else
{
size_t v___x_1196_; size_t v___x_1197_; lean_object* v___x_1198_; 
v___x_1196_ = ((size_t)0ULL);
v___x_1197_ = lean_usize_of_nat(v___x_1193_);
v___x_1198_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_cs_1191_, v___x_1196_, v___x_1197_, v_x_1190_);
return v___x_1198_;
}
}
else
{
size_t v___x_1199_; size_t v___x_1200_; lean_object* v___x_1201_; 
v___x_1199_ = ((size_t)0ULL);
v___x_1200_ = lean_usize_of_nat(v___x_1193_);
v___x_1201_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_cs_1191_, v___x_1199_, v___x_1200_, v_x_1190_);
return v___x_1201_;
}
}
}
else
{
lean_object* v_vs_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; uint8_t v___x_1205_; 
v_vs_1202_ = lean_ctor_get(v_x_1189_, 0);
v___x_1203_ = lean_unsigned_to_nat(0u);
v___x_1204_ = lean_array_get_size(v_vs_1202_);
v___x_1205_ = lean_nat_dec_lt(v___x_1203_, v___x_1204_);
if (v___x_1205_ == 0)
{
return v_x_1190_;
}
else
{
uint8_t v___x_1206_; 
v___x_1206_ = lean_nat_dec_le(v___x_1204_, v___x_1204_);
if (v___x_1206_ == 0)
{
if (v___x_1205_ == 0)
{
return v_x_1190_;
}
else
{
size_t v___x_1207_; size_t v___x_1208_; lean_object* v___x_1209_; 
v___x_1207_ = ((size_t)0ULL);
v___x_1208_ = lean_usize_of_nat(v___x_1204_);
v___x_1209_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_vs_1202_, v___x_1207_, v___x_1208_, v_x_1190_);
return v___x_1209_;
}
}
else
{
size_t v___x_1210_; size_t v___x_1211_; lean_object* v___x_1212_; 
v___x_1210_ = ((size_t)0ULL);
v___x_1211_ = lean_usize_of_nat(v___x_1204_);
v___x_1212_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_vs_1202_, v___x_1210_, v___x_1211_, v_x_1190_);
return v___x_1212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(lean_object* v_as_1213_, size_t v_i_1214_, size_t v_stop_1215_, lean_object* v_b_1216_){
_start:
{
uint8_t v___x_1217_; 
v___x_1217_ = lean_usize_dec_eq(v_i_1214_, v_stop_1215_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1218_; lean_object* v___x_1219_; size_t v___x_1220_; size_t v___x_1221_; 
v___x_1218_ = lean_array_uget_borrowed(v_as_1213_, v_i_1214_);
v___x_1219_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(v___x_1218_, v_b_1216_);
v___x_1220_ = ((size_t)1ULL);
v___x_1221_ = lean_usize_add(v_i_1214_, v___x_1220_);
v_i_1214_ = v___x_1221_;
v_b_1216_ = v___x_1219_;
goto _start;
}
else
{
return v_b_1216_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1___boxed(lean_object* v_as_1223_, lean_object* v_i_1224_, lean_object* v_stop_1225_, lean_object* v_b_1226_){
_start:
{
size_t v_i_boxed_1227_; size_t v_stop_boxed_1228_; lean_object* v_res_1229_; 
v_i_boxed_1227_ = lean_unbox_usize(v_i_1224_);
lean_dec(v_i_1224_);
v_stop_boxed_1228_ = lean_unbox_usize(v_stop_1225_);
lean_dec(v_stop_1225_);
v_res_1229_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_as_1223_, v_i_boxed_1227_, v_stop_boxed_1228_, v_b_1226_);
lean_dec_ref(v_as_1223_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2___boxed(lean_object* v_x_1230_, lean_object* v_x_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(v_x_1230_, v_x_1231_);
lean_dec_ref(v_x_1230_);
return v_res_1232_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1233_; 
v___x_1233_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(lean_object* v_x_1234_, size_t v_x_1235_, size_t v_x_1236_, lean_object* v_x_1237_){
_start:
{
if (lean_obj_tag(v_x_1234_) == 0)
{
lean_object* v_cs_1238_; lean_object* v___x_1239_; size_t v___x_1240_; lean_object* v_j_1241_; lean_object* v___x_1242_; size_t v___x_1243_; size_t v___x_1244_; size_t v___x_1245_; size_t v___x_1246_; size_t v___x_1247_; size_t v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; uint8_t v___x_1253_; 
v_cs_1238_ = lean_ctor_get(v_x_1234_, 0);
v___x_1239_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0);
v___x_1240_ = lean_usize_shift_right(v_x_1235_, v_x_1236_);
v_j_1241_ = lean_usize_to_nat(v___x_1240_);
v___x_1242_ = lean_array_get_borrowed(v___x_1239_, v_cs_1238_, v_j_1241_);
v___x_1243_ = ((size_t)1ULL);
v___x_1244_ = lean_usize_shift_left(v___x_1243_, v_x_1236_);
v___x_1245_ = lean_usize_sub(v___x_1244_, v___x_1243_);
v___x_1246_ = lean_usize_land(v_x_1235_, v___x_1245_);
v___x_1247_ = ((size_t)5ULL);
v___x_1248_ = lean_usize_sub(v_x_1236_, v___x_1247_);
v___x_1249_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(v___x_1242_, v___x_1246_, v___x_1248_, v_x_1237_);
v___x_1250_ = lean_unsigned_to_nat(1u);
v___x_1251_ = lean_nat_add(v_j_1241_, v___x_1250_);
lean_dec(v_j_1241_);
v___x_1252_ = lean_array_get_size(v_cs_1238_);
v___x_1253_ = lean_nat_dec_lt(v___x_1251_, v___x_1252_);
if (v___x_1253_ == 0)
{
lean_dec(v___x_1251_);
return v___x_1249_;
}
else
{
uint8_t v___x_1254_; 
v___x_1254_ = lean_nat_dec_le(v___x_1252_, v___x_1252_);
if (v___x_1254_ == 0)
{
if (v___x_1253_ == 0)
{
lean_dec(v___x_1251_);
return v___x_1249_;
}
else
{
size_t v___x_1255_; size_t v___x_1256_; lean_object* v___x_1257_; 
v___x_1255_ = lean_usize_of_nat(v___x_1251_);
lean_dec(v___x_1251_);
v___x_1256_ = lean_usize_of_nat(v___x_1252_);
v___x_1257_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_cs_1238_, v___x_1255_, v___x_1256_, v___x_1249_);
return v___x_1257_;
}
}
else
{
size_t v___x_1258_; size_t v___x_1259_; lean_object* v___x_1260_; 
v___x_1258_ = lean_usize_of_nat(v___x_1251_);
lean_dec(v___x_1251_);
v___x_1259_ = lean_usize_of_nat(v___x_1252_);
v___x_1260_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_cs_1238_, v___x_1258_, v___x_1259_, v___x_1249_);
return v___x_1260_;
}
}
}
else
{
lean_object* v_vs_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; uint8_t v___x_1264_; 
v_vs_1261_ = lean_ctor_get(v_x_1234_, 0);
v___x_1262_ = lean_usize_to_nat(v_x_1235_);
v___x_1263_ = lean_array_get_size(v_vs_1261_);
v___x_1264_ = lean_nat_dec_lt(v___x_1262_, v___x_1263_);
if (v___x_1264_ == 0)
{
lean_dec(v___x_1262_);
return v_x_1237_;
}
else
{
uint8_t v___x_1265_; 
v___x_1265_ = lean_nat_dec_le(v___x_1263_, v___x_1263_);
if (v___x_1265_ == 0)
{
if (v___x_1264_ == 0)
{
lean_dec(v___x_1262_);
return v_x_1237_;
}
else
{
size_t v___x_1266_; size_t v___x_1267_; lean_object* v___x_1268_; 
v___x_1266_ = lean_usize_of_nat(v___x_1262_);
lean_dec(v___x_1262_);
v___x_1267_ = lean_usize_of_nat(v___x_1263_);
v___x_1268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_vs_1261_, v___x_1266_, v___x_1267_, v_x_1237_);
return v___x_1268_;
}
}
else
{
size_t v___x_1269_; size_t v___x_1270_; lean_object* v___x_1271_; 
v___x_1269_ = lean_usize_of_nat(v___x_1262_);
lean_dec(v___x_1262_);
v___x_1270_ = lean_usize_of_nat(v___x_1263_);
v___x_1271_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_vs_1261_, v___x_1269_, v___x_1270_, v_x_1237_);
return v___x_1271_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___boxed(lean_object* v_x_1272_, lean_object* v_x_1273_, lean_object* v_x_1274_, lean_object* v_x_1275_){
_start:
{
size_t v_x_1632__boxed_1276_; size_t v_x_1633__boxed_1277_; lean_object* v_res_1278_; 
v_x_1632__boxed_1276_ = lean_unbox_usize(v_x_1273_);
lean_dec(v_x_1273_);
v_x_1633__boxed_1277_ = lean_unbox_usize(v_x_1274_);
lean_dec(v_x_1274_);
v_res_1278_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(v_x_1272_, v_x_1632__boxed_1276_, v_x_1633__boxed_1277_, v_x_1275_);
lean_dec_ref(v_x_1272_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0(lean_object* v_t_1279_, lean_object* v_init_1280_, lean_object* v_start_1281_){
_start:
{
lean_object* v___x_1282_; uint8_t v___x_1283_; 
v___x_1282_ = lean_unsigned_to_nat(0u);
v___x_1283_ = lean_nat_dec_eq(v_start_1281_, v___x_1282_);
if (v___x_1283_ == 0)
{
lean_object* v_root_1284_; lean_object* v_tail_1285_; size_t v_shift_1286_; lean_object* v_tailOff_1287_; uint8_t v___x_1288_; 
v_root_1284_ = lean_ctor_get(v_t_1279_, 0);
v_tail_1285_ = lean_ctor_get(v_t_1279_, 1);
v_shift_1286_ = lean_ctor_get_usize(v_t_1279_, 4);
v_tailOff_1287_ = lean_ctor_get(v_t_1279_, 3);
v___x_1288_ = lean_nat_dec_le(v_tailOff_1287_, v_start_1281_);
if (v___x_1288_ == 0)
{
size_t v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; uint8_t v___x_1292_; 
v___x_1289_ = lean_usize_of_nat(v_start_1281_);
v___x_1290_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(v_root_1284_, v___x_1289_, v_shift_1286_, v_init_1280_);
v___x_1291_ = lean_array_get_size(v_tail_1285_);
v___x_1292_ = lean_nat_dec_lt(v___x_1282_, v___x_1291_);
if (v___x_1292_ == 0)
{
return v___x_1290_;
}
else
{
uint8_t v___x_1293_; 
v___x_1293_ = lean_nat_dec_le(v___x_1291_, v___x_1291_);
if (v___x_1293_ == 0)
{
if (v___x_1292_ == 0)
{
return v___x_1290_;
}
else
{
size_t v___x_1294_; size_t v___x_1295_; lean_object* v___x_1296_; 
v___x_1294_ = ((size_t)0ULL);
v___x_1295_ = lean_usize_of_nat(v___x_1291_);
v___x_1296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1285_, v___x_1294_, v___x_1295_, v___x_1290_);
return v___x_1296_;
}
}
else
{
size_t v___x_1297_; size_t v___x_1298_; lean_object* v___x_1299_; 
v___x_1297_ = ((size_t)0ULL);
v___x_1298_ = lean_usize_of_nat(v___x_1291_);
v___x_1299_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1285_, v___x_1297_, v___x_1298_, v___x_1290_);
return v___x_1299_;
}
}
}
else
{
lean_object* v___x_1300_; lean_object* v___x_1301_; uint8_t v___x_1302_; 
v___x_1300_ = lean_nat_sub(v_start_1281_, v_tailOff_1287_);
v___x_1301_ = lean_array_get_size(v_tail_1285_);
v___x_1302_ = lean_nat_dec_lt(v___x_1300_, v___x_1301_);
if (v___x_1302_ == 0)
{
lean_dec(v___x_1300_);
return v_init_1280_;
}
else
{
uint8_t v___x_1303_; 
v___x_1303_ = lean_nat_dec_le(v___x_1301_, v___x_1301_);
if (v___x_1303_ == 0)
{
if (v___x_1302_ == 0)
{
lean_dec(v___x_1300_);
return v_init_1280_;
}
else
{
size_t v___x_1304_; size_t v___x_1305_; lean_object* v___x_1306_; 
v___x_1304_ = lean_usize_of_nat(v___x_1300_);
lean_dec(v___x_1300_);
v___x_1305_ = lean_usize_of_nat(v___x_1301_);
v___x_1306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1285_, v___x_1304_, v___x_1305_, v_init_1280_);
return v___x_1306_;
}
}
else
{
size_t v___x_1307_; size_t v___x_1308_; lean_object* v___x_1309_; 
v___x_1307_ = lean_usize_of_nat(v___x_1300_);
lean_dec(v___x_1300_);
v___x_1308_ = lean_usize_of_nat(v___x_1301_);
v___x_1309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1285_, v___x_1307_, v___x_1308_, v_init_1280_);
return v___x_1309_;
}
}
}
}
else
{
lean_object* v_root_1310_; lean_object* v_tail_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; 
v_root_1310_ = lean_ctor_get(v_t_1279_, 0);
v_tail_1311_ = lean_ctor_get(v_t_1279_, 1);
v___x_1312_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(v_root_1310_, v_init_1280_);
v___x_1313_ = lean_array_get_size(v_tail_1311_);
v___x_1314_ = lean_nat_dec_lt(v___x_1282_, v___x_1313_);
if (v___x_1314_ == 0)
{
return v___x_1312_;
}
else
{
uint8_t v___x_1315_; 
v___x_1315_ = lean_nat_dec_le(v___x_1313_, v___x_1313_);
if (v___x_1315_ == 0)
{
if (v___x_1314_ == 0)
{
return v___x_1312_;
}
else
{
size_t v___x_1316_; size_t v___x_1317_; lean_object* v___x_1318_; 
v___x_1316_ = ((size_t)0ULL);
v___x_1317_ = lean_usize_of_nat(v___x_1313_);
v___x_1318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1311_, v___x_1316_, v___x_1317_, v___x_1312_);
return v___x_1318_;
}
}
else
{
size_t v___x_1319_; size_t v___x_1320_; lean_object* v___x_1321_; 
v___x_1319_ = ((size_t)0ULL);
v___x_1320_ = lean_usize_of_nat(v___x_1313_);
v___x_1321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1311_, v___x_1319_, v___x_1320_, v___x_1312_);
return v___x_1321_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0___boxed(lean_object* v_t_1322_, lean_object* v_init_1323_, lean_object* v_start_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0(v_t_1322_, v_init_1323_, v_start_1324_);
lean_dec(v_start_1324_);
lean_dec_ref(v_t_1322_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVarIds(lean_object* v_lctx_1328_){
_start:
{
lean_object* v_decls_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v_decls_1329_ = lean_ctor_get(v_lctx_1328_, 1);
v___x_1330_ = lean_unsigned_to_nat(0u);
v___x_1331_ = ((lean_object*)(l_Lean_LocalContext_getFVarIds___closed__0));
v___x_1332_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0(v_decls_1329_, v___x_1331_, v___x_1330_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVarIds___boxed(lean_object* v_lctx_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Lean_LocalContext_getFVarIds(v_lctx_1333_);
lean_dec_ref(v_lctx_1333_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0(size_t v_sz_1335_, size_t v_i_1336_, lean_object* v_bs_1337_){
_start:
{
uint8_t v___x_1338_; 
v___x_1338_ = lean_usize_dec_lt(v_i_1336_, v_sz_1335_);
if (v___x_1338_ == 0)
{
return v_bs_1337_;
}
else
{
lean_object* v_v_1339_; lean_object* v___x_1340_; lean_object* v_bs_x27_1341_; lean_object* v___x_1342_; size_t v___x_1343_; size_t v___x_1344_; lean_object* v___x_1345_; 
v_v_1339_ = lean_array_uget(v_bs_1337_, v_i_1336_);
v___x_1340_ = lean_unsigned_to_nat(0u);
v_bs_x27_1341_ = lean_array_uset(v_bs_1337_, v_i_1336_, v___x_1340_);
v___x_1342_ = l_Lean_mkFVar(v_v_1339_);
v___x_1343_ = ((size_t)1ULL);
v___x_1344_ = lean_usize_add(v_i_1336_, v___x_1343_);
v___x_1345_ = lean_array_uset(v_bs_x27_1341_, v_i_1336_, v___x_1342_);
v_i_1336_ = v___x_1344_;
v_bs_1337_ = v___x_1345_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0___boxed(lean_object* v_sz_1347_, lean_object* v_i_1348_, lean_object* v_bs_1349_){
_start:
{
size_t v_sz_boxed_1350_; size_t v_i_boxed_1351_; lean_object* v_res_1352_; 
v_sz_boxed_1350_ = lean_unbox_usize(v_sz_1347_);
lean_dec(v_sz_1347_);
v_i_boxed_1351_ = lean_unbox_usize(v_i_1348_);
lean_dec(v_i_1348_);
v_res_1352_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0(v_sz_boxed_1350_, v_i_boxed_1351_, v_bs_1349_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVars(lean_object* v_lctx_1353_){
_start:
{
lean_object* v___x_1354_; size_t v_sz_1355_; size_t v___x_1356_; lean_object* v___x_1357_; 
v___x_1354_ = l_Lean_LocalContext_getFVarIds(v_lctx_1353_);
v_sz_1355_ = lean_array_size(v___x_1354_);
v___x_1356_ = ((size_t)0ULL);
v___x_1357_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0(v_sz_1355_, v___x_1356_, v___x_1354_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVars___boxed(lean_object* v_lctx_1358_){
_start:
{
lean_object* v_res_1359_; 
v_res_1359_ = l_Lean_LocalContext_getFVars(v_lctx_1358_);
lean_dec_ref(v_lctx_1358_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(lean_object* v_a_1360_){
_start:
{
lean_object* v_size_1361_; lean_object* v___x_1362_; uint8_t v___x_1363_; 
v_size_1361_ = lean_ctor_get(v_a_1360_, 2);
v___x_1362_ = lean_unsigned_to_nat(0u);
v___x_1363_ = lean_nat_dec_eq(v_size_1361_, v___x_1362_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1364_ = lean_box(0);
v___x_1365_ = lean_unsigned_to_nat(1u);
v___x_1366_ = lean_nat_sub(v_size_1361_, v___x_1365_);
v___x_1367_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1364_, v_a_1360_, v___x_1366_);
lean_dec(v___x_1366_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v___x_1368_; 
v___x_1368_ = l_Lean_PersistentArray_pop___redArg(v_a_1360_);
v_a_1360_ = v___x_1368_;
goto _start;
}
else
{
lean_dec_ref_known(v___x_1367_, 1);
return v_a_1360_;
}
}
else
{
return v_a_1360_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(lean_object* v_k_1370_, lean_object* v_t_1371_){
_start:
{
if (lean_obj_tag(v_t_1371_) == 0)
{
lean_object* v_k_1372_; lean_object* v_v_1373_; lean_object* v_l_1374_; lean_object* v_r_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_2029_; 
v_k_1372_ = lean_ctor_get(v_t_1371_, 1);
v_v_1373_ = lean_ctor_get(v_t_1371_, 2);
v_l_1374_ = lean_ctor_get(v_t_1371_, 3);
v_r_1375_ = lean_ctor_get(v_t_1371_, 4);
v_isSharedCheck_2029_ = !lean_is_exclusive(v_t_1371_);
if (v_isSharedCheck_2029_ == 0)
{
lean_object* v_unused_2030_; 
v_unused_2030_ = lean_ctor_get(v_t_1371_, 0);
lean_dec(v_unused_2030_);
v___x_1377_ = v_t_1371_;
v_isShared_1378_ = v_isSharedCheck_2029_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_r_1375_);
lean_inc(v_l_1374_);
lean_inc(v_v_1373_);
lean_inc(v_k_1372_);
lean_dec(v_t_1371_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_2029_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
uint8_t v___x_1379_; 
v___x_1379_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1370_, v_k_1372_);
switch(v___x_1379_)
{
case 0:
{
lean_object* v_impl_1380_; lean_object* v___x_1381_; 
v_impl_1380_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_1370_, v_l_1374_);
v___x_1381_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1380_) == 0)
{
if (lean_obj_tag(v_r_1375_) == 0)
{
lean_object* v_size_1382_; lean_object* v_size_1383_; lean_object* v_k_1384_; lean_object* v_v_1385_; lean_object* v_l_1386_; lean_object* v_r_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; uint8_t v___x_1390_; 
v_size_1382_ = lean_ctor_get(v_impl_1380_, 0);
lean_inc(v_size_1382_);
v_size_1383_ = lean_ctor_get(v_r_1375_, 0);
v_k_1384_ = lean_ctor_get(v_r_1375_, 1);
v_v_1385_ = lean_ctor_get(v_r_1375_, 2);
v_l_1386_ = lean_ctor_get(v_r_1375_, 3);
lean_inc(v_l_1386_);
v_r_1387_ = lean_ctor_get(v_r_1375_, 4);
v___x_1388_ = lean_unsigned_to_nat(3u);
v___x_1389_ = lean_nat_mul(v___x_1388_, v_size_1382_);
v___x_1390_ = lean_nat_dec_lt(v___x_1389_, v_size_1383_);
lean_dec(v___x_1389_);
if (v___x_1390_ == 0)
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1394_; 
lean_dec(v_l_1386_);
v___x_1391_ = lean_nat_add(v___x_1381_, v_size_1382_);
lean_dec(v_size_1382_);
v___x_1392_ = lean_nat_add(v___x_1391_, v_size_1383_);
lean_dec(v___x_1391_);
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 3, v_impl_1380_);
lean_ctor_set(v___x_1377_, 0, v___x_1392_);
v___x_1394_ = v___x_1377_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1392_);
lean_ctor_set(v_reuseFailAlloc_1395_, 1, v_k_1372_);
lean_ctor_set(v_reuseFailAlloc_1395_, 2, v_v_1373_);
lean_ctor_set(v_reuseFailAlloc_1395_, 3, v_impl_1380_);
lean_ctor_set(v_reuseFailAlloc_1395_, 4, v_r_1375_);
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
lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1459_; 
lean_inc(v_r_1387_);
lean_inc(v_v_1385_);
lean_inc(v_k_1384_);
lean_inc(v_size_1383_);
v_isSharedCheck_1459_ = !lean_is_exclusive(v_r_1375_);
if (v_isSharedCheck_1459_ == 0)
{
lean_object* v_unused_1460_; lean_object* v_unused_1461_; lean_object* v_unused_1462_; lean_object* v_unused_1463_; lean_object* v_unused_1464_; 
v_unused_1460_ = lean_ctor_get(v_r_1375_, 4);
lean_dec(v_unused_1460_);
v_unused_1461_ = lean_ctor_get(v_r_1375_, 3);
lean_dec(v_unused_1461_);
v_unused_1462_ = lean_ctor_get(v_r_1375_, 2);
lean_dec(v_unused_1462_);
v_unused_1463_ = lean_ctor_get(v_r_1375_, 1);
lean_dec(v_unused_1463_);
v_unused_1464_ = lean_ctor_get(v_r_1375_, 0);
lean_dec(v_unused_1464_);
v___x_1397_ = v_r_1375_;
v_isShared_1398_ = v_isSharedCheck_1459_;
goto v_resetjp_1396_;
}
else
{
lean_dec(v_r_1375_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1459_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v_size_1399_; lean_object* v_k_1400_; lean_object* v_v_1401_; lean_object* v_l_1402_; lean_object* v_r_1403_; lean_object* v_size_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; uint8_t v___x_1407_; 
v_size_1399_ = lean_ctor_get(v_l_1386_, 0);
v_k_1400_ = lean_ctor_get(v_l_1386_, 1);
v_v_1401_ = lean_ctor_get(v_l_1386_, 2);
v_l_1402_ = lean_ctor_get(v_l_1386_, 3);
v_r_1403_ = lean_ctor_get(v_l_1386_, 4);
v_size_1404_ = lean_ctor_get(v_r_1387_, 0);
v___x_1405_ = lean_unsigned_to_nat(2u);
v___x_1406_ = lean_nat_mul(v___x_1405_, v_size_1404_);
v___x_1407_ = lean_nat_dec_lt(v_size_1399_, v___x_1406_);
lean_dec(v___x_1406_);
if (v___x_1407_ == 0)
{
lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1435_; 
lean_inc(v_r_1403_);
lean_inc(v_l_1402_);
lean_inc(v_v_1401_);
lean_inc(v_k_1400_);
v_isSharedCheck_1435_ = !lean_is_exclusive(v_l_1386_);
if (v_isSharedCheck_1435_ == 0)
{
lean_object* v_unused_1436_; lean_object* v_unused_1437_; lean_object* v_unused_1438_; lean_object* v_unused_1439_; lean_object* v_unused_1440_; 
v_unused_1436_ = lean_ctor_get(v_l_1386_, 4);
lean_dec(v_unused_1436_);
v_unused_1437_ = lean_ctor_get(v_l_1386_, 3);
lean_dec(v_unused_1437_);
v_unused_1438_ = lean_ctor_get(v_l_1386_, 2);
lean_dec(v_unused_1438_);
v_unused_1439_ = lean_ctor_get(v_l_1386_, 1);
lean_dec(v_unused_1439_);
v_unused_1440_ = lean_ctor_get(v_l_1386_, 0);
lean_dec(v_unused_1440_);
v___x_1409_ = v_l_1386_;
v_isShared_1410_ = v_isSharedCheck_1435_;
goto v_resetjp_1408_;
}
else
{
lean_dec(v_l_1386_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1435_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1425_; 
v___x_1411_ = lean_nat_add(v___x_1381_, v_size_1382_);
lean_dec(v_size_1382_);
v___x_1412_ = lean_nat_add(v___x_1411_, v_size_1383_);
lean_dec(v_size_1383_);
if (lean_obj_tag(v_l_1402_) == 0)
{
lean_object* v_size_1433_; 
v_size_1433_ = lean_ctor_get(v_l_1402_, 0);
lean_inc(v_size_1433_);
v___y_1425_ = v_size_1433_;
goto v___jp_1424_;
}
else
{
lean_object* v___x_1434_; 
v___x_1434_ = lean_unsigned_to_nat(0u);
v___y_1425_ = v___x_1434_;
goto v___jp_1424_;
}
v___jp_1413_:
{
lean_object* v___x_1417_; lean_object* v___x_1419_; 
v___x_1417_ = lean_nat_add(v___y_1415_, v___y_1416_);
lean_dec(v___y_1416_);
lean_dec(v___y_1415_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 4, v_r_1387_);
lean_ctor_set(v___x_1409_, 3, v_r_1403_);
lean_ctor_set(v___x_1409_, 2, v_v_1385_);
lean_ctor_set(v___x_1409_, 1, v_k_1384_);
lean_ctor_set(v___x_1409_, 0, v___x_1417_);
v___x_1419_ = v___x_1409_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1417_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v_k_1384_);
lean_ctor_set(v_reuseFailAlloc_1423_, 2, v_v_1385_);
lean_ctor_set(v_reuseFailAlloc_1423_, 3, v_r_1403_);
lean_ctor_set(v_reuseFailAlloc_1423_, 4, v_r_1387_);
v___x_1419_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
lean_object* v___x_1421_; 
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 4, v___x_1419_);
lean_ctor_set(v___x_1397_, 3, v___y_1414_);
lean_ctor_set(v___x_1397_, 2, v_v_1401_);
lean_ctor_set(v___x_1397_, 1, v_k_1400_);
lean_ctor_set(v___x_1397_, 0, v___x_1412_);
v___x_1421_ = v___x_1397_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1412_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v_k_1400_);
lean_ctor_set(v_reuseFailAlloc_1422_, 2, v_v_1401_);
lean_ctor_set(v_reuseFailAlloc_1422_, 3, v___y_1414_);
lean_ctor_set(v_reuseFailAlloc_1422_, 4, v___x_1419_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
v___jp_1424_:
{
lean_object* v___x_1426_; lean_object* v___x_1428_; 
v___x_1426_ = lean_nat_add(v___x_1411_, v___y_1425_);
lean_dec(v___y_1425_);
lean_dec(v___x_1411_);
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 4, v_l_1402_);
lean_ctor_set(v___x_1377_, 3, v_impl_1380_);
lean_ctor_set(v___x_1377_, 0, v___x_1426_);
v___x_1428_ = v___x_1377_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1426_);
lean_ctor_set(v_reuseFailAlloc_1432_, 1, v_k_1372_);
lean_ctor_set(v_reuseFailAlloc_1432_, 2, v_v_1373_);
lean_ctor_set(v_reuseFailAlloc_1432_, 3, v_impl_1380_);
lean_ctor_set(v_reuseFailAlloc_1432_, 4, v_l_1402_);
v___x_1428_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
lean_object* v___x_1429_; 
v___x_1429_ = lean_nat_add(v___x_1381_, v_size_1404_);
if (lean_obj_tag(v_r_1403_) == 0)
{
lean_object* v_size_1430_; 
v_size_1430_ = lean_ctor_get(v_r_1403_, 0);
lean_inc(v_size_1430_);
v___y_1414_ = v___x_1428_;
v___y_1415_ = v___x_1429_;
v___y_1416_ = v_size_1430_;
goto v___jp_1413_;
}
else
{
lean_object* v___x_1431_; 
v___x_1431_ = lean_unsigned_to_nat(0u);
v___y_1414_ = v___x_1428_;
v___y_1415_ = v___x_1429_;
v___y_1416_ = v___x_1431_;
goto v___jp_1413_;
}
}
}
}
}
else
{
lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1445_; 
lean_del_object(v___x_1377_);
v___x_1441_ = lean_nat_add(v___x_1381_, v_size_1382_);
lean_dec(v_size_1382_);
v___x_1442_ = lean_nat_add(v___x_1441_, v_size_1383_);
lean_dec(v_size_1383_);
v___x_1443_ = lean_nat_add(v___x_1441_, v_size_1399_);
lean_dec(v___x_1441_);
lean_inc_ref(v_impl_1380_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 4, v_l_1386_);
lean_ctor_set(v___x_1397_, 3, v_impl_1380_);
lean_ctor_set(v___x_1397_, 2, v_v_1373_);
lean_ctor_set(v___x_1397_, 1, v_k_1372_);
lean_ctor_set(v___x_1397_, 0, v___x_1443_);
v___x_1445_ = v___x_1397_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1443_);
lean_ctor_set(v_reuseFailAlloc_1458_, 1, v_k_1372_);
lean_ctor_set(v_reuseFailAlloc_1458_, 2, v_v_1373_);
lean_ctor_set(v_reuseFailAlloc_1458_, 3, v_impl_1380_);
lean_ctor_set(v_reuseFailAlloc_1458_, 4, v_l_1386_);
v___x_1445_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1452_; 
v_isSharedCheck_1452_ = !lean_is_exclusive(v_impl_1380_);
if (v_isSharedCheck_1452_ == 0)
{
lean_object* v_unused_1453_; lean_object* v_unused_1454_; lean_object* v_unused_1455_; lean_object* v_unused_1456_; lean_object* v_unused_1457_; 
v_unused_1453_ = lean_ctor_get(v_impl_1380_, 4);
lean_dec(v_unused_1453_);
v_unused_1454_ = lean_ctor_get(v_impl_1380_, 3);
lean_dec(v_unused_1454_);
v_unused_1455_ = lean_ctor_get(v_impl_1380_, 2);
lean_dec(v_unused_1455_);
v_unused_1456_ = lean_ctor_get(v_impl_1380_, 1);
lean_dec(v_unused_1456_);
v_unused_1457_ = lean_ctor_get(v_impl_1380_, 0);
lean_dec(v_unused_1457_);
v___x_1447_ = v_impl_1380_;
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
else
{
lean_dec(v_impl_1380_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1450_; 
if (v_isShared_1448_ == 0)
{
lean_ctor_set(v___x_1447_, 4, v_r_1387_);
lean_ctor_set(v___x_1447_, 3, v___x_1445_);
lean_ctor_set(v___x_1447_, 2, v_v_1385_);
lean_ctor_set(v___x_1447_, 1, v_k_1384_);
lean_ctor_set(v___x_1447_, 0, v___x_1442_);
v___x_1450_ = v___x_1447_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1442_);
lean_ctor_set(v_reuseFailAlloc_1451_, 1, v_k_1384_);
lean_ctor_set(v_reuseFailAlloc_1451_, 2, v_v_1385_);
lean_ctor_set(v_reuseFailAlloc_1451_, 3, v___x_1445_);
lean_ctor_set(v_reuseFailAlloc_1451_, 4, v_r_1387_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1465_; lean_object* v___x_1466_; lean_object* v___x_1468_; 
v_size_1465_ = lean_ctor_get(v_impl_1380_, 0);
lean_inc(v_size_1465_);
v___x_1466_ = lean_nat_add(v___x_1381_, v_size_1465_);
lean_dec(v_size_1465_);
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 3, v_impl_1380_);
lean_ctor_set(v___x_1377_, 0, v___x_1466_);
v___x_1468_ = v___x_1377_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v___x_1466_);
lean_ctor_set(v_reuseFailAlloc_1469_, 1, v_k_1372_);
lean_ctor_set(v_reuseFailAlloc_1469_, 2, v_v_1373_);
lean_ctor_set(v_reuseFailAlloc_1469_, 3, v_impl_1380_);
lean_ctor_set(v_reuseFailAlloc_1469_, 4, v_r_1375_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
else
{
if (lean_obj_tag(v_r_1375_) == 0)
{
lean_object* v_l_1470_; 
v_l_1470_ = lean_ctor_get(v_r_1375_, 3);
lean_inc(v_l_1470_);
if (lean_obj_tag(v_l_1470_) == 0)
{
lean_object* v_r_1471_; 
v_r_1471_ = lean_ctor_get(v_r_1375_, 4);
lean_inc(v_r_1471_);
if (lean_obj_tag(v_r_1471_) == 0)
{
lean_object* v_size_1472_; lean_object* v_k_1473_; lean_object* v_v_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1487_; 
v_size_1472_ = lean_ctor_get(v_r_1375_, 0);
v_k_1473_ = lean_ctor_get(v_r_1375_, 1);
v_v_1474_ = lean_ctor_get(v_r_1375_, 2);
v_isSharedCheck_1487_ = !lean_is_exclusive(v_r_1375_);
if (v_isSharedCheck_1487_ == 0)
{
lean_object* v_unused_1488_; lean_object* v_unused_1489_; 
v_unused_1488_ = lean_ctor_get(v_r_1375_, 4);
lean_dec(v_unused_1488_);
v_unused_1489_ = lean_ctor_get(v_r_1375_, 3);
lean_dec(v_unused_1489_);
v___x_1476_ = v_r_1375_;
v_isShared_1477_ = v_isSharedCheck_1487_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_v_1474_);
lean_inc(v_k_1473_);
lean_inc(v_size_1472_);
lean_dec(v_r_1375_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1487_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v_size_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1482_; 
v_size_1478_ = lean_ctor_get(v_l_1470_, 0);
v___x_1479_ = lean_nat_add(v___x_1381_, v_size_1472_);
lean_dec(v_size_1472_);
v___x_1480_ = lean_nat_add(v___x_1381_, v_size_1478_);
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 4, v_l_1470_);
lean_ctor_set(v___x_1476_, 3, v_impl_1380_);
lean_ctor_set(v___x_1476_, 2, v_v_1373_);
lean_ctor_set(v___x_1476_, 1, v_k_1372_);
lean_ctor_set(v___x_1476_, 0, v___x_1480_);
v___x_1482_ = v___x_1476_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v___x_1480_);
lean_ctor_set(v_reuseFailAlloc_1486_, 1, v_k_1372_);
lean_ctor_set(v_reuseFailAlloc_1486_, 2, v_v_1373_);
lean_ctor_set(v_reuseFailAlloc_1486_, 3, v_impl_1380_);
lean_ctor_set(v_reuseFailAlloc_1486_, 4, v_l_1470_);
v___x_1482_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
lean_object* v___x_1484_; 
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 4, v_r_1471_);
lean_ctor_set(v___x_1377_, 3, v___x_1482_);
lean_ctor_set(v___x_1377_, 2, v_v_1474_);
lean_ctor_set(v___x_1377_, 1, v_k_1473_);
lean_ctor_set(v___x_1377_, 0, v___x_1479_);
v___x_1484_ = v___x_1377_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1479_);
lean_ctor_set(v_reuseFailAlloc_1485_, 1, v_k_1473_);
lean_ctor_set(v_reuseFailAlloc_1485_, 2, v_v_1474_);
lean_ctor_set(v_reuseFailAlloc_1485_, 3, v___x_1482_);
lean_ctor_set(v_reuseFailAlloc_1485_, 4, v_r_1471_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
else
{
lean_object* v_k_1490_; lean_object* v_v_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1514_; 
v_k_1490_ = lean_ctor_get(v_r_1375_, 1);
v_v_1491_ = lean_ctor_get(v_r_1375_, 2);
v_isSharedCheck_1514_ = !lean_is_exclusive(v_r_1375_);
if (v_isSharedCheck_1514_ == 0)
{
lean_object* v_unused_1515_; lean_object* v_unused_1516_; lean_object* v_unused_1517_; 
v_unused_1515_ = lean_ctor_get(v_r_1375_, 4);
lean_dec(v_unused_1515_);
v_unused_1516_ = lean_ctor_get(v_r_1375_, 3);
lean_dec(v_unused_1516_);
v_unused_1517_ = lean_ctor_get(v_r_1375_, 0);
lean_dec(v_unused_1517_);
v___x_1493_ = v_r_1375_;
v_isShared_1494_ = v_isSharedCheck_1514_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_v_1491_);
lean_inc(v_k_1490_);
lean_dec(v_r_1375_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1514_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v_k_1495_; lean_object* v_v_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1510_; 
v_k_1495_ = lean_ctor_get(v_l_1470_, 1);
v_v_1496_ = lean_ctor_get(v_l_1470_, 2);
v_isSharedCheck_1510_ = !lean_is_exclusive(v_l_1470_);
if (v_isSharedCheck_1510_ == 0)
{
lean_object* v_unused_1511_; lean_object* v_unused_1512_; lean_object* v_unused_1513_; 
v_unused_1511_ = lean_ctor_get(v_l_1470_, 4);
lean_dec(v_unused_1511_);
v_unused_1512_ = lean_ctor_get(v_l_1470_, 3);
lean_dec(v_unused_1512_);
v_unused_1513_ = lean_ctor_get(v_l_1470_, 0);
lean_dec(v_unused_1513_);
v___x_1498_ = v_l_1470_;
v_isShared_1499_ = v_isSharedCheck_1510_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_v_1496_);
lean_inc(v_k_1495_);
lean_dec(v_l_1470_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1510_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1500_; lean_object* v___x_1502_; 
v___x_1500_ = lean_unsigned_to_nat(3u);
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 4, v_r_1471_);
lean_ctor_set(v___x_1498_, 3, v_r_1471_);
lean_ctor_set(v___x_1498_, 2, v_v_1373_);
lean_ctor_set(v___x_1498_, 1, v_k_1372_);
lean_ctor_set(v___x_1498_, 0, v___x_1381_);
v___x_1502_ = v___x_1498_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1381_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v_k_1372_);
lean_ctor_set(v_reuseFailAlloc_1509_, 2, v_v_1373_);
lean_ctor_set(v_reuseFailAlloc_1509_, 3, v_r_1471_);
lean_ctor_set(v_reuseFailAlloc_1509_, 4, v_r_1471_);
v___x_1502_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
lean_object* v___x_1504_; 
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 3, v_r_1471_);
lean_ctor_set(v___x_1493_, 0, v___x_1381_);
v___x_1504_ = v___x_1493_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1381_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_k_1490_);
lean_ctor_set(v_reuseFailAlloc_1508_, 2, v_v_1491_);
lean_ctor_set(v_reuseFailAlloc_1508_, 3, v_r_1471_);
lean_ctor_set(v_reuseFailAlloc_1508_, 4, v_r_1471_);
v___x_1504_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
lean_object* v___x_1506_; 
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 4, v___x_1504_);
lean_ctor_set(v___x_1377_, 3, v___x_1502_);
lean_ctor_set(v___x_1377_, 2, v_v_1496_);
lean_ctor_set(v___x_1377_, 1, v_k_1495_);
lean_ctor_set(v___x_1377_, 0, v___x_1500_);
v___x_1506_ = v___x_1377_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1500_);
lean_ctor_set(v_reuseFailAlloc_1507_, 1, v_k_1495_);
lean_ctor_set(v_reuseFailAlloc_1507_, 2, v_v_1496_);
lean_ctor_set(v_reuseFailAlloc_1507_, 3, v___x_1502_);
lean_ctor_set(v_reuseFailAlloc_1507_, 4, v___x_1504_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1518_; 
v_r_1518_ = lean_ctor_get(v_r_1375_, 4);
lean_inc(v_r_1518_);
if (lean_obj_tag(v_r_1518_) == 0)
{
lean_object* v_k_1519_; lean_object* v_v_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1531_; 
v_k_1519_ = lean_ctor_get(v_r_1375_, 1);
v_v_1520_ = lean_ctor_get(v_r_1375_, 2);
v_isSharedCheck_1531_ = !lean_is_exclusive(v_r_1375_);
if (v_isSharedCheck_1531_ == 0)
{
lean_object* v_unused_1532_; lean_object* v_unused_1533_; lean_object* v_unused_1534_; 
v_unused_1532_ = lean_ctor_get(v_r_1375_, 4);
lean_dec(v_unused_1532_);
v_unused_1533_ = lean_ctor_get(v_r_1375_, 3);
lean_dec(v_unused_1533_);
v_unused_1534_ = lean_ctor_get(v_r_1375_, 0);
lean_dec(v_unused_1534_);
v___x_1522_ = v_r_1375_;
v_isShared_1523_ = v_isSharedCheck_1531_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_v_1520_);
lean_inc(v_k_1519_);
lean_dec(v_r_1375_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1531_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1524_; lean_object* v___x_1526_; 
v___x_1524_ = lean_unsigned_to_nat(3u);
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 4, v_l_1470_);
lean_ctor_set(v___x_1522_, 2, v_v_1373_);
lean_ctor_set(v___x_1522_, 1, v_k_1372_);
lean_ctor_set(v___x_1522_, 0, v___x_1381_);
v___x_1526_ = v___x_1522_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___x_1381_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v_k_1372_);
lean_ctor_set(v_reuseFailAlloc_1530_, 2, v_v_1373_);
lean_ctor_set(v_reuseFailAlloc_1530_, 3, v_l_1470_);
lean_ctor_set(v_reuseFailAlloc_1530_, 4, v_l_1470_);
v___x_1526_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
lean_object* v___x_1528_; 
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 4, v_r_1518_);
lean_ctor_set(v___x_1377_, 3, v___x_1526_);
lean_ctor_set(v___x_1377_, 2, v_v_1520_);
lean_ctor_set(v___x_1377_, 1, v_k_1519_);
lean_ctor_set(v___x_1377_, 0, v___x_1524_);
v___x_1528_ = v___x_1377_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___x_1524_);
lean_ctor_set(v_reuseFailAlloc_1529_, 1, v_k_1519_);
lean_ctor_set(v_reuseFailAlloc_1529_, 2, v_v_1520_);
lean_ctor_set(v_reuseFailAlloc_1529_, 3, v___x_1526_);
lean_ctor_set(v_reuseFailAlloc_1529_, 4, v_r_1518_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
}
else
{
lean_object* v_size_1535_; lean_object* v_k_1536_; lean_object* v_v_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1548_; 
v_size_1535_ = lean_ctor_get(v_r_1375_, 0);
v_k_1536_ = lean_ctor_get(v_r_1375_, 1);
v_v_1537_ = lean_ctor_get(v_r_1375_, 2);
v_isSharedCheck_1548_ = !lean_is_exclusive(v_r_1375_);
if (v_isSharedCheck_1548_ == 0)
{
lean_object* v_unused_1549_; lean_object* v_unused_1550_; 
v_unused_1549_ = lean_ctor_get(v_r_1375_, 4);
lean_dec(v_unused_1549_);
v_unused_1550_ = lean_ctor_get(v_r_1375_, 3);
lean_dec(v_unused_1550_);
v___x_1539_ = v_r_1375_;
v_isShared_1540_ = v_isSharedCheck_1548_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_v_1537_);
lean_inc(v_k_1536_);
lean_inc(v_size_1535_);
lean_dec(v_r_1375_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1548_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1542_; 
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 3, v_r_1518_);
v___x_1542_ = v___x_1539_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_size_1535_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v_k_1536_);
lean_ctor_set(v_reuseFailAlloc_1547_, 2, v_v_1537_);
lean_ctor_set(v_reuseFailAlloc_1547_, 3, v_r_1518_);
lean_ctor_set(v_reuseFailAlloc_1547_, 4, v_r_1518_);
v___x_1542_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
lean_object* v___x_1543_; lean_object* v___x_1545_; 
v___x_1543_ = lean_unsigned_to_nat(2u);
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 4, v___x_1542_);
lean_ctor_set(v___x_1377_, 3, v_r_1518_);
lean_ctor_set(v___x_1377_, 0, v___x_1543_);
v___x_1545_ = v___x_1377_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1543_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v_k_1372_);
lean_ctor_set(v_reuseFailAlloc_1546_, 2, v_v_1373_);
lean_ctor_set(v_reuseFailAlloc_1546_, 3, v_r_1518_);
lean_ctor_set(v_reuseFailAlloc_1546_, 4, v___x_1542_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
}
}
}
else
{
lean_object* v___x_1552_; 
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 3, v_r_1375_);
lean_ctor_set(v___x_1377_, 0, v___x_1381_);
v___x_1552_ = v___x_1377_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1381_);
lean_ctor_set(v_reuseFailAlloc_1553_, 1, v_k_1372_);
lean_ctor_set(v_reuseFailAlloc_1553_, 2, v_v_1373_);
lean_ctor_set(v_reuseFailAlloc_1553_, 3, v_r_1375_);
lean_ctor_set(v_reuseFailAlloc_1553_, 4, v_r_1375_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
case 1:
{
lean_del_object(v___x_1377_);
lean_dec(v_v_1373_);
lean_dec(v_k_1372_);
if (lean_obj_tag(v_l_1374_) == 0)
{
if (lean_obj_tag(v_r_1375_) == 0)
{
lean_object* v_size_1554_; lean_object* v_k_1555_; lean_object* v_v_1556_; lean_object* v_l_1557_; lean_object* v_r_1558_; lean_object* v_size_1559_; lean_object* v_k_1560_; lean_object* v_v_1561_; lean_object* v_l_1562_; lean_object* v_r_1563_; lean_object* v___x_1564_; uint8_t v___x_1565_; 
v_size_1554_ = lean_ctor_get(v_l_1374_, 0);
v_k_1555_ = lean_ctor_get(v_l_1374_, 1);
v_v_1556_ = lean_ctor_get(v_l_1374_, 2);
v_l_1557_ = lean_ctor_get(v_l_1374_, 3);
v_r_1558_ = lean_ctor_get(v_l_1374_, 4);
lean_inc(v_r_1558_);
v_size_1559_ = lean_ctor_get(v_r_1375_, 0);
v_k_1560_ = lean_ctor_get(v_r_1375_, 1);
v_v_1561_ = lean_ctor_get(v_r_1375_, 2);
v_l_1562_ = lean_ctor_get(v_r_1375_, 3);
lean_inc(v_l_1562_);
v_r_1563_ = lean_ctor_get(v_r_1375_, 4);
v___x_1564_ = lean_unsigned_to_nat(1u);
v___x_1565_ = lean_nat_dec_lt(v_size_1554_, v_size_1559_);
if (v___x_1565_ == 0)
{
lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1701_; 
lean_inc(v_l_1557_);
lean_inc(v_v_1556_);
lean_inc(v_k_1555_);
v_isSharedCheck_1701_ = !lean_is_exclusive(v_l_1374_);
if (v_isSharedCheck_1701_ == 0)
{
lean_object* v_unused_1702_; lean_object* v_unused_1703_; lean_object* v_unused_1704_; lean_object* v_unused_1705_; lean_object* v_unused_1706_; 
v_unused_1702_ = lean_ctor_get(v_l_1374_, 4);
lean_dec(v_unused_1702_);
v_unused_1703_ = lean_ctor_get(v_l_1374_, 3);
lean_dec(v_unused_1703_);
v_unused_1704_ = lean_ctor_get(v_l_1374_, 2);
lean_dec(v_unused_1704_);
v_unused_1705_ = lean_ctor_get(v_l_1374_, 1);
lean_dec(v_unused_1705_);
v_unused_1706_ = lean_ctor_get(v_l_1374_, 0);
lean_dec(v_unused_1706_);
v___x_1567_ = v_l_1374_;
v_isShared_1568_ = v_isSharedCheck_1701_;
goto v_resetjp_1566_;
}
else
{
lean_dec(v_l_1374_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1701_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1569_; lean_object* v_tree_1570_; 
v___x_1569_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_1555_, v_v_1556_, v_l_1557_, v_r_1558_);
v_tree_1570_ = lean_ctor_get(v___x_1569_, 2);
lean_inc(v_tree_1570_);
if (lean_obj_tag(v_tree_1570_) == 0)
{
lean_object* v_k_1571_; lean_object* v_v_1572_; lean_object* v_size_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; uint8_t v___x_1576_; 
v_k_1571_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_k_1571_);
v_v_1572_ = lean_ctor_get(v___x_1569_, 1);
lean_inc(v_v_1572_);
lean_dec_ref(v___x_1569_);
v_size_1573_ = lean_ctor_get(v_tree_1570_, 0);
v___x_1574_ = lean_unsigned_to_nat(3u);
v___x_1575_ = lean_nat_mul(v___x_1574_, v_size_1573_);
v___x_1576_ = lean_nat_dec_lt(v___x_1575_, v_size_1559_);
lean_dec(v___x_1575_);
if (v___x_1576_ == 0)
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1580_; 
lean_dec(v_l_1562_);
v___x_1577_ = lean_nat_add(v___x_1564_, v_size_1573_);
v___x_1578_ = lean_nat_add(v___x_1577_, v_size_1559_);
lean_dec(v___x_1577_);
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 4, v_r_1375_);
lean_ctor_set(v___x_1567_, 3, v_tree_1570_);
lean_ctor_set(v___x_1567_, 2, v_v_1572_);
lean_ctor_set(v___x_1567_, 1, v_k_1571_);
lean_ctor_set(v___x_1567_, 0, v___x_1578_);
v___x_1580_ = v___x_1567_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1578_);
lean_ctor_set(v_reuseFailAlloc_1581_, 1, v_k_1571_);
lean_ctor_set(v_reuseFailAlloc_1581_, 2, v_v_1572_);
lean_ctor_set(v_reuseFailAlloc_1581_, 3, v_tree_1570_);
lean_ctor_set(v_reuseFailAlloc_1581_, 4, v_r_1375_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
else
{
lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1636_; 
lean_inc(v_r_1563_);
lean_inc(v_v_1561_);
lean_inc(v_k_1560_);
lean_inc(v_size_1559_);
v_isSharedCheck_1636_ = !lean_is_exclusive(v_r_1375_);
if (v_isSharedCheck_1636_ == 0)
{
lean_object* v_unused_1637_; lean_object* v_unused_1638_; lean_object* v_unused_1639_; lean_object* v_unused_1640_; lean_object* v_unused_1641_; 
v_unused_1637_ = lean_ctor_get(v_r_1375_, 4);
lean_dec(v_unused_1637_);
v_unused_1638_ = lean_ctor_get(v_r_1375_, 3);
lean_dec(v_unused_1638_);
v_unused_1639_ = lean_ctor_get(v_r_1375_, 2);
lean_dec(v_unused_1639_);
v_unused_1640_ = lean_ctor_get(v_r_1375_, 1);
lean_dec(v_unused_1640_);
v_unused_1641_ = lean_ctor_get(v_r_1375_, 0);
lean_dec(v_unused_1641_);
v___x_1583_ = v_r_1375_;
v_isShared_1584_ = v_isSharedCheck_1636_;
goto v_resetjp_1582_;
}
else
{
lean_dec(v_r_1375_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1636_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v_size_1585_; lean_object* v_k_1586_; lean_object* v_v_1587_; lean_object* v_l_1588_; lean_object* v_r_1589_; lean_object* v_size_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; uint8_t v___x_1593_; 
v_size_1585_ = lean_ctor_get(v_l_1562_, 0);
v_k_1586_ = lean_ctor_get(v_l_1562_, 1);
v_v_1587_ = lean_ctor_get(v_l_1562_, 2);
v_l_1588_ = lean_ctor_get(v_l_1562_, 3);
v_r_1589_ = lean_ctor_get(v_l_1562_, 4);
v_size_1590_ = lean_ctor_get(v_r_1563_, 0);
v___x_1591_ = lean_unsigned_to_nat(2u);
v___x_1592_ = lean_nat_mul(v___x_1591_, v_size_1590_);
v___x_1593_ = lean_nat_dec_lt(v_size_1585_, v___x_1592_);
lean_dec(v___x_1592_);
if (v___x_1593_ == 0)
{
lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1621_; 
lean_inc(v_r_1589_);
lean_inc(v_l_1588_);
lean_inc(v_v_1587_);
lean_inc(v_k_1586_);
v_isSharedCheck_1621_ = !lean_is_exclusive(v_l_1562_);
if (v_isSharedCheck_1621_ == 0)
{
lean_object* v_unused_1622_; lean_object* v_unused_1623_; lean_object* v_unused_1624_; lean_object* v_unused_1625_; lean_object* v_unused_1626_; 
v_unused_1622_ = lean_ctor_get(v_l_1562_, 4);
lean_dec(v_unused_1622_);
v_unused_1623_ = lean_ctor_get(v_l_1562_, 3);
lean_dec(v_unused_1623_);
v_unused_1624_ = lean_ctor_get(v_l_1562_, 2);
lean_dec(v_unused_1624_);
v_unused_1625_ = lean_ctor_get(v_l_1562_, 1);
lean_dec(v_unused_1625_);
v_unused_1626_ = lean_ctor_get(v_l_1562_, 0);
lean_dec(v_unused_1626_);
v___x_1595_ = v_l_1562_;
v_isShared_1596_ = v_isSharedCheck_1621_;
goto v_resetjp_1594_;
}
else
{
lean_dec(v_l_1562_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1621_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1611_; 
v___x_1597_ = lean_nat_add(v___x_1564_, v_size_1573_);
v___x_1598_ = lean_nat_add(v___x_1597_, v_size_1559_);
lean_dec(v_size_1559_);
if (lean_obj_tag(v_l_1588_) == 0)
{
lean_object* v_size_1619_; 
v_size_1619_ = lean_ctor_get(v_l_1588_, 0);
lean_inc(v_size_1619_);
v___y_1611_ = v_size_1619_;
goto v___jp_1610_;
}
else
{
lean_object* v___x_1620_; 
v___x_1620_ = lean_unsigned_to_nat(0u);
v___y_1611_ = v___x_1620_;
goto v___jp_1610_;
}
v___jp_1599_:
{
lean_object* v___x_1603_; lean_object* v___x_1605_; 
v___x_1603_ = lean_nat_add(v___y_1601_, v___y_1602_);
lean_dec(v___y_1602_);
lean_dec(v___y_1601_);
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 4, v_r_1563_);
lean_ctor_set(v___x_1595_, 3, v_r_1589_);
lean_ctor_set(v___x_1595_, 2, v_v_1561_);
lean_ctor_set(v___x_1595_, 1, v_k_1560_);
lean_ctor_set(v___x_1595_, 0, v___x_1603_);
v___x_1605_ = v___x_1595_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___x_1603_);
lean_ctor_set(v_reuseFailAlloc_1609_, 1, v_k_1560_);
lean_ctor_set(v_reuseFailAlloc_1609_, 2, v_v_1561_);
lean_ctor_set(v_reuseFailAlloc_1609_, 3, v_r_1589_);
lean_ctor_set(v_reuseFailAlloc_1609_, 4, v_r_1563_);
v___x_1605_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
lean_object* v___x_1607_; 
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 4, v___x_1605_);
lean_ctor_set(v___x_1583_, 3, v___y_1600_);
lean_ctor_set(v___x_1583_, 2, v_v_1587_);
lean_ctor_set(v___x_1583_, 1, v_k_1586_);
lean_ctor_set(v___x_1583_, 0, v___x_1598_);
v___x_1607_ = v___x_1583_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1598_);
lean_ctor_set(v_reuseFailAlloc_1608_, 1, v_k_1586_);
lean_ctor_set(v_reuseFailAlloc_1608_, 2, v_v_1587_);
lean_ctor_set(v_reuseFailAlloc_1608_, 3, v___y_1600_);
lean_ctor_set(v_reuseFailAlloc_1608_, 4, v___x_1605_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
v___jp_1610_:
{
lean_object* v___x_1612_; lean_object* v___x_1614_; 
v___x_1612_ = lean_nat_add(v___x_1597_, v___y_1611_);
lean_dec(v___y_1611_);
lean_dec(v___x_1597_);
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 4, v_l_1588_);
lean_ctor_set(v___x_1567_, 3, v_tree_1570_);
lean_ctor_set(v___x_1567_, 2, v_v_1572_);
lean_ctor_set(v___x_1567_, 1, v_k_1571_);
lean_ctor_set(v___x_1567_, 0, v___x_1612_);
v___x_1614_ = v___x_1567_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___x_1612_);
lean_ctor_set(v_reuseFailAlloc_1618_, 1, v_k_1571_);
lean_ctor_set(v_reuseFailAlloc_1618_, 2, v_v_1572_);
lean_ctor_set(v_reuseFailAlloc_1618_, 3, v_tree_1570_);
lean_ctor_set(v_reuseFailAlloc_1618_, 4, v_l_1588_);
v___x_1614_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
lean_object* v___x_1615_; 
v___x_1615_ = lean_nat_add(v___x_1564_, v_size_1590_);
if (lean_obj_tag(v_r_1589_) == 0)
{
lean_object* v_size_1616_; 
v_size_1616_ = lean_ctor_get(v_r_1589_, 0);
lean_inc(v_size_1616_);
v___y_1600_ = v___x_1614_;
v___y_1601_ = v___x_1615_;
v___y_1602_ = v_size_1616_;
goto v___jp_1599_;
}
else
{
lean_object* v___x_1617_; 
v___x_1617_ = lean_unsigned_to_nat(0u);
v___y_1600_ = v___x_1614_;
v___y_1601_ = v___x_1615_;
v___y_1602_ = v___x_1617_;
goto v___jp_1599_;
}
}
}
}
}
else
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1631_; 
v___x_1627_ = lean_nat_add(v___x_1564_, v_size_1573_);
v___x_1628_ = lean_nat_add(v___x_1627_, v_size_1559_);
lean_dec(v_size_1559_);
v___x_1629_ = lean_nat_add(v___x_1627_, v_size_1585_);
lean_dec(v___x_1627_);
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 4, v_l_1562_);
lean_ctor_set(v___x_1583_, 3, v_tree_1570_);
lean_ctor_set(v___x_1583_, 2, v_v_1572_);
lean_ctor_set(v___x_1583_, 1, v_k_1571_);
lean_ctor_set(v___x_1583_, 0, v___x_1629_);
v___x_1631_ = v___x_1583_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v___x_1629_);
lean_ctor_set(v_reuseFailAlloc_1635_, 1, v_k_1571_);
lean_ctor_set(v_reuseFailAlloc_1635_, 2, v_v_1572_);
lean_ctor_set(v_reuseFailAlloc_1635_, 3, v_tree_1570_);
lean_ctor_set(v_reuseFailAlloc_1635_, 4, v_l_1562_);
v___x_1631_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
lean_object* v___x_1633_; 
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 4, v_r_1563_);
lean_ctor_set(v___x_1567_, 3, v___x_1631_);
lean_ctor_set(v___x_1567_, 2, v_v_1561_);
lean_ctor_set(v___x_1567_, 1, v_k_1560_);
lean_ctor_set(v___x_1567_, 0, v___x_1628_);
v___x_1633_ = v___x_1567_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v___x_1628_);
lean_ctor_set(v_reuseFailAlloc_1634_, 1, v_k_1560_);
lean_ctor_set(v_reuseFailAlloc_1634_, 2, v_v_1561_);
lean_ctor_set(v_reuseFailAlloc_1634_, 3, v___x_1631_);
lean_ctor_set(v_reuseFailAlloc_1634_, 4, v_r_1563_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
}
}
}
else
{
lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1695_; 
lean_inc(v_r_1563_);
lean_inc(v_v_1561_);
lean_inc(v_k_1560_);
lean_inc(v_size_1559_);
v_isSharedCheck_1695_ = !lean_is_exclusive(v_r_1375_);
if (v_isSharedCheck_1695_ == 0)
{
lean_object* v_unused_1696_; lean_object* v_unused_1697_; lean_object* v_unused_1698_; lean_object* v_unused_1699_; lean_object* v_unused_1700_; 
v_unused_1696_ = lean_ctor_get(v_r_1375_, 4);
lean_dec(v_unused_1696_);
v_unused_1697_ = lean_ctor_get(v_r_1375_, 3);
lean_dec(v_unused_1697_);
v_unused_1698_ = lean_ctor_get(v_r_1375_, 2);
lean_dec(v_unused_1698_);
v_unused_1699_ = lean_ctor_get(v_r_1375_, 1);
lean_dec(v_unused_1699_);
v_unused_1700_ = lean_ctor_get(v_r_1375_, 0);
lean_dec(v_unused_1700_);
v___x_1643_ = v_r_1375_;
v_isShared_1644_ = v_isSharedCheck_1695_;
goto v_resetjp_1642_;
}
else
{
lean_dec(v_r_1375_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1695_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
if (lean_obj_tag(v_l_1562_) == 0)
{
if (lean_obj_tag(v_r_1563_) == 0)
{
lean_object* v_k_1645_; lean_object* v_v_1646_; lean_object* v_size_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1651_; 
v_k_1645_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_k_1645_);
v_v_1646_ = lean_ctor_get(v___x_1569_, 1);
lean_inc(v_v_1646_);
lean_dec_ref(v___x_1569_);
v_size_1647_ = lean_ctor_get(v_l_1562_, 0);
v___x_1648_ = lean_nat_add(v___x_1564_, v_size_1559_);
lean_dec(v_size_1559_);
v___x_1649_ = lean_nat_add(v___x_1564_, v_size_1647_);
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 4, v_l_1562_);
lean_ctor_set(v___x_1643_, 3, v_tree_1570_);
lean_ctor_set(v___x_1643_, 2, v_v_1646_);
lean_ctor_set(v___x_1643_, 1, v_k_1645_);
lean_ctor_set(v___x_1643_, 0, v___x_1649_);
v___x_1651_ = v___x_1643_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1649_);
lean_ctor_set(v_reuseFailAlloc_1655_, 1, v_k_1645_);
lean_ctor_set(v_reuseFailAlloc_1655_, 2, v_v_1646_);
lean_ctor_set(v_reuseFailAlloc_1655_, 3, v_tree_1570_);
lean_ctor_set(v_reuseFailAlloc_1655_, 4, v_l_1562_);
v___x_1651_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
lean_object* v___x_1653_; 
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 4, v_r_1563_);
lean_ctor_set(v___x_1567_, 3, v___x_1651_);
lean_ctor_set(v___x_1567_, 2, v_v_1561_);
lean_ctor_set(v___x_1567_, 1, v_k_1560_);
lean_ctor_set(v___x_1567_, 0, v___x_1648_);
v___x_1653_ = v___x_1567_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1648_);
lean_ctor_set(v_reuseFailAlloc_1654_, 1, v_k_1560_);
lean_ctor_set(v_reuseFailAlloc_1654_, 2, v_v_1561_);
lean_ctor_set(v_reuseFailAlloc_1654_, 3, v___x_1651_);
lean_ctor_set(v_reuseFailAlloc_1654_, 4, v_r_1563_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
else
{
lean_object* v_k_1656_; lean_object* v_v_1657_; lean_object* v_k_1658_; lean_object* v_v_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1673_; 
lean_dec(v_size_1559_);
v_k_1656_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_k_1656_);
v_v_1657_ = lean_ctor_get(v___x_1569_, 1);
lean_inc(v_v_1657_);
lean_dec_ref(v___x_1569_);
v_k_1658_ = lean_ctor_get(v_l_1562_, 1);
v_v_1659_ = lean_ctor_get(v_l_1562_, 2);
v_isSharedCheck_1673_ = !lean_is_exclusive(v_l_1562_);
if (v_isSharedCheck_1673_ == 0)
{
lean_object* v_unused_1674_; lean_object* v_unused_1675_; lean_object* v_unused_1676_; 
v_unused_1674_ = lean_ctor_get(v_l_1562_, 4);
lean_dec(v_unused_1674_);
v_unused_1675_ = lean_ctor_get(v_l_1562_, 3);
lean_dec(v_unused_1675_);
v_unused_1676_ = lean_ctor_get(v_l_1562_, 0);
lean_dec(v_unused_1676_);
v___x_1661_ = v_l_1562_;
v_isShared_1662_ = v_isSharedCheck_1673_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_v_1659_);
lean_inc(v_k_1658_);
lean_dec(v_l_1562_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1673_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1663_; lean_object* v___x_1665_; 
v___x_1663_ = lean_unsigned_to_nat(3u);
if (v_isShared_1662_ == 0)
{
lean_ctor_set(v___x_1661_, 4, v_r_1563_);
lean_ctor_set(v___x_1661_, 3, v_r_1563_);
lean_ctor_set(v___x_1661_, 2, v_v_1657_);
lean_ctor_set(v___x_1661_, 1, v_k_1656_);
lean_ctor_set(v___x_1661_, 0, v___x_1564_);
v___x_1665_ = v___x_1661_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1564_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v_k_1656_);
lean_ctor_set(v_reuseFailAlloc_1672_, 2, v_v_1657_);
lean_ctor_set(v_reuseFailAlloc_1672_, 3, v_r_1563_);
lean_ctor_set(v_reuseFailAlloc_1672_, 4, v_r_1563_);
v___x_1665_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
lean_object* v___x_1667_; 
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 3, v_r_1563_);
lean_ctor_set(v___x_1643_, 0, v___x_1564_);
v___x_1667_ = v___x_1643_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1564_);
lean_ctor_set(v_reuseFailAlloc_1671_, 1, v_k_1560_);
lean_ctor_set(v_reuseFailAlloc_1671_, 2, v_v_1561_);
lean_ctor_set(v_reuseFailAlloc_1671_, 3, v_r_1563_);
lean_ctor_set(v_reuseFailAlloc_1671_, 4, v_r_1563_);
v___x_1667_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
lean_object* v___x_1669_; 
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 4, v___x_1667_);
lean_ctor_set(v___x_1567_, 3, v___x_1665_);
lean_ctor_set(v___x_1567_, 2, v_v_1659_);
lean_ctor_set(v___x_1567_, 1, v_k_1658_);
lean_ctor_set(v___x_1567_, 0, v___x_1663_);
v___x_1669_ = v___x_1567_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v___x_1663_);
lean_ctor_set(v_reuseFailAlloc_1670_, 1, v_k_1658_);
lean_ctor_set(v_reuseFailAlloc_1670_, 2, v_v_1659_);
lean_ctor_set(v_reuseFailAlloc_1670_, 3, v___x_1665_);
lean_ctor_set(v_reuseFailAlloc_1670_, 4, v___x_1667_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1563_) == 0)
{
lean_object* v_k_1677_; lean_object* v_v_1678_; lean_object* v___x_1679_; lean_object* v___x_1681_; 
lean_dec(v_size_1559_);
v_k_1677_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_k_1677_);
v_v_1678_ = lean_ctor_get(v___x_1569_, 1);
lean_inc(v_v_1678_);
lean_dec_ref(v___x_1569_);
v___x_1679_ = lean_unsigned_to_nat(3u);
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 4, v_l_1562_);
lean_ctor_set(v___x_1643_, 2, v_v_1678_);
lean_ctor_set(v___x_1643_, 1, v_k_1677_);
lean_ctor_set(v___x_1643_, 0, v___x_1564_);
v___x_1681_ = v___x_1643_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v___x_1564_);
lean_ctor_set(v_reuseFailAlloc_1685_, 1, v_k_1677_);
lean_ctor_set(v_reuseFailAlloc_1685_, 2, v_v_1678_);
lean_ctor_set(v_reuseFailAlloc_1685_, 3, v_l_1562_);
lean_ctor_set(v_reuseFailAlloc_1685_, 4, v_l_1562_);
v___x_1681_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
lean_object* v___x_1683_; 
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 4, v_r_1563_);
lean_ctor_set(v___x_1567_, 3, v___x_1681_);
lean_ctor_set(v___x_1567_, 2, v_v_1561_);
lean_ctor_set(v___x_1567_, 1, v_k_1560_);
lean_ctor_set(v___x_1567_, 0, v___x_1679_);
v___x_1683_ = v___x_1567_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1679_);
lean_ctor_set(v_reuseFailAlloc_1684_, 1, v_k_1560_);
lean_ctor_set(v_reuseFailAlloc_1684_, 2, v_v_1561_);
lean_ctor_set(v_reuseFailAlloc_1684_, 3, v___x_1681_);
lean_ctor_set(v_reuseFailAlloc_1684_, 4, v_r_1563_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
else
{
lean_object* v_k_1686_; lean_object* v_v_1687_; lean_object* v___x_1689_; 
v_k_1686_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_k_1686_);
v_v_1687_ = lean_ctor_get(v___x_1569_, 1);
lean_inc(v_v_1687_);
lean_dec_ref(v___x_1569_);
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 3, v_r_1563_);
v___x_1689_ = v___x_1643_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_size_1559_);
lean_ctor_set(v_reuseFailAlloc_1694_, 1, v_k_1560_);
lean_ctor_set(v_reuseFailAlloc_1694_, 2, v_v_1561_);
lean_ctor_set(v_reuseFailAlloc_1694_, 3, v_r_1563_);
lean_ctor_set(v_reuseFailAlloc_1694_, 4, v_r_1563_);
v___x_1689_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
lean_object* v___x_1690_; lean_object* v___x_1692_; 
v___x_1690_ = lean_unsigned_to_nat(2u);
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 4, v___x_1689_);
lean_ctor_set(v___x_1567_, 3, v_r_1563_);
lean_ctor_set(v___x_1567_, 2, v_v_1687_);
lean_ctor_set(v___x_1567_, 1, v_k_1686_);
lean_ctor_set(v___x_1567_, 0, v___x_1690_);
v___x_1692_ = v___x_1567_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1690_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v_k_1686_);
lean_ctor_set(v_reuseFailAlloc_1693_, 2, v_v_1687_);
lean_ctor_set(v_reuseFailAlloc_1693_, 3, v_r_1563_);
lean_ctor_set(v_reuseFailAlloc_1693_, 4, v___x_1689_);
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
}
}
else
{
lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1859_; 
lean_inc(v_r_1563_);
lean_inc(v_v_1561_);
lean_inc(v_k_1560_);
v_isSharedCheck_1859_ = !lean_is_exclusive(v_r_1375_);
if (v_isSharedCheck_1859_ == 0)
{
lean_object* v_unused_1860_; lean_object* v_unused_1861_; lean_object* v_unused_1862_; lean_object* v_unused_1863_; lean_object* v_unused_1864_; 
v_unused_1860_ = lean_ctor_get(v_r_1375_, 4);
lean_dec(v_unused_1860_);
v_unused_1861_ = lean_ctor_get(v_r_1375_, 3);
lean_dec(v_unused_1861_);
v_unused_1862_ = lean_ctor_get(v_r_1375_, 2);
lean_dec(v_unused_1862_);
v_unused_1863_ = lean_ctor_get(v_r_1375_, 1);
lean_dec(v_unused_1863_);
v_unused_1864_ = lean_ctor_get(v_r_1375_, 0);
lean_dec(v_unused_1864_);
v___x_1708_ = v_r_1375_;
v_isShared_1709_ = v_isSharedCheck_1859_;
goto v_resetjp_1707_;
}
else
{
lean_dec(v_r_1375_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1859_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1710_; lean_object* v_tree_1711_; 
v___x_1710_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_1560_, v_v_1561_, v_l_1562_, v_r_1563_);
v_tree_1711_ = lean_ctor_get(v___x_1710_, 2);
lean_inc(v_tree_1711_);
if (lean_obj_tag(v_tree_1711_) == 0)
{
lean_object* v_k_1712_; lean_object* v_v_1713_; lean_object* v_size_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; uint8_t v___x_1717_; 
v_k_1712_ = lean_ctor_get(v___x_1710_, 0);
lean_inc(v_k_1712_);
v_v_1713_ = lean_ctor_get(v___x_1710_, 1);
lean_inc(v_v_1713_);
lean_dec_ref(v___x_1710_);
v_size_1714_ = lean_ctor_get(v_tree_1711_, 0);
v___x_1715_ = lean_unsigned_to_nat(3u);
v___x_1716_ = lean_nat_mul(v___x_1715_, v_size_1714_);
v___x_1717_ = lean_nat_dec_lt(v___x_1716_, v_size_1554_);
lean_dec(v___x_1716_);
if (v___x_1717_ == 0)
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1721_; 
lean_dec(v_r_1558_);
v___x_1718_ = lean_nat_add(v___x_1564_, v_size_1554_);
v___x_1719_ = lean_nat_add(v___x_1718_, v_size_1714_);
lean_dec(v___x_1718_);
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 4, v_tree_1711_);
lean_ctor_set(v___x_1708_, 3, v_l_1374_);
lean_ctor_set(v___x_1708_, 2, v_v_1713_);
lean_ctor_set(v___x_1708_, 1, v_k_1712_);
lean_ctor_set(v___x_1708_, 0, v___x_1719_);
v___x_1721_ = v___x_1708_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1719_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v_k_1712_);
lean_ctor_set(v_reuseFailAlloc_1722_, 2, v_v_1713_);
lean_ctor_set(v_reuseFailAlloc_1722_, 3, v_l_1374_);
lean_ctor_set(v_reuseFailAlloc_1722_, 4, v_tree_1711_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
else
{
lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1788_; 
lean_inc(v_l_1557_);
lean_inc(v_v_1556_);
lean_inc(v_k_1555_);
lean_inc(v_size_1554_);
v_isSharedCheck_1788_ = !lean_is_exclusive(v_l_1374_);
if (v_isSharedCheck_1788_ == 0)
{
lean_object* v_unused_1789_; lean_object* v_unused_1790_; lean_object* v_unused_1791_; lean_object* v_unused_1792_; lean_object* v_unused_1793_; 
v_unused_1789_ = lean_ctor_get(v_l_1374_, 4);
lean_dec(v_unused_1789_);
v_unused_1790_ = lean_ctor_get(v_l_1374_, 3);
lean_dec(v_unused_1790_);
v_unused_1791_ = lean_ctor_get(v_l_1374_, 2);
lean_dec(v_unused_1791_);
v_unused_1792_ = lean_ctor_get(v_l_1374_, 1);
lean_dec(v_unused_1792_);
v_unused_1793_ = lean_ctor_get(v_l_1374_, 0);
lean_dec(v_unused_1793_);
v___x_1724_ = v_l_1374_;
v_isShared_1725_ = v_isSharedCheck_1788_;
goto v_resetjp_1723_;
}
else
{
lean_dec(v_l_1374_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1788_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v_size_1726_; lean_object* v_size_1727_; lean_object* v_k_1728_; lean_object* v_v_1729_; lean_object* v_l_1730_; lean_object* v_r_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; uint8_t v___x_1734_; 
v_size_1726_ = lean_ctor_get(v_l_1557_, 0);
v_size_1727_ = lean_ctor_get(v_r_1558_, 0);
v_k_1728_ = lean_ctor_get(v_r_1558_, 1);
v_v_1729_ = lean_ctor_get(v_r_1558_, 2);
v_l_1730_ = lean_ctor_get(v_r_1558_, 3);
v_r_1731_ = lean_ctor_get(v_r_1558_, 4);
v___x_1732_ = lean_unsigned_to_nat(2u);
v___x_1733_ = lean_nat_mul(v___x_1732_, v_size_1726_);
v___x_1734_ = lean_nat_dec_lt(v_size_1727_, v___x_1733_);
lean_dec(v___x_1733_);
if (v___x_1734_ == 0)
{
lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1772_; 
lean_inc(v_r_1731_);
lean_inc(v_l_1730_);
lean_inc(v_v_1729_);
lean_inc(v_k_1728_);
lean_del_object(v___x_1724_);
v_isSharedCheck_1772_ = !lean_is_exclusive(v_r_1558_);
if (v_isSharedCheck_1772_ == 0)
{
lean_object* v_unused_1773_; lean_object* v_unused_1774_; lean_object* v_unused_1775_; lean_object* v_unused_1776_; lean_object* v_unused_1777_; 
v_unused_1773_ = lean_ctor_get(v_r_1558_, 4);
lean_dec(v_unused_1773_);
v_unused_1774_ = lean_ctor_get(v_r_1558_, 3);
lean_dec(v_unused_1774_);
v_unused_1775_ = lean_ctor_get(v_r_1558_, 2);
lean_dec(v_unused_1775_);
v_unused_1776_ = lean_ctor_get(v_r_1558_, 1);
lean_dec(v_unused_1776_);
v_unused_1777_ = lean_ctor_get(v_r_1558_, 0);
lean_dec(v_unused_1777_);
v___x_1736_ = v_r_1558_;
v_isShared_1737_ = v_isSharedCheck_1772_;
goto v_resetjp_1735_;
}
else
{
lean_dec(v_r_1558_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1772_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v___y_1743_; lean_object* v___x_1760_; lean_object* v___y_1762_; 
v___x_1738_ = lean_nat_add(v___x_1564_, v_size_1554_);
lean_dec(v_size_1554_);
v___x_1739_ = lean_nat_add(v___x_1738_, v_size_1714_);
lean_dec(v___x_1738_);
v___x_1760_ = lean_nat_add(v___x_1564_, v_size_1726_);
if (lean_obj_tag(v_l_1730_) == 0)
{
lean_object* v_size_1770_; 
v_size_1770_ = lean_ctor_get(v_l_1730_, 0);
lean_inc(v_size_1770_);
v___y_1762_ = v_size_1770_;
goto v___jp_1761_;
}
else
{
lean_object* v___x_1771_; 
v___x_1771_ = lean_unsigned_to_nat(0u);
v___y_1762_ = v___x_1771_;
goto v___jp_1761_;
}
v___jp_1740_:
{
lean_object* v___x_1744_; lean_object* v___x_1746_; 
v___x_1744_ = lean_nat_add(v___y_1741_, v___y_1743_);
lean_dec(v___y_1743_);
lean_dec(v___y_1741_);
lean_inc_ref(v_tree_1711_);
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 4, v_tree_1711_);
lean_ctor_set(v___x_1736_, 3, v_r_1731_);
lean_ctor_set(v___x_1736_, 2, v_v_1713_);
lean_ctor_set(v___x_1736_, 1, v_k_1712_);
lean_ctor_set(v___x_1736_, 0, v___x_1744_);
v___x_1746_ = v___x_1736_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1744_);
lean_ctor_set(v_reuseFailAlloc_1759_, 1, v_k_1712_);
lean_ctor_set(v_reuseFailAlloc_1759_, 2, v_v_1713_);
lean_ctor_set(v_reuseFailAlloc_1759_, 3, v_r_1731_);
lean_ctor_set(v_reuseFailAlloc_1759_, 4, v_tree_1711_);
v___x_1746_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1753_; 
v_isSharedCheck_1753_ = !lean_is_exclusive(v_tree_1711_);
if (v_isSharedCheck_1753_ == 0)
{
lean_object* v_unused_1754_; lean_object* v_unused_1755_; lean_object* v_unused_1756_; lean_object* v_unused_1757_; lean_object* v_unused_1758_; 
v_unused_1754_ = lean_ctor_get(v_tree_1711_, 4);
lean_dec(v_unused_1754_);
v_unused_1755_ = lean_ctor_get(v_tree_1711_, 3);
lean_dec(v_unused_1755_);
v_unused_1756_ = lean_ctor_get(v_tree_1711_, 2);
lean_dec(v_unused_1756_);
v_unused_1757_ = lean_ctor_get(v_tree_1711_, 1);
lean_dec(v_unused_1757_);
v_unused_1758_ = lean_ctor_get(v_tree_1711_, 0);
lean_dec(v_unused_1758_);
v___x_1748_ = v_tree_1711_;
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
else
{
lean_dec(v_tree_1711_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1751_; 
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 4, v___x_1746_);
lean_ctor_set(v___x_1748_, 3, v___y_1742_);
lean_ctor_set(v___x_1748_, 2, v_v_1729_);
lean_ctor_set(v___x_1748_, 1, v_k_1728_);
lean_ctor_set(v___x_1748_, 0, v___x_1739_);
v___x_1751_ = v___x_1748_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___x_1739_);
lean_ctor_set(v_reuseFailAlloc_1752_, 1, v_k_1728_);
lean_ctor_set(v_reuseFailAlloc_1752_, 2, v_v_1729_);
lean_ctor_set(v_reuseFailAlloc_1752_, 3, v___y_1742_);
lean_ctor_set(v_reuseFailAlloc_1752_, 4, v___x_1746_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
}
v___jp_1761_:
{
lean_object* v___x_1763_; lean_object* v___x_1765_; 
v___x_1763_ = lean_nat_add(v___x_1760_, v___y_1762_);
lean_dec(v___y_1762_);
lean_dec(v___x_1760_);
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 4, v_l_1730_);
lean_ctor_set(v___x_1708_, 3, v_l_1557_);
lean_ctor_set(v___x_1708_, 2, v_v_1556_);
lean_ctor_set(v___x_1708_, 1, v_k_1555_);
lean_ctor_set(v___x_1708_, 0, v___x_1763_);
v___x_1765_ = v___x_1708_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v___x_1763_);
lean_ctor_set(v_reuseFailAlloc_1769_, 1, v_k_1555_);
lean_ctor_set(v_reuseFailAlloc_1769_, 2, v_v_1556_);
lean_ctor_set(v_reuseFailAlloc_1769_, 3, v_l_1557_);
lean_ctor_set(v_reuseFailAlloc_1769_, 4, v_l_1730_);
v___x_1765_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
lean_object* v___x_1766_; 
v___x_1766_ = lean_nat_add(v___x_1564_, v_size_1714_);
if (lean_obj_tag(v_r_1731_) == 0)
{
lean_object* v_size_1767_; 
v_size_1767_ = lean_ctor_get(v_r_1731_, 0);
lean_inc(v_size_1767_);
v___y_1741_ = v___x_1766_;
v___y_1742_ = v___x_1765_;
v___y_1743_ = v_size_1767_;
goto v___jp_1740_;
}
else
{
lean_object* v___x_1768_; 
v___x_1768_ = lean_unsigned_to_nat(0u);
v___y_1741_ = v___x_1766_;
v___y_1742_ = v___x_1765_;
v___y_1743_ = v___x_1768_;
goto v___jp_1740_;
}
}
}
}
}
else
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1783_; 
v___x_1778_ = lean_nat_add(v___x_1564_, v_size_1554_);
lean_dec(v_size_1554_);
v___x_1779_ = lean_nat_add(v___x_1778_, v_size_1714_);
lean_dec(v___x_1778_);
v___x_1780_ = lean_nat_add(v___x_1564_, v_size_1714_);
v___x_1781_ = lean_nat_add(v___x_1780_, v_size_1727_);
lean_dec(v___x_1780_);
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 4, v_tree_1711_);
lean_ctor_set(v___x_1708_, 3, v_r_1558_);
lean_ctor_set(v___x_1708_, 2, v_v_1713_);
lean_ctor_set(v___x_1708_, 1, v_k_1712_);
lean_ctor_set(v___x_1708_, 0, v___x_1781_);
v___x_1783_ = v___x_1708_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1781_);
lean_ctor_set(v_reuseFailAlloc_1787_, 1, v_k_1712_);
lean_ctor_set(v_reuseFailAlloc_1787_, 2, v_v_1713_);
lean_ctor_set(v_reuseFailAlloc_1787_, 3, v_r_1558_);
lean_ctor_set(v_reuseFailAlloc_1787_, 4, v_tree_1711_);
v___x_1783_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
lean_object* v___x_1785_; 
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 4, v___x_1783_);
lean_ctor_set(v___x_1724_, 0, v___x_1779_);
v___x_1785_ = v___x_1724_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1779_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v_k_1555_);
lean_ctor_set(v_reuseFailAlloc_1786_, 2, v_v_1556_);
lean_ctor_set(v_reuseFailAlloc_1786_, 3, v_l_1557_);
lean_ctor_set(v_reuseFailAlloc_1786_, 4, v___x_1783_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_1557_) == 0)
{
lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1817_; 
lean_inc_ref(v_l_1557_);
lean_inc(v_v_1556_);
lean_inc(v_k_1555_);
lean_inc(v_size_1554_);
v_isSharedCheck_1817_ = !lean_is_exclusive(v_l_1374_);
if (v_isSharedCheck_1817_ == 0)
{
lean_object* v_unused_1818_; lean_object* v_unused_1819_; lean_object* v_unused_1820_; lean_object* v_unused_1821_; lean_object* v_unused_1822_; 
v_unused_1818_ = lean_ctor_get(v_l_1374_, 4);
lean_dec(v_unused_1818_);
v_unused_1819_ = lean_ctor_get(v_l_1374_, 3);
lean_dec(v_unused_1819_);
v_unused_1820_ = lean_ctor_get(v_l_1374_, 2);
lean_dec(v_unused_1820_);
v_unused_1821_ = lean_ctor_get(v_l_1374_, 1);
lean_dec(v_unused_1821_);
v_unused_1822_ = lean_ctor_get(v_l_1374_, 0);
lean_dec(v_unused_1822_);
v___x_1795_ = v_l_1374_;
v_isShared_1796_ = v_isSharedCheck_1817_;
goto v_resetjp_1794_;
}
else
{
lean_dec(v_l_1374_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1817_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
if (lean_obj_tag(v_r_1558_) == 0)
{
lean_object* v_k_1797_; lean_object* v_v_1798_; lean_object* v_size_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1803_; 
v_k_1797_ = lean_ctor_get(v___x_1710_, 0);
lean_inc(v_k_1797_);
v_v_1798_ = lean_ctor_get(v___x_1710_, 1);
lean_inc(v_v_1798_);
lean_dec_ref(v___x_1710_);
v_size_1799_ = lean_ctor_get(v_r_1558_, 0);
v___x_1800_ = lean_nat_add(v___x_1564_, v_size_1554_);
lean_dec(v_size_1554_);
v___x_1801_ = lean_nat_add(v___x_1564_, v_size_1799_);
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 4, v_tree_1711_);
lean_ctor_set(v___x_1708_, 3, v_r_1558_);
lean_ctor_set(v___x_1708_, 2, v_v_1798_);
lean_ctor_set(v___x_1708_, 1, v_k_1797_);
lean_ctor_set(v___x_1708_, 0, v___x_1801_);
v___x_1803_ = v___x_1708_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v___x_1801_);
lean_ctor_set(v_reuseFailAlloc_1807_, 1, v_k_1797_);
lean_ctor_set(v_reuseFailAlloc_1807_, 2, v_v_1798_);
lean_ctor_set(v_reuseFailAlloc_1807_, 3, v_r_1558_);
lean_ctor_set(v_reuseFailAlloc_1807_, 4, v_tree_1711_);
v___x_1803_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
lean_object* v___x_1805_; 
if (v_isShared_1796_ == 0)
{
lean_ctor_set(v___x_1795_, 4, v___x_1803_);
lean_ctor_set(v___x_1795_, 0, v___x_1800_);
v___x_1805_ = v___x_1795_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v___x_1800_);
lean_ctor_set(v_reuseFailAlloc_1806_, 1, v_k_1555_);
lean_ctor_set(v_reuseFailAlloc_1806_, 2, v_v_1556_);
lean_ctor_set(v_reuseFailAlloc_1806_, 3, v_l_1557_);
lean_ctor_set(v_reuseFailAlloc_1806_, 4, v___x_1803_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
else
{
lean_object* v_k_1808_; lean_object* v_v_1809_; lean_object* v___x_1810_; lean_object* v___x_1812_; 
lean_dec(v_size_1554_);
v_k_1808_ = lean_ctor_get(v___x_1710_, 0);
lean_inc(v_k_1808_);
v_v_1809_ = lean_ctor_get(v___x_1710_, 1);
lean_inc(v_v_1809_);
lean_dec_ref(v___x_1710_);
v___x_1810_ = lean_unsigned_to_nat(3u);
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 4, v_r_1558_);
lean_ctor_set(v___x_1708_, 3, v_r_1558_);
lean_ctor_set(v___x_1708_, 2, v_v_1809_);
lean_ctor_set(v___x_1708_, 1, v_k_1808_);
lean_ctor_set(v___x_1708_, 0, v___x_1564_);
v___x_1812_ = v___x_1708_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1564_);
lean_ctor_set(v_reuseFailAlloc_1816_, 1, v_k_1808_);
lean_ctor_set(v_reuseFailAlloc_1816_, 2, v_v_1809_);
lean_ctor_set(v_reuseFailAlloc_1816_, 3, v_r_1558_);
lean_ctor_set(v_reuseFailAlloc_1816_, 4, v_r_1558_);
v___x_1812_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
lean_object* v___x_1814_; 
if (v_isShared_1796_ == 0)
{
lean_ctor_set(v___x_1795_, 4, v___x_1812_);
lean_ctor_set(v___x_1795_, 0, v___x_1810_);
v___x_1814_ = v___x_1795_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1810_);
lean_ctor_set(v_reuseFailAlloc_1815_, 1, v_k_1555_);
lean_ctor_set(v_reuseFailAlloc_1815_, 2, v_v_1556_);
lean_ctor_set(v_reuseFailAlloc_1815_, 3, v_l_1557_);
lean_ctor_set(v_reuseFailAlloc_1815_, 4, v___x_1812_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1558_) == 0)
{
lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1847_; 
lean_inc(v_l_1557_);
lean_inc(v_v_1556_);
lean_inc(v_k_1555_);
v_isSharedCheck_1847_ = !lean_is_exclusive(v_l_1374_);
if (v_isSharedCheck_1847_ == 0)
{
lean_object* v_unused_1848_; lean_object* v_unused_1849_; lean_object* v_unused_1850_; lean_object* v_unused_1851_; lean_object* v_unused_1852_; 
v_unused_1848_ = lean_ctor_get(v_l_1374_, 4);
lean_dec(v_unused_1848_);
v_unused_1849_ = lean_ctor_get(v_l_1374_, 3);
lean_dec(v_unused_1849_);
v_unused_1850_ = lean_ctor_get(v_l_1374_, 2);
lean_dec(v_unused_1850_);
v_unused_1851_ = lean_ctor_get(v_l_1374_, 1);
lean_dec(v_unused_1851_);
v_unused_1852_ = lean_ctor_get(v_l_1374_, 0);
lean_dec(v_unused_1852_);
v___x_1824_ = v_l_1374_;
v_isShared_1825_ = v_isSharedCheck_1847_;
goto v_resetjp_1823_;
}
else
{
lean_dec(v_l_1374_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1847_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v_k_1826_; lean_object* v_v_1827_; lean_object* v_k_1828_; lean_object* v_v_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1843_; 
v_k_1826_ = lean_ctor_get(v___x_1710_, 0);
lean_inc(v_k_1826_);
v_v_1827_ = lean_ctor_get(v___x_1710_, 1);
lean_inc(v_v_1827_);
lean_dec_ref(v___x_1710_);
v_k_1828_ = lean_ctor_get(v_r_1558_, 1);
v_v_1829_ = lean_ctor_get(v_r_1558_, 2);
v_isSharedCheck_1843_ = !lean_is_exclusive(v_r_1558_);
if (v_isSharedCheck_1843_ == 0)
{
lean_object* v_unused_1844_; lean_object* v_unused_1845_; lean_object* v_unused_1846_; 
v_unused_1844_ = lean_ctor_get(v_r_1558_, 4);
lean_dec(v_unused_1844_);
v_unused_1845_ = lean_ctor_get(v_r_1558_, 3);
lean_dec(v_unused_1845_);
v_unused_1846_ = lean_ctor_get(v_r_1558_, 0);
lean_dec(v_unused_1846_);
v___x_1831_ = v_r_1558_;
v_isShared_1832_ = v_isSharedCheck_1843_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_v_1829_);
lean_inc(v_k_1828_);
lean_dec(v_r_1558_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1843_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1833_; lean_object* v___x_1835_; 
v___x_1833_ = lean_unsigned_to_nat(3u);
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 4, v_l_1557_);
lean_ctor_set(v___x_1831_, 3, v_l_1557_);
lean_ctor_set(v___x_1831_, 2, v_v_1556_);
lean_ctor_set(v___x_1831_, 1, v_k_1555_);
lean_ctor_set(v___x_1831_, 0, v___x_1564_);
v___x_1835_ = v___x_1831_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1564_);
lean_ctor_set(v_reuseFailAlloc_1842_, 1, v_k_1555_);
lean_ctor_set(v_reuseFailAlloc_1842_, 2, v_v_1556_);
lean_ctor_set(v_reuseFailAlloc_1842_, 3, v_l_1557_);
lean_ctor_set(v_reuseFailAlloc_1842_, 4, v_l_1557_);
v___x_1835_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
lean_object* v___x_1837_; 
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 4, v_l_1557_);
lean_ctor_set(v___x_1708_, 3, v_l_1557_);
lean_ctor_set(v___x_1708_, 2, v_v_1827_);
lean_ctor_set(v___x_1708_, 1, v_k_1826_);
lean_ctor_set(v___x_1708_, 0, v___x_1564_);
v___x_1837_ = v___x_1708_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1564_);
lean_ctor_set(v_reuseFailAlloc_1841_, 1, v_k_1826_);
lean_ctor_set(v_reuseFailAlloc_1841_, 2, v_v_1827_);
lean_ctor_set(v_reuseFailAlloc_1841_, 3, v_l_1557_);
lean_ctor_set(v_reuseFailAlloc_1841_, 4, v_l_1557_);
v___x_1837_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
lean_object* v___x_1839_; 
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 4, v___x_1837_);
lean_ctor_set(v___x_1824_, 3, v___x_1835_);
lean_ctor_set(v___x_1824_, 2, v_v_1829_);
lean_ctor_set(v___x_1824_, 1, v_k_1828_);
lean_ctor_set(v___x_1824_, 0, v___x_1833_);
v___x_1839_ = v___x_1824_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1833_);
lean_ctor_set(v_reuseFailAlloc_1840_, 1, v_k_1828_);
lean_ctor_set(v_reuseFailAlloc_1840_, 2, v_v_1829_);
lean_ctor_set(v_reuseFailAlloc_1840_, 3, v___x_1835_);
lean_ctor_set(v_reuseFailAlloc_1840_, 4, v___x_1837_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
}
}
}
}
else
{
lean_object* v_k_1853_; lean_object* v_v_1854_; lean_object* v___x_1855_; lean_object* v___x_1857_; 
v_k_1853_ = lean_ctor_get(v___x_1710_, 0);
lean_inc(v_k_1853_);
v_v_1854_ = lean_ctor_get(v___x_1710_, 1);
lean_inc(v_v_1854_);
lean_dec_ref(v___x_1710_);
v___x_1855_ = lean_unsigned_to_nat(2u);
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 4, v_r_1558_);
lean_ctor_set(v___x_1708_, 3, v_l_1374_);
lean_ctor_set(v___x_1708_, 2, v_v_1854_);
lean_ctor_set(v___x_1708_, 1, v_k_1853_);
lean_ctor_set(v___x_1708_, 0, v___x_1855_);
v___x_1857_ = v___x_1708_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1855_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v_k_1853_);
lean_ctor_set(v_reuseFailAlloc_1858_, 2, v_v_1854_);
lean_ctor_set(v_reuseFailAlloc_1858_, 3, v_l_1374_);
lean_ctor_set(v_reuseFailAlloc_1858_, 4, v_r_1558_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
}
}
}
else
{
return v_l_1374_;
}
}
else
{
return v_r_1375_;
}
}
default: 
{
lean_object* v_impl_1865_; lean_object* v___x_1866_; 
v_impl_1865_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_1370_, v_r_1375_);
v___x_1866_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1865_) == 0)
{
if (lean_obj_tag(v_l_1374_) == 0)
{
lean_object* v_size_1867_; lean_object* v_size_1868_; lean_object* v_k_1869_; lean_object* v_v_1870_; lean_object* v_l_1871_; lean_object* v_r_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; uint8_t v___x_1875_; 
v_size_1867_ = lean_ctor_get(v_impl_1865_, 0);
lean_inc(v_size_1867_);
v_size_1868_ = lean_ctor_get(v_l_1374_, 0);
v_k_1869_ = lean_ctor_get(v_l_1374_, 1);
v_v_1870_ = lean_ctor_get(v_l_1374_, 2);
v_l_1871_ = lean_ctor_get(v_l_1374_, 3);
v_r_1872_ = lean_ctor_get(v_l_1374_, 4);
lean_inc(v_r_1872_);
v___x_1873_ = lean_unsigned_to_nat(3u);
v___x_1874_ = lean_nat_mul(v___x_1873_, v_size_1867_);
v___x_1875_ = lean_nat_dec_lt(v___x_1874_, v_size_1868_);
lean_dec(v___x_1874_);
if (v___x_1875_ == 0)
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1879_; 
lean_dec(v_r_1872_);
v___x_1876_ = lean_nat_add(v___x_1866_, v_size_1868_);
v___x_1877_ = lean_nat_add(v___x_1876_, v_size_1867_);
lean_dec(v_size_1867_);
lean_dec(v___x_1876_);
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 4, v_impl_1865_);
lean_ctor_set(v___x_1377_, 0, v___x_1877_);
v___x_1879_ = v___x_1377_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v___x_1877_);
lean_ctor_set(v_reuseFailAlloc_1880_, 1, v_k_1372_);
lean_ctor_set(v_reuseFailAlloc_1880_, 2, v_v_1373_);
lean_ctor_set(v_reuseFailAlloc_1880_, 3, v_l_1374_);
lean_ctor_set(v_reuseFailAlloc_1880_, 4, v_impl_1865_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
else
{
lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1946_; 
lean_inc(v_l_1871_);
lean_inc(v_v_1870_);
lean_inc(v_k_1869_);
lean_inc(v_size_1868_);
v_isSharedCheck_1946_ = !lean_is_exclusive(v_l_1374_);
if (v_isSharedCheck_1946_ == 0)
{
lean_object* v_unused_1947_; lean_object* v_unused_1948_; lean_object* v_unused_1949_; lean_object* v_unused_1950_; lean_object* v_unused_1951_; 
v_unused_1947_ = lean_ctor_get(v_l_1374_, 4);
lean_dec(v_unused_1947_);
v_unused_1948_ = lean_ctor_get(v_l_1374_, 3);
lean_dec(v_unused_1948_);
v_unused_1949_ = lean_ctor_get(v_l_1374_, 2);
lean_dec(v_unused_1949_);
v_unused_1950_ = lean_ctor_get(v_l_1374_, 1);
lean_dec(v_unused_1950_);
v_unused_1951_ = lean_ctor_get(v_l_1374_, 0);
lean_dec(v_unused_1951_);
v___x_1882_ = v_l_1374_;
v_isShared_1883_ = v_isSharedCheck_1946_;
goto v_resetjp_1881_;
}
else
{
lean_dec(v_l_1374_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1946_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v_size_1884_; lean_object* v_size_1885_; lean_object* v_k_1886_; lean_object* v_v_1887_; lean_object* v_l_1888_; lean_object* v_r_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; uint8_t v___x_1892_; 
v_size_1884_ = lean_ctor_get(v_l_1871_, 0);
v_size_1885_ = lean_ctor_get(v_r_1872_, 0);
v_k_1886_ = lean_ctor_get(v_r_1872_, 1);
v_v_1887_ = lean_ctor_get(v_r_1872_, 2);
v_l_1888_ = lean_ctor_get(v_r_1872_, 3);
v_r_1889_ = lean_ctor_get(v_r_1872_, 4);
v___x_1890_ = lean_unsigned_to_nat(2u);
v___x_1891_ = lean_nat_mul(v___x_1890_, v_size_1884_);
v___x_1892_ = lean_nat_dec_lt(v_size_1885_, v___x_1891_);
lean_dec(v___x_1891_);
if (v___x_1892_ == 0)
{
lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1921_; 
lean_inc(v_r_1889_);
lean_inc(v_l_1888_);
lean_inc(v_v_1887_);
lean_inc(v_k_1886_);
v_isSharedCheck_1921_ = !lean_is_exclusive(v_r_1872_);
if (v_isSharedCheck_1921_ == 0)
{
lean_object* v_unused_1922_; lean_object* v_unused_1923_; lean_object* v_unused_1924_; lean_object* v_unused_1925_; lean_object* v_unused_1926_; 
v_unused_1922_ = lean_ctor_get(v_r_1872_, 4);
lean_dec(v_unused_1922_);
v_unused_1923_ = lean_ctor_get(v_r_1872_, 3);
lean_dec(v_unused_1923_);
v_unused_1924_ = lean_ctor_get(v_r_1872_, 2);
lean_dec(v_unused_1924_);
v_unused_1925_ = lean_ctor_get(v_r_1872_, 1);
lean_dec(v_unused_1925_);
v_unused_1926_ = lean_ctor_get(v_r_1872_, 0);
lean_dec(v_unused_1926_);
v___x_1894_ = v_r_1872_;
v_isShared_1895_ = v_isSharedCheck_1921_;
goto v_resetjp_1893_;
}
else
{
lean_dec(v_r_1872_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1921_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1901_; lean_object* v___x_1909_; lean_object* v___y_1911_; 
v___x_1896_ = lean_nat_add(v___x_1866_, v_size_1868_);
lean_dec(v_size_1868_);
v___x_1897_ = lean_nat_add(v___x_1896_, v_size_1867_);
lean_dec(v___x_1896_);
v___x_1909_ = lean_nat_add(v___x_1866_, v_size_1884_);
if (lean_obj_tag(v_l_1888_) == 0)
{
lean_object* v_size_1919_; 
v_size_1919_ = lean_ctor_get(v_l_1888_, 0);
lean_inc(v_size_1919_);
v___y_1911_ = v_size_1919_;
goto v___jp_1910_;
}
else
{
lean_object* v___x_1920_; 
v___x_1920_ = lean_unsigned_to_nat(0u);
v___y_1911_ = v___x_1920_;
goto v___jp_1910_;
}
v___jp_1898_:
{
lean_object* v___x_1902_; lean_object* v___x_1904_; 
v___x_1902_ = lean_nat_add(v___y_1899_, v___y_1901_);
lean_dec(v___y_1901_);
lean_dec(v___y_1899_);
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 4, v_impl_1865_);
lean_ctor_set(v___x_1894_, 3, v_r_1889_);
lean_ctor_set(v___x_1894_, 2, v_v_1373_);
lean_ctor_set(v___x_1894_, 1, v_k_1372_);
lean_ctor_set(v___x_1894_, 0, v___x_1902_);
v___x_1904_ = v___x_1894_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v___x_1902_);
lean_ctor_set(v_reuseFailAlloc_1908_, 1, v_k_1372_);
lean_ctor_set(v_reuseFailAlloc_1908_, 2, v_v_1373_);
lean_ctor_set(v_reuseFailAlloc_1908_, 3, v_r_1889_);
lean_ctor_set(v_reuseFailAlloc_1908_, 4, v_impl_1865_);
v___x_1904_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
lean_object* v___x_1906_; 
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 4, v___x_1904_);
lean_ctor_set(v___x_1882_, 3, v___y_1900_);
lean_ctor_set(v___x_1882_, 2, v_v_1887_);
lean_ctor_set(v___x_1882_, 1, v_k_1886_);
lean_ctor_set(v___x_1882_, 0, v___x_1897_);
v___x_1906_ = v___x_1882_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v___x_1897_);
lean_ctor_set(v_reuseFailAlloc_1907_, 1, v_k_1886_);
lean_ctor_set(v_reuseFailAlloc_1907_, 2, v_v_1887_);
lean_ctor_set(v_reuseFailAlloc_1907_, 3, v___y_1900_);
lean_ctor_set(v_reuseFailAlloc_1907_, 4, v___x_1904_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
v___jp_1910_:
{
lean_object* v___x_1912_; lean_object* v___x_1914_; 
v___x_1912_ = lean_nat_add(v___x_1909_, v___y_1911_);
lean_dec(v___y_1911_);
lean_dec(v___x_1909_);
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 4, v_l_1888_);
lean_ctor_set(v___x_1377_, 3, v_l_1871_);
lean_ctor_set(v___x_1377_, 2, v_v_1870_);
lean_ctor_set(v___x_1377_, 1, v_k_1869_);
lean_ctor_set(v___x_1377_, 0, v___x_1912_);
v___x_1914_ = v___x_1377_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1912_);
lean_ctor_set(v_reuseFailAlloc_1918_, 1, v_k_1869_);
lean_ctor_set(v_reuseFailAlloc_1918_, 2, v_v_1870_);
lean_ctor_set(v_reuseFailAlloc_1918_, 3, v_l_1871_);
lean_ctor_set(v_reuseFailAlloc_1918_, 4, v_l_1888_);
v___x_1914_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
lean_object* v___x_1915_; 
v___x_1915_ = lean_nat_add(v___x_1866_, v_size_1867_);
lean_dec(v_size_1867_);
if (lean_obj_tag(v_r_1889_) == 0)
{
lean_object* v_size_1916_; 
v_size_1916_ = lean_ctor_get(v_r_1889_, 0);
lean_inc(v_size_1916_);
v___y_1899_ = v___x_1915_;
v___y_1900_ = v___x_1914_;
v___y_1901_ = v_size_1916_;
goto v___jp_1898_;
}
else
{
lean_object* v___x_1917_; 
v___x_1917_ = lean_unsigned_to_nat(0u);
v___y_1899_ = v___x_1915_;
v___y_1900_ = v___x_1914_;
v___y_1901_ = v___x_1917_;
goto v___jp_1898_;
}
}
}
}
}
else
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1932_; 
lean_del_object(v___x_1377_);
v___x_1927_ = lean_nat_add(v___x_1866_, v_size_1868_);
lean_dec(v_size_1868_);
v___x_1928_ = lean_nat_add(v___x_1927_, v_size_1867_);
lean_dec(v___x_1927_);
v___x_1929_ = lean_nat_add(v___x_1866_, v_size_1867_);
lean_dec(v_size_1867_);
v___x_1930_ = lean_nat_add(v___x_1929_, v_size_1885_);
lean_dec(v___x_1929_);
lean_inc_ref(v_impl_1865_);
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 4, v_impl_1865_);
lean_ctor_set(v___x_1882_, 3, v_r_1872_);
lean_ctor_set(v___x_1882_, 2, v_v_1373_);
lean_ctor_set(v___x_1882_, 1, v_k_1372_);
lean_ctor_set(v___x_1882_, 0, v___x_1930_);
v___x_1932_ = v___x_1882_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v___x_1930_);
lean_ctor_set(v_reuseFailAlloc_1945_, 1, v_k_1372_);
lean_ctor_set(v_reuseFailAlloc_1945_, 2, v_v_1373_);
lean_ctor_set(v_reuseFailAlloc_1945_, 3, v_r_1872_);
lean_ctor_set(v_reuseFailAlloc_1945_, 4, v_impl_1865_);
v___x_1932_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1939_; 
v_isSharedCheck_1939_ = !lean_is_exclusive(v_impl_1865_);
if (v_isSharedCheck_1939_ == 0)
{
lean_object* v_unused_1940_; lean_object* v_unused_1941_; lean_object* v_unused_1942_; lean_object* v_unused_1943_; lean_object* v_unused_1944_; 
v_unused_1940_ = lean_ctor_get(v_impl_1865_, 4);
lean_dec(v_unused_1940_);
v_unused_1941_ = lean_ctor_get(v_impl_1865_, 3);
lean_dec(v_unused_1941_);
v_unused_1942_ = lean_ctor_get(v_impl_1865_, 2);
lean_dec(v_unused_1942_);
v_unused_1943_ = lean_ctor_get(v_impl_1865_, 1);
lean_dec(v_unused_1943_);
v_unused_1944_ = lean_ctor_get(v_impl_1865_, 0);
lean_dec(v_unused_1944_);
v___x_1934_ = v_impl_1865_;
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
else
{
lean_dec(v_impl_1865_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1937_; 
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 4, v___x_1932_);
lean_ctor_set(v___x_1934_, 3, v_l_1871_);
lean_ctor_set(v___x_1934_, 2, v_v_1870_);
lean_ctor_set(v___x_1934_, 1, v_k_1869_);
lean_ctor_set(v___x_1934_, 0, v___x_1928_);
v___x_1937_ = v___x_1934_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v___x_1928_);
lean_ctor_set(v_reuseFailAlloc_1938_, 1, v_k_1869_);
lean_ctor_set(v_reuseFailAlloc_1938_, 2, v_v_1870_);
lean_ctor_set(v_reuseFailAlloc_1938_, 3, v_l_1871_);
lean_ctor_set(v_reuseFailAlloc_1938_, 4, v___x_1932_);
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
}
}
}
else
{
lean_object* v_size_1952_; lean_object* v___x_1953_; lean_object* v___x_1955_; 
v_size_1952_ = lean_ctor_get(v_impl_1865_, 0);
lean_inc(v_size_1952_);
v___x_1953_ = lean_nat_add(v___x_1866_, v_size_1952_);
lean_dec(v_size_1952_);
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 4, v_impl_1865_);
lean_ctor_set(v___x_1377_, 0, v___x_1953_);
v___x_1955_ = v___x_1377_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v___x_1953_);
lean_ctor_set(v_reuseFailAlloc_1956_, 1, v_k_1372_);
lean_ctor_set(v_reuseFailAlloc_1956_, 2, v_v_1373_);
lean_ctor_set(v_reuseFailAlloc_1956_, 3, v_l_1374_);
lean_ctor_set(v_reuseFailAlloc_1956_, 4, v_impl_1865_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
else
{
if (lean_obj_tag(v_l_1374_) == 0)
{
lean_object* v_l_1957_; 
v_l_1957_ = lean_ctor_get(v_l_1374_, 3);
if (lean_obj_tag(v_l_1957_) == 0)
{
lean_object* v_r_1958_; 
lean_inc_ref(v_l_1957_);
v_r_1958_ = lean_ctor_get(v_l_1374_, 4);
lean_inc(v_r_1958_);
if (lean_obj_tag(v_r_1958_) == 0)
{
lean_object* v_size_1959_; lean_object* v_k_1960_; lean_object* v_v_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1974_; 
v_size_1959_ = lean_ctor_get(v_l_1374_, 0);
v_k_1960_ = lean_ctor_get(v_l_1374_, 1);
v_v_1961_ = lean_ctor_get(v_l_1374_, 2);
v_isSharedCheck_1974_ = !lean_is_exclusive(v_l_1374_);
if (v_isSharedCheck_1974_ == 0)
{
lean_object* v_unused_1975_; lean_object* v_unused_1976_; 
v_unused_1975_ = lean_ctor_get(v_l_1374_, 4);
lean_dec(v_unused_1975_);
v_unused_1976_ = lean_ctor_get(v_l_1374_, 3);
lean_dec(v_unused_1976_);
v___x_1963_ = v_l_1374_;
v_isShared_1964_ = v_isSharedCheck_1974_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_v_1961_);
lean_inc(v_k_1960_);
lean_inc(v_size_1959_);
lean_dec(v_l_1374_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1974_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v_size_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1969_; 
v_size_1965_ = lean_ctor_get(v_r_1958_, 0);
v___x_1966_ = lean_nat_add(v___x_1866_, v_size_1959_);
lean_dec(v_size_1959_);
v___x_1967_ = lean_nat_add(v___x_1866_, v_size_1965_);
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 4, v_impl_1865_);
lean_ctor_set(v___x_1963_, 3, v_r_1958_);
lean_ctor_set(v___x_1963_, 2, v_v_1373_);
lean_ctor_set(v___x_1963_, 1, v_k_1372_);
lean_ctor_set(v___x_1963_, 0, v___x_1967_);
v___x_1969_ = v___x_1963_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1967_);
lean_ctor_set(v_reuseFailAlloc_1973_, 1, v_k_1372_);
lean_ctor_set(v_reuseFailAlloc_1973_, 2, v_v_1373_);
lean_ctor_set(v_reuseFailAlloc_1973_, 3, v_r_1958_);
lean_ctor_set(v_reuseFailAlloc_1973_, 4, v_impl_1865_);
v___x_1969_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
lean_object* v___x_1971_; 
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 4, v___x_1969_);
lean_ctor_set(v___x_1377_, 3, v_l_1957_);
lean_ctor_set(v___x_1377_, 2, v_v_1961_);
lean_ctor_set(v___x_1377_, 1, v_k_1960_);
lean_ctor_set(v___x_1377_, 0, v___x_1966_);
v___x_1971_ = v___x_1377_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1966_);
lean_ctor_set(v_reuseFailAlloc_1972_, 1, v_k_1960_);
lean_ctor_set(v_reuseFailAlloc_1972_, 2, v_v_1961_);
lean_ctor_set(v_reuseFailAlloc_1972_, 3, v_l_1957_);
lean_ctor_set(v_reuseFailAlloc_1972_, 4, v___x_1969_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
}
else
{
lean_object* v_k_1977_; lean_object* v_v_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1989_; 
v_k_1977_ = lean_ctor_get(v_l_1374_, 1);
v_v_1978_ = lean_ctor_get(v_l_1374_, 2);
v_isSharedCheck_1989_ = !lean_is_exclusive(v_l_1374_);
if (v_isSharedCheck_1989_ == 0)
{
lean_object* v_unused_1990_; lean_object* v_unused_1991_; lean_object* v_unused_1992_; 
v_unused_1990_ = lean_ctor_get(v_l_1374_, 4);
lean_dec(v_unused_1990_);
v_unused_1991_ = lean_ctor_get(v_l_1374_, 3);
lean_dec(v_unused_1991_);
v_unused_1992_ = lean_ctor_get(v_l_1374_, 0);
lean_dec(v_unused_1992_);
v___x_1980_ = v_l_1374_;
v_isShared_1981_ = v_isSharedCheck_1989_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_v_1978_);
lean_inc(v_k_1977_);
lean_dec(v_l_1374_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1989_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1982_; lean_object* v___x_1984_; 
v___x_1982_ = lean_unsigned_to_nat(3u);
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 3, v_r_1958_);
lean_ctor_set(v___x_1980_, 2, v_v_1373_);
lean_ctor_set(v___x_1980_, 1, v_k_1372_);
lean_ctor_set(v___x_1980_, 0, v___x_1866_);
v___x_1984_ = v___x_1980_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1866_);
lean_ctor_set(v_reuseFailAlloc_1988_, 1, v_k_1372_);
lean_ctor_set(v_reuseFailAlloc_1988_, 2, v_v_1373_);
lean_ctor_set(v_reuseFailAlloc_1988_, 3, v_r_1958_);
lean_ctor_set(v_reuseFailAlloc_1988_, 4, v_r_1958_);
v___x_1984_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
lean_object* v___x_1986_; 
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 4, v___x_1984_);
lean_ctor_set(v___x_1377_, 3, v_l_1957_);
lean_ctor_set(v___x_1377_, 2, v_v_1978_);
lean_ctor_set(v___x_1377_, 1, v_k_1977_);
lean_ctor_set(v___x_1377_, 0, v___x_1982_);
v___x_1986_ = v___x_1377_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___x_1982_);
lean_ctor_set(v_reuseFailAlloc_1987_, 1, v_k_1977_);
lean_ctor_set(v_reuseFailAlloc_1987_, 2, v_v_1978_);
lean_ctor_set(v_reuseFailAlloc_1987_, 3, v_l_1957_);
lean_ctor_set(v_reuseFailAlloc_1987_, 4, v___x_1984_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
}
else
{
lean_object* v_r_1993_; 
v_r_1993_ = lean_ctor_get(v_l_1374_, 4);
lean_inc(v_r_1993_);
if (lean_obj_tag(v_r_1993_) == 0)
{
lean_object* v_k_1994_; lean_object* v_v_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2018_; 
lean_inc(v_l_1957_);
v_k_1994_ = lean_ctor_get(v_l_1374_, 1);
v_v_1995_ = lean_ctor_get(v_l_1374_, 2);
v_isSharedCheck_2018_ = !lean_is_exclusive(v_l_1374_);
if (v_isSharedCheck_2018_ == 0)
{
lean_object* v_unused_2019_; lean_object* v_unused_2020_; lean_object* v_unused_2021_; 
v_unused_2019_ = lean_ctor_get(v_l_1374_, 4);
lean_dec(v_unused_2019_);
v_unused_2020_ = lean_ctor_get(v_l_1374_, 3);
lean_dec(v_unused_2020_);
v_unused_2021_ = lean_ctor_get(v_l_1374_, 0);
lean_dec(v_unused_2021_);
v___x_1997_ = v_l_1374_;
v_isShared_1998_ = v_isSharedCheck_2018_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_v_1995_);
lean_inc(v_k_1994_);
lean_dec(v_l_1374_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2018_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v_k_1999_; lean_object* v_v_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2014_; 
v_k_1999_ = lean_ctor_get(v_r_1993_, 1);
v_v_2000_ = lean_ctor_get(v_r_1993_, 2);
v_isSharedCheck_2014_ = !lean_is_exclusive(v_r_1993_);
if (v_isSharedCheck_2014_ == 0)
{
lean_object* v_unused_2015_; lean_object* v_unused_2016_; lean_object* v_unused_2017_; 
v_unused_2015_ = lean_ctor_get(v_r_1993_, 4);
lean_dec(v_unused_2015_);
v_unused_2016_ = lean_ctor_get(v_r_1993_, 3);
lean_dec(v_unused_2016_);
v_unused_2017_ = lean_ctor_get(v_r_1993_, 0);
lean_dec(v_unused_2017_);
v___x_2002_ = v_r_1993_;
v_isShared_2003_ = v_isSharedCheck_2014_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_v_2000_);
lean_inc(v_k_1999_);
lean_dec(v_r_1993_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2014_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2004_; lean_object* v___x_2006_; 
v___x_2004_ = lean_unsigned_to_nat(3u);
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 4, v_l_1957_);
lean_ctor_set(v___x_2002_, 3, v_l_1957_);
lean_ctor_set(v___x_2002_, 2, v_v_1995_);
lean_ctor_set(v___x_2002_, 1, v_k_1994_);
lean_ctor_set(v___x_2002_, 0, v___x_1866_);
v___x_2006_ = v___x_2002_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_1866_);
lean_ctor_set(v_reuseFailAlloc_2013_, 1, v_k_1994_);
lean_ctor_set(v_reuseFailAlloc_2013_, 2, v_v_1995_);
lean_ctor_set(v_reuseFailAlloc_2013_, 3, v_l_1957_);
lean_ctor_set(v_reuseFailAlloc_2013_, 4, v_l_1957_);
v___x_2006_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
lean_object* v___x_2008_; 
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 4, v_l_1957_);
lean_ctor_set(v___x_1997_, 2, v_v_1373_);
lean_ctor_set(v___x_1997_, 1, v_k_1372_);
lean_ctor_set(v___x_1997_, 0, v___x_1866_);
v___x_2008_ = v___x_1997_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v___x_1866_);
lean_ctor_set(v_reuseFailAlloc_2012_, 1, v_k_1372_);
lean_ctor_set(v_reuseFailAlloc_2012_, 2, v_v_1373_);
lean_ctor_set(v_reuseFailAlloc_2012_, 3, v_l_1957_);
lean_ctor_set(v_reuseFailAlloc_2012_, 4, v_l_1957_);
v___x_2008_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
lean_object* v___x_2010_; 
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 4, v___x_2008_);
lean_ctor_set(v___x_1377_, 3, v___x_2006_);
lean_ctor_set(v___x_1377_, 2, v_v_2000_);
lean_ctor_set(v___x_1377_, 1, v_k_1999_);
lean_ctor_set(v___x_1377_, 0, v___x_2004_);
v___x_2010_ = v___x_1377_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v___x_2004_);
lean_ctor_set(v_reuseFailAlloc_2011_, 1, v_k_1999_);
lean_ctor_set(v_reuseFailAlloc_2011_, 2, v_v_2000_);
lean_ctor_set(v_reuseFailAlloc_2011_, 3, v___x_2006_);
lean_ctor_set(v_reuseFailAlloc_2011_, 4, v___x_2008_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
}
}
}
else
{
lean_object* v___x_2022_; lean_object* v___x_2024_; 
v___x_2022_ = lean_unsigned_to_nat(2u);
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 4, v_r_1993_);
lean_ctor_set(v___x_1377_, 0, v___x_2022_);
v___x_2024_ = v___x_1377_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_2022_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v_k_1372_);
lean_ctor_set(v_reuseFailAlloc_2025_, 2, v_v_1373_);
lean_ctor_set(v_reuseFailAlloc_2025_, 3, v_l_1374_);
lean_ctor_set(v_reuseFailAlloc_2025_, 4, v_r_1993_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
}
else
{
lean_object* v___x_2027_; 
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 4, v_l_1374_);
lean_ctor_set(v___x_1377_, 0, v___x_1866_);
v___x_2027_ = v___x_1377_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_1866_);
lean_ctor_set(v_reuseFailAlloc_2028_, 1, v_k_1372_);
lean_ctor_set(v_reuseFailAlloc_2028_, 2, v_v_1373_);
lean_ctor_set(v_reuseFailAlloc_2028_, 3, v_l_1374_);
lean_ctor_set(v_reuseFailAlloc_2028_, 4, v_l_1374_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
}
}
}
else
{
return v_t_1371_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg___boxed(lean_object* v_k_2031_, lean_object* v_t_2032_){
_start:
{
lean_object* v_res_2033_; 
v_res_2033_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_2031_, v_t_2032_);
lean_dec(v_k_2031_);
return v_res_2033_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3(lean_object* v_xs_2034_, lean_object* v_v_2035_, lean_object* v_i_2036_){
_start:
{
lean_object* v___x_2037_; uint8_t v___x_2038_; 
v___x_2037_ = lean_array_get_size(v_xs_2034_);
v___x_2038_ = lean_nat_dec_lt(v_i_2036_, v___x_2037_);
if (v___x_2038_ == 0)
{
lean_object* v___x_2039_; 
lean_dec(v_i_2036_);
v___x_2039_ = lean_box(0);
return v___x_2039_;
}
else
{
lean_object* v___x_2040_; uint8_t v___x_2041_; 
v___x_2040_ = lean_array_fget_borrowed(v_xs_2034_, v_i_2036_);
v___x_2041_ = l_Lean_instBEqFVarId_beq(v___x_2040_, v_v_2035_);
if (v___x_2041_ == 0)
{
lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2042_ = lean_unsigned_to_nat(1u);
v___x_2043_ = lean_nat_add(v_i_2036_, v___x_2042_);
lean_dec(v_i_2036_);
v_i_2036_ = v___x_2043_;
goto _start;
}
else
{
lean_object* v___x_2045_; 
v___x_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2045_, 0, v_i_2036_);
return v___x_2045_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_xs_2046_, lean_object* v_v_2047_, lean_object* v_i_2048_){
_start:
{
lean_object* v_res_2049_; 
v_res_2049_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3(v_xs_2046_, v_v_2047_, v_i_2048_);
lean_dec(v_v_2047_);
lean_dec_ref(v_xs_2046_);
return v_res_2049_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1(lean_object* v_xs_2050_, lean_object* v_v_2051_){
_start:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2052_ = lean_unsigned_to_nat(0u);
v___x_2053_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3(v_xs_2050_, v_v_2051_, v___x_2052_);
return v___x_2053_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_2054_, lean_object* v_v_2055_){
_start:
{
lean_object* v_res_2056_; 
v_res_2056_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1(v_xs_2054_, v_v_2055_);
lean_dec(v_v_2055_);
lean_dec_ref(v_xs_2054_);
return v_res_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(lean_object* v_x_2057_, size_t v_x_2058_, lean_object* v_x_2059_){
_start:
{
if (lean_obj_tag(v_x_2057_) == 0)
{
lean_object* v_es_2060_; lean_object* v___x_2061_; size_t v___x_2062_; size_t v___x_2063_; lean_object* v_j_2064_; lean_object* v_entry_2065_; 
v_es_2060_ = lean_ctor_get(v_x_2057_, 0);
v___x_2061_ = lean_box(2);
v___x_2062_ = ((size_t)31ULL);
v___x_2063_ = lean_usize_land(v_x_2058_, v___x_2062_);
v_j_2064_ = lean_usize_to_nat(v___x_2063_);
v_entry_2065_ = lean_array_get(v___x_2061_, v_es_2060_, v_j_2064_);
switch(lean_obj_tag(v_entry_2065_))
{
case 0:
{
lean_object* v_key_2066_; uint8_t v___x_2067_; 
v_key_2066_ = lean_ctor_get(v_entry_2065_, 0);
lean_inc(v_key_2066_);
lean_dec_ref_known(v_entry_2065_, 2);
v___x_2067_ = l_Lean_instBEqFVarId_beq(v_x_2059_, v_key_2066_);
lean_dec(v_key_2066_);
if (v___x_2067_ == 0)
{
lean_dec(v_j_2064_);
return v_x_2057_;
}
else
{
lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2075_; 
lean_inc_ref(v_es_2060_);
v_isSharedCheck_2075_ = !lean_is_exclusive(v_x_2057_);
if (v_isSharedCheck_2075_ == 0)
{
lean_object* v_unused_2076_; 
v_unused_2076_ = lean_ctor_get(v_x_2057_, 0);
lean_dec(v_unused_2076_);
v___x_2069_ = v_x_2057_;
v_isShared_2070_ = v_isSharedCheck_2075_;
goto v_resetjp_2068_;
}
else
{
lean_dec(v_x_2057_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2075_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2071_; lean_object* v___x_2073_; 
v___x_2071_ = lean_array_set(v_es_2060_, v_j_2064_, v___x_2061_);
lean_dec(v_j_2064_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 0, v___x_2071_);
v___x_2073_ = v___x_2069_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2071_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
case 1:
{
lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2111_; 
lean_inc_ref(v_es_2060_);
v_isSharedCheck_2111_ = !lean_is_exclusive(v_x_2057_);
if (v_isSharedCheck_2111_ == 0)
{
lean_object* v_unused_2112_; 
v_unused_2112_ = lean_ctor_get(v_x_2057_, 0);
lean_dec(v_unused_2112_);
v___x_2078_ = v_x_2057_;
v_isShared_2079_ = v_isSharedCheck_2111_;
goto v_resetjp_2077_;
}
else
{
lean_dec(v_x_2057_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2111_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v_node_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2110_; 
v_node_2080_ = lean_ctor_get(v_entry_2065_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v_entry_2065_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2082_ = v_entry_2065_;
v_isShared_2083_ = v_isSharedCheck_2110_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_node_2080_);
lean_dec(v_entry_2065_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2110_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
size_t v___x_2084_; lean_object* v_entries_2085_; size_t v___x_2086_; lean_object* v_newNode_2087_; lean_object* v___x_2088_; 
v___x_2084_ = ((size_t)5ULL);
v_entries_2085_ = lean_array_set(v_es_2060_, v_j_2064_, v___x_2061_);
v___x_2086_ = lean_usize_shift_right(v_x_2058_, v___x_2084_);
v_newNode_2087_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_node_2080_, v___x_2086_, v_x_2059_);
lean_inc_ref(v_newNode_2087_);
v___x_2088_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_2087_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v___x_2090_; 
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 0, v_newNode_2087_);
v___x_2090_ = v___x_2082_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_newNode_2087_);
v___x_2090_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
lean_object* v___x_2091_; lean_object* v___x_2093_; 
v___x_2091_ = lean_array_set(v_entries_2085_, v_j_2064_, v___x_2090_);
lean_dec(v_j_2064_);
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 0, v___x_2091_);
v___x_2093_ = v___x_2078_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2091_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
else
{
lean_object* v_val_2096_; lean_object* v_fst_2097_; lean_object* v_snd_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2109_; 
lean_dec_ref(v_newNode_2087_);
lean_del_object(v___x_2082_);
v_val_2096_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_val_2096_);
lean_dec_ref_known(v___x_2088_, 1);
v_fst_2097_ = lean_ctor_get(v_val_2096_, 0);
v_snd_2098_ = lean_ctor_get(v_val_2096_, 1);
v_isSharedCheck_2109_ = !lean_is_exclusive(v_val_2096_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2100_ = v_val_2096_;
v_isShared_2101_ = v_isSharedCheck_2109_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_snd_2098_);
lean_inc(v_fst_2097_);
lean_dec(v_val_2096_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2109_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2103_; 
if (v_isShared_2101_ == 0)
{
v___x_2103_ = v___x_2100_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_fst_2097_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v_snd_2098_);
v___x_2103_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
lean_object* v___x_2104_; lean_object* v___x_2106_; 
v___x_2104_ = lean_array_set(v_entries_2085_, v_j_2064_, v___x_2103_);
lean_dec(v_j_2064_);
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 0, v___x_2104_);
v___x_2106_ = v___x_2078_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2104_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_2064_);
return v_x_2057_;
}
}
}
else
{
lean_object* v_ks_2113_; lean_object* v_vs_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2128_; 
v_ks_2113_ = lean_ctor_get(v_x_2057_, 0);
v_vs_2114_ = lean_ctor_get(v_x_2057_, 1);
v_isSharedCheck_2128_ = !lean_is_exclusive(v_x_2057_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2116_ = v_x_2057_;
v_isShared_2117_ = v_isSharedCheck_2128_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_vs_2114_);
lean_inc(v_ks_2113_);
lean_dec(v_x_2057_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2128_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2118_; 
v___x_2118_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1(v_ks_2113_, v_x_2059_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v___x_2120_; 
if (v_isShared_2117_ == 0)
{
v___x_2120_ = v___x_2116_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_ks_2113_);
lean_ctor_set(v_reuseFailAlloc_2121_, 1, v_vs_2114_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
else
{
lean_object* v_val_2122_; lean_object* v_keys_x27_2123_; lean_object* v_vals_x27_2124_; lean_object* v___x_2126_; 
v_val_2122_ = lean_ctor_get(v___x_2118_, 0);
lean_inc_n(v_val_2122_, 2);
lean_dec_ref_known(v___x_2118_, 1);
v_keys_x27_2123_ = l_Array_eraseIdx___redArg(v_ks_2113_, v_val_2122_);
v_vals_x27_2124_ = l_Array_eraseIdx___redArg(v_vs_2114_, v_val_2122_);
if (v_isShared_2117_ == 0)
{
lean_ctor_set(v___x_2116_, 1, v_vals_x27_2124_);
lean_ctor_set(v___x_2116_, 0, v_keys_x27_2123_);
v___x_2126_ = v___x_2116_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_keys_x27_2123_);
lean_ctor_set(v_reuseFailAlloc_2127_, 1, v_vals_x27_2124_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg___boxed(lean_object* v_x_2129_, lean_object* v_x_2130_, lean_object* v_x_2131_){
_start:
{
size_t v_x_2685__boxed_2132_; lean_object* v_res_2133_; 
v_x_2685__boxed_2132_ = lean_unbox_usize(v_x_2130_);
lean_dec(v_x_2130_);
v_res_2133_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_x_2129_, v_x_2685__boxed_2132_, v_x_2131_);
lean_dec(v_x_2131_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(lean_object* v_x_2134_, lean_object* v_x_2135_){
_start:
{
uint64_t v___x_2136_; size_t v_h_2137_; lean_object* v___x_2138_; 
v___x_2136_ = l_Lean_instHashableFVarId_hash(v_x_2135_);
v_h_2137_ = lean_uint64_to_usize(v___x_2136_);
v___x_2138_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_x_2134_, v_h_2137_, v_x_2135_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg___boxed(lean_object* v_x_2139_, lean_object* v_x_2140_){
_start:
{
lean_object* v_res_2141_; 
v_res_2141_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_x_2139_, v_x_2140_);
lean_dec(v_x_2140_);
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_erase(lean_object* v_lctx_2142_, lean_object* v_fvarId_2143_){
_start:
{
lean_object* v_fvarIdToDecl_2144_; lean_object* v_decls_2145_; lean_object* v_auxDeclToFullName_2146_; lean_object* v___x_2147_; 
v_fvarIdToDecl_2144_ = lean_ctor_get(v_lctx_2142_, 0);
v_decls_2145_ = lean_ctor_get(v_lctx_2142_, 1);
v_auxDeclToFullName_2146_ = lean_ctor_get(v_lctx_2142_, 2);
v___x_2147_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_fvarIdToDecl_2144_, v_fvarId_2143_);
if (lean_obj_tag(v___x_2147_) == 0)
{
lean_dec(v_fvarId_2143_);
return v_lctx_2142_;
}
else
{
lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2167_; 
lean_inc(v_auxDeclToFullName_2146_);
lean_inc_ref(v_decls_2145_);
lean_inc_ref(v_fvarIdToDecl_2144_);
v_isSharedCheck_2167_ = !lean_is_exclusive(v_lctx_2142_);
if (v_isSharedCheck_2167_ == 0)
{
lean_object* v_unused_2168_; lean_object* v_unused_2169_; lean_object* v_unused_2170_; 
v_unused_2168_ = lean_ctor_get(v_lctx_2142_, 2);
lean_dec(v_unused_2168_);
v_unused_2169_ = lean_ctor_get(v_lctx_2142_, 1);
lean_dec(v_unused_2169_);
v_unused_2170_ = lean_ctor_get(v_lctx_2142_, 0);
lean_dec(v_unused_2170_);
v___x_2149_ = v_lctx_2142_;
v_isShared_2150_ = v_isSharedCheck_2167_;
goto v_resetjp_2148_;
}
else
{
lean_dec(v_lctx_2142_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2167_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v_val_2151_; lean_object* v___x_2152_; lean_object* v___y_2154_; lean_object* v_index_2166_; 
v_val_2151_ = lean_ctor_get(v___x_2147_, 0);
lean_inc(v_val_2151_);
lean_dec_ref_known(v___x_2147_, 1);
v___x_2152_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_fvarIdToDecl_2144_, v_fvarId_2143_);
v_index_2166_ = lean_ctor_get(v_val_2151_, 0);
lean_inc(v_index_2166_);
v___y_2154_ = v_index_2166_;
goto v___jp_2153_;
v___jp_2153_:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; uint8_t v___x_2158_; 
v___x_2155_ = lean_box(0);
v___x_2156_ = l_Lean_PersistentArray_set___redArg(v_decls_2145_, v___y_2154_, v___x_2155_);
lean_dec(v___y_2154_);
v___x_2157_ = l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(v___x_2156_);
v___x_2158_ = l_Lean_LocalDecl_isAuxDecl(v_val_2151_);
lean_dec(v_val_2151_);
if (v___x_2158_ == 0)
{
lean_object* v___x_2160_; 
lean_dec(v_fvarId_2143_);
if (v_isShared_2150_ == 0)
{
lean_ctor_set(v___x_2149_, 1, v___x_2157_);
lean_ctor_set(v___x_2149_, 0, v___x_2152_);
v___x_2160_ = v___x_2149_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v___x_2152_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v___x_2157_);
lean_ctor_set(v_reuseFailAlloc_2161_, 2, v_auxDeclToFullName_2146_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
else
{
lean_object* v___x_2162_; lean_object* v___x_2164_; 
v___x_2162_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_fvarId_2143_, v_auxDeclToFullName_2146_);
lean_dec(v_fvarId_2143_);
if (v_isShared_2150_ == 0)
{
lean_ctor_set(v___x_2149_, 2, v___x_2162_);
lean_ctor_set(v___x_2149_, 1, v___x_2157_);
lean_ctor_set(v___x_2149_, 0, v___x_2152_);
v___x_2164_ = v___x_2149_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v___x_2152_);
lean_ctor_set(v_reuseFailAlloc_2165_, 1, v___x_2157_);
lean_ctor_set(v_reuseFailAlloc_2165_, 2, v___x_2162_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0(lean_object* v_00_u03b2_2171_, lean_object* v_x_2172_, lean_object* v_x_2173_){
_start:
{
lean_object* v___x_2174_; 
v___x_2174_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_x_2172_, v_x_2173_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___boxed(lean_object* v_00_u03b2_2175_, lean_object* v_x_2176_, lean_object* v_x_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0(v_00_u03b2_2175_, v_x_2176_, v_x_2177_);
lean_dec(v_x_2177_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1(lean_object* v_00_u03b2_2179_, lean_object* v_k_2180_, lean_object* v_t_2181_, lean_object* v_h_2182_){
_start:
{
lean_object* v___x_2183_; 
v___x_2183_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_2180_, v_t_2181_);
return v___x_2183_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___boxed(lean_object* v_00_u03b2_2184_, lean_object* v_k_2185_, lean_object* v_t_2186_, lean_object* v_h_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1(v_00_u03b2_2184_, v_k_2185_, v_t_2186_, v_h_2187_);
lean_dec(v_k_2185_);
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0(lean_object* v_00_u03b2_2189_, lean_object* v_x_2190_, size_t v_x_2191_, lean_object* v_x_2192_){
_start:
{
lean_object* v___x_2193_; 
v___x_2193_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_x_2190_, v_x_2191_, v_x_2192_);
return v___x_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2194_, lean_object* v_x_2195_, lean_object* v_x_2196_, lean_object* v_x_2197_){
_start:
{
size_t v_x_2907__boxed_2198_; lean_object* v_res_2199_; 
v_x_2907__boxed_2198_ = lean_unbox_usize(v_x_2196_);
lean_dec(v_x_2196_);
v_res_2199_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0(v_00_u03b2_2194_, v_x_2195_, v_x_2907__boxed_2198_, v_x_2197_);
lean_dec(v_x_2197_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_pop(lean_object* v_lctx_2200_){
_start:
{
lean_object* v_decls_2201_; lean_object* v_fvarIdToDecl_2202_; lean_object* v_auxDeclToFullName_2203_; lean_object* v_size_2204_; lean_object* v___x_2205_; uint8_t v___x_2206_; 
v_decls_2201_ = lean_ctor_get(v_lctx_2200_, 1);
v_fvarIdToDecl_2202_ = lean_ctor_get(v_lctx_2200_, 0);
v_auxDeclToFullName_2203_ = lean_ctor_get(v_lctx_2200_, 2);
v_size_2204_ = lean_ctor_get(v_decls_2201_, 2);
v___x_2205_ = lean_unsigned_to_nat(0u);
v___x_2206_ = lean_nat_dec_eq(v_size_2204_, v___x_2205_);
if (v___x_2206_ == 0)
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2207_ = lean_box(0);
v___x_2208_ = lean_unsigned_to_nat(1u);
v___x_2209_ = lean_nat_sub(v_size_2204_, v___x_2208_);
v___x_2210_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2207_, v_decls_2201_, v___x_2209_);
lean_dec(v___x_2209_);
if (lean_obj_tag(v___x_2210_) == 0)
{
return v_lctx_2200_;
}
else
{
lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2229_; 
lean_inc(v_auxDeclToFullName_2203_);
lean_inc_ref(v_fvarIdToDecl_2202_);
lean_inc_ref(v_decls_2201_);
v_isSharedCheck_2229_ = !lean_is_exclusive(v_lctx_2200_);
if (v_isSharedCheck_2229_ == 0)
{
lean_object* v_unused_2230_; lean_object* v_unused_2231_; lean_object* v_unused_2232_; 
v_unused_2230_ = lean_ctor_get(v_lctx_2200_, 2);
lean_dec(v_unused_2230_);
v_unused_2231_ = lean_ctor_get(v_lctx_2200_, 1);
lean_dec(v_unused_2231_);
v_unused_2232_ = lean_ctor_get(v_lctx_2200_, 0);
lean_dec(v_unused_2232_);
v___x_2212_ = v_lctx_2200_;
v_isShared_2213_ = v_isSharedCheck_2229_;
goto v_resetjp_2211_;
}
else
{
lean_dec(v_lctx_2200_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2229_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v_val_2214_; lean_object* v___y_2216_; lean_object* v_fvarId_2228_; 
v_val_2214_ = lean_ctor_get(v___x_2210_, 0);
lean_inc(v_val_2214_);
lean_dec_ref_known(v___x_2210_, 1);
v_fvarId_2228_ = lean_ctor_get(v_val_2214_, 1);
lean_inc(v_fvarId_2228_);
v___y_2216_ = v_fvarId_2228_;
goto v___jp_2215_;
v___jp_2215_:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; uint8_t v___x_2220_; 
v___x_2217_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_fvarIdToDecl_2202_, v___y_2216_);
v___x_2218_ = l_Lean_PersistentArray_pop___redArg(v_decls_2201_);
v___x_2219_ = l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(v___x_2218_);
v___x_2220_ = l_Lean_LocalDecl_isAuxDecl(v_val_2214_);
lean_dec(v_val_2214_);
if (v___x_2220_ == 0)
{
lean_object* v___x_2222_; 
lean_dec(v___y_2216_);
if (v_isShared_2213_ == 0)
{
lean_ctor_set(v___x_2212_, 1, v___x_2219_);
lean_ctor_set(v___x_2212_, 0, v___x_2217_);
v___x_2222_ = v___x_2212_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v___x_2217_);
lean_ctor_set(v_reuseFailAlloc_2223_, 1, v___x_2219_);
lean_ctor_set(v_reuseFailAlloc_2223_, 2, v_auxDeclToFullName_2203_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
else
{
lean_object* v___x_2224_; lean_object* v___x_2226_; 
v___x_2224_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v___y_2216_, v_auxDeclToFullName_2203_);
lean_dec(v___y_2216_);
if (v_isShared_2213_ == 0)
{
lean_ctor_set(v___x_2212_, 2, v___x_2224_);
lean_ctor_set(v___x_2212_, 1, v___x_2219_);
lean_ctor_set(v___x_2212_, 0, v___x_2217_);
v___x_2226_ = v___x_2212_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v___x_2217_);
lean_ctor_set(v_reuseFailAlloc_2227_, 1, v___x_2219_);
lean_ctor_set(v_reuseFailAlloc_2227_, 2, v___x_2224_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
}
}
}
else
{
return v_lctx_2200_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(lean_object* v_userName_2233_, lean_object* v_as_2234_, lean_object* v_i_2235_){
_start:
{
lean_object* v_zero_2236_; uint8_t v_isZero_2237_; 
v_zero_2236_ = lean_unsigned_to_nat(0u);
v_isZero_2237_ = lean_nat_dec_eq(v_i_2235_, v_zero_2236_);
if (v_isZero_2237_ == 1)
{
lean_object* v___x_2238_; 
lean_dec(v_i_2235_);
v___x_2238_ = lean_box(0);
return v___x_2238_;
}
else
{
lean_object* v_one_2239_; lean_object* v_n_2240_; lean_object* v___y_2242_; lean_object* v___x_2244_; lean_object* v___y_2246_; 
v_one_2239_ = lean_unsigned_to_nat(1u);
v_n_2240_ = lean_nat_sub(v_i_2235_, v_one_2239_);
lean_dec(v_i_2235_);
v___x_2244_ = lean_array_fget_borrowed(v_as_2234_, v_n_2240_);
if (lean_obj_tag(v___x_2244_) == 0)
{
v___y_2242_ = v___x_2244_;
goto v___jp_2241_;
}
else
{
lean_object* v_val_2249_; lean_object* v_userName_2250_; 
v_val_2249_ = lean_ctor_get(v___x_2244_, 0);
v_userName_2250_ = lean_ctor_get(v_val_2249_, 2);
v___y_2246_ = v_userName_2250_;
goto v___jp_2245_;
}
v___jp_2241_:
{
if (lean_obj_tag(v___y_2242_) == 0)
{
v_i_2235_ = v_n_2240_;
goto _start;
}
else
{
lean_dec(v_n_2240_);
lean_inc_ref(v___y_2242_);
return v___y_2242_;
}
}
v___jp_2245_:
{
uint8_t v___x_2247_; 
v___x_2247_ = lean_name_eq(v___y_2246_, v_userName_2233_);
if (v___x_2247_ == 0)
{
v_i_2235_ = v_n_2240_;
goto _start;
}
else
{
v___y_2242_ = v___x_2244_;
goto v___jp_2241_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_userName_2251_, lean_object* v_as_2252_, lean_object* v_i_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2251_, v_as_2252_, v_i_2253_);
lean_dec_ref(v_as_2252_);
lean_dec(v_userName_2251_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(lean_object* v_userName_2255_, lean_object* v_as_2256_, lean_object* v_i_2257_){
_start:
{
lean_object* v_zero_2258_; uint8_t v_isZero_2259_; 
v_zero_2258_ = lean_unsigned_to_nat(0u);
v_isZero_2259_ = lean_nat_dec_eq(v_i_2257_, v_zero_2258_);
if (v_isZero_2259_ == 1)
{
lean_object* v___x_2260_; 
lean_dec(v_i_2257_);
v___x_2260_ = lean_box(0);
return v___x_2260_;
}
else
{
lean_object* v_one_2261_; lean_object* v_n_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
v_one_2261_ = lean_unsigned_to_nat(1u);
v_n_2262_ = lean_nat_sub(v_i_2257_, v_one_2261_);
lean_dec(v_i_2257_);
v___x_2263_ = lean_array_fget_borrowed(v_as_2256_, v_n_2262_);
v___x_2264_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(v_userName_2255_, v___x_2263_);
if (lean_obj_tag(v___x_2264_) == 0)
{
v_i_2257_ = v_n_2262_;
goto _start;
}
else
{
lean_dec(v_n_2262_);
return v___x_2264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(lean_object* v_userName_2266_, lean_object* v_x_2267_){
_start:
{
if (lean_obj_tag(v_x_2267_) == 0)
{
lean_object* v_cs_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
v_cs_2268_ = lean_ctor_get(v_x_2267_, 0);
v___x_2269_ = lean_array_get_size(v_cs_2268_);
v___x_2270_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(v_userName_2266_, v_cs_2268_, v___x_2269_);
return v___x_2270_;
}
else
{
lean_object* v_vs_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v_vs_2271_ = lean_ctor_get(v_x_2267_, 0);
v___x_2272_ = lean_array_get_size(v_vs_2271_);
v___x_2273_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2266_, v_vs_2271_, v___x_2272_);
return v___x_2273_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1___boxed(lean_object* v_userName_2274_, lean_object* v_x_2275_){
_start:
{
lean_object* v_res_2276_; 
v_res_2276_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(v_userName_2274_, v_x_2275_);
lean_dec_ref(v_x_2275_);
lean_dec(v_userName_2274_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_userName_2277_, lean_object* v_as_2278_, lean_object* v_i_2279_){
_start:
{
lean_object* v_res_2280_; 
v_res_2280_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(v_userName_2277_, v_as_2278_, v_i_2279_);
lean_dec_ref(v_as_2278_);
lean_dec(v_userName_2277_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0(lean_object* v_userName_2281_, lean_object* v_t_2282_){
_start:
{
lean_object* v_root_2283_; lean_object* v_tail_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v_root_2283_ = lean_ctor_get(v_t_2282_, 0);
v_tail_2284_ = lean_ctor_get(v_t_2282_, 1);
v___x_2285_ = lean_array_get_size(v_tail_2284_);
v___x_2286_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2281_, v_tail_2284_, v___x_2285_);
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_object* v___x_2287_; 
v___x_2287_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(v_userName_2281_, v_root_2283_);
return v___x_2287_;
}
else
{
return v___x_2286_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0___boxed(lean_object* v_userName_2288_, lean_object* v_t_2289_){
_start:
{
lean_object* v_res_2290_; 
v_res_2290_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0(v_userName_2288_, v_t_2289_);
lean_dec_ref(v_t_2289_);
lean_dec(v_userName_2288_);
return v_res_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object* v_lctx_2291_, lean_object* v_userName_2292_){
_start:
{
lean_object* v_decls_2293_; lean_object* v___x_2294_; 
v_decls_2293_ = lean_ctor_get(v_lctx_2291_, 1);
v___x_2294_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0(v_userName_2292_, v_decls_2293_);
return v___x_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserName_x3f___boxed(lean_object* v_lctx_2295_, lean_object* v_userName_2296_){
_start:
{
lean_object* v_res_2297_; 
v_res_2297_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2295_, v_userName_2296_);
lean_dec(v_userName_2296_);
lean_dec_ref(v_lctx_2295_);
return v_res_2297_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0(lean_object* v_userName_2298_, lean_object* v_as_2299_, lean_object* v_i_2300_, lean_object* v_a_2301_){
_start:
{
lean_object* v___x_2302_; 
v___x_2302_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2298_, v_as_2299_, v_i_2300_);
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___boxed(lean_object* v_userName_2303_, lean_object* v_as_2304_, lean_object* v_i_2305_, lean_object* v_a_2306_){
_start:
{
lean_object* v_res_2307_; 
v_res_2307_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0(v_userName_2303_, v_as_2304_, v_i_2305_, v_a_2306_);
lean_dec_ref(v_as_2304_);
lean_dec(v_userName_2303_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2(lean_object* v_userName_2308_, lean_object* v_as_2309_, lean_object* v_i_2310_, lean_object* v_a_2311_){
_start:
{
lean_object* v___x_2312_; 
v___x_2312_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(v_userName_2308_, v_as_2309_, v_i_2310_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___boxed(lean_object* v_userName_2313_, lean_object* v_as_2314_, lean_object* v_i_2315_, lean_object* v_a_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2(v_userName_2313_, v_as_2314_, v_i_2315_, v_a_2316_);
lean_dec_ref(v_as_2314_);
lean_dec(v_userName_2313_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFromUserName_x21(lean_object* v_lctx_2321_, lean_object* v_userName_2322_){
_start:
{
lean_object* v___x_2323_; 
v___x_2323_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2321_, v_userName_2322_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; uint8_t v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2324_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_2325_ = ((lean_object*)(l_Lean_LocalContext_getFromUserName_x21___closed__0));
v___x_2326_ = lean_unsigned_to_nat(403u);
v___x_2327_ = lean_unsigned_to_nat(17u);
v___x_2328_ = ((lean_object*)(l_Lean_LocalContext_getFromUserName_x21___closed__1));
v___x_2329_ = 1;
v___x_2330_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_userName_2322_, v___x_2329_);
v___x_2331_ = lean_string_append(v___x_2328_, v___x_2330_);
lean_dec_ref(v___x_2330_);
v___x_2332_ = ((lean_object*)(l_Lean_LocalContext_getFromUserName_x21___closed__2));
v___x_2333_ = lean_string_append(v___x_2331_, v___x_2332_);
v___x_2334_ = l_mkPanicMessageWithDecl(v___x_2324_, v___x_2325_, v___x_2326_, v___x_2327_, v___x_2333_);
lean_dec_ref(v___x_2333_);
v___x_2335_ = l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(v___x_2334_);
return v___x_2335_;
}
else
{
lean_object* v_val_2336_; 
lean_dec(v_userName_2322_);
v_val_2336_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_val_2336_);
lean_dec_ref_known(v___x_2323_, 1);
return v_val_2336_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFromUserName_x21___boxed(lean_object* v_lctx_2337_, lean_object* v_userName_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l_Lean_LocalContext_getFromUserName_x21(v_lctx_2337_, v_userName_2338_);
lean_dec_ref(v_lctx_2337_);
return v_res_2339_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_usesUserName(lean_object* v_lctx_2340_, lean_object* v_userName_2341_){
_start:
{
lean_object* v___x_2342_; 
v___x_2342_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2340_, v_userName_2341_);
if (lean_obj_tag(v___x_2342_) == 0)
{
uint8_t v___x_2343_; 
v___x_2343_ = 0;
return v___x_2343_;
}
else
{
uint8_t v___x_2344_; 
lean_dec_ref_known(v___x_2342_, 1);
v___x_2344_ = 1;
return v___x_2344_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_usesUserName___boxed(lean_object* v_lctx_2345_, lean_object* v_userName_2346_){
_start:
{
uint8_t v_res_2347_; lean_object* v_r_2348_; 
v_res_2347_ = l_Lean_LocalContext_usesUserName(v_lctx_2345_, v_userName_2346_);
lean_dec(v_userName_2346_);
lean_dec_ref(v_lctx_2345_);
v_r_2348_ = lean_box(v_res_2347_);
return v_r_2348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(lean_object* v_lctx_2349_, lean_object* v_suggestion_2350_, lean_object* v_i_2351_){
_start:
{
lean_object* v_curr_2352_; uint8_t v___x_2353_; 
lean_inc(v_i_2351_);
lean_inc(v_suggestion_2350_);
v_curr_2352_ = lean_name_append_index_after(v_suggestion_2350_, v_i_2351_);
v___x_2353_ = l_Lean_LocalContext_usesUserName(v_lctx_2349_, v_curr_2352_);
if (v___x_2353_ == 0)
{
lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
lean_dec(v_suggestion_2350_);
v___x_2354_ = lean_unsigned_to_nat(1u);
v___x_2355_ = lean_nat_add(v_i_2351_, v___x_2354_);
lean_dec(v_i_2351_);
v___x_2356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2356_, 0, v_curr_2352_);
lean_ctor_set(v___x_2356_, 1, v___x_2355_);
return v___x_2356_;
}
else
{
lean_object* v___x_2357_; lean_object* v___x_2358_; 
lean_dec(v_curr_2352_);
v___x_2357_ = lean_unsigned_to_nat(1u);
v___x_2358_ = lean_nat_add(v_i_2351_, v___x_2357_);
lean_dec(v_i_2351_);
v_i_2351_ = v___x_2358_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux___boxed(lean_object* v_lctx_2360_, lean_object* v_suggestion_2361_, lean_object* v_i_2362_){
_start:
{
lean_object* v_res_2363_; 
v_res_2363_ = l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(v_lctx_2360_, v_suggestion_2361_, v_i_2362_);
lean_dec_ref(v_lctx_2360_);
return v_res_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getUnusedName(lean_object* v_lctx_2364_, lean_object* v_suggestion_2365_){
_start:
{
lean_object* v_suggestion_2366_; uint8_t v___x_2367_; 
v_suggestion_2366_ = lean_erase_macro_scopes(v_suggestion_2365_);
v___x_2367_ = l_Lean_LocalContext_usesUserName(v_lctx_2364_, v_suggestion_2366_);
if (v___x_2367_ == 0)
{
return v_suggestion_2366_;
}
else
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v_fst_2370_; 
v___x_2368_ = lean_unsigned_to_nat(1u);
v___x_2369_ = l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(v_lctx_2364_, v_suggestion_2366_, v___x_2368_);
v_fst_2370_ = lean_ctor_get(v___x_2369_, 0);
lean_inc(v_fst_2370_);
lean_dec_ref(v___x_2369_);
return v_fst_2370_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getUnusedName___boxed(lean_object* v_lctx_2371_, lean_object* v_suggestion_2372_){
_start:
{
lean_object* v_res_2373_; 
v_res_2373_ = l_Lean_LocalContext_getUnusedName(v_lctx_2371_, v_suggestion_2372_);
lean_dec_ref(v_lctx_2371_);
return v_res_2373_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_lastDecl(lean_object* v_lctx_2374_){
_start:
{
lean_object* v_decls_2375_; lean_object* v_size_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; uint8_t v___x_2380_; 
v_decls_2375_ = lean_ctor_get(v_lctx_2374_, 1);
v_size_2376_ = lean_ctor_get(v_decls_2375_, 2);
v___x_2377_ = lean_box(0);
v___x_2378_ = lean_unsigned_to_nat(1u);
v___x_2379_ = lean_nat_sub(v_size_2376_, v___x_2378_);
v___x_2380_ = lean_nat_dec_lt(v___x_2379_, v_size_2376_);
if (v___x_2380_ == 0)
{
lean_object* v___x_2381_; 
lean_dec(v___x_2379_);
v___x_2381_ = l_outOfBounds___redArg(v___x_2377_);
return v___x_2381_;
}
else
{
lean_object* v___x_2382_; 
v___x_2382_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2377_, v_decls_2375_, v___x_2379_);
lean_dec(v___x_2379_);
return v___x_2382_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_lastDecl___boxed(lean_object* v_lctx_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l_Lean_LocalContext_lastDecl(v_lctx_2383_);
lean_dec_ref(v_lctx_2383_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setUserName(lean_object* v_lctx_2385_, lean_object* v_fvarId_2386_, lean_object* v_userName_2387_){
_start:
{
lean_object* v_fvarIdToDecl_2388_; lean_object* v_decls_2389_; lean_object* v_auxDeclToFullName_2390_; lean_object* v_decl_2391_; lean_object* v_decl_2392_; lean_object* v___y_2394_; lean_object* v___y_2395_; lean_object* v___y_2400_; lean_object* v_fvarId_2403_; 
v_fvarIdToDecl_2388_ = lean_ctor_get(v_lctx_2385_, 0);
lean_inc_ref(v_fvarIdToDecl_2388_);
v_decls_2389_ = lean_ctor_get(v_lctx_2385_, 1);
lean_inc_ref(v_decls_2389_);
v_auxDeclToFullName_2390_ = lean_ctor_get(v_lctx_2385_, 2);
lean_inc(v_auxDeclToFullName_2390_);
v_decl_2391_ = l_Lean_LocalContext_get_x21(v_lctx_2385_, v_fvarId_2386_);
v_decl_2392_ = l_Lean_LocalDecl_setUserName(v_decl_2391_, v_userName_2387_);
v_fvarId_2403_ = lean_ctor_get(v_decl_2392_, 1);
lean_inc(v_fvarId_2403_);
v___y_2400_ = v_fvarId_2403_;
goto v___jp_2399_;
v___jp_2393_:
{
lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2396_, 0, v_decl_2392_);
v___x_2397_ = l_Lean_PersistentArray_set___redArg(v_decls_2389_, v___y_2395_, v___x_2396_);
lean_dec(v___y_2395_);
v___x_2398_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2398_, 0, v___y_2394_);
lean_ctor_set(v___x_2398_, 1, v___x_2397_);
lean_ctor_set(v___x_2398_, 2, v_auxDeclToFullName_2390_);
return v___x_2398_;
}
v___jp_2399_:
{
lean_object* v___x_2401_; lean_object* v_index_2402_; 
lean_inc_ref(v_decl_2392_);
v___x_2401_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2388_, v___y_2400_, v_decl_2392_);
v_index_2402_ = lean_ctor_get(v_decl_2392_, 0);
lean_inc(v_index_2402_);
v___y_2394_ = v___x_2401_;
v___y_2395_ = v_index_2402_;
goto v___jp_2393_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_renameUserName(lean_object* v_lctx_2404_, lean_object* v_fromName_2405_, lean_object* v_toName_2406_){
_start:
{
lean_object* v_fvarIdToDecl_2407_; lean_object* v_decls_2408_; lean_object* v_auxDeclToFullName_2409_; lean_object* v___x_2410_; 
v_fvarIdToDecl_2407_ = lean_ctor_get(v_lctx_2404_, 0);
v_decls_2408_ = lean_ctor_get(v_lctx_2404_, 1);
v_auxDeclToFullName_2409_ = lean_ctor_get(v_lctx_2404_, 2);
v___x_2410_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2404_, v_fromName_2405_);
if (lean_obj_tag(v___x_2410_) == 0)
{
lean_dec(v_toName_2406_);
return v_lctx_2404_;
}
else
{
lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2435_; 
lean_inc(v_auxDeclToFullName_2409_);
lean_inc_ref(v_decls_2408_);
lean_inc_ref(v_fvarIdToDecl_2407_);
v_isSharedCheck_2435_ = !lean_is_exclusive(v_lctx_2404_);
if (v_isSharedCheck_2435_ == 0)
{
lean_object* v_unused_2436_; lean_object* v_unused_2437_; lean_object* v_unused_2438_; 
v_unused_2436_ = lean_ctor_get(v_lctx_2404_, 2);
lean_dec(v_unused_2436_);
v_unused_2437_ = lean_ctor_get(v_lctx_2404_, 1);
lean_dec(v_unused_2437_);
v_unused_2438_ = lean_ctor_get(v_lctx_2404_, 0);
lean_dec(v_unused_2438_);
v___x_2412_ = v_lctx_2404_;
v_isShared_2413_ = v_isSharedCheck_2435_;
goto v_resetjp_2411_;
}
else
{
lean_dec(v_lctx_2404_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2435_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v_val_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2434_; 
v_val_2414_ = lean_ctor_get(v___x_2410_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2416_ = v___x_2410_;
v_isShared_2417_ = v_isSharedCheck_2434_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_val_2414_);
lean_dec(v___x_2410_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2434_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v_decl_2418_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2430_; lean_object* v_fvarId_2433_; 
v_decl_2418_ = l_Lean_LocalDecl_setUserName(v_val_2414_, v_toName_2406_);
v_fvarId_2433_ = lean_ctor_get(v_decl_2418_, 1);
lean_inc(v_fvarId_2433_);
v___y_2430_ = v_fvarId_2433_;
goto v___jp_2429_;
v___jp_2419_:
{
lean_object* v___x_2423_; 
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 0, v_decl_2418_);
v___x_2423_ = v___x_2416_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_decl_2418_);
v___x_2423_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
lean_object* v___x_2424_; lean_object* v___x_2426_; 
v___x_2424_ = l_Lean_PersistentArray_set___redArg(v_decls_2408_, v___y_2421_, v___x_2423_);
lean_dec(v___y_2421_);
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 1, v___x_2424_);
lean_ctor_set(v___x_2412_, 0, v___y_2420_);
v___x_2426_ = v___x_2412_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___y_2420_);
lean_ctor_set(v_reuseFailAlloc_2427_, 1, v___x_2424_);
lean_ctor_set(v_reuseFailAlloc_2427_, 2, v_auxDeclToFullName_2409_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
v___jp_2429_:
{
lean_object* v___x_2431_; lean_object* v_index_2432_; 
lean_inc_ref(v_decl_2418_);
v___x_2431_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2407_, v___y_2430_, v_decl_2418_);
v_index_2432_ = lean_ctor_get(v_decl_2418_, 0);
lean_inc(v_index_2432_);
v___y_2420_ = v___x_2431_;
v___y_2421_ = v_index_2432_;
goto v___jp_2419_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_renameUserName___boxed(lean_object* v_lctx_2439_, lean_object* v_fromName_2440_, lean_object* v_toName_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l_Lean_LocalContext_renameUserName(v_lctx_2439_, v_fromName_2440_, v_toName_2441_);
lean_dec(v_fromName_2440_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_modifyLocalDecl(lean_object* v_lctx_2445_, lean_object* v_fvarId_2446_, lean_object* v_f_2447_){
_start:
{
lean_object* v_fvarIdToDecl_2448_; lean_object* v_decls_2449_; lean_object* v_auxDeclToFullName_2450_; lean_object* v___x_2451_; 
v_fvarIdToDecl_2448_ = lean_ctor_get(v_lctx_2445_, 0);
v_decls_2449_ = lean_ctor_get(v_lctx_2445_, 1);
v_auxDeclToFullName_2450_ = lean_ctor_get(v_lctx_2445_, 2);
lean_inc_ref(v_lctx_2445_);
v___x_2451_ = lean_local_ctx_find(v_lctx_2445_, v_fvarId_2446_);
if (lean_obj_tag(v___x_2451_) == 0)
{
lean_dec_ref(v_f_2447_);
return v_lctx_2445_;
}
else
{
lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2478_; 
lean_inc(v_auxDeclToFullName_2450_);
lean_inc_ref(v_decls_2449_);
lean_inc_ref(v_fvarIdToDecl_2448_);
v_isSharedCheck_2478_ = !lean_is_exclusive(v_lctx_2445_);
if (v_isSharedCheck_2478_ == 0)
{
lean_object* v_unused_2479_; lean_object* v_unused_2480_; lean_object* v_unused_2481_; 
v_unused_2479_ = lean_ctor_get(v_lctx_2445_, 2);
lean_dec(v_unused_2479_);
v_unused_2480_ = lean_ctor_get(v_lctx_2445_, 1);
lean_dec(v_unused_2480_);
v_unused_2481_ = lean_ctor_get(v_lctx_2445_, 0);
lean_dec(v_unused_2481_);
v___x_2453_ = v_lctx_2445_;
v_isShared_2454_ = v_isSharedCheck_2478_;
goto v_resetjp_2452_;
}
else
{
lean_dec(v_lctx_2445_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2478_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v_val_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2477_; 
v_val_2455_ = lean_ctor_get(v___x_2451_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2457_ = v___x_2451_;
v_isShared_2458_ = v_isSharedCheck_2477_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_val_2455_);
lean_dec(v___x_2451_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2477_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v_decl_2461_; lean_object* v___y_2463_; lean_object* v___y_2464_; lean_object* v___y_2473_; lean_object* v_fvarId_2476_; 
v___x_2459_ = ((lean_object*)(l_Lean_LocalContext_modifyLocalDecl___closed__0));
v___x_2460_ = ((lean_object*)(l_Lean_LocalContext_modifyLocalDecl___closed__1));
v_decl_2461_ = lean_apply_1(v_f_2447_, v_val_2455_);
v_fvarId_2476_ = lean_ctor_get(v_decl_2461_, 1);
lean_inc(v_fvarId_2476_);
v___y_2473_ = v_fvarId_2476_;
goto v___jp_2472_;
v___jp_2462_:
{
lean_object* v___x_2466_; 
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 0, v_decl_2461_);
v___x_2466_ = v___x_2457_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_decl_2461_);
v___x_2466_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
lean_object* v___x_2467_; lean_object* v___x_2469_; 
v___x_2467_ = l_Lean_PersistentArray_set___redArg(v_decls_2449_, v___y_2464_, v___x_2466_);
lean_dec(v___y_2464_);
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 1, v___x_2467_);
lean_ctor_set(v___x_2453_, 0, v___y_2463_);
v___x_2469_ = v___x_2453_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v___y_2463_);
lean_ctor_set(v_reuseFailAlloc_2470_, 1, v___x_2467_);
lean_ctor_set(v_reuseFailAlloc_2470_, 2, v_auxDeclToFullName_2450_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
v___jp_2472_:
{
lean_object* v___x_2474_; lean_object* v_index_2475_; 
lean_inc_ref(v_decl_2461_);
v___x_2474_ = l_Lean_PersistentHashMap_insert___redArg(v___x_2459_, v___x_2460_, v_fvarIdToDecl_2448_, v___y_2473_, v_decl_2461_);
v_index_2475_ = lean_ctor_get(v_decl_2461_, 0);
lean_inc(v_index_2475_);
v___y_2463_ = v___x_2474_;
v___y_2464_ = v_index_2475_;
goto v___jp_2462_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(lean_object* v_f_2482_, lean_object* v_as_2483_, size_t v_i_2484_, size_t v_stop_2485_, lean_object* v_b_2486_){
_start:
{
lean_object* v___y_2488_; uint8_t v___x_2492_; 
v___x_2492_ = lean_usize_dec_eq(v_i_2484_, v_stop_2485_);
if (v___x_2492_ == 0)
{
lean_object* v___x_2493_; 
v___x_2493_ = lean_array_uget(v_as_2483_, v_i_2484_);
if (lean_obj_tag(v___x_2493_) == 0)
{
v___y_2488_ = v_b_2486_;
goto v___jp_2487_;
}
else
{
lean_object* v_val_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2521_; 
v_val_2494_ = lean_ctor_get(v___x_2493_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2496_ = v___x_2493_;
v_isShared_2497_ = v_isSharedCheck_2521_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_val_2494_);
lean_dec(v___x_2493_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2521_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v_fvarIdToDecl_2498_; lean_object* v_decls_2499_; lean_object* v_auxDeclToFullName_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2520_; 
v_fvarIdToDecl_2498_ = lean_ctor_get(v_b_2486_, 0);
v_decls_2499_ = lean_ctor_get(v_b_2486_, 1);
v_auxDeclToFullName_2500_ = lean_ctor_get(v_b_2486_, 2);
v_isSharedCheck_2520_ = !lean_is_exclusive(v_b_2486_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2502_ = v_b_2486_;
v_isShared_2503_ = v_isSharedCheck_2520_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_auxDeclToFullName_2500_);
lean_inc(v_decls_2499_);
lean_inc(v_fvarIdToDecl_2498_);
lean_dec(v_b_2486_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2520_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v_decl_2504_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2516_; lean_object* v_fvarId_2519_; 
lean_inc_ref(v_f_2482_);
v_decl_2504_ = lean_apply_1(v_f_2482_, v_val_2494_);
v_fvarId_2519_ = lean_ctor_get(v_decl_2504_, 1);
lean_inc(v_fvarId_2519_);
v___y_2516_ = v_fvarId_2519_;
goto v___jp_2515_;
v___jp_2505_:
{
lean_object* v___x_2509_; 
if (v_isShared_2497_ == 0)
{
lean_ctor_set(v___x_2496_, 0, v_decl_2504_);
v___x_2509_ = v___x_2496_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_decl_2504_);
v___x_2509_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
lean_object* v___x_2510_; lean_object* v___x_2512_; 
v___x_2510_ = l_Lean_PersistentArray_set___redArg(v_decls_2499_, v___y_2507_, v___x_2509_);
lean_dec(v___y_2507_);
if (v_isShared_2503_ == 0)
{
lean_ctor_set(v___x_2502_, 1, v___x_2510_);
lean_ctor_set(v___x_2502_, 0, v___y_2506_);
v___x_2512_ = v___x_2502_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___y_2506_);
lean_ctor_set(v_reuseFailAlloc_2513_, 1, v___x_2510_);
lean_ctor_set(v_reuseFailAlloc_2513_, 2, v_auxDeclToFullName_2500_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
v___y_2488_ = v___x_2512_;
goto v___jp_2487_;
}
}
}
v___jp_2515_:
{
lean_object* v___x_2517_; lean_object* v_index_2518_; 
lean_inc_ref(v_decl_2504_);
v___x_2517_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2498_, v___y_2516_, v_decl_2504_);
v_index_2518_ = lean_ctor_get(v_decl_2504_, 0);
lean_inc(v_index_2518_);
v___y_2506_ = v___x_2517_;
v___y_2507_ = v_index_2518_;
goto v___jp_2505_;
}
}
}
}
}
else
{
lean_dec_ref(v_f_2482_);
return v_b_2486_;
}
v___jp_2487_:
{
size_t v___x_2489_; size_t v___x_2490_; 
v___x_2489_ = ((size_t)1ULL);
v___x_2490_ = lean_usize_add(v_i_2484_, v___x_2489_);
v_i_2484_ = v___x_2490_;
v_b_2486_ = v___y_2488_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1___boxed(lean_object* v_f_2522_, lean_object* v_as_2523_, lean_object* v_i_2524_, lean_object* v_stop_2525_, lean_object* v_b_2526_){
_start:
{
size_t v_i_boxed_2527_; size_t v_stop_boxed_2528_; lean_object* v_res_2529_; 
v_i_boxed_2527_ = lean_unbox_usize(v_i_2524_);
lean_dec(v_i_2524_);
v_stop_boxed_2528_ = lean_unbox_usize(v_stop_2525_);
lean_dec(v_stop_2525_);
v_res_2529_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2522_, v_as_2523_, v_i_boxed_2527_, v_stop_boxed_2528_, v_b_2526_);
lean_dec_ref(v_as_2523_);
return v_res_2529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(lean_object* v_f_2530_, lean_object* v_x_2531_, lean_object* v_x_2532_){
_start:
{
if (lean_obj_tag(v_x_2531_) == 0)
{
lean_object* v_cs_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; uint8_t v___x_2536_; 
v_cs_2533_ = lean_ctor_get(v_x_2531_, 0);
v___x_2534_ = lean_unsigned_to_nat(0u);
v___x_2535_ = lean_array_get_size(v_cs_2533_);
v___x_2536_ = lean_nat_dec_lt(v___x_2534_, v___x_2535_);
if (v___x_2536_ == 0)
{
lean_dec_ref(v_f_2530_);
return v_x_2532_;
}
else
{
uint8_t v___x_2537_; 
v___x_2537_ = lean_nat_dec_le(v___x_2535_, v___x_2535_);
if (v___x_2537_ == 0)
{
if (v___x_2536_ == 0)
{
lean_dec_ref(v_f_2530_);
return v_x_2532_;
}
else
{
size_t v___x_2538_; size_t v___x_2539_; lean_object* v___x_2540_; 
v___x_2538_ = ((size_t)0ULL);
v___x_2539_ = lean_usize_of_nat(v___x_2535_);
v___x_2540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2530_, v_cs_2533_, v___x_2538_, v___x_2539_, v_x_2532_);
return v___x_2540_;
}
}
else
{
size_t v___x_2541_; size_t v___x_2542_; lean_object* v___x_2543_; 
v___x_2541_ = ((size_t)0ULL);
v___x_2542_ = lean_usize_of_nat(v___x_2535_);
v___x_2543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2530_, v_cs_2533_, v___x_2541_, v___x_2542_, v_x_2532_);
return v___x_2543_;
}
}
}
else
{
lean_object* v_vs_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; uint8_t v___x_2547_; 
v_vs_2544_ = lean_ctor_get(v_x_2531_, 0);
v___x_2545_ = lean_unsigned_to_nat(0u);
v___x_2546_ = lean_array_get_size(v_vs_2544_);
v___x_2547_ = lean_nat_dec_lt(v___x_2545_, v___x_2546_);
if (v___x_2547_ == 0)
{
lean_dec_ref(v_f_2530_);
return v_x_2532_;
}
else
{
uint8_t v___x_2548_; 
v___x_2548_ = lean_nat_dec_le(v___x_2546_, v___x_2546_);
if (v___x_2548_ == 0)
{
if (v___x_2547_ == 0)
{
lean_dec_ref(v_f_2530_);
return v_x_2532_;
}
else
{
size_t v___x_2549_; size_t v___x_2550_; lean_object* v___x_2551_; 
v___x_2549_ = ((size_t)0ULL);
v___x_2550_ = lean_usize_of_nat(v___x_2546_);
v___x_2551_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2530_, v_vs_2544_, v___x_2549_, v___x_2550_, v_x_2532_);
return v___x_2551_;
}
}
else
{
size_t v___x_2552_; size_t v___x_2553_; lean_object* v___x_2554_; 
v___x_2552_ = ((size_t)0ULL);
v___x_2553_ = lean_usize_of_nat(v___x_2546_);
v___x_2554_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2530_, v_vs_2544_, v___x_2552_, v___x_2553_, v_x_2532_);
return v___x_2554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(lean_object* v_f_2555_, lean_object* v_as_2556_, size_t v_i_2557_, size_t v_stop_2558_, lean_object* v_b_2559_){
_start:
{
uint8_t v___x_2560_; 
v___x_2560_ = lean_usize_dec_eq(v_i_2557_, v_stop_2558_);
if (v___x_2560_ == 0)
{
lean_object* v___x_2561_; lean_object* v___x_2562_; size_t v___x_2563_; size_t v___x_2564_; 
v___x_2561_ = lean_array_uget_borrowed(v_as_2556_, v_i_2557_);
lean_inc_ref(v_f_2555_);
v___x_2562_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(v_f_2555_, v___x_2561_, v_b_2559_);
v___x_2563_ = ((size_t)1ULL);
v___x_2564_ = lean_usize_add(v_i_2557_, v___x_2563_);
v_i_2557_ = v___x_2564_;
v_b_2559_ = v___x_2562_;
goto _start;
}
else
{
lean_dec_ref(v_f_2555_);
return v_b_2559_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1___boxed(lean_object* v_f_2566_, lean_object* v_as_2567_, lean_object* v_i_2568_, lean_object* v_stop_2569_, lean_object* v_b_2570_){
_start:
{
size_t v_i_boxed_2571_; size_t v_stop_boxed_2572_; lean_object* v_res_2573_; 
v_i_boxed_2571_ = lean_unbox_usize(v_i_2568_);
lean_dec(v_i_2568_);
v_stop_boxed_2572_ = lean_unbox_usize(v_stop_2569_);
lean_dec(v_stop_2569_);
v_res_2573_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2566_, v_as_2567_, v_i_boxed_2571_, v_stop_boxed_2572_, v_b_2570_);
lean_dec_ref(v_as_2567_);
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2___boxed(lean_object* v_f_2574_, lean_object* v_x_2575_, lean_object* v_x_2576_){
_start:
{
lean_object* v_res_2577_; 
v_res_2577_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(v_f_2574_, v_x_2575_, v_x_2576_);
lean_dec_ref(v_x_2575_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(lean_object* v_f_2578_, lean_object* v_x_2579_, size_t v_x_2580_, size_t v_x_2581_, lean_object* v_x_2582_){
_start:
{
if (lean_obj_tag(v_x_2579_) == 0)
{
lean_object* v_cs_2583_; lean_object* v___x_2584_; size_t v___x_2585_; lean_object* v_j_2586_; lean_object* v___x_2587_; size_t v___x_2588_; size_t v___x_2589_; size_t v___x_2590_; size_t v___x_2591_; size_t v___x_2592_; size_t v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; uint8_t v___x_2598_; 
v_cs_2583_ = lean_ctor_get(v_x_2579_, 0);
v___x_2584_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0);
v___x_2585_ = lean_usize_shift_right(v_x_2580_, v_x_2581_);
v_j_2586_ = lean_usize_to_nat(v___x_2585_);
v___x_2587_ = lean_array_get_borrowed(v___x_2584_, v_cs_2583_, v_j_2586_);
v___x_2588_ = ((size_t)1ULL);
v___x_2589_ = lean_usize_shift_left(v___x_2588_, v_x_2581_);
v___x_2590_ = lean_usize_sub(v___x_2589_, v___x_2588_);
v___x_2591_ = lean_usize_land(v_x_2580_, v___x_2590_);
v___x_2592_ = ((size_t)5ULL);
v___x_2593_ = lean_usize_sub(v_x_2581_, v___x_2592_);
lean_inc_ref(v_f_2578_);
v___x_2594_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(v_f_2578_, v___x_2587_, v___x_2591_, v___x_2593_, v_x_2582_);
v___x_2595_ = lean_unsigned_to_nat(1u);
v___x_2596_ = lean_nat_add(v_j_2586_, v___x_2595_);
lean_dec(v_j_2586_);
v___x_2597_ = lean_array_get_size(v_cs_2583_);
v___x_2598_ = lean_nat_dec_lt(v___x_2596_, v___x_2597_);
if (v___x_2598_ == 0)
{
lean_dec(v___x_2596_);
lean_dec_ref(v_f_2578_);
return v___x_2594_;
}
else
{
uint8_t v___x_2599_; 
v___x_2599_ = lean_nat_dec_le(v___x_2597_, v___x_2597_);
if (v___x_2599_ == 0)
{
if (v___x_2598_ == 0)
{
lean_dec(v___x_2596_);
lean_dec_ref(v_f_2578_);
return v___x_2594_;
}
else
{
size_t v___x_2600_; size_t v___x_2601_; lean_object* v___x_2602_; 
v___x_2600_ = lean_usize_of_nat(v___x_2596_);
lean_dec(v___x_2596_);
v___x_2601_ = lean_usize_of_nat(v___x_2597_);
v___x_2602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2578_, v_cs_2583_, v___x_2600_, v___x_2601_, v___x_2594_);
return v___x_2602_;
}
}
else
{
size_t v___x_2603_; size_t v___x_2604_; lean_object* v___x_2605_; 
v___x_2603_ = lean_usize_of_nat(v___x_2596_);
lean_dec(v___x_2596_);
v___x_2604_ = lean_usize_of_nat(v___x_2597_);
v___x_2605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2578_, v_cs_2583_, v___x_2603_, v___x_2604_, v___x_2594_);
return v___x_2605_;
}
}
}
else
{
lean_object* v_vs_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; uint8_t v___x_2609_; 
v_vs_2606_ = lean_ctor_get(v_x_2579_, 0);
v___x_2607_ = lean_usize_to_nat(v_x_2580_);
v___x_2608_ = lean_array_get_size(v_vs_2606_);
v___x_2609_ = lean_nat_dec_lt(v___x_2607_, v___x_2608_);
if (v___x_2609_ == 0)
{
lean_dec(v___x_2607_);
lean_dec_ref(v_f_2578_);
return v_x_2582_;
}
else
{
uint8_t v___x_2610_; 
v___x_2610_ = lean_nat_dec_le(v___x_2608_, v___x_2608_);
if (v___x_2610_ == 0)
{
if (v___x_2609_ == 0)
{
lean_dec(v___x_2607_);
lean_dec_ref(v_f_2578_);
return v_x_2582_;
}
else
{
size_t v___x_2611_; size_t v___x_2612_; lean_object* v___x_2613_; 
v___x_2611_ = lean_usize_of_nat(v___x_2607_);
lean_dec(v___x_2607_);
v___x_2612_ = lean_usize_of_nat(v___x_2608_);
v___x_2613_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2578_, v_vs_2606_, v___x_2611_, v___x_2612_, v_x_2582_);
return v___x_2613_;
}
}
else
{
size_t v___x_2614_; size_t v___x_2615_; lean_object* v___x_2616_; 
v___x_2614_ = lean_usize_of_nat(v___x_2607_);
lean_dec(v___x_2607_);
v___x_2615_ = lean_usize_of_nat(v___x_2608_);
v___x_2616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2578_, v_vs_2606_, v___x_2614_, v___x_2615_, v_x_2582_);
return v___x_2616_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0___boxed(lean_object* v_f_2617_, lean_object* v_x_2618_, lean_object* v_x_2619_, lean_object* v_x_2620_, lean_object* v_x_2621_){
_start:
{
size_t v_x_1859__boxed_2622_; size_t v_x_1860__boxed_2623_; lean_object* v_res_2624_; 
v_x_1859__boxed_2622_ = lean_unbox_usize(v_x_2619_);
lean_dec(v_x_2619_);
v_x_1860__boxed_2623_ = lean_unbox_usize(v_x_2620_);
lean_dec(v_x_2620_);
v_res_2624_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(v_f_2617_, v_x_2618_, v_x_1859__boxed_2622_, v_x_1860__boxed_2623_, v_x_2621_);
lean_dec_ref(v_x_2618_);
return v_res_2624_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0(lean_object* v_f_2625_, lean_object* v_t_2626_, lean_object* v_init_2627_, lean_object* v_start_2628_){
_start:
{
lean_object* v___x_2629_; uint8_t v___x_2630_; 
v___x_2629_ = lean_unsigned_to_nat(0u);
v___x_2630_ = lean_nat_dec_eq(v_start_2628_, v___x_2629_);
if (v___x_2630_ == 0)
{
lean_object* v_root_2631_; lean_object* v_tail_2632_; size_t v_shift_2633_; lean_object* v_tailOff_2634_; uint8_t v___x_2635_; 
v_root_2631_ = lean_ctor_get(v_t_2626_, 0);
v_tail_2632_ = lean_ctor_get(v_t_2626_, 1);
v_shift_2633_ = lean_ctor_get_usize(v_t_2626_, 4);
v_tailOff_2634_ = lean_ctor_get(v_t_2626_, 3);
v___x_2635_ = lean_nat_dec_le(v_tailOff_2634_, v_start_2628_);
if (v___x_2635_ == 0)
{
size_t v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; uint8_t v___x_2639_; 
v___x_2636_ = lean_usize_of_nat(v_start_2628_);
lean_inc_ref(v_f_2625_);
v___x_2637_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(v_f_2625_, v_root_2631_, v___x_2636_, v_shift_2633_, v_init_2627_);
v___x_2638_ = lean_array_get_size(v_tail_2632_);
v___x_2639_ = lean_nat_dec_lt(v___x_2629_, v___x_2638_);
if (v___x_2639_ == 0)
{
lean_dec_ref(v_f_2625_);
return v___x_2637_;
}
else
{
uint8_t v___x_2640_; 
v___x_2640_ = lean_nat_dec_le(v___x_2638_, v___x_2638_);
if (v___x_2640_ == 0)
{
if (v___x_2639_ == 0)
{
lean_dec_ref(v_f_2625_);
return v___x_2637_;
}
else
{
size_t v___x_2641_; size_t v___x_2642_; lean_object* v___x_2643_; 
v___x_2641_ = ((size_t)0ULL);
v___x_2642_ = lean_usize_of_nat(v___x_2638_);
v___x_2643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2625_, v_tail_2632_, v___x_2641_, v___x_2642_, v___x_2637_);
return v___x_2643_;
}
}
else
{
size_t v___x_2644_; size_t v___x_2645_; lean_object* v___x_2646_; 
v___x_2644_ = ((size_t)0ULL);
v___x_2645_ = lean_usize_of_nat(v___x_2638_);
v___x_2646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2625_, v_tail_2632_, v___x_2644_, v___x_2645_, v___x_2637_);
return v___x_2646_;
}
}
}
else
{
lean_object* v___x_2647_; lean_object* v___x_2648_; uint8_t v___x_2649_; 
v___x_2647_ = lean_nat_sub(v_start_2628_, v_tailOff_2634_);
v___x_2648_ = lean_array_get_size(v_tail_2632_);
v___x_2649_ = lean_nat_dec_lt(v___x_2647_, v___x_2648_);
if (v___x_2649_ == 0)
{
lean_dec(v___x_2647_);
lean_dec_ref(v_f_2625_);
return v_init_2627_;
}
else
{
uint8_t v___x_2650_; 
v___x_2650_ = lean_nat_dec_le(v___x_2648_, v___x_2648_);
if (v___x_2650_ == 0)
{
if (v___x_2649_ == 0)
{
lean_dec(v___x_2647_);
lean_dec_ref(v_f_2625_);
return v_init_2627_;
}
else
{
size_t v___x_2651_; size_t v___x_2652_; lean_object* v___x_2653_; 
v___x_2651_ = lean_usize_of_nat(v___x_2647_);
lean_dec(v___x_2647_);
v___x_2652_ = lean_usize_of_nat(v___x_2648_);
v___x_2653_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2625_, v_tail_2632_, v___x_2651_, v___x_2652_, v_init_2627_);
return v___x_2653_;
}
}
else
{
size_t v___x_2654_; size_t v___x_2655_; lean_object* v___x_2656_; 
v___x_2654_ = lean_usize_of_nat(v___x_2647_);
lean_dec(v___x_2647_);
v___x_2655_ = lean_usize_of_nat(v___x_2648_);
v___x_2656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2625_, v_tail_2632_, v___x_2654_, v___x_2655_, v_init_2627_);
return v___x_2656_;
}
}
}
}
else
{
lean_object* v_root_2657_; lean_object* v_tail_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; uint8_t v___x_2661_; 
v_root_2657_ = lean_ctor_get(v_t_2626_, 0);
v_tail_2658_ = lean_ctor_get(v_t_2626_, 1);
lean_inc_ref(v_f_2625_);
v___x_2659_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(v_f_2625_, v_root_2657_, v_init_2627_);
v___x_2660_ = lean_array_get_size(v_tail_2658_);
v___x_2661_ = lean_nat_dec_lt(v___x_2629_, v___x_2660_);
if (v___x_2661_ == 0)
{
lean_dec_ref(v_f_2625_);
return v___x_2659_;
}
else
{
uint8_t v___x_2662_; 
v___x_2662_ = lean_nat_dec_le(v___x_2660_, v___x_2660_);
if (v___x_2662_ == 0)
{
if (v___x_2661_ == 0)
{
lean_dec_ref(v_f_2625_);
return v___x_2659_;
}
else
{
size_t v___x_2663_; size_t v___x_2664_; lean_object* v___x_2665_; 
v___x_2663_ = ((size_t)0ULL);
v___x_2664_ = lean_usize_of_nat(v___x_2660_);
v___x_2665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2625_, v_tail_2658_, v___x_2663_, v___x_2664_, v___x_2659_);
return v___x_2665_;
}
}
else
{
size_t v___x_2666_; size_t v___x_2667_; lean_object* v___x_2668_; 
v___x_2666_ = ((size_t)0ULL);
v___x_2667_ = lean_usize_of_nat(v___x_2660_);
v___x_2668_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2625_, v_tail_2658_, v___x_2666_, v___x_2667_, v___x_2659_);
return v___x_2668_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0___boxed(lean_object* v_f_2669_, lean_object* v_t_2670_, lean_object* v_init_2671_, lean_object* v_start_2672_){
_start:
{
lean_object* v_res_2673_; 
v_res_2673_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0(v_f_2669_, v_t_2670_, v_init_2671_, v_start_2672_);
lean_dec(v_start_2672_);
lean_dec_ref(v_t_2670_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_modifyLocalDecls(lean_object* v_lctx_2674_, lean_object* v_f_2675_){
_start:
{
lean_object* v_decls_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
v_decls_2676_ = lean_ctor_get(v_lctx_2674_, 1);
lean_inc_ref(v_decls_2676_);
v___x_2677_ = lean_unsigned_to_nat(0u);
v___x_2678_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0(v_f_2675_, v_decls_2676_, v_lctx_2674_, v___x_2677_);
lean_dec_ref(v_decls_2676_);
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setKind(lean_object* v_lctx_2679_, lean_object* v_fvarId_2680_, uint8_t v_kind_2681_){
_start:
{
lean_object* v_fvarIdToDecl_2682_; lean_object* v_decls_2683_; lean_object* v_auxDeclToFullName_2684_; lean_object* v___x_2685_; 
v_fvarIdToDecl_2682_ = lean_ctor_get(v_lctx_2679_, 0);
v_decls_2683_ = lean_ctor_get(v_lctx_2679_, 1);
v_auxDeclToFullName_2684_ = lean_ctor_get(v_lctx_2679_, 2);
lean_inc_ref(v_lctx_2679_);
v___x_2685_ = lean_local_ctx_find(v_lctx_2679_, v_fvarId_2680_);
if (lean_obj_tag(v___x_2685_) == 0)
{
return v_lctx_2679_;
}
else
{
lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2710_; 
lean_inc(v_auxDeclToFullName_2684_);
lean_inc_ref(v_decls_2683_);
lean_inc_ref(v_fvarIdToDecl_2682_);
v_isSharedCheck_2710_ = !lean_is_exclusive(v_lctx_2679_);
if (v_isSharedCheck_2710_ == 0)
{
lean_object* v_unused_2711_; lean_object* v_unused_2712_; lean_object* v_unused_2713_; 
v_unused_2711_ = lean_ctor_get(v_lctx_2679_, 2);
lean_dec(v_unused_2711_);
v_unused_2712_ = lean_ctor_get(v_lctx_2679_, 1);
lean_dec(v_unused_2712_);
v_unused_2713_ = lean_ctor_get(v_lctx_2679_, 0);
lean_dec(v_unused_2713_);
v___x_2687_ = v_lctx_2679_;
v_isShared_2688_ = v_isSharedCheck_2710_;
goto v_resetjp_2686_;
}
else
{
lean_dec(v_lctx_2679_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2710_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v_val_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2709_; 
v_val_2689_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2691_ = v___x_2685_;
v_isShared_2692_ = v_isSharedCheck_2709_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_val_2689_);
lean_dec(v___x_2685_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2709_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v_decl_2693_; lean_object* v___y_2695_; lean_object* v___y_2696_; lean_object* v___y_2705_; lean_object* v_fvarId_2708_; 
v_decl_2693_ = l_Lean_LocalDecl_setKind(v_val_2689_, v_kind_2681_);
v_fvarId_2708_ = lean_ctor_get(v_decl_2693_, 1);
lean_inc(v_fvarId_2708_);
v___y_2705_ = v_fvarId_2708_;
goto v___jp_2704_;
v___jp_2694_:
{
lean_object* v___x_2698_; 
if (v_isShared_2692_ == 0)
{
lean_ctor_set(v___x_2691_, 0, v_decl_2693_);
v___x_2698_ = v___x_2691_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_decl_2693_);
v___x_2698_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
lean_object* v___x_2699_; lean_object* v___x_2701_; 
v___x_2699_ = l_Lean_PersistentArray_set___redArg(v_decls_2683_, v___y_2696_, v___x_2698_);
lean_dec(v___y_2696_);
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 1, v___x_2699_);
lean_ctor_set(v___x_2687_, 0, v___y_2695_);
v___x_2701_ = v___x_2687_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v___y_2695_);
lean_ctor_set(v_reuseFailAlloc_2702_, 1, v___x_2699_);
lean_ctor_set(v_reuseFailAlloc_2702_, 2, v_auxDeclToFullName_2684_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
v___jp_2704_:
{
lean_object* v___x_2706_; lean_object* v_index_2707_; 
lean_inc_ref(v_decl_2693_);
v___x_2706_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2682_, v___y_2705_, v_decl_2693_);
v_index_2707_ = lean_ctor_get(v_decl_2693_, 0);
lean_inc(v_index_2707_);
v___y_2695_ = v___x_2706_;
v___y_2696_ = v_index_2707_;
goto v___jp_2694_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setKind___boxed(lean_object* v_lctx_2714_, lean_object* v_fvarId_2715_, lean_object* v_kind_2716_){
_start:
{
uint8_t v_kind_boxed_2717_; lean_object* v_res_2718_; 
v_kind_boxed_2717_ = lean_unbox(v_kind_2716_);
v_res_2718_ = l_Lean_LocalContext_setKind(v_lctx_2714_, v_fvarId_2715_, v_kind_boxed_2717_);
return v_res_2718_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setBinderInfo(lean_object* v_lctx_2719_, lean_object* v_fvarId_2720_, uint8_t v_bi_2721_){
_start:
{
lean_object* v_fvarIdToDecl_2722_; lean_object* v_decls_2723_; lean_object* v_auxDeclToFullName_2724_; lean_object* v___x_2725_; 
v_fvarIdToDecl_2722_ = lean_ctor_get(v_lctx_2719_, 0);
v_decls_2723_ = lean_ctor_get(v_lctx_2719_, 1);
v_auxDeclToFullName_2724_ = lean_ctor_get(v_lctx_2719_, 2);
lean_inc_ref(v_lctx_2719_);
v___x_2725_ = lean_local_ctx_find(v_lctx_2719_, v_fvarId_2720_);
if (lean_obj_tag(v___x_2725_) == 0)
{
return v_lctx_2719_;
}
else
{
lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2750_; 
lean_inc(v_auxDeclToFullName_2724_);
lean_inc_ref(v_decls_2723_);
lean_inc_ref(v_fvarIdToDecl_2722_);
v_isSharedCheck_2750_ = !lean_is_exclusive(v_lctx_2719_);
if (v_isSharedCheck_2750_ == 0)
{
lean_object* v_unused_2751_; lean_object* v_unused_2752_; lean_object* v_unused_2753_; 
v_unused_2751_ = lean_ctor_get(v_lctx_2719_, 2);
lean_dec(v_unused_2751_);
v_unused_2752_ = lean_ctor_get(v_lctx_2719_, 1);
lean_dec(v_unused_2752_);
v_unused_2753_ = lean_ctor_get(v_lctx_2719_, 0);
lean_dec(v_unused_2753_);
v___x_2727_ = v_lctx_2719_;
v_isShared_2728_ = v_isSharedCheck_2750_;
goto v_resetjp_2726_;
}
else
{
lean_dec(v_lctx_2719_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2750_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v_val_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2749_; 
v_val_2729_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2731_ = v___x_2725_;
v_isShared_2732_ = v_isSharedCheck_2749_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_val_2729_);
lean_dec(v___x_2725_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2749_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
lean_object* v_decl_2733_; lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v___y_2745_; lean_object* v_fvarId_2748_; 
v_decl_2733_ = l_Lean_LocalDecl_setBinderInfo(v_val_2729_, v_bi_2721_);
v_fvarId_2748_ = lean_ctor_get(v_decl_2733_, 1);
lean_inc(v_fvarId_2748_);
v___y_2745_ = v_fvarId_2748_;
goto v___jp_2744_;
v___jp_2734_:
{
lean_object* v___x_2738_; 
if (v_isShared_2732_ == 0)
{
lean_ctor_set(v___x_2731_, 0, v_decl_2733_);
v___x_2738_ = v___x_2731_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_decl_2733_);
v___x_2738_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
lean_object* v___x_2739_; lean_object* v___x_2741_; 
v___x_2739_ = l_Lean_PersistentArray_set___redArg(v_decls_2723_, v___y_2736_, v___x_2738_);
lean_dec(v___y_2736_);
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 1, v___x_2739_);
lean_ctor_set(v___x_2727_, 0, v___y_2735_);
v___x_2741_ = v___x_2727_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v___y_2735_);
lean_ctor_set(v_reuseFailAlloc_2742_, 1, v___x_2739_);
lean_ctor_set(v_reuseFailAlloc_2742_, 2, v_auxDeclToFullName_2724_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
return v___x_2741_;
}
}
}
v___jp_2744_:
{
lean_object* v___x_2746_; lean_object* v_index_2747_; 
lean_inc_ref(v_decl_2733_);
v___x_2746_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2722_, v___y_2745_, v_decl_2733_);
v_index_2747_ = lean_ctor_get(v_decl_2733_, 0);
lean_inc(v_index_2747_);
v___y_2735_ = v___x_2746_;
v___y_2736_ = v_index_2747_;
goto v___jp_2734_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setBinderInfo___boxed(lean_object* v_lctx_2754_, lean_object* v_fvarId_2755_, lean_object* v_bi_2756_){
_start:
{
uint8_t v_bi_boxed_2757_; lean_object* v_res_2758_; 
v_bi_boxed_2757_ = lean_unbox(v_bi_2756_);
v_res_2758_ = l_Lean_LocalContext_setBinderInfo(v_lctx_2754_, v_fvarId_2755_, v_bi_boxed_2757_);
return v_res_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setType(lean_object* v_lctx_2759_, lean_object* v_fvarId_2760_, lean_object* v_type_2761_){
_start:
{
lean_object* v_fvarIdToDecl_2762_; lean_object* v_decls_2763_; lean_object* v_auxDeclToFullName_2764_; lean_object* v___x_2765_; 
v_fvarIdToDecl_2762_ = lean_ctor_get(v_lctx_2759_, 0);
v_decls_2763_ = lean_ctor_get(v_lctx_2759_, 1);
v_auxDeclToFullName_2764_ = lean_ctor_get(v_lctx_2759_, 2);
lean_inc_ref(v_lctx_2759_);
v___x_2765_ = lean_local_ctx_find(v_lctx_2759_, v_fvarId_2760_);
if (lean_obj_tag(v___x_2765_) == 0)
{
lean_dec_ref(v_type_2761_);
return v_lctx_2759_;
}
else
{
lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2790_; 
lean_inc(v_auxDeclToFullName_2764_);
lean_inc_ref(v_decls_2763_);
lean_inc_ref(v_fvarIdToDecl_2762_);
v_isSharedCheck_2790_ = !lean_is_exclusive(v_lctx_2759_);
if (v_isSharedCheck_2790_ == 0)
{
lean_object* v_unused_2791_; lean_object* v_unused_2792_; lean_object* v_unused_2793_; 
v_unused_2791_ = lean_ctor_get(v_lctx_2759_, 2);
lean_dec(v_unused_2791_);
v_unused_2792_ = lean_ctor_get(v_lctx_2759_, 1);
lean_dec(v_unused_2792_);
v_unused_2793_ = lean_ctor_get(v_lctx_2759_, 0);
lean_dec(v_unused_2793_);
v___x_2767_ = v_lctx_2759_;
v_isShared_2768_ = v_isSharedCheck_2790_;
goto v_resetjp_2766_;
}
else
{
lean_dec(v_lctx_2759_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2790_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v_val_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2789_; 
v_val_2769_ = lean_ctor_get(v___x_2765_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2771_ = v___x_2765_;
v_isShared_2772_ = v_isSharedCheck_2789_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_val_2769_);
lean_dec(v___x_2765_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2789_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v_decl_2773_; lean_object* v___y_2775_; lean_object* v___y_2776_; lean_object* v___y_2785_; lean_object* v_fvarId_2788_; 
v_decl_2773_ = l_Lean_LocalDecl_setType(v_val_2769_, v_type_2761_);
v_fvarId_2788_ = lean_ctor_get(v_decl_2773_, 1);
lean_inc(v_fvarId_2788_);
v___y_2785_ = v_fvarId_2788_;
goto v___jp_2784_;
v___jp_2774_:
{
lean_object* v___x_2778_; 
if (v_isShared_2772_ == 0)
{
lean_ctor_set(v___x_2771_, 0, v_decl_2773_);
v___x_2778_ = v___x_2771_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_decl_2773_);
v___x_2778_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
lean_object* v___x_2779_; lean_object* v___x_2781_; 
v___x_2779_ = l_Lean_PersistentArray_set___redArg(v_decls_2763_, v___y_2776_, v___x_2778_);
lean_dec(v___y_2776_);
if (v_isShared_2768_ == 0)
{
lean_ctor_set(v___x_2767_, 1, v___x_2779_);
lean_ctor_set(v___x_2767_, 0, v___y_2775_);
v___x_2781_ = v___x_2767_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v___y_2775_);
lean_ctor_set(v_reuseFailAlloc_2782_, 1, v___x_2779_);
lean_ctor_set(v_reuseFailAlloc_2782_, 2, v_auxDeclToFullName_2764_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
v___jp_2784_:
{
lean_object* v___x_2786_; lean_object* v_index_2787_; 
lean_inc_ref(v_decl_2773_);
v___x_2786_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2762_, v___y_2785_, v_decl_2773_);
v_index_2787_ = lean_ctor_get(v_decl_2773_, 0);
lean_inc(v_index_2787_);
v___y_2775_ = v___x_2786_;
v___y_2776_ = v_index_2787_;
goto v___jp_2774_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lean_local_ctx_num_indices(lean_object* v_lctx_2794_){
_start:
{
lean_object* v_decls_2795_; lean_object* v_size_2796_; 
v_decls_2795_ = lean_ctor_get(v_lctx_2794_, 1);
lean_inc_ref(v_decls_2795_);
lean_dec_ref(v_lctx_2794_);
v_size_2796_ = lean_ctor_get(v_decls_2795_, 2);
lean_inc(v_size_2796_);
lean_dec_ref(v_decls_2795_);
return v_size_2796_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getAt_x3f(lean_object* v_lctx_2797_, lean_object* v_i_2798_){
_start:
{
lean_object* v_decls_2799_; lean_object* v_size_2800_; lean_object* v___x_2801_; uint8_t v___x_2802_; 
v_decls_2799_ = lean_ctor_get(v_lctx_2797_, 1);
v_size_2800_ = lean_ctor_get(v_decls_2799_, 2);
v___x_2801_ = lean_box(0);
v___x_2802_ = lean_nat_dec_lt(v_i_2798_, v_size_2800_);
if (v___x_2802_ == 0)
{
lean_object* v___x_2803_; 
v___x_2803_ = l_outOfBounds___redArg(v___x_2801_);
return v___x_2803_;
}
else
{
lean_object* v___x_2804_; 
v___x_2804_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2801_, v_decls_2799_, v_i_2798_);
return v___x_2804_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getAt_x3f___boxed(lean_object* v_lctx_2805_, lean_object* v_i_2806_){
_start:
{
lean_object* v_res_2807_; 
v_res_2807_ = l_Lean_LocalContext_getAt_x3f(v_lctx_2805_, v_i_2806_);
lean_dec(v_i_2806_);
lean_dec_ref(v_lctx_2805_);
return v_res_2807_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg___lam__0(lean_object* v_toPure_2808_, lean_object* v_f_2809_, lean_object* v_b_2810_, lean_object* v_decl_2811_){
_start:
{
if (lean_obj_tag(v_decl_2811_) == 0)
{
lean_object* v___x_2812_; 
lean_dec(v_f_2809_);
v___x_2812_ = lean_apply_2(v_toPure_2808_, lean_box(0), v_b_2810_);
return v___x_2812_;
}
else
{
lean_object* v_val_2813_; lean_object* v___x_2814_; 
lean_dec(v_toPure_2808_);
v_val_2813_ = lean_ctor_get(v_decl_2811_, 0);
lean_inc(v_val_2813_);
lean_dec_ref_known(v_decl_2811_, 1);
v___x_2814_ = lean_apply_2(v_f_2809_, v_b_2810_, v_val_2813_);
return v___x_2814_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg(lean_object* v_inst_2815_, lean_object* v_lctx_2816_, lean_object* v_f_2817_, lean_object* v_init_2818_, lean_object* v_start_2819_){
_start:
{
lean_object* v_toApplicative_2820_; lean_object* v_decls_2821_; lean_object* v_toPure_2822_; lean_object* v___f_2823_; lean_object* v___x_2824_; 
v_toApplicative_2820_ = lean_ctor_get(v_inst_2815_, 0);
v_decls_2821_ = lean_ctor_get(v_lctx_2816_, 1);
lean_inc_ref(v_decls_2821_);
lean_dec_ref(v_lctx_2816_);
v_toPure_2822_ = lean_ctor_get(v_toApplicative_2820_, 1);
lean_inc(v_toPure_2822_);
v___f_2823_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldlM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2823_, 0, v_toPure_2822_);
lean_closure_set(v___f_2823_, 1, v_f_2817_);
v___x_2824_ = l_Lean_PersistentArray_foldlM___redArg(v_inst_2815_, v_decls_2821_, v___f_2823_, v_init_2818_, v_start_2819_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg___boxed(lean_object* v_inst_2825_, lean_object* v_lctx_2826_, lean_object* v_f_2827_, lean_object* v_init_2828_, lean_object* v_start_2829_){
_start:
{
lean_object* v_res_2830_; 
v_res_2830_ = l_Lean_LocalContext_foldlM___redArg(v_inst_2825_, v_lctx_2826_, v_f_2827_, v_init_2828_, v_start_2829_);
lean_dec(v_start_2829_);
return v_res_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM(lean_object* v_m_2831_, lean_object* v_00_u03b2_2832_, lean_object* v_inst_2833_, lean_object* v_lctx_2834_, lean_object* v_f_2835_, lean_object* v_init_2836_, lean_object* v_start_2837_){
_start:
{
lean_object* v___x_2838_; 
v___x_2838_ = l_Lean_LocalContext_foldlM___redArg(v_inst_2833_, v_lctx_2834_, v_f_2835_, v_init_2836_, v_start_2837_);
return v___x_2838_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___boxed(lean_object* v_m_2839_, lean_object* v_00_u03b2_2840_, lean_object* v_inst_2841_, lean_object* v_lctx_2842_, lean_object* v_f_2843_, lean_object* v_init_2844_, lean_object* v_start_2845_){
_start:
{
lean_object* v_res_2846_; 
v_res_2846_ = l_Lean_LocalContext_foldlM(v_m_2839_, v_00_u03b2_2840_, v_inst_2841_, v_lctx_2842_, v_f_2843_, v_init_2844_, v_start_2845_);
lean_dec(v_start_2845_);
return v_res_2846_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___redArg___lam__0(lean_object* v_toPure_2847_, lean_object* v_f_2848_, lean_object* v_decl_2849_, lean_object* v_b_2850_){
_start:
{
if (lean_obj_tag(v_decl_2849_) == 0)
{
lean_object* v___x_2851_; 
lean_dec(v_f_2848_);
v___x_2851_ = lean_apply_2(v_toPure_2847_, lean_box(0), v_b_2850_);
return v___x_2851_;
}
else
{
lean_object* v_val_2852_; lean_object* v___x_2853_; 
lean_dec(v_toPure_2847_);
v_val_2852_ = lean_ctor_get(v_decl_2849_, 0);
lean_inc(v_val_2852_);
lean_dec_ref_known(v_decl_2849_, 1);
v___x_2853_ = lean_apply_2(v_f_2848_, v_val_2852_, v_b_2850_);
return v___x_2853_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___redArg(lean_object* v_inst_2854_, lean_object* v_lctx_2855_, lean_object* v_f_2856_, lean_object* v_init_2857_){
_start:
{
lean_object* v_toApplicative_2858_; lean_object* v_decls_2859_; lean_object* v_toPure_2860_; lean_object* v___f_2861_; lean_object* v___x_2862_; 
v_toApplicative_2858_ = lean_ctor_get(v_inst_2854_, 0);
v_decls_2859_ = lean_ctor_get(v_lctx_2855_, 1);
lean_inc_ref(v_decls_2859_);
lean_dec_ref(v_lctx_2855_);
v_toPure_2860_ = lean_ctor_get(v_toApplicative_2858_, 1);
lean_inc(v_toPure_2860_);
v___f_2861_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldrM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2861_, 0, v_toPure_2860_);
lean_closure_set(v___f_2861_, 1, v_f_2856_);
v___x_2862_ = l_Lean_PersistentArray_foldrM___redArg(v_inst_2854_, v_decls_2859_, v___f_2861_, v_init_2857_);
return v___x_2862_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM(lean_object* v_m_2863_, lean_object* v_00_u03b2_2864_, lean_object* v_inst_2865_, lean_object* v_lctx_2866_, lean_object* v_f_2867_, lean_object* v_init_2868_){
_start:
{
lean_object* v___x_2869_; 
v___x_2869_ = l_Lean_LocalContext_foldrM___redArg(v_inst_2865_, v_lctx_2866_, v_f_2867_, v_init_2868_);
return v___x_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg___lam__0(lean_object* v_toPure_2870_, lean_object* v_f_2871_, lean_object* v_decl_2872_){
_start:
{
if (lean_obj_tag(v_decl_2872_) == 0)
{
lean_object* v___x_2873_; lean_object* v___x_2874_; 
lean_dec(v_f_2871_);
v___x_2873_ = lean_box(0);
v___x_2874_ = lean_apply_2(v_toPure_2870_, lean_box(0), v___x_2873_);
return v___x_2874_;
}
else
{
lean_object* v_val_2875_; lean_object* v___x_2876_; 
lean_dec(v_toPure_2870_);
v_val_2875_ = lean_ctor_get(v_decl_2872_, 0);
lean_inc(v_val_2875_);
lean_dec_ref_known(v_decl_2872_, 1);
v___x_2876_ = lean_apply_1(v_f_2871_, v_val_2875_);
return v___x_2876_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg(lean_object* v_inst_2877_, lean_object* v_lctx_2878_, lean_object* v_f_2879_, lean_object* v_start_2880_){
_start:
{
lean_object* v_toApplicative_2881_; lean_object* v_decls_2882_; lean_object* v_toPure_2883_; lean_object* v___f_2884_; lean_object* v___x_2885_; 
v_toApplicative_2881_ = lean_ctor_get(v_inst_2877_, 0);
v_decls_2882_ = lean_ctor_get(v_lctx_2878_, 1);
lean_inc_ref(v_decls_2882_);
lean_dec_ref(v_lctx_2878_);
v_toPure_2883_ = lean_ctor_get(v_toApplicative_2881_, 1);
lean_inc(v_toPure_2883_);
v___f_2884_ = lean_alloc_closure((void*)(l_Lean_LocalContext_forM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2884_, 0, v_toPure_2883_);
lean_closure_set(v___f_2884_, 1, v_f_2879_);
v___x_2885_ = l_Lean_PersistentArray_forM___redArg(v_inst_2877_, v_decls_2882_, v___f_2884_, v_start_2880_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg___boxed(lean_object* v_inst_2886_, lean_object* v_lctx_2887_, lean_object* v_f_2888_, lean_object* v_start_2889_){
_start:
{
lean_object* v_res_2890_; 
v_res_2890_ = l_Lean_LocalContext_forM___redArg(v_inst_2886_, v_lctx_2887_, v_f_2888_, v_start_2889_);
lean_dec(v_start_2889_);
return v_res_2890_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM(lean_object* v_m_2891_, lean_object* v_inst_2892_, lean_object* v_lctx_2893_, lean_object* v_f_2894_, lean_object* v_start_2895_){
_start:
{
lean_object* v___x_2896_; 
v___x_2896_ = l_Lean_LocalContext_forM___redArg(v_inst_2892_, v_lctx_2893_, v_f_2894_, v_start_2895_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___boxed(lean_object* v_m_2897_, lean_object* v_inst_2898_, lean_object* v_lctx_2899_, lean_object* v_f_2900_, lean_object* v_start_2901_){
_start:
{
lean_object* v_res_2902_; 
v_res_2902_ = l_Lean_LocalContext_forM(v_m_2897_, v_inst_2898_, v_lctx_2899_, v_f_2900_, v_start_2901_);
lean_dec(v_start_2901_);
return v_res_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0(lean_object* v_toPure_2903_, lean_object* v_f_2904_, lean_object* v_decl_2905_){
_start:
{
if (lean_obj_tag(v_decl_2905_) == 0)
{
lean_object* v___x_2906_; lean_object* v___x_2907_; 
lean_dec(v_f_2904_);
v___x_2906_ = lean_box(0);
v___x_2907_ = lean_apply_2(v_toPure_2903_, lean_box(0), v___x_2906_);
return v___x_2907_;
}
else
{
lean_object* v_val_2908_; lean_object* v___x_2909_; 
lean_dec(v_toPure_2903_);
v_val_2908_ = lean_ctor_get(v_decl_2905_, 0);
lean_inc(v_val_2908_);
lean_dec_ref_known(v_decl_2905_, 1);
v___x_2909_ = lean_apply_1(v_f_2904_, v_val_2908_);
return v___x_2909_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___redArg(lean_object* v_inst_2910_, lean_object* v_lctx_2911_, lean_object* v_f_2912_){
_start:
{
lean_object* v_toApplicative_2913_; lean_object* v_decls_2914_; lean_object* v_toPure_2915_; lean_object* v___f_2916_; lean_object* v___x_2917_; 
v_toApplicative_2913_ = lean_ctor_get(v_inst_2910_, 0);
v_decls_2914_ = lean_ctor_get(v_lctx_2911_, 1);
lean_inc_ref(v_decls_2914_);
lean_dec_ref(v_lctx_2911_);
v_toPure_2915_ = lean_ctor_get(v_toApplicative_2913_, 1);
lean_inc(v_toPure_2915_);
v___f_2916_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2916_, 0, v_toPure_2915_);
lean_closure_set(v___f_2916_, 1, v_f_2912_);
v___x_2917_ = l_Lean_PersistentArray_findSomeM_x3f___redArg(v_inst_2910_, v_decls_2914_, v___f_2916_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f(lean_object* v_m_2918_, lean_object* v_00_u03b2_2919_, lean_object* v_inst_2920_, lean_object* v_lctx_2921_, lean_object* v_f_2922_){
_start:
{
lean_object* v___x_2923_; 
v___x_2923_ = l_Lean_LocalContext_findDeclM_x3f___redArg(v_inst_2920_, v_lctx_2921_, v_f_2922_);
return v___x_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___redArg(lean_object* v_inst_2924_, lean_object* v_lctx_2925_, lean_object* v_f_2926_){
_start:
{
lean_object* v_toApplicative_2927_; lean_object* v_decls_2928_; lean_object* v_toPure_2929_; lean_object* v___f_2930_; lean_object* v___x_2931_; 
v_toApplicative_2927_ = lean_ctor_get(v_inst_2924_, 0);
v_decls_2928_ = lean_ctor_get(v_lctx_2925_, 1);
lean_inc_ref(v_decls_2928_);
lean_dec_ref(v_lctx_2925_);
v_toPure_2929_ = lean_ctor_get(v_toApplicative_2927_, 1);
lean_inc(v_toPure_2929_);
v___f_2930_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2930_, 0, v_toPure_2929_);
lean_closure_set(v___f_2930_, 1, v_f_2926_);
v___x_2931_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v_inst_2924_, v_decls_2928_, v___f_2930_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f(lean_object* v_m_2932_, lean_object* v_00_u03b2_2933_, lean_object* v_inst_2934_, lean_object* v_lctx_2935_, lean_object* v_f_2936_){
_start:
{
lean_object* v___x_2937_; 
v___x_2937_ = l_Lean_LocalContext_findDeclRevM_x3f___redArg(v_inst_2934_, v_lctx_2935_, v_f_2936_);
return v___x_2937_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__0(lean_object* v_toPure_2938_, lean_object* v_f_2939_, lean_object* v_d_x3f_2940_, lean_object* v_b_2941_){
_start:
{
if (lean_obj_tag(v_d_x3f_2940_) == 0)
{
lean_object* v___x_2942_; lean_object* v___x_2943_; 
lean_dec(v_f_2939_);
v___x_2942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2942_, 0, v_b_2941_);
v___x_2943_ = lean_apply_2(v_toPure_2938_, lean_box(0), v___x_2942_);
return v___x_2943_;
}
else
{
lean_object* v_val_2944_; lean_object* v___x_2945_; 
lean_dec(v_toPure_2938_);
v_val_2944_ = lean_ctor_get(v_d_x3f_2940_, 0);
lean_inc(v_val_2944_);
lean_dec_ref_known(v_d_x3f_2940_, 1);
v___x_2945_ = lean_apply_2(v_f_2939_, v_val_2944_, v_b_2941_);
return v___x_2945_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1(lean_object* v_toPure_2946_, lean_object* v_inst_2947_, lean_object* v_00_u03b2_2948_, lean_object* v_lctx_2949_, lean_object* v_init_2950_, lean_object* v_f_2951_){
_start:
{
lean_object* v_decls_2952_; lean_object* v___f_2953_; lean_object* v___x_2954_; 
v_decls_2952_ = lean_ctor_get(v_lctx_2949_, 1);
v___f_2953_ = lean_alloc_closure((void*)(l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2953_, 0, v_toPure_2946_);
lean_closure_set(v___f_2953_, 1, v_f_2951_);
v___x_2954_ = l_Lean_PersistentArray_forIn___redArg(v_inst_2947_, v_decls_2952_, v_init_2950_, v___f_2953_);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1___boxed(lean_object* v_toPure_2955_, lean_object* v_inst_2956_, lean_object* v_00_u03b2_2957_, lean_object* v_lctx_2958_, lean_object* v_init_2959_, lean_object* v_f_2960_){
_start:
{
lean_object* v_res_2961_; 
v_res_2961_ = l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1(v_toPure_2955_, v_inst_2956_, v_00_u03b2_2957_, v_lctx_2958_, v_init_2959_, v_f_2960_);
lean_dec_ref(v_lctx_2958_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg(lean_object* v_inst_2962_){
_start:
{
lean_object* v_toApplicative_2963_; lean_object* v_toPure_2964_; lean_object* v___f_2965_; 
v_toApplicative_2963_ = lean_ctor_get(v_inst_2962_, 0);
v_toPure_2964_ = lean_ctor_get(v_toApplicative_2963_, 1);
lean_inc(v_toPure_2964_);
v___f_2965_ = lean_alloc_closure((void*)(l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1___boxed), 6, 2);
lean_closure_set(v___f_2965_, 0, v_toPure_2964_);
lean_closure_set(v___f_2965_, 1, v_inst_2962_);
return v___f_2965_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad(lean_object* v_m_2966_, lean_object* v_inst_2967_){
_start:
{
lean_object* v___x_2968_; 
v___x_2968_ = l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg(v_inst_2967_);
return v___x_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg___lam__0(lean_object* v_f_2969_, lean_object* v_x1_2970_, lean_object* v_x2_2971_){
_start:
{
lean_object* v___x_2972_; 
v___x_2972_ = lean_apply_2(v_f_2969_, v_x1_2970_, v_x2_2971_);
return v___x_2972_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg(lean_object* v_lctx_2992_, lean_object* v_f_2993_, lean_object* v_init_2994_, lean_object* v_start_2995_){
_start:
{
lean_object* v___f_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___f_2996_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2996_, 0, v_f_2993_);
v___x_2997_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_2998_ = l_Lean_LocalContext_foldlM___redArg(v___x_2997_, v_lctx_2992_, v___f_2996_, v_init_2994_, v_start_2995_);
return v___x_2998_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg___boxed(lean_object* v_lctx_2999_, lean_object* v_f_3000_, lean_object* v_init_3001_, lean_object* v_start_3002_){
_start:
{
lean_object* v_res_3003_; 
v_res_3003_ = l_Lean_LocalContext_foldl___redArg(v_lctx_2999_, v_f_3000_, v_init_3001_, v_start_3002_);
lean_dec(v_start_3002_);
return v_res_3003_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl(lean_object* v_00_u03b2_3004_, lean_object* v_lctx_3005_, lean_object* v_f_3006_, lean_object* v_init_3007_, lean_object* v_start_3008_){
_start:
{
lean_object* v___f_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___f_3009_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3009_, 0, v_f_3006_);
v___x_3010_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3011_ = l_Lean_LocalContext_foldlM___redArg(v___x_3010_, v_lctx_3005_, v___f_3009_, v_init_3007_, v_start_3008_);
return v___x_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___boxed(lean_object* v_00_u03b2_3012_, lean_object* v_lctx_3013_, lean_object* v_f_3014_, lean_object* v_init_3015_, lean_object* v_start_3016_){
_start:
{
lean_object* v_res_3017_; 
v_res_3017_ = l_Lean_LocalContext_foldl(v_00_u03b2_3012_, v_lctx_3013_, v_f_3014_, v_init_3015_, v_start_3016_);
lean_dec(v_start_3016_);
return v_res_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr___redArg___lam__0(lean_object* v_f_3018_, lean_object* v_x1_3019_, lean_object* v_x2_3020_){
_start:
{
lean_object* v___x_3021_; 
v___x_3021_ = lean_apply_2(v_f_3018_, v_x1_3019_, v_x2_3020_);
return v___x_3021_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr___redArg(lean_object* v_lctx_3022_, lean_object* v_f_3023_, lean_object* v_init_3024_){
_start:
{
lean_object* v___f_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___f_3025_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3025_, 0, v_f_3023_);
v___x_3026_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3027_ = l_Lean_LocalContext_foldrM___redArg(v___x_3026_, v_lctx_3022_, v___f_3025_, v_init_3024_);
return v___x_3027_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr(lean_object* v_00_u03b2_3028_, lean_object* v_lctx_3029_, lean_object* v_f_3030_, lean_object* v_init_3031_){
_start:
{
lean_object* v___f_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; 
v___f_3032_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3032_, 0, v_f_3030_);
v___x_3033_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3034_ = l_Lean_LocalContext_foldrM___redArg(v___x_3033_, v_lctx_3029_, v___f_3032_, v_init_3031_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(lean_object* v_as_3035_, size_t v_i_3036_, size_t v_stop_3037_, lean_object* v_b_3038_){
_start:
{
lean_object* v___y_3040_; uint8_t v___x_3044_; 
v___x_3044_ = lean_usize_dec_eq(v_i_3036_, v_stop_3037_);
if (v___x_3044_ == 0)
{
lean_object* v___x_3045_; 
v___x_3045_ = lean_array_uget_borrowed(v_as_3035_, v_i_3036_);
if (lean_obj_tag(v___x_3045_) == 0)
{
v___y_3040_ = v_b_3038_;
goto v___jp_3039_;
}
else
{
lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3046_ = lean_unsigned_to_nat(1u);
v___x_3047_ = lean_nat_add(v_b_3038_, v___x_3046_);
lean_dec(v_b_3038_);
v___y_3040_ = v___x_3047_;
goto v___jp_3039_;
}
}
else
{
return v_b_3038_;
}
v___jp_3039_:
{
size_t v___x_3041_; size_t v___x_3042_; 
v___x_3041_ = ((size_t)1ULL);
v___x_3042_ = lean_usize_add(v_i_3036_, v___x_3041_);
v_i_3036_ = v___x_3042_;
v_b_3038_ = v___y_3040_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3048_, lean_object* v_i_3049_, lean_object* v_stop_3050_, lean_object* v_b_3051_){
_start:
{
size_t v_i_boxed_3052_; size_t v_stop_boxed_3053_; lean_object* v_res_3054_; 
v_i_boxed_3052_ = lean_unbox_usize(v_i_3049_);
lean_dec(v_i_3049_);
v_stop_boxed_3053_ = lean_unbox_usize(v_stop_3050_);
lean_dec(v_stop_3050_);
v_res_3054_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_as_3048_, v_i_boxed_3052_, v_stop_boxed_3053_, v_b_3051_);
lean_dec_ref(v_as_3048_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(lean_object* v_x_3055_, lean_object* v_x_3056_){
_start:
{
if (lean_obj_tag(v_x_3055_) == 0)
{
lean_object* v_cs_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; uint8_t v___x_3060_; 
v_cs_3057_ = lean_ctor_get(v_x_3055_, 0);
v___x_3058_ = lean_unsigned_to_nat(0u);
v___x_3059_ = lean_array_get_size(v_cs_3057_);
v___x_3060_ = lean_nat_dec_lt(v___x_3058_, v___x_3059_);
if (v___x_3060_ == 0)
{
return v_x_3056_;
}
else
{
uint8_t v___x_3061_; 
v___x_3061_ = lean_nat_dec_le(v___x_3059_, v___x_3059_);
if (v___x_3061_ == 0)
{
if (v___x_3060_ == 0)
{
return v_x_3056_;
}
else
{
size_t v___x_3062_; size_t v___x_3063_; lean_object* v___x_3064_; 
v___x_3062_ = ((size_t)0ULL);
v___x_3063_ = lean_usize_of_nat(v___x_3059_);
v___x_3064_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_cs_3057_, v___x_3062_, v___x_3063_, v_x_3056_);
return v___x_3064_;
}
}
else
{
size_t v___x_3065_; size_t v___x_3066_; lean_object* v___x_3067_; 
v___x_3065_ = ((size_t)0ULL);
v___x_3066_ = lean_usize_of_nat(v___x_3059_);
v___x_3067_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_cs_3057_, v___x_3065_, v___x_3066_, v_x_3056_);
return v___x_3067_;
}
}
}
else
{
lean_object* v_vs_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; uint8_t v___x_3071_; 
v_vs_3068_ = lean_ctor_get(v_x_3055_, 0);
v___x_3069_ = lean_unsigned_to_nat(0u);
v___x_3070_ = lean_array_get_size(v_vs_3068_);
v___x_3071_ = lean_nat_dec_lt(v___x_3069_, v___x_3070_);
if (v___x_3071_ == 0)
{
return v_x_3056_;
}
else
{
uint8_t v___x_3072_; 
v___x_3072_ = lean_nat_dec_le(v___x_3070_, v___x_3070_);
if (v___x_3072_ == 0)
{
if (v___x_3071_ == 0)
{
return v_x_3056_;
}
else
{
size_t v___x_3073_; size_t v___x_3074_; lean_object* v___x_3075_; 
v___x_3073_ = ((size_t)0ULL);
v___x_3074_ = lean_usize_of_nat(v___x_3070_);
v___x_3075_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_vs_3068_, v___x_3073_, v___x_3074_, v_x_3056_);
return v___x_3075_;
}
}
else
{
size_t v___x_3076_; size_t v___x_3077_; lean_object* v___x_3078_; 
v___x_3076_ = ((size_t)0ULL);
v___x_3077_ = lean_usize_of_nat(v___x_3070_);
v___x_3078_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_vs_3068_, v___x_3076_, v___x_3077_, v_x_3056_);
return v___x_3078_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(lean_object* v_as_3079_, size_t v_i_3080_, size_t v_stop_3081_, lean_object* v_b_3082_){
_start:
{
uint8_t v___x_3083_; 
v___x_3083_ = lean_usize_dec_eq(v_i_3080_, v_stop_3081_);
if (v___x_3083_ == 0)
{
lean_object* v___x_3084_; lean_object* v___x_3085_; size_t v___x_3086_; size_t v___x_3087_; 
v___x_3084_ = lean_array_uget_borrowed(v_as_3079_, v_i_3080_);
v___x_3085_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(v___x_3084_, v_b_3082_);
v___x_3086_ = ((size_t)1ULL);
v___x_3087_ = lean_usize_add(v_i_3080_, v___x_3086_);
v_i_3080_ = v___x_3087_;
v_b_3082_ = v___x_3085_;
goto _start;
}
else
{
return v_b_3082_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_as_3089_, lean_object* v_i_3090_, lean_object* v_stop_3091_, lean_object* v_b_3092_){
_start:
{
size_t v_i_boxed_3093_; size_t v_stop_boxed_3094_; lean_object* v_res_3095_; 
v_i_boxed_3093_ = lean_unbox_usize(v_i_3090_);
lean_dec(v_i_3090_);
v_stop_boxed_3094_ = lean_unbox_usize(v_stop_3091_);
lean_dec(v_stop_3091_);
v_res_3095_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_as_3089_, v_i_boxed_3093_, v_stop_boxed_3094_, v_b_3092_);
lean_dec_ref(v_as_3089_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3___boxed(lean_object* v_x_3096_, lean_object* v_x_3097_){
_start:
{
lean_object* v_res_3098_; 
v_res_3098_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(v_x_3096_, v_x_3097_);
lean_dec_ref(v_x_3096_);
return v_res_3098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(lean_object* v_x_3099_, size_t v_x_3100_, size_t v_x_3101_, lean_object* v_x_3102_){
_start:
{
if (lean_obj_tag(v_x_3099_) == 0)
{
lean_object* v_cs_3103_; lean_object* v___x_3104_; size_t v___x_3105_; lean_object* v_j_3106_; lean_object* v___x_3107_; size_t v___x_3108_; size_t v___x_3109_; size_t v___x_3110_; size_t v___x_3111_; size_t v___x_3112_; size_t v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; uint8_t v___x_3118_; 
v_cs_3103_ = lean_ctor_get(v_x_3099_, 0);
v___x_3104_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0);
v___x_3105_ = lean_usize_shift_right(v_x_3100_, v_x_3101_);
v_j_3106_ = lean_usize_to_nat(v___x_3105_);
v___x_3107_ = lean_array_get_borrowed(v___x_3104_, v_cs_3103_, v_j_3106_);
v___x_3108_ = ((size_t)1ULL);
v___x_3109_ = lean_usize_shift_left(v___x_3108_, v_x_3101_);
v___x_3110_ = lean_usize_sub(v___x_3109_, v___x_3108_);
v___x_3111_ = lean_usize_land(v_x_3100_, v___x_3110_);
v___x_3112_ = ((size_t)5ULL);
v___x_3113_ = lean_usize_sub(v_x_3101_, v___x_3112_);
v___x_3114_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(v___x_3107_, v___x_3111_, v___x_3113_, v_x_3102_);
v___x_3115_ = lean_unsigned_to_nat(1u);
v___x_3116_ = lean_nat_add(v_j_3106_, v___x_3115_);
lean_dec(v_j_3106_);
v___x_3117_ = lean_array_get_size(v_cs_3103_);
v___x_3118_ = lean_nat_dec_lt(v___x_3116_, v___x_3117_);
if (v___x_3118_ == 0)
{
lean_dec(v___x_3116_);
return v___x_3114_;
}
else
{
uint8_t v___x_3119_; 
v___x_3119_ = lean_nat_dec_le(v___x_3117_, v___x_3117_);
if (v___x_3119_ == 0)
{
if (v___x_3118_ == 0)
{
lean_dec(v___x_3116_);
return v___x_3114_;
}
else
{
size_t v___x_3120_; size_t v___x_3121_; lean_object* v___x_3122_; 
v___x_3120_ = lean_usize_of_nat(v___x_3116_);
lean_dec(v___x_3116_);
v___x_3121_ = lean_usize_of_nat(v___x_3117_);
v___x_3122_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_cs_3103_, v___x_3120_, v___x_3121_, v___x_3114_);
return v___x_3122_;
}
}
else
{
size_t v___x_3123_; size_t v___x_3124_; lean_object* v___x_3125_; 
v___x_3123_ = lean_usize_of_nat(v___x_3116_);
lean_dec(v___x_3116_);
v___x_3124_ = lean_usize_of_nat(v___x_3117_);
v___x_3125_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_cs_3103_, v___x_3123_, v___x_3124_, v___x_3114_);
return v___x_3125_;
}
}
}
else
{
lean_object* v_vs_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; uint8_t v___x_3129_; 
v_vs_3126_ = lean_ctor_get(v_x_3099_, 0);
v___x_3127_ = lean_usize_to_nat(v_x_3100_);
v___x_3128_ = lean_array_get_size(v_vs_3126_);
v___x_3129_ = lean_nat_dec_lt(v___x_3127_, v___x_3128_);
if (v___x_3129_ == 0)
{
lean_dec(v___x_3127_);
return v_x_3102_;
}
else
{
uint8_t v___x_3130_; 
v___x_3130_ = lean_nat_dec_le(v___x_3128_, v___x_3128_);
if (v___x_3130_ == 0)
{
if (v___x_3129_ == 0)
{
lean_dec(v___x_3127_);
return v_x_3102_;
}
else
{
size_t v___x_3131_; size_t v___x_3132_; lean_object* v___x_3133_; 
v___x_3131_ = lean_usize_of_nat(v___x_3127_);
lean_dec(v___x_3127_);
v___x_3132_ = lean_usize_of_nat(v___x_3128_);
v___x_3133_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_vs_3126_, v___x_3131_, v___x_3132_, v_x_3102_);
return v___x_3133_;
}
}
else
{
size_t v___x_3134_; size_t v___x_3135_; lean_object* v___x_3136_; 
v___x_3134_ = lean_usize_of_nat(v___x_3127_);
lean_dec(v___x_3127_);
v___x_3135_ = lean_usize_of_nat(v___x_3128_);
v___x_3136_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_vs_3126_, v___x_3134_, v___x_3135_, v_x_3102_);
return v___x_3136_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3137_, lean_object* v_x_3138_, lean_object* v_x_3139_, lean_object* v_x_3140_){
_start:
{
size_t v_x_1557__boxed_3141_; size_t v_x_1558__boxed_3142_; lean_object* v_res_3143_; 
v_x_1557__boxed_3141_ = lean_unbox_usize(v_x_3138_);
lean_dec(v_x_3138_);
v_x_1558__boxed_3142_ = lean_unbox_usize(v_x_3139_);
lean_dec(v_x_3139_);
v_res_3143_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(v_x_3137_, v_x_1557__boxed_3141_, v_x_1558__boxed_3142_, v_x_3140_);
lean_dec_ref(v_x_3137_);
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(lean_object* v_t_3144_, lean_object* v_init_3145_, lean_object* v_start_3146_){
_start:
{
lean_object* v___x_3147_; uint8_t v___x_3148_; 
v___x_3147_ = lean_unsigned_to_nat(0u);
v___x_3148_ = lean_nat_dec_eq(v_start_3146_, v___x_3147_);
if (v___x_3148_ == 0)
{
lean_object* v_root_3149_; lean_object* v_tail_3150_; size_t v_shift_3151_; lean_object* v_tailOff_3152_; uint8_t v___x_3153_; 
v_root_3149_ = lean_ctor_get(v_t_3144_, 0);
v_tail_3150_ = lean_ctor_get(v_t_3144_, 1);
v_shift_3151_ = lean_ctor_get_usize(v_t_3144_, 4);
v_tailOff_3152_ = lean_ctor_get(v_t_3144_, 3);
v___x_3153_ = lean_nat_dec_le(v_tailOff_3152_, v_start_3146_);
if (v___x_3153_ == 0)
{
size_t v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; uint8_t v___x_3157_; 
v___x_3154_ = lean_usize_of_nat(v_start_3146_);
v___x_3155_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(v_root_3149_, v___x_3154_, v_shift_3151_, v_init_3145_);
v___x_3156_ = lean_array_get_size(v_tail_3150_);
v___x_3157_ = lean_nat_dec_lt(v___x_3147_, v___x_3156_);
if (v___x_3157_ == 0)
{
return v___x_3155_;
}
else
{
uint8_t v___x_3158_; 
v___x_3158_ = lean_nat_dec_le(v___x_3156_, v___x_3156_);
if (v___x_3158_ == 0)
{
if (v___x_3157_ == 0)
{
return v___x_3155_;
}
else
{
size_t v___x_3159_; size_t v___x_3160_; lean_object* v___x_3161_; 
v___x_3159_ = ((size_t)0ULL);
v___x_3160_ = lean_usize_of_nat(v___x_3156_);
v___x_3161_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3150_, v___x_3159_, v___x_3160_, v___x_3155_);
return v___x_3161_;
}
}
else
{
size_t v___x_3162_; size_t v___x_3163_; lean_object* v___x_3164_; 
v___x_3162_ = ((size_t)0ULL);
v___x_3163_ = lean_usize_of_nat(v___x_3156_);
v___x_3164_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3150_, v___x_3162_, v___x_3163_, v___x_3155_);
return v___x_3164_;
}
}
}
else
{
lean_object* v___x_3165_; lean_object* v___x_3166_; uint8_t v___x_3167_; 
v___x_3165_ = lean_nat_sub(v_start_3146_, v_tailOff_3152_);
v___x_3166_ = lean_array_get_size(v_tail_3150_);
v___x_3167_ = lean_nat_dec_lt(v___x_3165_, v___x_3166_);
if (v___x_3167_ == 0)
{
lean_dec(v___x_3165_);
return v_init_3145_;
}
else
{
uint8_t v___x_3168_; 
v___x_3168_ = lean_nat_dec_le(v___x_3166_, v___x_3166_);
if (v___x_3168_ == 0)
{
if (v___x_3167_ == 0)
{
lean_dec(v___x_3165_);
return v_init_3145_;
}
else
{
size_t v___x_3169_; size_t v___x_3170_; lean_object* v___x_3171_; 
v___x_3169_ = lean_usize_of_nat(v___x_3165_);
lean_dec(v___x_3165_);
v___x_3170_ = lean_usize_of_nat(v___x_3166_);
v___x_3171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3150_, v___x_3169_, v___x_3170_, v_init_3145_);
return v___x_3171_;
}
}
else
{
size_t v___x_3172_; size_t v___x_3173_; lean_object* v___x_3174_; 
v___x_3172_ = lean_usize_of_nat(v___x_3165_);
lean_dec(v___x_3165_);
v___x_3173_ = lean_usize_of_nat(v___x_3166_);
v___x_3174_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3150_, v___x_3172_, v___x_3173_, v_init_3145_);
return v___x_3174_;
}
}
}
}
else
{
lean_object* v_root_3175_; lean_object* v_tail_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; uint8_t v___x_3179_; 
v_root_3175_ = lean_ctor_get(v_t_3144_, 0);
v_tail_3176_ = lean_ctor_get(v_t_3144_, 1);
v___x_3177_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(v_root_3175_, v_init_3145_);
v___x_3178_ = lean_array_get_size(v_tail_3176_);
v___x_3179_ = lean_nat_dec_lt(v___x_3147_, v___x_3178_);
if (v___x_3179_ == 0)
{
return v___x_3177_;
}
else
{
uint8_t v___x_3180_; 
v___x_3180_ = lean_nat_dec_le(v___x_3178_, v___x_3178_);
if (v___x_3180_ == 0)
{
if (v___x_3179_ == 0)
{
return v___x_3177_;
}
else
{
size_t v___x_3181_; size_t v___x_3182_; lean_object* v___x_3183_; 
v___x_3181_ = ((size_t)0ULL);
v___x_3182_ = lean_usize_of_nat(v___x_3178_);
v___x_3183_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3176_, v___x_3181_, v___x_3182_, v___x_3177_);
return v___x_3183_;
}
}
else
{
size_t v___x_3184_; size_t v___x_3185_; lean_object* v___x_3186_; 
v___x_3184_ = ((size_t)0ULL);
v___x_3185_ = lean_usize_of_nat(v___x_3178_);
v___x_3186_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3176_, v___x_3184_, v___x_3185_, v___x_3177_);
return v___x_3186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0___boxed(lean_object* v_t_3187_, lean_object* v_init_3188_, lean_object* v_start_3189_){
_start:
{
lean_object* v_res_3190_; 
v_res_3190_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(v_t_3187_, v_init_3188_, v_start_3189_);
lean_dec(v_start_3189_);
lean_dec_ref(v_t_3187_);
return v_res_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(lean_object* v_lctx_3191_, lean_object* v_init_3192_, lean_object* v_start_3193_){
_start:
{
lean_object* v_decls_3194_; lean_object* v___x_3195_; 
v_decls_3194_ = lean_ctor_get(v_lctx_3191_, 1);
v___x_3195_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(v_decls_3194_, v_init_3192_, v_start_3193_);
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0___boxed(lean_object* v_lctx_3196_, lean_object* v_init_3197_, lean_object* v_start_3198_){
_start:
{
lean_object* v_res_3199_; 
v_res_3199_ = l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(v_lctx_3196_, v_init_3197_, v_start_3198_);
lean_dec(v_start_3198_);
lean_dec_ref(v_lctx_3196_);
return v_res_3199_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_size(lean_object* v_lctx_3200_){
_start:
{
lean_object* v___x_3201_; lean_object* v___x_3202_; 
v___x_3201_ = lean_unsigned_to_nat(0u);
v___x_3202_ = l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(v_lctx_3200_, v___x_3201_, v___x_3201_);
return v___x_3202_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_size___boxed(lean_object* v_lctx_3203_){
_start:
{
lean_object* v_res_3204_; 
v_res_3204_ = l_Lean_LocalContext_size(v_lctx_3203_);
lean_dec_ref(v_lctx_3203_);
return v_res_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f___redArg___lam__0(lean_object* v_f_3205_, lean_object* v_x_3206_){
_start:
{
lean_object* v___x_3207_; 
v___x_3207_ = lean_apply_1(v_f_3205_, v_x_3206_);
return v___x_3207_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f___redArg(lean_object* v_lctx_3208_, lean_object* v_f_3209_){
_start:
{
lean_object* v___f_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___f_3210_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3210_, 0, v_f_3209_);
v___x_3211_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3212_ = l_Lean_LocalContext_findDeclM_x3f___redArg(v___x_3211_, v_lctx_3208_, v___f_3210_);
return v___x_3212_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f(lean_object* v_00_u03b2_3213_, lean_object* v_lctx_3214_, lean_object* v_f_3215_){
_start:
{
lean_object* v___f_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; 
v___f_3216_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3216_, 0, v_f_3215_);
v___x_3217_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3218_ = l_Lean_LocalContext_findDeclM_x3f___redArg(v___x_3217_, v_lctx_3214_, v___f_3216_);
return v___x_3218_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRev_x3f___redArg(lean_object* v_lctx_3219_, lean_object* v_f_3220_){
_start:
{
lean_object* v___f_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___f_3221_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3221_, 0, v_f_3220_);
v___x_3222_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3223_ = l_Lean_LocalContext_findDeclRevM_x3f___redArg(v___x_3222_, v_lctx_3219_, v___f_3221_);
return v___x_3223_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRev_x3f(lean_object* v_00_u03b2_3224_, lean_object* v_lctx_3225_, lean_object* v_f_3226_){
_start:
{
lean_object* v___f_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; 
v___f_3227_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3227_, 0, v_f_3226_);
v___x_3228_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3229_ = l_Lean_LocalContext_findDeclRevM_x3f___redArg(v___x_3228_, v_lctx_3225_, v___f_3227_);
return v___x_3229_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(lean_object* v_val_3230_, lean_object* v_as_3231_, size_t v_i_3232_, size_t v_stop_3233_){
_start:
{
uint8_t v___x_3234_; 
v___x_3234_ = lean_usize_dec_eq(v_i_3232_, v_stop_3233_);
if (v___x_3234_ == 0)
{
uint8_t v___x_3235_; uint8_t v___y_3237_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v_fvarId_3243_; uint8_t v___x_3244_; 
v___x_3235_ = 1;
v___x_3241_ = lean_array_uget_borrowed(v_as_3231_, v_i_3232_);
v___x_3242_ = l_Lean_Expr_fvarId_x21(v___x_3241_);
v_fvarId_3243_ = lean_ctor_get(v_val_3230_, 1);
v___x_3244_ = l_Lean_instBEqFVarId_beq(v___x_3242_, v_fvarId_3243_);
lean_dec(v___x_3242_);
v___y_3237_ = v___x_3244_;
goto v___jp_3236_;
v___jp_3236_:
{
if (v___y_3237_ == 0)
{
size_t v___x_3238_; size_t v___x_3239_; 
v___x_3238_ = ((size_t)1ULL);
v___x_3239_ = lean_usize_add(v_i_3232_, v___x_3238_);
v_i_3232_ = v___x_3239_;
goto _start;
}
else
{
return v___x_3235_;
}
}
}
else
{
uint8_t v___x_3245_; 
v___x_3245_ = 0;
return v___x_3245_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0___boxed(lean_object* v_val_3246_, lean_object* v_as_3247_, lean_object* v_i_3248_, lean_object* v_stop_3249_){
_start:
{
size_t v_i_boxed_3250_; size_t v_stop_boxed_3251_; uint8_t v_res_3252_; lean_object* v_r_3253_; 
v_i_boxed_3250_ = lean_unbox_usize(v_i_3248_);
lean_dec(v_i_3248_);
v_stop_boxed_3251_ = lean_unbox_usize(v_stop_3249_);
lean_dec(v_stop_3249_);
v_res_3252_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(v_val_3246_, v_as_3247_, v_i_boxed_3250_, v_stop_boxed_3251_);
lean_dec_ref(v_as_3247_);
lean_dec_ref(v_val_3246_);
v_r_3253_ = lean_box(v_res_3252_);
return v_r_3253_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_isSubPrefixOfAux(lean_object* v_a_u2081_3254_, lean_object* v_a_u2082_3255_, lean_object* v_exceptFVars_3256_, lean_object* v_i_3257_, lean_object* v_j_3258_){
_start:
{
lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v_size_3274_; uint8_t v___x_3275_; 
v_size_3274_ = lean_ctor_get(v_a_u2081_3254_, 2);
v___x_3275_ = lean_nat_dec_lt(v_i_3257_, v_size_3274_);
if (v___x_3275_ == 0)
{
uint8_t v___x_3276_; 
lean_dec(v_j_3258_);
lean_dec(v_i_3257_);
v___x_3276_ = 1;
return v___x_3276_;
}
else
{
lean_object* v___x_3277_; lean_object* v___x_3278_; 
v___x_3277_ = lean_box(0);
v___x_3278_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3277_, v_a_u2081_3254_, v_i_3257_);
if (lean_obj_tag(v___x_3278_) == 0)
{
lean_object* v___x_3279_; lean_object* v___x_3280_; 
v___x_3279_ = lean_unsigned_to_nat(1u);
v___x_3280_ = lean_nat_add(v_i_3257_, v___x_3279_);
lean_dec(v_i_3257_);
v_i_3257_ = v___x_3280_;
goto _start;
}
else
{
lean_object* v_val_3282_; uint8_t v___y_3284_; lean_object* v___x_3293_; lean_object* v___x_3294_; uint8_t v___x_3295_; 
v_val_3282_ = lean_ctor_get(v___x_3278_, 0);
lean_inc(v_val_3282_);
lean_dec_ref_known(v___x_3278_, 1);
v___x_3293_ = lean_unsigned_to_nat(0u);
v___x_3294_ = lean_array_get_size(v_exceptFVars_3256_);
v___x_3295_ = lean_nat_dec_lt(v___x_3293_, v___x_3294_);
if (v___x_3295_ == 0)
{
v___y_3284_ = v___x_3295_;
goto v___jp_3283_;
}
else
{
if (v___x_3295_ == 0)
{
v___y_3284_ = v___x_3295_;
goto v___jp_3283_;
}
else
{
size_t v___x_3296_; size_t v___x_3297_; uint8_t v___x_3298_; 
v___x_3296_ = ((size_t)0ULL);
v___x_3297_ = lean_usize_of_nat(v___x_3294_);
v___x_3298_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(v_val_3282_, v_exceptFVars_3256_, v___x_3296_, v___x_3297_);
if (v___x_3298_ == 0)
{
v___y_3284_ = v___x_3298_;
goto v___jp_3283_;
}
else
{
lean_object* v___x_3299_; lean_object* v___x_3300_; 
lean_dec(v_val_3282_);
v___x_3299_ = lean_unsigned_to_nat(1u);
v___x_3300_ = lean_nat_add(v_i_3257_, v___x_3299_);
lean_dec(v_i_3257_);
v_i_3257_ = v___x_3300_;
goto _start;
}
}
}
v___jp_3283_:
{
lean_object* v_size_3285_; uint8_t v___x_3286_; 
v_size_3285_ = lean_ctor_get(v_a_u2082_3255_, 2);
v___x_3286_ = lean_nat_dec_lt(v_j_3258_, v_size_3285_);
if (v___x_3286_ == 0)
{
lean_dec(v_val_3282_);
lean_dec(v_j_3258_);
lean_dec(v_i_3257_);
return v___y_3284_;
}
else
{
lean_object* v___x_3287_; 
v___x_3287_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3277_, v_a_u2082_3255_, v_j_3258_);
if (lean_obj_tag(v___x_3287_) == 0)
{
lean_object* v___x_3288_; lean_object* v___x_3289_; 
lean_dec(v_val_3282_);
v___x_3288_ = lean_unsigned_to_nat(1u);
v___x_3289_ = lean_nat_add(v_j_3258_, v___x_3288_);
lean_dec(v_j_3258_);
v_j_3258_ = v___x_3289_;
goto _start;
}
else
{
lean_object* v_val_3291_; lean_object* v_fvarId_3292_; 
v_val_3291_ = lean_ctor_get(v___x_3287_, 0);
lean_inc(v_val_3291_);
lean_dec_ref_known(v___x_3287_, 1);
v_fvarId_3292_ = lean_ctor_get(v_val_3282_, 1);
lean_inc(v_fvarId_3292_);
lean_dec(v_val_3282_);
v___y_3271_ = v_val_3291_;
v___y_3272_ = v_fvarId_3292_;
goto v___jp_3270_;
}
}
}
}
}
v___jp_3259_:
{
uint8_t v___x_3262_; 
v___x_3262_ = l_Lean_instBEqFVarId_beq(v___y_3260_, v___y_3261_);
lean_dec(v___y_3261_);
lean_dec(v___y_3260_);
if (v___x_3262_ == 0)
{
lean_object* v___x_3263_; lean_object* v___x_3264_; 
v___x_3263_ = lean_unsigned_to_nat(1u);
v___x_3264_ = lean_nat_add(v_j_3258_, v___x_3263_);
lean_dec(v_j_3258_);
v_j_3258_ = v___x_3264_;
goto _start;
}
else
{
lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; 
v___x_3266_ = lean_unsigned_to_nat(1u);
v___x_3267_ = lean_nat_add(v_i_3257_, v___x_3266_);
lean_dec(v_i_3257_);
v___x_3268_ = lean_nat_add(v_j_3258_, v___x_3266_);
lean_dec(v_j_3258_);
v_i_3257_ = v___x_3267_;
v_j_3258_ = v___x_3268_;
goto _start;
}
}
v___jp_3270_:
{
lean_object* v_fvarId_3273_; 
v_fvarId_3273_ = lean_ctor_get(v___y_3271_, 1);
lean_inc(v_fvarId_3273_);
lean_dec_ref(v___y_3271_);
v___y_3260_ = v___y_3272_;
v___y_3261_ = v_fvarId_3273_;
goto v___jp_3259_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_isSubPrefixOfAux___boxed(lean_object* v_a_u2081_3302_, lean_object* v_a_u2082_3303_, lean_object* v_exceptFVars_3304_, lean_object* v_i_3305_, lean_object* v_j_3306_){
_start:
{
uint8_t v_res_3307_; lean_object* v_r_3308_; 
v_res_3307_ = l_Lean_LocalContext_isSubPrefixOfAux(v_a_u2081_3302_, v_a_u2082_3303_, v_exceptFVars_3304_, v_i_3305_, v_j_3306_);
lean_dec_ref(v_exceptFVars_3304_);
lean_dec_ref(v_a_u2082_3303_);
lean_dec_ref(v_a_u2081_3302_);
v_r_3308_ = lean_box(v_res_3307_);
return v_r_3308_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_isSubPrefixOf(lean_object* v_lctx_u2081_3309_, lean_object* v_lctx_u2082_3310_, lean_object* v_exceptFVars_3311_){
_start:
{
lean_object* v_decls_3312_; lean_object* v_decls_3313_; lean_object* v___x_3314_; uint8_t v___x_3315_; 
v_decls_3312_ = lean_ctor_get(v_lctx_u2081_3309_, 1);
v_decls_3313_ = lean_ctor_get(v_lctx_u2082_3310_, 1);
v___x_3314_ = lean_unsigned_to_nat(0u);
v___x_3315_ = l_Lean_LocalContext_isSubPrefixOfAux(v_decls_3312_, v_decls_3313_, v_exceptFVars_3311_, v___x_3314_, v___x_3314_);
return v___x_3315_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_isSubPrefixOf___boxed(lean_object* v_lctx_u2081_3316_, lean_object* v_lctx_u2082_3317_, lean_object* v_exceptFVars_3318_){
_start:
{
uint8_t v_res_3319_; lean_object* v_r_3320_; 
v_res_3319_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_u2081_3316_, v_lctx_u2082_3317_, v_exceptFVars_3318_);
lean_dec_ref(v_exceptFVars_3318_);
lean_dec_ref(v_lctx_u2082_3317_);
lean_dec_ref(v_lctx_u2081_3316_);
v_r_3320_ = lean_box(v_res_3319_);
return v_r_3320_;
}
}
static lean_object* _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; 
v___x_3322_ = ((lean_object*)(l_Lean_LocalContext_get_x21___closed__1));
v___x_3323_ = lean_unsigned_to_nat(14u);
v___x_3324_ = lean_unsigned_to_nat(576u);
v___x_3325_ = ((lean_object*)(l_Lean_LocalContext_mkBinding___lam__0___closed__0));
v___x_3326_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_3327_ = l_mkPanicMessageWithDecl(v___x_3326_, v___x_3325_, v___x_3324_, v___x_3323_, v___x_3322_);
return v___x_3327_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___lam__0(lean_object* v_xs_3328_, lean_object* v_lctx_3329_, lean_object* v___x_3330_, uint8_t v_isLambda_3331_, uint8_t v_usedLetOnly_3332_, uint8_t v_generalizeNondepLet_3333_, lean_object* v_i_3334_, lean_object* v_x_3335_, lean_object* v_b_3336_){
_start:
{
lean_object* v_n_3338_; lean_object* v_ty_3339_; uint8_t v_bi_3340_; lean_object* v_x_3344_; lean_object* v___x_3345_; 
v_x_3344_ = lean_array_fget_borrowed(v_xs_3328_, v_i_3334_);
v___x_3345_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3329_, v_x_3344_);
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_object* v___x_3346_; lean_object* v___x_3347_; 
lean_dec_ref(v_b_3336_);
v___x_3346_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3347_ = l_panic___redArg(v___x_3330_, v___x_3346_);
return v___x_3347_;
}
else
{
lean_object* v_val_3348_; 
v_val_3348_ = lean_ctor_get(v___x_3345_, 0);
lean_inc(v_val_3348_);
lean_dec_ref_known(v___x_3345_, 1);
if (lean_obj_tag(v_val_3348_) == 0)
{
lean_object* v_userName_3349_; lean_object* v_type_3350_; uint8_t v_bi_3351_; 
v_userName_3349_ = lean_ctor_get(v_val_3348_, 2);
lean_inc(v_userName_3349_);
v_type_3350_ = lean_ctor_get(v_val_3348_, 3);
lean_inc_ref(v_type_3350_);
v_bi_3351_ = lean_ctor_get_uint8(v_val_3348_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3348_, 4);
v_n_3338_ = v_userName_3349_;
v_ty_3339_ = v_type_3350_;
v_bi_3340_ = v_bi_3351_;
goto v___jp_3337_;
}
else
{
lean_object* v_userName_3352_; lean_object* v_type_3353_; lean_object* v_value_3354_; uint8_t v_nondep_3355_; uint8_t v___y_3361_; 
v_userName_3352_ = lean_ctor_get(v_val_3348_, 2);
lean_inc(v_userName_3352_);
v_type_3353_ = lean_ctor_get(v_val_3348_, 3);
lean_inc_ref(v_type_3353_);
v_value_3354_ = lean_ctor_get(v_val_3348_, 4);
lean_inc_ref(v_value_3354_);
v_nondep_3355_ = lean_ctor_get_uint8(v_val_3348_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3348_, 5);
if (v_nondep_3355_ == 0)
{
v___y_3361_ = v_nondep_3355_;
goto v___jp_3360_;
}
else
{
if (v_generalizeNondepLet_3333_ == 0)
{
v___y_3361_ = v_generalizeNondepLet_3333_;
goto v___jp_3360_;
}
else
{
uint8_t v___x_3366_; 
lean_dec_ref(v_value_3354_);
v___x_3366_ = 0;
v_n_3338_ = v_userName_3352_;
v_ty_3339_ = v_type_3353_;
v_bi_3340_ = v___x_3366_;
goto v___jp_3337_;
}
}
v___jp_3356_:
{
lean_object* v_ty_3357_; lean_object* v_val_3358_; lean_object* v___x_3359_; 
v_ty_3357_ = lean_expr_abstract_range(v_type_3353_, v_i_3334_, v_xs_3328_);
lean_dec_ref(v_type_3353_);
v_val_3358_ = lean_expr_abstract_range(v_value_3354_, v_i_3334_, v_xs_3328_);
lean_dec_ref(v_value_3354_);
v___x_3359_ = l_Lean_Expr_letE___override(v_userName_3352_, v_ty_3357_, v_val_3358_, v_b_3336_, v_nondep_3355_);
return v___x_3359_;
}
v___jp_3360_:
{
if (v_usedLetOnly_3332_ == 0)
{
goto v___jp_3356_;
}
else
{
if (v___y_3361_ == 0)
{
lean_object* v___x_3362_; uint8_t v___x_3363_; 
v___x_3362_ = lean_unsigned_to_nat(0u);
v___x_3363_ = lean_expr_has_loose_bvar(v_b_3336_, v___x_3362_);
if (v___x_3363_ == 0)
{
lean_object* v___x_3364_; lean_object* v___x_3365_; 
lean_dec_ref(v_value_3354_);
lean_dec_ref(v_type_3353_);
lean_dec(v_userName_3352_);
v___x_3364_ = lean_unsigned_to_nat(1u);
v___x_3365_ = lean_expr_lower_loose_bvars(v_b_3336_, v___x_3364_, v___x_3364_);
lean_dec_ref(v_b_3336_);
return v___x_3365_;
}
else
{
goto v___jp_3356_;
}
}
else
{
goto v___jp_3356_;
}
}
}
}
}
v___jp_3337_:
{
lean_object* v_ty_3341_; 
v_ty_3341_ = lean_expr_abstract_range(v_ty_3339_, v_i_3334_, v_xs_3328_);
lean_dec_ref(v_ty_3339_);
if (v_isLambda_3331_ == 0)
{
lean_object* v___x_3342_; 
v___x_3342_ = l_Lean_mkForall(v_n_3338_, v_bi_3340_, v_ty_3341_, v_b_3336_);
return v___x_3342_;
}
else
{
lean_object* v___x_3343_; 
v___x_3343_ = l_Lean_mkLambda(v_n_3338_, v_bi_3340_, v_ty_3341_, v_b_3336_);
return v___x_3343_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___lam__0___boxed(lean_object* v_xs_3367_, lean_object* v_lctx_3368_, lean_object* v___x_3369_, lean_object* v_isLambda_3370_, lean_object* v_usedLetOnly_3371_, lean_object* v_generalizeNondepLet_3372_, lean_object* v_i_3373_, lean_object* v_x_3374_, lean_object* v_b_3375_){
_start:
{
uint8_t v_isLambda_boxed_3376_; uint8_t v_usedLetOnly_boxed_3377_; uint8_t v_generalizeNondepLet_boxed_3378_; lean_object* v_res_3379_; 
v_isLambda_boxed_3376_ = lean_unbox(v_isLambda_3370_);
v_usedLetOnly_boxed_3377_ = lean_unbox(v_usedLetOnly_3371_);
v_generalizeNondepLet_boxed_3378_ = lean_unbox(v_generalizeNondepLet_3372_);
v_res_3379_ = l_Lean_LocalContext_mkBinding___lam__0(v_xs_3367_, v_lctx_3368_, v___x_3369_, v_isLambda_boxed_3376_, v_usedLetOnly_boxed_3377_, v_generalizeNondepLet_boxed_3378_, v_i_3373_, v_x_3374_, v_b_3375_);
lean_dec(v_i_3373_);
lean_dec_ref(v___x_3369_);
lean_dec_ref(v_xs_3367_);
return v_res_3379_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding(uint8_t v_isLambda_3380_, lean_object* v_lctx_3381_, lean_object* v_xs_3382_, lean_object* v_b_3383_, uint8_t v_usedLetOnly_3384_, uint8_t v_generalizeNondepLet_3385_){
_start:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___f_3390_; lean_object* v_b_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3386_ = l_Lean_instInhabitedExpr;
v___x_3387_ = lean_box(v_isLambda_3380_);
v___x_3388_ = lean_box(v_usedLetOnly_3384_);
v___x_3389_ = lean_box(v_generalizeNondepLet_3385_);
lean_inc_ref(v_xs_3382_);
v___f_3390_ = lean_alloc_closure((void*)(l_Lean_LocalContext_mkBinding___lam__0___boxed), 9, 6);
lean_closure_set(v___f_3390_, 0, v_xs_3382_);
lean_closure_set(v___f_3390_, 1, v_lctx_3381_);
lean_closure_set(v___f_3390_, 2, v___x_3386_);
lean_closure_set(v___f_3390_, 3, v___x_3387_);
lean_closure_set(v___f_3390_, 4, v___x_3388_);
lean_closure_set(v___f_3390_, 5, v___x_3389_);
v_b_3391_ = lean_expr_abstract(v_b_3383_, v_xs_3382_);
v___x_3392_ = lean_array_get_size(v_xs_3382_);
lean_dec_ref(v_xs_3382_);
v___x_3393_ = l_Nat_foldRev___redArg(v___x_3392_, v___f_3390_, v_b_3391_);
return v___x_3393_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___boxed(lean_object* v_isLambda_3394_, lean_object* v_lctx_3395_, lean_object* v_xs_3396_, lean_object* v_b_3397_, lean_object* v_usedLetOnly_3398_, lean_object* v_generalizeNondepLet_3399_){
_start:
{
uint8_t v_isLambda_boxed_3400_; uint8_t v_usedLetOnly_boxed_3401_; uint8_t v_generalizeNondepLet_boxed_3402_; lean_object* v_res_3403_; 
v_isLambda_boxed_3400_ = lean_unbox(v_isLambda_3394_);
v_usedLetOnly_boxed_3401_ = lean_unbox(v_usedLetOnly_3398_);
v_generalizeNondepLet_boxed_3402_ = lean_unbox(v_generalizeNondepLet_3399_);
v_res_3403_ = l_Lean_LocalContext_mkBinding(v_isLambda_boxed_3400_, v_lctx_3395_, v_xs_3396_, v_b_3397_, v_usedLetOnly_boxed_3401_, v_generalizeNondepLet_boxed_3402_);
lean_dec_ref(v_b_3397_);
return v_res_3403_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(lean_object* v_xs_3404_, lean_object* v_lctx_3405_, uint8_t v_usedLetOnly_3406_, uint8_t v_generalizeNondepLet_3407_, lean_object* v_x_3408_, lean_object* v_x_3409_){
_start:
{
lean_object* v_zero_3410_; uint8_t v_isZero_3411_; 
v_zero_3410_ = lean_unsigned_to_nat(0u);
v_isZero_3411_ = lean_nat_dec_eq(v_x_3408_, v_zero_3410_);
if (v_isZero_3411_ == 1)
{
lean_dec(v_x_3408_);
lean_dec_ref(v_lctx_3405_);
return v_x_3409_;
}
else
{
lean_object* v_one_3412_; lean_object* v_n_3413_; lean_object* v_n_3415_; lean_object* v_ty_3416_; uint8_t v_bi_3417_; lean_object* v_x_3421_; lean_object* v___x_3422_; 
v_one_3412_ = lean_unsigned_to_nat(1u);
v_n_3413_ = lean_nat_sub(v_x_3408_, v_one_3412_);
lean_dec(v_x_3408_);
v_x_3421_ = lean_array_fget_borrowed(v_xs_3404_, v_n_3413_);
lean_inc_ref(v_lctx_3405_);
v___x_3422_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3405_, v_x_3421_);
if (lean_obj_tag(v___x_3422_) == 0)
{
lean_object* v___x_3423_; lean_object* v___x_3424_; 
lean_dec_ref(v_x_3409_);
v___x_3423_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3424_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3423_);
v_x_3408_ = v_n_3413_;
v_x_3409_ = v___x_3424_;
goto _start;
}
else
{
lean_object* v_val_3426_; 
v_val_3426_ = lean_ctor_get(v___x_3422_, 0);
lean_inc(v_val_3426_);
lean_dec_ref_known(v___x_3422_, 1);
if (lean_obj_tag(v_val_3426_) == 0)
{
lean_object* v_userName_3427_; lean_object* v_type_3428_; uint8_t v_bi_3429_; 
v_userName_3427_ = lean_ctor_get(v_val_3426_, 2);
lean_inc(v_userName_3427_);
v_type_3428_ = lean_ctor_get(v_val_3426_, 3);
lean_inc_ref(v_type_3428_);
v_bi_3429_ = lean_ctor_get_uint8(v_val_3426_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3426_, 4);
v_n_3415_ = v_userName_3427_;
v_ty_3416_ = v_type_3428_;
v_bi_3417_ = v_bi_3429_;
goto v___jp_3414_;
}
else
{
lean_object* v_userName_3430_; lean_object* v_type_3431_; lean_object* v_value_3432_; uint8_t v_nondep_3433_; uint8_t v___y_3440_; 
v_userName_3430_ = lean_ctor_get(v_val_3426_, 2);
lean_inc(v_userName_3430_);
v_type_3431_ = lean_ctor_get(v_val_3426_, 3);
lean_inc_ref(v_type_3431_);
v_value_3432_ = lean_ctor_get(v_val_3426_, 4);
lean_inc_ref(v_value_3432_);
v_nondep_3433_ = lean_ctor_get_uint8(v_val_3426_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3426_, 5);
if (v_nondep_3433_ == 0)
{
v___y_3440_ = v_nondep_3433_;
goto v___jp_3439_;
}
else
{
if (v_generalizeNondepLet_3407_ == 0)
{
v___y_3440_ = v_generalizeNondepLet_3407_;
goto v___jp_3439_;
}
else
{
uint8_t v___x_3444_; 
lean_dec_ref(v_value_3432_);
v___x_3444_ = 0;
v_n_3415_ = v_userName_3430_;
v_ty_3416_ = v_type_3431_;
v_bi_3417_ = v___x_3444_;
goto v___jp_3414_;
}
}
v___jp_3434_:
{
lean_object* v_ty_3435_; lean_object* v_val_3436_; lean_object* v___x_3437_; 
v_ty_3435_ = lean_expr_abstract_range(v_type_3431_, v_n_3413_, v_xs_3404_);
lean_dec_ref(v_type_3431_);
v_val_3436_ = lean_expr_abstract_range(v_value_3432_, v_n_3413_, v_xs_3404_);
lean_dec_ref(v_value_3432_);
v___x_3437_ = l_Lean_Expr_letE___override(v_userName_3430_, v_ty_3435_, v_val_3436_, v_x_3409_, v_nondep_3433_);
v_x_3408_ = v_n_3413_;
v_x_3409_ = v___x_3437_;
goto _start;
}
v___jp_3439_:
{
if (v_usedLetOnly_3406_ == 0)
{
goto v___jp_3434_;
}
else
{
if (v___y_3440_ == 0)
{
uint8_t v___x_3441_; 
v___x_3441_ = lean_expr_has_loose_bvar(v_x_3409_, v_zero_3410_);
if (v___x_3441_ == 0)
{
lean_object* v___x_3442_; 
lean_dec_ref(v_value_3432_);
lean_dec_ref(v_type_3431_);
lean_dec(v_userName_3430_);
v___x_3442_ = lean_expr_lower_loose_bvars(v_x_3409_, v_one_3412_, v_one_3412_);
lean_dec_ref(v_x_3409_);
v_x_3408_ = v_n_3413_;
v_x_3409_ = v___x_3442_;
goto _start;
}
else
{
goto v___jp_3434_;
}
}
else
{
goto v___jp_3434_;
}
}
}
}
}
v___jp_3414_:
{
lean_object* v_ty_3418_; lean_object* v___x_3419_; 
v_ty_3418_ = lean_expr_abstract_range(v_ty_3416_, v_n_3413_, v_xs_3404_);
lean_dec_ref(v_ty_3416_);
v___x_3419_ = l_Lean_mkLambda(v_n_3415_, v_bi_3417_, v_ty_3418_, v_x_3409_);
v_x_3408_ = v_n_3413_;
v_x_3409_ = v___x_3419_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0___boxed(lean_object* v_xs_3445_, lean_object* v_lctx_3446_, lean_object* v_usedLetOnly_3447_, lean_object* v_generalizeNondepLet_3448_, lean_object* v_x_3449_, lean_object* v_x_3450_){
_start:
{
uint8_t v_usedLetOnly_boxed_3451_; uint8_t v_generalizeNondepLet_boxed_3452_; lean_object* v_res_3453_; 
v_usedLetOnly_boxed_3451_ = lean_unbox(v_usedLetOnly_3447_);
v_generalizeNondepLet_boxed_3452_ = lean_unbox(v_generalizeNondepLet_3448_);
v_res_3453_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3445_, v_lctx_3446_, v_usedLetOnly_boxed_3451_, v_generalizeNondepLet_boxed_3452_, v_x_3449_, v_x_3450_);
lean_dec_ref(v_xs_3445_);
return v_res_3453_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(lean_object* v_xs_3454_, lean_object* v_lctx_3455_, uint8_t v_usedLetOnly_3456_, uint8_t v_generalizeNondepLet_3457_, lean_object* v_x_3458_, lean_object* v_x_3459_){
_start:
{
lean_object* v_zero_3460_; uint8_t v_isZero_3461_; 
v_zero_3460_ = lean_unsigned_to_nat(0u);
v_isZero_3461_ = lean_nat_dec_eq(v_x_3458_, v_zero_3460_);
if (v_isZero_3461_ == 1)
{
lean_dec_ref(v_lctx_3455_);
return v_x_3459_;
}
else
{
lean_object* v_one_3462_; lean_object* v_n_3463_; lean_object* v_n_3465_; lean_object* v_ty_3466_; uint8_t v_bi_3467_; lean_object* v_x_3471_; lean_object* v___x_3472_; 
v_one_3462_ = lean_unsigned_to_nat(1u);
v_n_3463_ = lean_nat_sub(v_x_3458_, v_one_3462_);
v_x_3471_ = lean_array_fget_borrowed(v_xs_3454_, v_n_3463_);
lean_inc_ref(v_lctx_3455_);
v___x_3472_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3455_, v_x_3471_);
if (lean_obj_tag(v___x_3472_) == 0)
{
lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; 
lean_dec_ref(v_x_3459_);
v___x_3473_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3474_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3473_);
v___x_3475_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3454_, v_lctx_3455_, v_usedLetOnly_3456_, v_generalizeNondepLet_3457_, v_n_3463_, v___x_3474_);
return v___x_3475_;
}
else
{
lean_object* v_val_3476_; 
v_val_3476_ = lean_ctor_get(v___x_3472_, 0);
lean_inc(v_val_3476_);
lean_dec_ref_known(v___x_3472_, 1);
if (lean_obj_tag(v_val_3476_) == 0)
{
lean_object* v_userName_3477_; lean_object* v_type_3478_; uint8_t v_bi_3479_; 
v_userName_3477_ = lean_ctor_get(v_val_3476_, 2);
lean_inc(v_userName_3477_);
v_type_3478_ = lean_ctor_get(v_val_3476_, 3);
lean_inc_ref(v_type_3478_);
v_bi_3479_ = lean_ctor_get_uint8(v_val_3476_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3476_, 4);
v_n_3465_ = v_userName_3477_;
v_ty_3466_ = v_type_3478_;
v_bi_3467_ = v_bi_3479_;
goto v___jp_3464_;
}
else
{
lean_object* v_userName_3480_; lean_object* v_type_3481_; lean_object* v_value_3482_; uint8_t v_nondep_3483_; uint8_t v___y_3490_; 
v_userName_3480_ = lean_ctor_get(v_val_3476_, 2);
lean_inc(v_userName_3480_);
v_type_3481_ = lean_ctor_get(v_val_3476_, 3);
lean_inc_ref(v_type_3481_);
v_value_3482_ = lean_ctor_get(v_val_3476_, 4);
lean_inc_ref(v_value_3482_);
v_nondep_3483_ = lean_ctor_get_uint8(v_val_3476_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3476_, 5);
if (v_nondep_3483_ == 0)
{
v___y_3490_ = v_nondep_3483_;
goto v___jp_3489_;
}
else
{
if (v_generalizeNondepLet_3457_ == 0)
{
v___y_3490_ = v_generalizeNondepLet_3457_;
goto v___jp_3489_;
}
else
{
uint8_t v___x_3494_; 
lean_dec_ref(v_value_3482_);
v___x_3494_ = 0;
v_n_3465_ = v_userName_3480_;
v_ty_3466_ = v_type_3481_;
v_bi_3467_ = v___x_3494_;
goto v___jp_3464_;
}
}
v___jp_3484_:
{
lean_object* v_ty_3485_; lean_object* v_val_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; 
v_ty_3485_ = lean_expr_abstract_range(v_type_3481_, v_n_3463_, v_xs_3454_);
lean_dec_ref(v_type_3481_);
v_val_3486_ = lean_expr_abstract_range(v_value_3482_, v_n_3463_, v_xs_3454_);
lean_dec_ref(v_value_3482_);
v___x_3487_ = l_Lean_Expr_letE___override(v_userName_3480_, v_ty_3485_, v_val_3486_, v_x_3459_, v_nondep_3483_);
v___x_3488_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3454_, v_lctx_3455_, v_usedLetOnly_3456_, v_generalizeNondepLet_3457_, v_n_3463_, v___x_3487_);
return v___x_3488_;
}
v___jp_3489_:
{
if (v_usedLetOnly_3456_ == 0)
{
goto v___jp_3484_;
}
else
{
if (v___y_3490_ == 0)
{
uint8_t v___x_3491_; 
v___x_3491_ = lean_expr_has_loose_bvar(v_x_3459_, v_zero_3460_);
if (v___x_3491_ == 0)
{
lean_object* v___x_3492_; lean_object* v___x_3493_; 
lean_dec_ref(v_value_3482_);
lean_dec_ref(v_type_3481_);
lean_dec(v_userName_3480_);
v___x_3492_ = lean_expr_lower_loose_bvars(v_x_3459_, v_one_3462_, v_one_3462_);
lean_dec_ref(v_x_3459_);
v___x_3493_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3454_, v_lctx_3455_, v_usedLetOnly_3456_, v_generalizeNondepLet_3457_, v_n_3463_, v___x_3492_);
return v___x_3493_;
}
else
{
goto v___jp_3484_;
}
}
else
{
goto v___jp_3484_;
}
}
}
}
}
v___jp_3464_:
{
lean_object* v_ty_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; 
v_ty_3468_ = lean_expr_abstract_range(v_ty_3466_, v_n_3463_, v_xs_3454_);
lean_dec_ref(v_ty_3466_);
v___x_3469_ = l_Lean_mkLambda(v_n_3465_, v_bi_3467_, v_ty_3468_, v_x_3459_);
v___x_3470_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3454_, v_lctx_3455_, v_usedLetOnly_3456_, v_generalizeNondepLet_3457_, v_n_3463_, v___x_3469_);
return v___x_3470_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0___boxed(lean_object* v_xs_3495_, lean_object* v_lctx_3496_, lean_object* v_usedLetOnly_3497_, lean_object* v_generalizeNondepLet_3498_, lean_object* v_x_3499_, lean_object* v_x_3500_){
_start:
{
uint8_t v_usedLetOnly_boxed_3501_; uint8_t v_generalizeNondepLet_boxed_3502_; lean_object* v_res_3503_; 
v_usedLetOnly_boxed_3501_ = lean_unbox(v_usedLetOnly_3497_);
v_generalizeNondepLet_boxed_3502_ = lean_unbox(v_generalizeNondepLet_3498_);
v_res_3503_ = l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(v_xs_3495_, v_lctx_3496_, v_usedLetOnly_boxed_3501_, v_generalizeNondepLet_boxed_3502_, v_x_3499_, v_x_3500_);
lean_dec(v_x_3499_);
lean_dec_ref(v_xs_3495_);
return v_res_3503_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLambda(lean_object* v_lctx_3504_, lean_object* v_xs_3505_, lean_object* v_b_3506_, uint8_t v_usedLetOnly_3507_, uint8_t v_generalizeNondepLet_3508_){
_start:
{
lean_object* v_b_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; 
v_b_3509_ = lean_expr_abstract(v_b_3506_, v_xs_3505_);
v___x_3510_ = lean_array_get_size(v_xs_3505_);
v___x_3511_ = l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(v_xs_3505_, v_lctx_3504_, v_usedLetOnly_3507_, v_generalizeNondepLet_3508_, v___x_3510_, v_b_3509_);
return v___x_3511_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLambda___boxed(lean_object* v_lctx_3512_, lean_object* v_xs_3513_, lean_object* v_b_3514_, lean_object* v_usedLetOnly_3515_, lean_object* v_generalizeNondepLet_3516_){
_start:
{
uint8_t v_usedLetOnly_boxed_3517_; uint8_t v_generalizeNondepLet_boxed_3518_; lean_object* v_res_3519_; 
v_usedLetOnly_boxed_3517_ = lean_unbox(v_usedLetOnly_3515_);
v_generalizeNondepLet_boxed_3518_ = lean_unbox(v_generalizeNondepLet_3516_);
v_res_3519_ = l_Lean_LocalContext_mkLambda(v_lctx_3512_, v_xs_3513_, v_b_3514_, v_usedLetOnly_boxed_3517_, v_generalizeNondepLet_boxed_3518_);
lean_dec_ref(v_b_3514_);
lean_dec_ref(v_xs_3513_);
return v_res_3519_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(lean_object* v_xs_3520_, lean_object* v_lctx_3521_, uint8_t v_usedLetOnly_3522_, uint8_t v_generalizeNondepLet_3523_, lean_object* v_x_3524_, lean_object* v_x_3525_){
_start:
{
lean_object* v_zero_3526_; uint8_t v_isZero_3527_; 
v_zero_3526_ = lean_unsigned_to_nat(0u);
v_isZero_3527_ = lean_nat_dec_eq(v_x_3524_, v_zero_3526_);
if (v_isZero_3527_ == 1)
{
lean_dec(v_x_3524_);
lean_dec_ref(v_lctx_3521_);
return v_x_3525_;
}
else
{
lean_object* v_one_3528_; lean_object* v_n_3529_; lean_object* v_n_3531_; lean_object* v_ty_3532_; uint8_t v_bi_3533_; lean_object* v_x_3537_; lean_object* v___x_3538_; 
v_one_3528_ = lean_unsigned_to_nat(1u);
v_n_3529_ = lean_nat_sub(v_x_3524_, v_one_3528_);
lean_dec(v_x_3524_);
v_x_3537_ = lean_array_fget_borrowed(v_xs_3520_, v_n_3529_);
lean_inc_ref(v_lctx_3521_);
v___x_3538_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3521_, v_x_3537_);
if (lean_obj_tag(v___x_3538_) == 0)
{
lean_object* v___x_3539_; lean_object* v___x_3540_; 
lean_dec_ref(v_x_3525_);
v___x_3539_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3540_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3539_);
v_x_3524_ = v_n_3529_;
v_x_3525_ = v___x_3540_;
goto _start;
}
else
{
lean_object* v_val_3542_; 
v_val_3542_ = lean_ctor_get(v___x_3538_, 0);
lean_inc(v_val_3542_);
lean_dec_ref_known(v___x_3538_, 1);
if (lean_obj_tag(v_val_3542_) == 0)
{
lean_object* v_userName_3543_; lean_object* v_type_3544_; uint8_t v_bi_3545_; 
v_userName_3543_ = lean_ctor_get(v_val_3542_, 2);
lean_inc(v_userName_3543_);
v_type_3544_ = lean_ctor_get(v_val_3542_, 3);
lean_inc_ref(v_type_3544_);
v_bi_3545_ = lean_ctor_get_uint8(v_val_3542_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3542_, 4);
v_n_3531_ = v_userName_3543_;
v_ty_3532_ = v_type_3544_;
v_bi_3533_ = v_bi_3545_;
goto v___jp_3530_;
}
else
{
lean_object* v_userName_3546_; lean_object* v_type_3547_; lean_object* v_value_3548_; uint8_t v_nondep_3549_; uint8_t v___y_3556_; 
v_userName_3546_ = lean_ctor_get(v_val_3542_, 2);
lean_inc(v_userName_3546_);
v_type_3547_ = lean_ctor_get(v_val_3542_, 3);
lean_inc_ref(v_type_3547_);
v_value_3548_ = lean_ctor_get(v_val_3542_, 4);
lean_inc_ref(v_value_3548_);
v_nondep_3549_ = lean_ctor_get_uint8(v_val_3542_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3542_, 5);
if (v_nondep_3549_ == 0)
{
v___y_3556_ = v_nondep_3549_;
goto v___jp_3555_;
}
else
{
if (v_generalizeNondepLet_3523_ == 0)
{
v___y_3556_ = v_generalizeNondepLet_3523_;
goto v___jp_3555_;
}
else
{
uint8_t v___x_3560_; 
lean_dec_ref(v_value_3548_);
v___x_3560_ = 0;
v_n_3531_ = v_userName_3546_;
v_ty_3532_ = v_type_3547_;
v_bi_3533_ = v___x_3560_;
goto v___jp_3530_;
}
}
v___jp_3550_:
{
lean_object* v_ty_3551_; lean_object* v_val_3552_; lean_object* v___x_3553_; 
v_ty_3551_ = lean_expr_abstract_range(v_type_3547_, v_n_3529_, v_xs_3520_);
lean_dec_ref(v_type_3547_);
v_val_3552_ = lean_expr_abstract_range(v_value_3548_, v_n_3529_, v_xs_3520_);
lean_dec_ref(v_value_3548_);
v___x_3553_ = l_Lean_Expr_letE___override(v_userName_3546_, v_ty_3551_, v_val_3552_, v_x_3525_, v_nondep_3549_);
v_x_3524_ = v_n_3529_;
v_x_3525_ = v___x_3553_;
goto _start;
}
v___jp_3555_:
{
if (v_usedLetOnly_3522_ == 0)
{
goto v___jp_3550_;
}
else
{
if (v___y_3556_ == 0)
{
uint8_t v___x_3557_; 
v___x_3557_ = lean_expr_has_loose_bvar(v_x_3525_, v_zero_3526_);
if (v___x_3557_ == 0)
{
lean_object* v___x_3558_; 
lean_dec_ref(v_value_3548_);
lean_dec_ref(v_type_3547_);
lean_dec(v_userName_3546_);
v___x_3558_ = lean_expr_lower_loose_bvars(v_x_3525_, v_one_3528_, v_one_3528_);
lean_dec_ref(v_x_3525_);
v_x_3524_ = v_n_3529_;
v_x_3525_ = v___x_3558_;
goto _start;
}
else
{
goto v___jp_3550_;
}
}
else
{
goto v___jp_3550_;
}
}
}
}
}
v___jp_3530_:
{
lean_object* v_ty_3534_; lean_object* v___x_3535_; 
v_ty_3534_ = lean_expr_abstract_range(v_ty_3532_, v_n_3529_, v_xs_3520_);
lean_dec_ref(v_ty_3532_);
v___x_3535_ = l_Lean_mkForall(v_n_3531_, v_bi_3533_, v_ty_3534_, v_x_3525_);
v_x_3524_ = v_n_3529_;
v_x_3525_ = v___x_3535_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0___boxed(lean_object* v_xs_3561_, lean_object* v_lctx_3562_, lean_object* v_usedLetOnly_3563_, lean_object* v_generalizeNondepLet_3564_, lean_object* v_x_3565_, lean_object* v_x_3566_){
_start:
{
uint8_t v_usedLetOnly_boxed_3567_; uint8_t v_generalizeNondepLet_boxed_3568_; lean_object* v_res_3569_; 
v_usedLetOnly_boxed_3567_ = lean_unbox(v_usedLetOnly_3563_);
v_generalizeNondepLet_boxed_3568_ = lean_unbox(v_generalizeNondepLet_3564_);
v_res_3569_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3561_, v_lctx_3562_, v_usedLetOnly_boxed_3567_, v_generalizeNondepLet_boxed_3568_, v_x_3565_, v_x_3566_);
lean_dec_ref(v_xs_3561_);
return v_res_3569_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(lean_object* v_xs_3570_, lean_object* v_lctx_3571_, uint8_t v_usedLetOnly_3572_, uint8_t v_generalizeNondepLet_3573_, lean_object* v_x_3574_, lean_object* v_x_3575_){
_start:
{
lean_object* v_zero_3576_; uint8_t v_isZero_3577_; 
v_zero_3576_ = lean_unsigned_to_nat(0u);
v_isZero_3577_ = lean_nat_dec_eq(v_x_3574_, v_zero_3576_);
if (v_isZero_3577_ == 1)
{
lean_dec_ref(v_lctx_3571_);
return v_x_3575_;
}
else
{
lean_object* v_one_3578_; lean_object* v_n_3579_; lean_object* v_n_3581_; lean_object* v_ty_3582_; uint8_t v_bi_3583_; lean_object* v_x_3587_; lean_object* v___x_3588_; 
v_one_3578_ = lean_unsigned_to_nat(1u);
v_n_3579_ = lean_nat_sub(v_x_3574_, v_one_3578_);
v_x_3587_ = lean_array_fget_borrowed(v_xs_3570_, v_n_3579_);
lean_inc_ref(v_lctx_3571_);
v___x_3588_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3571_, v_x_3587_);
if (lean_obj_tag(v___x_3588_) == 0)
{
lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; 
lean_dec_ref(v_x_3575_);
v___x_3589_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3590_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3589_);
v___x_3591_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3570_, v_lctx_3571_, v_usedLetOnly_3572_, v_generalizeNondepLet_3573_, v_n_3579_, v___x_3590_);
return v___x_3591_;
}
else
{
lean_object* v_val_3592_; 
v_val_3592_ = lean_ctor_get(v___x_3588_, 0);
lean_inc(v_val_3592_);
lean_dec_ref_known(v___x_3588_, 1);
if (lean_obj_tag(v_val_3592_) == 0)
{
lean_object* v_userName_3593_; lean_object* v_type_3594_; uint8_t v_bi_3595_; 
v_userName_3593_ = lean_ctor_get(v_val_3592_, 2);
lean_inc(v_userName_3593_);
v_type_3594_ = lean_ctor_get(v_val_3592_, 3);
lean_inc_ref(v_type_3594_);
v_bi_3595_ = lean_ctor_get_uint8(v_val_3592_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3592_, 4);
v_n_3581_ = v_userName_3593_;
v_ty_3582_ = v_type_3594_;
v_bi_3583_ = v_bi_3595_;
goto v___jp_3580_;
}
else
{
lean_object* v_userName_3596_; lean_object* v_type_3597_; lean_object* v_value_3598_; uint8_t v_nondep_3599_; uint8_t v___y_3606_; 
v_userName_3596_ = lean_ctor_get(v_val_3592_, 2);
lean_inc(v_userName_3596_);
v_type_3597_ = lean_ctor_get(v_val_3592_, 3);
lean_inc_ref(v_type_3597_);
v_value_3598_ = lean_ctor_get(v_val_3592_, 4);
lean_inc_ref(v_value_3598_);
v_nondep_3599_ = lean_ctor_get_uint8(v_val_3592_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3592_, 5);
if (v_nondep_3599_ == 0)
{
v___y_3606_ = v_nondep_3599_;
goto v___jp_3605_;
}
else
{
if (v_generalizeNondepLet_3573_ == 0)
{
v___y_3606_ = v_generalizeNondepLet_3573_;
goto v___jp_3605_;
}
else
{
uint8_t v___x_3610_; 
lean_dec_ref(v_value_3598_);
v___x_3610_ = 0;
v_n_3581_ = v_userName_3596_;
v_ty_3582_ = v_type_3597_;
v_bi_3583_ = v___x_3610_;
goto v___jp_3580_;
}
}
v___jp_3600_:
{
lean_object* v_ty_3601_; lean_object* v_val_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; 
v_ty_3601_ = lean_expr_abstract_range(v_type_3597_, v_n_3579_, v_xs_3570_);
lean_dec_ref(v_type_3597_);
v_val_3602_ = lean_expr_abstract_range(v_value_3598_, v_n_3579_, v_xs_3570_);
lean_dec_ref(v_value_3598_);
v___x_3603_ = l_Lean_Expr_letE___override(v_userName_3596_, v_ty_3601_, v_val_3602_, v_x_3575_, v_nondep_3599_);
v___x_3604_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3570_, v_lctx_3571_, v_usedLetOnly_3572_, v_generalizeNondepLet_3573_, v_n_3579_, v___x_3603_);
return v___x_3604_;
}
v___jp_3605_:
{
if (v_usedLetOnly_3572_ == 0)
{
goto v___jp_3600_;
}
else
{
if (v___y_3606_ == 0)
{
uint8_t v___x_3607_; 
v___x_3607_ = lean_expr_has_loose_bvar(v_x_3575_, v_zero_3576_);
if (v___x_3607_ == 0)
{
lean_object* v___x_3608_; lean_object* v___x_3609_; 
lean_dec_ref(v_value_3598_);
lean_dec_ref(v_type_3597_);
lean_dec(v_userName_3596_);
v___x_3608_ = lean_expr_lower_loose_bvars(v_x_3575_, v_one_3578_, v_one_3578_);
lean_dec_ref(v_x_3575_);
v___x_3609_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3570_, v_lctx_3571_, v_usedLetOnly_3572_, v_generalizeNondepLet_3573_, v_n_3579_, v___x_3608_);
return v___x_3609_;
}
else
{
goto v___jp_3600_;
}
}
else
{
goto v___jp_3600_;
}
}
}
}
}
v___jp_3580_:
{
lean_object* v_ty_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; 
v_ty_3584_ = lean_expr_abstract_range(v_ty_3582_, v_n_3579_, v_xs_3570_);
lean_dec_ref(v_ty_3582_);
v___x_3585_ = l_Lean_mkForall(v_n_3581_, v_bi_3583_, v_ty_3584_, v_x_3575_);
v___x_3586_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3570_, v_lctx_3571_, v_usedLetOnly_3572_, v_generalizeNondepLet_3573_, v_n_3579_, v___x_3585_);
return v___x_3586_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0___boxed(lean_object* v_xs_3611_, lean_object* v_lctx_3612_, lean_object* v_usedLetOnly_3613_, lean_object* v_generalizeNondepLet_3614_, lean_object* v_x_3615_, lean_object* v_x_3616_){
_start:
{
uint8_t v_usedLetOnly_boxed_3617_; uint8_t v_generalizeNondepLet_boxed_3618_; lean_object* v_res_3619_; 
v_usedLetOnly_boxed_3617_ = lean_unbox(v_usedLetOnly_3613_);
v_generalizeNondepLet_boxed_3618_ = lean_unbox(v_generalizeNondepLet_3614_);
v_res_3619_ = l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(v_xs_3611_, v_lctx_3612_, v_usedLetOnly_boxed_3617_, v_generalizeNondepLet_boxed_3618_, v_x_3615_, v_x_3616_);
lean_dec(v_x_3615_);
lean_dec_ref(v_xs_3611_);
return v_res_3619_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkForall(lean_object* v_lctx_3620_, lean_object* v_xs_3621_, lean_object* v_b_3622_, uint8_t v_usedLetOnly_3623_, uint8_t v_generalizeNondepLet_3624_){
_start:
{
lean_object* v_b_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; 
v_b_3625_ = lean_expr_abstract(v_b_3622_, v_xs_3621_);
v___x_3626_ = lean_array_get_size(v_xs_3621_);
v___x_3627_ = l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(v_xs_3621_, v_lctx_3620_, v_usedLetOnly_3623_, v_generalizeNondepLet_3624_, v___x_3626_, v_b_3625_);
return v___x_3627_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkForall___boxed(lean_object* v_lctx_3628_, lean_object* v_xs_3629_, lean_object* v_b_3630_, lean_object* v_usedLetOnly_3631_, lean_object* v_generalizeNondepLet_3632_){
_start:
{
uint8_t v_usedLetOnly_boxed_3633_; uint8_t v_generalizeNondepLet_boxed_3634_; lean_object* v_res_3635_; 
v_usedLetOnly_boxed_3633_ = lean_unbox(v_usedLetOnly_3631_);
v_generalizeNondepLet_boxed_3634_ = lean_unbox(v_generalizeNondepLet_3632_);
v_res_3635_ = l_Lean_LocalContext_mkForall(v_lctx_3628_, v_xs_3629_, v_b_3630_, v_usedLetOnly_boxed_3633_, v_generalizeNondepLet_boxed_3634_);
lean_dec_ref(v_b_3630_);
lean_dec_ref(v_xs_3629_);
return v_res_3635_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM___redArg___lam__0(lean_object* v_toPure_3636_, lean_object* v_p_3637_, lean_object* v_d_3638_){
_start:
{
if (lean_obj_tag(v_d_3638_) == 0)
{
uint8_t v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; 
lean_dec(v_p_3637_);
v___x_3639_ = 0;
v___x_3640_ = lean_box(v___x_3639_);
v___x_3641_ = lean_apply_2(v_toPure_3636_, lean_box(0), v___x_3640_);
return v___x_3641_;
}
else
{
lean_object* v_val_3642_; lean_object* v___x_3643_; 
lean_dec(v_toPure_3636_);
v_val_3642_ = lean_ctor_get(v_d_3638_, 0);
lean_inc(v_val_3642_);
lean_dec_ref_known(v_d_3638_, 1);
v___x_3643_ = lean_apply_1(v_p_3637_, v_val_3642_);
return v___x_3643_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM___redArg(lean_object* v_inst_3644_, lean_object* v_lctx_3645_, lean_object* v_p_3646_){
_start:
{
lean_object* v_toApplicative_3647_; lean_object* v_decls_3648_; lean_object* v_toPure_3649_; lean_object* v___f_3650_; lean_object* v___x_3651_; 
v_toApplicative_3647_ = lean_ctor_get(v_inst_3644_, 0);
v_decls_3648_ = lean_ctor_get(v_lctx_3645_, 1);
lean_inc_ref(v_decls_3648_);
lean_dec_ref(v_lctx_3645_);
v_toPure_3649_ = lean_ctor_get(v_toApplicative_3647_, 1);
lean_inc(v_toPure_3649_);
v___f_3650_ = lean_alloc_closure((void*)(l_Lean_LocalContext_anyM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3650_, 0, v_toPure_3649_);
lean_closure_set(v___f_3650_, 1, v_p_3646_);
v___x_3651_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3644_, v_decls_3648_, v___f_3650_);
return v___x_3651_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM(lean_object* v_m_3652_, lean_object* v_inst_3653_, lean_object* v_lctx_3654_, lean_object* v_p_3655_){
_start:
{
lean_object* v_toApplicative_3656_; lean_object* v_decls_3657_; lean_object* v_toPure_3658_; lean_object* v___f_3659_; lean_object* v___x_3660_; 
v_toApplicative_3656_ = lean_ctor_get(v_inst_3653_, 0);
v_decls_3657_ = lean_ctor_get(v_lctx_3654_, 1);
lean_inc_ref(v_decls_3657_);
lean_dec_ref(v_lctx_3654_);
v_toPure_3658_ = lean_ctor_get(v_toApplicative_3656_, 1);
lean_inc(v_toPure_3658_);
v___f_3659_ = lean_alloc_closure((void*)(l_Lean_LocalContext_anyM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3659_, 0, v_toPure_3658_);
lean_closure_set(v___f_3659_, 1, v_p_3655_);
v___x_3660_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3653_, v_decls_3657_, v___f_3659_);
return v___x_3660_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__0(lean_object* v_toPure_3661_, uint8_t v_b_3662_){
_start:
{
if (v_b_3662_ == 0)
{
uint8_t v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; 
v___x_3663_ = 1;
v___x_3664_ = lean_box(v___x_3663_);
v___x_3665_ = lean_apply_2(v_toPure_3661_, lean_box(0), v___x_3664_);
return v___x_3665_;
}
else
{
uint8_t v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; 
v___x_3666_ = 0;
v___x_3667_ = lean_box(v___x_3666_);
v___x_3668_ = lean_apply_2(v_toPure_3661_, lean_box(0), v___x_3667_);
return v___x_3668_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__0___boxed(lean_object* v_toPure_3669_, lean_object* v_b_3670_){
_start:
{
uint8_t v_b_boxed_3671_; lean_object* v_res_3672_; 
v_b_boxed_3671_ = lean_unbox(v_b_3670_);
v_res_3672_ = l_Lean_LocalContext_allM___redArg___lam__0(v_toPure_3669_, v_b_boxed_3671_);
return v_res_3672_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__2(lean_object* v_toPure_3673_, lean_object* v_toBind_3674_, lean_object* v___f_3675_, lean_object* v_p_3676_, lean_object* v_v_3677_){
_start:
{
if (lean_obj_tag(v_v_3677_) == 0)
{
uint8_t v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; 
lean_dec(v_p_3676_);
v___x_3678_ = 1;
v___x_3679_ = lean_box(v___x_3678_);
v___x_3680_ = lean_apply_2(v_toPure_3673_, lean_box(0), v___x_3679_);
v___x_3681_ = lean_apply_4(v_toBind_3674_, lean_box(0), lean_box(0), v___x_3680_, v___f_3675_);
return v___x_3681_;
}
else
{
lean_object* v_val_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; 
lean_dec(v_toPure_3673_);
v_val_3682_ = lean_ctor_get(v_v_3677_, 0);
lean_inc(v_val_3682_);
lean_dec_ref_known(v_v_3677_, 1);
v___x_3683_ = lean_apply_1(v_p_3676_, v_val_3682_);
v___x_3684_ = lean_apply_4(v_toBind_3674_, lean_box(0), lean_box(0), v___x_3683_, v___f_3675_);
return v___x_3684_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg(lean_object* v_inst_3685_, lean_object* v_lctx_3686_, lean_object* v_p_3687_){
_start:
{
lean_object* v_toApplicative_3688_; lean_object* v_decls_3689_; lean_object* v_toBind_3690_; lean_object* v_toPure_3691_; lean_object* v___f_3692_; lean_object* v___f_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; 
v_toApplicative_3688_ = lean_ctor_get(v_inst_3685_, 0);
v_decls_3689_ = lean_ctor_get(v_lctx_3686_, 1);
lean_inc_ref(v_decls_3689_);
lean_dec_ref(v_lctx_3686_);
v_toBind_3690_ = lean_ctor_get(v_inst_3685_, 1);
lean_inc_n(v_toBind_3690_, 2);
v_toPure_3691_ = lean_ctor_get(v_toApplicative_3688_, 1);
lean_inc_n(v_toPure_3691_, 2);
v___f_3692_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3692_, 0, v_toPure_3691_);
lean_inc_ref(v___f_3692_);
v___f_3693_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3693_, 0, v_toPure_3691_);
lean_closure_set(v___f_3693_, 1, v_toBind_3690_);
lean_closure_set(v___f_3693_, 2, v___f_3692_);
lean_closure_set(v___f_3693_, 3, v_p_3687_);
v___x_3694_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3685_, v_decls_3689_, v___f_3693_);
v___x_3695_ = lean_apply_4(v_toBind_3690_, lean_box(0), lean_box(0), v___x_3694_, v___f_3692_);
return v___x_3695_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM(lean_object* v_m_3696_, lean_object* v_inst_3697_, lean_object* v_lctx_3698_, lean_object* v_p_3699_){
_start:
{
lean_object* v_toApplicative_3700_; lean_object* v_decls_3701_; lean_object* v_toBind_3702_; lean_object* v_toPure_3703_; lean_object* v___f_3704_; lean_object* v___f_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
v_toApplicative_3700_ = lean_ctor_get(v_inst_3697_, 0);
v_decls_3701_ = lean_ctor_get(v_lctx_3698_, 1);
lean_inc_ref(v_decls_3701_);
lean_dec_ref(v_lctx_3698_);
v_toBind_3702_ = lean_ctor_get(v_inst_3697_, 1);
lean_inc_n(v_toBind_3702_, 2);
v_toPure_3703_ = lean_ctor_get(v_toApplicative_3700_, 1);
lean_inc_n(v_toPure_3703_, 2);
v___f_3704_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3704_, 0, v_toPure_3703_);
lean_inc_ref(v___f_3704_);
v___f_3705_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3705_, 0, v_toPure_3703_);
lean_closure_set(v___f_3705_, 1, v_toBind_3702_);
lean_closure_set(v___f_3705_, 2, v___f_3704_);
lean_closure_set(v___f_3705_, 3, v_p_3699_);
v___x_3706_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3697_, v_decls_3701_, v___f_3705_);
v___x_3707_ = lean_apply_4(v_toBind_3702_, lean_box(0), lean_box(0), v___x_3706_, v___f_3704_);
return v___x_3707_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_any___lam__0(lean_object* v_p_3708_, lean_object* v_d_3709_){
_start:
{
if (lean_obj_tag(v_d_3709_) == 0)
{
uint8_t v___x_3710_; 
lean_dec_ref(v_p_3708_);
v___x_3710_ = 0;
return v___x_3710_;
}
else
{
lean_object* v_val_3711_; lean_object* v___x_3712_; uint8_t v___x_3713_; 
v_val_3711_ = lean_ctor_get(v_d_3709_, 0);
lean_inc(v_val_3711_);
lean_dec_ref_known(v_d_3709_, 1);
v___x_3712_ = lean_apply_1(v_p_3708_, v_val_3711_);
v___x_3713_ = lean_unbox(v___x_3712_);
return v___x_3713_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_any___lam__0___boxed(lean_object* v_p_3714_, lean_object* v_d_3715_){
_start:
{
uint8_t v_res_3716_; lean_object* v_r_3717_; 
v_res_3716_ = l_Lean_LocalContext_any___lam__0(v_p_3714_, v_d_3715_);
v_r_3717_ = lean_box(v_res_3716_);
return v_r_3717_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_any(lean_object* v_lctx_3718_, lean_object* v_p_3719_){
_start:
{
lean_object* v___x_3720_; lean_object* v_decls_3721_; lean_object* v___f_3722_; lean_object* v___x_3723_; uint8_t v___x_3724_; 
v___x_3720_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v_decls_3721_ = lean_ctor_get(v_lctx_3718_, 1);
lean_inc_ref(v_decls_3721_);
lean_dec_ref(v_lctx_3718_);
v___f_3722_ = lean_alloc_closure((void*)(l_Lean_LocalContext_any___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3722_, 0, v_p_3719_);
v___x_3723_ = l_Lean_PersistentArray_anyM___redArg(v___x_3720_, v_decls_3721_, v___f_3722_);
v___x_3724_ = lean_unbox(v___x_3723_);
lean_dec(v___x_3723_);
return v___x_3724_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_any___boxed(lean_object* v_lctx_3725_, lean_object* v_p_3726_){
_start:
{
uint8_t v_res_3727_; lean_object* v_r_3728_; 
v_res_3727_ = l_Lean_LocalContext_any(v_lctx_3725_, v_p_3726_);
v_r_3728_ = lean_box(v_res_3727_);
return v_r_3728_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_all___lam__0(lean_object* v_p_3729_, lean_object* v_v_3730_){
_start:
{
if (lean_obj_tag(v_v_3730_) == 0)
{
uint8_t v___x_3731_; 
lean_dec_ref(v_p_3729_);
v___x_3731_ = 0;
return v___x_3731_;
}
else
{
lean_object* v_val_3732_; lean_object* v___x_3733_; uint8_t v___x_3734_; 
v_val_3732_ = lean_ctor_get(v_v_3730_, 0);
lean_inc(v_val_3732_);
lean_dec_ref_known(v_v_3730_, 1);
v___x_3733_ = lean_apply_1(v_p_3729_, v_val_3732_);
v___x_3734_ = lean_unbox(v___x_3733_);
if (v___x_3734_ == 0)
{
uint8_t v___x_3735_; 
v___x_3735_ = 1;
return v___x_3735_;
}
else
{
uint8_t v___x_3736_; 
v___x_3736_ = 0;
return v___x_3736_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_all___lam__0___boxed(lean_object* v_p_3737_, lean_object* v_v_3738_){
_start:
{
uint8_t v_res_3739_; lean_object* v_r_3740_; 
v_res_3739_ = l_Lean_LocalContext_all___lam__0(v_p_3737_, v_v_3738_);
v_r_3740_ = lean_box(v_res_3739_);
return v_r_3740_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_all(lean_object* v_lctx_3741_, lean_object* v_p_3742_){
_start:
{
lean_object* v___x_3743_; lean_object* v_decls_3744_; lean_object* v___f_3745_; lean_object* v___x_3746_; uint8_t v___x_3747_; 
v___x_3743_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v_decls_3744_ = lean_ctor_get(v_lctx_3741_, 1);
lean_inc_ref(v_decls_3744_);
lean_dec_ref(v_lctx_3741_);
v___f_3745_ = lean_alloc_closure((void*)(l_Lean_LocalContext_all___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3745_, 0, v_p_3742_);
v___x_3746_ = l_Lean_PersistentArray_anyM___redArg(v___x_3743_, v_decls_3744_, v___f_3745_);
v___x_3747_ = lean_unbox(v___x_3746_);
lean_dec(v___x_3746_);
if (v___x_3747_ == 0)
{
uint8_t v___x_3748_; 
v___x_3748_ = 1;
return v___x_3748_;
}
else
{
uint8_t v___x_3749_; 
v___x_3749_ = 0;
return v___x_3749_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_all___boxed(lean_object* v_lctx_3750_, lean_object* v_p_3751_){
_start:
{
uint8_t v_res_3752_; lean_object* v_r_3753_; 
v_res_3752_ = l_Lean_LocalContext_all(v_lctx_3750_, v_p_3751_);
v_r_3753_ = lean_box(v_res_3752_);
return v_r_3753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(lean_object* v_i_3754_, lean_object* v_a_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_){
_start:
{
lean_object* v_zero_3758_; uint8_t v_isZero_3759_; 
v_zero_3758_ = lean_unsigned_to_nat(0u);
v_isZero_3759_ = lean_nat_dec_eq(v_i_3754_, v_zero_3758_);
if (v_isZero_3759_ == 1)
{
lean_object* v___x_3760_; lean_object* v___x_3761_; 
lean_dec(v_i_3754_);
v___x_3760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3760_, 0, v_a_3755_);
lean_ctor_set(v___x_3760_, 1, v___y_3756_);
v___x_3761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3761_, 0, v___x_3760_);
lean_ctor_set(v___x_3761_, 1, v___y_3757_);
return v___x_3761_;
}
else
{
lean_object* v_decls_3762_; lean_object* v_size_3763_; lean_object* v_one_3764_; lean_object* v_n_3765_; lean_object* v___y_3767_; lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3774_; lean_object* v___y_3775_; lean_object* v___y_3782_; lean_object* v___y_3783_; uint8_t v___y_3784_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3794_; lean_object* v___x_3798_; uint8_t v___x_3799_; 
v_decls_3762_ = lean_ctor_get(v_a_3755_, 1);
v_size_3763_ = lean_ctor_get(v_decls_3762_, 2);
v_one_3764_ = lean_unsigned_to_nat(1u);
v_n_3765_ = lean_nat_sub(v_i_3754_, v_one_3764_);
lean_dec(v_i_3754_);
v___x_3798_ = lean_box(0);
v___x_3799_ = lean_nat_dec_lt(v_n_3765_, v_size_3763_);
if (v___x_3799_ == 0)
{
lean_object* v___x_3800_; 
v___x_3800_ = l_outOfBounds___redArg(v___x_3798_);
v___y_3794_ = v___x_3800_;
goto v___jp_3793_;
}
else
{
lean_object* v___x_3801_; 
v___x_3801_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3798_, v_decls_3762_, v_n_3765_);
v___y_3794_ = v___x_3801_;
goto v___jp_3793_;
}
v___jp_3766_:
{
lean_object* v___x_3771_; 
v___x_3771_ = l_Lean_LocalContext_setUserName(v_a_3755_, v___y_3770_, v___y_3769_);
v_i_3754_ = v_n_3765_;
v_a_3755_ = v___x_3771_;
v___y_3756_ = v___y_3768_;
v___y_3757_ = v___y_3767_;
goto _start;
}
v___jp_3773_:
{
lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v_fst_3778_; lean_object* v_snd_3779_; lean_object* v_fvarId_3780_; 
lean_inc(v___y_3774_);
v___x_3776_ = l_Lean_NameSet_insert(v___y_3756_, v___y_3774_);
v___x_3777_ = l_Lean_sanitizeName(v___y_3774_, v___y_3757_);
v_fst_3778_ = lean_ctor_get(v___x_3777_, 0);
lean_inc(v_fst_3778_);
v_snd_3779_ = lean_ctor_get(v___x_3777_, 1);
lean_inc(v_snd_3779_);
lean_dec_ref(v___x_3777_);
v_fvarId_3780_ = lean_ctor_get(v___y_3775_, 1);
lean_inc(v_fvarId_3780_);
lean_dec_ref(v___y_3775_);
v___y_3767_ = v_snd_3779_;
v___y_3768_ = v___x_3776_;
v___y_3769_ = v_fst_3778_;
v___y_3770_ = v_fvarId_3780_;
goto v___jp_3766_;
}
v___jp_3781_:
{
if (v___y_3784_ == 0)
{
lean_object* v___x_3785_; 
lean_dec_ref(v___y_3783_);
v___x_3785_ = l_Lean_NameSet_insert(v___y_3756_, v___y_3782_);
v_i_3754_ = v_n_3765_;
v___y_3756_ = v___x_3785_;
goto _start;
}
else
{
v___y_3774_ = v___y_3782_;
v___y_3775_ = v___y_3783_;
goto v___jp_3773_;
}
}
v___jp_3787_:
{
uint8_t v___x_3790_; 
v___x_3790_ = l_Lean_Name_hasMacroScopes(v___y_3789_);
if (v___x_3790_ == 0)
{
lean_object* v_userName_3791_; uint8_t v___x_3792_; 
v_userName_3791_ = lean_ctor_get(v___y_3788_, 2);
v___x_3792_ = l_Lean_NameSet_contains(v___y_3756_, v_userName_3791_);
v___y_3782_ = v___y_3789_;
v___y_3783_ = v___y_3788_;
v___y_3784_ = v___x_3792_;
goto v___jp_3781_;
}
else
{
v___y_3774_ = v___y_3789_;
v___y_3775_ = v___y_3788_;
goto v___jp_3773_;
}
}
v___jp_3793_:
{
if (lean_obj_tag(v___y_3794_) == 0)
{
v_i_3754_ = v_n_3765_;
goto _start;
}
else
{
lean_object* v_val_3796_; lean_object* v_userName_3797_; 
v_val_3796_ = lean_ctor_get(v___y_3794_, 0);
lean_inc(v_val_3796_);
lean_dec_ref_known(v___y_3794_, 1);
v_userName_3797_ = lean_ctor_get(v_val_3796_, 2);
lean_inc(v_userName_3797_);
v___y_3788_ = v_val_3796_;
v___y_3789_ = v_userName_3797_;
goto v___jp_3787_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_sanitizeNames(lean_object* v_lctx_3802_, lean_object* v_a_3803_){
_start:
{
lean_object* v_options_3804_; uint8_t v___x_3805_; 
v_options_3804_ = lean_ctor_get(v_a_3803_, 0);
v___x_3805_ = l_Lean_getSanitizeNames(v_options_3804_);
if (v___x_3805_ == 0)
{
lean_object* v___x_3806_; 
v___x_3806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3806_, 0, v_lctx_3802_);
lean_ctor_set(v___x_3806_, 1, v_a_3803_);
return v___x_3806_;
}
else
{
lean_object* v_decls_3807_; lean_object* v_size_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v_fst_3811_; lean_object* v_snd_3812_; lean_object* v_fst_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3820_; 
v_decls_3807_ = lean_ctor_get(v_lctx_3802_, 1);
v_size_3808_ = lean_ctor_get(v_decls_3807_, 2);
lean_inc(v_size_3808_);
v___x_3809_ = l_Lean_NameSet_empty;
v___x_3810_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(v_size_3808_, v_lctx_3802_, v___x_3809_, v_a_3803_);
v_fst_3811_ = lean_ctor_get(v___x_3810_, 0);
lean_inc(v_fst_3811_);
v_snd_3812_ = lean_ctor_get(v___x_3810_, 1);
lean_inc(v_snd_3812_);
lean_dec_ref(v___x_3810_);
v_fst_3813_ = lean_ctor_get(v_fst_3811_, 0);
v_isSharedCheck_3820_ = !lean_is_exclusive(v_fst_3811_);
if (v_isSharedCheck_3820_ == 0)
{
lean_object* v_unused_3821_; 
v_unused_3821_ = lean_ctor_get(v_fst_3811_, 1);
lean_dec(v_unused_3821_);
v___x_3815_ = v_fst_3811_;
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_fst_3813_);
lean_dec(v_fst_3811_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v___x_3818_; 
if (v_isShared_3816_ == 0)
{
lean_ctor_set(v___x_3815_, 1, v_snd_3812_);
v___x_3818_ = v___x_3815_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v_fst_3813_);
lean_ctor_set(v_reuseFailAlloc_3819_, 1, v_snd_3812_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0(lean_object* v_n_3822_, lean_object* v_i_3823_, lean_object* v_a_3824_, lean_object* v_a_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_){
_start:
{
lean_object* v___x_3828_; 
v___x_3828_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(v_i_3823_, v_a_3825_, v___y_3826_, v___y_3827_);
return v___x_3828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___boxed(lean_object* v_n_3829_, lean_object* v_i_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_){
_start:
{
lean_object* v_res_3835_; 
v_res_3835_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0(v_n_3829_, v_i_3830_, v_a_3831_, v_a_3832_, v___y_3833_, v___y_3834_);
lean_dec(v_n_3829_);
return v_res_3835_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getRoundtrippingUserName_x3f(lean_object* v_lctx_3836_, lean_object* v_fvarId_3837_){
_start:
{
lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___x_3850_; 
lean_inc_ref(v_lctx_3836_);
v___x_3850_ = lean_local_ctx_find(v_lctx_3836_, v_fvarId_3837_);
if (lean_obj_tag(v___x_3850_) == 0)
{
lean_object* v___x_3851_; 
lean_dec_ref(v_lctx_3836_);
v___x_3851_ = lean_box(0);
return v___x_3851_;
}
else
{
lean_object* v_val_3852_; lean_object* v___y_3854_; lean_object* v_userName_3859_; 
v_val_3852_ = lean_ctor_get(v___x_3850_, 0);
lean_inc(v_val_3852_);
lean_dec_ref_known(v___x_3850_, 1);
v_userName_3859_ = lean_ctor_get(v_val_3852_, 2);
lean_inc(v_userName_3859_);
v___y_3854_ = v_userName_3859_;
goto v___jp_3853_;
v___jp_3853_:
{
lean_object* v___x_3855_; 
v___x_3855_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_3836_, v___y_3854_);
lean_dec_ref(v_lctx_3836_);
if (lean_obj_tag(v___x_3855_) == 0)
{
lean_object* v___x_3856_; 
lean_dec(v___y_3854_);
lean_dec(v_val_3852_);
v___x_3856_ = lean_box(0);
return v___x_3856_;
}
else
{
lean_object* v_val_3857_; lean_object* v_fvarId_3858_; 
v_val_3857_ = lean_ctor_get(v___x_3855_, 0);
lean_inc(v_val_3857_);
lean_dec_ref_known(v___x_3855_, 1);
v_fvarId_3858_ = lean_ctor_get(v_val_3852_, 1);
lean_inc(v_fvarId_3858_);
lean_dec(v_val_3852_);
v___y_3846_ = v_val_3857_;
v___y_3847_ = v___y_3854_;
v___y_3848_ = v_fvarId_3858_;
goto v___jp_3845_;
}
}
}
v___jp_3838_:
{
uint8_t v___x_3842_; 
v___x_3842_ = l_Lean_instBEqFVarId_beq(v___y_3840_, v___y_3841_);
lean_dec(v___y_3841_);
lean_dec(v___y_3840_);
if (v___x_3842_ == 0)
{
lean_object* v___x_3843_; 
lean_dec(v___y_3839_);
v___x_3843_ = lean_box(0);
return v___x_3843_;
}
else
{
lean_object* v___x_3844_; 
v___x_3844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3844_, 0, v___y_3839_);
return v___x_3844_;
}
}
v___jp_3845_:
{
lean_object* v_fvarId_3849_; 
v_fvarId_3849_ = lean_ctor_get(v___y_3846_, 1);
lean_inc(v_fvarId_3849_);
lean_dec_ref(v___y_3846_);
v___y_3839_ = v___y_3847_;
v___y_3840_ = v___y_3848_;
v___y_3841_ = v_fvarId_3849_;
goto v___jp_3838_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(size_t v_sz_3860_, size_t v_i_3861_, lean_object* v_bs_3862_){
_start:
{
uint8_t v___x_3863_; 
v___x_3863_ = lean_usize_dec_lt(v_i_3861_, v_sz_3860_);
if (v___x_3863_ == 0)
{
return v_bs_3862_;
}
else
{
lean_object* v_v_3864_; lean_object* v_snd_3865_; lean_object* v___x_3866_; lean_object* v_bs_x27_3867_; size_t v___x_3868_; size_t v___x_3869_; lean_object* v___x_3870_; 
v_v_3864_ = lean_array_uget_borrowed(v_bs_3862_, v_i_3861_);
v_snd_3865_ = lean_ctor_get(v_v_3864_, 1);
lean_inc(v_snd_3865_);
v___x_3866_ = lean_unsigned_to_nat(0u);
v_bs_x27_3867_ = lean_array_uset(v_bs_3862_, v_i_3861_, v___x_3866_);
v___x_3868_ = ((size_t)1ULL);
v___x_3869_ = lean_usize_add(v_i_3861_, v___x_3868_);
v___x_3870_ = lean_array_uset(v_bs_x27_3867_, v_i_3861_, v_snd_3865_);
v_i_3861_ = v___x_3869_;
v_bs_3862_ = v___x_3870_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0___boxed(lean_object* v_sz_3872_, lean_object* v_i_3873_, lean_object* v_bs_3874_){
_start:
{
size_t v_sz_boxed_3875_; size_t v_i_boxed_3876_; lean_object* v_res_3877_; 
v_sz_boxed_3875_ = lean_unbox_usize(v_sz_3872_);
lean_dec(v_sz_3872_);
v_i_boxed_3876_ = lean_unbox_usize(v_i_3873_);
lean_dec(v_i_3873_);
v_res_3877_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(v_sz_boxed_3875_, v_i_boxed_3876_, v_bs_3874_);
return v_res_3877_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(lean_object* v_lctx_3878_, size_t v_sz_3879_, size_t v_i_3880_, lean_object* v_bs_3881_){
_start:
{
uint8_t v___x_3882_; 
v___x_3882_ = lean_usize_dec_lt(v_i_3880_, v_sz_3879_);
if (v___x_3882_ == 0)
{
return v_bs_3881_;
}
else
{
lean_object* v_fvarIdToDecl_3883_; lean_object* v_v_3884_; lean_object* v___x_3885_; lean_object* v_bs_x27_3886_; lean_object* v___y_3888_; lean_object* v___x_3893_; 
v_fvarIdToDecl_3883_ = lean_ctor_get(v_lctx_3878_, 0);
v_v_3884_ = lean_array_uget(v_bs_3881_, v_i_3880_);
v___x_3885_ = lean_unsigned_to_nat(0u);
v_bs_x27_3886_ = lean_array_uset(v_bs_3881_, v_i_3880_, v___x_3885_);
v___x_3893_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_fvarIdToDecl_3883_, v_v_3884_);
if (lean_obj_tag(v___x_3893_) == 0)
{
lean_object* v___x_3894_; 
v___x_3894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3894_, 0, v___x_3885_);
lean_ctor_set(v___x_3894_, 1, v_v_3884_);
v___y_3888_ = v___x_3894_;
goto v___jp_3887_;
}
else
{
lean_object* v_val_3895_; lean_object* v_index_3896_; lean_object* v___x_3897_; 
v_val_3895_ = lean_ctor_get(v___x_3893_, 0);
lean_inc(v_val_3895_);
lean_dec_ref_known(v___x_3893_, 1);
v_index_3896_ = lean_ctor_get(v_val_3895_, 0);
lean_inc(v_index_3896_);
lean_dec(v_val_3895_);
v___x_3897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3897_, 0, v_index_3896_);
lean_ctor_set(v___x_3897_, 1, v_v_3884_);
v___y_3888_ = v___x_3897_;
goto v___jp_3887_;
}
v___jp_3887_:
{
size_t v___x_3889_; size_t v___x_3890_; lean_object* v___x_3891_; 
v___x_3889_ = ((size_t)1ULL);
v___x_3890_ = lean_usize_add(v_i_3880_, v___x_3889_);
v___x_3891_ = lean_array_uset(v_bs_x27_3886_, v_i_3880_, v___y_3888_);
v_i_3880_ = v___x_3890_;
v_bs_3881_ = v___x_3891_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1___boxed(lean_object* v_lctx_3898_, lean_object* v_sz_3899_, lean_object* v_i_3900_, lean_object* v_bs_3901_){
_start:
{
size_t v_sz_boxed_3902_; size_t v_i_boxed_3903_; lean_object* v_res_3904_; 
v_sz_boxed_3902_ = lean_unbox_usize(v_sz_3899_);
lean_dec(v_sz_3899_);
v_i_boxed_3903_ = lean_unbox_usize(v_i_3900_);
lean_dec(v_i_3900_);
v_res_3904_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(v_lctx_3898_, v_sz_boxed_3902_, v_i_boxed_3903_, v_bs_3901_);
lean_dec_ref(v_lctx_3898_);
return v_res_3904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(lean_object* v_hi_3905_, lean_object* v_pivot_3906_, lean_object* v_as_3907_, lean_object* v_i_3908_, lean_object* v_k_3909_){
_start:
{
uint8_t v___x_3910_; 
v___x_3910_ = lean_nat_dec_lt(v_k_3909_, v_hi_3905_);
if (v___x_3910_ == 0)
{
lean_object* v___x_3911_; lean_object* v___x_3912_; 
lean_dec(v_k_3909_);
v___x_3911_ = lean_array_fswap(v_as_3907_, v_i_3908_, v_hi_3905_);
v___x_3912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3912_, 0, v_i_3908_);
lean_ctor_set(v___x_3912_, 1, v___x_3911_);
return v___x_3912_;
}
else
{
lean_object* v___x_3913_; lean_object* v_fst_3914_; lean_object* v_fst_3915_; uint8_t v___x_3916_; 
v___x_3913_ = lean_array_fget_borrowed(v_as_3907_, v_k_3909_);
v_fst_3914_ = lean_ctor_get(v___x_3913_, 0);
v_fst_3915_ = lean_ctor_get(v_pivot_3906_, 0);
v___x_3916_ = lean_nat_dec_lt(v_fst_3914_, v_fst_3915_);
if (v___x_3916_ == 0)
{
lean_object* v___x_3917_; lean_object* v___x_3918_; 
v___x_3917_ = lean_unsigned_to_nat(1u);
v___x_3918_ = lean_nat_add(v_k_3909_, v___x_3917_);
lean_dec(v_k_3909_);
v_k_3909_ = v___x_3918_;
goto _start;
}
else
{
lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; 
v___x_3920_ = lean_array_fswap(v_as_3907_, v_i_3908_, v_k_3909_);
v___x_3921_ = lean_unsigned_to_nat(1u);
v___x_3922_ = lean_nat_add(v_i_3908_, v___x_3921_);
lean_dec(v_i_3908_);
v___x_3923_ = lean_nat_add(v_k_3909_, v___x_3921_);
lean_dec(v_k_3909_);
v_as_3907_ = v___x_3920_;
v_i_3908_ = v___x_3922_;
v_k_3909_ = v___x_3923_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg___boxed(lean_object* v_hi_3925_, lean_object* v_pivot_3926_, lean_object* v_as_3927_, lean_object* v_i_3928_, lean_object* v_k_3929_){
_start:
{
lean_object* v_res_3930_; 
v_res_3930_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(v_hi_3925_, v_pivot_3926_, v_as_3927_, v_i_3928_, v_k_3929_);
lean_dec_ref(v_pivot_3926_);
lean_dec(v_hi_3925_);
return v_res_3930_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(lean_object* v_h_3931_, lean_object* v_i_3932_){
_start:
{
lean_object* v_fst_3933_; lean_object* v_fst_3934_; uint8_t v___x_3935_; 
v_fst_3933_ = lean_ctor_get(v_h_3931_, 0);
v_fst_3934_ = lean_ctor_get(v_i_3932_, 0);
v___x_3935_ = lean_nat_dec_lt(v_fst_3933_, v_fst_3934_);
return v___x_3935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0___boxed(lean_object* v_h_3936_, lean_object* v_i_3937_){
_start:
{
uint8_t v_res_3938_; lean_object* v_r_3939_; 
v_res_3938_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v_h_3936_, v_i_3937_);
lean_dec_ref(v_i_3937_);
lean_dec_ref(v_h_3936_);
v_r_3939_ = lean_box(v_res_3938_);
return v_r_3939_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(lean_object* v_n_3940_, lean_object* v_as_3941_, lean_object* v_lo_3942_, lean_object* v_hi_3943_){
_start:
{
lean_object* v___y_3945_; uint8_t v___x_3955_; 
v___x_3955_ = lean_nat_dec_lt(v_lo_3942_, v_hi_3943_);
if (v___x_3955_ == 0)
{
lean_dec(v_lo_3942_);
return v_as_3941_;
}
else
{
lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v_mid_3958_; lean_object* v___y_3960_; lean_object* v___y_3966_; lean_object* v___x_3971_; lean_object* v___x_3972_; uint8_t v___x_3973_; 
v___x_3956_ = lean_nat_add(v_lo_3942_, v_hi_3943_);
v___x_3957_ = lean_unsigned_to_nat(1u);
v_mid_3958_ = lean_nat_shiftr(v___x_3956_, v___x_3957_);
lean_dec(v___x_3956_);
v___x_3971_ = lean_array_fget_borrowed(v_as_3941_, v_mid_3958_);
v___x_3972_ = lean_array_fget_borrowed(v_as_3941_, v_lo_3942_);
v___x_3973_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v___x_3971_, v___x_3972_);
if (v___x_3973_ == 0)
{
v___y_3966_ = v_as_3941_;
goto v___jp_3965_;
}
else
{
lean_object* v___x_3974_; 
v___x_3974_ = lean_array_fswap(v_as_3941_, v_lo_3942_, v_mid_3958_);
v___y_3966_ = v___x_3974_;
goto v___jp_3965_;
}
v___jp_3959_:
{
lean_object* v___x_3961_; lean_object* v___x_3962_; uint8_t v___x_3963_; 
v___x_3961_ = lean_array_fget_borrowed(v___y_3960_, v_mid_3958_);
v___x_3962_ = lean_array_fget_borrowed(v___y_3960_, v_hi_3943_);
v___x_3963_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v___x_3961_, v___x_3962_);
if (v___x_3963_ == 0)
{
lean_dec(v_mid_3958_);
v___y_3945_ = v___y_3960_;
goto v___jp_3944_;
}
else
{
lean_object* v___x_3964_; 
v___x_3964_ = lean_array_fswap(v___y_3960_, v_mid_3958_, v_hi_3943_);
lean_dec(v_mid_3958_);
v___y_3945_ = v___x_3964_;
goto v___jp_3944_;
}
}
v___jp_3965_:
{
lean_object* v___x_3967_; lean_object* v___x_3968_; uint8_t v___x_3969_; 
v___x_3967_ = lean_array_fget_borrowed(v___y_3966_, v_hi_3943_);
v___x_3968_ = lean_array_fget_borrowed(v___y_3966_, v_lo_3942_);
v___x_3969_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v___x_3967_, v___x_3968_);
if (v___x_3969_ == 0)
{
v___y_3960_ = v___y_3966_;
goto v___jp_3959_;
}
else
{
lean_object* v___x_3970_; 
v___x_3970_ = lean_array_fswap(v___y_3966_, v_lo_3942_, v_hi_3943_);
v___y_3960_ = v___x_3970_;
goto v___jp_3959_;
}
}
}
v___jp_3944_:
{
lean_object* v_pivot_3946_; lean_object* v___x_3947_; lean_object* v_fst_3948_; lean_object* v_snd_3949_; uint8_t v___x_3950_; 
v_pivot_3946_ = lean_array_fget(v___y_3945_, v_hi_3943_);
lean_inc_n(v_lo_3942_, 2);
v___x_3947_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(v_hi_3943_, v_pivot_3946_, v___y_3945_, v_lo_3942_, v_lo_3942_);
lean_dec(v_pivot_3946_);
v_fst_3948_ = lean_ctor_get(v___x_3947_, 0);
lean_inc(v_fst_3948_);
v_snd_3949_ = lean_ctor_get(v___x_3947_, 1);
lean_inc(v_snd_3949_);
lean_dec_ref(v___x_3947_);
v___x_3950_ = lean_nat_dec_le(v_hi_3943_, v_fst_3948_);
if (v___x_3950_ == 0)
{
lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; 
v___x_3951_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v_n_3940_, v_snd_3949_, v_lo_3942_, v_fst_3948_);
v___x_3952_ = lean_unsigned_to_nat(1u);
v___x_3953_ = lean_nat_add(v_fst_3948_, v___x_3952_);
lean_dec(v_fst_3948_);
v_as_3941_ = v___x_3951_;
v_lo_3942_ = v___x_3953_;
goto _start;
}
else
{
lean_dec(v_fst_3948_);
lean_dec(v_lo_3942_);
return v_snd_3949_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___boxed(lean_object* v_n_3975_, lean_object* v_as_3976_, lean_object* v_lo_3977_, lean_object* v_hi_3978_){
_start:
{
lean_object* v_res_3979_; 
v_res_3979_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v_n_3975_, v_as_3976_, v_lo_3977_, v_hi_3978_);
lean_dec(v_hi_3978_);
lean_dec(v_n_3975_);
return v_res_3979_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_sortFVarsByContextOrder(lean_object* v_lctx_3980_, lean_object* v_hyps_3981_){
_start:
{
lean_object* v___y_3983_; size_t v_sz_3987_; size_t v___x_3988_; lean_object* v_hyps_3989_; lean_object* v___x_3990_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___x_3995_; uint8_t v___x_3996_; 
v_sz_3987_ = lean_array_size(v_hyps_3981_);
v___x_3988_ = ((size_t)0ULL);
v_hyps_3989_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(v_lctx_3980_, v_sz_3987_, v___x_3988_, v_hyps_3981_);
v___x_3990_ = lean_array_get_size(v_hyps_3989_);
v___x_3995_ = lean_unsigned_to_nat(0u);
v___x_3996_ = lean_nat_dec_eq(v___x_3990_, v___x_3995_);
if (v___x_3996_ == 0)
{
lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___y_4000_; uint8_t v___x_4002_; 
v___x_3997_ = lean_unsigned_to_nat(1u);
v___x_3998_ = lean_nat_sub(v___x_3990_, v___x_3997_);
v___x_4002_ = lean_nat_dec_le(v___x_3995_, v___x_3998_);
if (v___x_4002_ == 0)
{
lean_inc(v___x_3998_);
v___y_4000_ = v___x_3998_;
goto v___jp_3999_;
}
else
{
v___y_4000_ = v___x_3995_;
goto v___jp_3999_;
}
v___jp_3999_:
{
uint8_t v___x_4001_; 
v___x_4001_ = lean_nat_dec_le(v___y_4000_, v___x_3998_);
if (v___x_4001_ == 0)
{
lean_dec(v___x_3998_);
lean_inc(v___y_4000_);
v___y_3992_ = v___y_4000_;
v___y_3993_ = v___y_4000_;
goto v___jp_3991_;
}
else
{
v___y_3992_ = v___y_4000_;
v___y_3993_ = v___x_3998_;
goto v___jp_3991_;
}
}
}
else
{
v___y_3983_ = v_hyps_3989_;
goto v___jp_3982_;
}
v___jp_3982_:
{
size_t v_sz_3984_; size_t v___x_3985_; lean_object* v___x_3986_; 
v_sz_3984_ = lean_array_size(v___y_3983_);
v___x_3985_ = ((size_t)0ULL);
v___x_3986_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(v_sz_3984_, v___x_3985_, v___y_3983_);
return v___x_3986_;
}
v___jp_3991_:
{
lean_object* v___x_3994_; 
v___x_3994_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v___x_3990_, v_hyps_3989_, v___y_3992_, v___y_3993_);
lean_dec(v___y_3993_);
v___y_3983_ = v___x_3994_;
goto v___jp_3982_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_sortFVarsByContextOrder___boxed(lean_object* v_lctx_4003_, lean_object* v_hyps_4004_){
_start:
{
lean_object* v_res_4005_; 
v_res_4005_ = l_Lean_LocalContext_sortFVarsByContextOrder(v_lctx_4003_, v_hyps_4004_);
lean_dec_ref(v_lctx_4003_);
return v_res_4005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2(lean_object* v_n_4006_, lean_object* v_as_4007_, lean_object* v_lo_4008_, lean_object* v_hi_4009_, lean_object* v_w_4010_, lean_object* v_hlo_4011_, lean_object* v_hhi_4012_){
_start:
{
lean_object* v___x_4013_; 
v___x_4013_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v_n_4006_, v_as_4007_, v_lo_4008_, v_hi_4009_);
return v___x_4013_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___boxed(lean_object* v_n_4014_, lean_object* v_as_4015_, lean_object* v_lo_4016_, lean_object* v_hi_4017_, lean_object* v_w_4018_, lean_object* v_hlo_4019_, lean_object* v_hhi_4020_){
_start:
{
lean_object* v_res_4021_; 
v_res_4021_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2(v_n_4014_, v_as_4015_, v_lo_4016_, v_hi_4017_, v_w_4018_, v_hlo_4019_, v_hhi_4020_);
lean_dec(v_hi_4017_);
lean_dec(v_n_4014_);
return v_res_4021_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2(lean_object* v_n_4022_, lean_object* v_lo_4023_, lean_object* v_hi_4024_, lean_object* v_hhi_4025_, lean_object* v_pivot_4026_, lean_object* v_as_4027_, lean_object* v_i_4028_, lean_object* v_k_4029_, lean_object* v_ilo_4030_, lean_object* v_ik_4031_, lean_object* v_w_4032_){
_start:
{
lean_object* v___x_4033_; 
v___x_4033_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(v_hi_4024_, v_pivot_4026_, v_as_4027_, v_i_4028_, v_k_4029_);
return v___x_4033_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___boxed(lean_object* v_n_4034_, lean_object* v_lo_4035_, lean_object* v_hi_4036_, lean_object* v_hhi_4037_, lean_object* v_pivot_4038_, lean_object* v_as_4039_, lean_object* v_i_4040_, lean_object* v_k_4041_, lean_object* v_ilo_4042_, lean_object* v_ik_4043_, lean_object* v_w_4044_){
_start:
{
lean_object* v_res_4045_; 
v_res_4045_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2(v_n_4034_, v_lo_4035_, v_hi_4036_, v_hhi_4037_, v_pivot_4038_, v_as_4039_, v_i_4040_, v_k_4041_, v_ilo_4042_, v_ik_4043_, v_w_4044_);
lean_dec_ref(v_pivot_4038_);
lean_dec(v_hi_4036_);
lean_dec(v_lo_4035_);
lean_dec(v_n_4034_);
return v_res_4045_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(lean_object* v_a_4046_, lean_object* v_x_4047_){
_start:
{
if (lean_obj_tag(v_x_4047_) == 0)
{
uint8_t v___x_4048_; 
v___x_4048_ = 0;
return v___x_4048_;
}
else
{
lean_object* v_key_4049_; lean_object* v_tail_4050_; uint8_t v___x_4051_; 
v_key_4049_ = lean_ctor_get(v_x_4047_, 0);
v_tail_4050_ = lean_ctor_get(v_x_4047_, 2);
v___x_4051_ = lean_name_eq(v_key_4049_, v_a_4046_);
if (v___x_4051_ == 0)
{
v_x_4047_ = v_tail_4050_;
goto _start;
}
else
{
return v___x_4051_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg___boxed(lean_object* v_a_4053_, lean_object* v_x_4054_){
_start:
{
uint8_t v_res_4055_; lean_object* v_r_4056_; 
v_res_4055_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_4053_, v_x_4054_);
lean_dec(v_x_4054_);
lean_dec(v_a_4053_);
v_r_4056_ = lean_box(v_res_4055_);
return v_r_4056_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(lean_object* v_a_4057_, lean_object* v_x_4058_){
_start:
{
if (lean_obj_tag(v_x_4058_) == 0)
{
return v_x_4058_;
}
else
{
lean_object* v_key_4059_; lean_object* v_value_4060_; lean_object* v_tail_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4070_; 
v_key_4059_ = lean_ctor_get(v_x_4058_, 0);
v_value_4060_ = lean_ctor_get(v_x_4058_, 1);
v_tail_4061_ = lean_ctor_get(v_x_4058_, 2);
v_isSharedCheck_4070_ = !lean_is_exclusive(v_x_4058_);
if (v_isSharedCheck_4070_ == 0)
{
v___x_4063_ = v_x_4058_;
v_isShared_4064_ = v_isSharedCheck_4070_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_tail_4061_);
lean_inc(v_value_4060_);
lean_inc(v_key_4059_);
lean_dec(v_x_4058_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4070_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
uint8_t v___x_4065_; 
v___x_4065_ = lean_name_eq(v_key_4059_, v_a_4057_);
if (v___x_4065_ == 0)
{
lean_object* v___x_4066_; lean_object* v___x_4068_; 
v___x_4066_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_4057_, v_tail_4061_);
if (v_isShared_4064_ == 0)
{
lean_ctor_set(v___x_4063_, 2, v___x_4066_);
v___x_4068_ = v___x_4063_;
goto v_reusejp_4067_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v_key_4059_);
lean_ctor_set(v_reuseFailAlloc_4069_, 1, v_value_4060_);
lean_ctor_set(v_reuseFailAlloc_4069_, 2, v___x_4066_);
v___x_4068_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4067_;
}
v_reusejp_4067_:
{
return v___x_4068_;
}
}
else
{
lean_del_object(v___x_4063_);
lean_dec(v_value_4060_);
lean_dec(v_key_4059_);
return v_tail_4061_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg___boxed(lean_object* v_a_4071_, lean_object* v_x_4072_){
_start:
{
lean_object* v_res_4073_; 
v_res_4073_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_4071_, v_x_4072_);
lean_dec(v_a_4071_);
return v_res_4073_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_4074_; uint64_t v___x_4075_; 
v___x_4074_ = lean_unsigned_to_nat(1723u);
v___x_4075_ = lean_uint64_of_nat(v___x_4074_);
return v___x_4075_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(lean_object* v_m_4076_, lean_object* v_a_4077_){
_start:
{
lean_object* v_size_4078_; lean_object* v_buckets_4079_; lean_object* v___x_4080_; uint64_t v___y_4082_; 
v_size_4078_ = lean_ctor_get(v_m_4076_, 0);
v_buckets_4079_ = lean_ctor_get(v_m_4076_, 1);
v___x_4080_ = lean_array_get_size(v_buckets_4079_);
if (lean_obj_tag(v_a_4077_) == 0)
{
uint64_t v___x_4111_; 
v___x_4111_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0);
v___y_4082_ = v___x_4111_;
goto v___jp_4081_;
}
else
{
uint64_t v_hash_4112_; 
v_hash_4112_ = lean_ctor_get_uint64(v_a_4077_, sizeof(void*)*2);
v___y_4082_ = v_hash_4112_;
goto v___jp_4081_;
}
v___jp_4081_:
{
uint64_t v___x_4083_; uint64_t v___x_4084_; uint64_t v_fold_4085_; uint64_t v___x_4086_; uint64_t v___x_4087_; uint64_t v___x_4088_; size_t v___x_4089_; size_t v___x_4090_; size_t v___x_4091_; size_t v___x_4092_; size_t v___x_4093_; lean_object* v_bkt_4094_; uint8_t v___x_4095_; 
v___x_4083_ = 32ULL;
v___x_4084_ = lean_uint64_shift_right(v___y_4082_, v___x_4083_);
v_fold_4085_ = lean_uint64_xor(v___y_4082_, v___x_4084_);
v___x_4086_ = 16ULL;
v___x_4087_ = lean_uint64_shift_right(v_fold_4085_, v___x_4086_);
v___x_4088_ = lean_uint64_xor(v_fold_4085_, v___x_4087_);
v___x_4089_ = lean_uint64_to_usize(v___x_4088_);
v___x_4090_ = lean_usize_of_nat(v___x_4080_);
v___x_4091_ = ((size_t)1ULL);
v___x_4092_ = lean_usize_sub(v___x_4090_, v___x_4091_);
v___x_4093_ = lean_usize_land(v___x_4089_, v___x_4092_);
v_bkt_4094_ = lean_array_uget_borrowed(v_buckets_4079_, v___x_4093_);
v___x_4095_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_4077_, v_bkt_4094_);
if (v___x_4095_ == 0)
{
return v_m_4076_;
}
else
{
lean_object* v___x_4097_; uint8_t v_isShared_4098_; uint8_t v_isSharedCheck_4108_; 
lean_inc(v_bkt_4094_);
lean_inc_ref(v_buckets_4079_);
lean_inc(v_size_4078_);
v_isSharedCheck_4108_ = !lean_is_exclusive(v_m_4076_);
if (v_isSharedCheck_4108_ == 0)
{
lean_object* v_unused_4109_; lean_object* v_unused_4110_; 
v_unused_4109_ = lean_ctor_get(v_m_4076_, 1);
lean_dec(v_unused_4109_);
v_unused_4110_ = lean_ctor_get(v_m_4076_, 0);
lean_dec(v_unused_4110_);
v___x_4097_ = v_m_4076_;
v_isShared_4098_ = v_isSharedCheck_4108_;
goto v_resetjp_4096_;
}
else
{
lean_dec(v_m_4076_);
v___x_4097_ = lean_box(0);
v_isShared_4098_ = v_isSharedCheck_4108_;
goto v_resetjp_4096_;
}
v_resetjp_4096_:
{
lean_object* v___x_4099_; lean_object* v_buckets_x27_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4106_; 
v___x_4099_ = lean_box(0);
v_buckets_x27_4100_ = lean_array_uset(v_buckets_4079_, v___x_4093_, v___x_4099_);
v___x_4101_ = lean_unsigned_to_nat(1u);
v___x_4102_ = lean_nat_sub(v_size_4078_, v___x_4101_);
lean_dec(v_size_4078_);
v___x_4103_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_4077_, v_bkt_4094_);
v___x_4104_ = lean_array_uset(v_buckets_x27_4100_, v___x_4093_, v___x_4103_);
if (v_isShared_4098_ == 0)
{
lean_ctor_set(v___x_4097_, 1, v___x_4104_);
lean_ctor_set(v___x_4097_, 0, v___x_4102_);
v___x_4106_ = v___x_4097_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4107_; 
v_reuseFailAlloc_4107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4107_, 0, v___x_4102_);
lean_ctor_set(v_reuseFailAlloc_4107_, 1, v___x_4104_);
v___x_4106_ = v_reuseFailAlloc_4107_;
goto v_reusejp_4105_;
}
v_reusejp_4105_:
{
return v___x_4106_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___boxed(lean_object* v_m_4113_, lean_object* v_a_4114_){
_start:
{
lean_object* v_res_4115_; 
v_res_4115_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_m_4113_, v_a_4114_);
lean_dec(v_a_4114_);
return v_res_4115_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(lean_object* v_m_4116_, lean_object* v_a_4117_){
_start:
{
lean_object* v_buckets_4118_; lean_object* v___x_4119_; uint64_t v___y_4121_; 
v_buckets_4118_ = lean_ctor_get(v_m_4116_, 1);
v___x_4119_ = lean_array_get_size(v_buckets_4118_);
if (lean_obj_tag(v_a_4117_) == 0)
{
uint64_t v___x_4135_; 
v___x_4135_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0);
v___y_4121_ = v___x_4135_;
goto v___jp_4120_;
}
else
{
uint64_t v_hash_4136_; 
v_hash_4136_ = lean_ctor_get_uint64(v_a_4117_, sizeof(void*)*2);
v___y_4121_ = v_hash_4136_;
goto v___jp_4120_;
}
v___jp_4120_:
{
uint64_t v___x_4122_; uint64_t v___x_4123_; uint64_t v_fold_4124_; uint64_t v___x_4125_; uint64_t v___x_4126_; uint64_t v___x_4127_; size_t v___x_4128_; size_t v___x_4129_; size_t v___x_4130_; size_t v___x_4131_; size_t v___x_4132_; lean_object* v___x_4133_; uint8_t v___x_4134_; 
v___x_4122_ = 32ULL;
v___x_4123_ = lean_uint64_shift_right(v___y_4121_, v___x_4122_);
v_fold_4124_ = lean_uint64_xor(v___y_4121_, v___x_4123_);
v___x_4125_ = 16ULL;
v___x_4126_ = lean_uint64_shift_right(v_fold_4124_, v___x_4125_);
v___x_4127_ = lean_uint64_xor(v_fold_4124_, v___x_4126_);
v___x_4128_ = lean_uint64_to_usize(v___x_4127_);
v___x_4129_ = lean_usize_of_nat(v___x_4119_);
v___x_4130_ = ((size_t)1ULL);
v___x_4131_ = lean_usize_sub(v___x_4129_, v___x_4130_);
v___x_4132_ = lean_usize_land(v___x_4128_, v___x_4131_);
v___x_4133_ = lean_array_uget_borrowed(v_buckets_4118_, v___x_4132_);
v___x_4134_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_4117_, v___x_4133_);
return v___x_4134_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg___boxed(lean_object* v_m_4137_, lean_object* v_a_4138_){
_start:
{
uint8_t v_res_4139_; lean_object* v_r_4140_; 
v_res_4139_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(v_m_4137_, v_a_4138_);
lean_dec(v_a_4138_);
lean_dec_ref(v_m_4137_);
v_r_4140_ = lean_box(v_res_4139_);
return v_r_4140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(lean_object* v_start_4141_, lean_object* v_as_4142_, size_t v_i_4143_, size_t v_stop_4144_, lean_object* v_b_4145_){
_start:
{
uint8_t v___x_4146_; 
v___x_4146_ = lean_usize_dec_eq(v_i_4143_, v_stop_4144_);
if (v___x_4146_ == 0)
{
size_t v___x_4147_; size_t v___x_4148_; lean_object* v___x_4149_; 
v___x_4147_ = ((size_t)1ULL);
v___x_4148_ = lean_usize_sub(v_i_4143_, v___x_4147_);
v___x_4149_ = lean_array_uget(v_as_4142_, v___x_4148_);
if (lean_obj_tag(v___x_4149_) == 0)
{
v_i_4143_ = v___x_4148_;
goto _start;
}
else
{
lean_object* v_val_4151_; lean_object* v___x_4153_; uint8_t v_isShared_4154_; uint8_t v_isSharedCheck_4185_; 
v_val_4151_ = lean_ctor_get(v___x_4149_, 0);
v_isSharedCheck_4185_ = !lean_is_exclusive(v___x_4149_);
if (v_isSharedCheck_4185_ == 0)
{
v___x_4153_ = v___x_4149_;
v_isShared_4154_ = v_isSharedCheck_4185_;
goto v_resetjp_4152_;
}
else
{
lean_inc(v_val_4151_);
lean_dec(v___x_4149_);
v___x_4153_ = lean_box(0);
v_isShared_4154_ = v_isSharedCheck_4185_;
goto v_resetjp_4152_;
}
v_resetjp_4152_:
{
lean_object* v_fst_4155_; lean_object* v_snd_4156_; lean_object* v___y_4158_; lean_object* v___y_4174_; lean_object* v_size_4180_; lean_object* v___x_4181_; uint8_t v___x_4182_; 
v_fst_4155_ = lean_ctor_get(v_b_4145_, 0);
v_snd_4156_ = lean_ctor_get(v_b_4145_, 1);
v_size_4180_ = lean_ctor_get(v_fst_4155_, 0);
v___x_4181_ = lean_unsigned_to_nat(0u);
v___x_4182_ = lean_nat_dec_eq(v_size_4180_, v___x_4181_);
if (v___x_4182_ == 0)
{
lean_object* v_index_4183_; 
v_index_4183_ = lean_ctor_get(v_val_4151_, 0);
lean_inc(v_index_4183_);
v___y_4174_ = v_index_4183_;
goto v___jp_4173_;
}
else
{
lean_object* v___x_4184_; 
lean_inc(v_snd_4156_);
lean_del_object(v___x_4153_);
lean_dec(v_val_4151_);
lean_dec_ref(v_b_4145_);
v___x_4184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4184_, 0, v_snd_4156_);
return v___x_4184_;
}
v___jp_4157_:
{
uint8_t v___x_4159_; 
v___x_4159_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(v_fst_4155_, v___y_4158_);
if (v___x_4159_ == 0)
{
lean_dec(v___y_4158_);
lean_dec(v_val_4151_);
v_i_4143_ = v___x_4148_;
goto _start;
}
else
{
lean_object* v___x_4162_; uint8_t v_isShared_4163_; uint8_t v_isSharedCheck_4170_; 
lean_inc(v_snd_4156_);
lean_inc(v_fst_4155_);
v_isSharedCheck_4170_ = !lean_is_exclusive(v_b_4145_);
if (v_isSharedCheck_4170_ == 0)
{
lean_object* v_unused_4171_; lean_object* v_unused_4172_; 
v_unused_4171_ = lean_ctor_get(v_b_4145_, 1);
lean_dec(v_unused_4171_);
v_unused_4172_ = lean_ctor_get(v_b_4145_, 0);
lean_dec(v_unused_4172_);
v___x_4162_ = v_b_4145_;
v_isShared_4163_ = v_isSharedCheck_4170_;
goto v_resetjp_4161_;
}
else
{
lean_dec(v_b_4145_);
v___x_4162_ = lean_box(0);
v_isShared_4163_ = v_isSharedCheck_4170_;
goto v_resetjp_4161_;
}
v_resetjp_4161_:
{
lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4167_; 
v___x_4164_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_fst_4155_, v___y_4158_);
lean_dec(v___y_4158_);
v___x_4165_ = lean_array_push(v_snd_4156_, v_val_4151_);
if (v_isShared_4163_ == 0)
{
lean_ctor_set(v___x_4162_, 1, v___x_4165_);
lean_ctor_set(v___x_4162_, 0, v___x_4164_);
v___x_4167_ = v___x_4162_;
goto v_reusejp_4166_;
}
else
{
lean_object* v_reuseFailAlloc_4169_; 
v_reuseFailAlloc_4169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4169_, 0, v___x_4164_);
lean_ctor_set(v_reuseFailAlloc_4169_, 1, v___x_4165_);
v___x_4167_ = v_reuseFailAlloc_4169_;
goto v_reusejp_4166_;
}
v_reusejp_4166_:
{
v_i_4143_ = v___x_4148_;
v_b_4145_ = v___x_4167_;
goto _start;
}
}
}
}
v___jp_4173_:
{
uint8_t v___x_4175_; 
v___x_4175_ = lean_nat_dec_lt(v___y_4174_, v_start_4141_);
lean_dec(v___y_4174_);
if (v___x_4175_ == 0)
{
lean_object* v_userName_4176_; 
lean_del_object(v___x_4153_);
v_userName_4176_ = lean_ctor_get(v_val_4151_, 2);
lean_inc(v_userName_4176_);
v___y_4158_ = v_userName_4176_;
goto v___jp_4157_;
}
else
{
lean_object* v___x_4178_; 
lean_inc(v_snd_4156_);
lean_dec(v_val_4151_);
lean_dec_ref(v_b_4145_);
if (v_isShared_4154_ == 0)
{
lean_ctor_set_tag(v___x_4153_, 0);
lean_ctor_set(v___x_4153_, 0, v_snd_4156_);
v___x_4178_ = v___x_4153_;
goto v_reusejp_4177_;
}
else
{
lean_object* v_reuseFailAlloc_4179_; 
v_reuseFailAlloc_4179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4179_, 0, v_snd_4156_);
v___x_4178_ = v_reuseFailAlloc_4179_;
goto v_reusejp_4177_;
}
v_reusejp_4177_:
{
return v___x_4178_;
}
}
}
}
}
}
else
{
lean_object* v___x_4186_; 
v___x_4186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4186_, 0, v_b_4145_);
return v___x_4186_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_start_4187_, lean_object* v_as_4188_, lean_object* v_i_4189_, lean_object* v_stop_4190_, lean_object* v_b_4191_){
_start:
{
size_t v_i_boxed_4192_; size_t v_stop_boxed_4193_; lean_object* v_res_4194_; 
v_i_boxed_4192_ = lean_unbox_usize(v_i_4189_);
lean_dec(v_i_4189_);
v_stop_boxed_4193_ = lean_unbox_usize(v_stop_4190_);
lean_dec(v_stop_4190_);
v_res_4194_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4187_, v_as_4188_, v_i_boxed_4192_, v_stop_boxed_4193_, v_b_4191_);
lean_dec_ref(v_as_4188_);
lean_dec(v_start_4187_);
return v_res_4194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(lean_object* v_start_4195_, lean_object* v_x_4196_, lean_object* v_x_4197_){
_start:
{
if (lean_obj_tag(v_x_4196_) == 0)
{
lean_object* v_cs_4198_; lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4211_; 
v_cs_4198_ = lean_ctor_get(v_x_4196_, 0);
v_isSharedCheck_4211_ = !lean_is_exclusive(v_x_4196_);
if (v_isSharedCheck_4211_ == 0)
{
v___x_4200_ = v_x_4196_;
v_isShared_4201_ = v_isSharedCheck_4211_;
goto v_resetjp_4199_;
}
else
{
lean_inc(v_cs_4198_);
lean_dec(v_x_4196_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4211_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
lean_object* v___x_4202_; lean_object* v___x_4203_; uint8_t v___x_4204_; 
v___x_4202_ = lean_array_get_size(v_cs_4198_);
v___x_4203_ = lean_unsigned_to_nat(0u);
v___x_4204_ = lean_nat_dec_lt(v___x_4203_, v___x_4202_);
if (v___x_4204_ == 0)
{
lean_object* v___x_4206_; 
lean_dec_ref(v_cs_4198_);
if (v_isShared_4201_ == 0)
{
lean_ctor_set_tag(v___x_4200_, 1);
lean_ctor_set(v___x_4200_, 0, v_x_4197_);
v___x_4206_ = v___x_4200_;
goto v_reusejp_4205_;
}
else
{
lean_object* v_reuseFailAlloc_4207_; 
v_reuseFailAlloc_4207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4207_, 0, v_x_4197_);
v___x_4206_ = v_reuseFailAlloc_4207_;
goto v_reusejp_4205_;
}
v_reusejp_4205_:
{
return v___x_4206_;
}
}
else
{
size_t v___x_4208_; size_t v___x_4209_; lean_object* v___x_4210_; 
lean_del_object(v___x_4200_);
v___x_4208_ = lean_usize_of_nat(v___x_4202_);
v___x_4209_ = ((size_t)0ULL);
v___x_4210_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(v_start_4195_, v_cs_4198_, v___x_4208_, v___x_4209_, v_x_4197_);
lean_dec_ref(v_cs_4198_);
return v___x_4210_;
}
}
}
else
{
lean_object* v_vs_4212_; lean_object* v___x_4214_; uint8_t v_isShared_4215_; uint8_t v_isSharedCheck_4225_; 
v_vs_4212_ = lean_ctor_get(v_x_4196_, 0);
v_isSharedCheck_4225_ = !lean_is_exclusive(v_x_4196_);
if (v_isSharedCheck_4225_ == 0)
{
v___x_4214_ = v_x_4196_;
v_isShared_4215_ = v_isSharedCheck_4225_;
goto v_resetjp_4213_;
}
else
{
lean_inc(v_vs_4212_);
lean_dec(v_x_4196_);
v___x_4214_ = lean_box(0);
v_isShared_4215_ = v_isSharedCheck_4225_;
goto v_resetjp_4213_;
}
v_resetjp_4213_:
{
lean_object* v___x_4216_; lean_object* v___x_4217_; uint8_t v___x_4218_; 
v___x_4216_ = lean_array_get_size(v_vs_4212_);
v___x_4217_ = lean_unsigned_to_nat(0u);
v___x_4218_ = lean_nat_dec_lt(v___x_4217_, v___x_4216_);
if (v___x_4218_ == 0)
{
lean_object* v___x_4220_; 
lean_dec_ref(v_vs_4212_);
if (v_isShared_4215_ == 0)
{
lean_ctor_set(v___x_4214_, 0, v_x_4197_);
v___x_4220_ = v___x_4214_;
goto v_reusejp_4219_;
}
else
{
lean_object* v_reuseFailAlloc_4221_; 
v_reuseFailAlloc_4221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4221_, 0, v_x_4197_);
v___x_4220_ = v_reuseFailAlloc_4221_;
goto v_reusejp_4219_;
}
v_reusejp_4219_:
{
return v___x_4220_;
}
}
else
{
size_t v___x_4222_; size_t v___x_4223_; lean_object* v___x_4224_; 
lean_del_object(v___x_4214_);
v___x_4222_ = lean_usize_of_nat(v___x_4216_);
v___x_4223_ = ((size_t)0ULL);
v___x_4224_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4195_, v_vs_4212_, v___x_4222_, v___x_4223_, v_x_4197_);
lean_dec_ref(v_vs_4212_);
return v___x_4224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_start_4226_, lean_object* v_as_4227_, size_t v_i_4228_, size_t v_stop_4229_, lean_object* v_b_4230_){
_start:
{
uint8_t v___x_4231_; 
v___x_4231_ = lean_usize_dec_eq(v_i_4228_, v_stop_4229_);
if (v___x_4231_ == 0)
{
size_t v___x_4232_; size_t v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; 
v___x_4232_ = ((size_t)1ULL);
v___x_4233_ = lean_usize_sub(v_i_4228_, v___x_4232_);
v___x_4234_ = lean_array_uget_borrowed(v_as_4227_, v___x_4233_);
lean_inc(v___x_4234_);
v___x_4235_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4226_, v___x_4234_, v_b_4230_);
if (lean_obj_tag(v___x_4235_) == 0)
{
return v___x_4235_;
}
else
{
lean_object* v_a_4236_; 
v_a_4236_ = lean_ctor_get(v___x_4235_, 0);
lean_inc(v_a_4236_);
lean_dec_ref_known(v___x_4235_, 1);
v_i_4228_ = v___x_4233_;
v_b_4230_ = v_a_4236_;
goto _start;
}
}
else
{
lean_object* v___x_4238_; 
v___x_4238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4238_, 0, v_b_4230_);
return v___x_4238_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_start_4239_, lean_object* v_as_4240_, lean_object* v_i_4241_, lean_object* v_stop_4242_, lean_object* v_b_4243_){
_start:
{
size_t v_i_boxed_4244_; size_t v_stop_boxed_4245_; lean_object* v_res_4246_; 
v_i_boxed_4244_ = lean_unbox_usize(v_i_4241_);
lean_dec(v_i_4241_);
v_stop_boxed_4245_ = lean_unbox_usize(v_stop_4242_);
lean_dec(v_stop_4242_);
v_res_4246_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(v_start_4239_, v_as_4240_, v_i_boxed_4244_, v_stop_boxed_4245_, v_b_4243_);
lean_dec_ref(v_as_4240_);
lean_dec(v_start_4239_);
return v_res_4246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_start_4247_, lean_object* v_x_4248_, lean_object* v_x_4249_){
_start:
{
lean_object* v_res_4250_; 
v_res_4250_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4247_, v_x_4248_, v_x_4249_);
lean_dec(v_start_4247_);
return v_res_4250_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(lean_object* v_start_4251_, lean_object* v_t_4252_, lean_object* v_init_4253_){
_start:
{
lean_object* v_root_4254_; lean_object* v_tail_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; uint8_t v___x_4258_; 
v_root_4254_ = lean_ctor_get(v_t_4252_, 0);
lean_inc_ref(v_root_4254_);
v_tail_4255_ = lean_ctor_get(v_t_4252_, 1);
lean_inc_ref(v_tail_4255_);
lean_dec_ref(v_t_4252_);
v___x_4256_ = lean_array_get_size(v_tail_4255_);
v___x_4257_ = lean_unsigned_to_nat(0u);
v___x_4258_ = lean_nat_dec_lt(v___x_4257_, v___x_4256_);
if (v___x_4258_ == 0)
{
lean_object* v___x_4259_; 
lean_dec_ref(v_tail_4255_);
v___x_4259_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4251_, v_root_4254_, v_init_4253_);
return v___x_4259_;
}
else
{
size_t v___x_4260_; size_t v___x_4261_; lean_object* v___x_4262_; 
v___x_4260_ = lean_usize_of_nat(v___x_4256_);
v___x_4261_ = ((size_t)0ULL);
v___x_4262_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4251_, v_tail_4255_, v___x_4260_, v___x_4261_, v_init_4253_);
lean_dec_ref(v_tail_4255_);
if (lean_obj_tag(v___x_4262_) == 0)
{
lean_dec_ref(v_root_4254_);
return v___x_4262_;
}
else
{
lean_object* v_a_4263_; lean_object* v___x_4264_; 
v_a_4263_ = lean_ctor_get(v___x_4262_, 0);
lean_inc(v_a_4263_);
lean_dec_ref_known(v___x_4262_, 1);
v___x_4264_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4251_, v_root_4254_, v_a_4263_);
return v___x_4264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg___boxed(lean_object* v_start_4265_, lean_object* v_t_4266_, lean_object* v_init_4267_){
_start:
{
lean_object* v_res_4268_; 
v_res_4268_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(v_start_4265_, v_t_4266_, v_init_4267_);
lean_dec(v_start_4265_);
return v_res_4268_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(lean_object* v_start_4269_, lean_object* v_lctx_4270_, lean_object* v_init_4271_){
_start:
{
lean_object* v_decls_4272_; lean_object* v___x_4273_; 
v_decls_4272_ = lean_ctor_get(v_lctx_4270_, 1);
lean_inc_ref(v_decls_4272_);
lean_dec_ref(v_lctx_4270_);
v___x_4273_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(v_start_4269_, v_decls_4272_, v_init_4271_);
return v___x_4273_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg___boxed(lean_object* v_start_4274_, lean_object* v_lctx_4275_, lean_object* v_init_4276_){
_start:
{
lean_object* v_res_4277_; 
v_res_4277_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(v_start_4274_, v_lctx_4275_, v_init_4276_);
lean_dec(v_start_4274_);
return v_res_4277_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___redArg(lean_object* v_lctx_4280_, lean_object* v_userNames_4281_, lean_object* v_start_4282_){
_start:
{
lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; 
v___x_4283_ = ((lean_object*)(l_Lean_LocalContext_findFromUserNames___redArg___closed__0));
v___x_4284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4284_, 0, v_userNames_4281_);
lean_ctor_set(v___x_4284_, 1, v___x_4283_);
v___x_4285_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(v_start_4282_, v_lctx_4280_, v___x_4284_);
if (lean_obj_tag(v___x_4285_) == 0)
{
lean_object* v_a_4286_; lean_object* v___x_4287_; 
v_a_4286_ = lean_ctor_get(v___x_4285_, 0);
lean_inc(v_a_4286_);
lean_dec_ref_known(v___x_4285_, 1);
v___x_4287_ = l_Array_reverse___redArg(v_a_4286_);
return v___x_4287_;
}
else
{
lean_object* v_a_4288_; lean_object* v_snd_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; 
v_a_4288_ = lean_ctor_get(v___x_4285_, 0);
lean_inc(v_a_4288_);
lean_dec_ref_known(v___x_4285_, 1);
v_snd_4289_ = lean_ctor_get(v_a_4288_, 1);
lean_inc(v_snd_4289_);
lean_dec(v_a_4288_);
v___x_4290_ = l_Array_reverse___redArg(v_snd_4289_);
v___x_4291_ = l_Array_reverse___redArg(v___x_4290_);
return v___x_4291_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___redArg___boxed(lean_object* v_lctx_4292_, lean_object* v_userNames_4293_, lean_object* v_start_4294_){
_start:
{
lean_object* v_res_4295_; 
v_res_4295_ = l_Lean_LocalContext_findFromUserNames___redArg(v_lctx_4292_, v_userNames_4293_, v_start_4294_);
lean_dec(v_start_4294_);
return v_res_4295_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames(lean_object* v_00_u03b1_4296_, lean_object* v_lctx_4297_, lean_object* v_userNames_4298_, lean_object* v_start_4299_){
_start:
{
lean_object* v___x_4300_; 
v___x_4300_ = l_Lean_LocalContext_findFromUserNames___redArg(v_lctx_4297_, v_userNames_4298_, v_start_4299_);
return v___x_4300_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___boxed(lean_object* v_00_u03b1_4301_, lean_object* v_lctx_4302_, lean_object* v_userNames_4303_, lean_object* v_start_4304_){
_start:
{
lean_object* v_res_4305_; 
v_res_4305_ = l_Lean_LocalContext_findFromUserNames(v_00_u03b1_4301_, v_lctx_4302_, v_userNames_4303_, v_start_4304_);
lean_dec(v_start_4304_);
return v_res_4305_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0(lean_object* v_00_u03b2_4306_, lean_object* v_m_4307_, lean_object* v_a_4308_){
_start:
{
uint8_t v___x_4309_; 
v___x_4309_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(v_m_4307_, v_a_4308_);
return v___x_4309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___boxed(lean_object* v_00_u03b2_4310_, lean_object* v_m_4311_, lean_object* v_a_4312_){
_start:
{
uint8_t v_res_4313_; lean_object* v_r_4314_; 
v_res_4313_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0(v_00_u03b2_4310_, v_m_4311_, v_a_4312_);
lean_dec(v_a_4312_);
lean_dec_ref(v_m_4311_);
v_r_4314_ = lean_box(v_res_4313_);
return v_r_4314_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1(lean_object* v_00_u03b2_4315_, lean_object* v_m_4316_, lean_object* v_a_4317_){
_start:
{
lean_object* v___x_4318_; 
v___x_4318_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_m_4316_, v_a_4317_);
return v___x_4318_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___boxed(lean_object* v_00_u03b2_4319_, lean_object* v_m_4320_, lean_object* v_a_4321_){
_start:
{
lean_object* v_res_4322_; 
v_res_4322_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1(v_00_u03b2_4319_, v_m_4320_, v_a_4321_);
lean_dec(v_a_4321_);
return v_res_4322_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2(lean_object* v_00_u03b1_4323_, lean_object* v_start_4324_, lean_object* v_lctx_4325_, lean_object* v_init_4326_){
_start:
{
lean_object* v___x_4327_; 
v___x_4327_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(v_start_4324_, v_lctx_4325_, v_init_4326_);
return v___x_4327_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___boxed(lean_object* v_00_u03b1_4328_, lean_object* v_start_4329_, lean_object* v_lctx_4330_, lean_object* v_init_4331_){
_start:
{
lean_object* v_res_4332_; 
v_res_4332_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2(v_00_u03b1_4328_, v_start_4329_, v_lctx_4330_, v_init_4331_);
lean_dec(v_start_4329_);
return v_res_4332_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0(lean_object* v_00_u03b2_4333_, lean_object* v_a_4334_, lean_object* v_x_4335_){
_start:
{
uint8_t v___x_4336_; 
v___x_4336_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_4334_, v_x_4335_);
return v___x_4336_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4337_, lean_object* v_a_4338_, lean_object* v_x_4339_){
_start:
{
uint8_t v_res_4340_; lean_object* v_r_4341_; 
v_res_4340_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0(v_00_u03b2_4337_, v_a_4338_, v_x_4339_);
lean_dec(v_x_4339_);
lean_dec(v_a_4338_);
v_r_4341_ = lean_box(v_res_4340_);
return v_r_4341_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2(lean_object* v_00_u03b2_4342_, lean_object* v_a_4343_, lean_object* v_x_4344_){
_start:
{
lean_object* v___x_4345_; 
v___x_4345_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_4343_, v_x_4344_);
return v___x_4345_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4346_, lean_object* v_a_4347_, lean_object* v_x_4348_){
_start:
{
lean_object* v_res_4349_; 
v_res_4349_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2(v_00_u03b2_4346_, v_a_4347_, v_x_4348_);
lean_dec(v_a_4347_);
return v_res_4349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4(lean_object* v_00_u03b1_4350_, lean_object* v_start_4351_, lean_object* v_t_4352_, lean_object* v_init_4353_){
_start:
{
lean_object* v___x_4354_; 
v___x_4354_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(v_start_4351_, v_t_4352_, v_init_4353_);
return v___x_4354_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___boxed(lean_object* v_00_u03b1_4355_, lean_object* v_start_4356_, lean_object* v_t_4357_, lean_object* v_init_4358_){
_start:
{
lean_object* v_res_4359_; 
v_res_4359_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4(v_00_u03b1_4355_, v_start_4356_, v_t_4357_, v_init_4358_);
lean_dec(v_start_4356_);
return v_res_4359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5(lean_object* v_00_u03b1_4360_, lean_object* v_start_4361_, lean_object* v_x_4362_, lean_object* v_x_4363_){
_start:
{
lean_object* v___x_4364_; 
v___x_4364_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4361_, v_x_4362_, v_x_4363_);
return v___x_4364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b1_4365_, lean_object* v_start_4366_, lean_object* v_x_4367_, lean_object* v_x_4368_){
_start:
{
lean_object* v_res_4369_; 
v_res_4369_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5(v_00_u03b1_4365_, v_start_4366_, v_x_4367_, v_x_4368_);
lean_dec(v_start_4366_);
return v_res_4369_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_4370_, lean_object* v_start_4371_, lean_object* v_as_4372_, size_t v_i_4373_, size_t v_stop_4374_, lean_object* v_b_4375_){
_start:
{
lean_object* v___x_4376_; 
v___x_4376_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4371_, v_as_4372_, v_i_4373_, v_stop_4374_, v_b_4375_);
return v___x_4376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_4377_, lean_object* v_start_4378_, lean_object* v_as_4379_, lean_object* v_i_4380_, lean_object* v_stop_4381_, lean_object* v_b_4382_){
_start:
{
size_t v_i_boxed_4383_; size_t v_stop_boxed_4384_; lean_object* v_res_4385_; 
v_i_boxed_4383_ = lean_unbox_usize(v_i_4380_);
lean_dec(v_i_4380_);
v_stop_boxed_4384_ = lean_unbox_usize(v_stop_4381_);
lean_dec(v_stop_4381_);
v_res_4385_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6(v_00_u03b1_4377_, v_start_4378_, v_as_4379_, v_i_boxed_4383_, v_stop_boxed_4384_, v_b_4382_);
lean_dec_ref(v_as_4379_);
lean_dec(v_start_4378_);
return v_res_4385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b1_4386_, lean_object* v_start_4387_, lean_object* v_as_4388_, size_t v_i_4389_, size_t v_stop_4390_, lean_object* v_b_4391_){
_start:
{
lean_object* v___x_4392_; 
v___x_4392_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(v_start_4387_, v_as_4388_, v_i_4389_, v_stop_4390_, v_b_4391_);
return v___x_4392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___boxed(lean_object* v_00_u03b1_4393_, lean_object* v_start_4394_, lean_object* v_as_4395_, lean_object* v_i_4396_, lean_object* v_stop_4397_, lean_object* v_b_4398_){
_start:
{
size_t v_i_boxed_4399_; size_t v_stop_boxed_4400_; lean_object* v_res_4401_; 
v_i_boxed_4399_ = lean_unbox_usize(v_i_4396_);
lean_dec(v_i_4396_);
v_stop_boxed_4400_ = lean_unbox_usize(v_stop_4397_);
lean_dec(v_stop_4397_);
v_res_4401_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6(v_00_u03b1_4393_, v_start_4394_, v_as_4395_, v_i_boxed_4399_, v_stop_boxed_4400_, v_b_4398_);
lean_dec_ref(v_as_4395_);
lean_dec(v_start_4394_);
return v_res_4401_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLCtxOfMonadLift___redArg(lean_object* v_inst_4402_, lean_object* v_inst_4403_){
_start:
{
lean_object* v___x_4404_; 
v___x_4404_ = lean_apply_2(v_inst_4402_, lean_box(0), v_inst_4403_);
return v___x_4404_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLCtxOfMonadLift(lean_object* v_m_4405_, lean_object* v_n_4406_, lean_object* v_inst_4407_, lean_object* v_inst_4408_){
_start:
{
lean_object* v___x_4409_; 
v___x_4409_ = lean_apply_2(v_inst_4407_, lean_box(0), v_inst_4408_);
return v___x_4409_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__0(lean_object* v_toPure_4410_, lean_object* v_d_x3f_4411_, lean_object* v_b_4412_){
_start:
{
if (lean_obj_tag(v_d_x3f_4411_) == 0)
{
lean_object* v___x_4413_; lean_object* v___x_4414_; 
v___x_4413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4413_, 0, v_b_4412_);
v___x_4414_ = lean_apply_2(v_toPure_4410_, lean_box(0), v___x_4413_);
return v___x_4414_;
}
else
{
lean_object* v_val_4415_; lean_object* v___x_4417_; uint8_t v_isShared_4418_; uint8_t v_isSharedCheck_4430_; 
v_val_4415_ = lean_ctor_get(v_d_x3f_4411_, 0);
v_isSharedCheck_4430_ = !lean_is_exclusive(v_d_x3f_4411_);
if (v_isSharedCheck_4430_ == 0)
{
v___x_4417_ = v_d_x3f_4411_;
v_isShared_4418_ = v_isSharedCheck_4430_;
goto v_resetjp_4416_;
}
else
{
lean_inc(v_val_4415_);
lean_dec(v_d_x3f_4411_);
v___x_4417_ = lean_box(0);
v_isShared_4418_ = v_isSharedCheck_4430_;
goto v_resetjp_4416_;
}
v_resetjp_4416_:
{
uint8_t v___x_4419_; 
v___x_4419_ = l_Lean_LocalDecl_isImplementationDetail(v_val_4415_);
if (v___x_4419_ == 0)
{
lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4423_; 
v___x_4420_ = l_Lean_LocalDecl_toExpr(v_val_4415_);
v___x_4421_ = lean_array_push(v_b_4412_, v___x_4420_);
if (v_isShared_4418_ == 0)
{
lean_ctor_set(v___x_4417_, 0, v___x_4421_);
v___x_4423_ = v___x_4417_;
goto v_reusejp_4422_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v___x_4421_);
v___x_4423_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4422_;
}
v_reusejp_4422_:
{
lean_object* v___x_4424_; 
v___x_4424_ = lean_apply_2(v_toPure_4410_, lean_box(0), v___x_4423_);
return v___x_4424_;
}
}
else
{
lean_object* v___x_4427_; 
lean_dec(v_val_4415_);
if (v_isShared_4418_ == 0)
{
lean_ctor_set(v___x_4417_, 0, v_b_4412_);
v___x_4427_ = v___x_4417_;
goto v_reusejp_4426_;
}
else
{
lean_object* v_reuseFailAlloc_4429_; 
v_reuseFailAlloc_4429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4429_, 0, v_b_4412_);
v___x_4427_ = v_reuseFailAlloc_4429_;
goto v_reusejp_4426_;
}
v_reusejp_4426_:
{
lean_object* v___x_4428_; 
v___x_4428_ = lean_apply_2(v_toPure_4410_, lean_box(0), v___x_4427_);
return v___x_4428_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__1(lean_object* v_toPure_4431_, lean_object* v_____s_4432_){
_start:
{
lean_object* v___x_4433_; 
v___x_4433_ = lean_apply_2(v_toPure_4431_, lean_box(0), v_____s_4432_);
return v___x_4433_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__2(lean_object* v_inst_4434_, lean_object* v_hs_4435_, lean_object* v___f_4436_, lean_object* v_toBind_4437_, lean_object* v___f_4438_, lean_object* v_____do__lift_4439_){
_start:
{
lean_object* v_decls_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; 
v_decls_4440_ = lean_ctor_get(v_____do__lift_4439_, 1);
v___x_4441_ = l_Lean_PersistentArray_forIn___redArg(v_inst_4434_, v_decls_4440_, v_hs_4435_, v___f_4436_);
v___x_4442_ = lean_apply_4(v_toBind_4437_, lean_box(0), lean_box(0), v___x_4441_, v___f_4438_);
return v___x_4442_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__2___boxed(lean_object* v_inst_4443_, lean_object* v_hs_4444_, lean_object* v___f_4445_, lean_object* v_toBind_4446_, lean_object* v___f_4447_, lean_object* v_____do__lift_4448_){
_start:
{
lean_object* v_res_4449_; 
v_res_4449_ = l_Lean_getLocalHyps___redArg___lam__2(v_inst_4443_, v_hs_4444_, v___f_4445_, v_toBind_4446_, v___f_4447_, v_____do__lift_4448_);
lean_dec_ref(v_____do__lift_4448_);
return v_res_4449_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg(lean_object* v_inst_4452_, lean_object* v_inst_4453_){
_start:
{
lean_object* v_toApplicative_4454_; lean_object* v_toBind_4455_; lean_object* v_toPure_4456_; lean_object* v_hs_4457_; lean_object* v___f_4458_; lean_object* v___f_4459_; lean_object* v___f_4460_; lean_object* v___x_4461_; 
v_toApplicative_4454_ = lean_ctor_get(v_inst_4452_, 0);
v_toBind_4455_ = lean_ctor_get(v_inst_4452_, 1);
lean_inc_n(v_toBind_4455_, 2);
v_toPure_4456_ = lean_ctor_get(v_toApplicative_4454_, 1);
v_hs_4457_ = ((lean_object*)(l_Lean_getLocalHyps___redArg___closed__0));
lean_inc_n(v_toPure_4456_, 2);
v___f_4458_ = lean_alloc_closure((void*)(l_Lean_getLocalHyps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4458_, 0, v_toPure_4456_);
v___f_4459_ = lean_alloc_closure((void*)(l_Lean_getLocalHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_4459_, 0, v_toPure_4456_);
v___f_4460_ = lean_alloc_closure((void*)(l_Lean_getLocalHyps___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_4460_, 0, v_inst_4452_);
lean_closure_set(v___f_4460_, 1, v_hs_4457_);
lean_closure_set(v___f_4460_, 2, v___f_4458_);
lean_closure_set(v___f_4460_, 3, v_toBind_4455_);
lean_closure_set(v___f_4460_, 4, v___f_4459_);
v___x_4461_ = lean_apply_4(v_toBind_4455_, lean_box(0), lean_box(0), v_inst_4453_, v___f_4460_);
return v___x_4461_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps(lean_object* v_m_4462_, lean_object* v_inst_4463_, lean_object* v_inst_4464_){
_start:
{
lean_object* v___x_4465_; 
v___x_4465_ = l_Lean_getLocalHyps___redArg(v_inst_4463_, v_inst_4464_);
return v___x_4465_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_replaceFVarId(lean_object* v_fvarId_4466_, lean_object* v_e_4467_, lean_object* v_d_4468_){
_start:
{
lean_object* v___y_4470_; lean_object* v_fvarId_4502_; 
v_fvarId_4502_ = lean_ctor_get(v_d_4468_, 1);
lean_inc(v_fvarId_4502_);
v___y_4470_ = v_fvarId_4502_;
goto v___jp_4469_;
v___jp_4469_:
{
uint8_t v___x_4471_; 
v___x_4471_ = l_Lean_instBEqFVarId_beq(v___y_4470_, v_fvarId_4466_);
lean_dec(v___y_4470_);
if (v___x_4471_ == 0)
{
if (lean_obj_tag(v_d_4468_) == 0)
{
lean_object* v_index_4472_; lean_object* v_fvarId_4473_; lean_object* v_userName_4474_; lean_object* v_type_4475_; uint8_t v_bi_4476_; uint8_t v_kind_4477_; lean_object* v___x_4479_; uint8_t v_isShared_4480_; uint8_t v_isSharedCheck_4485_; 
v_index_4472_ = lean_ctor_get(v_d_4468_, 0);
v_fvarId_4473_ = lean_ctor_get(v_d_4468_, 1);
v_userName_4474_ = lean_ctor_get(v_d_4468_, 2);
v_type_4475_ = lean_ctor_get(v_d_4468_, 3);
v_bi_4476_ = lean_ctor_get_uint8(v_d_4468_, sizeof(void*)*4);
v_kind_4477_ = lean_ctor_get_uint8(v_d_4468_, sizeof(void*)*4 + 1);
v_isSharedCheck_4485_ = !lean_is_exclusive(v_d_4468_);
if (v_isSharedCheck_4485_ == 0)
{
v___x_4479_ = v_d_4468_;
v_isShared_4480_ = v_isSharedCheck_4485_;
goto v_resetjp_4478_;
}
else
{
lean_inc(v_type_4475_);
lean_inc(v_userName_4474_);
lean_inc(v_fvarId_4473_);
lean_inc(v_index_4472_);
lean_dec(v_d_4468_);
v___x_4479_ = lean_box(0);
v_isShared_4480_ = v_isSharedCheck_4485_;
goto v_resetjp_4478_;
}
v_resetjp_4478_:
{
lean_object* v___x_4481_; lean_object* v___x_4483_; 
v___x_4481_ = l_Lean_Expr_replaceFVarId(v_type_4475_, v_fvarId_4466_, v_e_4467_);
lean_dec_ref(v_type_4475_);
if (v_isShared_4480_ == 0)
{
lean_ctor_set(v___x_4479_, 3, v___x_4481_);
v___x_4483_ = v___x_4479_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4484_; 
v_reuseFailAlloc_4484_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4484_, 0, v_index_4472_);
lean_ctor_set(v_reuseFailAlloc_4484_, 1, v_fvarId_4473_);
lean_ctor_set(v_reuseFailAlloc_4484_, 2, v_userName_4474_);
lean_ctor_set(v_reuseFailAlloc_4484_, 3, v___x_4481_);
lean_ctor_set_uint8(v_reuseFailAlloc_4484_, sizeof(void*)*4, v_bi_4476_);
lean_ctor_set_uint8(v_reuseFailAlloc_4484_, sizeof(void*)*4 + 1, v_kind_4477_);
v___x_4483_ = v_reuseFailAlloc_4484_;
goto v_reusejp_4482_;
}
v_reusejp_4482_:
{
return v___x_4483_;
}
}
}
else
{
lean_object* v_index_4486_; lean_object* v_fvarId_4487_; lean_object* v_userName_4488_; lean_object* v_type_4489_; lean_object* v_value_4490_; uint8_t v_nondep_4491_; uint8_t v_kind_4492_; lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_4501_; 
v_index_4486_ = lean_ctor_get(v_d_4468_, 0);
v_fvarId_4487_ = lean_ctor_get(v_d_4468_, 1);
v_userName_4488_ = lean_ctor_get(v_d_4468_, 2);
v_type_4489_ = lean_ctor_get(v_d_4468_, 3);
v_value_4490_ = lean_ctor_get(v_d_4468_, 4);
v_nondep_4491_ = lean_ctor_get_uint8(v_d_4468_, sizeof(void*)*5);
v_kind_4492_ = lean_ctor_get_uint8(v_d_4468_, sizeof(void*)*5 + 1);
v_isSharedCheck_4501_ = !lean_is_exclusive(v_d_4468_);
if (v_isSharedCheck_4501_ == 0)
{
v___x_4494_ = v_d_4468_;
v_isShared_4495_ = v_isSharedCheck_4501_;
goto v_resetjp_4493_;
}
else
{
lean_inc(v_value_4490_);
lean_inc(v_type_4489_);
lean_inc(v_userName_4488_);
lean_inc(v_fvarId_4487_);
lean_inc(v_index_4486_);
lean_dec(v_d_4468_);
v___x_4494_ = lean_box(0);
v_isShared_4495_ = v_isSharedCheck_4501_;
goto v_resetjp_4493_;
}
v_resetjp_4493_:
{
lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4499_; 
lean_inc(v_fvarId_4466_);
v___x_4496_ = l_Lean_Expr_replaceFVarId(v_type_4489_, v_fvarId_4466_, v_e_4467_);
lean_dec_ref(v_type_4489_);
v___x_4497_ = l_Lean_Expr_replaceFVarId(v_value_4490_, v_fvarId_4466_, v_e_4467_);
lean_dec_ref(v_value_4490_);
if (v_isShared_4495_ == 0)
{
lean_ctor_set(v___x_4494_, 4, v___x_4497_);
lean_ctor_set(v___x_4494_, 3, v___x_4496_);
v___x_4499_ = v___x_4494_;
goto v_reusejp_4498_;
}
else
{
lean_object* v_reuseFailAlloc_4500_; 
v_reuseFailAlloc_4500_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_4500_, 0, v_index_4486_);
lean_ctor_set(v_reuseFailAlloc_4500_, 1, v_fvarId_4487_);
lean_ctor_set(v_reuseFailAlloc_4500_, 2, v_userName_4488_);
lean_ctor_set(v_reuseFailAlloc_4500_, 3, v___x_4496_);
lean_ctor_set(v_reuseFailAlloc_4500_, 4, v___x_4497_);
lean_ctor_set_uint8(v_reuseFailAlloc_4500_, sizeof(void*)*5, v_nondep_4491_);
lean_ctor_set_uint8(v_reuseFailAlloc_4500_, sizeof(void*)*5 + 1, v_kind_4492_);
v___x_4499_ = v_reuseFailAlloc_4500_;
goto v_reusejp_4498_;
}
v_reusejp_4498_:
{
return v___x_4499_;
}
}
}
}
else
{
lean_dec(v_fvarId_4466_);
return v_d_4468_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_replaceFVarId___boxed(lean_object* v_fvarId_4503_, lean_object* v_e_4504_, lean_object* v_d_4505_){
_start:
{
lean_object* v_res_4506_; 
v_res_4506_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_4503_, v_e_4504_, v_d_4505_);
lean_dec_ref(v_e_4504_);
return v_res_4506_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId___lam__0(lean_object* v_fvarId_4507_, lean_object* v_e_4508_, lean_object* v_x_4509_){
_start:
{
lean_object* v___x_4510_; 
v___x_4510_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_4507_, v_e_4508_, v_x_4509_);
return v___x_4510_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId___lam__0___boxed(lean_object* v_fvarId_4511_, lean_object* v_e_4512_, lean_object* v_x_4513_){
_start:
{
lean_object* v_res_4514_; 
v_res_4514_ = l_Lean_LocalContext_replaceFVarId___lam__0(v_fvarId_4511_, v_e_4512_, v_x_4513_);
lean_dec_ref(v_e_4512_);
return v_res_4514_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(lean_object* v_fvarId_4515_, lean_object* v_e_4516_, size_t v_sz_4517_, size_t v_i_4518_, lean_object* v_bs_4519_){
_start:
{
uint8_t v___x_4520_; 
v___x_4520_ = lean_usize_dec_lt(v_i_4518_, v_sz_4517_);
if (v___x_4520_ == 0)
{
lean_dec(v_fvarId_4515_);
return v_bs_4519_;
}
else
{
lean_object* v_v_4521_; lean_object* v___x_4522_; lean_object* v_bs_x27_4523_; lean_object* v___y_4525_; 
v_v_4521_ = lean_array_uget(v_bs_4519_, v_i_4518_);
v___x_4522_ = lean_unsigned_to_nat(0u);
v_bs_x27_4523_ = lean_array_uset(v_bs_4519_, v_i_4518_, v___x_4522_);
if (lean_obj_tag(v_v_4521_) == 0)
{
v___y_4525_ = v_v_4521_;
goto v___jp_4524_;
}
else
{
lean_object* v_val_4530_; lean_object* v___x_4532_; uint8_t v_isShared_4533_; uint8_t v_isSharedCheck_4538_; 
v_val_4530_ = lean_ctor_get(v_v_4521_, 0);
v_isSharedCheck_4538_ = !lean_is_exclusive(v_v_4521_);
if (v_isSharedCheck_4538_ == 0)
{
v___x_4532_ = v_v_4521_;
v_isShared_4533_ = v_isSharedCheck_4538_;
goto v_resetjp_4531_;
}
else
{
lean_inc(v_val_4530_);
lean_dec(v_v_4521_);
v___x_4532_ = lean_box(0);
v_isShared_4533_ = v_isSharedCheck_4538_;
goto v_resetjp_4531_;
}
v_resetjp_4531_:
{
lean_object* v___x_4534_; lean_object* v___x_4536_; 
lean_inc(v_fvarId_4515_);
v___x_4534_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_4515_, v_e_4516_, v_val_4530_);
if (v_isShared_4533_ == 0)
{
lean_ctor_set(v___x_4532_, 0, v___x_4534_);
v___x_4536_ = v___x_4532_;
goto v_reusejp_4535_;
}
else
{
lean_object* v_reuseFailAlloc_4537_; 
v_reuseFailAlloc_4537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4537_, 0, v___x_4534_);
v___x_4536_ = v_reuseFailAlloc_4537_;
goto v_reusejp_4535_;
}
v_reusejp_4535_:
{
v___y_4525_ = v___x_4536_;
goto v___jp_4524_;
}
}
}
v___jp_4524_:
{
size_t v___x_4526_; size_t v___x_4527_; lean_object* v___x_4528_; 
v___x_4526_ = ((size_t)1ULL);
v___x_4527_ = lean_usize_add(v_i_4518_, v___x_4526_);
v___x_4528_ = lean_array_uset(v_bs_x27_4523_, v_i_4518_, v___y_4525_);
v_i_4518_ = v___x_4527_;
v_bs_4519_ = v___x_4528_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3___boxed(lean_object* v_fvarId_4539_, lean_object* v_e_4540_, lean_object* v_sz_4541_, lean_object* v_i_4542_, lean_object* v_bs_4543_){
_start:
{
size_t v_sz_boxed_4544_; size_t v_i_boxed_4545_; lean_object* v_res_4546_; 
v_sz_boxed_4544_ = lean_unbox_usize(v_sz_4541_);
lean_dec(v_sz_4541_);
v_i_boxed_4545_ = lean_unbox_usize(v_i_4542_);
lean_dec(v_i_4542_);
v_res_4546_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(v_fvarId_4539_, v_e_4540_, v_sz_boxed_4544_, v_i_boxed_4545_, v_bs_4543_);
lean_dec_ref(v_e_4540_);
return v_res_4546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(lean_object* v_fvarId_4547_, lean_object* v_e_4548_, size_t v_sz_4549_, size_t v_i_4550_, lean_object* v_bs_4551_){
_start:
{
uint8_t v___x_4552_; 
v___x_4552_ = lean_usize_dec_lt(v_i_4550_, v_sz_4549_);
if (v___x_4552_ == 0)
{
lean_dec(v_fvarId_4547_);
return v_bs_4551_;
}
else
{
lean_object* v_v_4553_; lean_object* v___x_4554_; lean_object* v_bs_x27_4555_; lean_object* v___x_4556_; size_t v___x_4557_; size_t v___x_4558_; lean_object* v___x_4559_; 
v_v_4553_ = lean_array_uget(v_bs_4551_, v_i_4550_);
v___x_4554_ = lean_unsigned_to_nat(0u);
v_bs_x27_4555_ = lean_array_uset(v_bs_4551_, v_i_4550_, v___x_4554_);
lean_inc(v_fvarId_4547_);
v___x_4556_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(v_fvarId_4547_, v_e_4548_, v_v_4553_);
v___x_4557_ = ((size_t)1ULL);
v___x_4558_ = lean_usize_add(v_i_4550_, v___x_4557_);
v___x_4559_ = lean_array_uset(v_bs_x27_4555_, v_i_4550_, v___x_4556_);
v_i_4550_ = v___x_4558_;
v_bs_4551_ = v___x_4559_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(lean_object* v_fvarId_4561_, lean_object* v_e_4562_, lean_object* v_x_4563_){
_start:
{
if (lean_obj_tag(v_x_4563_) == 0)
{
lean_object* v_cs_4564_; lean_object* v___x_4566_; uint8_t v_isShared_4567_; uint8_t v_isSharedCheck_4574_; 
v_cs_4564_ = lean_ctor_get(v_x_4563_, 0);
v_isSharedCheck_4574_ = !lean_is_exclusive(v_x_4563_);
if (v_isSharedCheck_4574_ == 0)
{
v___x_4566_ = v_x_4563_;
v_isShared_4567_ = v_isSharedCheck_4574_;
goto v_resetjp_4565_;
}
else
{
lean_inc(v_cs_4564_);
lean_dec(v_x_4563_);
v___x_4566_ = lean_box(0);
v_isShared_4567_ = v_isSharedCheck_4574_;
goto v_resetjp_4565_;
}
v_resetjp_4565_:
{
size_t v_sz_4568_; size_t v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4572_; 
v_sz_4568_ = lean_array_size(v_cs_4564_);
v___x_4569_ = ((size_t)0ULL);
v___x_4570_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(v_fvarId_4561_, v_e_4562_, v_sz_4568_, v___x_4569_, v_cs_4564_);
if (v_isShared_4567_ == 0)
{
lean_ctor_set(v___x_4566_, 0, v___x_4570_);
v___x_4572_ = v___x_4566_;
goto v_reusejp_4571_;
}
else
{
lean_object* v_reuseFailAlloc_4573_; 
v_reuseFailAlloc_4573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4573_, 0, v___x_4570_);
v___x_4572_ = v_reuseFailAlloc_4573_;
goto v_reusejp_4571_;
}
v_reusejp_4571_:
{
return v___x_4572_;
}
}
}
else
{
lean_object* v_vs_4575_; lean_object* v___x_4577_; uint8_t v_isShared_4578_; uint8_t v_isSharedCheck_4585_; 
v_vs_4575_ = lean_ctor_get(v_x_4563_, 0);
v_isSharedCheck_4585_ = !lean_is_exclusive(v_x_4563_);
if (v_isSharedCheck_4585_ == 0)
{
v___x_4577_ = v_x_4563_;
v_isShared_4578_ = v_isSharedCheck_4585_;
goto v_resetjp_4576_;
}
else
{
lean_inc(v_vs_4575_);
lean_dec(v_x_4563_);
v___x_4577_ = lean_box(0);
v_isShared_4578_ = v_isSharedCheck_4585_;
goto v_resetjp_4576_;
}
v_resetjp_4576_:
{
size_t v_sz_4579_; size_t v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4583_; 
v_sz_4579_ = lean_array_size(v_vs_4575_);
v___x_4580_ = ((size_t)0ULL);
v___x_4581_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(v_fvarId_4561_, v_e_4562_, v_sz_4579_, v___x_4580_, v_vs_4575_);
if (v_isShared_4578_ == 0)
{
lean_ctor_set(v___x_4577_, 0, v___x_4581_);
v___x_4583_ = v___x_4577_;
goto v_reusejp_4582_;
}
else
{
lean_object* v_reuseFailAlloc_4584_; 
v_reuseFailAlloc_4584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4584_, 0, v___x_4581_);
v___x_4583_ = v_reuseFailAlloc_4584_;
goto v_reusejp_4582_;
}
v_reusejp_4582_:
{
return v___x_4583_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2___boxed(lean_object* v_fvarId_4586_, lean_object* v_e_4587_, lean_object* v_x_4588_){
_start:
{
lean_object* v_res_4589_; 
v_res_4589_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(v_fvarId_4586_, v_e_4587_, v_x_4588_);
lean_dec_ref(v_e_4587_);
return v_res_4589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4___boxed(lean_object* v_fvarId_4590_, lean_object* v_e_4591_, lean_object* v_sz_4592_, lean_object* v_i_4593_, lean_object* v_bs_4594_){
_start:
{
size_t v_sz_boxed_4595_; size_t v_i_boxed_4596_; lean_object* v_res_4597_; 
v_sz_boxed_4595_ = lean_unbox_usize(v_sz_4592_);
lean_dec(v_sz_4592_);
v_i_boxed_4596_ = lean_unbox_usize(v_i_4593_);
lean_dec(v_i_4593_);
v_res_4597_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(v_fvarId_4590_, v_e_4591_, v_sz_boxed_4595_, v_i_boxed_4596_, v_bs_4594_);
lean_dec_ref(v_e_4591_);
return v_res_4597_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(lean_object* v_fvarId_4598_, lean_object* v_e_4599_, lean_object* v_t_4600_){
_start:
{
lean_object* v_root_4601_; lean_object* v_tail_4602_; lean_object* v_size_4603_; size_t v_shift_4604_; lean_object* v_tailOff_4605_; lean_object* v___x_4607_; uint8_t v_isShared_4608_; uint8_t v_isSharedCheck_4616_; 
v_root_4601_ = lean_ctor_get(v_t_4600_, 0);
v_tail_4602_ = lean_ctor_get(v_t_4600_, 1);
v_size_4603_ = lean_ctor_get(v_t_4600_, 2);
v_shift_4604_ = lean_ctor_get_usize(v_t_4600_, 4);
v_tailOff_4605_ = lean_ctor_get(v_t_4600_, 3);
v_isSharedCheck_4616_ = !lean_is_exclusive(v_t_4600_);
if (v_isSharedCheck_4616_ == 0)
{
v___x_4607_ = v_t_4600_;
v_isShared_4608_ = v_isSharedCheck_4616_;
goto v_resetjp_4606_;
}
else
{
lean_inc(v_tailOff_4605_);
lean_inc(v_size_4603_);
lean_inc(v_tail_4602_);
lean_inc(v_root_4601_);
lean_dec(v_t_4600_);
v___x_4607_ = lean_box(0);
v_isShared_4608_ = v_isSharedCheck_4616_;
goto v_resetjp_4606_;
}
v_resetjp_4606_:
{
lean_object* v___x_4609_; size_t v_sz_4610_; size_t v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4614_; 
lean_inc(v_fvarId_4598_);
v___x_4609_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(v_fvarId_4598_, v_e_4599_, v_root_4601_);
v_sz_4610_ = lean_array_size(v_tail_4602_);
v___x_4611_ = ((size_t)0ULL);
v___x_4612_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(v_fvarId_4598_, v_e_4599_, v_sz_4610_, v___x_4611_, v_tail_4602_);
if (v_isShared_4608_ == 0)
{
lean_ctor_set(v___x_4607_, 1, v___x_4612_);
lean_ctor_set(v___x_4607_, 0, v___x_4609_);
v___x_4614_ = v___x_4607_;
goto v_reusejp_4613_;
}
else
{
lean_object* v_reuseFailAlloc_4615_; 
v_reuseFailAlloc_4615_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_4615_, 0, v___x_4609_);
lean_ctor_set(v_reuseFailAlloc_4615_, 1, v___x_4612_);
lean_ctor_set(v_reuseFailAlloc_4615_, 2, v_size_4603_);
lean_ctor_set(v_reuseFailAlloc_4615_, 3, v_tailOff_4605_);
lean_ctor_set_usize(v_reuseFailAlloc_4615_, 4, v_shift_4604_);
v___x_4614_ = v_reuseFailAlloc_4615_;
goto v_reusejp_4613_;
}
v_reusejp_4613_:
{
return v___x_4614_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1___boxed(lean_object* v_fvarId_4617_, lean_object* v_e_4618_, lean_object* v_t_4619_){
_start:
{
lean_object* v_res_4620_; 
v_res_4620_ = l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(v_fvarId_4617_, v_e_4618_, v_t_4619_);
lean_dec_ref(v_e_4618_);
return v_res_4620_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg___lam__0(lean_object* v_f_4621_, lean_object* v_x_4622_){
_start:
{
lean_object* v___x_4623_; 
v___x_4623_ = lean_apply_1(v_f_4621_, v_x_4622_);
return v___x_4623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(lean_object* v_f_4624_, lean_object* v_as_4625_, lean_object* v_i_4626_, lean_object* v_acc_4627_){
_start:
{
lean_object* v___x_4628_; uint8_t v___x_4629_; 
v___x_4628_ = lean_array_get_size(v_as_4625_);
v___x_4629_ = lean_nat_dec_eq(v_i_4626_, v___x_4628_);
if (v___x_4629_ == 0)
{
lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; 
v___x_4630_ = lean_array_fget_borrowed(v_as_4625_, v_i_4626_);
lean_inc(v_f_4624_);
lean_inc(v___x_4630_);
v___x_4631_ = lean_apply_1(v_f_4624_, v___x_4630_);
v___x_4632_ = lean_unsigned_to_nat(1u);
v___x_4633_ = lean_nat_add(v_i_4626_, v___x_4632_);
lean_dec(v_i_4626_);
v___x_4634_ = lean_array_push(v_acc_4627_, v___x_4631_);
v_i_4626_ = v___x_4633_;
v_acc_4627_ = v___x_4634_;
goto _start;
}
else
{
lean_dec(v_i_4626_);
lean_dec(v_f_4624_);
return v_acc_4627_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg___boxed(lean_object* v_f_4636_, lean_object* v_as_4637_, lean_object* v_i_4638_, lean_object* v_acc_4639_){
_start:
{
lean_object* v_res_4640_; 
v_res_4640_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_f_4636_, v_as_4637_, v_i_4638_, v_acc_4639_);
lean_dec_ref(v_as_4637_);
return v_res_4640_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_f_4641_, lean_object* v_as_4642_){
_start:
{
lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; 
v___x_4643_ = lean_unsigned_to_nat(0u);
v___x_4644_ = lean_array_get_size(v_as_4642_);
v___x_4645_ = lean_mk_empty_array_with_capacity(v___x_4644_);
v___x_4646_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_f_4641_, v_as_4642_, v___x_4643_, v___x_4645_);
return v___x_4646_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_f_4647_, lean_object* v_as_4648_){
_start:
{
lean_object* v_res_4649_; 
v_res_4649_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(v_f_4647_, v_as_4648_);
lean_dec_ref(v_as_4648_);
return v_res_4649_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_4650_, size_t v_sz_4651_, size_t v_i_4652_, lean_object* v_bs_4653_){
_start:
{
uint8_t v___x_4654_; 
v___x_4654_ = lean_usize_dec_lt(v_i_4652_, v_sz_4651_);
if (v___x_4654_ == 0)
{
lean_dec(v_f_4650_);
return v_bs_4653_;
}
else
{
lean_object* v_v_4655_; lean_object* v___x_4656_; lean_object* v_bs_x27_4657_; lean_object* v___y_4659_; 
v_v_4655_ = lean_array_uget(v_bs_4653_, v_i_4652_);
v___x_4656_ = lean_unsigned_to_nat(0u);
v_bs_x27_4657_ = lean_array_uset(v_bs_4653_, v_i_4652_, v___x_4656_);
switch(lean_obj_tag(v_v_4655_))
{
case 0:
{
lean_object* v_key_4664_; lean_object* v_val_4665_; lean_object* v___x_4667_; uint8_t v_isShared_4668_; uint8_t v_isSharedCheck_4673_; 
v_key_4664_ = lean_ctor_get(v_v_4655_, 0);
v_val_4665_ = lean_ctor_get(v_v_4655_, 1);
v_isSharedCheck_4673_ = !lean_is_exclusive(v_v_4655_);
if (v_isSharedCheck_4673_ == 0)
{
v___x_4667_ = v_v_4655_;
v_isShared_4668_ = v_isSharedCheck_4673_;
goto v_resetjp_4666_;
}
else
{
lean_inc(v_val_4665_);
lean_inc(v_key_4664_);
lean_dec(v_v_4655_);
v___x_4667_ = lean_box(0);
v_isShared_4668_ = v_isSharedCheck_4673_;
goto v_resetjp_4666_;
}
v_resetjp_4666_:
{
lean_object* v___x_4669_; lean_object* v___x_4671_; 
lean_inc(v_f_4650_);
v___x_4669_ = lean_apply_1(v_f_4650_, v_val_4665_);
if (v_isShared_4668_ == 0)
{
lean_ctor_set(v___x_4667_, 1, v___x_4669_);
v___x_4671_ = v___x_4667_;
goto v_reusejp_4670_;
}
else
{
lean_object* v_reuseFailAlloc_4672_; 
v_reuseFailAlloc_4672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4672_, 0, v_key_4664_);
lean_ctor_set(v_reuseFailAlloc_4672_, 1, v___x_4669_);
v___x_4671_ = v_reuseFailAlloc_4672_;
goto v_reusejp_4670_;
}
v_reusejp_4670_:
{
v___y_4659_ = v___x_4671_;
goto v___jp_4658_;
}
}
}
case 1:
{
lean_object* v_node_4674_; lean_object* v___x_4676_; uint8_t v_isShared_4677_; uint8_t v_isSharedCheck_4682_; 
v_node_4674_ = lean_ctor_get(v_v_4655_, 0);
v_isSharedCheck_4682_ = !lean_is_exclusive(v_v_4655_);
if (v_isSharedCheck_4682_ == 0)
{
v___x_4676_ = v_v_4655_;
v_isShared_4677_ = v_isSharedCheck_4682_;
goto v_resetjp_4675_;
}
else
{
lean_inc(v_node_4674_);
lean_dec(v_v_4655_);
v___x_4676_ = lean_box(0);
v_isShared_4677_ = v_isSharedCheck_4682_;
goto v_resetjp_4675_;
}
v_resetjp_4675_:
{
lean_object* v___x_4678_; lean_object* v___x_4680_; 
lean_inc(v_f_4650_);
v___x_4678_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4650_, v_node_4674_);
if (v_isShared_4677_ == 0)
{
lean_ctor_set(v___x_4676_, 0, v___x_4678_);
v___x_4680_ = v___x_4676_;
goto v_reusejp_4679_;
}
else
{
lean_object* v_reuseFailAlloc_4681_; 
v_reuseFailAlloc_4681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4681_, 0, v___x_4678_);
v___x_4680_ = v_reuseFailAlloc_4681_;
goto v_reusejp_4679_;
}
v_reusejp_4679_:
{
v___y_4659_ = v___x_4680_;
goto v___jp_4658_;
}
}
}
default: 
{
lean_object* v___x_4683_; 
v___x_4683_ = lean_box(2);
v___y_4659_ = v___x_4683_;
goto v___jp_4658_;
}
}
v___jp_4658_:
{
size_t v___x_4660_; size_t v___x_4661_; lean_object* v___x_4662_; 
v___x_4660_ = ((size_t)1ULL);
v___x_4661_ = lean_usize_add(v_i_4652_, v___x_4660_);
v___x_4662_ = lean_array_uset(v_bs_x27_4657_, v_i_4652_, v___y_4659_);
v_i_4652_ = v___x_4661_;
v_bs_4653_ = v___x_4662_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(lean_object* v_f_4684_, lean_object* v_n_4685_){
_start:
{
if (lean_obj_tag(v_n_4685_) == 0)
{
lean_object* v_es_4686_; lean_object* v___x_4688_; uint8_t v_isShared_4689_; uint8_t v_isSharedCheck_4696_; 
v_es_4686_ = lean_ctor_get(v_n_4685_, 0);
v_isSharedCheck_4696_ = !lean_is_exclusive(v_n_4685_);
if (v_isSharedCheck_4696_ == 0)
{
v___x_4688_ = v_n_4685_;
v_isShared_4689_ = v_isSharedCheck_4696_;
goto v_resetjp_4687_;
}
else
{
lean_inc(v_es_4686_);
lean_dec(v_n_4685_);
v___x_4688_ = lean_box(0);
v_isShared_4689_ = v_isSharedCheck_4696_;
goto v_resetjp_4687_;
}
v_resetjp_4687_:
{
size_t v_sz_4690_; size_t v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4694_; 
v_sz_4690_ = lean_array_size(v_es_4686_);
v___x_4691_ = ((size_t)0ULL);
v___x_4692_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(v_f_4684_, v_sz_4690_, v___x_4691_, v_es_4686_);
if (v_isShared_4689_ == 0)
{
lean_ctor_set(v___x_4688_, 0, v___x_4692_);
v___x_4694_ = v___x_4688_;
goto v_reusejp_4693_;
}
else
{
lean_object* v_reuseFailAlloc_4695_; 
v_reuseFailAlloc_4695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4695_, 0, v___x_4692_);
v___x_4694_ = v_reuseFailAlloc_4695_;
goto v_reusejp_4693_;
}
v_reusejp_4693_:
{
return v___x_4694_;
}
}
}
else
{
lean_object* v_ks_4697_; lean_object* v_vs_4698_; lean_object* v___x_4700_; uint8_t v_isShared_4701_; uint8_t v_isSharedCheck_4706_; 
v_ks_4697_ = lean_ctor_get(v_n_4685_, 0);
v_vs_4698_ = lean_ctor_get(v_n_4685_, 1);
v_isSharedCheck_4706_ = !lean_is_exclusive(v_n_4685_);
if (v_isSharedCheck_4706_ == 0)
{
v___x_4700_ = v_n_4685_;
v_isShared_4701_ = v_isSharedCheck_4706_;
goto v_resetjp_4699_;
}
else
{
lean_inc(v_vs_4698_);
lean_inc(v_ks_4697_);
lean_dec(v_n_4685_);
v___x_4700_ = lean_box(0);
v_isShared_4701_ = v_isSharedCheck_4706_;
goto v_resetjp_4699_;
}
v_resetjp_4699_:
{
lean_object* v_val_4702_; lean_object* v___x_4704_; 
v_val_4702_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(v_f_4684_, v_vs_4698_);
lean_dec_ref(v_vs_4698_);
if (v_isShared_4701_ == 0)
{
lean_ctor_set(v___x_4700_, 1, v_val_4702_);
v___x_4704_ = v___x_4700_;
goto v_reusejp_4703_;
}
else
{
lean_object* v_reuseFailAlloc_4705_; 
v_reuseFailAlloc_4705_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4705_, 0, v_ks_4697_);
lean_ctor_set(v_reuseFailAlloc_4705_, 1, v_val_4702_);
v___x_4704_ = v_reuseFailAlloc_4705_;
goto v_reusejp_4703_;
}
v_reusejp_4703_:
{
return v___x_4704_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_4707_, lean_object* v_sz_4708_, lean_object* v_i_4709_, lean_object* v_bs_4710_){
_start:
{
size_t v_sz_boxed_4711_; size_t v_i_boxed_4712_; lean_object* v_res_4713_; 
v_sz_boxed_4711_ = lean_unbox_usize(v_sz_4708_);
lean_dec(v_sz_4708_);
v_i_boxed_4712_ = lean_unbox_usize(v_i_4709_);
lean_dec(v_i_4709_);
v_res_4713_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(v_f_4707_, v_sz_boxed_4711_, v_i_boxed_4712_, v_bs_4710_);
return v_res_4713_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(lean_object* v_pm_4714_, lean_object* v_f_4715_){
_start:
{
lean_object* v___f_4716_; lean_object* v___x_4717_; 
v___f_4716_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4716_, 0, v_f_4715_);
v___x_4717_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v___f_4716_, v_pm_4714_);
return v___x_4717_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId(lean_object* v_fvarId_4718_, lean_object* v_e_4719_, lean_object* v_lctx_4720_){
_start:
{
lean_object* v_lctx_4721_; lean_object* v_fvarIdToDecl_4722_; lean_object* v_decls_4723_; lean_object* v_auxDeclToFullName_4724_; lean_object* v___x_4726_; uint8_t v_isShared_4727_; uint8_t v_isSharedCheck_4734_; 
lean_inc(v_fvarId_4718_);
v_lctx_4721_ = lean_local_ctx_erase(v_lctx_4720_, v_fvarId_4718_);
v_fvarIdToDecl_4722_ = lean_ctor_get(v_lctx_4721_, 0);
v_decls_4723_ = lean_ctor_get(v_lctx_4721_, 1);
v_auxDeclToFullName_4724_ = lean_ctor_get(v_lctx_4721_, 2);
v_isSharedCheck_4734_ = !lean_is_exclusive(v_lctx_4721_);
if (v_isSharedCheck_4734_ == 0)
{
v___x_4726_ = v_lctx_4721_;
v_isShared_4727_ = v_isSharedCheck_4734_;
goto v_resetjp_4725_;
}
else
{
lean_inc(v_auxDeclToFullName_4724_);
lean_inc(v_decls_4723_);
lean_inc(v_fvarIdToDecl_4722_);
lean_dec(v_lctx_4721_);
v___x_4726_ = lean_box(0);
v_isShared_4727_ = v_isSharedCheck_4734_;
goto v_resetjp_4725_;
}
v_resetjp_4725_:
{
lean_object* v___f_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4732_; 
lean_inc_ref(v_e_4719_);
lean_inc(v_fvarId_4718_);
v___f_4728_ = lean_alloc_closure((void*)(l_Lean_LocalContext_replaceFVarId___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4728_, 0, v_fvarId_4718_);
lean_closure_set(v___f_4728_, 1, v_e_4719_);
v___x_4729_ = l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(v_fvarIdToDecl_4722_, v___f_4728_);
v___x_4730_ = l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(v_fvarId_4718_, v_e_4719_, v_decls_4723_);
lean_dec_ref(v_e_4719_);
if (v_isShared_4727_ == 0)
{
lean_ctor_set(v___x_4726_, 1, v___x_4730_);
lean_ctor_set(v___x_4726_, 0, v___x_4729_);
v___x_4732_ = v___x_4726_;
goto v_reusejp_4731_;
}
else
{
lean_object* v_reuseFailAlloc_4733_; 
v_reuseFailAlloc_4733_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4733_, 0, v___x_4729_);
lean_ctor_set(v_reuseFailAlloc_4733_, 1, v___x_4730_);
lean_ctor_set(v_reuseFailAlloc_4733_, 2, v_auxDeclToFullName_4724_);
v___x_4732_ = v_reuseFailAlloc_4733_;
goto v_reusejp_4731_;
}
v_reusejp_4731_:
{
return v___x_4732_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0(lean_object* v_00_u03b2_4735_, lean_object* v_00_u03c3_4736_, lean_object* v_pm_4737_, lean_object* v_f_4738_){
_start:
{
lean_object* v___x_4739_; 
v___x_4739_ = l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(v_pm_4737_, v_f_4738_);
return v___x_4739_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0___redArg(lean_object* v_pm_4740_, lean_object* v_f_4741_){
_start:
{
lean_object* v___x_4742_; 
v___x_4742_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4741_, v_pm_4740_);
return v___x_4742_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0(lean_object* v_00_u03b2_4743_, lean_object* v_00_u03c3_4744_, lean_object* v_pm_4745_, lean_object* v_f_4746_){
_start:
{
lean_object* v___x_4747_; 
v___x_4747_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4746_, v_pm_4745_);
return v___x_4747_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_4748_, lean_object* v_00_u03b2_4749_, lean_object* v_00_u03c3_4750_, lean_object* v_f_4751_, lean_object* v_n_4752_){
_start:
{
lean_object* v___x_4753_; 
v___x_4753_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4751_, v_n_4752_);
return v___x_4753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_4754_, lean_object* v_00_u03b2_4755_, lean_object* v_00_u03c3_4756_, lean_object* v_f_4757_, size_t v_sz_4758_, size_t v_i_4759_, lean_object* v_bs_4760_){
_start:
{
lean_object* v___x_4761_; 
v___x_4761_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(v_f_4757_, v_sz_4758_, v_i_4759_, v_bs_4760_);
return v___x_4761_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_4762_, lean_object* v_00_u03b2_4763_, lean_object* v_00_u03c3_4764_, lean_object* v_f_4765_, lean_object* v_sz_4766_, lean_object* v_i_4767_, lean_object* v_bs_4768_){
_start:
{
size_t v_sz_boxed_4769_; size_t v_i_boxed_4770_; lean_object* v_res_4771_; 
v_sz_boxed_4769_ = lean_unbox_usize(v_sz_4766_);
lean_dec(v_sz_4766_);
v_i_boxed_4770_ = lean_unbox_usize(v_i_4767_);
lean_dec(v_i_4767_);
v_res_4771_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_4762_, v_00_u03b2_4763_, v_00_u03c3_4764_, v_f_4765_, v_sz_boxed_4769_, v_i_boxed_4770_, v_bs_4768_);
return v_res_4771_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_4772_, lean_object* v_00_u03b2_4773_, lean_object* v_f_4774_, lean_object* v_as_4775_){
_start:
{
lean_object* v___x_4776_; 
v___x_4776_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(v_f_4774_, v_as_4775_);
return v___x_4776_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_4777_, lean_object* v_00_u03b2_4778_, lean_object* v_f_4779_, lean_object* v_as_4780_){
_start:
{
lean_object* v_res_4781_; 
v_res_4781_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_4777_, v_00_u03b2_4778_, v_f_4779_, v_as_4780_);
lean_dec_ref(v_as_4780_);
return v_res_4781_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7(lean_object* v_00_u03b1_4782_, lean_object* v_00_u03b2_4783_, lean_object* v_f_4784_, lean_object* v_as_4785_, lean_object* v_i_4786_, lean_object* v_acc_4787_, lean_object* v_hle_4788_){
_start:
{
lean_object* v___x_4789_; 
v___x_4789_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_f_4784_, v_as_4785_, v_i_4786_, v_acc_4787_);
return v___x_4789_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___boxed(lean_object* v_00_u03b1_4790_, lean_object* v_00_u03b2_4791_, lean_object* v_f_4792_, lean_object* v_as_4793_, lean_object* v_i_4794_, lean_object* v_acc_4795_, lean_object* v_hle_4796_){
_start:
{
lean_object* v_res_4797_; 
v_res_4797_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7(v_00_u03b1_4790_, v_00_u03b2_4791_, v_f_4792_, v_as_4793_, v_i_4794_, v_acc_4795_, v_hle_4796_);
lean_dec_ref(v_as_4793_);
return v_res_4797_;
}
}
lean_object* runtime_initialize_Init_Data_Nat_Control(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_PersistentArray(uint8_t builtin);
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_LocalContext(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Nat_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_PersistentArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedLocalDeclKind_default = _init_l_Lean_instInhabitedLocalDeclKind_default();
l_Lean_instInhabitedLocalDeclKind = _init_l_Lean_instInhabitedLocalDeclKind();
l_Lean_instInhabitedLocalDecl_default = _init_l_Lean_instInhabitedLocalDecl_default();
lean_mark_persistent(l_Lean_instInhabitedLocalDecl_default);
l_Lean_instInhabitedLocalDecl = _init_l_Lean_instInhabitedLocalDecl();
lean_mark_persistent(l_Lean_instInhabitedLocalDecl);
l_Lean_instInhabitedLocalContext_default = _init_l_Lean_instInhabitedLocalContext_default();
lean_mark_persistent(l_Lean_instInhabitedLocalContext_default);
l_Lean_instInhabitedLocalContext = _init_l_Lean_instInhabitedLocalContext();
lean_mark_persistent(l_Lean_instInhabitedLocalContext);
l_Lean_LocalContext_empty = _init_l_Lean_LocalContext_empty();
lean_mark_persistent(l_Lean_LocalContext_empty);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_LocalContext(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Nat_Control(uint8_t builtin);
lean_object* initialize_Lean_Data_PersistentArray(uint8_t builtin);
lean_object* initialize_Lean_Expr(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_LocalContext(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_PersistentArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_LocalContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_LocalContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_LocalContext(builtin);
}
#ifdef __cplusplus
}
#endif
