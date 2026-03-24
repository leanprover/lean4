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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_anyM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
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
extern lean_object* l_Lean_instInhabitedFVarId_default;
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
lean_object* l_Lean_instInhabitedPersistentArray_default(lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_instInhabitedLocalContext_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedLocalContext;
static lean_once_cell_t l_Lean_LocalContext_mkEmpty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LocalContext_mkEmpty___closed__0;
static lean_once_cell_t l_Lean_LocalContext_mkEmpty___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LocalContext_mkEmpty___closed__1;
static lean_once_cell_t l_Lean_LocalContext_mkEmpty___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LocalContext_mkEmpty___closed__2;
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__2;
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_sortFVarsByContextOrder(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_t_160_);
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
lean_dec_ref(v_t_160_);
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
uint8_t v___x_215_; uint8_t v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_215_ = 0;
v___x_216_ = 0;
v___x_217_ = lean_obj_once(&l_Lean_instInhabitedLocalDecl_default___closed__2, &l_Lean_instInhabitedLocalDecl_default___closed__2_once, _init_l_Lean_instInhabitedLocalDecl_default___closed__2);
v___x_218_ = lean_box(0);
v___x_219_ = l_Lean_instInhabitedFVarId_default;
v___x_220_ = lean_unsigned_to_nat(0u);
v___x_221_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_221_, 0, v___x_220_);
lean_ctor_set(v___x_221_, 1, v___x_219_);
lean_ctor_set(v___x_221_, 2, v___x_218_);
lean_ctor_set(v___x_221_, 3, v___x_217_);
lean_ctor_set_uint8(v___x_221_, sizeof(void*)*4, v___x_216_);
lean_ctor_set_uint8(v___x_221_, sizeof(void*)*4 + 1, v___x_215_);
return v___x_221_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl_default(void){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = lean_obj_once(&l_Lean_instInhabitedLocalDecl_default___closed__3, &l_Lean_instInhabitedLocalDecl_default___closed__3_once, _init_l_Lean_instInhabitedLocalDecl_default___closed__3);
return v___x_222_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl(void){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l_Lean_instInhabitedLocalDecl_default;
return v___x_223_;
}
}
LEAN_EXPORT lean_object* lean_mk_local_decl(lean_object* v_index_224_, lean_object* v_fvarId_225_, lean_object* v_userName_226_, lean_object* v_type_227_, uint8_t v_bi_228_){
_start:
{
uint8_t v___x_229_; lean_object* v___x_230_; 
v___x_229_ = 0;
v___x_230_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_230_, 0, v_index_224_);
lean_ctor_set(v___x_230_, 1, v_fvarId_225_);
lean_ctor_set(v___x_230_, 2, v_userName_226_);
lean_ctor_set(v___x_230_, 3, v_type_227_);
lean_ctor_set_uint8(v___x_230_, sizeof(void*)*4, v_bi_228_);
lean_ctor_set_uint8(v___x_230_, sizeof(void*)*4 + 1, v___x_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLocalDeclEx___boxed(lean_object* v_index_231_, lean_object* v_fvarId_232_, lean_object* v_userName_233_, lean_object* v_type_234_, lean_object* v_bi_235_){
_start:
{
uint8_t v_bi_boxed_236_; lean_object* v_res_237_; 
v_bi_boxed_236_ = lean_unbox(v_bi_235_);
v_res_237_ = lean_mk_local_decl(v_index_231_, v_fvarId_232_, v_userName_233_, v_type_234_, v_bi_boxed_236_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* lean_mk_let_decl(lean_object* v_index_238_, lean_object* v_fvarId_239_, lean_object* v_userName_240_, lean_object* v_type_241_, lean_object* v_val_242_){
_start:
{
uint8_t v___x_243_; uint8_t v___x_244_; lean_object* v___x_245_; 
v___x_243_ = 0;
v___x_244_ = 0;
v___x_245_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v___x_245_, 0, v_index_238_);
lean_ctor_set(v___x_245_, 1, v_fvarId_239_);
lean_ctor_set(v___x_245_, 2, v_userName_240_);
lean_ctor_set(v___x_245_, 3, v_type_241_);
lean_ctor_set(v___x_245_, 4, v_val_242_);
lean_ctor_set_uint8(v___x_245_, sizeof(void*)*5, v___x_243_);
lean_ctor_set_uint8(v___x_245_, sizeof(void*)*5 + 1, v___x_244_);
return v___x_245_;
}
}
LEAN_EXPORT uint8_t lean_local_decl_binder_info(lean_object* v_x_246_){
_start:
{
if (lean_obj_tag(v_x_246_) == 0)
{
uint8_t v_bi_247_; 
v_bi_247_ = lean_ctor_get_uint8(v_x_246_, sizeof(void*)*4);
lean_dec_ref(v_x_246_);
return v_bi_247_;
}
else
{
uint8_t v___x_248_; 
lean_dec_ref(v_x_246_);
v___x_248_ = 0;
return v___x_248_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_binderInfoEx___boxed(lean_object* v_x_249_){
_start:
{
uint8_t v_res_250_; lean_object* v_r_251_; 
v_res_250_ = lean_local_decl_binder_info(v_x_249_);
v_r_251_ = lean_box(v_res_250_);
return v_r_251_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isLet(lean_object* v_x_252_, uint8_t v_x_253_){
_start:
{
if (lean_obj_tag(v_x_252_) == 0)
{
uint8_t v___x_254_; 
v___x_254_ = 0;
return v___x_254_;
}
else
{
uint8_t v_nondep_255_; 
v_nondep_255_ = lean_ctor_get_uint8(v_x_252_, sizeof(void*)*5);
if (v_nondep_255_ == 0)
{
uint8_t v___x_256_; 
v___x_256_ = 1;
return v___x_256_;
}
else
{
return v_x_253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isLet___boxed(lean_object* v_x_257_, lean_object* v_x_258_){
_start:
{
uint8_t v_x_53__boxed_259_; uint8_t v_res_260_; lean_object* v_r_261_; 
v_x_53__boxed_259_ = lean_unbox(v_x_258_);
v_res_260_ = l_Lean_LocalDecl_isLet(v_x_257_, v_x_53__boxed_259_);
lean_dec_ref(v_x_257_);
v_r_261_ = lean_box(v_res_260_);
return v_r_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_index(lean_object* v_x_262_){
_start:
{
lean_object* v_index_263_; 
v_index_263_ = lean_ctor_get(v_x_262_, 0);
lean_inc(v_index_263_);
return v_index_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_index___boxed(lean_object* v_x_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Lean_LocalDecl_index(v_x_264_);
lean_dec_ref(v_x_264_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setIndex(lean_object* v_x_266_, lean_object* v_x_267_){
_start:
{
if (lean_obj_tag(v_x_266_) == 0)
{
lean_object* v_fvarId_268_; lean_object* v_userName_269_; lean_object* v_type_270_; uint8_t v_bi_271_; uint8_t v_kind_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_279_; 
v_fvarId_268_ = lean_ctor_get(v_x_266_, 1);
v_userName_269_ = lean_ctor_get(v_x_266_, 2);
v_type_270_ = lean_ctor_get(v_x_266_, 3);
v_bi_271_ = lean_ctor_get_uint8(v_x_266_, sizeof(void*)*4);
v_kind_272_ = lean_ctor_get_uint8(v_x_266_, sizeof(void*)*4 + 1);
v_isSharedCheck_279_ = !lean_is_exclusive(v_x_266_);
if (v_isSharedCheck_279_ == 0)
{
lean_object* v_unused_280_; 
v_unused_280_ = lean_ctor_get(v_x_266_, 0);
lean_dec(v_unused_280_);
v___x_274_ = v_x_266_;
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_type_270_);
lean_inc(v_userName_269_);
lean_inc(v_fvarId_268_);
lean_dec(v_x_266_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_277_; 
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 0, v_x_267_);
v___x_277_ = v___x_274_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_x_267_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v_fvarId_268_);
lean_ctor_set(v_reuseFailAlloc_278_, 2, v_userName_269_);
lean_ctor_set(v_reuseFailAlloc_278_, 3, v_type_270_);
lean_ctor_set_uint8(v_reuseFailAlloc_278_, sizeof(void*)*4, v_bi_271_);
lean_ctor_set_uint8(v_reuseFailAlloc_278_, sizeof(void*)*4 + 1, v_kind_272_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
else
{
lean_object* v_fvarId_281_; lean_object* v_userName_282_; lean_object* v_type_283_; lean_object* v_value_284_; uint8_t v_nondep_285_; uint8_t v_kind_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
v_fvarId_281_ = lean_ctor_get(v_x_266_, 1);
v_userName_282_ = lean_ctor_get(v_x_266_, 2);
v_type_283_ = lean_ctor_get(v_x_266_, 3);
v_value_284_ = lean_ctor_get(v_x_266_, 4);
v_nondep_285_ = lean_ctor_get_uint8(v_x_266_, sizeof(void*)*5);
v_kind_286_ = lean_ctor_get_uint8(v_x_266_, sizeof(void*)*5 + 1);
v_isSharedCheck_293_ = !lean_is_exclusive(v_x_266_);
if (v_isSharedCheck_293_ == 0)
{
lean_object* v_unused_294_; 
v_unused_294_ = lean_ctor_get(v_x_266_, 0);
lean_dec(v_unused_294_);
v___x_288_ = v_x_266_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_value_284_);
lean_inc(v_type_283_);
lean_inc(v_userName_282_);
lean_inc(v_fvarId_281_);
lean_dec(v_x_266_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 0, v_x_267_);
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_x_267_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v_fvarId_281_);
lean_ctor_set(v_reuseFailAlloc_292_, 2, v_userName_282_);
lean_ctor_set(v_reuseFailAlloc_292_, 3, v_type_283_);
lean_ctor_set(v_reuseFailAlloc_292_, 4, v_value_284_);
lean_ctor_set_uint8(v_reuseFailAlloc_292_, sizeof(void*)*5, v_nondep_285_);
lean_ctor_set_uint8(v_reuseFailAlloc_292_, sizeof(void*)*5 + 1, v_kind_286_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_fvarId(lean_object* v_x_295_){
_start:
{
lean_object* v_fvarId_296_; 
v_fvarId_296_ = lean_ctor_get(v_x_295_, 1);
lean_inc(v_fvarId_296_);
return v_fvarId_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_fvarId___boxed(lean_object* v_x_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lean_LocalDecl_fvarId(v_x_297_);
lean_dec_ref(v_x_297_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_userName(lean_object* v_x_299_){
_start:
{
lean_object* v_userName_300_; 
v_userName_300_ = lean_ctor_get(v_x_299_, 2);
lean_inc(v_userName_300_);
return v_userName_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_userName___boxed(lean_object* v_x_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_LocalDecl_userName(v_x_301_);
lean_dec_ref(v_x_301_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_type(lean_object* v_x_303_){
_start:
{
lean_object* v_type_304_; 
v_type_304_ = lean_ctor_get(v_x_303_, 3);
lean_inc_ref(v_type_304_);
return v_type_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_type___boxed(lean_object* v_x_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_LocalDecl_type(v_x_305_);
lean_dec_ref(v_x_305_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setType(lean_object* v_x_307_, lean_object* v_x_308_){
_start:
{
if (lean_obj_tag(v_x_307_) == 0)
{
lean_object* v_index_309_; lean_object* v_fvarId_310_; lean_object* v_userName_311_; uint8_t v_bi_312_; uint8_t v_kind_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_320_; 
v_index_309_ = lean_ctor_get(v_x_307_, 0);
v_fvarId_310_ = lean_ctor_get(v_x_307_, 1);
v_userName_311_ = lean_ctor_get(v_x_307_, 2);
v_bi_312_ = lean_ctor_get_uint8(v_x_307_, sizeof(void*)*4);
v_kind_313_ = lean_ctor_get_uint8(v_x_307_, sizeof(void*)*4 + 1);
v_isSharedCheck_320_ = !lean_is_exclusive(v_x_307_);
if (v_isSharedCheck_320_ == 0)
{
lean_object* v_unused_321_; 
v_unused_321_ = lean_ctor_get(v_x_307_, 3);
lean_dec(v_unused_321_);
v___x_315_ = v_x_307_;
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_userName_311_);
lean_inc(v_fvarId_310_);
lean_inc(v_index_309_);
lean_dec(v_x_307_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 3, v_x_308_);
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_index_309_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v_fvarId_310_);
lean_ctor_set(v_reuseFailAlloc_319_, 2, v_userName_311_);
lean_ctor_set(v_reuseFailAlloc_319_, 3, v_x_308_);
lean_ctor_set_uint8(v_reuseFailAlloc_319_, sizeof(void*)*4, v_bi_312_);
lean_ctor_set_uint8(v_reuseFailAlloc_319_, sizeof(void*)*4 + 1, v_kind_313_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
else
{
lean_object* v_index_322_; lean_object* v_fvarId_323_; lean_object* v_userName_324_; lean_object* v_value_325_; uint8_t v_nondep_326_; uint8_t v_kind_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_334_; 
v_index_322_ = lean_ctor_get(v_x_307_, 0);
v_fvarId_323_ = lean_ctor_get(v_x_307_, 1);
v_userName_324_ = lean_ctor_get(v_x_307_, 2);
v_value_325_ = lean_ctor_get(v_x_307_, 4);
v_nondep_326_ = lean_ctor_get_uint8(v_x_307_, sizeof(void*)*5);
v_kind_327_ = lean_ctor_get_uint8(v_x_307_, sizeof(void*)*5 + 1);
v_isSharedCheck_334_ = !lean_is_exclusive(v_x_307_);
if (v_isSharedCheck_334_ == 0)
{
lean_object* v_unused_335_; 
v_unused_335_ = lean_ctor_get(v_x_307_, 3);
lean_dec(v_unused_335_);
v___x_329_ = v_x_307_;
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_value_325_);
lean_inc(v_userName_324_);
lean_inc(v_fvarId_323_);
lean_inc(v_index_322_);
lean_dec(v_x_307_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_332_; 
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 3, v_x_308_);
v___x_332_ = v___x_329_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_index_322_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v_fvarId_323_);
lean_ctor_set(v_reuseFailAlloc_333_, 2, v_userName_324_);
lean_ctor_set(v_reuseFailAlloc_333_, 3, v_x_308_);
lean_ctor_set(v_reuseFailAlloc_333_, 4, v_value_325_);
lean_ctor_set_uint8(v_reuseFailAlloc_333_, sizeof(void*)*5, v_nondep_326_);
lean_ctor_set_uint8(v_reuseFailAlloc_333_, sizeof(void*)*5 + 1, v_kind_327_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_binderInfo(lean_object* v_x_336_){
_start:
{
if (lean_obj_tag(v_x_336_) == 0)
{
uint8_t v_bi_337_; 
v_bi_337_ = lean_ctor_get_uint8(v_x_336_, sizeof(void*)*4);
return v_bi_337_;
}
else
{
uint8_t v___x_338_; 
v___x_338_ = 0;
return v___x_338_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_binderInfo___boxed(lean_object* v_x_339_){
_start:
{
uint8_t v_res_340_; lean_object* v_r_341_; 
v_res_340_ = l_Lean_LocalDecl_binderInfo(v_x_339_);
lean_dec_ref(v_x_339_);
v_r_341_ = lean_box(v_res_340_);
return v_r_341_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_kind(lean_object* v_x_342_){
_start:
{
if (lean_obj_tag(v_x_342_) == 0)
{
uint8_t v_kind_343_; 
v_kind_343_ = lean_ctor_get_uint8(v_x_342_, sizeof(void*)*4 + 1);
return v_kind_343_;
}
else
{
uint8_t v_kind_344_; 
v_kind_344_ = lean_ctor_get_uint8(v_x_342_, sizeof(void*)*5 + 1);
return v_kind_344_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_kind___boxed(lean_object* v_x_345_){
_start:
{
uint8_t v_res_346_; lean_object* v_r_347_; 
v_res_346_ = l_Lean_LocalDecl_kind(v_x_345_);
lean_dec_ref(v_x_345_);
v_r_347_ = lean_box(v_res_346_);
return v_r_347_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object* v_d_348_){
_start:
{
uint8_t v___y_350_; 
if (lean_obj_tag(v_d_348_) == 0)
{
uint8_t v_kind_353_; 
v_kind_353_ = lean_ctor_get_uint8(v_d_348_, sizeof(void*)*4 + 1);
v___y_350_ = v_kind_353_;
goto v___jp_349_;
}
else
{
uint8_t v_kind_354_; 
v_kind_354_ = lean_ctor_get_uint8(v_d_348_, sizeof(void*)*5 + 1);
v___y_350_ = v_kind_354_;
goto v___jp_349_;
}
v___jp_349_:
{
uint8_t v___x_351_; uint8_t v___x_352_; 
v___x_351_ = 2;
v___x_352_ = l_Lean_instDecidableEqLocalDeclKind(v___y_350_, v___x_351_);
return v___x_352_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isAuxDecl___boxed(lean_object* v_d_355_){
_start:
{
uint8_t v_res_356_; lean_object* v_r_357_; 
v_res_356_ = l_Lean_LocalDecl_isAuxDecl(v_d_355_);
lean_dec_ref(v_d_355_);
v_r_357_ = lean_box(v_res_356_);
return v_r_357_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object* v_d_358_){
_start:
{
uint8_t v___y_360_; 
if (lean_obj_tag(v_d_358_) == 0)
{
uint8_t v_kind_365_; 
v_kind_365_ = lean_ctor_get_uint8(v_d_358_, sizeof(void*)*4 + 1);
v___y_360_ = v_kind_365_;
goto v___jp_359_;
}
else
{
uint8_t v_kind_366_; 
v_kind_366_ = lean_ctor_get_uint8(v_d_358_, sizeof(void*)*5 + 1);
v___y_360_ = v_kind_366_;
goto v___jp_359_;
}
v___jp_359_:
{
uint8_t v___x_361_; uint8_t v___x_362_; 
v___x_361_ = 0;
v___x_362_ = l_Lean_instDecidableEqLocalDeclKind(v___y_360_, v___x_361_);
if (v___x_362_ == 0)
{
uint8_t v___x_363_; 
v___x_363_ = 1;
return v___x_363_;
}
else
{
uint8_t v___x_364_; 
v___x_364_ = 0;
return v___x_364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isImplementationDetail___boxed(lean_object* v_d_367_){
_start:
{
uint8_t v_res_368_; lean_object* v_r_369_; 
v_res_368_ = l_Lean_LocalDecl_isImplementationDetail(v_d_367_);
lean_dec_ref(v_d_367_);
v_r_369_ = lean_box(v_res_368_);
return v_r_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value_x3f(lean_object* v_x_370_, uint8_t v_x_371_){
_start:
{
if (lean_obj_tag(v_x_370_) == 1)
{
uint8_t v_nondep_372_; 
v_nondep_372_ = lean_ctor_get_uint8(v_x_370_, sizeof(void*)*5);
if (v_nondep_372_ == 0)
{
lean_object* v_value_373_; lean_object* v___x_374_; 
v_value_373_ = lean_ctor_get(v_x_370_, 4);
lean_inc_ref(v_value_373_);
v___x_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_374_, 0, v_value_373_);
return v___x_374_;
}
else
{
if (v_x_371_ == 1)
{
lean_object* v_value_375_; lean_object* v___x_376_; 
v_value_375_ = lean_ctor_get(v_x_370_, 4);
lean_inc_ref(v_value_375_);
v___x_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_376_, 0, v_value_375_);
return v___x_376_;
}
else
{
lean_object* v___x_377_; 
v___x_377_ = lean_box(0);
return v___x_377_;
}
}
}
else
{
lean_object* v___x_378_; 
v___x_378_ = lean_box(0);
return v___x_378_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value_x3f___boxed(lean_object* v_x_379_, lean_object* v_x_380_){
_start:
{
uint8_t v_x_57__boxed_381_; lean_object* v_res_382_; 
v_x_57__boxed_381_ = lean_unbox(v_x_380_);
v_res_382_ = l_Lean_LocalDecl_value_x3f(v_x_379_, v_x_57__boxed_381_);
lean_dec_ref(v_x_379_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_LocalDecl_value_spec__0(lean_object* v_msg_383_){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = l_Lean_instInhabitedExpr;
v___x_385_ = lean_panic_fn(v___x_384_, v_msg_383_);
return v___x_385_;
}
}
static lean_object* _init_l_Lean_LocalDecl_value___closed__3(void){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_389_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__2));
v___x_390_ = lean_unsigned_to_nat(54u);
v___x_391_ = lean_unsigned_to_nat(172u);
v___x_392_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__1));
v___x_393_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_394_ = l_mkPanicMessageWithDecl(v___x_393_, v___x_392_, v___x_391_, v___x_390_, v___x_389_);
return v___x_394_;
}
}
static lean_object* _init_l_Lean_LocalDecl_value___closed__5(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_396_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__4));
v___x_397_ = lean_unsigned_to_nat(54u);
v___x_398_ = lean_unsigned_to_nat(175u);
v___x_399_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__1));
v___x_400_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_401_ = l_mkPanicMessageWithDecl(v___x_400_, v___x_399_, v___x_398_, v___x_397_, v___x_396_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value(lean_object* v_x_402_, uint8_t v_x_403_){
_start:
{
if (lean_obj_tag(v_x_402_) == 0)
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = lean_obj_once(&l_Lean_LocalDecl_value___closed__3, &l_Lean_LocalDecl_value___closed__3_once, _init_l_Lean_LocalDecl_value___closed__3);
v___x_405_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_404_);
return v___x_405_;
}
else
{
uint8_t v_nondep_406_; 
v_nondep_406_ = lean_ctor_get_uint8(v_x_402_, sizeof(void*)*5);
if (v_nondep_406_ == 0)
{
lean_object* v_value_407_; 
v_value_407_ = lean_ctor_get(v_x_402_, 4);
lean_inc_ref(v_value_407_);
return v_value_407_;
}
else
{
if (v_x_403_ == 0)
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = lean_obj_once(&l_Lean_LocalDecl_value___closed__5, &l_Lean_LocalDecl_value___closed__5_once, _init_l_Lean_LocalDecl_value___closed__5);
v___x_409_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_408_);
return v___x_409_;
}
else
{
lean_object* v_value_410_; 
v_value_410_ = lean_ctor_get(v_x_402_, 4);
lean_inc_ref(v_value_410_);
return v_value_410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value___boxed(lean_object* v_x_411_, lean_object* v_x_412_){
_start:
{
uint8_t v_x_143__boxed_413_; lean_object* v_res_414_; 
v_x_143__boxed_413_ = lean_unbox(v_x_412_);
v_res_414_ = l_Lean_LocalDecl_value(v_x_411_, v_x_143__boxed_413_);
lean_dec_ref(v_x_411_);
return v_res_414_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_hasValue(lean_object* v_x_415_, uint8_t v_x_416_){
_start:
{
if (lean_obj_tag(v_x_415_) == 0)
{
uint8_t v___x_417_; 
v___x_417_ = 0;
return v___x_417_;
}
else
{
uint8_t v_nondep_418_; 
v_nondep_418_ = lean_ctor_get_uint8(v_x_415_, sizeof(void*)*5);
if (v_nondep_418_ == 0)
{
uint8_t v___x_419_; 
v___x_419_ = 1;
return v___x_419_;
}
else
{
return v_x_416_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_hasValue___boxed(lean_object* v_x_420_, lean_object* v_x_421_){
_start:
{
uint8_t v_x_72__boxed_422_; uint8_t v_res_423_; lean_object* v_r_424_; 
v_x_72__boxed_422_ = lean_unbox(v_x_421_);
v_res_423_ = l_Lean_LocalDecl_hasValue(v_x_420_, v_x_72__boxed_422_);
lean_dec_ref(v_x_420_);
v_r_424_ = lean_box(v_res_423_);
return v_r_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setValue(lean_object* v_x_425_, lean_object* v_x_426_){
_start:
{
if (lean_obj_tag(v_x_425_) == 1)
{
lean_object* v_index_427_; lean_object* v_fvarId_428_; lean_object* v_userName_429_; lean_object* v_type_430_; uint8_t v_nondep_431_; uint8_t v_kind_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_439_; 
v_index_427_ = lean_ctor_get(v_x_425_, 0);
v_fvarId_428_ = lean_ctor_get(v_x_425_, 1);
v_userName_429_ = lean_ctor_get(v_x_425_, 2);
v_type_430_ = lean_ctor_get(v_x_425_, 3);
v_nondep_431_ = lean_ctor_get_uint8(v_x_425_, sizeof(void*)*5);
v_kind_432_ = lean_ctor_get_uint8(v_x_425_, sizeof(void*)*5 + 1);
v_isSharedCheck_439_ = !lean_is_exclusive(v_x_425_);
if (v_isSharedCheck_439_ == 0)
{
lean_object* v_unused_440_; 
v_unused_440_ = lean_ctor_get(v_x_425_, 4);
lean_dec(v_unused_440_);
v___x_434_ = v_x_425_;
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_type_430_);
lean_inc(v_userName_429_);
lean_inc(v_fvarId_428_);
lean_inc(v_index_427_);
lean_dec(v_x_425_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 4, v_x_426_);
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_index_427_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v_fvarId_428_);
lean_ctor_set(v_reuseFailAlloc_438_, 2, v_userName_429_);
lean_ctor_set(v_reuseFailAlloc_438_, 3, v_type_430_);
lean_ctor_set(v_reuseFailAlloc_438_, 4, v_x_426_);
lean_ctor_set_uint8(v_reuseFailAlloc_438_, sizeof(void*)*5, v_nondep_431_);
lean_ctor_set_uint8(v_reuseFailAlloc_438_, sizeof(void*)*5 + 1, v_kind_432_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
else
{
lean_dec_ref(v_x_426_);
return v_x_425_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setNondep(lean_object* v_x_441_, uint8_t v_x_442_){
_start:
{
if (lean_obj_tag(v_x_441_) == 1)
{
lean_object* v_index_443_; lean_object* v_fvarId_444_; lean_object* v_userName_445_; lean_object* v_type_446_; lean_object* v_value_447_; uint8_t v_kind_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_455_; 
v_index_443_ = lean_ctor_get(v_x_441_, 0);
v_fvarId_444_ = lean_ctor_get(v_x_441_, 1);
v_userName_445_ = lean_ctor_get(v_x_441_, 2);
v_type_446_ = lean_ctor_get(v_x_441_, 3);
v_value_447_ = lean_ctor_get(v_x_441_, 4);
v_kind_448_ = lean_ctor_get_uint8(v_x_441_, sizeof(void*)*5 + 1);
v_isSharedCheck_455_ = !lean_is_exclusive(v_x_441_);
if (v_isSharedCheck_455_ == 0)
{
v___x_450_ = v_x_441_;
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_value_447_);
lean_inc(v_type_446_);
lean_inc(v_userName_445_);
lean_inc(v_fvarId_444_);
lean_inc(v_index_443_);
lean_dec(v_x_441_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_453_; 
if (v_isShared_451_ == 0)
{
v___x_453_ = v___x_450_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_index_443_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_fvarId_444_);
lean_ctor_set(v_reuseFailAlloc_454_, 2, v_userName_445_);
lean_ctor_set(v_reuseFailAlloc_454_, 3, v_type_446_);
lean_ctor_set(v_reuseFailAlloc_454_, 4, v_value_447_);
lean_ctor_set_uint8(v_reuseFailAlloc_454_, sizeof(void*)*5 + 1, v_kind_448_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
lean_ctor_set_uint8(v___x_453_, sizeof(void*)*5, v_x_442_);
return v___x_453_;
}
}
}
else
{
return v_x_441_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setNondep___boxed(lean_object* v_x_456_, lean_object* v_x_457_){
_start:
{
uint8_t v_x_27__boxed_458_; lean_object* v_res_459_; 
v_x_27__boxed_458_ = lean_unbox(v_x_457_);
v_res_459_ = l_Lean_LocalDecl_setNondep(v_x_456_, v_x_27__boxed_458_);
return v_res_459_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isNondep(lean_object* v_x_460_){
_start:
{
if (lean_obj_tag(v_x_460_) == 1)
{
uint8_t v_nondep_461_; 
v_nondep_461_ = lean_ctor_get_uint8(v_x_460_, sizeof(void*)*5);
return v_nondep_461_;
}
else
{
uint8_t v___x_462_; 
v___x_462_ = 0;
return v___x_462_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isNondep___boxed(lean_object* v_x_463_){
_start:
{
uint8_t v_res_464_; lean_object* v_r_465_; 
v_res_464_ = l_Lean_LocalDecl_isNondep(v_x_463_);
lean_dec_ref(v_x_463_);
v_r_465_ = lean_box(v_res_464_);
return v_r_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setUserName(lean_object* v_x_466_, lean_object* v_x_467_){
_start:
{
if (lean_obj_tag(v_x_466_) == 0)
{
lean_object* v_index_468_; lean_object* v_fvarId_469_; lean_object* v_type_470_; uint8_t v_bi_471_; uint8_t v_kind_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
v_index_468_ = lean_ctor_get(v_x_466_, 0);
v_fvarId_469_ = lean_ctor_get(v_x_466_, 1);
v_type_470_ = lean_ctor_get(v_x_466_, 3);
v_bi_471_ = lean_ctor_get_uint8(v_x_466_, sizeof(void*)*4);
v_kind_472_ = lean_ctor_get_uint8(v_x_466_, sizeof(void*)*4 + 1);
v_isSharedCheck_479_ = !lean_is_exclusive(v_x_466_);
if (v_isSharedCheck_479_ == 0)
{
lean_object* v_unused_480_; 
v_unused_480_ = lean_ctor_get(v_x_466_, 2);
lean_dec(v_unused_480_);
v___x_474_ = v_x_466_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_type_470_);
lean_inc(v_fvarId_469_);
lean_inc(v_index_468_);
lean_dec(v_x_466_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 2, v_x_467_);
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_index_468_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v_fvarId_469_);
lean_ctor_set(v_reuseFailAlloc_478_, 2, v_x_467_);
lean_ctor_set(v_reuseFailAlloc_478_, 3, v_type_470_);
lean_ctor_set_uint8(v_reuseFailAlloc_478_, sizeof(void*)*4, v_bi_471_);
lean_ctor_set_uint8(v_reuseFailAlloc_478_, sizeof(void*)*4 + 1, v_kind_472_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
else
{
lean_object* v_index_481_; lean_object* v_fvarId_482_; lean_object* v_type_483_; lean_object* v_value_484_; uint8_t v_nondep_485_; uint8_t v_kind_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_493_; 
v_index_481_ = lean_ctor_get(v_x_466_, 0);
v_fvarId_482_ = lean_ctor_get(v_x_466_, 1);
v_type_483_ = lean_ctor_get(v_x_466_, 3);
v_value_484_ = lean_ctor_get(v_x_466_, 4);
v_nondep_485_ = lean_ctor_get_uint8(v_x_466_, sizeof(void*)*5);
v_kind_486_ = lean_ctor_get_uint8(v_x_466_, sizeof(void*)*5 + 1);
v_isSharedCheck_493_ = !lean_is_exclusive(v_x_466_);
if (v_isSharedCheck_493_ == 0)
{
lean_object* v_unused_494_; 
v_unused_494_ = lean_ctor_get(v_x_466_, 2);
lean_dec(v_unused_494_);
v___x_488_ = v_x_466_;
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_value_484_);
lean_inc(v_type_483_);
lean_inc(v_fvarId_482_);
lean_inc(v_index_481_);
lean_dec(v_x_466_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 2, v_x_467_);
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_index_481_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v_fvarId_482_);
lean_ctor_set(v_reuseFailAlloc_492_, 2, v_x_467_);
lean_ctor_set(v_reuseFailAlloc_492_, 3, v_type_483_);
lean_ctor_set(v_reuseFailAlloc_492_, 4, v_value_484_);
lean_ctor_set_uint8(v_reuseFailAlloc_492_, sizeof(void*)*5, v_nondep_485_);
lean_ctor_set_uint8(v_reuseFailAlloc_492_, sizeof(void*)*5 + 1, v_kind_486_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(lean_object* v_msg_495_){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = l_Lean_instInhabitedLocalDecl_default;
v___x_497_ = lean_panic_fn(v___x_496_, v_msg_495_);
return v___x_497_;
}
}
static lean_object* _init_l_Lean_LocalDecl_setBinderInfo___closed__2(void){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_500_ = ((lean_object*)(l_Lean_LocalDecl_setBinderInfo___closed__1));
v___x_501_ = lean_unsigned_to_nat(38u);
v___x_502_ = lean_unsigned_to_nat(237u);
v___x_503_ = ((lean_object*)(l_Lean_LocalDecl_setBinderInfo___closed__0));
v___x_504_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_505_ = l_mkPanicMessageWithDecl(v___x_504_, v___x_503_, v___x_502_, v___x_501_, v___x_500_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setBinderInfo(lean_object* v_x_506_, uint8_t v_x_507_){
_start:
{
if (lean_obj_tag(v_x_506_) == 0)
{
lean_object* v_index_508_; lean_object* v_fvarId_509_; lean_object* v_userName_510_; lean_object* v_type_511_; uint8_t v_kind_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
v_index_508_ = lean_ctor_get(v_x_506_, 0);
v_fvarId_509_ = lean_ctor_get(v_x_506_, 1);
v_userName_510_ = lean_ctor_get(v_x_506_, 2);
v_type_511_ = lean_ctor_get(v_x_506_, 3);
v_kind_512_ = lean_ctor_get_uint8(v_x_506_, sizeof(void*)*4 + 1);
v_isSharedCheck_519_ = !lean_is_exclusive(v_x_506_);
if (v_isSharedCheck_519_ == 0)
{
v___x_514_ = v_x_506_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_type_511_);
lean_inc(v_userName_510_);
lean_inc(v_fvarId_509_);
lean_inc(v_index_508_);
lean_dec(v_x_506_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_517_; 
if (v_isShared_515_ == 0)
{
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_index_508_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v_fvarId_509_);
lean_ctor_set(v_reuseFailAlloc_518_, 2, v_userName_510_);
lean_ctor_set(v_reuseFailAlloc_518_, 3, v_type_511_);
lean_ctor_set_uint8(v_reuseFailAlloc_518_, sizeof(void*)*4 + 1, v_kind_512_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
lean_ctor_set_uint8(v___x_517_, sizeof(void*)*4, v_x_507_);
return v___x_517_;
}
}
}
else
{
lean_object* v___x_520_; lean_object* v___x_521_; 
lean_dec_ref(v_x_506_);
v___x_520_ = lean_obj_once(&l_Lean_LocalDecl_setBinderInfo___closed__2, &l_Lean_LocalDecl_setBinderInfo___closed__2_once, _init_l_Lean_LocalDecl_setBinderInfo___closed__2);
v___x_521_ = l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(v___x_520_);
return v___x_521_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setBinderInfo___boxed(lean_object* v_x_522_, lean_object* v_x_523_){
_start:
{
uint8_t v_x_84__boxed_524_; lean_object* v_res_525_; 
v_x_84__boxed_524_ = lean_unbox(v_x_523_);
v_res_525_ = l_Lean_LocalDecl_setBinderInfo(v_x_522_, v_x_84__boxed_524_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_toExpr(lean_object* v_decl_526_){
_start:
{
lean_object* v_fvarId_527_; lean_object* v___x_528_; 
v_fvarId_527_ = lean_ctor_get(v_decl_526_, 1);
lean_inc(v_fvarId_527_);
lean_dec_ref(v_decl_526_);
v___x_528_ = l_Lean_mkFVar(v_fvarId_527_);
return v___x_528_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_hasExprMVar(lean_object* v_x_529_){
_start:
{
if (lean_obj_tag(v_x_529_) == 0)
{
lean_object* v_type_530_; uint8_t v___x_531_; 
v_type_530_ = lean_ctor_get(v_x_529_, 3);
v___x_531_ = l_Lean_Expr_hasExprMVar(v_type_530_);
return v___x_531_;
}
else
{
lean_object* v_type_532_; lean_object* v_value_533_; uint8_t v___x_534_; 
v_type_532_ = lean_ctor_get(v_x_529_, 3);
v_value_533_ = lean_ctor_get(v_x_529_, 4);
v___x_534_ = l_Lean_Expr_hasExprMVar(v_type_532_);
if (v___x_534_ == 0)
{
uint8_t v___x_535_; 
v___x_535_ = l_Lean_Expr_hasExprMVar(v_value_533_);
return v___x_535_;
}
else
{
return v___x_534_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_hasExprMVar___boxed(lean_object* v_x_536_){
_start:
{
uint8_t v_res_537_; lean_object* v_r_538_; 
v_res_537_ = l_Lean_LocalDecl_hasExprMVar(v_x_536_);
lean_dec_ref(v_x_536_);
v_r_538_ = lean_box(v_res_537_);
return v_r_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setKind(lean_object* v_x_539_, uint8_t v_x_540_){
_start:
{
if (lean_obj_tag(v_x_539_) == 0)
{
lean_object* v_index_541_; lean_object* v_fvarId_542_; lean_object* v_userName_543_; lean_object* v_type_544_; uint8_t v_bi_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
v_index_541_ = lean_ctor_get(v_x_539_, 0);
v_fvarId_542_ = lean_ctor_get(v_x_539_, 1);
v_userName_543_ = lean_ctor_get(v_x_539_, 2);
v_type_544_ = lean_ctor_get(v_x_539_, 3);
v_bi_545_ = lean_ctor_get_uint8(v_x_539_, sizeof(void*)*4);
v_isSharedCheck_552_ = !lean_is_exclusive(v_x_539_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v_x_539_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_type_544_);
lean_inc(v_userName_543_);
lean_inc(v_fvarId_542_);
lean_inc(v_index_541_);
lean_dec(v_x_539_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_index_541_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v_fvarId_542_);
lean_ctor_set(v_reuseFailAlloc_551_, 2, v_userName_543_);
lean_ctor_set(v_reuseFailAlloc_551_, 3, v_type_544_);
lean_ctor_set_uint8(v_reuseFailAlloc_551_, sizeof(void*)*4, v_bi_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
lean_ctor_set_uint8(v___x_550_, sizeof(void*)*4 + 1, v_x_540_);
return v___x_550_;
}
}
}
else
{
lean_object* v_index_553_; lean_object* v_fvarId_554_; lean_object* v_userName_555_; lean_object* v_type_556_; lean_object* v_value_557_; uint8_t v_nondep_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_565_; 
v_index_553_ = lean_ctor_get(v_x_539_, 0);
v_fvarId_554_ = lean_ctor_get(v_x_539_, 1);
v_userName_555_ = lean_ctor_get(v_x_539_, 2);
v_type_556_ = lean_ctor_get(v_x_539_, 3);
v_value_557_ = lean_ctor_get(v_x_539_, 4);
v_nondep_558_ = lean_ctor_get_uint8(v_x_539_, sizeof(void*)*5);
v_isSharedCheck_565_ = !lean_is_exclusive(v_x_539_);
if (v_isSharedCheck_565_ == 0)
{
v___x_560_ = v_x_539_;
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_value_557_);
lean_inc(v_type_556_);
lean_inc(v_userName_555_);
lean_inc(v_fvarId_554_);
lean_inc(v_index_553_);
lean_dec(v_x_539_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_563_; 
if (v_isShared_561_ == 0)
{
v___x_563_ = v___x_560_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_index_553_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_fvarId_554_);
lean_ctor_set(v_reuseFailAlloc_564_, 2, v_userName_555_);
lean_ctor_set(v_reuseFailAlloc_564_, 3, v_type_556_);
lean_ctor_set(v_reuseFailAlloc_564_, 4, v_value_557_);
lean_ctor_set_uint8(v_reuseFailAlloc_564_, sizeof(void*)*5, v_nondep_558_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
lean_ctor_set_uint8(v___x_563_, sizeof(void*)*5 + 1, v_x_540_);
return v___x_563_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setKind___boxed(lean_object* v_x_566_, lean_object* v_x_567_){
_start:
{
uint8_t v_x_31__boxed_568_; lean_object* v_res_569_; 
v_x_31__boxed_568_ = lean_unbox(v_x_567_);
v_res_569_ = l_Lean_LocalDecl_setKind(v_x_566_, v_x_31__boxed_568_);
return v_res_569_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__0(void){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_570_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__1(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__0, &l_Lean_instInhabitedLocalContext_default___closed__0_once, _init_l_Lean_instInhabitedLocalContext_default___closed__0);
v___x_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
return v___x_572_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__2(void){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_573_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__3(void){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_574_ = lean_box(1);
v___x_575_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__2, &l_Lean_instInhabitedLocalContext_default___closed__2_once, _init_l_Lean_instInhabitedLocalContext_default___closed__2);
v___x_576_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__1, &l_Lean_instInhabitedLocalContext_default___closed__1_once, _init_l_Lean_instInhabitedLocalContext_default___closed__1);
v___x_577_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
lean_ctor_set(v___x_577_, 1, v___x_575_);
lean_ctor_set(v___x_577_, 2, v___x_574_);
return v___x_577_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default(void){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__3, &l_Lean_instInhabitedLocalContext_default___closed__3_once, _init_l_Lean_instInhabitedLocalContext_default___closed__3);
return v___x_578_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext(void){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Lean_instInhabitedLocalContext_default;
return v___x_579_;
}
}
static lean_object* _init_l_Lean_LocalContext_mkEmpty___closed__0(void){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_580_ = lean_unsigned_to_nat(32u);
v___x_581_ = lean_mk_empty_array_with_capacity(v___x_580_);
v___x_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
return v___x_582_;
}
}
static lean_object* _init_l_Lean_LocalContext_mkEmpty___closed__1(void){
_start:
{
size_t v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_583_ = ((size_t)5ULL);
v___x_584_ = lean_unsigned_to_nat(0u);
v___x_585_ = lean_unsigned_to_nat(32u);
v___x_586_ = lean_mk_empty_array_with_capacity(v___x_585_);
v___x_587_ = lean_obj_once(&l_Lean_LocalContext_mkEmpty___closed__0, &l_Lean_LocalContext_mkEmpty___closed__0_once, _init_l_Lean_LocalContext_mkEmpty___closed__0);
v___x_588_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_588_, 0, v___x_587_);
lean_ctor_set(v___x_588_, 1, v___x_586_);
lean_ctor_set(v___x_588_, 2, v___x_584_);
lean_ctor_set(v___x_588_, 3, v___x_584_);
lean_ctor_set_usize(v___x_588_, 4, v___x_583_);
return v___x_588_;
}
}
static lean_object* _init_l_Lean_LocalContext_mkEmpty___closed__2(void){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_589_ = lean_box(1);
v___x_590_ = lean_obj_once(&l_Lean_LocalContext_mkEmpty___closed__1, &l_Lean_LocalContext_mkEmpty___closed__1_once, _init_l_Lean_LocalContext_mkEmpty___closed__1);
v___x_591_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__1, &l_Lean_instInhabitedLocalContext_default___closed__1_once, _init_l_Lean_instInhabitedLocalContext_default___closed__1);
v___x_592_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
lean_ctor_set(v___x_592_, 1, v___x_590_);
lean_ctor_set(v___x_592_, 2, v___x_589_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* lean_mk_empty_local_ctx(lean_object* v_x_593_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = lean_obj_once(&l_Lean_LocalContext_mkEmpty___closed__2, &l_Lean_LocalContext_mkEmpty___closed__2_once, _init_l_Lean_LocalContext_mkEmpty___closed__2);
return v___x_594_;
}
}
static lean_object* _init_l_Lean_LocalContext_empty(void){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_595_ = lean_unsigned_to_nat(32u);
v___x_596_ = lean_mk_empty_array_with_capacity(v___x_595_);
lean_dec_ref(v___x_596_);
v___x_597_ = lean_obj_once(&l_Lean_LocalContext_mkEmpty___closed__2, &l_Lean_LocalContext_mkEmpty___closed__2_once, _init_l_Lean_LocalContext_mkEmpty___closed__2);
return v___x_597_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg(lean_object* v_x_598_){
_start:
{
uint8_t v___x_599_; 
v___x_599_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg___boxed(lean_object* v_x_600_){
_start:
{
uint8_t v_res_601_; lean_object* v_r_602_; 
v_res_601_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg(v_x_600_);
lean_dec_ref(v_x_600_);
v_r_602_ = lean_box(v_res_601_);
return v_r_602_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0(lean_object* v_00_u03b2_603_, lean_object* v_x_604_){
_start:
{
uint8_t v___x_605_; 
v___x_605_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___boxed(lean_object* v_00_u03b2_606_, lean_object* v_x_607_){
_start:
{
uint8_t v_res_608_; lean_object* v_r_609_; 
v_res_608_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0(v_00_u03b2_606_, v_x_607_);
lean_dec_ref(v_x_607_);
v_r_609_ = lean_box(v_res_608_);
return v_r_609_;
}
}
LEAN_EXPORT uint8_t lean_local_ctx_is_empty(lean_object* v_lctx_610_){
_start:
{
lean_object* v_fvarIdToDecl_611_; uint8_t v___x_612_; 
v_fvarIdToDecl_611_ = lean_ctor_get(v_lctx_610_, 0);
lean_inc_ref(v_fvarIdToDecl_611_);
lean_dec_ref(v_lctx_610_);
v___x_612_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_fvarIdToDecl_611_);
lean_dec_ref(v_fvarIdToDecl_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_isEmpty___boxed(lean_object* v_lctx_613_){
_start:
{
uint8_t v_res_614_; lean_object* v_r_615_; 
v_res_614_ = lean_local_ctx_is_empty(v_lctx_613_);
v_r_615_ = lean_box(v_res_614_);
return v_r_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_616_, lean_object* v_x_617_, lean_object* v_x_618_, lean_object* v_x_619_){
_start:
{
lean_object* v_ks_620_; lean_object* v_vs_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_645_; 
v_ks_620_ = lean_ctor_get(v_x_616_, 0);
v_vs_621_ = lean_ctor_get(v_x_616_, 1);
v_isSharedCheck_645_ = !lean_is_exclusive(v_x_616_);
if (v_isSharedCheck_645_ == 0)
{
v___x_623_ = v_x_616_;
v_isShared_624_ = v_isSharedCheck_645_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_vs_621_);
lean_inc(v_ks_620_);
lean_dec(v_x_616_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_645_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_625_; uint8_t v___x_626_; 
v___x_625_ = lean_array_get_size(v_ks_620_);
v___x_626_ = lean_nat_dec_lt(v_x_617_, v___x_625_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_630_; 
lean_dec(v_x_617_);
v___x_627_ = lean_array_push(v_ks_620_, v_x_618_);
v___x_628_ = lean_array_push(v_vs_621_, v_x_619_);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 1, v___x_628_);
lean_ctor_set(v___x_623_, 0, v___x_627_);
v___x_630_ = v___x_623_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_627_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v___x_628_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
else
{
lean_object* v_k_x27_632_; uint8_t v___x_633_; 
v_k_x27_632_ = lean_array_fget_borrowed(v_ks_620_, v_x_617_);
v___x_633_ = l_Lean_instBEqFVarId_beq(v_x_618_, v_k_x27_632_);
if (v___x_633_ == 0)
{
lean_object* v___x_635_; 
if (v_isShared_624_ == 0)
{
v___x_635_ = v___x_623_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_ks_620_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v_vs_621_);
v___x_635_ = v_reuseFailAlloc_639_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = lean_unsigned_to_nat(1u);
v___x_637_ = lean_nat_add(v_x_617_, v___x_636_);
lean_dec(v_x_617_);
v_x_616_ = v___x_635_;
v_x_617_ = v___x_637_;
goto _start;
}
}
else
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_643_; 
v___x_640_ = lean_array_fset(v_ks_620_, v_x_617_, v_x_618_);
v___x_641_ = lean_array_fset(v_vs_621_, v_x_617_, v_x_619_);
lean_dec(v_x_617_);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 1, v___x_641_);
lean_ctor_set(v___x_623_, 0, v___x_640_);
v___x_643_ = v___x_623_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_640_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v___x_641_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1___redArg(lean_object* v_n_646_, lean_object* v_k_647_, lean_object* v_v_648_){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = lean_unsigned_to_nat(0u);
v___x_650_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2___redArg(v_n_646_, v___x_649_, v_k_647_, v_v_648_);
return v___x_650_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_651_; size_t v___x_652_; size_t v___x_653_; 
v___x_651_ = ((size_t)5ULL);
v___x_652_ = ((size_t)1ULL);
v___x_653_ = lean_usize_shift_left(v___x_652_, v___x_651_);
return v___x_653_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_654_; size_t v___x_655_; size_t v___x_656_; 
v___x_654_ = ((size_t)1ULL);
v___x_655_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0);
v___x_656_ = lean_usize_sub(v___x_655_, v___x_654_);
return v___x_656_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(lean_object* v_x_658_, size_t v_x_659_, size_t v_x_660_, lean_object* v_x_661_, lean_object* v_x_662_){
_start:
{
if (lean_obj_tag(v_x_658_) == 0)
{
lean_object* v_es_663_; size_t v___x_664_; size_t v___x_665_; size_t v___x_666_; size_t v___x_667_; lean_object* v_j_668_; lean_object* v___x_669_; uint8_t v___x_670_; 
v_es_663_ = lean_ctor_get(v_x_658_, 0);
v___x_664_ = ((size_t)5ULL);
v___x_665_ = ((size_t)1ULL);
v___x_666_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1);
v___x_667_ = lean_usize_land(v_x_659_, v___x_666_);
v_j_668_ = lean_usize_to_nat(v___x_667_);
v___x_669_ = lean_array_get_size(v_es_663_);
v___x_670_ = lean_nat_dec_lt(v_j_668_, v___x_669_);
if (v___x_670_ == 0)
{
lean_dec(v_j_668_);
lean_dec(v_x_662_);
lean_dec(v_x_661_);
return v_x_658_;
}
else
{
lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_707_; 
lean_inc_ref(v_es_663_);
v_isSharedCheck_707_ = !lean_is_exclusive(v_x_658_);
if (v_isSharedCheck_707_ == 0)
{
lean_object* v_unused_708_; 
v_unused_708_ = lean_ctor_get(v_x_658_, 0);
lean_dec(v_unused_708_);
v___x_672_ = v_x_658_;
v_isShared_673_ = v_isSharedCheck_707_;
goto v_resetjp_671_;
}
else
{
lean_dec(v_x_658_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_707_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v_v_674_; lean_object* v___x_675_; lean_object* v_xs_x27_676_; lean_object* v___y_678_; 
v_v_674_ = lean_array_fget(v_es_663_, v_j_668_);
v___x_675_ = lean_box(0);
v_xs_x27_676_ = lean_array_fset(v_es_663_, v_j_668_, v___x_675_);
switch(lean_obj_tag(v_v_674_))
{
case 0:
{
lean_object* v_key_683_; lean_object* v_val_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_694_; 
v_key_683_ = lean_ctor_get(v_v_674_, 0);
v_val_684_ = lean_ctor_get(v_v_674_, 1);
v_isSharedCheck_694_ = !lean_is_exclusive(v_v_674_);
if (v_isSharedCheck_694_ == 0)
{
v___x_686_ = v_v_674_;
v_isShared_687_ = v_isSharedCheck_694_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_val_684_);
lean_inc(v_key_683_);
lean_dec(v_v_674_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_694_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
uint8_t v___x_688_; 
v___x_688_ = l_Lean_instBEqFVarId_beq(v_x_661_, v_key_683_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; lean_object* v___x_690_; 
lean_del_object(v___x_686_);
v___x_689_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_683_, v_val_684_, v_x_661_, v_x_662_);
v___x_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
v___y_678_ = v___x_690_;
goto v___jp_677_;
}
else
{
lean_object* v___x_692_; 
lean_dec(v_val_684_);
lean_dec(v_key_683_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 1, v_x_662_);
lean_ctor_set(v___x_686_, 0, v_x_661_);
v___x_692_ = v___x_686_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_x_661_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v_x_662_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
v___y_678_ = v___x_692_;
goto v___jp_677_;
}
}
}
}
case 1:
{
lean_object* v_node_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_705_; 
v_node_695_ = lean_ctor_get(v_v_674_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v_v_674_);
if (v_isSharedCheck_705_ == 0)
{
v___x_697_ = v_v_674_;
v_isShared_698_ = v_isSharedCheck_705_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_node_695_);
lean_dec(v_v_674_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_705_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
size_t v___x_699_; size_t v___x_700_; lean_object* v___x_701_; lean_object* v___x_703_; 
v___x_699_ = lean_usize_shift_right(v_x_659_, v___x_664_);
v___x_700_ = lean_usize_add(v_x_660_, v___x_665_);
v___x_701_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_node_695_, v___x_699_, v___x_700_, v_x_661_, v_x_662_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 0, v___x_701_);
v___x_703_ = v___x_697_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_701_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
v___y_678_ = v___x_703_;
goto v___jp_677_;
}
}
}
default: 
{
lean_object* v___x_706_; 
v___x_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_706_, 0, v_x_661_);
lean_ctor_set(v___x_706_, 1, v_x_662_);
v___y_678_ = v___x_706_;
goto v___jp_677_;
}
}
v___jp_677_:
{
lean_object* v___x_679_; lean_object* v___x_681_; 
v___x_679_ = lean_array_fset(v_xs_x27_676_, v_j_668_, v___y_678_);
lean_dec(v_j_668_);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 0, v___x_679_);
v___x_681_ = v___x_672_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_679_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
}
else
{
lean_object* v_ks_709_; lean_object* v_vs_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_730_; 
v_ks_709_ = lean_ctor_get(v_x_658_, 0);
v_vs_710_ = lean_ctor_get(v_x_658_, 1);
v_isSharedCheck_730_ = !lean_is_exclusive(v_x_658_);
if (v_isSharedCheck_730_ == 0)
{
v___x_712_ = v_x_658_;
v_isShared_713_ = v_isSharedCheck_730_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_vs_710_);
lean_inc(v_ks_709_);
lean_dec(v_x_658_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_730_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_713_ == 0)
{
v___x_715_ = v___x_712_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_ks_709_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v_vs_710_);
v___x_715_ = v_reuseFailAlloc_729_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
lean_object* v_newNode_716_; uint8_t v___y_718_; size_t v___x_724_; uint8_t v___x_725_; 
v_newNode_716_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1___redArg(v___x_715_, v_x_661_, v_x_662_);
v___x_724_ = ((size_t)7ULL);
v___x_725_ = lean_usize_dec_le(v___x_724_, v_x_660_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; lean_object* v___x_727_; uint8_t v___x_728_; 
v___x_726_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_716_);
v___x_727_ = lean_unsigned_to_nat(4u);
v___x_728_ = lean_nat_dec_lt(v___x_726_, v___x_727_);
lean_dec(v___x_726_);
v___y_718_ = v___x_728_;
goto v___jp_717_;
}
else
{
v___y_718_ = v___x_725_;
goto v___jp_717_;
}
v___jp_717_:
{
if (v___y_718_ == 0)
{
lean_object* v_ks_719_; lean_object* v_vs_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v_ks_719_ = lean_ctor_get(v_newNode_716_, 0);
lean_inc_ref(v_ks_719_);
v_vs_720_ = lean_ctor_get(v_newNode_716_, 1);
lean_inc_ref(v_vs_720_);
lean_dec_ref(v_newNode_716_);
v___x_721_ = lean_unsigned_to_nat(0u);
v___x_722_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__2);
v___x_723_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(v_x_660_, v_ks_719_, v_vs_720_, v___x_721_, v___x_722_);
lean_dec_ref(v_vs_720_);
lean_dec_ref(v_ks_719_);
return v___x_723_;
}
else
{
return v_newNode_716_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(size_t v_depth_731_, lean_object* v_keys_732_, lean_object* v_vals_733_, lean_object* v_i_734_, lean_object* v_entries_735_){
_start:
{
lean_object* v___x_736_; uint8_t v___x_737_; 
v___x_736_ = lean_array_get_size(v_keys_732_);
v___x_737_ = lean_nat_dec_lt(v_i_734_, v___x_736_);
if (v___x_737_ == 0)
{
lean_dec(v_i_734_);
return v_entries_735_;
}
else
{
lean_object* v_k_738_; lean_object* v_v_739_; uint64_t v___x_740_; size_t v_h_741_; size_t v___x_742_; lean_object* v___x_743_; size_t v___x_744_; size_t v___x_745_; size_t v___x_746_; size_t v_h_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v_k_738_ = lean_array_fget_borrowed(v_keys_732_, v_i_734_);
v_v_739_ = lean_array_fget_borrowed(v_vals_733_, v_i_734_);
v___x_740_ = l_Lean_instHashableFVarId_hash(v_k_738_);
v_h_741_ = lean_uint64_to_usize(v___x_740_);
v___x_742_ = ((size_t)5ULL);
v___x_743_ = lean_unsigned_to_nat(1u);
v___x_744_ = ((size_t)1ULL);
v___x_745_ = lean_usize_sub(v_depth_731_, v___x_744_);
v___x_746_ = lean_usize_mul(v___x_742_, v___x_745_);
v_h_747_ = lean_usize_shift_right(v_h_741_, v___x_746_);
v___x_748_ = lean_nat_add(v_i_734_, v___x_743_);
lean_dec(v_i_734_);
lean_inc(v_v_739_);
lean_inc(v_k_738_);
v___x_749_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_entries_735_, v_h_747_, v_depth_731_, v_k_738_, v_v_739_);
v_i_734_ = v___x_748_;
v_entries_735_ = v___x_749_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_751_, lean_object* v_keys_752_, lean_object* v_vals_753_, lean_object* v_i_754_, lean_object* v_entries_755_){
_start:
{
size_t v_depth_boxed_756_; lean_object* v_res_757_; 
v_depth_boxed_756_ = lean_unbox_usize(v_depth_751_);
lean_dec(v_depth_751_);
v_res_757_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(v_depth_boxed_756_, v_keys_752_, v_vals_753_, v_i_754_, v_entries_755_);
lean_dec_ref(v_vals_753_);
lean_dec_ref(v_keys_752_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___boxed(lean_object* v_x_758_, lean_object* v_x_759_, lean_object* v_x_760_, lean_object* v_x_761_, lean_object* v_x_762_){
_start:
{
size_t v_x_371__boxed_763_; size_t v_x_372__boxed_764_; lean_object* v_res_765_; 
v_x_371__boxed_763_ = lean_unbox_usize(v_x_759_);
lean_dec(v_x_759_);
v_x_372__boxed_764_ = lean_unbox_usize(v_x_760_);
lean_dec(v_x_760_);
v_res_765_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_x_758_, v_x_371__boxed_763_, v_x_372__boxed_764_, v_x_761_, v_x_762_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(lean_object* v_x_766_, lean_object* v_x_767_, lean_object* v_x_768_){
_start:
{
uint64_t v___x_769_; size_t v___x_770_; size_t v___x_771_; lean_object* v___x_772_; 
v___x_769_ = l_Lean_instHashableFVarId_hash(v_x_767_);
v___x_770_ = lean_uint64_to_usize(v___x_769_);
v___x_771_ = ((size_t)1ULL);
v___x_772_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_x_766_, v___x_770_, v___x_771_, v_x_767_, v_x_768_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object* v_lctx_773_, lean_object* v_fvarId_774_, lean_object* v_userName_775_, lean_object* v_type_776_, uint8_t v_bi_777_, uint8_t v_kind_778_){
_start:
{
lean_object* v_decls_779_; lean_object* v_fvarIdToDecl_780_; lean_object* v_auxDeclToFullName_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_793_; 
v_decls_779_ = lean_ctor_get(v_lctx_773_, 1);
v_fvarIdToDecl_780_ = lean_ctor_get(v_lctx_773_, 0);
v_auxDeclToFullName_781_ = lean_ctor_get(v_lctx_773_, 2);
v_isSharedCheck_793_ = !lean_is_exclusive(v_lctx_773_);
if (v_isSharedCheck_793_ == 0)
{
v___x_783_ = v_lctx_773_;
v_isShared_784_ = v_isSharedCheck_793_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_auxDeclToFullName_781_);
lean_inc(v_decls_779_);
lean_inc(v_fvarIdToDecl_780_);
lean_dec(v_lctx_773_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_793_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v_size_785_; lean_object* v_decl_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_791_; 
v_size_785_ = lean_ctor_get(v_decls_779_, 2);
lean_inc(v_fvarId_774_);
lean_inc(v_size_785_);
v_decl_786_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_decl_786_, 0, v_size_785_);
lean_ctor_set(v_decl_786_, 1, v_fvarId_774_);
lean_ctor_set(v_decl_786_, 2, v_userName_775_);
lean_ctor_set(v_decl_786_, 3, v_type_776_);
lean_ctor_set_uint8(v_decl_786_, sizeof(void*)*4, v_bi_777_);
lean_ctor_set_uint8(v_decl_786_, sizeof(void*)*4 + 1, v_kind_778_);
lean_inc_ref(v_decl_786_);
v___x_787_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_780_, v_fvarId_774_, v_decl_786_);
v___x_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_788_, 0, v_decl_786_);
v___x_789_ = l_Lean_PersistentArray_push___redArg(v_decls_779_, v___x_788_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 1, v___x_789_);
lean_ctor_set(v___x_783_, 0, v___x_787_);
v___x_791_ = v___x_783_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_787_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v___x_789_);
lean_ctor_set(v_reuseFailAlloc_792_, 2, v_auxDeclToFullName_781_);
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
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLocalDecl___boxed(lean_object* v_lctx_794_, lean_object* v_fvarId_795_, lean_object* v_userName_796_, lean_object* v_type_797_, lean_object* v_bi_798_, lean_object* v_kind_799_){
_start:
{
uint8_t v_bi_boxed_800_; uint8_t v_kind_boxed_801_; lean_object* v_res_802_; 
v_bi_boxed_800_ = lean_unbox(v_bi_798_);
v_kind_boxed_801_ = lean_unbox(v_kind_799_);
v_res_802_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_794_, v_fvarId_795_, v_userName_796_, v_type_797_, v_bi_boxed_800_, v_kind_boxed_801_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0(lean_object* v_00_u03b2_803_, lean_object* v_x_804_, lean_object* v_x_805_, lean_object* v_x_806_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_x_804_, v_x_805_, v_x_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0(lean_object* v_00_u03b2_808_, lean_object* v_x_809_, size_t v_x_810_, size_t v_x_811_, lean_object* v_x_812_, lean_object* v_x_813_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_x_809_, v_x_810_, v_x_811_, v_x_812_, v_x_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_815_, lean_object* v_x_816_, lean_object* v_x_817_, lean_object* v_x_818_, lean_object* v_x_819_, lean_object* v_x_820_){
_start:
{
size_t v_x_581__boxed_821_; size_t v_x_582__boxed_822_; lean_object* v_res_823_; 
v_x_581__boxed_821_ = lean_unbox_usize(v_x_817_);
lean_dec(v_x_817_);
v_x_582__boxed_822_ = lean_unbox_usize(v_x_818_);
lean_dec(v_x_818_);
v_res_823_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0(v_00_u03b2_815_, v_x_816_, v_x_581__boxed_821_, v_x_582__boxed_822_, v_x_819_, v_x_820_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_824_, lean_object* v_n_825_, lean_object* v_k_826_, lean_object* v_v_827_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1___redArg(v_n_825_, v_k_826_, v_v_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_829_, size_t v_depth_830_, lean_object* v_keys_831_, lean_object* v_vals_832_, lean_object* v_heq_833_, lean_object* v_i_834_, lean_object* v_entries_835_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(v_depth_830_, v_keys_831_, v_vals_832_, v_i_834_, v_entries_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_837_, lean_object* v_depth_838_, lean_object* v_keys_839_, lean_object* v_vals_840_, lean_object* v_heq_841_, lean_object* v_i_842_, lean_object* v_entries_843_){
_start:
{
size_t v_depth_boxed_844_; lean_object* v_res_845_; 
v_depth_boxed_844_ = lean_unbox_usize(v_depth_838_);
lean_dec(v_depth_838_);
v_res_845_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2(v_00_u03b2_837_, v_depth_boxed_844_, v_keys_839_, v_vals_840_, v_heq_841_, v_i_842_, v_entries_843_);
lean_dec_ref(v_vals_840_);
lean_dec_ref(v_keys_839_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_846_, lean_object* v_x_847_, lean_object* v_x_848_, lean_object* v_x_849_, lean_object* v_x_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2___redArg(v_x_847_, v_x_848_, v_x_849_, v_x_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_mk_local_decl(lean_object* v_lctx_852_, lean_object* v_fvarId_853_, lean_object* v_userName_854_, lean_object* v_type_855_, uint8_t v_bi_856_){
_start:
{
uint8_t v___x_857_; lean_object* v___x_858_; 
v___x_857_ = 0;
v___x_858_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_852_, v_fvarId_853_, v_userName_854_, v_type_855_, v_bi_856_, v___x_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_mkLocalDeclExported___boxed(lean_object* v_lctx_859_, lean_object* v_fvarId_860_, lean_object* v_userName_861_, lean_object* v_type_862_, lean_object* v_bi_863_){
_start:
{
uint8_t v_bi_boxed_864_; lean_object* v_res_865_; 
v_bi_boxed_864_ = lean_unbox(v_bi_863_);
v_res_865_ = lean_local_ctx_mk_local_decl(v_lctx_859_, v_fvarId_860_, v_userName_861_, v_type_862_, v_bi_boxed_864_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLetDecl(lean_object* v_lctx_866_, lean_object* v_fvarId_867_, lean_object* v_userName_868_, lean_object* v_type_869_, lean_object* v_value_870_, uint8_t v_nondep_871_, uint8_t v_kind_872_){
_start:
{
lean_object* v_decls_873_; lean_object* v_fvarIdToDecl_874_; lean_object* v_auxDeclToFullName_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_887_; 
v_decls_873_ = lean_ctor_get(v_lctx_866_, 1);
v_fvarIdToDecl_874_ = lean_ctor_get(v_lctx_866_, 0);
v_auxDeclToFullName_875_ = lean_ctor_get(v_lctx_866_, 2);
v_isSharedCheck_887_ = !lean_is_exclusive(v_lctx_866_);
if (v_isSharedCheck_887_ == 0)
{
v___x_877_ = v_lctx_866_;
v_isShared_878_ = v_isSharedCheck_887_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_auxDeclToFullName_875_);
lean_inc(v_decls_873_);
lean_inc(v_fvarIdToDecl_874_);
lean_dec(v_lctx_866_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_887_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v_size_879_; lean_object* v_decl_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_885_; 
v_size_879_ = lean_ctor_get(v_decls_873_, 2);
lean_inc(v_fvarId_867_);
lean_inc(v_size_879_);
v_decl_880_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_decl_880_, 0, v_size_879_);
lean_ctor_set(v_decl_880_, 1, v_fvarId_867_);
lean_ctor_set(v_decl_880_, 2, v_userName_868_);
lean_ctor_set(v_decl_880_, 3, v_type_869_);
lean_ctor_set(v_decl_880_, 4, v_value_870_);
lean_ctor_set_uint8(v_decl_880_, sizeof(void*)*5, v_nondep_871_);
lean_ctor_set_uint8(v_decl_880_, sizeof(void*)*5 + 1, v_kind_872_);
lean_inc_ref(v_decl_880_);
v___x_881_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_874_, v_fvarId_867_, v_decl_880_);
v___x_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_882_, 0, v_decl_880_);
v___x_883_ = l_Lean_PersistentArray_push___redArg(v_decls_873_, v___x_882_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 1, v___x_883_);
lean_ctor_set(v___x_877_, 0, v___x_881_);
v___x_885_ = v___x_877_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_881_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v___x_883_);
lean_ctor_set(v_reuseFailAlloc_886_, 2, v_auxDeclToFullName_875_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLetDecl___boxed(lean_object* v_lctx_888_, lean_object* v_fvarId_889_, lean_object* v_userName_890_, lean_object* v_type_891_, lean_object* v_value_892_, lean_object* v_nondep_893_, lean_object* v_kind_894_){
_start:
{
uint8_t v_nondep_boxed_895_; uint8_t v_kind_boxed_896_; lean_object* v_res_897_; 
v_nondep_boxed_895_ = lean_unbox(v_nondep_893_);
v_kind_boxed_896_ = lean_unbox(v_kind_894_);
v_res_897_ = l_Lean_LocalContext_mkLetDecl(v_lctx_888_, v_fvarId_889_, v_userName_890_, v_type_891_, v_value_892_, v_nondep_boxed_895_, v_kind_boxed_896_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_mk_let_decl(lean_object* v_lctx_898_, lean_object* v_fvarId_899_, lean_object* v_userName_900_, lean_object* v_type_901_, lean_object* v_value_902_, uint8_t v_nondep_903_){
_start:
{
uint8_t v___x_904_; lean_object* v___x_905_; 
v___x_904_ = 0;
v___x_905_ = l_Lean_LocalContext_mkLetDecl(v_lctx_898_, v_fvarId_899_, v_userName_900_, v_type_901_, v_value_902_, v_nondep_903_, v___x_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_mkLetDeclExported___boxed(lean_object* v_lctx_906_, lean_object* v_fvarId_907_, lean_object* v_userName_908_, lean_object* v_type_909_, lean_object* v_value_910_, lean_object* v_nondep_911_){
_start:
{
uint8_t v_nondep_boxed_912_; lean_object* v_res_913_; 
v_nondep_boxed_912_ = lean_unbox(v_nondep_911_);
v_res_913_ = lean_local_ctx_mk_let_decl(v_lctx_906_, v_fvarId_907_, v_userName_908_, v_type_909_, v_value_910_, v_nondep_boxed_912_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkAuxDecl(lean_object* v_lctx_914_, lean_object* v_fvarId_915_, lean_object* v_userName_916_, lean_object* v_type_917_, lean_object* v_fullName_918_){
_start:
{
lean_object* v_decls_919_; lean_object* v_fvarIdToDecl_920_; lean_object* v_auxDeclToFullName_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_936_; 
v_decls_919_ = lean_ctor_get(v_lctx_914_, 1);
v_fvarIdToDecl_920_ = lean_ctor_get(v_lctx_914_, 0);
v_auxDeclToFullName_921_ = lean_ctor_get(v_lctx_914_, 2);
v_isSharedCheck_936_ = !lean_is_exclusive(v_lctx_914_);
if (v_isSharedCheck_936_ == 0)
{
v___x_923_ = v_lctx_914_;
v_isShared_924_ = v_isSharedCheck_936_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_auxDeclToFullName_921_);
lean_inc(v_decls_919_);
lean_inc(v_fvarIdToDecl_920_);
lean_dec(v_lctx_914_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_936_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v_size_925_; uint8_t v___x_926_; uint8_t v___x_927_; lean_object* v_decl_928_; lean_object* v_auxDeclToFullName_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_934_; 
v_size_925_ = lean_ctor_get(v_decls_919_, 2);
v___x_926_ = 0;
v___x_927_ = 2;
lean_inc(v_fvarId_915_);
lean_inc(v_size_925_);
v_decl_928_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_decl_928_, 0, v_size_925_);
lean_ctor_set(v_decl_928_, 1, v_fvarId_915_);
lean_ctor_set(v_decl_928_, 2, v_userName_916_);
lean_ctor_set(v_decl_928_, 3, v_type_917_);
lean_ctor_set_uint8(v_decl_928_, sizeof(void*)*4, v___x_926_);
lean_ctor_set_uint8(v_decl_928_, sizeof(void*)*4 + 1, v___x_927_);
lean_inc(v_fvarId_915_);
v_auxDeclToFullName_929_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(v_fvarId_915_, v_fullName_918_, v_auxDeclToFullName_921_);
lean_inc_ref(v_decl_928_);
v___x_930_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_920_, v_fvarId_915_, v_decl_928_);
v___x_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_931_, 0, v_decl_928_);
v___x_932_ = l_Lean_PersistentArray_push___redArg(v_decls_919_, v___x_931_);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 2, v_auxDeclToFullName_929_);
lean_ctor_set(v___x_923_, 1, v___x_932_);
lean_ctor_set(v___x_923_, 0, v___x_930_);
v___x_934_ = v___x_923_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_930_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v___x_932_);
lean_ctor_set(v_reuseFailAlloc_935_, 2, v_auxDeclToFullName_929_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_addDecl(lean_object* v_lctx_937_, lean_object* v_newDecl_938_){
_start:
{
lean_object* v_decls_939_; lean_object* v_fvarIdToDecl_940_; lean_object* v_auxDeclToFullName_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_956_; 
v_decls_939_ = lean_ctor_get(v_lctx_937_, 1);
v_fvarIdToDecl_940_ = lean_ctor_get(v_lctx_937_, 0);
v_auxDeclToFullName_941_ = lean_ctor_get(v_lctx_937_, 2);
v_isSharedCheck_956_ = !lean_is_exclusive(v_lctx_937_);
if (v_isSharedCheck_956_ == 0)
{
v___x_943_ = v_lctx_937_;
v_isShared_944_ = v_isSharedCheck_956_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_auxDeclToFullName_941_);
lean_inc(v_decls_939_);
lean_inc(v_fvarIdToDecl_940_);
lean_dec(v_lctx_937_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_956_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v_size_945_; lean_object* v_newDecl_946_; lean_object* v___y_948_; lean_object* v_fvarId_955_; 
v_size_945_ = lean_ctor_get(v_decls_939_, 2);
lean_inc(v_size_945_);
v_newDecl_946_ = l_Lean_LocalDecl_setIndex(v_newDecl_938_, v_size_945_);
v_fvarId_955_ = lean_ctor_get(v_newDecl_946_, 1);
lean_inc(v_fvarId_955_);
v___y_948_ = v_fvarId_955_;
goto v___jp_947_;
v___jp_947_:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_953_; 
lean_inc_ref(v_newDecl_946_);
v___x_949_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_940_, v___y_948_, v_newDecl_946_);
v___x_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_950_, 0, v_newDecl_946_);
v___x_951_ = l_Lean_PersistentArray_push___redArg(v_decls_939_, v___x_950_);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 1, v___x_951_);
lean_ctor_set(v___x_943_, 0, v___x_949_);
v___x_953_ = v___x_943_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_949_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v___x_951_);
lean_ctor_set(v_reuseFailAlloc_954_, 2, v_auxDeclToFullName_941_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_957_, lean_object* v_vals_958_, lean_object* v_i_959_, lean_object* v_k_960_){
_start:
{
lean_object* v___x_961_; uint8_t v___x_962_; 
v___x_961_ = lean_array_get_size(v_keys_957_);
v___x_962_ = lean_nat_dec_lt(v_i_959_, v___x_961_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; 
lean_dec(v_i_959_);
v___x_963_ = lean_box(0);
return v___x_963_;
}
else
{
lean_object* v_k_x27_964_; uint8_t v___x_965_; 
v_k_x27_964_ = lean_array_fget_borrowed(v_keys_957_, v_i_959_);
v___x_965_ = l_Lean_instBEqFVarId_beq(v_k_960_, v_k_x27_964_);
if (v___x_965_ == 0)
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = lean_unsigned_to_nat(1u);
v___x_967_ = lean_nat_add(v_i_959_, v___x_966_);
lean_dec(v_i_959_);
v_i_959_ = v___x_967_;
goto _start;
}
else
{
lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_969_ = lean_array_fget_borrowed(v_vals_958_, v_i_959_);
lean_dec(v_i_959_);
lean_inc(v___x_969_);
v___x_970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
return v___x_970_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_971_, lean_object* v_vals_972_, lean_object* v_i_973_, lean_object* v_k_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_971_, v_vals_972_, v_i_973_, v_k_974_);
lean_dec(v_k_974_);
lean_dec_ref(v_vals_972_);
lean_dec_ref(v_keys_971_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(lean_object* v_x_976_, size_t v_x_977_, lean_object* v_x_978_){
_start:
{
if (lean_obj_tag(v_x_976_) == 0)
{
lean_object* v_es_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_1000_; 
v_es_979_ = lean_ctor_get(v_x_976_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v_x_976_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_981_ = v_x_976_;
v_isShared_982_ = v_isSharedCheck_1000_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_es_979_);
lean_dec(v_x_976_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_1000_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_983_; size_t v___x_984_; size_t v___x_985_; size_t v___x_986_; lean_object* v_j_987_; lean_object* v___x_988_; 
v___x_983_ = lean_box(2);
v___x_984_ = ((size_t)5ULL);
v___x_985_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1);
v___x_986_ = lean_usize_land(v_x_977_, v___x_985_);
v_j_987_ = lean_usize_to_nat(v___x_986_);
v___x_988_ = lean_array_get(v___x_983_, v_es_979_, v_j_987_);
lean_dec(v_j_987_);
lean_dec_ref(v_es_979_);
switch(lean_obj_tag(v___x_988_))
{
case 0:
{
lean_object* v_key_989_; lean_object* v_val_990_; uint8_t v___x_991_; 
v_key_989_ = lean_ctor_get(v___x_988_, 0);
lean_inc(v_key_989_);
v_val_990_ = lean_ctor_get(v___x_988_, 1);
lean_inc(v_val_990_);
lean_dec_ref(v___x_988_);
v___x_991_ = l_Lean_instBEqFVarId_beq(v_x_978_, v_key_989_);
lean_dec(v_key_989_);
if (v___x_991_ == 0)
{
lean_object* v___x_992_; 
lean_dec(v_val_990_);
lean_del_object(v___x_981_);
v___x_992_ = lean_box(0);
return v___x_992_;
}
else
{
lean_object* v___x_994_; 
if (v_isShared_982_ == 0)
{
lean_ctor_set_tag(v___x_981_, 1);
lean_ctor_set(v___x_981_, 0, v_val_990_);
v___x_994_ = v___x_981_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_val_990_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
case 1:
{
lean_object* v_node_996_; size_t v___x_997_; 
lean_del_object(v___x_981_);
v_node_996_ = lean_ctor_get(v___x_988_, 0);
lean_inc(v_node_996_);
lean_dec_ref(v___x_988_);
v___x_997_ = lean_usize_shift_right(v_x_977_, v___x_984_);
v_x_976_ = v_node_996_;
v_x_977_ = v___x_997_;
goto _start;
}
default: 
{
lean_object* v___x_999_; 
lean_del_object(v___x_981_);
v___x_999_ = lean_box(0);
return v___x_999_;
}
}
}
}
else
{
lean_object* v_ks_1001_; lean_object* v_vs_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v_ks_1001_ = lean_ctor_get(v_x_976_, 0);
lean_inc_ref(v_ks_1001_);
v_vs_1002_ = lean_ctor_get(v_x_976_, 1);
lean_inc_ref(v_vs_1002_);
lean_dec_ref(v_x_976_);
v___x_1003_ = lean_unsigned_to_nat(0u);
v___x_1004_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1001_, v_vs_1002_, v___x_1003_, v_x_978_);
lean_dec_ref(v_vs_1002_);
lean_dec_ref(v_ks_1001_);
return v___x_1004_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1005_, lean_object* v_x_1006_, lean_object* v_x_1007_){
_start:
{
size_t v_x_143__boxed_1008_; lean_object* v_res_1009_; 
v_x_143__boxed_1008_ = lean_unbox_usize(v_x_1006_);
lean_dec(v_x_1006_);
v_res_1009_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(v_x_1005_, v_x_143__boxed_1008_, v_x_1007_);
lean_dec(v_x_1007_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(lean_object* v_x_1010_, lean_object* v_x_1011_){
_start:
{
uint64_t v___x_1012_; size_t v___x_1013_; lean_object* v___x_1014_; 
v___x_1012_ = l_Lean_instHashableFVarId_hash(v_x_1011_);
v___x_1013_ = lean_uint64_to_usize(v___x_1012_);
v___x_1014_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(v_x_1010_, v___x_1013_, v_x_1011_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg___boxed(lean_object* v_x_1015_, lean_object* v_x_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_x_1015_, v_x_1016_);
lean_dec(v_x_1016_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_find(lean_object* v_lctx_1018_, lean_object* v_fvarId_1019_){
_start:
{
lean_object* v_fvarIdToDecl_1020_; lean_object* v___x_1021_; 
v_fvarIdToDecl_1020_ = lean_ctor_get(v_lctx_1018_, 0);
lean_inc_ref(v_fvarIdToDecl_1020_);
lean_dec_ref(v_lctx_1018_);
v___x_1021_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_fvarIdToDecl_1020_, v_fvarId_1019_);
lean_dec(v_fvarId_1019_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0(lean_object* v_00_u03b2_1022_, lean_object* v_x_1023_, lean_object* v_x_1024_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_x_1023_, v_x_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___boxed(lean_object* v_00_u03b2_1026_, lean_object* v_x_1027_, lean_object* v_x_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0(v_00_u03b2_1026_, v_x_1027_, v_x_1028_);
lean_dec(v_x_1028_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1030_, lean_object* v_x_1031_, size_t v_x_1032_, lean_object* v_x_1033_){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(v_x_1031_, v_x_1032_, v_x_1033_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1035_, lean_object* v_x_1036_, lean_object* v_x_1037_, lean_object* v_x_1038_){
_start:
{
size_t v_x_226__boxed_1039_; lean_object* v_res_1040_; 
v_x_226__boxed_1039_ = lean_unbox_usize(v_x_1037_);
lean_dec(v_x_1037_);
v_res_1040_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0(v_00_u03b2_1035_, v_x_1036_, v_x_226__boxed_1039_, v_x_1038_);
lean_dec(v_x_1038_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1041_, lean_object* v_keys_1042_, lean_object* v_vals_1043_, lean_object* v_heq_1044_, lean_object* v_i_1045_, lean_object* v_k_1046_){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1042_, v_vals_1043_, v_i_1045_, v_k_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1048_, lean_object* v_keys_1049_, lean_object* v_vals_1050_, lean_object* v_heq_1051_, lean_object* v_i_1052_, lean_object* v_k_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1048_, v_keys_1049_, v_vals_1050_, v_heq_1051_, v_i_1052_, v_k_1053_);
lean_dec(v_k_1053_);
lean_dec_ref(v_vals_1050_);
lean_dec_ref(v_keys_1049_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFVar_x3f(lean_object* v_lctx_1055_, lean_object* v_e_1056_){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = l_Lean_Expr_fvarId_x21(v_e_1056_);
v___x_1058_ = lean_local_ctx_find(v_lctx_1055_, v___x_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFVar_x3f___boxed(lean_object* v_lctx_1059_, lean_object* v_e_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_1059_, v_e_1060_);
lean_dec_ref(v_e_1060_);
return v_res_1061_;
}
}
static lean_object* _init_l_Lean_LocalContext_get_x21___closed__2(void){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1064_ = ((lean_object*)(l_Lean_LocalContext_get_x21___closed__1));
v___x_1065_ = lean_unsigned_to_nat(14u);
v___x_1066_ = lean_unsigned_to_nat(340u);
v___x_1067_ = ((lean_object*)(l_Lean_LocalContext_get_x21___closed__0));
v___x_1068_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_1069_ = l_mkPanicMessageWithDecl(v___x_1068_, v___x_1067_, v___x_1066_, v___x_1065_, v___x_1064_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_get_x21(lean_object* v_lctx_1070_, lean_object* v_fvarId_1071_){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = lean_local_ctx_find(v_lctx_1070_, v_fvarId_1071_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = lean_obj_once(&l_Lean_LocalContext_get_x21___closed__2, &l_Lean_LocalContext_get_x21___closed__2_once, _init_l_Lean_LocalContext_get_x21___closed__2);
v___x_1074_ = l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(v___x_1073_);
return v___x_1074_;
}
else
{
lean_object* v_val_1075_; 
v_val_1075_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_val_1075_);
lean_dec_ref(v___x_1072_);
return v_val_1075_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVar_x21(lean_object* v_lctx_1076_, lean_object* v_e_1077_){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = l_Lean_Expr_fvarId_x21(v_e_1077_);
v___x_1079_ = l_Lean_LocalContext_get_x21(v_lctx_1076_, v___x_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVar_x21___boxed(lean_object* v_lctx_1080_, lean_object* v_e_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Lean_LocalContext_getFVar_x21(v_lctx_1080_, v_e_1081_);
lean_dec_ref(v_e_1081_);
return v_res_1082_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1083_, lean_object* v_i_1084_, lean_object* v_k_1085_){
_start:
{
lean_object* v___x_1086_; uint8_t v___x_1087_; 
v___x_1086_ = lean_array_get_size(v_keys_1083_);
v___x_1087_ = lean_nat_dec_lt(v_i_1084_, v___x_1086_);
if (v___x_1087_ == 0)
{
lean_dec(v_i_1084_);
return v___x_1087_;
}
else
{
lean_object* v_k_x27_1088_; uint8_t v___x_1089_; 
v_k_x27_1088_ = lean_array_fget_borrowed(v_keys_1083_, v_i_1084_);
v___x_1089_ = l_Lean_instBEqFVarId_beq(v_k_1085_, v_k_x27_1088_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = lean_unsigned_to_nat(1u);
v___x_1091_ = lean_nat_add(v_i_1084_, v___x_1090_);
lean_dec(v_i_1084_);
v_i_1084_ = v___x_1091_;
goto _start;
}
else
{
lean_dec(v_i_1084_);
return v___x_1089_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1093_, lean_object* v_i_1094_, lean_object* v_k_1095_){
_start:
{
uint8_t v_res_1096_; lean_object* v_r_1097_; 
v_res_1096_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(v_keys_1093_, v_i_1094_, v_k_1095_);
lean_dec(v_k_1095_);
lean_dec_ref(v_keys_1093_);
v_r_1097_ = lean_box(v_res_1096_);
return v_r_1097_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(lean_object* v_x_1098_, size_t v_x_1099_, lean_object* v_x_1100_){
_start:
{
if (lean_obj_tag(v_x_1098_) == 0)
{
lean_object* v_es_1101_; lean_object* v___x_1102_; size_t v___x_1103_; size_t v___x_1104_; size_t v___x_1105_; lean_object* v_j_1106_; lean_object* v___x_1107_; 
v_es_1101_ = lean_ctor_get(v_x_1098_, 0);
lean_inc_ref(v_es_1101_);
lean_dec_ref(v_x_1098_);
v___x_1102_ = lean_box(2);
v___x_1103_ = ((size_t)5ULL);
v___x_1104_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1);
v___x_1105_ = lean_usize_land(v_x_1099_, v___x_1104_);
v_j_1106_ = lean_usize_to_nat(v___x_1105_);
v___x_1107_ = lean_array_get(v___x_1102_, v_es_1101_, v_j_1106_);
lean_dec(v_j_1106_);
lean_dec_ref(v_es_1101_);
switch(lean_obj_tag(v___x_1107_))
{
case 0:
{
lean_object* v_key_1108_; uint8_t v___x_1109_; 
v_key_1108_ = lean_ctor_get(v___x_1107_, 0);
lean_inc(v_key_1108_);
lean_dec_ref(v___x_1107_);
v___x_1109_ = l_Lean_instBEqFVarId_beq(v_x_1100_, v_key_1108_);
lean_dec(v_key_1108_);
return v___x_1109_;
}
case 1:
{
lean_object* v_node_1110_; size_t v___x_1111_; 
v_node_1110_ = lean_ctor_get(v___x_1107_, 0);
lean_inc(v_node_1110_);
lean_dec_ref(v___x_1107_);
v___x_1111_ = lean_usize_shift_right(v_x_1099_, v___x_1103_);
v_x_1098_ = v_node_1110_;
v_x_1099_ = v___x_1111_;
goto _start;
}
default: 
{
uint8_t v___x_1113_; 
v___x_1113_ = 0;
return v___x_1113_;
}
}
}
else
{
lean_object* v_ks_1114_; lean_object* v___x_1115_; uint8_t v___x_1116_; 
v_ks_1114_ = lean_ctor_get(v_x_1098_, 0);
lean_inc_ref(v_ks_1114_);
lean_dec_ref(v_x_1098_);
v___x_1115_ = lean_unsigned_to_nat(0u);
v___x_1116_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(v_ks_1114_, v___x_1115_, v_x_1100_);
lean_dec_ref(v_ks_1114_);
return v___x_1116_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg___boxed(lean_object* v_x_1117_, lean_object* v_x_1118_, lean_object* v_x_1119_){
_start:
{
size_t v_x_129__boxed_1120_; uint8_t v_res_1121_; lean_object* v_r_1122_; 
v_x_129__boxed_1120_ = lean_unbox_usize(v_x_1118_);
lean_dec(v_x_1118_);
v_res_1121_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(v_x_1117_, v_x_129__boxed_1120_, v_x_1119_);
lean_dec(v_x_1119_);
v_r_1122_ = lean_box(v_res_1121_);
return v_r_1122_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(lean_object* v_x_1123_, lean_object* v_x_1124_){
_start:
{
uint64_t v___x_1125_; size_t v___x_1126_; uint8_t v___x_1127_; 
v___x_1125_ = l_Lean_instHashableFVarId_hash(v_x_1124_);
v___x_1126_ = lean_uint64_to_usize(v___x_1125_);
v___x_1127_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(v_x_1123_, v___x_1126_, v_x_1124_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg___boxed(lean_object* v_x_1128_, lean_object* v_x_1129_){
_start:
{
uint8_t v_res_1130_; lean_object* v_r_1131_; 
v_res_1130_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(v_x_1128_, v_x_1129_);
lean_dec(v_x_1129_);
v_r_1131_ = lean_box(v_res_1130_);
return v_r_1131_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_contains(lean_object* v_lctx_1132_, lean_object* v_fvarId_1133_){
_start:
{
lean_object* v_fvarIdToDecl_1134_; uint8_t v___x_1135_; 
v_fvarIdToDecl_1134_ = lean_ctor_get(v_lctx_1132_, 0);
lean_inc_ref(v_fvarIdToDecl_1134_);
lean_dec_ref(v_lctx_1132_);
v___x_1135_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(v_fvarIdToDecl_1134_, v_fvarId_1133_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_contains___boxed(lean_object* v_lctx_1136_, lean_object* v_fvarId_1137_){
_start:
{
uint8_t v_res_1138_; lean_object* v_r_1139_; 
v_res_1138_ = l_Lean_LocalContext_contains(v_lctx_1136_, v_fvarId_1137_);
lean_dec(v_fvarId_1137_);
v_r_1139_ = lean_box(v_res_1138_);
return v_r_1139_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0(lean_object* v_00_u03b2_1140_, lean_object* v_x_1141_, lean_object* v_x_1142_){
_start:
{
uint8_t v___x_1143_; 
v___x_1143_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(v_x_1141_, v_x_1142_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___boxed(lean_object* v_00_u03b2_1144_, lean_object* v_x_1145_, lean_object* v_x_1146_){
_start:
{
uint8_t v_res_1147_; lean_object* v_r_1148_; 
v_res_1147_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0(v_00_u03b2_1144_, v_x_1145_, v_x_1146_);
lean_dec(v_x_1146_);
v_r_1148_ = lean_box(v_res_1147_);
return v_r_1148_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0(lean_object* v_00_u03b2_1149_, lean_object* v_x_1150_, size_t v_x_1151_, lean_object* v_x_1152_){
_start:
{
uint8_t v___x_1153_; 
v___x_1153_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(v_x_1150_, v_x_1151_, v_x_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1154_, lean_object* v_x_1155_, lean_object* v_x_1156_, lean_object* v_x_1157_){
_start:
{
size_t v_x_194__boxed_1158_; uint8_t v_res_1159_; lean_object* v_r_1160_; 
v_x_194__boxed_1158_ = lean_unbox_usize(v_x_1156_);
lean_dec(v_x_1156_);
v_res_1159_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0(v_00_u03b2_1154_, v_x_1155_, v_x_194__boxed_1158_, v_x_1157_);
lean_dec(v_x_1157_);
v_r_1160_ = lean_box(v_res_1159_);
return v_r_1160_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1161_, lean_object* v_keys_1162_, lean_object* v_vals_1163_, lean_object* v_heq_1164_, lean_object* v_i_1165_, lean_object* v_k_1166_){
_start:
{
uint8_t v___x_1167_; 
v___x_1167_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(v_keys_1162_, v_i_1165_, v_k_1166_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1168_, lean_object* v_keys_1169_, lean_object* v_vals_1170_, lean_object* v_heq_1171_, lean_object* v_i_1172_, lean_object* v_k_1173_){
_start:
{
uint8_t v_res_1174_; lean_object* v_r_1175_; 
v_res_1174_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1(v_00_u03b2_1168_, v_keys_1169_, v_vals_1170_, v_heq_1171_, v_i_1172_, v_k_1173_);
lean_dec(v_k_1173_);
lean_dec_ref(v_vals_1170_);
lean_dec_ref(v_keys_1169_);
v_r_1175_ = lean_box(v_res_1174_);
return v_r_1175_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_containsFVar(lean_object* v_lctx_1176_, lean_object* v_e_1177_){
_start:
{
lean_object* v___x_1178_; uint8_t v___x_1179_; 
v___x_1178_ = l_Lean_Expr_fvarId_x21(v_e_1177_);
v___x_1179_ = l_Lean_LocalContext_contains(v_lctx_1176_, v___x_1178_);
lean_dec(v___x_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_containsFVar___boxed(lean_object* v_lctx_1180_, lean_object* v_e_1181_){
_start:
{
uint8_t v_res_1182_; lean_object* v_r_1183_; 
v_res_1182_ = l_Lean_LocalContext_containsFVar(v_lctx_1180_, v_e_1181_);
lean_dec_ref(v_e_1181_);
v_r_1183_ = lean_box(v_res_1182_);
return v_r_1183_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(lean_object* v_as_1184_, size_t v_i_1185_, size_t v_stop_1186_, lean_object* v_b_1187_){
_start:
{
lean_object* v___y_1189_; uint8_t v___x_1193_; 
v___x_1193_ = lean_usize_dec_eq(v_i_1185_, v_stop_1186_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; 
v___x_1194_ = lean_array_uget_borrowed(v_as_1184_, v_i_1185_);
if (lean_obj_tag(v___x_1194_) == 0)
{
v___y_1189_ = v_b_1187_;
goto v___jp_1188_;
}
else
{
lean_object* v_val_1195_; lean_object* v_fvarId_1196_; lean_object* v___x_1197_; 
v_val_1195_ = lean_ctor_get(v___x_1194_, 0);
v_fvarId_1196_ = lean_ctor_get(v_val_1195_, 1);
lean_inc(v_fvarId_1196_);
v___x_1197_ = lean_array_push(v_b_1187_, v_fvarId_1196_);
v___y_1189_ = v___x_1197_;
goto v___jp_1188_;
}
}
else
{
return v_b_1187_;
}
v___jp_1188_:
{
size_t v___x_1190_; size_t v___x_1191_; 
v___x_1190_ = ((size_t)1ULL);
v___x_1191_ = lean_usize_add(v_i_1185_, v___x_1190_);
v_i_1185_ = v___x_1191_;
v_b_1187_ = v___y_1189_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1___boxed(lean_object* v_as_1198_, lean_object* v_i_1199_, lean_object* v_stop_1200_, lean_object* v_b_1201_){
_start:
{
size_t v_i_boxed_1202_; size_t v_stop_boxed_1203_; lean_object* v_res_1204_; 
v_i_boxed_1202_ = lean_unbox_usize(v_i_1199_);
lean_dec(v_i_1199_);
v_stop_boxed_1203_ = lean_unbox_usize(v_stop_1200_);
lean_dec(v_stop_1200_);
v_res_1204_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_as_1198_, v_i_boxed_1202_, v_stop_boxed_1203_, v_b_1201_);
lean_dec_ref(v_as_1198_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(lean_object* v_x_1205_, lean_object* v_x_1206_){
_start:
{
if (lean_obj_tag(v_x_1205_) == 0)
{
lean_object* v_cs_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; uint8_t v___x_1210_; 
v_cs_1207_ = lean_ctor_get(v_x_1205_, 0);
v___x_1208_ = lean_unsigned_to_nat(0u);
v___x_1209_ = lean_array_get_size(v_cs_1207_);
v___x_1210_ = lean_nat_dec_lt(v___x_1208_, v___x_1209_);
if (v___x_1210_ == 0)
{
return v_x_1206_;
}
else
{
uint8_t v___x_1211_; 
v___x_1211_ = lean_nat_dec_le(v___x_1209_, v___x_1209_);
if (v___x_1211_ == 0)
{
if (v___x_1210_ == 0)
{
return v_x_1206_;
}
else
{
size_t v___x_1212_; size_t v___x_1213_; lean_object* v___x_1214_; 
v___x_1212_ = ((size_t)0ULL);
v___x_1213_ = lean_usize_of_nat(v___x_1209_);
v___x_1214_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_cs_1207_, v___x_1212_, v___x_1213_, v_x_1206_);
return v___x_1214_;
}
}
else
{
size_t v___x_1215_; size_t v___x_1216_; lean_object* v___x_1217_; 
v___x_1215_ = ((size_t)0ULL);
v___x_1216_ = lean_usize_of_nat(v___x_1209_);
v___x_1217_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_cs_1207_, v___x_1215_, v___x_1216_, v_x_1206_);
return v___x_1217_;
}
}
}
else
{
lean_object* v_vs_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; uint8_t v___x_1221_; 
v_vs_1218_ = lean_ctor_get(v_x_1205_, 0);
v___x_1219_ = lean_unsigned_to_nat(0u);
v___x_1220_ = lean_array_get_size(v_vs_1218_);
v___x_1221_ = lean_nat_dec_lt(v___x_1219_, v___x_1220_);
if (v___x_1221_ == 0)
{
return v_x_1206_;
}
else
{
uint8_t v___x_1222_; 
v___x_1222_ = lean_nat_dec_le(v___x_1220_, v___x_1220_);
if (v___x_1222_ == 0)
{
if (v___x_1221_ == 0)
{
return v_x_1206_;
}
else
{
size_t v___x_1223_; size_t v___x_1224_; lean_object* v___x_1225_; 
v___x_1223_ = ((size_t)0ULL);
v___x_1224_ = lean_usize_of_nat(v___x_1220_);
v___x_1225_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_vs_1218_, v___x_1223_, v___x_1224_, v_x_1206_);
return v___x_1225_;
}
}
else
{
size_t v___x_1226_; size_t v___x_1227_; lean_object* v___x_1228_; 
v___x_1226_ = ((size_t)0ULL);
v___x_1227_ = lean_usize_of_nat(v___x_1220_);
v___x_1228_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_vs_1218_, v___x_1226_, v___x_1227_, v_x_1206_);
return v___x_1228_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(lean_object* v_as_1229_, size_t v_i_1230_, size_t v_stop_1231_, lean_object* v_b_1232_){
_start:
{
uint8_t v___x_1233_; 
v___x_1233_ = lean_usize_dec_eq(v_i_1230_, v_stop_1231_);
if (v___x_1233_ == 0)
{
lean_object* v___x_1234_; lean_object* v___x_1235_; size_t v___x_1236_; size_t v___x_1237_; 
v___x_1234_ = lean_array_uget_borrowed(v_as_1229_, v_i_1230_);
v___x_1235_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(v___x_1234_, v_b_1232_);
v___x_1236_ = ((size_t)1ULL);
v___x_1237_ = lean_usize_add(v_i_1230_, v___x_1236_);
v_i_1230_ = v___x_1237_;
v_b_1232_ = v___x_1235_;
goto _start;
}
else
{
return v_b_1232_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1___boxed(lean_object* v_as_1239_, lean_object* v_i_1240_, lean_object* v_stop_1241_, lean_object* v_b_1242_){
_start:
{
size_t v_i_boxed_1243_; size_t v_stop_boxed_1244_; lean_object* v_res_1245_; 
v_i_boxed_1243_ = lean_unbox_usize(v_i_1240_);
lean_dec(v_i_1240_);
v_stop_boxed_1244_ = lean_unbox_usize(v_stop_1241_);
lean_dec(v_stop_1241_);
v_res_1245_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_as_1239_, v_i_boxed_1243_, v_stop_boxed_1244_, v_b_1242_);
lean_dec_ref(v_as_1239_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2___boxed(lean_object* v_x_1246_, lean_object* v_x_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(v_x_1246_, v_x_1247_);
lean_dec_ref(v_x_1246_);
return v_res_1248_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1249_; 
v___x_1249_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(lean_object* v_x_1250_, size_t v_x_1251_, size_t v_x_1252_, lean_object* v_x_1253_){
_start:
{
if (lean_obj_tag(v_x_1250_) == 0)
{
lean_object* v_cs_1254_; lean_object* v___x_1255_; size_t v___x_1256_; lean_object* v_j_1257_; lean_object* v___x_1258_; size_t v___x_1259_; size_t v___x_1260_; size_t v___x_1261_; size_t v___x_1262_; size_t v___x_1263_; size_t v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; uint8_t v___x_1269_; 
v_cs_1254_ = lean_ctor_get(v_x_1250_, 0);
v___x_1255_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0);
v___x_1256_ = lean_usize_shift_right(v_x_1251_, v_x_1252_);
v_j_1257_ = lean_usize_to_nat(v___x_1256_);
v___x_1258_ = lean_array_get_borrowed(v___x_1255_, v_cs_1254_, v_j_1257_);
v___x_1259_ = ((size_t)1ULL);
v___x_1260_ = lean_usize_shift_left(v___x_1259_, v_x_1252_);
v___x_1261_ = lean_usize_sub(v___x_1260_, v___x_1259_);
v___x_1262_ = lean_usize_land(v_x_1251_, v___x_1261_);
v___x_1263_ = ((size_t)5ULL);
v___x_1264_ = lean_usize_sub(v_x_1252_, v___x_1263_);
v___x_1265_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(v___x_1258_, v___x_1262_, v___x_1264_, v_x_1253_);
v___x_1266_ = lean_unsigned_to_nat(1u);
v___x_1267_ = lean_nat_add(v_j_1257_, v___x_1266_);
lean_dec(v_j_1257_);
v___x_1268_ = lean_array_get_size(v_cs_1254_);
v___x_1269_ = lean_nat_dec_lt(v___x_1267_, v___x_1268_);
if (v___x_1269_ == 0)
{
lean_dec(v___x_1267_);
return v___x_1265_;
}
else
{
uint8_t v___x_1270_; 
v___x_1270_ = lean_nat_dec_le(v___x_1268_, v___x_1268_);
if (v___x_1270_ == 0)
{
if (v___x_1269_ == 0)
{
lean_dec(v___x_1267_);
return v___x_1265_;
}
else
{
size_t v___x_1271_; size_t v___x_1272_; lean_object* v___x_1273_; 
v___x_1271_ = lean_usize_of_nat(v___x_1267_);
lean_dec(v___x_1267_);
v___x_1272_ = lean_usize_of_nat(v___x_1268_);
v___x_1273_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_cs_1254_, v___x_1271_, v___x_1272_, v___x_1265_);
return v___x_1273_;
}
}
else
{
size_t v___x_1274_; size_t v___x_1275_; lean_object* v___x_1276_; 
v___x_1274_ = lean_usize_of_nat(v___x_1267_);
lean_dec(v___x_1267_);
v___x_1275_ = lean_usize_of_nat(v___x_1268_);
v___x_1276_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_cs_1254_, v___x_1274_, v___x_1275_, v___x_1265_);
return v___x_1276_;
}
}
}
else
{
lean_object* v_vs_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; uint8_t v___x_1280_; 
v_vs_1277_ = lean_ctor_get(v_x_1250_, 0);
v___x_1278_ = lean_usize_to_nat(v_x_1251_);
v___x_1279_ = lean_array_get_size(v_vs_1277_);
v___x_1280_ = lean_nat_dec_lt(v___x_1278_, v___x_1279_);
if (v___x_1280_ == 0)
{
lean_dec(v___x_1278_);
return v_x_1253_;
}
else
{
uint8_t v___x_1281_; 
v___x_1281_ = lean_nat_dec_le(v___x_1279_, v___x_1279_);
if (v___x_1281_ == 0)
{
if (v___x_1280_ == 0)
{
lean_dec(v___x_1278_);
return v_x_1253_;
}
else
{
size_t v___x_1282_; size_t v___x_1283_; lean_object* v___x_1284_; 
v___x_1282_ = lean_usize_of_nat(v___x_1278_);
lean_dec(v___x_1278_);
v___x_1283_ = lean_usize_of_nat(v___x_1279_);
v___x_1284_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_vs_1277_, v___x_1282_, v___x_1283_, v_x_1253_);
return v___x_1284_;
}
}
else
{
size_t v___x_1285_; size_t v___x_1286_; lean_object* v___x_1287_; 
v___x_1285_ = lean_usize_of_nat(v___x_1278_);
lean_dec(v___x_1278_);
v___x_1286_ = lean_usize_of_nat(v___x_1279_);
v___x_1287_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_vs_1277_, v___x_1285_, v___x_1286_, v_x_1253_);
return v___x_1287_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___boxed(lean_object* v_x_1288_, lean_object* v_x_1289_, lean_object* v_x_1290_, lean_object* v_x_1291_){
_start:
{
size_t v_x_1632__boxed_1292_; size_t v_x_1633__boxed_1293_; lean_object* v_res_1294_; 
v_x_1632__boxed_1292_ = lean_unbox_usize(v_x_1289_);
lean_dec(v_x_1289_);
v_x_1633__boxed_1293_ = lean_unbox_usize(v_x_1290_);
lean_dec(v_x_1290_);
v_res_1294_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(v_x_1288_, v_x_1632__boxed_1292_, v_x_1633__boxed_1293_, v_x_1291_);
lean_dec_ref(v_x_1288_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0(lean_object* v_t_1295_, lean_object* v_init_1296_, lean_object* v_start_1297_){
_start:
{
lean_object* v___x_1298_; uint8_t v___x_1299_; 
v___x_1298_ = lean_unsigned_to_nat(0u);
v___x_1299_ = lean_nat_dec_eq(v_start_1297_, v___x_1298_);
if (v___x_1299_ == 0)
{
lean_object* v_root_1300_; lean_object* v_tail_1301_; size_t v_shift_1302_; lean_object* v_tailOff_1303_; uint8_t v___x_1304_; 
v_root_1300_ = lean_ctor_get(v_t_1295_, 0);
v_tail_1301_ = lean_ctor_get(v_t_1295_, 1);
v_shift_1302_ = lean_ctor_get_usize(v_t_1295_, 4);
v_tailOff_1303_ = lean_ctor_get(v_t_1295_, 3);
v___x_1304_ = lean_nat_dec_le(v_tailOff_1303_, v_start_1297_);
if (v___x_1304_ == 0)
{
size_t v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; uint8_t v___x_1308_; 
v___x_1305_ = lean_usize_of_nat(v_start_1297_);
v___x_1306_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(v_root_1300_, v___x_1305_, v_shift_1302_, v_init_1296_);
v___x_1307_ = lean_array_get_size(v_tail_1301_);
v___x_1308_ = lean_nat_dec_lt(v___x_1298_, v___x_1307_);
if (v___x_1308_ == 0)
{
return v___x_1306_;
}
else
{
uint8_t v___x_1309_; 
v___x_1309_ = lean_nat_dec_le(v___x_1307_, v___x_1307_);
if (v___x_1309_ == 0)
{
if (v___x_1308_ == 0)
{
return v___x_1306_;
}
else
{
size_t v___x_1310_; size_t v___x_1311_; lean_object* v___x_1312_; 
v___x_1310_ = ((size_t)0ULL);
v___x_1311_ = lean_usize_of_nat(v___x_1307_);
v___x_1312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1301_, v___x_1310_, v___x_1311_, v___x_1306_);
return v___x_1312_;
}
}
else
{
size_t v___x_1313_; size_t v___x_1314_; lean_object* v___x_1315_; 
v___x_1313_ = ((size_t)0ULL);
v___x_1314_ = lean_usize_of_nat(v___x_1307_);
v___x_1315_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1301_, v___x_1313_, v___x_1314_, v___x_1306_);
return v___x_1315_;
}
}
}
else
{
lean_object* v___x_1316_; lean_object* v___x_1317_; uint8_t v___x_1318_; 
v___x_1316_ = lean_nat_sub(v_start_1297_, v_tailOff_1303_);
v___x_1317_ = lean_array_get_size(v_tail_1301_);
v___x_1318_ = lean_nat_dec_lt(v___x_1316_, v___x_1317_);
if (v___x_1318_ == 0)
{
lean_dec(v___x_1316_);
return v_init_1296_;
}
else
{
uint8_t v___x_1319_; 
v___x_1319_ = lean_nat_dec_le(v___x_1317_, v___x_1317_);
if (v___x_1319_ == 0)
{
if (v___x_1318_ == 0)
{
lean_dec(v___x_1316_);
return v_init_1296_;
}
else
{
size_t v___x_1320_; size_t v___x_1321_; lean_object* v___x_1322_; 
v___x_1320_ = lean_usize_of_nat(v___x_1316_);
lean_dec(v___x_1316_);
v___x_1321_ = lean_usize_of_nat(v___x_1317_);
v___x_1322_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1301_, v___x_1320_, v___x_1321_, v_init_1296_);
return v___x_1322_;
}
}
else
{
size_t v___x_1323_; size_t v___x_1324_; lean_object* v___x_1325_; 
v___x_1323_ = lean_usize_of_nat(v___x_1316_);
lean_dec(v___x_1316_);
v___x_1324_ = lean_usize_of_nat(v___x_1317_);
v___x_1325_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1301_, v___x_1323_, v___x_1324_, v_init_1296_);
return v___x_1325_;
}
}
}
}
else
{
lean_object* v_root_1326_; lean_object* v_tail_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; uint8_t v___x_1330_; 
v_root_1326_ = lean_ctor_get(v_t_1295_, 0);
v_tail_1327_ = lean_ctor_get(v_t_1295_, 1);
v___x_1328_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(v_root_1326_, v_init_1296_);
v___x_1329_ = lean_array_get_size(v_tail_1327_);
v___x_1330_ = lean_nat_dec_lt(v___x_1298_, v___x_1329_);
if (v___x_1330_ == 0)
{
return v___x_1328_;
}
else
{
uint8_t v___x_1331_; 
v___x_1331_ = lean_nat_dec_le(v___x_1329_, v___x_1329_);
if (v___x_1331_ == 0)
{
if (v___x_1330_ == 0)
{
return v___x_1328_;
}
else
{
size_t v___x_1332_; size_t v___x_1333_; lean_object* v___x_1334_; 
v___x_1332_ = ((size_t)0ULL);
v___x_1333_ = lean_usize_of_nat(v___x_1329_);
v___x_1334_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1327_, v___x_1332_, v___x_1333_, v___x_1328_);
return v___x_1334_;
}
}
else
{
size_t v___x_1335_; size_t v___x_1336_; lean_object* v___x_1337_; 
v___x_1335_ = ((size_t)0ULL);
v___x_1336_ = lean_usize_of_nat(v___x_1329_);
v___x_1337_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1327_, v___x_1335_, v___x_1336_, v___x_1328_);
return v___x_1337_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0___boxed(lean_object* v_t_1338_, lean_object* v_init_1339_, lean_object* v_start_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0(v_t_1338_, v_init_1339_, v_start_1340_);
lean_dec(v_start_1340_);
lean_dec_ref(v_t_1338_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVarIds(lean_object* v_lctx_1344_){
_start:
{
lean_object* v_decls_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v_decls_1345_ = lean_ctor_get(v_lctx_1344_, 1);
v___x_1346_ = lean_unsigned_to_nat(0u);
v___x_1347_ = ((lean_object*)(l_Lean_LocalContext_getFVarIds___closed__0));
v___x_1348_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0(v_decls_1345_, v___x_1347_, v___x_1346_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVarIds___boxed(lean_object* v_lctx_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Lean_LocalContext_getFVarIds(v_lctx_1349_);
lean_dec_ref(v_lctx_1349_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0(size_t v_sz_1351_, size_t v_i_1352_, lean_object* v_bs_1353_){
_start:
{
uint8_t v___x_1354_; 
v___x_1354_ = lean_usize_dec_lt(v_i_1352_, v_sz_1351_);
if (v___x_1354_ == 0)
{
return v_bs_1353_;
}
else
{
lean_object* v_v_1355_; lean_object* v___x_1356_; lean_object* v_bs_x27_1357_; lean_object* v___x_1358_; size_t v___x_1359_; size_t v___x_1360_; lean_object* v___x_1361_; 
v_v_1355_ = lean_array_uget(v_bs_1353_, v_i_1352_);
v___x_1356_ = lean_unsigned_to_nat(0u);
v_bs_x27_1357_ = lean_array_uset(v_bs_1353_, v_i_1352_, v___x_1356_);
v___x_1358_ = l_Lean_mkFVar(v_v_1355_);
v___x_1359_ = ((size_t)1ULL);
v___x_1360_ = lean_usize_add(v_i_1352_, v___x_1359_);
v___x_1361_ = lean_array_uset(v_bs_x27_1357_, v_i_1352_, v___x_1358_);
v_i_1352_ = v___x_1360_;
v_bs_1353_ = v___x_1361_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0___boxed(lean_object* v_sz_1363_, lean_object* v_i_1364_, lean_object* v_bs_1365_){
_start:
{
size_t v_sz_boxed_1366_; size_t v_i_boxed_1367_; lean_object* v_res_1368_; 
v_sz_boxed_1366_ = lean_unbox_usize(v_sz_1363_);
lean_dec(v_sz_1363_);
v_i_boxed_1367_ = lean_unbox_usize(v_i_1364_);
lean_dec(v_i_1364_);
v_res_1368_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0(v_sz_boxed_1366_, v_i_boxed_1367_, v_bs_1365_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVars(lean_object* v_lctx_1369_){
_start:
{
lean_object* v___x_1370_; size_t v_sz_1371_; size_t v___x_1372_; lean_object* v___x_1373_; 
v___x_1370_ = l_Lean_LocalContext_getFVarIds(v_lctx_1369_);
v_sz_1371_ = lean_array_size(v___x_1370_);
v___x_1372_ = ((size_t)0ULL);
v___x_1373_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0(v_sz_1371_, v___x_1372_, v___x_1370_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVars___boxed(lean_object* v_lctx_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l_Lean_LocalContext_getFVars(v_lctx_1374_);
lean_dec_ref(v_lctx_1374_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(lean_object* v_a_1376_){
_start:
{
lean_object* v_size_1377_; lean_object* v___x_1378_; uint8_t v___x_1379_; 
v_size_1377_ = lean_ctor_get(v_a_1376_, 2);
v___x_1378_ = lean_unsigned_to_nat(0u);
v___x_1379_ = lean_nat_dec_eq(v_size_1377_, v___x_1378_);
if (v___x_1379_ == 0)
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1380_ = lean_box(0);
v___x_1381_ = lean_unsigned_to_nat(1u);
v___x_1382_ = lean_nat_sub(v_size_1377_, v___x_1381_);
lean_inc_ref(v_a_1376_);
v___x_1383_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1380_, v_a_1376_, v___x_1382_);
lean_dec(v___x_1382_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v___x_1384_; 
v___x_1384_ = l_Lean_PersistentArray_pop___redArg(v_a_1376_);
v_a_1376_ = v___x_1384_;
goto _start;
}
else
{
lean_dec_ref(v___x_1383_);
return v_a_1376_;
}
}
else
{
return v_a_1376_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(lean_object* v_k_1386_, lean_object* v_t_1387_){
_start:
{
if (lean_obj_tag(v_t_1387_) == 0)
{
lean_object* v_k_1388_; lean_object* v_v_1389_; lean_object* v_l_1390_; lean_object* v_r_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_2045_; 
v_k_1388_ = lean_ctor_get(v_t_1387_, 1);
v_v_1389_ = lean_ctor_get(v_t_1387_, 2);
v_l_1390_ = lean_ctor_get(v_t_1387_, 3);
v_r_1391_ = lean_ctor_get(v_t_1387_, 4);
v_isSharedCheck_2045_ = !lean_is_exclusive(v_t_1387_);
if (v_isSharedCheck_2045_ == 0)
{
lean_object* v_unused_2046_; 
v_unused_2046_ = lean_ctor_get(v_t_1387_, 0);
lean_dec(v_unused_2046_);
v___x_1393_ = v_t_1387_;
v_isShared_1394_ = v_isSharedCheck_2045_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_r_1391_);
lean_inc(v_l_1390_);
lean_inc(v_v_1389_);
lean_inc(v_k_1388_);
lean_dec(v_t_1387_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_2045_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
uint8_t v___x_1395_; 
v___x_1395_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1386_, v_k_1388_);
switch(v___x_1395_)
{
case 0:
{
lean_object* v_impl_1396_; lean_object* v___x_1397_; 
v_impl_1396_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_1386_, v_l_1390_);
v___x_1397_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1396_) == 0)
{
if (lean_obj_tag(v_r_1391_) == 0)
{
lean_object* v_size_1398_; lean_object* v_size_1399_; lean_object* v_k_1400_; lean_object* v_v_1401_; lean_object* v_l_1402_; lean_object* v_r_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; uint8_t v___x_1406_; 
v_size_1398_ = lean_ctor_get(v_impl_1396_, 0);
lean_inc(v_size_1398_);
v_size_1399_ = lean_ctor_get(v_r_1391_, 0);
v_k_1400_ = lean_ctor_get(v_r_1391_, 1);
v_v_1401_ = lean_ctor_get(v_r_1391_, 2);
v_l_1402_ = lean_ctor_get(v_r_1391_, 3);
lean_inc(v_l_1402_);
v_r_1403_ = lean_ctor_get(v_r_1391_, 4);
v___x_1404_ = lean_unsigned_to_nat(3u);
v___x_1405_ = lean_nat_mul(v___x_1404_, v_size_1398_);
v___x_1406_ = lean_nat_dec_lt(v___x_1405_, v_size_1399_);
lean_dec(v___x_1405_);
if (v___x_1406_ == 0)
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1410_; 
lean_dec(v_l_1402_);
v___x_1407_ = lean_nat_add(v___x_1397_, v_size_1398_);
lean_dec(v_size_1398_);
v___x_1408_ = lean_nat_add(v___x_1407_, v_size_1399_);
lean_dec(v___x_1407_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 3, v_impl_1396_);
lean_ctor_set(v___x_1393_, 0, v___x_1408_);
v___x_1410_ = v___x_1393_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v___x_1408_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v_k_1388_);
lean_ctor_set(v_reuseFailAlloc_1411_, 2, v_v_1389_);
lean_ctor_set(v_reuseFailAlloc_1411_, 3, v_impl_1396_);
lean_ctor_set(v_reuseFailAlloc_1411_, 4, v_r_1391_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
else
{
lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1475_; 
lean_inc(v_r_1403_);
lean_inc(v_v_1401_);
lean_inc(v_k_1400_);
lean_inc(v_size_1399_);
v_isSharedCheck_1475_ = !lean_is_exclusive(v_r_1391_);
if (v_isSharedCheck_1475_ == 0)
{
lean_object* v_unused_1476_; lean_object* v_unused_1477_; lean_object* v_unused_1478_; lean_object* v_unused_1479_; lean_object* v_unused_1480_; 
v_unused_1476_ = lean_ctor_get(v_r_1391_, 4);
lean_dec(v_unused_1476_);
v_unused_1477_ = lean_ctor_get(v_r_1391_, 3);
lean_dec(v_unused_1477_);
v_unused_1478_ = lean_ctor_get(v_r_1391_, 2);
lean_dec(v_unused_1478_);
v_unused_1479_ = lean_ctor_get(v_r_1391_, 1);
lean_dec(v_unused_1479_);
v_unused_1480_ = lean_ctor_get(v_r_1391_, 0);
lean_dec(v_unused_1480_);
v___x_1413_ = v_r_1391_;
v_isShared_1414_ = v_isSharedCheck_1475_;
goto v_resetjp_1412_;
}
else
{
lean_dec(v_r_1391_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1475_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v_size_1415_; lean_object* v_k_1416_; lean_object* v_v_1417_; lean_object* v_l_1418_; lean_object* v_r_1419_; lean_object* v_size_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; uint8_t v___x_1423_; 
v_size_1415_ = lean_ctor_get(v_l_1402_, 0);
v_k_1416_ = lean_ctor_get(v_l_1402_, 1);
v_v_1417_ = lean_ctor_get(v_l_1402_, 2);
v_l_1418_ = lean_ctor_get(v_l_1402_, 3);
v_r_1419_ = lean_ctor_get(v_l_1402_, 4);
v_size_1420_ = lean_ctor_get(v_r_1403_, 0);
v___x_1421_ = lean_unsigned_to_nat(2u);
v___x_1422_ = lean_nat_mul(v___x_1421_, v_size_1420_);
v___x_1423_ = lean_nat_dec_lt(v_size_1415_, v___x_1422_);
lean_dec(v___x_1422_);
if (v___x_1423_ == 0)
{
lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1451_; 
lean_inc(v_r_1419_);
lean_inc(v_l_1418_);
lean_inc(v_v_1417_);
lean_inc(v_k_1416_);
v_isSharedCheck_1451_ = !lean_is_exclusive(v_l_1402_);
if (v_isSharedCheck_1451_ == 0)
{
lean_object* v_unused_1452_; lean_object* v_unused_1453_; lean_object* v_unused_1454_; lean_object* v_unused_1455_; lean_object* v_unused_1456_; 
v_unused_1452_ = lean_ctor_get(v_l_1402_, 4);
lean_dec(v_unused_1452_);
v_unused_1453_ = lean_ctor_get(v_l_1402_, 3);
lean_dec(v_unused_1453_);
v_unused_1454_ = lean_ctor_get(v_l_1402_, 2);
lean_dec(v_unused_1454_);
v_unused_1455_ = lean_ctor_get(v_l_1402_, 1);
lean_dec(v_unused_1455_);
v_unused_1456_ = lean_ctor_get(v_l_1402_, 0);
lean_dec(v_unused_1456_);
v___x_1425_ = v_l_1402_;
v_isShared_1426_ = v_isSharedCheck_1451_;
goto v_resetjp_1424_;
}
else
{
lean_dec(v_l_1402_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1451_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1441_; 
v___x_1427_ = lean_nat_add(v___x_1397_, v_size_1398_);
lean_dec(v_size_1398_);
v___x_1428_ = lean_nat_add(v___x_1427_, v_size_1399_);
lean_dec(v_size_1399_);
if (lean_obj_tag(v_l_1418_) == 0)
{
lean_object* v_size_1449_; 
v_size_1449_ = lean_ctor_get(v_l_1418_, 0);
lean_inc(v_size_1449_);
v___y_1441_ = v_size_1449_;
goto v___jp_1440_;
}
else
{
lean_object* v___x_1450_; 
v___x_1450_ = lean_unsigned_to_nat(0u);
v___y_1441_ = v___x_1450_;
goto v___jp_1440_;
}
v___jp_1429_:
{
lean_object* v___x_1433_; lean_object* v___x_1435_; 
v___x_1433_ = lean_nat_add(v___y_1431_, v___y_1432_);
lean_dec(v___y_1432_);
lean_dec(v___y_1431_);
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 4, v_r_1403_);
lean_ctor_set(v___x_1425_, 3, v_r_1419_);
lean_ctor_set(v___x_1425_, 2, v_v_1401_);
lean_ctor_set(v___x_1425_, 1, v_k_1400_);
lean_ctor_set(v___x_1425_, 0, v___x_1433_);
v___x_1435_ = v___x_1425_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1433_);
lean_ctor_set(v_reuseFailAlloc_1439_, 1, v_k_1400_);
lean_ctor_set(v_reuseFailAlloc_1439_, 2, v_v_1401_);
lean_ctor_set(v_reuseFailAlloc_1439_, 3, v_r_1419_);
lean_ctor_set(v_reuseFailAlloc_1439_, 4, v_r_1403_);
v___x_1435_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
lean_object* v___x_1437_; 
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 4, v___x_1435_);
lean_ctor_set(v___x_1413_, 3, v___y_1430_);
lean_ctor_set(v___x_1413_, 2, v_v_1417_);
lean_ctor_set(v___x_1413_, 1, v_k_1416_);
lean_ctor_set(v___x_1413_, 0, v___x_1428_);
v___x_1437_ = v___x_1413_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1428_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v_k_1416_);
lean_ctor_set(v_reuseFailAlloc_1438_, 2, v_v_1417_);
lean_ctor_set(v_reuseFailAlloc_1438_, 3, v___y_1430_);
lean_ctor_set(v_reuseFailAlloc_1438_, 4, v___x_1435_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
v___jp_1440_:
{
lean_object* v___x_1442_; lean_object* v___x_1444_; 
v___x_1442_ = lean_nat_add(v___x_1427_, v___y_1441_);
lean_dec(v___y_1441_);
lean_dec(v___x_1427_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 4, v_l_1418_);
lean_ctor_set(v___x_1393_, 3, v_impl_1396_);
lean_ctor_set(v___x_1393_, 0, v___x_1442_);
v___x_1444_ = v___x_1393_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1442_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v_k_1388_);
lean_ctor_set(v_reuseFailAlloc_1448_, 2, v_v_1389_);
lean_ctor_set(v_reuseFailAlloc_1448_, 3, v_impl_1396_);
lean_ctor_set(v_reuseFailAlloc_1448_, 4, v_l_1418_);
v___x_1444_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
lean_object* v___x_1445_; 
v___x_1445_ = lean_nat_add(v___x_1397_, v_size_1420_);
if (lean_obj_tag(v_r_1419_) == 0)
{
lean_object* v_size_1446_; 
v_size_1446_ = lean_ctor_get(v_r_1419_, 0);
lean_inc(v_size_1446_);
v___y_1430_ = v___x_1444_;
v___y_1431_ = v___x_1445_;
v___y_1432_ = v_size_1446_;
goto v___jp_1429_;
}
else
{
lean_object* v___x_1447_; 
v___x_1447_ = lean_unsigned_to_nat(0u);
v___y_1430_ = v___x_1444_;
v___y_1431_ = v___x_1445_;
v___y_1432_ = v___x_1447_;
goto v___jp_1429_;
}
}
}
}
}
else
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1461_; 
lean_del_object(v___x_1393_);
v___x_1457_ = lean_nat_add(v___x_1397_, v_size_1398_);
lean_dec(v_size_1398_);
v___x_1458_ = lean_nat_add(v___x_1457_, v_size_1399_);
lean_dec(v_size_1399_);
v___x_1459_ = lean_nat_add(v___x_1457_, v_size_1415_);
lean_dec(v___x_1457_);
lean_inc_ref(v_impl_1396_);
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 4, v_l_1402_);
lean_ctor_set(v___x_1413_, 3, v_impl_1396_);
lean_ctor_set(v___x_1413_, 2, v_v_1389_);
lean_ctor_set(v___x_1413_, 1, v_k_1388_);
lean_ctor_set(v___x_1413_, 0, v___x_1459_);
v___x_1461_ = v___x_1413_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v___x_1459_);
lean_ctor_set(v_reuseFailAlloc_1474_, 1, v_k_1388_);
lean_ctor_set(v_reuseFailAlloc_1474_, 2, v_v_1389_);
lean_ctor_set(v_reuseFailAlloc_1474_, 3, v_impl_1396_);
lean_ctor_set(v_reuseFailAlloc_1474_, 4, v_l_1402_);
v___x_1461_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1468_; 
v_isSharedCheck_1468_ = !lean_is_exclusive(v_impl_1396_);
if (v_isSharedCheck_1468_ == 0)
{
lean_object* v_unused_1469_; lean_object* v_unused_1470_; lean_object* v_unused_1471_; lean_object* v_unused_1472_; lean_object* v_unused_1473_; 
v_unused_1469_ = lean_ctor_get(v_impl_1396_, 4);
lean_dec(v_unused_1469_);
v_unused_1470_ = lean_ctor_get(v_impl_1396_, 3);
lean_dec(v_unused_1470_);
v_unused_1471_ = lean_ctor_get(v_impl_1396_, 2);
lean_dec(v_unused_1471_);
v_unused_1472_ = lean_ctor_get(v_impl_1396_, 1);
lean_dec(v_unused_1472_);
v_unused_1473_ = lean_ctor_get(v_impl_1396_, 0);
lean_dec(v_unused_1473_);
v___x_1463_ = v_impl_1396_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_dec(v_impl_1396_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 4, v_r_1403_);
lean_ctor_set(v___x_1463_, 3, v___x_1461_);
lean_ctor_set(v___x_1463_, 2, v_v_1401_);
lean_ctor_set(v___x_1463_, 1, v_k_1400_);
lean_ctor_set(v___x_1463_, 0, v___x_1458_);
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1458_);
lean_ctor_set(v_reuseFailAlloc_1467_, 1, v_k_1400_);
lean_ctor_set(v_reuseFailAlloc_1467_, 2, v_v_1401_);
lean_ctor_set(v_reuseFailAlloc_1467_, 3, v___x_1461_);
lean_ctor_set(v_reuseFailAlloc_1467_, 4, v_r_1403_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1481_; lean_object* v___x_1482_; lean_object* v___x_1484_; 
v_size_1481_ = lean_ctor_get(v_impl_1396_, 0);
lean_inc(v_size_1481_);
v___x_1482_ = lean_nat_add(v___x_1397_, v_size_1481_);
lean_dec(v_size_1481_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 3, v_impl_1396_);
lean_ctor_set(v___x_1393_, 0, v___x_1482_);
v___x_1484_ = v___x_1393_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1482_);
lean_ctor_set(v_reuseFailAlloc_1485_, 1, v_k_1388_);
lean_ctor_set(v_reuseFailAlloc_1485_, 2, v_v_1389_);
lean_ctor_set(v_reuseFailAlloc_1485_, 3, v_impl_1396_);
lean_ctor_set(v_reuseFailAlloc_1485_, 4, v_r_1391_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
else
{
if (lean_obj_tag(v_r_1391_) == 0)
{
lean_object* v_l_1486_; 
v_l_1486_ = lean_ctor_get(v_r_1391_, 3);
lean_inc(v_l_1486_);
if (lean_obj_tag(v_l_1486_) == 0)
{
lean_object* v_r_1487_; 
v_r_1487_ = lean_ctor_get(v_r_1391_, 4);
lean_inc(v_r_1487_);
if (lean_obj_tag(v_r_1487_) == 0)
{
lean_object* v_size_1488_; lean_object* v_k_1489_; lean_object* v_v_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1503_; 
v_size_1488_ = lean_ctor_get(v_r_1391_, 0);
v_k_1489_ = lean_ctor_get(v_r_1391_, 1);
v_v_1490_ = lean_ctor_get(v_r_1391_, 2);
v_isSharedCheck_1503_ = !lean_is_exclusive(v_r_1391_);
if (v_isSharedCheck_1503_ == 0)
{
lean_object* v_unused_1504_; lean_object* v_unused_1505_; 
v_unused_1504_ = lean_ctor_get(v_r_1391_, 4);
lean_dec(v_unused_1504_);
v_unused_1505_ = lean_ctor_get(v_r_1391_, 3);
lean_dec(v_unused_1505_);
v___x_1492_ = v_r_1391_;
v_isShared_1493_ = v_isSharedCheck_1503_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_v_1490_);
lean_inc(v_k_1489_);
lean_inc(v_size_1488_);
lean_dec(v_r_1391_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1503_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v_size_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1498_; 
v_size_1494_ = lean_ctor_get(v_l_1486_, 0);
v___x_1495_ = lean_nat_add(v___x_1397_, v_size_1488_);
lean_dec(v_size_1488_);
v___x_1496_ = lean_nat_add(v___x_1397_, v_size_1494_);
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 4, v_l_1486_);
lean_ctor_set(v___x_1492_, 3, v_impl_1396_);
lean_ctor_set(v___x_1492_, 2, v_v_1389_);
lean_ctor_set(v___x_1492_, 1, v_k_1388_);
lean_ctor_set(v___x_1492_, 0, v___x_1496_);
v___x_1498_ = v___x_1492_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1496_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v_k_1388_);
lean_ctor_set(v_reuseFailAlloc_1502_, 2, v_v_1389_);
lean_ctor_set(v_reuseFailAlloc_1502_, 3, v_impl_1396_);
lean_ctor_set(v_reuseFailAlloc_1502_, 4, v_l_1486_);
v___x_1498_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
lean_object* v___x_1500_; 
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 4, v_r_1487_);
lean_ctor_set(v___x_1393_, 3, v___x_1498_);
lean_ctor_set(v___x_1393_, 2, v_v_1490_);
lean_ctor_set(v___x_1393_, 1, v_k_1489_);
lean_ctor_set(v___x_1393_, 0, v___x_1495_);
v___x_1500_ = v___x_1393_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1495_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v_k_1489_);
lean_ctor_set(v_reuseFailAlloc_1501_, 2, v_v_1490_);
lean_ctor_set(v_reuseFailAlloc_1501_, 3, v___x_1498_);
lean_ctor_set(v_reuseFailAlloc_1501_, 4, v_r_1487_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
else
{
lean_object* v_k_1506_; lean_object* v_v_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1530_; 
v_k_1506_ = lean_ctor_get(v_r_1391_, 1);
v_v_1507_ = lean_ctor_get(v_r_1391_, 2);
v_isSharedCheck_1530_ = !lean_is_exclusive(v_r_1391_);
if (v_isSharedCheck_1530_ == 0)
{
lean_object* v_unused_1531_; lean_object* v_unused_1532_; lean_object* v_unused_1533_; 
v_unused_1531_ = lean_ctor_get(v_r_1391_, 4);
lean_dec(v_unused_1531_);
v_unused_1532_ = lean_ctor_get(v_r_1391_, 3);
lean_dec(v_unused_1532_);
v_unused_1533_ = lean_ctor_get(v_r_1391_, 0);
lean_dec(v_unused_1533_);
v___x_1509_ = v_r_1391_;
v_isShared_1510_ = v_isSharedCheck_1530_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_v_1507_);
lean_inc(v_k_1506_);
lean_dec(v_r_1391_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1530_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v_k_1511_; lean_object* v_v_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1526_; 
v_k_1511_ = lean_ctor_get(v_l_1486_, 1);
v_v_1512_ = lean_ctor_get(v_l_1486_, 2);
v_isSharedCheck_1526_ = !lean_is_exclusive(v_l_1486_);
if (v_isSharedCheck_1526_ == 0)
{
lean_object* v_unused_1527_; lean_object* v_unused_1528_; lean_object* v_unused_1529_; 
v_unused_1527_ = lean_ctor_get(v_l_1486_, 4);
lean_dec(v_unused_1527_);
v_unused_1528_ = lean_ctor_get(v_l_1486_, 3);
lean_dec(v_unused_1528_);
v_unused_1529_ = lean_ctor_get(v_l_1486_, 0);
lean_dec(v_unused_1529_);
v___x_1514_ = v_l_1486_;
v_isShared_1515_ = v_isSharedCheck_1526_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_v_1512_);
lean_inc(v_k_1511_);
lean_dec(v_l_1486_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1526_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1516_; lean_object* v___x_1518_; 
v___x_1516_ = lean_unsigned_to_nat(3u);
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 4, v_r_1487_);
lean_ctor_set(v___x_1514_, 3, v_r_1487_);
lean_ctor_set(v___x_1514_, 2, v_v_1389_);
lean_ctor_set(v___x_1514_, 1, v_k_1388_);
lean_ctor_set(v___x_1514_, 0, v___x_1397_);
v___x_1518_ = v___x_1514_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1397_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v_k_1388_);
lean_ctor_set(v_reuseFailAlloc_1525_, 2, v_v_1389_);
lean_ctor_set(v_reuseFailAlloc_1525_, 3, v_r_1487_);
lean_ctor_set(v_reuseFailAlloc_1525_, 4, v_r_1487_);
v___x_1518_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
lean_object* v___x_1520_; 
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 3, v_r_1487_);
lean_ctor_set(v___x_1509_, 0, v___x_1397_);
v___x_1520_ = v___x_1509_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1397_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_k_1506_);
lean_ctor_set(v_reuseFailAlloc_1524_, 2, v_v_1507_);
lean_ctor_set(v_reuseFailAlloc_1524_, 3, v_r_1487_);
lean_ctor_set(v_reuseFailAlloc_1524_, 4, v_r_1487_);
v___x_1520_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
lean_object* v___x_1522_; 
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 4, v___x_1520_);
lean_ctor_set(v___x_1393_, 3, v___x_1518_);
lean_ctor_set(v___x_1393_, 2, v_v_1512_);
lean_ctor_set(v___x_1393_, 1, v_k_1511_);
lean_ctor_set(v___x_1393_, 0, v___x_1516_);
v___x_1522_ = v___x_1393_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1516_);
lean_ctor_set(v_reuseFailAlloc_1523_, 1, v_k_1511_);
lean_ctor_set(v_reuseFailAlloc_1523_, 2, v_v_1512_);
lean_ctor_set(v_reuseFailAlloc_1523_, 3, v___x_1518_);
lean_ctor_set(v_reuseFailAlloc_1523_, 4, v___x_1520_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1534_; 
v_r_1534_ = lean_ctor_get(v_r_1391_, 4);
lean_inc(v_r_1534_);
if (lean_obj_tag(v_r_1534_) == 0)
{
lean_object* v_k_1535_; lean_object* v_v_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1547_; 
v_k_1535_ = lean_ctor_get(v_r_1391_, 1);
v_v_1536_ = lean_ctor_get(v_r_1391_, 2);
v_isSharedCheck_1547_ = !lean_is_exclusive(v_r_1391_);
if (v_isSharedCheck_1547_ == 0)
{
lean_object* v_unused_1548_; lean_object* v_unused_1549_; lean_object* v_unused_1550_; 
v_unused_1548_ = lean_ctor_get(v_r_1391_, 4);
lean_dec(v_unused_1548_);
v_unused_1549_ = lean_ctor_get(v_r_1391_, 3);
lean_dec(v_unused_1549_);
v_unused_1550_ = lean_ctor_get(v_r_1391_, 0);
lean_dec(v_unused_1550_);
v___x_1538_ = v_r_1391_;
v_isShared_1539_ = v_isSharedCheck_1547_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_v_1536_);
lean_inc(v_k_1535_);
lean_dec(v_r_1391_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1547_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1540_; lean_object* v___x_1542_; 
v___x_1540_ = lean_unsigned_to_nat(3u);
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 4, v_l_1486_);
lean_ctor_set(v___x_1538_, 2, v_v_1389_);
lean_ctor_set(v___x_1538_, 1, v_k_1388_);
lean_ctor_set(v___x_1538_, 0, v___x_1397_);
v___x_1542_ = v___x_1538_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1397_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v_k_1388_);
lean_ctor_set(v_reuseFailAlloc_1546_, 2, v_v_1389_);
lean_ctor_set(v_reuseFailAlloc_1546_, 3, v_l_1486_);
lean_ctor_set(v_reuseFailAlloc_1546_, 4, v_l_1486_);
v___x_1542_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
lean_object* v___x_1544_; 
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 4, v_r_1534_);
lean_ctor_set(v___x_1393_, 3, v___x_1542_);
lean_ctor_set(v___x_1393_, 2, v_v_1536_);
lean_ctor_set(v___x_1393_, 1, v_k_1535_);
lean_ctor_set(v___x_1393_, 0, v___x_1540_);
v___x_1544_ = v___x_1393_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1540_);
lean_ctor_set(v_reuseFailAlloc_1545_, 1, v_k_1535_);
lean_ctor_set(v_reuseFailAlloc_1545_, 2, v_v_1536_);
lean_ctor_set(v_reuseFailAlloc_1545_, 3, v___x_1542_);
lean_ctor_set(v_reuseFailAlloc_1545_, 4, v_r_1534_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
}
else
{
lean_object* v_size_1551_; lean_object* v_k_1552_; lean_object* v_v_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1564_; 
v_size_1551_ = lean_ctor_get(v_r_1391_, 0);
v_k_1552_ = lean_ctor_get(v_r_1391_, 1);
v_v_1553_ = lean_ctor_get(v_r_1391_, 2);
v_isSharedCheck_1564_ = !lean_is_exclusive(v_r_1391_);
if (v_isSharedCheck_1564_ == 0)
{
lean_object* v_unused_1565_; lean_object* v_unused_1566_; 
v_unused_1565_ = lean_ctor_get(v_r_1391_, 4);
lean_dec(v_unused_1565_);
v_unused_1566_ = lean_ctor_get(v_r_1391_, 3);
lean_dec(v_unused_1566_);
v___x_1555_ = v_r_1391_;
v_isShared_1556_ = v_isSharedCheck_1564_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_v_1553_);
lean_inc(v_k_1552_);
lean_inc(v_size_1551_);
lean_dec(v_r_1391_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1564_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 3, v_r_1534_);
v___x_1558_ = v___x_1555_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_size_1551_);
lean_ctor_set(v_reuseFailAlloc_1563_, 1, v_k_1552_);
lean_ctor_set(v_reuseFailAlloc_1563_, 2, v_v_1553_);
lean_ctor_set(v_reuseFailAlloc_1563_, 3, v_r_1534_);
lean_ctor_set(v_reuseFailAlloc_1563_, 4, v_r_1534_);
v___x_1558_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
lean_object* v___x_1559_; lean_object* v___x_1561_; 
v___x_1559_ = lean_unsigned_to_nat(2u);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 4, v___x_1558_);
lean_ctor_set(v___x_1393_, 3, v_r_1534_);
lean_ctor_set(v___x_1393_, 0, v___x_1559_);
v___x_1561_ = v___x_1393_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1559_);
lean_ctor_set(v_reuseFailAlloc_1562_, 1, v_k_1388_);
lean_ctor_set(v_reuseFailAlloc_1562_, 2, v_v_1389_);
lean_ctor_set(v_reuseFailAlloc_1562_, 3, v_r_1534_);
lean_ctor_set(v_reuseFailAlloc_1562_, 4, v___x_1558_);
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
}
}
else
{
lean_object* v___x_1568_; 
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 3, v_r_1391_);
lean_ctor_set(v___x_1393_, 0, v___x_1397_);
v___x_1568_ = v___x_1393_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v___x_1397_);
lean_ctor_set(v_reuseFailAlloc_1569_, 1, v_k_1388_);
lean_ctor_set(v_reuseFailAlloc_1569_, 2, v_v_1389_);
lean_ctor_set(v_reuseFailAlloc_1569_, 3, v_r_1391_);
lean_ctor_set(v_reuseFailAlloc_1569_, 4, v_r_1391_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
}
case 1:
{
lean_del_object(v___x_1393_);
lean_dec(v_v_1389_);
lean_dec(v_k_1388_);
if (lean_obj_tag(v_l_1390_) == 0)
{
if (lean_obj_tag(v_r_1391_) == 0)
{
lean_object* v_size_1570_; lean_object* v_k_1571_; lean_object* v_v_1572_; lean_object* v_l_1573_; lean_object* v_r_1574_; lean_object* v_size_1575_; lean_object* v_k_1576_; lean_object* v_v_1577_; lean_object* v_l_1578_; lean_object* v_r_1579_; lean_object* v___x_1580_; uint8_t v___x_1581_; 
v_size_1570_ = lean_ctor_get(v_l_1390_, 0);
v_k_1571_ = lean_ctor_get(v_l_1390_, 1);
v_v_1572_ = lean_ctor_get(v_l_1390_, 2);
v_l_1573_ = lean_ctor_get(v_l_1390_, 3);
v_r_1574_ = lean_ctor_get(v_l_1390_, 4);
lean_inc(v_r_1574_);
v_size_1575_ = lean_ctor_get(v_r_1391_, 0);
v_k_1576_ = lean_ctor_get(v_r_1391_, 1);
v_v_1577_ = lean_ctor_get(v_r_1391_, 2);
v_l_1578_ = lean_ctor_get(v_r_1391_, 3);
lean_inc(v_l_1578_);
v_r_1579_ = lean_ctor_get(v_r_1391_, 4);
v___x_1580_ = lean_unsigned_to_nat(1u);
v___x_1581_ = lean_nat_dec_lt(v_size_1570_, v_size_1575_);
if (v___x_1581_ == 0)
{
lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1717_; 
lean_inc(v_l_1573_);
lean_inc(v_v_1572_);
lean_inc(v_k_1571_);
v_isSharedCheck_1717_ = !lean_is_exclusive(v_l_1390_);
if (v_isSharedCheck_1717_ == 0)
{
lean_object* v_unused_1718_; lean_object* v_unused_1719_; lean_object* v_unused_1720_; lean_object* v_unused_1721_; lean_object* v_unused_1722_; 
v_unused_1718_ = lean_ctor_get(v_l_1390_, 4);
lean_dec(v_unused_1718_);
v_unused_1719_ = lean_ctor_get(v_l_1390_, 3);
lean_dec(v_unused_1719_);
v_unused_1720_ = lean_ctor_get(v_l_1390_, 2);
lean_dec(v_unused_1720_);
v_unused_1721_ = lean_ctor_get(v_l_1390_, 1);
lean_dec(v_unused_1721_);
v_unused_1722_ = lean_ctor_get(v_l_1390_, 0);
lean_dec(v_unused_1722_);
v___x_1583_ = v_l_1390_;
v_isShared_1584_ = v_isSharedCheck_1717_;
goto v_resetjp_1582_;
}
else
{
lean_dec(v_l_1390_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1717_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1585_; lean_object* v_tree_1586_; 
v___x_1585_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_1571_, v_v_1572_, v_l_1573_, v_r_1574_);
v_tree_1586_ = lean_ctor_get(v___x_1585_, 2);
lean_inc(v_tree_1586_);
if (lean_obj_tag(v_tree_1586_) == 0)
{
lean_object* v_k_1587_; lean_object* v_v_1588_; lean_object* v_size_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; uint8_t v___x_1592_; 
v_k_1587_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_k_1587_);
v_v_1588_ = lean_ctor_get(v___x_1585_, 1);
lean_inc(v_v_1588_);
lean_dec_ref(v___x_1585_);
v_size_1589_ = lean_ctor_get(v_tree_1586_, 0);
v___x_1590_ = lean_unsigned_to_nat(3u);
v___x_1591_ = lean_nat_mul(v___x_1590_, v_size_1589_);
v___x_1592_ = lean_nat_dec_lt(v___x_1591_, v_size_1575_);
lean_dec(v___x_1591_);
if (v___x_1592_ == 0)
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1596_; 
lean_dec(v_l_1578_);
v___x_1593_ = lean_nat_add(v___x_1580_, v_size_1589_);
v___x_1594_ = lean_nat_add(v___x_1593_, v_size_1575_);
lean_dec(v___x_1593_);
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 4, v_r_1391_);
lean_ctor_set(v___x_1583_, 3, v_tree_1586_);
lean_ctor_set(v___x_1583_, 2, v_v_1588_);
lean_ctor_set(v___x_1583_, 1, v_k_1587_);
lean_ctor_set(v___x_1583_, 0, v___x_1594_);
v___x_1596_ = v___x_1583_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v___x_1594_);
lean_ctor_set(v_reuseFailAlloc_1597_, 1, v_k_1587_);
lean_ctor_set(v_reuseFailAlloc_1597_, 2, v_v_1588_);
lean_ctor_set(v_reuseFailAlloc_1597_, 3, v_tree_1586_);
lean_ctor_set(v_reuseFailAlloc_1597_, 4, v_r_1391_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
else
{
lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1652_; 
lean_inc(v_r_1579_);
lean_inc(v_v_1577_);
lean_inc(v_k_1576_);
lean_inc(v_size_1575_);
v_isSharedCheck_1652_ = !lean_is_exclusive(v_r_1391_);
if (v_isSharedCheck_1652_ == 0)
{
lean_object* v_unused_1653_; lean_object* v_unused_1654_; lean_object* v_unused_1655_; lean_object* v_unused_1656_; lean_object* v_unused_1657_; 
v_unused_1653_ = lean_ctor_get(v_r_1391_, 4);
lean_dec(v_unused_1653_);
v_unused_1654_ = lean_ctor_get(v_r_1391_, 3);
lean_dec(v_unused_1654_);
v_unused_1655_ = lean_ctor_get(v_r_1391_, 2);
lean_dec(v_unused_1655_);
v_unused_1656_ = lean_ctor_get(v_r_1391_, 1);
lean_dec(v_unused_1656_);
v_unused_1657_ = lean_ctor_get(v_r_1391_, 0);
lean_dec(v_unused_1657_);
v___x_1599_ = v_r_1391_;
v_isShared_1600_ = v_isSharedCheck_1652_;
goto v_resetjp_1598_;
}
else
{
lean_dec(v_r_1391_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1652_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v_size_1601_; lean_object* v_k_1602_; lean_object* v_v_1603_; lean_object* v_l_1604_; lean_object* v_r_1605_; lean_object* v_size_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; uint8_t v___x_1609_; 
v_size_1601_ = lean_ctor_get(v_l_1578_, 0);
v_k_1602_ = lean_ctor_get(v_l_1578_, 1);
v_v_1603_ = lean_ctor_get(v_l_1578_, 2);
v_l_1604_ = lean_ctor_get(v_l_1578_, 3);
v_r_1605_ = lean_ctor_get(v_l_1578_, 4);
v_size_1606_ = lean_ctor_get(v_r_1579_, 0);
v___x_1607_ = lean_unsigned_to_nat(2u);
v___x_1608_ = lean_nat_mul(v___x_1607_, v_size_1606_);
v___x_1609_ = lean_nat_dec_lt(v_size_1601_, v___x_1608_);
lean_dec(v___x_1608_);
if (v___x_1609_ == 0)
{
lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1637_; 
lean_inc(v_r_1605_);
lean_inc(v_l_1604_);
lean_inc(v_v_1603_);
lean_inc(v_k_1602_);
v_isSharedCheck_1637_ = !lean_is_exclusive(v_l_1578_);
if (v_isSharedCheck_1637_ == 0)
{
lean_object* v_unused_1638_; lean_object* v_unused_1639_; lean_object* v_unused_1640_; lean_object* v_unused_1641_; lean_object* v_unused_1642_; 
v_unused_1638_ = lean_ctor_get(v_l_1578_, 4);
lean_dec(v_unused_1638_);
v_unused_1639_ = lean_ctor_get(v_l_1578_, 3);
lean_dec(v_unused_1639_);
v_unused_1640_ = lean_ctor_get(v_l_1578_, 2);
lean_dec(v_unused_1640_);
v_unused_1641_ = lean_ctor_get(v_l_1578_, 1);
lean_dec(v_unused_1641_);
v_unused_1642_ = lean_ctor_get(v_l_1578_, 0);
lean_dec(v_unused_1642_);
v___x_1611_ = v_l_1578_;
v_isShared_1612_ = v_isSharedCheck_1637_;
goto v_resetjp_1610_;
}
else
{
lean_dec(v_l_1578_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1637_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1627_; 
v___x_1613_ = lean_nat_add(v___x_1580_, v_size_1589_);
v___x_1614_ = lean_nat_add(v___x_1613_, v_size_1575_);
lean_dec(v_size_1575_);
if (lean_obj_tag(v_l_1604_) == 0)
{
lean_object* v_size_1635_; 
v_size_1635_ = lean_ctor_get(v_l_1604_, 0);
lean_inc(v_size_1635_);
v___y_1627_ = v_size_1635_;
goto v___jp_1626_;
}
else
{
lean_object* v___x_1636_; 
v___x_1636_ = lean_unsigned_to_nat(0u);
v___y_1627_ = v___x_1636_;
goto v___jp_1626_;
}
v___jp_1615_:
{
lean_object* v___x_1619_; lean_object* v___x_1621_; 
v___x_1619_ = lean_nat_add(v___y_1616_, v___y_1618_);
lean_dec(v___y_1618_);
lean_dec(v___y_1616_);
if (v_isShared_1612_ == 0)
{
lean_ctor_set(v___x_1611_, 4, v_r_1579_);
lean_ctor_set(v___x_1611_, 3, v_r_1605_);
lean_ctor_set(v___x_1611_, 2, v_v_1577_);
lean_ctor_set(v___x_1611_, 1, v_k_1576_);
lean_ctor_set(v___x_1611_, 0, v___x_1619_);
v___x_1621_ = v___x_1611_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v___x_1619_);
lean_ctor_set(v_reuseFailAlloc_1625_, 1, v_k_1576_);
lean_ctor_set(v_reuseFailAlloc_1625_, 2, v_v_1577_);
lean_ctor_set(v_reuseFailAlloc_1625_, 3, v_r_1605_);
lean_ctor_set(v_reuseFailAlloc_1625_, 4, v_r_1579_);
v___x_1621_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
lean_object* v___x_1623_; 
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 4, v___x_1621_);
lean_ctor_set(v___x_1599_, 3, v___y_1617_);
lean_ctor_set(v___x_1599_, 2, v_v_1603_);
lean_ctor_set(v___x_1599_, 1, v_k_1602_);
lean_ctor_set(v___x_1599_, 0, v___x_1614_);
v___x_1623_ = v___x_1599_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1614_);
lean_ctor_set(v_reuseFailAlloc_1624_, 1, v_k_1602_);
lean_ctor_set(v_reuseFailAlloc_1624_, 2, v_v_1603_);
lean_ctor_set(v_reuseFailAlloc_1624_, 3, v___y_1617_);
lean_ctor_set(v_reuseFailAlloc_1624_, 4, v___x_1621_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
v___jp_1626_:
{
lean_object* v___x_1628_; lean_object* v___x_1630_; 
v___x_1628_ = lean_nat_add(v___x_1613_, v___y_1627_);
lean_dec(v___y_1627_);
lean_dec(v___x_1613_);
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 4, v_l_1604_);
lean_ctor_set(v___x_1583_, 3, v_tree_1586_);
lean_ctor_set(v___x_1583_, 2, v_v_1588_);
lean_ctor_set(v___x_1583_, 1, v_k_1587_);
lean_ctor_set(v___x_1583_, 0, v___x_1628_);
v___x_1630_ = v___x_1583_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v___x_1628_);
lean_ctor_set(v_reuseFailAlloc_1634_, 1, v_k_1587_);
lean_ctor_set(v_reuseFailAlloc_1634_, 2, v_v_1588_);
lean_ctor_set(v_reuseFailAlloc_1634_, 3, v_tree_1586_);
lean_ctor_set(v_reuseFailAlloc_1634_, 4, v_l_1604_);
v___x_1630_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
lean_object* v___x_1631_; 
v___x_1631_ = lean_nat_add(v___x_1580_, v_size_1606_);
if (lean_obj_tag(v_r_1605_) == 0)
{
lean_object* v_size_1632_; 
v_size_1632_ = lean_ctor_get(v_r_1605_, 0);
lean_inc(v_size_1632_);
v___y_1616_ = v___x_1631_;
v___y_1617_ = v___x_1630_;
v___y_1618_ = v_size_1632_;
goto v___jp_1615_;
}
else
{
lean_object* v___x_1633_; 
v___x_1633_ = lean_unsigned_to_nat(0u);
v___y_1616_ = v___x_1631_;
v___y_1617_ = v___x_1630_;
v___y_1618_ = v___x_1633_;
goto v___jp_1615_;
}
}
}
}
}
else
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1647_; 
v___x_1643_ = lean_nat_add(v___x_1580_, v_size_1589_);
v___x_1644_ = lean_nat_add(v___x_1643_, v_size_1575_);
lean_dec(v_size_1575_);
v___x_1645_ = lean_nat_add(v___x_1643_, v_size_1601_);
lean_dec(v___x_1643_);
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 4, v_l_1578_);
lean_ctor_set(v___x_1599_, 3, v_tree_1586_);
lean_ctor_set(v___x_1599_, 2, v_v_1588_);
lean_ctor_set(v___x_1599_, 1, v_k_1587_);
lean_ctor_set(v___x_1599_, 0, v___x_1645_);
v___x_1647_ = v___x_1599_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v___x_1645_);
lean_ctor_set(v_reuseFailAlloc_1651_, 1, v_k_1587_);
lean_ctor_set(v_reuseFailAlloc_1651_, 2, v_v_1588_);
lean_ctor_set(v_reuseFailAlloc_1651_, 3, v_tree_1586_);
lean_ctor_set(v_reuseFailAlloc_1651_, 4, v_l_1578_);
v___x_1647_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
lean_object* v___x_1649_; 
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 4, v_r_1579_);
lean_ctor_set(v___x_1583_, 3, v___x_1647_);
lean_ctor_set(v___x_1583_, 2, v_v_1577_);
lean_ctor_set(v___x_1583_, 1, v_k_1576_);
lean_ctor_set(v___x_1583_, 0, v___x_1644_);
v___x_1649_ = v___x_1583_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1644_);
lean_ctor_set(v_reuseFailAlloc_1650_, 1, v_k_1576_);
lean_ctor_set(v_reuseFailAlloc_1650_, 2, v_v_1577_);
lean_ctor_set(v_reuseFailAlloc_1650_, 3, v___x_1647_);
lean_ctor_set(v_reuseFailAlloc_1650_, 4, v_r_1579_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
}
}
else
{
lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1711_; 
lean_inc(v_r_1579_);
lean_inc(v_v_1577_);
lean_inc(v_k_1576_);
lean_inc(v_size_1575_);
v_isSharedCheck_1711_ = !lean_is_exclusive(v_r_1391_);
if (v_isSharedCheck_1711_ == 0)
{
lean_object* v_unused_1712_; lean_object* v_unused_1713_; lean_object* v_unused_1714_; lean_object* v_unused_1715_; lean_object* v_unused_1716_; 
v_unused_1712_ = lean_ctor_get(v_r_1391_, 4);
lean_dec(v_unused_1712_);
v_unused_1713_ = lean_ctor_get(v_r_1391_, 3);
lean_dec(v_unused_1713_);
v_unused_1714_ = lean_ctor_get(v_r_1391_, 2);
lean_dec(v_unused_1714_);
v_unused_1715_ = lean_ctor_get(v_r_1391_, 1);
lean_dec(v_unused_1715_);
v_unused_1716_ = lean_ctor_get(v_r_1391_, 0);
lean_dec(v_unused_1716_);
v___x_1659_ = v_r_1391_;
v_isShared_1660_ = v_isSharedCheck_1711_;
goto v_resetjp_1658_;
}
else
{
lean_dec(v_r_1391_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1711_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
if (lean_obj_tag(v_l_1578_) == 0)
{
if (lean_obj_tag(v_r_1579_) == 0)
{
lean_object* v_k_1661_; lean_object* v_v_1662_; lean_object* v_size_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1667_; 
v_k_1661_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_k_1661_);
v_v_1662_ = lean_ctor_get(v___x_1585_, 1);
lean_inc(v_v_1662_);
lean_dec_ref(v___x_1585_);
v_size_1663_ = lean_ctor_get(v_l_1578_, 0);
v___x_1664_ = lean_nat_add(v___x_1580_, v_size_1575_);
lean_dec(v_size_1575_);
v___x_1665_ = lean_nat_add(v___x_1580_, v_size_1663_);
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 4, v_l_1578_);
lean_ctor_set(v___x_1659_, 3, v_tree_1586_);
lean_ctor_set(v___x_1659_, 2, v_v_1662_);
lean_ctor_set(v___x_1659_, 1, v_k_1661_);
lean_ctor_set(v___x_1659_, 0, v___x_1665_);
v___x_1667_ = v___x_1659_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1665_);
lean_ctor_set(v_reuseFailAlloc_1671_, 1, v_k_1661_);
lean_ctor_set(v_reuseFailAlloc_1671_, 2, v_v_1662_);
lean_ctor_set(v_reuseFailAlloc_1671_, 3, v_tree_1586_);
lean_ctor_set(v_reuseFailAlloc_1671_, 4, v_l_1578_);
v___x_1667_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
lean_object* v___x_1669_; 
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 4, v_r_1579_);
lean_ctor_set(v___x_1583_, 3, v___x_1667_);
lean_ctor_set(v___x_1583_, 2, v_v_1577_);
lean_ctor_set(v___x_1583_, 1, v_k_1576_);
lean_ctor_set(v___x_1583_, 0, v___x_1664_);
v___x_1669_ = v___x_1583_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v___x_1664_);
lean_ctor_set(v_reuseFailAlloc_1670_, 1, v_k_1576_);
lean_ctor_set(v_reuseFailAlloc_1670_, 2, v_v_1577_);
lean_ctor_set(v_reuseFailAlloc_1670_, 3, v___x_1667_);
lean_ctor_set(v_reuseFailAlloc_1670_, 4, v_r_1579_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
else
{
lean_object* v_k_1672_; lean_object* v_v_1673_; lean_object* v_k_1674_; lean_object* v_v_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1689_; 
lean_dec(v_size_1575_);
v_k_1672_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_k_1672_);
v_v_1673_ = lean_ctor_get(v___x_1585_, 1);
lean_inc(v_v_1673_);
lean_dec_ref(v___x_1585_);
v_k_1674_ = lean_ctor_get(v_l_1578_, 1);
v_v_1675_ = lean_ctor_get(v_l_1578_, 2);
v_isSharedCheck_1689_ = !lean_is_exclusive(v_l_1578_);
if (v_isSharedCheck_1689_ == 0)
{
lean_object* v_unused_1690_; lean_object* v_unused_1691_; lean_object* v_unused_1692_; 
v_unused_1690_ = lean_ctor_get(v_l_1578_, 4);
lean_dec(v_unused_1690_);
v_unused_1691_ = lean_ctor_get(v_l_1578_, 3);
lean_dec(v_unused_1691_);
v_unused_1692_ = lean_ctor_get(v_l_1578_, 0);
lean_dec(v_unused_1692_);
v___x_1677_ = v_l_1578_;
v_isShared_1678_ = v_isSharedCheck_1689_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_v_1675_);
lean_inc(v_k_1674_);
lean_dec(v_l_1578_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1689_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1679_; lean_object* v___x_1681_; 
v___x_1679_ = lean_unsigned_to_nat(3u);
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 4, v_r_1579_);
lean_ctor_set(v___x_1677_, 3, v_r_1579_);
lean_ctor_set(v___x_1677_, 2, v_v_1673_);
lean_ctor_set(v___x_1677_, 1, v_k_1672_);
lean_ctor_set(v___x_1677_, 0, v___x_1580_);
v___x_1681_ = v___x_1677_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1580_);
lean_ctor_set(v_reuseFailAlloc_1688_, 1, v_k_1672_);
lean_ctor_set(v_reuseFailAlloc_1688_, 2, v_v_1673_);
lean_ctor_set(v_reuseFailAlloc_1688_, 3, v_r_1579_);
lean_ctor_set(v_reuseFailAlloc_1688_, 4, v_r_1579_);
v___x_1681_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
lean_object* v___x_1683_; 
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 3, v_r_1579_);
lean_ctor_set(v___x_1659_, 0, v___x_1580_);
v___x_1683_ = v___x_1659_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1580_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_k_1576_);
lean_ctor_set(v_reuseFailAlloc_1687_, 2, v_v_1577_);
lean_ctor_set(v_reuseFailAlloc_1687_, 3, v_r_1579_);
lean_ctor_set(v_reuseFailAlloc_1687_, 4, v_r_1579_);
v___x_1683_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
lean_object* v___x_1685_; 
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 4, v___x_1683_);
lean_ctor_set(v___x_1583_, 3, v___x_1681_);
lean_ctor_set(v___x_1583_, 2, v_v_1675_);
lean_ctor_set(v___x_1583_, 1, v_k_1674_);
lean_ctor_set(v___x_1583_, 0, v___x_1679_);
v___x_1685_ = v___x_1583_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1679_);
lean_ctor_set(v_reuseFailAlloc_1686_, 1, v_k_1674_);
lean_ctor_set(v_reuseFailAlloc_1686_, 2, v_v_1675_);
lean_ctor_set(v_reuseFailAlloc_1686_, 3, v___x_1681_);
lean_ctor_set(v_reuseFailAlloc_1686_, 4, v___x_1683_);
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
}
}
else
{
if (lean_obj_tag(v_r_1579_) == 0)
{
lean_object* v_k_1693_; lean_object* v_v_1694_; lean_object* v___x_1695_; lean_object* v___x_1697_; 
lean_dec(v_size_1575_);
v_k_1693_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_k_1693_);
v_v_1694_ = lean_ctor_get(v___x_1585_, 1);
lean_inc(v_v_1694_);
lean_dec_ref(v___x_1585_);
v___x_1695_ = lean_unsigned_to_nat(3u);
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 4, v_l_1578_);
lean_ctor_set(v___x_1659_, 2, v_v_1694_);
lean_ctor_set(v___x_1659_, 1, v_k_1693_);
lean_ctor_set(v___x_1659_, 0, v___x_1580_);
v___x_1697_ = v___x_1659_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1580_);
lean_ctor_set(v_reuseFailAlloc_1701_, 1, v_k_1693_);
lean_ctor_set(v_reuseFailAlloc_1701_, 2, v_v_1694_);
lean_ctor_set(v_reuseFailAlloc_1701_, 3, v_l_1578_);
lean_ctor_set(v_reuseFailAlloc_1701_, 4, v_l_1578_);
v___x_1697_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
lean_object* v___x_1699_; 
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 4, v_r_1579_);
lean_ctor_set(v___x_1583_, 3, v___x_1697_);
lean_ctor_set(v___x_1583_, 2, v_v_1577_);
lean_ctor_set(v___x_1583_, 1, v_k_1576_);
lean_ctor_set(v___x_1583_, 0, v___x_1695_);
v___x_1699_ = v___x_1583_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v___x_1695_);
lean_ctor_set(v_reuseFailAlloc_1700_, 1, v_k_1576_);
lean_ctor_set(v_reuseFailAlloc_1700_, 2, v_v_1577_);
lean_ctor_set(v_reuseFailAlloc_1700_, 3, v___x_1697_);
lean_ctor_set(v_reuseFailAlloc_1700_, 4, v_r_1579_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
else
{
lean_object* v_k_1702_; lean_object* v_v_1703_; lean_object* v___x_1705_; 
v_k_1702_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_k_1702_);
v_v_1703_ = lean_ctor_get(v___x_1585_, 1);
lean_inc(v_v_1703_);
lean_dec_ref(v___x_1585_);
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 3, v_r_1579_);
v___x_1705_ = v___x_1659_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_size_1575_);
lean_ctor_set(v_reuseFailAlloc_1710_, 1, v_k_1576_);
lean_ctor_set(v_reuseFailAlloc_1710_, 2, v_v_1577_);
lean_ctor_set(v_reuseFailAlloc_1710_, 3, v_r_1579_);
lean_ctor_set(v_reuseFailAlloc_1710_, 4, v_r_1579_);
v___x_1705_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
lean_object* v___x_1706_; lean_object* v___x_1708_; 
v___x_1706_ = lean_unsigned_to_nat(2u);
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 4, v___x_1705_);
lean_ctor_set(v___x_1583_, 3, v_r_1579_);
lean_ctor_set(v___x_1583_, 2, v_v_1703_);
lean_ctor_set(v___x_1583_, 1, v_k_1702_);
lean_ctor_set(v___x_1583_, 0, v___x_1706_);
v___x_1708_ = v___x_1583_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v___x_1706_);
lean_ctor_set(v_reuseFailAlloc_1709_, 1, v_k_1702_);
lean_ctor_set(v_reuseFailAlloc_1709_, 2, v_v_1703_);
lean_ctor_set(v_reuseFailAlloc_1709_, 3, v_r_1579_);
lean_ctor_set(v_reuseFailAlloc_1709_, 4, v___x_1705_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
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
lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1875_; 
lean_inc(v_r_1579_);
lean_inc(v_v_1577_);
lean_inc(v_k_1576_);
v_isSharedCheck_1875_ = !lean_is_exclusive(v_r_1391_);
if (v_isSharedCheck_1875_ == 0)
{
lean_object* v_unused_1876_; lean_object* v_unused_1877_; lean_object* v_unused_1878_; lean_object* v_unused_1879_; lean_object* v_unused_1880_; 
v_unused_1876_ = lean_ctor_get(v_r_1391_, 4);
lean_dec(v_unused_1876_);
v_unused_1877_ = lean_ctor_get(v_r_1391_, 3);
lean_dec(v_unused_1877_);
v_unused_1878_ = lean_ctor_get(v_r_1391_, 2);
lean_dec(v_unused_1878_);
v_unused_1879_ = lean_ctor_get(v_r_1391_, 1);
lean_dec(v_unused_1879_);
v_unused_1880_ = lean_ctor_get(v_r_1391_, 0);
lean_dec(v_unused_1880_);
v___x_1724_ = v_r_1391_;
v_isShared_1725_ = v_isSharedCheck_1875_;
goto v_resetjp_1723_;
}
else
{
lean_dec(v_r_1391_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1875_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1726_; lean_object* v_tree_1727_; 
v___x_1726_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_1576_, v_v_1577_, v_l_1578_, v_r_1579_);
v_tree_1727_ = lean_ctor_get(v___x_1726_, 2);
lean_inc(v_tree_1727_);
if (lean_obj_tag(v_tree_1727_) == 0)
{
lean_object* v_k_1728_; lean_object* v_v_1729_; lean_object* v_size_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; uint8_t v___x_1733_; 
v_k_1728_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_k_1728_);
v_v_1729_ = lean_ctor_get(v___x_1726_, 1);
lean_inc(v_v_1729_);
lean_dec_ref(v___x_1726_);
v_size_1730_ = lean_ctor_get(v_tree_1727_, 0);
v___x_1731_ = lean_unsigned_to_nat(3u);
v___x_1732_ = lean_nat_mul(v___x_1731_, v_size_1730_);
v___x_1733_ = lean_nat_dec_lt(v___x_1732_, v_size_1570_);
lean_dec(v___x_1732_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1737_; 
lean_dec(v_r_1574_);
v___x_1734_ = lean_nat_add(v___x_1580_, v_size_1570_);
v___x_1735_ = lean_nat_add(v___x_1734_, v_size_1730_);
lean_dec(v___x_1734_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 4, v_tree_1727_);
lean_ctor_set(v___x_1724_, 3, v_l_1390_);
lean_ctor_set(v___x_1724_, 2, v_v_1729_);
lean_ctor_set(v___x_1724_, 1, v_k_1728_);
lean_ctor_set(v___x_1724_, 0, v___x_1735_);
v___x_1737_ = v___x_1724_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v___x_1735_);
lean_ctor_set(v_reuseFailAlloc_1738_, 1, v_k_1728_);
lean_ctor_set(v_reuseFailAlloc_1738_, 2, v_v_1729_);
lean_ctor_set(v_reuseFailAlloc_1738_, 3, v_l_1390_);
lean_ctor_set(v_reuseFailAlloc_1738_, 4, v_tree_1727_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
else
{
lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1804_; 
lean_inc(v_l_1573_);
lean_inc(v_v_1572_);
lean_inc(v_k_1571_);
lean_inc(v_size_1570_);
v_isSharedCheck_1804_ = !lean_is_exclusive(v_l_1390_);
if (v_isSharedCheck_1804_ == 0)
{
lean_object* v_unused_1805_; lean_object* v_unused_1806_; lean_object* v_unused_1807_; lean_object* v_unused_1808_; lean_object* v_unused_1809_; 
v_unused_1805_ = lean_ctor_get(v_l_1390_, 4);
lean_dec(v_unused_1805_);
v_unused_1806_ = lean_ctor_get(v_l_1390_, 3);
lean_dec(v_unused_1806_);
v_unused_1807_ = lean_ctor_get(v_l_1390_, 2);
lean_dec(v_unused_1807_);
v_unused_1808_ = lean_ctor_get(v_l_1390_, 1);
lean_dec(v_unused_1808_);
v_unused_1809_ = lean_ctor_get(v_l_1390_, 0);
lean_dec(v_unused_1809_);
v___x_1740_ = v_l_1390_;
v_isShared_1741_ = v_isSharedCheck_1804_;
goto v_resetjp_1739_;
}
else
{
lean_dec(v_l_1390_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1804_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v_size_1742_; lean_object* v_size_1743_; lean_object* v_k_1744_; lean_object* v_v_1745_; lean_object* v_l_1746_; lean_object* v_r_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; uint8_t v___x_1750_; 
v_size_1742_ = lean_ctor_get(v_l_1573_, 0);
v_size_1743_ = lean_ctor_get(v_r_1574_, 0);
v_k_1744_ = lean_ctor_get(v_r_1574_, 1);
v_v_1745_ = lean_ctor_get(v_r_1574_, 2);
v_l_1746_ = lean_ctor_get(v_r_1574_, 3);
v_r_1747_ = lean_ctor_get(v_r_1574_, 4);
v___x_1748_ = lean_unsigned_to_nat(2u);
v___x_1749_ = lean_nat_mul(v___x_1748_, v_size_1742_);
v___x_1750_ = lean_nat_dec_lt(v_size_1743_, v___x_1749_);
lean_dec(v___x_1749_);
if (v___x_1750_ == 0)
{
lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1788_; 
lean_inc(v_r_1747_);
lean_inc(v_l_1746_);
lean_inc(v_v_1745_);
lean_inc(v_k_1744_);
lean_del_object(v___x_1740_);
v_isSharedCheck_1788_ = !lean_is_exclusive(v_r_1574_);
if (v_isSharedCheck_1788_ == 0)
{
lean_object* v_unused_1789_; lean_object* v_unused_1790_; lean_object* v_unused_1791_; lean_object* v_unused_1792_; lean_object* v_unused_1793_; 
v_unused_1789_ = lean_ctor_get(v_r_1574_, 4);
lean_dec(v_unused_1789_);
v_unused_1790_ = lean_ctor_get(v_r_1574_, 3);
lean_dec(v_unused_1790_);
v_unused_1791_ = lean_ctor_get(v_r_1574_, 2);
lean_dec(v_unused_1791_);
v_unused_1792_ = lean_ctor_get(v_r_1574_, 1);
lean_dec(v_unused_1792_);
v_unused_1793_ = lean_ctor_get(v_r_1574_, 0);
lean_dec(v_unused_1793_);
v___x_1752_ = v_r_1574_;
v_isShared_1753_ = v_isSharedCheck_1788_;
goto v_resetjp_1751_;
}
else
{
lean_dec(v_r_1574_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1788_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___y_1757_; lean_object* v___y_1758_; lean_object* v___y_1759_; lean_object* v___x_1776_; lean_object* v___y_1778_; 
v___x_1754_ = lean_nat_add(v___x_1580_, v_size_1570_);
lean_dec(v_size_1570_);
v___x_1755_ = lean_nat_add(v___x_1754_, v_size_1730_);
lean_dec(v___x_1754_);
v___x_1776_ = lean_nat_add(v___x_1580_, v_size_1742_);
if (lean_obj_tag(v_l_1746_) == 0)
{
lean_object* v_size_1786_; 
v_size_1786_ = lean_ctor_get(v_l_1746_, 0);
lean_inc(v_size_1786_);
v___y_1778_ = v_size_1786_;
goto v___jp_1777_;
}
else
{
lean_object* v___x_1787_; 
v___x_1787_ = lean_unsigned_to_nat(0u);
v___y_1778_ = v___x_1787_;
goto v___jp_1777_;
}
v___jp_1756_:
{
lean_object* v___x_1760_; lean_object* v___x_1762_; 
v___x_1760_ = lean_nat_add(v___y_1758_, v___y_1759_);
lean_dec(v___y_1759_);
lean_dec(v___y_1758_);
lean_inc_ref(v_tree_1727_);
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 4, v_tree_1727_);
lean_ctor_set(v___x_1752_, 3, v_r_1747_);
lean_ctor_set(v___x_1752_, 2, v_v_1729_);
lean_ctor_set(v___x_1752_, 1, v_k_1728_);
lean_ctor_set(v___x_1752_, 0, v___x_1760_);
v___x_1762_ = v___x_1752_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v___x_1760_);
lean_ctor_set(v_reuseFailAlloc_1775_, 1, v_k_1728_);
lean_ctor_set(v_reuseFailAlloc_1775_, 2, v_v_1729_);
lean_ctor_set(v_reuseFailAlloc_1775_, 3, v_r_1747_);
lean_ctor_set(v_reuseFailAlloc_1775_, 4, v_tree_1727_);
v___x_1762_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
v_isSharedCheck_1769_ = !lean_is_exclusive(v_tree_1727_);
if (v_isSharedCheck_1769_ == 0)
{
lean_object* v_unused_1770_; lean_object* v_unused_1771_; lean_object* v_unused_1772_; lean_object* v_unused_1773_; lean_object* v_unused_1774_; 
v_unused_1770_ = lean_ctor_get(v_tree_1727_, 4);
lean_dec(v_unused_1770_);
v_unused_1771_ = lean_ctor_get(v_tree_1727_, 3);
lean_dec(v_unused_1771_);
v_unused_1772_ = lean_ctor_get(v_tree_1727_, 2);
lean_dec(v_unused_1772_);
v_unused_1773_ = lean_ctor_get(v_tree_1727_, 1);
lean_dec(v_unused_1773_);
v_unused_1774_ = lean_ctor_get(v_tree_1727_, 0);
lean_dec(v_unused_1774_);
v___x_1764_ = v_tree_1727_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_dec(v_tree_1727_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 4, v___x_1762_);
lean_ctor_set(v___x_1764_, 3, v___y_1757_);
lean_ctor_set(v___x_1764_, 2, v_v_1745_);
lean_ctor_set(v___x_1764_, 1, v_k_1744_);
lean_ctor_set(v___x_1764_, 0, v___x_1755_);
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1755_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v_k_1744_);
lean_ctor_set(v_reuseFailAlloc_1768_, 2, v_v_1745_);
lean_ctor_set(v_reuseFailAlloc_1768_, 3, v___y_1757_);
lean_ctor_set(v_reuseFailAlloc_1768_, 4, v___x_1762_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
v___jp_1777_:
{
lean_object* v___x_1779_; lean_object* v___x_1781_; 
v___x_1779_ = lean_nat_add(v___x_1776_, v___y_1778_);
lean_dec(v___y_1778_);
lean_dec(v___x_1776_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 4, v_l_1746_);
lean_ctor_set(v___x_1724_, 3, v_l_1573_);
lean_ctor_set(v___x_1724_, 2, v_v_1572_);
lean_ctor_set(v___x_1724_, 1, v_k_1571_);
lean_ctor_set(v___x_1724_, 0, v___x_1779_);
v___x_1781_ = v___x_1724_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1779_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v_k_1571_);
lean_ctor_set(v_reuseFailAlloc_1785_, 2, v_v_1572_);
lean_ctor_set(v_reuseFailAlloc_1785_, 3, v_l_1573_);
lean_ctor_set(v_reuseFailAlloc_1785_, 4, v_l_1746_);
v___x_1781_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
lean_object* v___x_1782_; 
v___x_1782_ = lean_nat_add(v___x_1580_, v_size_1730_);
if (lean_obj_tag(v_r_1747_) == 0)
{
lean_object* v_size_1783_; 
v_size_1783_ = lean_ctor_get(v_r_1747_, 0);
lean_inc(v_size_1783_);
v___y_1757_ = v___x_1781_;
v___y_1758_ = v___x_1782_;
v___y_1759_ = v_size_1783_;
goto v___jp_1756_;
}
else
{
lean_object* v___x_1784_; 
v___x_1784_ = lean_unsigned_to_nat(0u);
v___y_1757_ = v___x_1781_;
v___y_1758_ = v___x_1782_;
v___y_1759_ = v___x_1784_;
goto v___jp_1756_;
}
}
}
}
}
else
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1799_; 
v___x_1794_ = lean_nat_add(v___x_1580_, v_size_1570_);
lean_dec(v_size_1570_);
v___x_1795_ = lean_nat_add(v___x_1794_, v_size_1730_);
lean_dec(v___x_1794_);
v___x_1796_ = lean_nat_add(v___x_1580_, v_size_1730_);
v___x_1797_ = lean_nat_add(v___x_1796_, v_size_1743_);
lean_dec(v___x_1796_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 4, v_tree_1727_);
lean_ctor_set(v___x_1724_, 3, v_r_1574_);
lean_ctor_set(v___x_1724_, 2, v_v_1729_);
lean_ctor_set(v___x_1724_, 1, v_k_1728_);
lean_ctor_set(v___x_1724_, 0, v___x_1797_);
v___x_1799_ = v___x_1724_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v___x_1797_);
lean_ctor_set(v_reuseFailAlloc_1803_, 1, v_k_1728_);
lean_ctor_set(v_reuseFailAlloc_1803_, 2, v_v_1729_);
lean_ctor_set(v_reuseFailAlloc_1803_, 3, v_r_1574_);
lean_ctor_set(v_reuseFailAlloc_1803_, 4, v_tree_1727_);
v___x_1799_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
lean_object* v___x_1801_; 
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 4, v___x_1799_);
lean_ctor_set(v___x_1740_, 0, v___x_1795_);
v___x_1801_ = v___x_1740_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v___x_1795_);
lean_ctor_set(v_reuseFailAlloc_1802_, 1, v_k_1571_);
lean_ctor_set(v_reuseFailAlloc_1802_, 2, v_v_1572_);
lean_ctor_set(v_reuseFailAlloc_1802_, 3, v_l_1573_);
lean_ctor_set(v_reuseFailAlloc_1802_, 4, v___x_1799_);
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
}
else
{
if (lean_obj_tag(v_l_1573_) == 0)
{
lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1833_; 
lean_inc_ref(v_l_1573_);
lean_inc(v_v_1572_);
lean_inc(v_k_1571_);
lean_inc(v_size_1570_);
v_isSharedCheck_1833_ = !lean_is_exclusive(v_l_1390_);
if (v_isSharedCheck_1833_ == 0)
{
lean_object* v_unused_1834_; lean_object* v_unused_1835_; lean_object* v_unused_1836_; lean_object* v_unused_1837_; lean_object* v_unused_1838_; 
v_unused_1834_ = lean_ctor_get(v_l_1390_, 4);
lean_dec(v_unused_1834_);
v_unused_1835_ = lean_ctor_get(v_l_1390_, 3);
lean_dec(v_unused_1835_);
v_unused_1836_ = lean_ctor_get(v_l_1390_, 2);
lean_dec(v_unused_1836_);
v_unused_1837_ = lean_ctor_get(v_l_1390_, 1);
lean_dec(v_unused_1837_);
v_unused_1838_ = lean_ctor_get(v_l_1390_, 0);
lean_dec(v_unused_1838_);
v___x_1811_ = v_l_1390_;
v_isShared_1812_ = v_isSharedCheck_1833_;
goto v_resetjp_1810_;
}
else
{
lean_dec(v_l_1390_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1833_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
if (lean_obj_tag(v_r_1574_) == 0)
{
lean_object* v_k_1813_; lean_object* v_v_1814_; lean_object* v_size_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1819_; 
v_k_1813_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_k_1813_);
v_v_1814_ = lean_ctor_get(v___x_1726_, 1);
lean_inc(v_v_1814_);
lean_dec_ref(v___x_1726_);
v_size_1815_ = lean_ctor_get(v_r_1574_, 0);
v___x_1816_ = lean_nat_add(v___x_1580_, v_size_1570_);
lean_dec(v_size_1570_);
v___x_1817_ = lean_nat_add(v___x_1580_, v_size_1815_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 4, v_tree_1727_);
lean_ctor_set(v___x_1724_, 3, v_r_1574_);
lean_ctor_set(v___x_1724_, 2, v_v_1814_);
lean_ctor_set(v___x_1724_, 1, v_k_1813_);
lean_ctor_set(v___x_1724_, 0, v___x_1817_);
v___x_1819_ = v___x_1724_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v___x_1817_);
lean_ctor_set(v_reuseFailAlloc_1823_, 1, v_k_1813_);
lean_ctor_set(v_reuseFailAlloc_1823_, 2, v_v_1814_);
lean_ctor_set(v_reuseFailAlloc_1823_, 3, v_r_1574_);
lean_ctor_set(v_reuseFailAlloc_1823_, 4, v_tree_1727_);
v___x_1819_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
lean_object* v___x_1821_; 
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 4, v___x_1819_);
lean_ctor_set(v___x_1811_, 0, v___x_1816_);
v___x_1821_ = v___x_1811_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1816_);
lean_ctor_set(v_reuseFailAlloc_1822_, 1, v_k_1571_);
lean_ctor_set(v_reuseFailAlloc_1822_, 2, v_v_1572_);
lean_ctor_set(v_reuseFailAlloc_1822_, 3, v_l_1573_);
lean_ctor_set(v_reuseFailAlloc_1822_, 4, v___x_1819_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
else
{
lean_object* v_k_1824_; lean_object* v_v_1825_; lean_object* v___x_1826_; lean_object* v___x_1828_; 
lean_dec(v_size_1570_);
v_k_1824_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_k_1824_);
v_v_1825_ = lean_ctor_get(v___x_1726_, 1);
lean_inc(v_v_1825_);
lean_dec_ref(v___x_1726_);
v___x_1826_ = lean_unsigned_to_nat(3u);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 4, v_r_1574_);
lean_ctor_set(v___x_1724_, 3, v_r_1574_);
lean_ctor_set(v___x_1724_, 2, v_v_1825_);
lean_ctor_set(v___x_1724_, 1, v_k_1824_);
lean_ctor_set(v___x_1724_, 0, v___x_1580_);
v___x_1828_ = v___x_1724_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1580_);
lean_ctor_set(v_reuseFailAlloc_1832_, 1, v_k_1824_);
lean_ctor_set(v_reuseFailAlloc_1832_, 2, v_v_1825_);
lean_ctor_set(v_reuseFailAlloc_1832_, 3, v_r_1574_);
lean_ctor_set(v_reuseFailAlloc_1832_, 4, v_r_1574_);
v___x_1828_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
lean_object* v___x_1830_; 
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 4, v___x_1828_);
lean_ctor_set(v___x_1811_, 0, v___x_1826_);
v___x_1830_ = v___x_1811_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v___x_1826_);
lean_ctor_set(v_reuseFailAlloc_1831_, 1, v_k_1571_);
lean_ctor_set(v_reuseFailAlloc_1831_, 2, v_v_1572_);
lean_ctor_set(v_reuseFailAlloc_1831_, 3, v_l_1573_);
lean_ctor_set(v_reuseFailAlloc_1831_, 4, v___x_1828_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1574_) == 0)
{
lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1863_; 
lean_inc(v_l_1573_);
lean_inc(v_v_1572_);
lean_inc(v_k_1571_);
v_isSharedCheck_1863_ = !lean_is_exclusive(v_l_1390_);
if (v_isSharedCheck_1863_ == 0)
{
lean_object* v_unused_1864_; lean_object* v_unused_1865_; lean_object* v_unused_1866_; lean_object* v_unused_1867_; lean_object* v_unused_1868_; 
v_unused_1864_ = lean_ctor_get(v_l_1390_, 4);
lean_dec(v_unused_1864_);
v_unused_1865_ = lean_ctor_get(v_l_1390_, 3);
lean_dec(v_unused_1865_);
v_unused_1866_ = lean_ctor_get(v_l_1390_, 2);
lean_dec(v_unused_1866_);
v_unused_1867_ = lean_ctor_get(v_l_1390_, 1);
lean_dec(v_unused_1867_);
v_unused_1868_ = lean_ctor_get(v_l_1390_, 0);
lean_dec(v_unused_1868_);
v___x_1840_ = v_l_1390_;
v_isShared_1841_ = v_isSharedCheck_1863_;
goto v_resetjp_1839_;
}
else
{
lean_dec(v_l_1390_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1863_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v_k_1842_; lean_object* v_v_1843_; lean_object* v_k_1844_; lean_object* v_v_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1859_; 
v_k_1842_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_k_1842_);
v_v_1843_ = lean_ctor_get(v___x_1726_, 1);
lean_inc(v_v_1843_);
lean_dec_ref(v___x_1726_);
v_k_1844_ = lean_ctor_get(v_r_1574_, 1);
v_v_1845_ = lean_ctor_get(v_r_1574_, 2);
v_isSharedCheck_1859_ = !lean_is_exclusive(v_r_1574_);
if (v_isSharedCheck_1859_ == 0)
{
lean_object* v_unused_1860_; lean_object* v_unused_1861_; lean_object* v_unused_1862_; 
v_unused_1860_ = lean_ctor_get(v_r_1574_, 4);
lean_dec(v_unused_1860_);
v_unused_1861_ = lean_ctor_get(v_r_1574_, 3);
lean_dec(v_unused_1861_);
v_unused_1862_ = lean_ctor_get(v_r_1574_, 0);
lean_dec(v_unused_1862_);
v___x_1847_ = v_r_1574_;
v_isShared_1848_ = v_isSharedCheck_1859_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_v_1845_);
lean_inc(v_k_1844_);
lean_dec(v_r_1574_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1859_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1849_; lean_object* v___x_1851_; 
v___x_1849_ = lean_unsigned_to_nat(3u);
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 4, v_l_1573_);
lean_ctor_set(v___x_1847_, 3, v_l_1573_);
lean_ctor_set(v___x_1847_, 2, v_v_1572_);
lean_ctor_set(v___x_1847_, 1, v_k_1571_);
lean_ctor_set(v___x_1847_, 0, v___x_1580_);
v___x_1851_ = v___x_1847_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1580_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v_k_1571_);
lean_ctor_set(v_reuseFailAlloc_1858_, 2, v_v_1572_);
lean_ctor_set(v_reuseFailAlloc_1858_, 3, v_l_1573_);
lean_ctor_set(v_reuseFailAlloc_1858_, 4, v_l_1573_);
v___x_1851_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
lean_object* v___x_1853_; 
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 4, v_l_1573_);
lean_ctor_set(v___x_1724_, 3, v_l_1573_);
lean_ctor_set(v___x_1724_, 2, v_v_1843_);
lean_ctor_set(v___x_1724_, 1, v_k_1842_);
lean_ctor_set(v___x_1724_, 0, v___x_1580_);
v___x_1853_ = v___x_1724_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1580_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v_k_1842_);
lean_ctor_set(v_reuseFailAlloc_1857_, 2, v_v_1843_);
lean_ctor_set(v_reuseFailAlloc_1857_, 3, v_l_1573_);
lean_ctor_set(v_reuseFailAlloc_1857_, 4, v_l_1573_);
v___x_1853_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
lean_object* v___x_1855_; 
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 4, v___x_1853_);
lean_ctor_set(v___x_1840_, 3, v___x_1851_);
lean_ctor_set(v___x_1840_, 2, v_v_1845_);
lean_ctor_set(v___x_1840_, 1, v_k_1844_);
lean_ctor_set(v___x_1840_, 0, v___x_1849_);
v___x_1855_ = v___x_1840_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1849_);
lean_ctor_set(v_reuseFailAlloc_1856_, 1, v_k_1844_);
lean_ctor_set(v_reuseFailAlloc_1856_, 2, v_v_1845_);
lean_ctor_set(v_reuseFailAlloc_1856_, 3, v___x_1851_);
lean_ctor_set(v_reuseFailAlloc_1856_, 4, v___x_1853_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
}
}
}
else
{
lean_object* v_k_1869_; lean_object* v_v_1870_; lean_object* v___x_1871_; lean_object* v___x_1873_; 
v_k_1869_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_k_1869_);
v_v_1870_ = lean_ctor_get(v___x_1726_, 1);
lean_inc(v_v_1870_);
lean_dec_ref(v___x_1726_);
v___x_1871_ = lean_unsigned_to_nat(2u);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 4, v_r_1574_);
lean_ctor_set(v___x_1724_, 3, v_l_1390_);
lean_ctor_set(v___x_1724_, 2, v_v_1870_);
lean_ctor_set(v___x_1724_, 1, v_k_1869_);
lean_ctor_set(v___x_1724_, 0, v___x_1871_);
v___x_1873_ = v___x_1724_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v___x_1871_);
lean_ctor_set(v_reuseFailAlloc_1874_, 1, v_k_1869_);
lean_ctor_set(v_reuseFailAlloc_1874_, 2, v_v_1870_);
lean_ctor_set(v_reuseFailAlloc_1874_, 3, v_l_1390_);
lean_ctor_set(v_reuseFailAlloc_1874_, 4, v_r_1574_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
}
}
}
}
else
{
return v_l_1390_;
}
}
else
{
return v_r_1391_;
}
}
default: 
{
lean_object* v_impl_1881_; lean_object* v___x_1882_; 
v_impl_1881_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_1386_, v_r_1391_);
v___x_1882_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1881_) == 0)
{
if (lean_obj_tag(v_l_1390_) == 0)
{
lean_object* v_size_1883_; lean_object* v_size_1884_; lean_object* v_k_1885_; lean_object* v_v_1886_; lean_object* v_l_1887_; lean_object* v_r_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; uint8_t v___x_1891_; 
v_size_1883_ = lean_ctor_get(v_impl_1881_, 0);
lean_inc(v_size_1883_);
v_size_1884_ = lean_ctor_get(v_l_1390_, 0);
v_k_1885_ = lean_ctor_get(v_l_1390_, 1);
v_v_1886_ = lean_ctor_get(v_l_1390_, 2);
v_l_1887_ = lean_ctor_get(v_l_1390_, 3);
v_r_1888_ = lean_ctor_get(v_l_1390_, 4);
lean_inc(v_r_1888_);
v___x_1889_ = lean_unsigned_to_nat(3u);
v___x_1890_ = lean_nat_mul(v___x_1889_, v_size_1883_);
v___x_1891_ = lean_nat_dec_lt(v___x_1890_, v_size_1884_);
lean_dec(v___x_1890_);
if (v___x_1891_ == 0)
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1895_; 
lean_dec(v_r_1888_);
v___x_1892_ = lean_nat_add(v___x_1882_, v_size_1884_);
v___x_1893_ = lean_nat_add(v___x_1892_, v_size_1883_);
lean_dec(v_size_1883_);
lean_dec(v___x_1892_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 4, v_impl_1881_);
lean_ctor_set(v___x_1393_, 0, v___x_1893_);
v___x_1895_ = v___x_1393_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1893_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v_k_1388_);
lean_ctor_set(v_reuseFailAlloc_1896_, 2, v_v_1389_);
lean_ctor_set(v_reuseFailAlloc_1896_, 3, v_l_1390_);
lean_ctor_set(v_reuseFailAlloc_1896_, 4, v_impl_1881_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
else
{
lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1962_; 
lean_inc(v_l_1887_);
lean_inc(v_v_1886_);
lean_inc(v_k_1885_);
lean_inc(v_size_1884_);
v_isSharedCheck_1962_ = !lean_is_exclusive(v_l_1390_);
if (v_isSharedCheck_1962_ == 0)
{
lean_object* v_unused_1963_; lean_object* v_unused_1964_; lean_object* v_unused_1965_; lean_object* v_unused_1966_; lean_object* v_unused_1967_; 
v_unused_1963_ = lean_ctor_get(v_l_1390_, 4);
lean_dec(v_unused_1963_);
v_unused_1964_ = lean_ctor_get(v_l_1390_, 3);
lean_dec(v_unused_1964_);
v_unused_1965_ = lean_ctor_get(v_l_1390_, 2);
lean_dec(v_unused_1965_);
v_unused_1966_ = lean_ctor_get(v_l_1390_, 1);
lean_dec(v_unused_1966_);
v_unused_1967_ = lean_ctor_get(v_l_1390_, 0);
lean_dec(v_unused_1967_);
v___x_1898_ = v_l_1390_;
v_isShared_1899_ = v_isSharedCheck_1962_;
goto v_resetjp_1897_;
}
else
{
lean_dec(v_l_1390_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1962_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v_size_1900_; lean_object* v_size_1901_; lean_object* v_k_1902_; lean_object* v_v_1903_; lean_object* v_l_1904_; lean_object* v_r_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; uint8_t v___x_1908_; 
v_size_1900_ = lean_ctor_get(v_l_1887_, 0);
v_size_1901_ = lean_ctor_get(v_r_1888_, 0);
v_k_1902_ = lean_ctor_get(v_r_1888_, 1);
v_v_1903_ = lean_ctor_get(v_r_1888_, 2);
v_l_1904_ = lean_ctor_get(v_r_1888_, 3);
v_r_1905_ = lean_ctor_get(v_r_1888_, 4);
v___x_1906_ = lean_unsigned_to_nat(2u);
v___x_1907_ = lean_nat_mul(v___x_1906_, v_size_1900_);
v___x_1908_ = lean_nat_dec_lt(v_size_1901_, v___x_1907_);
lean_dec(v___x_1907_);
if (v___x_1908_ == 0)
{
lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1937_; 
lean_inc(v_r_1905_);
lean_inc(v_l_1904_);
lean_inc(v_v_1903_);
lean_inc(v_k_1902_);
v_isSharedCheck_1937_ = !lean_is_exclusive(v_r_1888_);
if (v_isSharedCheck_1937_ == 0)
{
lean_object* v_unused_1938_; lean_object* v_unused_1939_; lean_object* v_unused_1940_; lean_object* v_unused_1941_; lean_object* v_unused_1942_; 
v_unused_1938_ = lean_ctor_get(v_r_1888_, 4);
lean_dec(v_unused_1938_);
v_unused_1939_ = lean_ctor_get(v_r_1888_, 3);
lean_dec(v_unused_1939_);
v_unused_1940_ = lean_ctor_get(v_r_1888_, 2);
lean_dec(v_unused_1940_);
v_unused_1941_ = lean_ctor_get(v_r_1888_, 1);
lean_dec(v_unused_1941_);
v_unused_1942_ = lean_ctor_get(v_r_1888_, 0);
lean_dec(v_unused_1942_);
v___x_1910_ = v_r_1888_;
v_isShared_1911_ = v_isSharedCheck_1937_;
goto v_resetjp_1909_;
}
else
{
lean_dec(v_r_1888_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1937_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1917_; lean_object* v___x_1925_; lean_object* v___y_1927_; 
v___x_1912_ = lean_nat_add(v___x_1882_, v_size_1884_);
lean_dec(v_size_1884_);
v___x_1913_ = lean_nat_add(v___x_1912_, v_size_1883_);
lean_dec(v___x_1912_);
v___x_1925_ = lean_nat_add(v___x_1882_, v_size_1900_);
if (lean_obj_tag(v_l_1904_) == 0)
{
lean_object* v_size_1935_; 
v_size_1935_ = lean_ctor_get(v_l_1904_, 0);
lean_inc(v_size_1935_);
v___y_1927_ = v_size_1935_;
goto v___jp_1926_;
}
else
{
lean_object* v___x_1936_; 
v___x_1936_ = lean_unsigned_to_nat(0u);
v___y_1927_ = v___x_1936_;
goto v___jp_1926_;
}
v___jp_1914_:
{
lean_object* v___x_1918_; lean_object* v___x_1920_; 
v___x_1918_ = lean_nat_add(v___y_1915_, v___y_1917_);
lean_dec(v___y_1917_);
lean_dec(v___y_1915_);
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 4, v_impl_1881_);
lean_ctor_set(v___x_1910_, 3, v_r_1905_);
lean_ctor_set(v___x_1910_, 2, v_v_1389_);
lean_ctor_set(v___x_1910_, 1, v_k_1388_);
lean_ctor_set(v___x_1910_, 0, v___x_1918_);
v___x_1920_ = v___x_1910_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1918_);
lean_ctor_set(v_reuseFailAlloc_1924_, 1, v_k_1388_);
lean_ctor_set(v_reuseFailAlloc_1924_, 2, v_v_1389_);
lean_ctor_set(v_reuseFailAlloc_1924_, 3, v_r_1905_);
lean_ctor_set(v_reuseFailAlloc_1924_, 4, v_impl_1881_);
v___x_1920_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
lean_object* v___x_1922_; 
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 4, v___x_1920_);
lean_ctor_set(v___x_1898_, 3, v___y_1916_);
lean_ctor_set(v___x_1898_, 2, v_v_1903_);
lean_ctor_set(v___x_1898_, 1, v_k_1902_);
lean_ctor_set(v___x_1898_, 0, v___x_1913_);
v___x_1922_ = v___x_1898_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v___x_1913_);
lean_ctor_set(v_reuseFailAlloc_1923_, 1, v_k_1902_);
lean_ctor_set(v_reuseFailAlloc_1923_, 2, v_v_1903_);
lean_ctor_set(v_reuseFailAlloc_1923_, 3, v___y_1916_);
lean_ctor_set(v_reuseFailAlloc_1923_, 4, v___x_1920_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
v___jp_1926_:
{
lean_object* v___x_1928_; lean_object* v___x_1930_; 
v___x_1928_ = lean_nat_add(v___x_1925_, v___y_1927_);
lean_dec(v___y_1927_);
lean_dec(v___x_1925_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 4, v_l_1904_);
lean_ctor_set(v___x_1393_, 3, v_l_1887_);
lean_ctor_set(v___x_1393_, 2, v_v_1886_);
lean_ctor_set(v___x_1393_, 1, v_k_1885_);
lean_ctor_set(v___x_1393_, 0, v___x_1928_);
v___x_1930_ = v___x_1393_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v___x_1928_);
lean_ctor_set(v_reuseFailAlloc_1934_, 1, v_k_1885_);
lean_ctor_set(v_reuseFailAlloc_1934_, 2, v_v_1886_);
lean_ctor_set(v_reuseFailAlloc_1934_, 3, v_l_1887_);
lean_ctor_set(v_reuseFailAlloc_1934_, 4, v_l_1904_);
v___x_1930_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
lean_object* v___x_1931_; 
v___x_1931_ = lean_nat_add(v___x_1882_, v_size_1883_);
lean_dec(v_size_1883_);
if (lean_obj_tag(v_r_1905_) == 0)
{
lean_object* v_size_1932_; 
v_size_1932_ = lean_ctor_get(v_r_1905_, 0);
lean_inc(v_size_1932_);
v___y_1915_ = v___x_1931_;
v___y_1916_ = v___x_1930_;
v___y_1917_ = v_size_1932_;
goto v___jp_1914_;
}
else
{
lean_object* v___x_1933_; 
v___x_1933_ = lean_unsigned_to_nat(0u);
v___y_1915_ = v___x_1931_;
v___y_1916_ = v___x_1930_;
v___y_1917_ = v___x_1933_;
goto v___jp_1914_;
}
}
}
}
}
else
{
lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1948_; 
lean_del_object(v___x_1393_);
v___x_1943_ = lean_nat_add(v___x_1882_, v_size_1884_);
lean_dec(v_size_1884_);
v___x_1944_ = lean_nat_add(v___x_1943_, v_size_1883_);
lean_dec(v___x_1943_);
v___x_1945_ = lean_nat_add(v___x_1882_, v_size_1883_);
lean_dec(v_size_1883_);
v___x_1946_ = lean_nat_add(v___x_1945_, v_size_1901_);
lean_dec(v___x_1945_);
lean_inc_ref(v_impl_1881_);
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 4, v_impl_1881_);
lean_ctor_set(v___x_1898_, 3, v_r_1888_);
lean_ctor_set(v___x_1898_, 2, v_v_1389_);
lean_ctor_set(v___x_1898_, 1, v_k_1388_);
lean_ctor_set(v___x_1898_, 0, v___x_1946_);
v___x_1948_ = v___x_1898_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v___x_1946_);
lean_ctor_set(v_reuseFailAlloc_1961_, 1, v_k_1388_);
lean_ctor_set(v_reuseFailAlloc_1961_, 2, v_v_1389_);
lean_ctor_set(v_reuseFailAlloc_1961_, 3, v_r_1888_);
lean_ctor_set(v_reuseFailAlloc_1961_, 4, v_impl_1881_);
v___x_1948_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
v_isSharedCheck_1955_ = !lean_is_exclusive(v_impl_1881_);
if (v_isSharedCheck_1955_ == 0)
{
lean_object* v_unused_1956_; lean_object* v_unused_1957_; lean_object* v_unused_1958_; lean_object* v_unused_1959_; lean_object* v_unused_1960_; 
v_unused_1956_ = lean_ctor_get(v_impl_1881_, 4);
lean_dec(v_unused_1956_);
v_unused_1957_ = lean_ctor_get(v_impl_1881_, 3);
lean_dec(v_unused_1957_);
v_unused_1958_ = lean_ctor_get(v_impl_1881_, 2);
lean_dec(v_unused_1958_);
v_unused_1959_ = lean_ctor_get(v_impl_1881_, 1);
lean_dec(v_unused_1959_);
v_unused_1960_ = lean_ctor_get(v_impl_1881_, 0);
lean_dec(v_unused_1960_);
v___x_1950_ = v_impl_1881_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_dec(v_impl_1881_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 4, v___x_1948_);
lean_ctor_set(v___x_1950_, 3, v_l_1887_);
lean_ctor_set(v___x_1950_, 2, v_v_1886_);
lean_ctor_set(v___x_1950_, 1, v_k_1885_);
lean_ctor_set(v___x_1950_, 0, v___x_1944_);
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v___x_1944_);
lean_ctor_set(v_reuseFailAlloc_1954_, 1, v_k_1885_);
lean_ctor_set(v_reuseFailAlloc_1954_, 2, v_v_1886_);
lean_ctor_set(v_reuseFailAlloc_1954_, 3, v_l_1887_);
lean_ctor_set(v_reuseFailAlloc_1954_, 4, v___x_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1968_; lean_object* v___x_1969_; lean_object* v___x_1971_; 
v_size_1968_ = lean_ctor_get(v_impl_1881_, 0);
lean_inc(v_size_1968_);
v___x_1969_ = lean_nat_add(v___x_1882_, v_size_1968_);
lean_dec(v_size_1968_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 4, v_impl_1881_);
lean_ctor_set(v___x_1393_, 0, v___x_1969_);
v___x_1971_ = v___x_1393_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1969_);
lean_ctor_set(v_reuseFailAlloc_1972_, 1, v_k_1388_);
lean_ctor_set(v_reuseFailAlloc_1972_, 2, v_v_1389_);
lean_ctor_set(v_reuseFailAlloc_1972_, 3, v_l_1390_);
lean_ctor_set(v_reuseFailAlloc_1972_, 4, v_impl_1881_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
else
{
if (lean_obj_tag(v_l_1390_) == 0)
{
lean_object* v_l_1973_; 
v_l_1973_ = lean_ctor_get(v_l_1390_, 3);
if (lean_obj_tag(v_l_1973_) == 0)
{
lean_object* v_r_1974_; 
lean_inc_ref(v_l_1973_);
v_r_1974_ = lean_ctor_get(v_l_1390_, 4);
lean_inc(v_r_1974_);
if (lean_obj_tag(v_r_1974_) == 0)
{
lean_object* v_size_1975_; lean_object* v_k_1976_; lean_object* v_v_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1990_; 
v_size_1975_ = lean_ctor_get(v_l_1390_, 0);
v_k_1976_ = lean_ctor_get(v_l_1390_, 1);
v_v_1977_ = lean_ctor_get(v_l_1390_, 2);
v_isSharedCheck_1990_ = !lean_is_exclusive(v_l_1390_);
if (v_isSharedCheck_1990_ == 0)
{
lean_object* v_unused_1991_; lean_object* v_unused_1992_; 
v_unused_1991_ = lean_ctor_get(v_l_1390_, 4);
lean_dec(v_unused_1991_);
v_unused_1992_ = lean_ctor_get(v_l_1390_, 3);
lean_dec(v_unused_1992_);
v___x_1979_ = v_l_1390_;
v_isShared_1980_ = v_isSharedCheck_1990_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_v_1977_);
lean_inc(v_k_1976_);
lean_inc(v_size_1975_);
lean_dec(v_l_1390_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1990_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v_size_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1985_; 
v_size_1981_ = lean_ctor_get(v_r_1974_, 0);
v___x_1982_ = lean_nat_add(v___x_1882_, v_size_1975_);
lean_dec(v_size_1975_);
v___x_1983_ = lean_nat_add(v___x_1882_, v_size_1981_);
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 4, v_impl_1881_);
lean_ctor_set(v___x_1979_, 3, v_r_1974_);
lean_ctor_set(v___x_1979_, 2, v_v_1389_);
lean_ctor_set(v___x_1979_, 1, v_k_1388_);
lean_ctor_set(v___x_1979_, 0, v___x_1983_);
v___x_1985_ = v___x_1979_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v___x_1983_);
lean_ctor_set(v_reuseFailAlloc_1989_, 1, v_k_1388_);
lean_ctor_set(v_reuseFailAlloc_1989_, 2, v_v_1389_);
lean_ctor_set(v_reuseFailAlloc_1989_, 3, v_r_1974_);
lean_ctor_set(v_reuseFailAlloc_1989_, 4, v_impl_1881_);
v___x_1985_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
lean_object* v___x_1987_; 
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 4, v___x_1985_);
lean_ctor_set(v___x_1393_, 3, v_l_1973_);
lean_ctor_set(v___x_1393_, 2, v_v_1977_);
lean_ctor_set(v___x_1393_, 1, v_k_1976_);
lean_ctor_set(v___x_1393_, 0, v___x_1982_);
v___x_1987_ = v___x_1393_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1982_);
lean_ctor_set(v_reuseFailAlloc_1988_, 1, v_k_1976_);
lean_ctor_set(v_reuseFailAlloc_1988_, 2, v_v_1977_);
lean_ctor_set(v_reuseFailAlloc_1988_, 3, v_l_1973_);
lean_ctor_set(v_reuseFailAlloc_1988_, 4, v___x_1985_);
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
else
{
lean_object* v_k_1993_; lean_object* v_v_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2005_; 
v_k_1993_ = lean_ctor_get(v_l_1390_, 1);
v_v_1994_ = lean_ctor_get(v_l_1390_, 2);
v_isSharedCheck_2005_ = !lean_is_exclusive(v_l_1390_);
if (v_isSharedCheck_2005_ == 0)
{
lean_object* v_unused_2006_; lean_object* v_unused_2007_; lean_object* v_unused_2008_; 
v_unused_2006_ = lean_ctor_get(v_l_1390_, 4);
lean_dec(v_unused_2006_);
v_unused_2007_ = lean_ctor_get(v_l_1390_, 3);
lean_dec(v_unused_2007_);
v_unused_2008_ = lean_ctor_get(v_l_1390_, 0);
lean_dec(v_unused_2008_);
v___x_1996_ = v_l_1390_;
v_isShared_1997_ = v_isSharedCheck_2005_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_v_1994_);
lean_inc(v_k_1993_);
lean_dec(v_l_1390_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2005_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1998_; lean_object* v___x_2000_; 
v___x_1998_ = lean_unsigned_to_nat(3u);
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 3, v_r_1974_);
lean_ctor_set(v___x_1996_, 2, v_v_1389_);
lean_ctor_set(v___x_1996_, 1, v_k_1388_);
lean_ctor_set(v___x_1996_, 0, v___x_1882_);
v___x_2000_ = v___x_1996_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v___x_1882_);
lean_ctor_set(v_reuseFailAlloc_2004_, 1, v_k_1388_);
lean_ctor_set(v_reuseFailAlloc_2004_, 2, v_v_1389_);
lean_ctor_set(v_reuseFailAlloc_2004_, 3, v_r_1974_);
lean_ctor_set(v_reuseFailAlloc_2004_, 4, v_r_1974_);
v___x_2000_ = v_reuseFailAlloc_2004_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
lean_object* v___x_2002_; 
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 4, v___x_2000_);
lean_ctor_set(v___x_1393_, 3, v_l_1973_);
lean_ctor_set(v___x_1393_, 2, v_v_1994_);
lean_ctor_set(v___x_1393_, 1, v_k_1993_);
lean_ctor_set(v___x_1393_, 0, v___x_1998_);
v___x_2002_ = v___x_1393_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_1998_);
lean_ctor_set(v_reuseFailAlloc_2003_, 1, v_k_1993_);
lean_ctor_set(v_reuseFailAlloc_2003_, 2, v_v_1994_);
lean_ctor_set(v_reuseFailAlloc_2003_, 3, v_l_1973_);
lean_ctor_set(v_reuseFailAlloc_2003_, 4, v___x_2000_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
}
}
else
{
lean_object* v_r_2009_; 
v_r_2009_ = lean_ctor_get(v_l_1390_, 4);
lean_inc(v_r_2009_);
if (lean_obj_tag(v_r_2009_) == 0)
{
lean_object* v_k_2010_; lean_object* v_v_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2034_; 
lean_inc(v_l_1973_);
v_k_2010_ = lean_ctor_get(v_l_1390_, 1);
v_v_2011_ = lean_ctor_get(v_l_1390_, 2);
v_isSharedCheck_2034_ = !lean_is_exclusive(v_l_1390_);
if (v_isSharedCheck_2034_ == 0)
{
lean_object* v_unused_2035_; lean_object* v_unused_2036_; lean_object* v_unused_2037_; 
v_unused_2035_ = lean_ctor_get(v_l_1390_, 4);
lean_dec(v_unused_2035_);
v_unused_2036_ = lean_ctor_get(v_l_1390_, 3);
lean_dec(v_unused_2036_);
v_unused_2037_ = lean_ctor_get(v_l_1390_, 0);
lean_dec(v_unused_2037_);
v___x_2013_ = v_l_1390_;
v_isShared_2014_ = v_isSharedCheck_2034_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_v_2011_);
lean_inc(v_k_2010_);
lean_dec(v_l_1390_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2034_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v_k_2015_; lean_object* v_v_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2030_; 
v_k_2015_ = lean_ctor_get(v_r_2009_, 1);
v_v_2016_ = lean_ctor_get(v_r_2009_, 2);
v_isSharedCheck_2030_ = !lean_is_exclusive(v_r_2009_);
if (v_isSharedCheck_2030_ == 0)
{
lean_object* v_unused_2031_; lean_object* v_unused_2032_; lean_object* v_unused_2033_; 
v_unused_2031_ = lean_ctor_get(v_r_2009_, 4);
lean_dec(v_unused_2031_);
v_unused_2032_ = lean_ctor_get(v_r_2009_, 3);
lean_dec(v_unused_2032_);
v_unused_2033_ = lean_ctor_get(v_r_2009_, 0);
lean_dec(v_unused_2033_);
v___x_2018_ = v_r_2009_;
v_isShared_2019_ = v_isSharedCheck_2030_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_v_2016_);
lean_inc(v_k_2015_);
lean_dec(v_r_2009_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2030_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2020_; lean_object* v___x_2022_; 
v___x_2020_ = lean_unsigned_to_nat(3u);
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 4, v_l_1973_);
lean_ctor_set(v___x_2018_, 3, v_l_1973_);
lean_ctor_set(v___x_2018_, 2, v_v_2011_);
lean_ctor_set(v___x_2018_, 1, v_k_2010_);
lean_ctor_set(v___x_2018_, 0, v___x_1882_);
v___x_2022_ = v___x_2018_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_1882_);
lean_ctor_set(v_reuseFailAlloc_2029_, 1, v_k_2010_);
lean_ctor_set(v_reuseFailAlloc_2029_, 2, v_v_2011_);
lean_ctor_set(v_reuseFailAlloc_2029_, 3, v_l_1973_);
lean_ctor_set(v_reuseFailAlloc_2029_, 4, v_l_1973_);
v___x_2022_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
lean_object* v___x_2024_; 
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 4, v_l_1973_);
lean_ctor_set(v___x_2013_, 2, v_v_1389_);
lean_ctor_set(v___x_2013_, 1, v_k_1388_);
lean_ctor_set(v___x_2013_, 0, v___x_1882_);
v___x_2024_ = v___x_2013_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_1882_);
lean_ctor_set(v_reuseFailAlloc_2028_, 1, v_k_1388_);
lean_ctor_set(v_reuseFailAlloc_2028_, 2, v_v_1389_);
lean_ctor_set(v_reuseFailAlloc_2028_, 3, v_l_1973_);
lean_ctor_set(v_reuseFailAlloc_2028_, 4, v_l_1973_);
v___x_2024_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
lean_object* v___x_2026_; 
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 4, v___x_2024_);
lean_ctor_set(v___x_1393_, 3, v___x_2022_);
lean_ctor_set(v___x_1393_, 2, v_v_2016_);
lean_ctor_set(v___x_1393_, 1, v_k_2015_);
lean_ctor_set(v___x_1393_, 0, v___x_2020_);
v___x_2026_ = v___x_1393_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2020_);
lean_ctor_set(v_reuseFailAlloc_2027_, 1, v_k_2015_);
lean_ctor_set(v_reuseFailAlloc_2027_, 2, v_v_2016_);
lean_ctor_set(v_reuseFailAlloc_2027_, 3, v___x_2022_);
lean_ctor_set(v_reuseFailAlloc_2027_, 4, v___x_2024_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
}
}
}
else
{
lean_object* v___x_2038_; lean_object* v___x_2040_; 
v___x_2038_ = lean_unsigned_to_nat(2u);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 4, v_r_2009_);
lean_ctor_set(v___x_1393_, 0, v___x_2038_);
v___x_2040_ = v___x_1393_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2038_);
lean_ctor_set(v_reuseFailAlloc_2041_, 1, v_k_1388_);
lean_ctor_set(v_reuseFailAlloc_2041_, 2, v_v_1389_);
lean_ctor_set(v_reuseFailAlloc_2041_, 3, v_l_1390_);
lean_ctor_set(v_reuseFailAlloc_2041_, 4, v_r_2009_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
else
{
lean_object* v___x_2043_; 
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 4, v_l_1390_);
lean_ctor_set(v___x_1393_, 0, v___x_1882_);
v___x_2043_ = v___x_1393_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v___x_1882_);
lean_ctor_set(v_reuseFailAlloc_2044_, 1, v_k_1388_);
lean_ctor_set(v_reuseFailAlloc_2044_, 2, v_v_1389_);
lean_ctor_set(v_reuseFailAlloc_2044_, 3, v_l_1390_);
lean_ctor_set(v_reuseFailAlloc_2044_, 4, v_l_1390_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
}
}
}
else
{
return v_t_1387_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg___boxed(lean_object* v_k_2047_, lean_object* v_t_2048_){
_start:
{
lean_object* v_res_2049_; 
v_res_2049_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_2047_, v_t_2048_);
lean_dec(v_k_2047_);
return v_res_2049_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3(lean_object* v_xs_2050_, lean_object* v_v_2051_, lean_object* v_i_2052_){
_start:
{
lean_object* v___x_2053_; uint8_t v___x_2054_; 
v___x_2053_ = lean_array_get_size(v_xs_2050_);
v___x_2054_ = lean_nat_dec_lt(v_i_2052_, v___x_2053_);
if (v___x_2054_ == 0)
{
lean_object* v___x_2055_; 
lean_dec(v_i_2052_);
v___x_2055_ = lean_box(0);
return v___x_2055_;
}
else
{
lean_object* v___x_2056_; uint8_t v___x_2057_; 
v___x_2056_ = lean_array_fget_borrowed(v_xs_2050_, v_i_2052_);
v___x_2057_ = l_Lean_instBEqFVarId_beq(v___x_2056_, v_v_2051_);
if (v___x_2057_ == 0)
{
lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2058_ = lean_unsigned_to_nat(1u);
v___x_2059_ = lean_nat_add(v_i_2052_, v___x_2058_);
lean_dec(v_i_2052_);
v_i_2052_ = v___x_2059_;
goto _start;
}
else
{
lean_object* v___x_2061_; 
v___x_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2061_, 0, v_i_2052_);
return v___x_2061_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_xs_2062_, lean_object* v_v_2063_, lean_object* v_i_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3(v_xs_2062_, v_v_2063_, v_i_2064_);
lean_dec(v_v_2063_);
lean_dec_ref(v_xs_2062_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1(lean_object* v_xs_2066_, lean_object* v_v_2067_){
_start:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2068_ = lean_unsigned_to_nat(0u);
v___x_2069_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3(v_xs_2066_, v_v_2067_, v___x_2068_);
return v___x_2069_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_2070_, lean_object* v_v_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1(v_xs_2070_, v_v_2071_);
lean_dec(v_v_2071_);
lean_dec_ref(v_xs_2070_);
return v_res_2072_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(lean_object* v_x_2073_, size_t v_x_2074_, lean_object* v_x_2075_){
_start:
{
if (lean_obj_tag(v_x_2073_) == 0)
{
lean_object* v_es_2076_; lean_object* v___x_2077_; size_t v___x_2078_; size_t v___x_2079_; size_t v___x_2080_; lean_object* v_j_2081_; lean_object* v_entry_2082_; 
v_es_2076_ = lean_ctor_get(v_x_2073_, 0);
v___x_2077_ = lean_box(2);
v___x_2078_ = ((size_t)5ULL);
v___x_2079_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1);
v___x_2080_ = lean_usize_land(v_x_2074_, v___x_2079_);
v_j_2081_ = lean_usize_to_nat(v___x_2080_);
v_entry_2082_ = lean_array_get(v___x_2077_, v_es_2076_, v_j_2081_);
switch(lean_obj_tag(v_entry_2082_))
{
case 0:
{
lean_object* v_key_2083_; uint8_t v___x_2084_; 
v_key_2083_ = lean_ctor_get(v_entry_2082_, 0);
lean_inc(v_key_2083_);
lean_dec_ref(v_entry_2082_);
v___x_2084_ = l_Lean_instBEqFVarId_beq(v_x_2075_, v_key_2083_);
lean_dec(v_key_2083_);
if (v___x_2084_ == 0)
{
lean_dec(v_j_2081_);
return v_x_2073_;
}
else
{
lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2092_; 
lean_inc_ref(v_es_2076_);
v_isSharedCheck_2092_ = !lean_is_exclusive(v_x_2073_);
if (v_isSharedCheck_2092_ == 0)
{
lean_object* v_unused_2093_; 
v_unused_2093_ = lean_ctor_get(v_x_2073_, 0);
lean_dec(v_unused_2093_);
v___x_2086_ = v_x_2073_;
v_isShared_2087_ = v_isSharedCheck_2092_;
goto v_resetjp_2085_;
}
else
{
lean_dec(v_x_2073_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2092_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2088_; lean_object* v___x_2090_; 
v___x_2088_ = lean_array_set(v_es_2076_, v_j_2081_, v___x_2077_);
lean_dec(v_j_2081_);
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 0, v___x_2088_);
v___x_2090_ = v___x_2086_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v___x_2088_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
}
case 1:
{
lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2127_; 
lean_inc_ref(v_es_2076_);
v_isSharedCheck_2127_ = !lean_is_exclusive(v_x_2073_);
if (v_isSharedCheck_2127_ == 0)
{
lean_object* v_unused_2128_; 
v_unused_2128_ = lean_ctor_get(v_x_2073_, 0);
lean_dec(v_unused_2128_);
v___x_2095_ = v_x_2073_;
v_isShared_2096_ = v_isSharedCheck_2127_;
goto v_resetjp_2094_;
}
else
{
lean_dec(v_x_2073_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2127_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v_node_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2126_; 
v_node_2097_ = lean_ctor_get(v_entry_2082_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v_entry_2082_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2099_ = v_entry_2082_;
v_isShared_2100_ = v_isSharedCheck_2126_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_node_2097_);
lean_dec(v_entry_2082_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2126_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v_entries_2101_; size_t v___x_2102_; lean_object* v_newNode_2103_; lean_object* v___x_2104_; 
v_entries_2101_ = lean_array_set(v_es_2076_, v_j_2081_, v___x_2077_);
v___x_2102_ = lean_usize_shift_right(v_x_2074_, v___x_2078_);
v_newNode_2103_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_node_2097_, v___x_2102_, v_x_2075_);
lean_inc_ref(v_newNode_2103_);
v___x_2104_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_2103_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v___x_2106_; 
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 0, v_newNode_2103_);
v___x_2106_ = v___x_2099_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_newNode_2103_);
v___x_2106_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
lean_object* v___x_2107_; lean_object* v___x_2109_; 
v___x_2107_ = lean_array_set(v_entries_2101_, v_j_2081_, v___x_2106_);
lean_dec(v_j_2081_);
if (v_isShared_2096_ == 0)
{
lean_ctor_set(v___x_2095_, 0, v___x_2107_);
v___x_2109_ = v___x_2095_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v___x_2107_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
else
{
lean_object* v_val_2112_; lean_object* v_fst_2113_; lean_object* v_snd_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2125_; 
lean_dec_ref(v_newNode_2103_);
lean_del_object(v___x_2099_);
v_val_2112_ = lean_ctor_get(v___x_2104_, 0);
lean_inc(v_val_2112_);
lean_dec_ref(v___x_2104_);
v_fst_2113_ = lean_ctor_get(v_val_2112_, 0);
v_snd_2114_ = lean_ctor_get(v_val_2112_, 1);
v_isSharedCheck_2125_ = !lean_is_exclusive(v_val_2112_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2116_ = v_val_2112_;
v_isShared_2117_ = v_isSharedCheck_2125_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_snd_2114_);
lean_inc(v_fst_2113_);
lean_dec(v_val_2112_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2125_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2119_; 
if (v_isShared_2117_ == 0)
{
v___x_2119_ = v___x_2116_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_fst_2113_);
lean_ctor_set(v_reuseFailAlloc_2124_, 1, v_snd_2114_);
v___x_2119_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
lean_object* v___x_2120_; lean_object* v___x_2122_; 
v___x_2120_ = lean_array_set(v_entries_2101_, v_j_2081_, v___x_2119_);
lean_dec(v_j_2081_);
if (v_isShared_2096_ == 0)
{
lean_ctor_set(v___x_2095_, 0, v___x_2120_);
v___x_2122_ = v___x_2095_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v___x_2120_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_2081_);
return v_x_2073_;
}
}
}
else
{
lean_object* v_ks_2129_; lean_object* v_vs_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2144_; 
v_ks_2129_ = lean_ctor_get(v_x_2073_, 0);
v_vs_2130_ = lean_ctor_get(v_x_2073_, 1);
v_isSharedCheck_2144_ = !lean_is_exclusive(v_x_2073_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2132_ = v_x_2073_;
v_isShared_2133_ = v_isSharedCheck_2144_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_vs_2130_);
lean_inc(v_ks_2129_);
lean_dec(v_x_2073_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2144_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2134_; 
v___x_2134_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1(v_ks_2129_, v_x_2075_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v___x_2136_; 
if (v_isShared_2133_ == 0)
{
v___x_2136_ = v___x_2132_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_ks_2129_);
lean_ctor_set(v_reuseFailAlloc_2137_, 1, v_vs_2130_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
else
{
lean_object* v_val_2138_; lean_object* v_keys_x27_2139_; lean_object* v_vals_x27_2140_; lean_object* v___x_2142_; 
v_val_2138_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_val_2138_);
lean_dec_ref(v___x_2134_);
lean_inc(v_val_2138_);
v_keys_x27_2139_ = l_Array_eraseIdx___redArg(v_ks_2129_, v_val_2138_);
v_vals_x27_2140_ = l_Array_eraseIdx___redArg(v_vs_2130_, v_val_2138_);
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 1, v_vals_x27_2140_);
lean_ctor_set(v___x_2132_, 0, v_keys_x27_2139_);
v___x_2142_ = v___x_2132_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_keys_x27_2139_);
lean_ctor_set(v_reuseFailAlloc_2143_, 1, v_vals_x27_2140_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg___boxed(lean_object* v_x_2145_, lean_object* v_x_2146_, lean_object* v_x_2147_){
_start:
{
size_t v_x_2695__boxed_2148_; lean_object* v_res_2149_; 
v_x_2695__boxed_2148_ = lean_unbox_usize(v_x_2146_);
lean_dec(v_x_2146_);
v_res_2149_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_x_2145_, v_x_2695__boxed_2148_, v_x_2147_);
lean_dec(v_x_2147_);
return v_res_2149_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(lean_object* v_x_2150_, lean_object* v_x_2151_){
_start:
{
uint64_t v___x_2152_; size_t v_h_2153_; lean_object* v___x_2154_; 
v___x_2152_ = l_Lean_instHashableFVarId_hash(v_x_2151_);
v_h_2153_ = lean_uint64_to_usize(v___x_2152_);
v___x_2154_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_x_2150_, v_h_2153_, v_x_2151_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg___boxed(lean_object* v_x_2155_, lean_object* v_x_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_x_2155_, v_x_2156_);
lean_dec(v_x_2156_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_erase(lean_object* v_lctx_2158_, lean_object* v_fvarId_2159_){
_start:
{
lean_object* v_fvarIdToDecl_2160_; lean_object* v_decls_2161_; lean_object* v_auxDeclToFullName_2162_; lean_object* v___x_2163_; 
v_fvarIdToDecl_2160_ = lean_ctor_get(v_lctx_2158_, 0);
v_decls_2161_ = lean_ctor_get(v_lctx_2158_, 1);
v_auxDeclToFullName_2162_ = lean_ctor_get(v_lctx_2158_, 2);
lean_inc_ref(v_fvarIdToDecl_2160_);
v___x_2163_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_fvarIdToDecl_2160_, v_fvarId_2159_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_dec(v_fvarId_2159_);
return v_lctx_2158_;
}
else
{
lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2183_; 
lean_inc(v_auxDeclToFullName_2162_);
lean_inc_ref(v_decls_2161_);
lean_inc_ref(v_fvarIdToDecl_2160_);
v_isSharedCheck_2183_ = !lean_is_exclusive(v_lctx_2158_);
if (v_isSharedCheck_2183_ == 0)
{
lean_object* v_unused_2184_; lean_object* v_unused_2185_; lean_object* v_unused_2186_; 
v_unused_2184_ = lean_ctor_get(v_lctx_2158_, 2);
lean_dec(v_unused_2184_);
v_unused_2185_ = lean_ctor_get(v_lctx_2158_, 1);
lean_dec(v_unused_2185_);
v_unused_2186_ = lean_ctor_get(v_lctx_2158_, 0);
lean_dec(v_unused_2186_);
v___x_2165_ = v_lctx_2158_;
v_isShared_2166_ = v_isSharedCheck_2183_;
goto v_resetjp_2164_;
}
else
{
lean_dec(v_lctx_2158_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2183_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v_val_2167_; lean_object* v___x_2168_; lean_object* v___y_2170_; lean_object* v_index_2182_; 
v_val_2167_ = lean_ctor_get(v___x_2163_, 0);
lean_inc(v_val_2167_);
lean_dec_ref(v___x_2163_);
v___x_2168_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_fvarIdToDecl_2160_, v_fvarId_2159_);
v_index_2182_ = lean_ctor_get(v_val_2167_, 0);
lean_inc(v_index_2182_);
v___y_2170_ = v_index_2182_;
goto v___jp_2169_;
v___jp_2169_:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; uint8_t v___x_2174_; 
v___x_2171_ = lean_box(0);
v___x_2172_ = l_Lean_PersistentArray_set___redArg(v_decls_2161_, v___y_2170_, v___x_2171_);
lean_dec(v___y_2170_);
v___x_2173_ = l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(v___x_2172_);
v___x_2174_ = l_Lean_LocalDecl_isAuxDecl(v_val_2167_);
lean_dec(v_val_2167_);
if (v___x_2174_ == 0)
{
lean_object* v___x_2176_; 
lean_dec(v_fvarId_2159_);
if (v_isShared_2166_ == 0)
{
lean_ctor_set(v___x_2165_, 1, v___x_2173_);
lean_ctor_set(v___x_2165_, 0, v___x_2168_);
v___x_2176_ = v___x_2165_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2168_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v___x_2173_);
lean_ctor_set(v_reuseFailAlloc_2177_, 2, v_auxDeclToFullName_2162_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
else
{
lean_object* v___x_2178_; lean_object* v___x_2180_; 
v___x_2178_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_fvarId_2159_, v_auxDeclToFullName_2162_);
lean_dec(v_fvarId_2159_);
if (v_isShared_2166_ == 0)
{
lean_ctor_set(v___x_2165_, 2, v___x_2178_);
lean_ctor_set(v___x_2165_, 1, v___x_2173_);
lean_ctor_set(v___x_2165_, 0, v___x_2168_);
v___x_2180_ = v___x_2165_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2168_);
lean_ctor_set(v_reuseFailAlloc_2181_, 1, v___x_2173_);
lean_ctor_set(v_reuseFailAlloc_2181_, 2, v___x_2178_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0(lean_object* v_00_u03b2_2187_, lean_object* v_x_2188_, lean_object* v_x_2189_){
_start:
{
lean_object* v___x_2190_; 
v___x_2190_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_x_2188_, v_x_2189_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___boxed(lean_object* v_00_u03b2_2191_, lean_object* v_x_2192_, lean_object* v_x_2193_){
_start:
{
lean_object* v_res_2194_; 
v_res_2194_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0(v_00_u03b2_2191_, v_x_2192_, v_x_2193_);
lean_dec(v_x_2193_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1(lean_object* v_00_u03b2_2195_, lean_object* v_k_2196_, lean_object* v_t_2197_, lean_object* v_h_2198_){
_start:
{
lean_object* v___x_2199_; 
v___x_2199_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_2196_, v_t_2197_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___boxed(lean_object* v_00_u03b2_2200_, lean_object* v_k_2201_, lean_object* v_t_2202_, lean_object* v_h_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1(v_00_u03b2_2200_, v_k_2201_, v_t_2202_, v_h_2203_);
lean_dec(v_k_2201_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0(lean_object* v_00_u03b2_2205_, lean_object* v_x_2206_, size_t v_x_2207_, lean_object* v_x_2208_){
_start:
{
lean_object* v___x_2209_; 
v___x_2209_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_x_2206_, v_x_2207_, v_x_2208_);
return v___x_2209_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2210_, lean_object* v_x_2211_, lean_object* v_x_2212_, lean_object* v_x_2213_){
_start:
{
size_t v_x_2919__boxed_2214_; lean_object* v_res_2215_; 
v_x_2919__boxed_2214_ = lean_unbox_usize(v_x_2212_);
lean_dec(v_x_2212_);
v_res_2215_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0(v_00_u03b2_2210_, v_x_2211_, v_x_2919__boxed_2214_, v_x_2213_);
lean_dec(v_x_2213_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_pop(lean_object* v_lctx_2216_){
_start:
{
lean_object* v_decls_2217_; lean_object* v_fvarIdToDecl_2218_; lean_object* v_auxDeclToFullName_2219_; lean_object* v_size_2220_; lean_object* v___x_2221_; uint8_t v___x_2222_; 
v_decls_2217_ = lean_ctor_get(v_lctx_2216_, 1);
v_fvarIdToDecl_2218_ = lean_ctor_get(v_lctx_2216_, 0);
v_auxDeclToFullName_2219_ = lean_ctor_get(v_lctx_2216_, 2);
v_size_2220_ = lean_ctor_get(v_decls_2217_, 2);
v___x_2221_ = lean_unsigned_to_nat(0u);
v___x_2222_ = lean_nat_dec_eq(v_size_2220_, v___x_2221_);
if (v___x_2222_ == 0)
{
lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2223_ = lean_box(0);
v___x_2224_ = lean_unsigned_to_nat(1u);
v___x_2225_ = lean_nat_sub(v_size_2220_, v___x_2224_);
lean_inc_ref(v_decls_2217_);
v___x_2226_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2223_, v_decls_2217_, v___x_2225_);
lean_dec(v___x_2225_);
if (lean_obj_tag(v___x_2226_) == 0)
{
return v_lctx_2216_;
}
else
{
lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2245_; 
lean_inc(v_auxDeclToFullName_2219_);
lean_inc_ref(v_fvarIdToDecl_2218_);
lean_inc_ref(v_decls_2217_);
v_isSharedCheck_2245_ = !lean_is_exclusive(v_lctx_2216_);
if (v_isSharedCheck_2245_ == 0)
{
lean_object* v_unused_2246_; lean_object* v_unused_2247_; lean_object* v_unused_2248_; 
v_unused_2246_ = lean_ctor_get(v_lctx_2216_, 2);
lean_dec(v_unused_2246_);
v_unused_2247_ = lean_ctor_get(v_lctx_2216_, 1);
lean_dec(v_unused_2247_);
v_unused_2248_ = lean_ctor_get(v_lctx_2216_, 0);
lean_dec(v_unused_2248_);
v___x_2228_ = v_lctx_2216_;
v_isShared_2229_ = v_isSharedCheck_2245_;
goto v_resetjp_2227_;
}
else
{
lean_dec(v_lctx_2216_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2245_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v_val_2230_; lean_object* v___y_2232_; lean_object* v_fvarId_2244_; 
v_val_2230_ = lean_ctor_get(v___x_2226_, 0);
lean_inc(v_val_2230_);
lean_dec_ref(v___x_2226_);
v_fvarId_2244_ = lean_ctor_get(v_val_2230_, 1);
lean_inc(v_fvarId_2244_);
v___y_2232_ = v_fvarId_2244_;
goto v___jp_2231_;
v___jp_2231_:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; uint8_t v___x_2236_; 
v___x_2233_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_fvarIdToDecl_2218_, v___y_2232_);
v___x_2234_ = l_Lean_PersistentArray_pop___redArg(v_decls_2217_);
v___x_2235_ = l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(v___x_2234_);
v___x_2236_ = l_Lean_LocalDecl_isAuxDecl(v_val_2230_);
lean_dec(v_val_2230_);
if (v___x_2236_ == 0)
{
lean_object* v___x_2238_; 
lean_dec(v___y_2232_);
if (v_isShared_2229_ == 0)
{
lean_ctor_set(v___x_2228_, 1, v___x_2235_);
lean_ctor_set(v___x_2228_, 0, v___x_2233_);
v___x_2238_ = v___x_2228_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v___x_2233_);
lean_ctor_set(v_reuseFailAlloc_2239_, 1, v___x_2235_);
lean_ctor_set(v_reuseFailAlloc_2239_, 2, v_auxDeclToFullName_2219_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
else
{
lean_object* v___x_2240_; lean_object* v___x_2242_; 
v___x_2240_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v___y_2232_, v_auxDeclToFullName_2219_);
lean_dec(v___y_2232_);
if (v_isShared_2229_ == 0)
{
lean_ctor_set(v___x_2228_, 2, v___x_2240_);
lean_ctor_set(v___x_2228_, 1, v___x_2235_);
lean_ctor_set(v___x_2228_, 0, v___x_2233_);
v___x_2242_ = v___x_2228_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2233_);
lean_ctor_set(v_reuseFailAlloc_2243_, 1, v___x_2235_);
lean_ctor_set(v_reuseFailAlloc_2243_, 2, v___x_2240_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
}
}
}
else
{
return v_lctx_2216_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(lean_object* v_userName_2249_, lean_object* v_as_2250_, lean_object* v_i_2251_){
_start:
{
lean_object* v_zero_2252_; uint8_t v_isZero_2253_; 
v_zero_2252_ = lean_unsigned_to_nat(0u);
v_isZero_2253_ = lean_nat_dec_eq(v_i_2251_, v_zero_2252_);
if (v_isZero_2253_ == 1)
{
lean_object* v___x_2254_; 
lean_dec(v_i_2251_);
v___x_2254_ = lean_box(0);
return v___x_2254_;
}
else
{
lean_object* v_one_2255_; lean_object* v_n_2256_; lean_object* v___y_2258_; lean_object* v___x_2260_; lean_object* v___y_2262_; 
v_one_2255_ = lean_unsigned_to_nat(1u);
v_n_2256_ = lean_nat_sub(v_i_2251_, v_one_2255_);
lean_dec(v_i_2251_);
v___x_2260_ = lean_array_fget_borrowed(v_as_2250_, v_n_2256_);
if (lean_obj_tag(v___x_2260_) == 0)
{
v___y_2258_ = v___x_2260_;
goto v___jp_2257_;
}
else
{
lean_object* v_val_2265_; lean_object* v_userName_2266_; 
v_val_2265_ = lean_ctor_get(v___x_2260_, 0);
v_userName_2266_ = lean_ctor_get(v_val_2265_, 2);
lean_inc(v_userName_2266_);
v___y_2262_ = v_userName_2266_;
goto v___jp_2261_;
}
v___jp_2257_:
{
if (lean_obj_tag(v___y_2258_) == 0)
{
v_i_2251_ = v_n_2256_;
goto _start;
}
else
{
lean_dec(v_n_2256_);
return v___y_2258_;
}
}
v___jp_2261_:
{
uint8_t v___x_2263_; 
v___x_2263_ = lean_name_eq(v___y_2262_, v_userName_2249_);
lean_dec(v___y_2262_);
if (v___x_2263_ == 0)
{
v_i_2251_ = v_n_2256_;
goto _start;
}
else
{
lean_inc(v___x_2260_);
v___y_2258_ = v___x_2260_;
goto v___jp_2257_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_userName_2267_, lean_object* v_as_2268_, lean_object* v_i_2269_){
_start:
{
lean_object* v_res_2270_; 
v_res_2270_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2267_, v_as_2268_, v_i_2269_);
lean_dec_ref(v_as_2268_);
lean_dec(v_userName_2267_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(lean_object* v_userName_2271_, lean_object* v_as_2272_, lean_object* v_i_2273_){
_start:
{
lean_object* v_zero_2274_; uint8_t v_isZero_2275_; 
v_zero_2274_ = lean_unsigned_to_nat(0u);
v_isZero_2275_ = lean_nat_dec_eq(v_i_2273_, v_zero_2274_);
if (v_isZero_2275_ == 1)
{
lean_object* v___x_2276_; 
lean_dec(v_i_2273_);
v___x_2276_ = lean_box(0);
return v___x_2276_;
}
else
{
lean_object* v_one_2277_; lean_object* v_n_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v_one_2277_ = lean_unsigned_to_nat(1u);
v_n_2278_ = lean_nat_sub(v_i_2273_, v_one_2277_);
lean_dec(v_i_2273_);
v___x_2279_ = lean_array_fget_borrowed(v_as_2272_, v_n_2278_);
v___x_2280_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(v_userName_2271_, v___x_2279_);
if (lean_obj_tag(v___x_2280_) == 0)
{
v_i_2273_ = v_n_2278_;
goto _start;
}
else
{
lean_dec(v_n_2278_);
return v___x_2280_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(lean_object* v_userName_2282_, lean_object* v_x_2283_){
_start:
{
if (lean_obj_tag(v_x_2283_) == 0)
{
lean_object* v_cs_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v_cs_2284_ = lean_ctor_get(v_x_2283_, 0);
v___x_2285_ = lean_array_get_size(v_cs_2284_);
v___x_2286_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(v_userName_2282_, v_cs_2284_, v___x_2285_);
return v___x_2286_;
}
else
{
lean_object* v_vs_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; 
v_vs_2287_ = lean_ctor_get(v_x_2283_, 0);
v___x_2288_ = lean_array_get_size(v_vs_2287_);
v___x_2289_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2282_, v_vs_2287_, v___x_2288_);
return v___x_2289_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1___boxed(lean_object* v_userName_2290_, lean_object* v_x_2291_){
_start:
{
lean_object* v_res_2292_; 
v_res_2292_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(v_userName_2290_, v_x_2291_);
lean_dec_ref(v_x_2291_);
lean_dec(v_userName_2290_);
return v_res_2292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_userName_2293_, lean_object* v_as_2294_, lean_object* v_i_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(v_userName_2293_, v_as_2294_, v_i_2295_);
lean_dec_ref(v_as_2294_);
lean_dec(v_userName_2293_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0(lean_object* v_userName_2297_, lean_object* v_t_2298_){
_start:
{
lean_object* v_root_2299_; lean_object* v_tail_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
v_root_2299_ = lean_ctor_get(v_t_2298_, 0);
v_tail_2300_ = lean_ctor_get(v_t_2298_, 1);
v___x_2301_ = lean_array_get_size(v_tail_2300_);
v___x_2302_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2297_, v_tail_2300_, v___x_2301_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v___x_2303_; 
v___x_2303_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(v_userName_2297_, v_root_2299_);
return v___x_2303_;
}
else
{
return v___x_2302_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0___boxed(lean_object* v_userName_2304_, lean_object* v_t_2305_){
_start:
{
lean_object* v_res_2306_; 
v_res_2306_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0(v_userName_2304_, v_t_2305_);
lean_dec_ref(v_t_2305_);
lean_dec(v_userName_2304_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object* v_lctx_2307_, lean_object* v_userName_2308_){
_start:
{
lean_object* v_decls_2309_; lean_object* v___x_2310_; 
v_decls_2309_ = lean_ctor_get(v_lctx_2307_, 1);
v___x_2310_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0(v_userName_2308_, v_decls_2309_);
return v___x_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserName_x3f___boxed(lean_object* v_lctx_2311_, lean_object* v_userName_2312_){
_start:
{
lean_object* v_res_2313_; 
v_res_2313_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2311_, v_userName_2312_);
lean_dec(v_userName_2312_);
lean_dec_ref(v_lctx_2311_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0(lean_object* v_userName_2314_, lean_object* v_as_2315_, lean_object* v_i_2316_, lean_object* v_a_2317_){
_start:
{
lean_object* v___x_2318_; 
v___x_2318_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2314_, v_as_2315_, v_i_2316_);
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___boxed(lean_object* v_userName_2319_, lean_object* v_as_2320_, lean_object* v_i_2321_, lean_object* v_a_2322_){
_start:
{
lean_object* v_res_2323_; 
v_res_2323_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0(v_userName_2319_, v_as_2320_, v_i_2321_, v_a_2322_);
lean_dec_ref(v_as_2320_);
lean_dec(v_userName_2319_);
return v_res_2323_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2(lean_object* v_userName_2324_, lean_object* v_as_2325_, lean_object* v_i_2326_, lean_object* v_a_2327_){
_start:
{
lean_object* v___x_2328_; 
v___x_2328_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(v_userName_2324_, v_as_2325_, v_i_2326_);
return v___x_2328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___boxed(lean_object* v_userName_2329_, lean_object* v_as_2330_, lean_object* v_i_2331_, lean_object* v_a_2332_){
_start:
{
lean_object* v_res_2333_; 
v_res_2333_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2(v_userName_2329_, v_as_2330_, v_i_2331_, v_a_2332_);
lean_dec_ref(v_as_2330_);
lean_dec(v_userName_2329_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFromUserName_x21(lean_object* v_lctx_2337_, lean_object* v_userName_2338_){
_start:
{
lean_object* v___x_2339_; 
v___x_2339_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2337_, v_userName_2338_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; uint8_t v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2340_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_2341_ = ((lean_object*)(l_Lean_LocalContext_getFromUserName_x21___closed__0));
v___x_2342_ = lean_unsigned_to_nat(403u);
v___x_2343_ = lean_unsigned_to_nat(17u);
v___x_2344_ = ((lean_object*)(l_Lean_LocalContext_getFromUserName_x21___closed__1));
v___x_2345_ = 1;
v___x_2346_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_userName_2338_, v___x_2345_);
v___x_2347_ = lean_string_append(v___x_2344_, v___x_2346_);
lean_dec_ref(v___x_2346_);
v___x_2348_ = ((lean_object*)(l_Lean_LocalContext_getFromUserName_x21___closed__2));
v___x_2349_ = lean_string_append(v___x_2347_, v___x_2348_);
v___x_2350_ = l_mkPanicMessageWithDecl(v___x_2340_, v___x_2341_, v___x_2342_, v___x_2343_, v___x_2349_);
lean_dec_ref(v___x_2349_);
v___x_2351_ = l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(v___x_2350_);
return v___x_2351_;
}
else
{
lean_object* v_val_2352_; 
lean_dec(v_userName_2338_);
v_val_2352_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_val_2352_);
lean_dec_ref(v___x_2339_);
return v_val_2352_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFromUserName_x21___boxed(lean_object* v_lctx_2353_, lean_object* v_userName_2354_){
_start:
{
lean_object* v_res_2355_; 
v_res_2355_ = l_Lean_LocalContext_getFromUserName_x21(v_lctx_2353_, v_userName_2354_);
lean_dec_ref(v_lctx_2353_);
return v_res_2355_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_usesUserName(lean_object* v_lctx_2356_, lean_object* v_userName_2357_){
_start:
{
lean_object* v___x_2358_; 
v___x_2358_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2356_, v_userName_2357_);
if (lean_obj_tag(v___x_2358_) == 0)
{
uint8_t v___x_2359_; 
v___x_2359_ = 0;
return v___x_2359_;
}
else
{
uint8_t v___x_2360_; 
lean_dec_ref(v___x_2358_);
v___x_2360_ = 1;
return v___x_2360_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_usesUserName___boxed(lean_object* v_lctx_2361_, lean_object* v_userName_2362_){
_start:
{
uint8_t v_res_2363_; lean_object* v_r_2364_; 
v_res_2363_ = l_Lean_LocalContext_usesUserName(v_lctx_2361_, v_userName_2362_);
lean_dec(v_userName_2362_);
lean_dec_ref(v_lctx_2361_);
v_r_2364_ = lean_box(v_res_2363_);
return v_r_2364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(lean_object* v_lctx_2365_, lean_object* v_suggestion_2366_, lean_object* v_i_2367_){
_start:
{
lean_object* v_curr_2368_; uint8_t v___x_2369_; 
lean_inc(v_i_2367_);
lean_inc(v_suggestion_2366_);
v_curr_2368_ = lean_name_append_index_after(v_suggestion_2366_, v_i_2367_);
v___x_2369_ = l_Lean_LocalContext_usesUserName(v_lctx_2365_, v_curr_2368_);
if (v___x_2369_ == 0)
{
lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; 
lean_dec(v_suggestion_2366_);
v___x_2370_ = lean_unsigned_to_nat(1u);
v___x_2371_ = lean_nat_add(v_i_2367_, v___x_2370_);
lean_dec(v_i_2367_);
v___x_2372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2372_, 0, v_curr_2368_);
lean_ctor_set(v___x_2372_, 1, v___x_2371_);
return v___x_2372_;
}
else
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
lean_dec(v_curr_2368_);
v___x_2373_ = lean_unsigned_to_nat(1u);
v___x_2374_ = lean_nat_add(v_i_2367_, v___x_2373_);
lean_dec(v_i_2367_);
v_i_2367_ = v___x_2374_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux___boxed(lean_object* v_lctx_2376_, lean_object* v_suggestion_2377_, lean_object* v_i_2378_){
_start:
{
lean_object* v_res_2379_; 
v_res_2379_ = l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(v_lctx_2376_, v_suggestion_2377_, v_i_2378_);
lean_dec_ref(v_lctx_2376_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getUnusedName(lean_object* v_lctx_2380_, lean_object* v_suggestion_2381_){
_start:
{
lean_object* v_suggestion_2382_; uint8_t v___x_2383_; 
v_suggestion_2382_ = lean_erase_macro_scopes(v_suggestion_2381_);
v___x_2383_ = l_Lean_LocalContext_usesUserName(v_lctx_2380_, v_suggestion_2382_);
if (v___x_2383_ == 0)
{
return v_suggestion_2382_;
}
else
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v_fst_2386_; 
v___x_2384_ = lean_unsigned_to_nat(1u);
v___x_2385_ = l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(v_lctx_2380_, v_suggestion_2382_, v___x_2384_);
v_fst_2386_ = lean_ctor_get(v___x_2385_, 0);
lean_inc(v_fst_2386_);
lean_dec_ref(v___x_2385_);
return v_fst_2386_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getUnusedName___boxed(lean_object* v_lctx_2387_, lean_object* v_suggestion_2388_){
_start:
{
lean_object* v_res_2389_; 
v_res_2389_ = l_Lean_LocalContext_getUnusedName(v_lctx_2387_, v_suggestion_2388_);
lean_dec_ref(v_lctx_2387_);
return v_res_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_lastDecl(lean_object* v_lctx_2390_){
_start:
{
lean_object* v_decls_2391_; lean_object* v_size_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; uint8_t v___x_2396_; 
v_decls_2391_ = lean_ctor_get(v_lctx_2390_, 1);
lean_inc_ref(v_decls_2391_);
lean_dec_ref(v_lctx_2390_);
v_size_2392_ = lean_ctor_get(v_decls_2391_, 2);
v___x_2393_ = lean_box(0);
v___x_2394_ = lean_unsigned_to_nat(1u);
v___x_2395_ = lean_nat_sub(v_size_2392_, v___x_2394_);
v___x_2396_ = lean_nat_dec_lt(v___x_2395_, v_size_2392_);
if (v___x_2396_ == 0)
{
lean_object* v___x_2397_; 
lean_dec(v___x_2395_);
lean_dec_ref(v_decls_2391_);
v___x_2397_ = l_outOfBounds___redArg(v___x_2393_);
return v___x_2397_;
}
else
{
lean_object* v___x_2398_; 
v___x_2398_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2393_, v_decls_2391_, v___x_2395_);
lean_dec(v___x_2395_);
return v___x_2398_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setUserName(lean_object* v_lctx_2399_, lean_object* v_fvarId_2400_, lean_object* v_userName_2401_){
_start:
{
lean_object* v_fvarIdToDecl_2402_; lean_object* v_decls_2403_; lean_object* v_auxDeclToFullName_2404_; lean_object* v_decl_2405_; lean_object* v_decl_2406_; lean_object* v___y_2408_; lean_object* v___y_2409_; lean_object* v___y_2414_; lean_object* v_fvarId_2417_; 
v_fvarIdToDecl_2402_ = lean_ctor_get(v_lctx_2399_, 0);
lean_inc_ref(v_fvarIdToDecl_2402_);
v_decls_2403_ = lean_ctor_get(v_lctx_2399_, 1);
lean_inc_ref(v_decls_2403_);
v_auxDeclToFullName_2404_ = lean_ctor_get(v_lctx_2399_, 2);
lean_inc(v_auxDeclToFullName_2404_);
v_decl_2405_ = l_Lean_LocalContext_get_x21(v_lctx_2399_, v_fvarId_2400_);
v_decl_2406_ = l_Lean_LocalDecl_setUserName(v_decl_2405_, v_userName_2401_);
v_fvarId_2417_ = lean_ctor_get(v_decl_2406_, 1);
lean_inc(v_fvarId_2417_);
v___y_2414_ = v_fvarId_2417_;
goto v___jp_2413_;
v___jp_2407_:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2410_, 0, v_decl_2406_);
v___x_2411_ = l_Lean_PersistentArray_set___redArg(v_decls_2403_, v___y_2409_, v___x_2410_);
lean_dec(v___y_2409_);
v___x_2412_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2412_, 0, v___y_2408_);
lean_ctor_set(v___x_2412_, 1, v___x_2411_);
lean_ctor_set(v___x_2412_, 2, v_auxDeclToFullName_2404_);
return v___x_2412_;
}
v___jp_2413_:
{
lean_object* v___x_2415_; lean_object* v_index_2416_; 
lean_inc_ref(v_decl_2406_);
v___x_2415_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2402_, v___y_2414_, v_decl_2406_);
v_index_2416_ = lean_ctor_get(v_decl_2406_, 0);
lean_inc(v_index_2416_);
v___y_2408_ = v___x_2415_;
v___y_2409_ = v_index_2416_;
goto v___jp_2407_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_renameUserName(lean_object* v_lctx_2418_, lean_object* v_fromName_2419_, lean_object* v_toName_2420_){
_start:
{
lean_object* v_fvarIdToDecl_2421_; lean_object* v_decls_2422_; lean_object* v_auxDeclToFullName_2423_; lean_object* v___x_2424_; 
v_fvarIdToDecl_2421_ = lean_ctor_get(v_lctx_2418_, 0);
v_decls_2422_ = lean_ctor_get(v_lctx_2418_, 1);
v_auxDeclToFullName_2423_ = lean_ctor_get(v_lctx_2418_, 2);
v___x_2424_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2418_, v_fromName_2419_);
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_dec(v_toName_2420_);
return v_lctx_2418_;
}
else
{
lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2449_; 
lean_inc(v_auxDeclToFullName_2423_);
lean_inc_ref(v_decls_2422_);
lean_inc_ref(v_fvarIdToDecl_2421_);
v_isSharedCheck_2449_ = !lean_is_exclusive(v_lctx_2418_);
if (v_isSharedCheck_2449_ == 0)
{
lean_object* v_unused_2450_; lean_object* v_unused_2451_; lean_object* v_unused_2452_; 
v_unused_2450_ = lean_ctor_get(v_lctx_2418_, 2);
lean_dec(v_unused_2450_);
v_unused_2451_ = lean_ctor_get(v_lctx_2418_, 1);
lean_dec(v_unused_2451_);
v_unused_2452_ = lean_ctor_get(v_lctx_2418_, 0);
lean_dec(v_unused_2452_);
v___x_2426_ = v_lctx_2418_;
v_isShared_2427_ = v_isSharedCheck_2449_;
goto v_resetjp_2425_;
}
else
{
lean_dec(v_lctx_2418_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2449_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v_val_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2448_; 
v_val_2428_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2430_ = v___x_2424_;
v_isShared_2431_ = v_isSharedCheck_2448_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_val_2428_);
lean_dec(v___x_2424_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2448_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v_decl_2432_; lean_object* v___y_2434_; lean_object* v___y_2435_; lean_object* v___y_2444_; lean_object* v_fvarId_2447_; 
v_decl_2432_ = l_Lean_LocalDecl_setUserName(v_val_2428_, v_toName_2420_);
v_fvarId_2447_ = lean_ctor_get(v_decl_2432_, 1);
lean_inc(v_fvarId_2447_);
v___y_2444_ = v_fvarId_2447_;
goto v___jp_2443_;
v___jp_2433_:
{
lean_object* v___x_2437_; 
if (v_isShared_2431_ == 0)
{
lean_ctor_set(v___x_2430_, 0, v_decl_2432_);
v___x_2437_ = v___x_2430_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_decl_2432_);
v___x_2437_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
lean_object* v___x_2438_; lean_object* v___x_2440_; 
v___x_2438_ = l_Lean_PersistentArray_set___redArg(v_decls_2422_, v___y_2435_, v___x_2437_);
lean_dec(v___y_2435_);
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 1, v___x_2438_);
lean_ctor_set(v___x_2426_, 0, v___y_2434_);
v___x_2440_ = v___x_2426_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v___y_2434_);
lean_ctor_set(v_reuseFailAlloc_2441_, 1, v___x_2438_);
lean_ctor_set(v_reuseFailAlloc_2441_, 2, v_auxDeclToFullName_2423_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
v___jp_2443_:
{
lean_object* v___x_2445_; lean_object* v_index_2446_; 
lean_inc_ref(v_decl_2432_);
v___x_2445_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2421_, v___y_2444_, v_decl_2432_);
v_index_2446_ = lean_ctor_get(v_decl_2432_, 0);
lean_inc(v_index_2446_);
v___y_2434_ = v___x_2445_;
v___y_2435_ = v_index_2446_;
goto v___jp_2433_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_renameUserName___boxed(lean_object* v_lctx_2453_, lean_object* v_fromName_2454_, lean_object* v_toName_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l_Lean_LocalContext_renameUserName(v_lctx_2453_, v_fromName_2454_, v_toName_2455_);
lean_dec(v_fromName_2454_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_modifyLocalDecl(lean_object* v_lctx_2459_, lean_object* v_fvarId_2460_, lean_object* v_f_2461_){
_start:
{
lean_object* v_fvarIdToDecl_2462_; lean_object* v_decls_2463_; lean_object* v_auxDeclToFullName_2464_; lean_object* v___x_2465_; 
v_fvarIdToDecl_2462_ = lean_ctor_get(v_lctx_2459_, 0);
v_decls_2463_ = lean_ctor_get(v_lctx_2459_, 1);
v_auxDeclToFullName_2464_ = lean_ctor_get(v_lctx_2459_, 2);
lean_inc_ref(v_lctx_2459_);
v___x_2465_ = lean_local_ctx_find(v_lctx_2459_, v_fvarId_2460_);
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_dec_ref(v_f_2461_);
return v_lctx_2459_;
}
else
{
lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2492_; 
lean_inc(v_auxDeclToFullName_2464_);
lean_inc_ref(v_decls_2463_);
lean_inc_ref(v_fvarIdToDecl_2462_);
v_isSharedCheck_2492_ = !lean_is_exclusive(v_lctx_2459_);
if (v_isSharedCheck_2492_ == 0)
{
lean_object* v_unused_2493_; lean_object* v_unused_2494_; lean_object* v_unused_2495_; 
v_unused_2493_ = lean_ctor_get(v_lctx_2459_, 2);
lean_dec(v_unused_2493_);
v_unused_2494_ = lean_ctor_get(v_lctx_2459_, 1);
lean_dec(v_unused_2494_);
v_unused_2495_ = lean_ctor_get(v_lctx_2459_, 0);
lean_dec(v_unused_2495_);
v___x_2467_ = v_lctx_2459_;
v_isShared_2468_ = v_isSharedCheck_2492_;
goto v_resetjp_2466_;
}
else
{
lean_dec(v_lctx_2459_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2492_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v_val_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2491_; 
v_val_2469_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2471_ = v___x_2465_;
v_isShared_2472_ = v_isSharedCheck_2491_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_val_2469_);
lean_dec(v___x_2465_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2491_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v_decl_2475_; lean_object* v___y_2477_; lean_object* v___y_2478_; lean_object* v___y_2487_; lean_object* v_fvarId_2490_; 
v___x_2473_ = ((lean_object*)(l_Lean_LocalContext_modifyLocalDecl___closed__0));
v___x_2474_ = ((lean_object*)(l_Lean_LocalContext_modifyLocalDecl___closed__1));
v_decl_2475_ = lean_apply_1(v_f_2461_, v_val_2469_);
v_fvarId_2490_ = lean_ctor_get(v_decl_2475_, 1);
lean_inc(v_fvarId_2490_);
v___y_2487_ = v_fvarId_2490_;
goto v___jp_2486_;
v___jp_2476_:
{
lean_object* v___x_2480_; 
if (v_isShared_2472_ == 0)
{
lean_ctor_set(v___x_2471_, 0, v_decl_2475_);
v___x_2480_ = v___x_2471_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_decl_2475_);
v___x_2480_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
lean_object* v___x_2481_; lean_object* v___x_2483_; 
v___x_2481_ = l_Lean_PersistentArray_set___redArg(v_decls_2463_, v___y_2478_, v___x_2480_);
lean_dec(v___y_2478_);
if (v_isShared_2468_ == 0)
{
lean_ctor_set(v___x_2467_, 1, v___x_2481_);
lean_ctor_set(v___x_2467_, 0, v___y_2477_);
v___x_2483_ = v___x_2467_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v___y_2477_);
lean_ctor_set(v_reuseFailAlloc_2484_, 1, v___x_2481_);
lean_ctor_set(v_reuseFailAlloc_2484_, 2, v_auxDeclToFullName_2464_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
v___jp_2486_:
{
lean_object* v___x_2488_; lean_object* v_index_2489_; 
lean_inc_ref(v_decl_2475_);
v___x_2488_ = l_Lean_PersistentHashMap_insert___redArg(v___x_2473_, v___x_2474_, v_fvarIdToDecl_2462_, v___y_2487_, v_decl_2475_);
v_index_2489_ = lean_ctor_get(v_decl_2475_, 0);
lean_inc(v_index_2489_);
v___y_2477_ = v___x_2488_;
v___y_2478_ = v_index_2489_;
goto v___jp_2476_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(lean_object* v_f_2496_, lean_object* v_as_2497_, size_t v_i_2498_, size_t v_stop_2499_, lean_object* v_b_2500_){
_start:
{
lean_object* v___y_2502_; uint8_t v___x_2506_; 
v___x_2506_ = lean_usize_dec_eq(v_i_2498_, v_stop_2499_);
if (v___x_2506_ == 0)
{
lean_object* v___x_2507_; 
v___x_2507_ = lean_array_uget(v_as_2497_, v_i_2498_);
if (lean_obj_tag(v___x_2507_) == 0)
{
v___y_2502_ = v_b_2500_;
goto v___jp_2501_;
}
else
{
lean_object* v_val_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2535_; 
v_val_2508_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2510_ = v___x_2507_;
v_isShared_2511_ = v_isSharedCheck_2535_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_val_2508_);
lean_dec(v___x_2507_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2535_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v_fvarIdToDecl_2512_; lean_object* v_decls_2513_; lean_object* v_auxDeclToFullName_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2534_; 
v_fvarIdToDecl_2512_ = lean_ctor_get(v_b_2500_, 0);
v_decls_2513_ = lean_ctor_get(v_b_2500_, 1);
v_auxDeclToFullName_2514_ = lean_ctor_get(v_b_2500_, 2);
v_isSharedCheck_2534_ = !lean_is_exclusive(v_b_2500_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2516_ = v_b_2500_;
v_isShared_2517_ = v_isSharedCheck_2534_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_auxDeclToFullName_2514_);
lean_inc(v_decls_2513_);
lean_inc(v_fvarIdToDecl_2512_);
lean_dec(v_b_2500_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2534_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v_decl_2518_; lean_object* v___y_2520_; lean_object* v___y_2521_; lean_object* v___y_2530_; lean_object* v_fvarId_2533_; 
lean_inc_ref(v_f_2496_);
v_decl_2518_ = lean_apply_1(v_f_2496_, v_val_2508_);
v_fvarId_2533_ = lean_ctor_get(v_decl_2518_, 1);
lean_inc(v_fvarId_2533_);
v___y_2530_ = v_fvarId_2533_;
goto v___jp_2529_;
v___jp_2519_:
{
lean_object* v___x_2523_; 
if (v_isShared_2511_ == 0)
{
lean_ctor_set(v___x_2510_, 0, v_decl_2518_);
v___x_2523_ = v___x_2510_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_decl_2518_);
v___x_2523_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
lean_object* v___x_2524_; lean_object* v___x_2526_; 
v___x_2524_ = l_Lean_PersistentArray_set___redArg(v_decls_2513_, v___y_2521_, v___x_2523_);
lean_dec(v___y_2521_);
if (v_isShared_2517_ == 0)
{
lean_ctor_set(v___x_2516_, 1, v___x_2524_);
lean_ctor_set(v___x_2516_, 0, v___y_2520_);
v___x_2526_ = v___x_2516_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v___y_2520_);
lean_ctor_set(v_reuseFailAlloc_2527_, 1, v___x_2524_);
lean_ctor_set(v_reuseFailAlloc_2527_, 2, v_auxDeclToFullName_2514_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
v___y_2502_ = v___x_2526_;
goto v___jp_2501_;
}
}
}
v___jp_2529_:
{
lean_object* v___x_2531_; lean_object* v_index_2532_; 
lean_inc_ref(v_decl_2518_);
v___x_2531_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2512_, v___y_2530_, v_decl_2518_);
v_index_2532_ = lean_ctor_get(v_decl_2518_, 0);
lean_inc(v_index_2532_);
v___y_2520_ = v___x_2531_;
v___y_2521_ = v_index_2532_;
goto v___jp_2519_;
}
}
}
}
}
else
{
lean_dec_ref(v_f_2496_);
return v_b_2500_;
}
v___jp_2501_:
{
size_t v___x_2503_; size_t v___x_2504_; 
v___x_2503_ = ((size_t)1ULL);
v___x_2504_ = lean_usize_add(v_i_2498_, v___x_2503_);
v_i_2498_ = v___x_2504_;
v_b_2500_ = v___y_2502_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1___boxed(lean_object* v_f_2536_, lean_object* v_as_2537_, lean_object* v_i_2538_, lean_object* v_stop_2539_, lean_object* v_b_2540_){
_start:
{
size_t v_i_boxed_2541_; size_t v_stop_boxed_2542_; lean_object* v_res_2543_; 
v_i_boxed_2541_ = lean_unbox_usize(v_i_2538_);
lean_dec(v_i_2538_);
v_stop_boxed_2542_ = lean_unbox_usize(v_stop_2539_);
lean_dec(v_stop_2539_);
v_res_2543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2536_, v_as_2537_, v_i_boxed_2541_, v_stop_boxed_2542_, v_b_2540_);
lean_dec_ref(v_as_2537_);
return v_res_2543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(lean_object* v_f_2544_, lean_object* v_x_2545_, lean_object* v_x_2546_){
_start:
{
if (lean_obj_tag(v_x_2545_) == 0)
{
lean_object* v_cs_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; uint8_t v___x_2550_; 
v_cs_2547_ = lean_ctor_get(v_x_2545_, 0);
v___x_2548_ = lean_unsigned_to_nat(0u);
v___x_2549_ = lean_array_get_size(v_cs_2547_);
v___x_2550_ = lean_nat_dec_lt(v___x_2548_, v___x_2549_);
if (v___x_2550_ == 0)
{
lean_dec_ref(v_f_2544_);
return v_x_2546_;
}
else
{
uint8_t v___x_2551_; 
v___x_2551_ = lean_nat_dec_le(v___x_2549_, v___x_2549_);
if (v___x_2551_ == 0)
{
if (v___x_2550_ == 0)
{
lean_dec_ref(v_f_2544_);
return v_x_2546_;
}
else
{
size_t v___x_2552_; size_t v___x_2553_; lean_object* v___x_2554_; 
v___x_2552_ = ((size_t)0ULL);
v___x_2553_ = lean_usize_of_nat(v___x_2549_);
v___x_2554_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2544_, v_cs_2547_, v___x_2552_, v___x_2553_, v_x_2546_);
return v___x_2554_;
}
}
else
{
size_t v___x_2555_; size_t v___x_2556_; lean_object* v___x_2557_; 
v___x_2555_ = ((size_t)0ULL);
v___x_2556_ = lean_usize_of_nat(v___x_2549_);
v___x_2557_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2544_, v_cs_2547_, v___x_2555_, v___x_2556_, v_x_2546_);
return v___x_2557_;
}
}
}
else
{
lean_object* v_vs_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; uint8_t v___x_2561_; 
v_vs_2558_ = lean_ctor_get(v_x_2545_, 0);
v___x_2559_ = lean_unsigned_to_nat(0u);
v___x_2560_ = lean_array_get_size(v_vs_2558_);
v___x_2561_ = lean_nat_dec_lt(v___x_2559_, v___x_2560_);
if (v___x_2561_ == 0)
{
lean_dec_ref(v_f_2544_);
return v_x_2546_;
}
else
{
uint8_t v___x_2562_; 
v___x_2562_ = lean_nat_dec_le(v___x_2560_, v___x_2560_);
if (v___x_2562_ == 0)
{
if (v___x_2561_ == 0)
{
lean_dec_ref(v_f_2544_);
return v_x_2546_;
}
else
{
size_t v___x_2563_; size_t v___x_2564_; lean_object* v___x_2565_; 
v___x_2563_ = ((size_t)0ULL);
v___x_2564_ = lean_usize_of_nat(v___x_2560_);
v___x_2565_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2544_, v_vs_2558_, v___x_2563_, v___x_2564_, v_x_2546_);
return v___x_2565_;
}
}
else
{
size_t v___x_2566_; size_t v___x_2567_; lean_object* v___x_2568_; 
v___x_2566_ = ((size_t)0ULL);
v___x_2567_ = lean_usize_of_nat(v___x_2560_);
v___x_2568_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2544_, v_vs_2558_, v___x_2566_, v___x_2567_, v_x_2546_);
return v___x_2568_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(lean_object* v_f_2569_, lean_object* v_as_2570_, size_t v_i_2571_, size_t v_stop_2572_, lean_object* v_b_2573_){
_start:
{
uint8_t v___x_2574_; 
v___x_2574_ = lean_usize_dec_eq(v_i_2571_, v_stop_2572_);
if (v___x_2574_ == 0)
{
lean_object* v___x_2575_; lean_object* v___x_2576_; size_t v___x_2577_; size_t v___x_2578_; 
v___x_2575_ = lean_array_uget_borrowed(v_as_2570_, v_i_2571_);
lean_inc_ref(v_f_2569_);
v___x_2576_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(v_f_2569_, v___x_2575_, v_b_2573_);
v___x_2577_ = ((size_t)1ULL);
v___x_2578_ = lean_usize_add(v_i_2571_, v___x_2577_);
v_i_2571_ = v___x_2578_;
v_b_2573_ = v___x_2576_;
goto _start;
}
else
{
lean_dec_ref(v_f_2569_);
return v_b_2573_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1___boxed(lean_object* v_f_2580_, lean_object* v_as_2581_, lean_object* v_i_2582_, lean_object* v_stop_2583_, lean_object* v_b_2584_){
_start:
{
size_t v_i_boxed_2585_; size_t v_stop_boxed_2586_; lean_object* v_res_2587_; 
v_i_boxed_2585_ = lean_unbox_usize(v_i_2582_);
lean_dec(v_i_2582_);
v_stop_boxed_2586_ = lean_unbox_usize(v_stop_2583_);
lean_dec(v_stop_2583_);
v_res_2587_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2580_, v_as_2581_, v_i_boxed_2585_, v_stop_boxed_2586_, v_b_2584_);
lean_dec_ref(v_as_2581_);
return v_res_2587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2___boxed(lean_object* v_f_2588_, lean_object* v_x_2589_, lean_object* v_x_2590_){
_start:
{
lean_object* v_res_2591_; 
v_res_2591_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(v_f_2588_, v_x_2589_, v_x_2590_);
lean_dec_ref(v_x_2589_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(lean_object* v_f_2592_, lean_object* v_x_2593_, size_t v_x_2594_, size_t v_x_2595_, lean_object* v_x_2596_){
_start:
{
if (lean_obj_tag(v_x_2593_) == 0)
{
lean_object* v_cs_2597_; lean_object* v___x_2598_; size_t v___x_2599_; lean_object* v_j_2600_; lean_object* v___x_2601_; size_t v___x_2602_; size_t v___x_2603_; size_t v___x_2604_; size_t v___x_2605_; size_t v___x_2606_; size_t v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; uint8_t v___x_2612_; 
v_cs_2597_ = lean_ctor_get(v_x_2593_, 0);
v___x_2598_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0);
v___x_2599_ = lean_usize_shift_right(v_x_2594_, v_x_2595_);
v_j_2600_ = lean_usize_to_nat(v___x_2599_);
v___x_2601_ = lean_array_get_borrowed(v___x_2598_, v_cs_2597_, v_j_2600_);
v___x_2602_ = ((size_t)1ULL);
v___x_2603_ = lean_usize_shift_left(v___x_2602_, v_x_2595_);
v___x_2604_ = lean_usize_sub(v___x_2603_, v___x_2602_);
v___x_2605_ = lean_usize_land(v_x_2594_, v___x_2604_);
v___x_2606_ = ((size_t)5ULL);
v___x_2607_ = lean_usize_sub(v_x_2595_, v___x_2606_);
lean_inc_ref(v_f_2592_);
v___x_2608_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(v_f_2592_, v___x_2601_, v___x_2605_, v___x_2607_, v_x_2596_);
v___x_2609_ = lean_unsigned_to_nat(1u);
v___x_2610_ = lean_nat_add(v_j_2600_, v___x_2609_);
lean_dec(v_j_2600_);
v___x_2611_ = lean_array_get_size(v_cs_2597_);
v___x_2612_ = lean_nat_dec_lt(v___x_2610_, v___x_2611_);
if (v___x_2612_ == 0)
{
lean_dec(v___x_2610_);
lean_dec_ref(v_f_2592_);
return v___x_2608_;
}
else
{
uint8_t v___x_2613_; 
v___x_2613_ = lean_nat_dec_le(v___x_2611_, v___x_2611_);
if (v___x_2613_ == 0)
{
if (v___x_2612_ == 0)
{
lean_dec(v___x_2610_);
lean_dec_ref(v_f_2592_);
return v___x_2608_;
}
else
{
size_t v___x_2614_; size_t v___x_2615_; lean_object* v___x_2616_; 
v___x_2614_ = lean_usize_of_nat(v___x_2610_);
lean_dec(v___x_2610_);
v___x_2615_ = lean_usize_of_nat(v___x_2611_);
v___x_2616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2592_, v_cs_2597_, v___x_2614_, v___x_2615_, v___x_2608_);
return v___x_2616_;
}
}
else
{
size_t v___x_2617_; size_t v___x_2618_; lean_object* v___x_2619_; 
v___x_2617_ = lean_usize_of_nat(v___x_2610_);
lean_dec(v___x_2610_);
v___x_2618_ = lean_usize_of_nat(v___x_2611_);
v___x_2619_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2592_, v_cs_2597_, v___x_2617_, v___x_2618_, v___x_2608_);
return v___x_2619_;
}
}
}
else
{
lean_object* v_vs_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; uint8_t v___x_2623_; 
v_vs_2620_ = lean_ctor_get(v_x_2593_, 0);
v___x_2621_ = lean_usize_to_nat(v_x_2594_);
v___x_2622_ = lean_array_get_size(v_vs_2620_);
v___x_2623_ = lean_nat_dec_lt(v___x_2621_, v___x_2622_);
if (v___x_2623_ == 0)
{
lean_dec(v___x_2621_);
lean_dec_ref(v_f_2592_);
return v_x_2596_;
}
else
{
uint8_t v___x_2624_; 
v___x_2624_ = lean_nat_dec_le(v___x_2622_, v___x_2622_);
if (v___x_2624_ == 0)
{
if (v___x_2623_ == 0)
{
lean_dec(v___x_2621_);
lean_dec_ref(v_f_2592_);
return v_x_2596_;
}
else
{
size_t v___x_2625_; size_t v___x_2626_; lean_object* v___x_2627_; 
v___x_2625_ = lean_usize_of_nat(v___x_2621_);
lean_dec(v___x_2621_);
v___x_2626_ = lean_usize_of_nat(v___x_2622_);
v___x_2627_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2592_, v_vs_2620_, v___x_2625_, v___x_2626_, v_x_2596_);
return v___x_2627_;
}
}
else
{
size_t v___x_2628_; size_t v___x_2629_; lean_object* v___x_2630_; 
v___x_2628_ = lean_usize_of_nat(v___x_2621_);
lean_dec(v___x_2621_);
v___x_2629_ = lean_usize_of_nat(v___x_2622_);
v___x_2630_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2592_, v_vs_2620_, v___x_2628_, v___x_2629_, v_x_2596_);
return v___x_2630_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0___boxed(lean_object* v_f_2631_, lean_object* v_x_2632_, lean_object* v_x_2633_, lean_object* v_x_2634_, lean_object* v_x_2635_){
_start:
{
size_t v_x_1859__boxed_2636_; size_t v_x_1860__boxed_2637_; lean_object* v_res_2638_; 
v_x_1859__boxed_2636_ = lean_unbox_usize(v_x_2633_);
lean_dec(v_x_2633_);
v_x_1860__boxed_2637_ = lean_unbox_usize(v_x_2634_);
lean_dec(v_x_2634_);
v_res_2638_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(v_f_2631_, v_x_2632_, v_x_1859__boxed_2636_, v_x_1860__boxed_2637_, v_x_2635_);
lean_dec_ref(v_x_2632_);
return v_res_2638_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0(lean_object* v_f_2639_, lean_object* v_t_2640_, lean_object* v_init_2641_, lean_object* v_start_2642_){
_start:
{
lean_object* v___x_2643_; uint8_t v___x_2644_; 
v___x_2643_ = lean_unsigned_to_nat(0u);
v___x_2644_ = lean_nat_dec_eq(v_start_2642_, v___x_2643_);
if (v___x_2644_ == 0)
{
lean_object* v_root_2645_; lean_object* v_tail_2646_; size_t v_shift_2647_; lean_object* v_tailOff_2648_; uint8_t v___x_2649_; 
v_root_2645_ = lean_ctor_get(v_t_2640_, 0);
v_tail_2646_ = lean_ctor_get(v_t_2640_, 1);
v_shift_2647_ = lean_ctor_get_usize(v_t_2640_, 4);
v_tailOff_2648_ = lean_ctor_get(v_t_2640_, 3);
v___x_2649_ = lean_nat_dec_le(v_tailOff_2648_, v_start_2642_);
if (v___x_2649_ == 0)
{
size_t v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; uint8_t v___x_2653_; 
v___x_2650_ = lean_usize_of_nat(v_start_2642_);
lean_inc_ref(v_f_2639_);
v___x_2651_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(v_f_2639_, v_root_2645_, v___x_2650_, v_shift_2647_, v_init_2641_);
v___x_2652_ = lean_array_get_size(v_tail_2646_);
v___x_2653_ = lean_nat_dec_lt(v___x_2643_, v___x_2652_);
if (v___x_2653_ == 0)
{
lean_dec_ref(v_f_2639_);
return v___x_2651_;
}
else
{
uint8_t v___x_2654_; 
v___x_2654_ = lean_nat_dec_le(v___x_2652_, v___x_2652_);
if (v___x_2654_ == 0)
{
if (v___x_2653_ == 0)
{
lean_dec_ref(v_f_2639_);
return v___x_2651_;
}
else
{
size_t v___x_2655_; size_t v___x_2656_; lean_object* v___x_2657_; 
v___x_2655_ = ((size_t)0ULL);
v___x_2656_ = lean_usize_of_nat(v___x_2652_);
v___x_2657_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2639_, v_tail_2646_, v___x_2655_, v___x_2656_, v___x_2651_);
return v___x_2657_;
}
}
else
{
size_t v___x_2658_; size_t v___x_2659_; lean_object* v___x_2660_; 
v___x_2658_ = ((size_t)0ULL);
v___x_2659_ = lean_usize_of_nat(v___x_2652_);
v___x_2660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2639_, v_tail_2646_, v___x_2658_, v___x_2659_, v___x_2651_);
return v___x_2660_;
}
}
}
else
{
lean_object* v___x_2661_; lean_object* v___x_2662_; uint8_t v___x_2663_; 
v___x_2661_ = lean_nat_sub(v_start_2642_, v_tailOff_2648_);
v___x_2662_ = lean_array_get_size(v_tail_2646_);
v___x_2663_ = lean_nat_dec_lt(v___x_2661_, v___x_2662_);
if (v___x_2663_ == 0)
{
lean_dec(v___x_2661_);
lean_dec_ref(v_f_2639_);
return v_init_2641_;
}
else
{
uint8_t v___x_2664_; 
v___x_2664_ = lean_nat_dec_le(v___x_2662_, v___x_2662_);
if (v___x_2664_ == 0)
{
if (v___x_2663_ == 0)
{
lean_dec(v___x_2661_);
lean_dec_ref(v_f_2639_);
return v_init_2641_;
}
else
{
size_t v___x_2665_; size_t v___x_2666_; lean_object* v___x_2667_; 
v___x_2665_ = lean_usize_of_nat(v___x_2661_);
lean_dec(v___x_2661_);
v___x_2666_ = lean_usize_of_nat(v___x_2662_);
v___x_2667_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2639_, v_tail_2646_, v___x_2665_, v___x_2666_, v_init_2641_);
return v___x_2667_;
}
}
else
{
size_t v___x_2668_; size_t v___x_2669_; lean_object* v___x_2670_; 
v___x_2668_ = lean_usize_of_nat(v___x_2661_);
lean_dec(v___x_2661_);
v___x_2669_ = lean_usize_of_nat(v___x_2662_);
v___x_2670_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2639_, v_tail_2646_, v___x_2668_, v___x_2669_, v_init_2641_);
return v___x_2670_;
}
}
}
}
else
{
lean_object* v_root_2671_; lean_object* v_tail_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; uint8_t v___x_2675_; 
v_root_2671_ = lean_ctor_get(v_t_2640_, 0);
v_tail_2672_ = lean_ctor_get(v_t_2640_, 1);
lean_inc_ref(v_f_2639_);
v___x_2673_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(v_f_2639_, v_root_2671_, v_init_2641_);
v___x_2674_ = lean_array_get_size(v_tail_2672_);
v___x_2675_ = lean_nat_dec_lt(v___x_2643_, v___x_2674_);
if (v___x_2675_ == 0)
{
lean_dec_ref(v_f_2639_);
return v___x_2673_;
}
else
{
uint8_t v___x_2676_; 
v___x_2676_ = lean_nat_dec_le(v___x_2674_, v___x_2674_);
if (v___x_2676_ == 0)
{
if (v___x_2675_ == 0)
{
lean_dec_ref(v_f_2639_);
return v___x_2673_;
}
else
{
size_t v___x_2677_; size_t v___x_2678_; lean_object* v___x_2679_; 
v___x_2677_ = ((size_t)0ULL);
v___x_2678_ = lean_usize_of_nat(v___x_2674_);
v___x_2679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2639_, v_tail_2672_, v___x_2677_, v___x_2678_, v___x_2673_);
return v___x_2679_;
}
}
else
{
size_t v___x_2680_; size_t v___x_2681_; lean_object* v___x_2682_; 
v___x_2680_ = ((size_t)0ULL);
v___x_2681_ = lean_usize_of_nat(v___x_2674_);
v___x_2682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2639_, v_tail_2672_, v___x_2680_, v___x_2681_, v___x_2673_);
return v___x_2682_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0___boxed(lean_object* v_f_2683_, lean_object* v_t_2684_, lean_object* v_init_2685_, lean_object* v_start_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0(v_f_2683_, v_t_2684_, v_init_2685_, v_start_2686_);
lean_dec(v_start_2686_);
lean_dec_ref(v_t_2684_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_modifyLocalDecls(lean_object* v_lctx_2688_, lean_object* v_f_2689_){
_start:
{
lean_object* v_decls_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v_decls_2690_ = lean_ctor_get(v_lctx_2688_, 1);
lean_inc_ref(v_decls_2690_);
v___x_2691_ = lean_unsigned_to_nat(0u);
v___x_2692_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0(v_f_2689_, v_decls_2690_, v_lctx_2688_, v___x_2691_);
lean_dec_ref(v_decls_2690_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setKind(lean_object* v_lctx_2693_, lean_object* v_fvarId_2694_, uint8_t v_kind_2695_){
_start:
{
lean_object* v_fvarIdToDecl_2696_; lean_object* v_decls_2697_; lean_object* v_auxDeclToFullName_2698_; lean_object* v___x_2699_; 
v_fvarIdToDecl_2696_ = lean_ctor_get(v_lctx_2693_, 0);
v_decls_2697_ = lean_ctor_get(v_lctx_2693_, 1);
v_auxDeclToFullName_2698_ = lean_ctor_get(v_lctx_2693_, 2);
lean_inc_ref(v_lctx_2693_);
v___x_2699_ = lean_local_ctx_find(v_lctx_2693_, v_fvarId_2694_);
if (lean_obj_tag(v___x_2699_) == 0)
{
return v_lctx_2693_;
}
else
{
lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2724_; 
lean_inc(v_auxDeclToFullName_2698_);
lean_inc_ref(v_decls_2697_);
lean_inc_ref(v_fvarIdToDecl_2696_);
v_isSharedCheck_2724_ = !lean_is_exclusive(v_lctx_2693_);
if (v_isSharedCheck_2724_ == 0)
{
lean_object* v_unused_2725_; lean_object* v_unused_2726_; lean_object* v_unused_2727_; 
v_unused_2725_ = lean_ctor_get(v_lctx_2693_, 2);
lean_dec(v_unused_2725_);
v_unused_2726_ = lean_ctor_get(v_lctx_2693_, 1);
lean_dec(v_unused_2726_);
v_unused_2727_ = lean_ctor_get(v_lctx_2693_, 0);
lean_dec(v_unused_2727_);
v___x_2701_ = v_lctx_2693_;
v_isShared_2702_ = v_isSharedCheck_2724_;
goto v_resetjp_2700_;
}
else
{
lean_dec(v_lctx_2693_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2724_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v_val_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2723_; 
v_val_2703_ = lean_ctor_get(v___x_2699_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2699_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2705_ = v___x_2699_;
v_isShared_2706_ = v_isSharedCheck_2723_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_val_2703_);
lean_dec(v___x_2699_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2723_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v_decl_2707_; lean_object* v___y_2709_; lean_object* v___y_2710_; lean_object* v___y_2719_; lean_object* v_fvarId_2722_; 
v_decl_2707_ = l_Lean_LocalDecl_setKind(v_val_2703_, v_kind_2695_);
v_fvarId_2722_ = lean_ctor_get(v_decl_2707_, 1);
lean_inc(v_fvarId_2722_);
v___y_2719_ = v_fvarId_2722_;
goto v___jp_2718_;
v___jp_2708_:
{
lean_object* v___x_2712_; 
if (v_isShared_2706_ == 0)
{
lean_ctor_set(v___x_2705_, 0, v_decl_2707_);
v___x_2712_ = v___x_2705_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_decl_2707_);
v___x_2712_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
lean_object* v___x_2713_; lean_object* v___x_2715_; 
v___x_2713_ = l_Lean_PersistentArray_set___redArg(v_decls_2697_, v___y_2710_, v___x_2712_);
lean_dec(v___y_2710_);
if (v_isShared_2702_ == 0)
{
lean_ctor_set(v___x_2701_, 1, v___x_2713_);
lean_ctor_set(v___x_2701_, 0, v___y_2709_);
v___x_2715_ = v___x_2701_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v___y_2709_);
lean_ctor_set(v_reuseFailAlloc_2716_, 1, v___x_2713_);
lean_ctor_set(v_reuseFailAlloc_2716_, 2, v_auxDeclToFullName_2698_);
v___x_2715_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
return v___x_2715_;
}
}
}
v___jp_2718_:
{
lean_object* v___x_2720_; lean_object* v_index_2721_; 
lean_inc_ref(v_decl_2707_);
v___x_2720_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2696_, v___y_2719_, v_decl_2707_);
v_index_2721_ = lean_ctor_get(v_decl_2707_, 0);
lean_inc(v_index_2721_);
v___y_2709_ = v___x_2720_;
v___y_2710_ = v_index_2721_;
goto v___jp_2708_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setKind___boxed(lean_object* v_lctx_2728_, lean_object* v_fvarId_2729_, lean_object* v_kind_2730_){
_start:
{
uint8_t v_kind_boxed_2731_; lean_object* v_res_2732_; 
v_kind_boxed_2731_ = lean_unbox(v_kind_2730_);
v_res_2732_ = l_Lean_LocalContext_setKind(v_lctx_2728_, v_fvarId_2729_, v_kind_boxed_2731_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setBinderInfo(lean_object* v_lctx_2733_, lean_object* v_fvarId_2734_, uint8_t v_bi_2735_){
_start:
{
lean_object* v_fvarIdToDecl_2736_; lean_object* v_decls_2737_; lean_object* v_auxDeclToFullName_2738_; lean_object* v___x_2739_; 
v_fvarIdToDecl_2736_ = lean_ctor_get(v_lctx_2733_, 0);
v_decls_2737_ = lean_ctor_get(v_lctx_2733_, 1);
v_auxDeclToFullName_2738_ = lean_ctor_get(v_lctx_2733_, 2);
lean_inc_ref(v_lctx_2733_);
v___x_2739_ = lean_local_ctx_find(v_lctx_2733_, v_fvarId_2734_);
if (lean_obj_tag(v___x_2739_) == 0)
{
return v_lctx_2733_;
}
else
{
lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2764_; 
lean_inc(v_auxDeclToFullName_2738_);
lean_inc_ref(v_decls_2737_);
lean_inc_ref(v_fvarIdToDecl_2736_);
v_isSharedCheck_2764_ = !lean_is_exclusive(v_lctx_2733_);
if (v_isSharedCheck_2764_ == 0)
{
lean_object* v_unused_2765_; lean_object* v_unused_2766_; lean_object* v_unused_2767_; 
v_unused_2765_ = lean_ctor_get(v_lctx_2733_, 2);
lean_dec(v_unused_2765_);
v_unused_2766_ = lean_ctor_get(v_lctx_2733_, 1);
lean_dec(v_unused_2766_);
v_unused_2767_ = lean_ctor_get(v_lctx_2733_, 0);
lean_dec(v_unused_2767_);
v___x_2741_ = v_lctx_2733_;
v_isShared_2742_ = v_isSharedCheck_2764_;
goto v_resetjp_2740_;
}
else
{
lean_dec(v_lctx_2733_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2764_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v_val_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2763_; 
v_val_2743_ = lean_ctor_get(v___x_2739_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2745_ = v___x_2739_;
v_isShared_2746_ = v_isSharedCheck_2763_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_val_2743_);
lean_dec(v___x_2739_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2763_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v_decl_2747_; lean_object* v___y_2749_; lean_object* v___y_2750_; lean_object* v___y_2759_; lean_object* v_fvarId_2762_; 
v_decl_2747_ = l_Lean_LocalDecl_setBinderInfo(v_val_2743_, v_bi_2735_);
v_fvarId_2762_ = lean_ctor_get(v_decl_2747_, 1);
lean_inc(v_fvarId_2762_);
v___y_2759_ = v_fvarId_2762_;
goto v___jp_2758_;
v___jp_2748_:
{
lean_object* v___x_2752_; 
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 0, v_decl_2747_);
v___x_2752_ = v___x_2745_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_decl_2747_);
v___x_2752_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
lean_object* v___x_2753_; lean_object* v___x_2755_; 
v___x_2753_ = l_Lean_PersistentArray_set___redArg(v_decls_2737_, v___y_2750_, v___x_2752_);
lean_dec(v___y_2750_);
if (v_isShared_2742_ == 0)
{
lean_ctor_set(v___x_2741_, 1, v___x_2753_);
lean_ctor_set(v___x_2741_, 0, v___y_2749_);
v___x_2755_ = v___x_2741_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v___y_2749_);
lean_ctor_set(v_reuseFailAlloc_2756_, 1, v___x_2753_);
lean_ctor_set(v_reuseFailAlloc_2756_, 2, v_auxDeclToFullName_2738_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
}
v___jp_2758_:
{
lean_object* v___x_2760_; lean_object* v_index_2761_; 
lean_inc_ref(v_decl_2747_);
v___x_2760_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2736_, v___y_2759_, v_decl_2747_);
v_index_2761_ = lean_ctor_get(v_decl_2747_, 0);
lean_inc(v_index_2761_);
v___y_2749_ = v___x_2760_;
v___y_2750_ = v_index_2761_;
goto v___jp_2748_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setBinderInfo___boxed(lean_object* v_lctx_2768_, lean_object* v_fvarId_2769_, lean_object* v_bi_2770_){
_start:
{
uint8_t v_bi_boxed_2771_; lean_object* v_res_2772_; 
v_bi_boxed_2771_ = lean_unbox(v_bi_2770_);
v_res_2772_ = l_Lean_LocalContext_setBinderInfo(v_lctx_2768_, v_fvarId_2769_, v_bi_boxed_2771_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_num_indices(lean_object* v_lctx_2773_){
_start:
{
lean_object* v_decls_2774_; lean_object* v_size_2775_; 
v_decls_2774_ = lean_ctor_get(v_lctx_2773_, 1);
lean_inc_ref(v_decls_2774_);
lean_dec_ref(v_lctx_2773_);
v_size_2775_ = lean_ctor_get(v_decls_2774_, 2);
lean_inc(v_size_2775_);
lean_dec_ref(v_decls_2774_);
return v_size_2775_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getAt_x3f(lean_object* v_lctx_2776_, lean_object* v_i_2777_){
_start:
{
lean_object* v_decls_2778_; lean_object* v_size_2779_; lean_object* v___x_2780_; uint8_t v___x_2781_; 
v_decls_2778_ = lean_ctor_get(v_lctx_2776_, 1);
lean_inc_ref(v_decls_2778_);
lean_dec_ref(v_lctx_2776_);
v_size_2779_ = lean_ctor_get(v_decls_2778_, 2);
v___x_2780_ = lean_box(0);
v___x_2781_ = lean_nat_dec_lt(v_i_2777_, v_size_2779_);
if (v___x_2781_ == 0)
{
lean_object* v___x_2782_; 
lean_dec_ref(v_decls_2778_);
v___x_2782_ = l_outOfBounds___redArg(v___x_2780_);
return v___x_2782_;
}
else
{
lean_object* v___x_2783_; 
v___x_2783_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2780_, v_decls_2778_, v_i_2777_);
return v___x_2783_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getAt_x3f___boxed(lean_object* v_lctx_2784_, lean_object* v_i_2785_){
_start:
{
lean_object* v_res_2786_; 
v_res_2786_ = l_Lean_LocalContext_getAt_x3f(v_lctx_2784_, v_i_2785_);
lean_dec(v_i_2785_);
return v_res_2786_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg___lam__0(lean_object* v_toPure_2787_, lean_object* v_f_2788_, lean_object* v_b_2789_, lean_object* v_decl_2790_){
_start:
{
if (lean_obj_tag(v_decl_2790_) == 0)
{
lean_object* v___x_2791_; 
lean_dec(v_f_2788_);
v___x_2791_ = lean_apply_2(v_toPure_2787_, lean_box(0), v_b_2789_);
return v___x_2791_;
}
else
{
lean_object* v_val_2792_; lean_object* v___x_2793_; 
lean_dec(v_toPure_2787_);
v_val_2792_ = lean_ctor_get(v_decl_2790_, 0);
lean_inc(v_val_2792_);
lean_dec_ref(v_decl_2790_);
v___x_2793_ = lean_apply_2(v_f_2788_, v_b_2789_, v_val_2792_);
return v___x_2793_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg(lean_object* v_inst_2794_, lean_object* v_lctx_2795_, lean_object* v_f_2796_, lean_object* v_init_2797_, lean_object* v_start_2798_){
_start:
{
lean_object* v_toApplicative_2799_; lean_object* v_decls_2800_; lean_object* v_toPure_2801_; lean_object* v___f_2802_; lean_object* v___x_2803_; 
v_toApplicative_2799_ = lean_ctor_get(v_inst_2794_, 0);
v_decls_2800_ = lean_ctor_get(v_lctx_2795_, 1);
lean_inc_ref(v_decls_2800_);
lean_dec_ref(v_lctx_2795_);
v_toPure_2801_ = lean_ctor_get(v_toApplicative_2799_, 1);
lean_inc(v_toPure_2801_);
v___f_2802_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldlM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2802_, 0, v_toPure_2801_);
lean_closure_set(v___f_2802_, 1, v_f_2796_);
v___x_2803_ = l_Lean_PersistentArray_foldlM___redArg(v_inst_2794_, v_decls_2800_, v___f_2802_, v_init_2797_, v_start_2798_);
return v___x_2803_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg___boxed(lean_object* v_inst_2804_, lean_object* v_lctx_2805_, lean_object* v_f_2806_, lean_object* v_init_2807_, lean_object* v_start_2808_){
_start:
{
lean_object* v_res_2809_; 
v_res_2809_ = l_Lean_LocalContext_foldlM___redArg(v_inst_2804_, v_lctx_2805_, v_f_2806_, v_init_2807_, v_start_2808_);
lean_dec(v_start_2808_);
return v_res_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM(lean_object* v_m_2810_, lean_object* v_00_u03b2_2811_, lean_object* v_inst_2812_, lean_object* v_lctx_2813_, lean_object* v_f_2814_, lean_object* v_init_2815_, lean_object* v_start_2816_){
_start:
{
lean_object* v___x_2817_; 
v___x_2817_ = l_Lean_LocalContext_foldlM___redArg(v_inst_2812_, v_lctx_2813_, v_f_2814_, v_init_2815_, v_start_2816_);
return v___x_2817_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___boxed(lean_object* v_m_2818_, lean_object* v_00_u03b2_2819_, lean_object* v_inst_2820_, lean_object* v_lctx_2821_, lean_object* v_f_2822_, lean_object* v_init_2823_, lean_object* v_start_2824_){
_start:
{
lean_object* v_res_2825_; 
v_res_2825_ = l_Lean_LocalContext_foldlM(v_m_2818_, v_00_u03b2_2819_, v_inst_2820_, v_lctx_2821_, v_f_2822_, v_init_2823_, v_start_2824_);
lean_dec(v_start_2824_);
return v_res_2825_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___redArg___lam__0(lean_object* v_toPure_2826_, lean_object* v_f_2827_, lean_object* v_decl_2828_, lean_object* v_b_2829_){
_start:
{
if (lean_obj_tag(v_decl_2828_) == 0)
{
lean_object* v___x_2830_; 
lean_dec(v_f_2827_);
v___x_2830_ = lean_apply_2(v_toPure_2826_, lean_box(0), v_b_2829_);
return v___x_2830_;
}
else
{
lean_object* v_val_2831_; lean_object* v___x_2832_; 
lean_dec(v_toPure_2826_);
v_val_2831_ = lean_ctor_get(v_decl_2828_, 0);
lean_inc(v_val_2831_);
lean_dec_ref(v_decl_2828_);
v___x_2832_ = lean_apply_2(v_f_2827_, v_val_2831_, v_b_2829_);
return v___x_2832_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___redArg(lean_object* v_inst_2833_, lean_object* v_lctx_2834_, lean_object* v_f_2835_, lean_object* v_init_2836_){
_start:
{
lean_object* v_toApplicative_2837_; lean_object* v_decls_2838_; lean_object* v_toPure_2839_; lean_object* v___f_2840_; lean_object* v___x_2841_; 
v_toApplicative_2837_ = lean_ctor_get(v_inst_2833_, 0);
v_decls_2838_ = lean_ctor_get(v_lctx_2834_, 1);
lean_inc_ref(v_decls_2838_);
lean_dec_ref(v_lctx_2834_);
v_toPure_2839_ = lean_ctor_get(v_toApplicative_2837_, 1);
lean_inc(v_toPure_2839_);
v___f_2840_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldrM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2840_, 0, v_toPure_2839_);
lean_closure_set(v___f_2840_, 1, v_f_2835_);
v___x_2841_ = l_Lean_PersistentArray_foldrM___redArg(v_inst_2833_, v_decls_2838_, v___f_2840_, v_init_2836_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM(lean_object* v_m_2842_, lean_object* v_00_u03b2_2843_, lean_object* v_inst_2844_, lean_object* v_lctx_2845_, lean_object* v_f_2846_, lean_object* v_init_2847_){
_start:
{
lean_object* v___x_2848_; 
v___x_2848_ = l_Lean_LocalContext_foldrM___redArg(v_inst_2844_, v_lctx_2845_, v_f_2846_, v_init_2847_);
return v___x_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg___lam__0(lean_object* v_toPure_2849_, lean_object* v_f_2850_, lean_object* v_decl_2851_){
_start:
{
if (lean_obj_tag(v_decl_2851_) == 0)
{
lean_object* v___x_2852_; lean_object* v___x_2853_; 
lean_dec(v_f_2850_);
v___x_2852_ = lean_box(0);
v___x_2853_ = lean_apply_2(v_toPure_2849_, lean_box(0), v___x_2852_);
return v___x_2853_;
}
else
{
lean_object* v_val_2854_; lean_object* v___x_2855_; 
lean_dec(v_toPure_2849_);
v_val_2854_ = lean_ctor_get(v_decl_2851_, 0);
lean_inc(v_val_2854_);
lean_dec_ref(v_decl_2851_);
v___x_2855_ = lean_apply_1(v_f_2850_, v_val_2854_);
return v___x_2855_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg(lean_object* v_inst_2856_, lean_object* v_lctx_2857_, lean_object* v_f_2858_, lean_object* v_start_2859_){
_start:
{
lean_object* v_toApplicative_2860_; lean_object* v_decls_2861_; lean_object* v_toPure_2862_; lean_object* v___f_2863_; lean_object* v___x_2864_; 
v_toApplicative_2860_ = lean_ctor_get(v_inst_2856_, 0);
v_decls_2861_ = lean_ctor_get(v_lctx_2857_, 1);
lean_inc_ref(v_decls_2861_);
lean_dec_ref(v_lctx_2857_);
v_toPure_2862_ = lean_ctor_get(v_toApplicative_2860_, 1);
lean_inc(v_toPure_2862_);
v___f_2863_ = lean_alloc_closure((void*)(l_Lean_LocalContext_forM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2863_, 0, v_toPure_2862_);
lean_closure_set(v___f_2863_, 1, v_f_2858_);
v___x_2864_ = l_Lean_PersistentArray_forM___redArg(v_inst_2856_, v_decls_2861_, v___f_2863_, v_start_2859_);
return v___x_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg___boxed(lean_object* v_inst_2865_, lean_object* v_lctx_2866_, lean_object* v_f_2867_, lean_object* v_start_2868_){
_start:
{
lean_object* v_res_2869_; 
v_res_2869_ = l_Lean_LocalContext_forM___redArg(v_inst_2865_, v_lctx_2866_, v_f_2867_, v_start_2868_);
lean_dec(v_start_2868_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM(lean_object* v_m_2870_, lean_object* v_inst_2871_, lean_object* v_lctx_2872_, lean_object* v_f_2873_, lean_object* v_start_2874_){
_start:
{
lean_object* v___x_2875_; 
v___x_2875_ = l_Lean_LocalContext_forM___redArg(v_inst_2871_, v_lctx_2872_, v_f_2873_, v_start_2874_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___boxed(lean_object* v_m_2876_, lean_object* v_inst_2877_, lean_object* v_lctx_2878_, lean_object* v_f_2879_, lean_object* v_start_2880_){
_start:
{
lean_object* v_res_2881_; 
v_res_2881_ = l_Lean_LocalContext_forM(v_m_2876_, v_inst_2877_, v_lctx_2878_, v_f_2879_, v_start_2880_);
lean_dec(v_start_2880_);
return v_res_2881_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0(lean_object* v_toPure_2882_, lean_object* v_f_2883_, lean_object* v_decl_2884_){
_start:
{
if (lean_obj_tag(v_decl_2884_) == 0)
{
lean_object* v___x_2885_; lean_object* v___x_2886_; 
lean_dec(v_f_2883_);
v___x_2885_ = lean_box(0);
v___x_2886_ = lean_apply_2(v_toPure_2882_, lean_box(0), v___x_2885_);
return v___x_2886_;
}
else
{
lean_object* v_val_2887_; lean_object* v___x_2888_; 
lean_dec(v_toPure_2882_);
v_val_2887_ = lean_ctor_get(v_decl_2884_, 0);
lean_inc(v_val_2887_);
lean_dec_ref(v_decl_2884_);
v___x_2888_ = lean_apply_1(v_f_2883_, v_val_2887_);
return v___x_2888_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___redArg(lean_object* v_inst_2889_, lean_object* v_lctx_2890_, lean_object* v_f_2891_){
_start:
{
lean_object* v_toApplicative_2892_; lean_object* v_decls_2893_; lean_object* v_toPure_2894_; lean_object* v___f_2895_; lean_object* v___x_2896_; 
v_toApplicative_2892_ = lean_ctor_get(v_inst_2889_, 0);
v_decls_2893_ = lean_ctor_get(v_lctx_2890_, 1);
lean_inc_ref(v_decls_2893_);
lean_dec_ref(v_lctx_2890_);
v_toPure_2894_ = lean_ctor_get(v_toApplicative_2892_, 1);
lean_inc(v_toPure_2894_);
v___f_2895_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2895_, 0, v_toPure_2894_);
lean_closure_set(v___f_2895_, 1, v_f_2891_);
v___x_2896_ = l_Lean_PersistentArray_findSomeM_x3f___redArg(v_inst_2889_, v_decls_2893_, v___f_2895_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f(lean_object* v_m_2897_, lean_object* v_00_u03b2_2898_, lean_object* v_inst_2899_, lean_object* v_lctx_2900_, lean_object* v_f_2901_){
_start:
{
lean_object* v___x_2902_; 
v___x_2902_ = l_Lean_LocalContext_findDeclM_x3f___redArg(v_inst_2899_, v_lctx_2900_, v_f_2901_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___redArg(lean_object* v_inst_2903_, lean_object* v_lctx_2904_, lean_object* v_f_2905_){
_start:
{
lean_object* v_toApplicative_2906_; lean_object* v_decls_2907_; lean_object* v_toPure_2908_; lean_object* v___f_2909_; lean_object* v___x_2910_; 
v_toApplicative_2906_ = lean_ctor_get(v_inst_2903_, 0);
v_decls_2907_ = lean_ctor_get(v_lctx_2904_, 1);
lean_inc_ref(v_decls_2907_);
lean_dec_ref(v_lctx_2904_);
v_toPure_2908_ = lean_ctor_get(v_toApplicative_2906_, 1);
lean_inc(v_toPure_2908_);
v___f_2909_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2909_, 0, v_toPure_2908_);
lean_closure_set(v___f_2909_, 1, v_f_2905_);
v___x_2910_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v_inst_2903_, v_decls_2907_, v___f_2909_);
return v___x_2910_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f(lean_object* v_m_2911_, lean_object* v_00_u03b2_2912_, lean_object* v_inst_2913_, lean_object* v_lctx_2914_, lean_object* v_f_2915_){
_start:
{
lean_object* v___x_2916_; 
v___x_2916_ = l_Lean_LocalContext_findDeclRevM_x3f___redArg(v_inst_2913_, v_lctx_2914_, v_f_2915_);
return v___x_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__0(lean_object* v_toPure_2917_, lean_object* v_f_2918_, lean_object* v_d_x3f_2919_, lean_object* v_b_2920_){
_start:
{
if (lean_obj_tag(v_d_x3f_2919_) == 0)
{
lean_object* v___x_2921_; lean_object* v___x_2922_; 
lean_dec(v_f_2918_);
v___x_2921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2921_, 0, v_b_2920_);
v___x_2922_ = lean_apply_2(v_toPure_2917_, lean_box(0), v___x_2921_);
return v___x_2922_;
}
else
{
lean_object* v_val_2923_; lean_object* v___x_2924_; 
lean_dec(v_toPure_2917_);
v_val_2923_ = lean_ctor_get(v_d_x3f_2919_, 0);
lean_inc(v_val_2923_);
lean_dec_ref(v_d_x3f_2919_);
v___x_2924_ = lean_apply_2(v_f_2918_, v_val_2923_, v_b_2920_);
return v___x_2924_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1(lean_object* v_toPure_2925_, lean_object* v_inst_2926_, lean_object* v_00_u03b2_2927_, lean_object* v_lctx_2928_, lean_object* v_init_2929_, lean_object* v_f_2930_){
_start:
{
lean_object* v_decls_2931_; lean_object* v___f_2932_; lean_object* v___x_2933_; 
v_decls_2931_ = lean_ctor_get(v_lctx_2928_, 1);
lean_inc_ref(v_decls_2931_);
lean_dec_ref(v_lctx_2928_);
v___f_2932_ = lean_alloc_closure((void*)(l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2932_, 0, v_toPure_2925_);
lean_closure_set(v___f_2932_, 1, v_f_2930_);
v___x_2933_ = l_Lean_PersistentArray_forIn___redArg(v_inst_2926_, v_decls_2931_, v_init_2929_, v___f_2932_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg(lean_object* v_inst_2934_){
_start:
{
lean_object* v_toApplicative_2935_; lean_object* v_toPure_2936_; lean_object* v___f_2937_; 
v_toApplicative_2935_ = lean_ctor_get(v_inst_2934_, 0);
v_toPure_2936_ = lean_ctor_get(v_toApplicative_2935_, 1);
lean_inc(v_toPure_2936_);
v___f_2937_ = lean_alloc_closure((void*)(l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1), 6, 2);
lean_closure_set(v___f_2937_, 0, v_toPure_2936_);
lean_closure_set(v___f_2937_, 1, v_inst_2934_);
return v___f_2937_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad(lean_object* v_m_2938_, lean_object* v_inst_2939_){
_start:
{
lean_object* v___x_2940_; 
v___x_2940_ = l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg(v_inst_2939_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg___lam__0(lean_object* v_f_2941_, lean_object* v_x1_2942_, lean_object* v_x2_2943_){
_start:
{
lean_object* v___x_2944_; 
v___x_2944_ = lean_apply_2(v_f_2941_, v_x1_2942_, v_x2_2943_);
return v___x_2944_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg(lean_object* v_lctx_2964_, lean_object* v_f_2965_, lean_object* v_init_2966_, lean_object* v_start_2967_){
_start:
{
lean_object* v___f_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___f_2968_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2968_, 0, v_f_2965_);
v___x_2969_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_2970_ = l_Lean_LocalContext_foldlM___redArg(v___x_2969_, v_lctx_2964_, v___f_2968_, v_init_2966_, v_start_2967_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg___boxed(lean_object* v_lctx_2971_, lean_object* v_f_2972_, lean_object* v_init_2973_, lean_object* v_start_2974_){
_start:
{
lean_object* v_res_2975_; 
v_res_2975_ = l_Lean_LocalContext_foldl___redArg(v_lctx_2971_, v_f_2972_, v_init_2973_, v_start_2974_);
lean_dec(v_start_2974_);
return v_res_2975_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl(lean_object* v_00_u03b2_2976_, lean_object* v_lctx_2977_, lean_object* v_f_2978_, lean_object* v_init_2979_, lean_object* v_start_2980_){
_start:
{
lean_object* v___f_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___f_2981_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2981_, 0, v_f_2978_);
v___x_2982_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_2983_ = l_Lean_LocalContext_foldlM___redArg(v___x_2982_, v_lctx_2977_, v___f_2981_, v_init_2979_, v_start_2980_);
return v___x_2983_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___boxed(lean_object* v_00_u03b2_2984_, lean_object* v_lctx_2985_, lean_object* v_f_2986_, lean_object* v_init_2987_, lean_object* v_start_2988_){
_start:
{
lean_object* v_res_2989_; 
v_res_2989_ = l_Lean_LocalContext_foldl(v_00_u03b2_2984_, v_lctx_2985_, v_f_2986_, v_init_2987_, v_start_2988_);
lean_dec(v_start_2988_);
return v_res_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr___redArg___lam__0(lean_object* v_f_2990_, lean_object* v_x1_2991_, lean_object* v_x2_2992_){
_start:
{
lean_object* v___x_2993_; 
v___x_2993_ = lean_apply_2(v_f_2990_, v_x1_2991_, v_x2_2992_);
return v___x_2993_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr___redArg(lean_object* v_lctx_2994_, lean_object* v_f_2995_, lean_object* v_init_2996_){
_start:
{
lean_object* v___f_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___f_2997_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2997_, 0, v_f_2995_);
v___x_2998_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_2999_ = l_Lean_LocalContext_foldrM___redArg(v___x_2998_, v_lctx_2994_, v___f_2997_, v_init_2996_);
return v___x_2999_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr(lean_object* v_00_u03b2_3000_, lean_object* v_lctx_3001_, lean_object* v_f_3002_, lean_object* v_init_3003_){
_start:
{
lean_object* v___f_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
v___f_3004_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3004_, 0, v_f_3002_);
v___x_3005_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3006_ = l_Lean_LocalContext_foldrM___redArg(v___x_3005_, v_lctx_3001_, v___f_3004_, v_init_3003_);
return v___x_3006_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(lean_object* v_as_3007_, size_t v_i_3008_, size_t v_stop_3009_, lean_object* v_b_3010_){
_start:
{
lean_object* v___y_3012_; uint8_t v___x_3016_; 
v___x_3016_ = lean_usize_dec_eq(v_i_3008_, v_stop_3009_);
if (v___x_3016_ == 0)
{
lean_object* v___x_3017_; 
v___x_3017_ = lean_array_uget_borrowed(v_as_3007_, v_i_3008_);
if (lean_obj_tag(v___x_3017_) == 0)
{
v___y_3012_ = v_b_3010_;
goto v___jp_3011_;
}
else
{
lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3018_ = lean_unsigned_to_nat(1u);
v___x_3019_ = lean_nat_add(v_b_3010_, v___x_3018_);
lean_dec(v_b_3010_);
v___y_3012_ = v___x_3019_;
goto v___jp_3011_;
}
}
else
{
return v_b_3010_;
}
v___jp_3011_:
{
size_t v___x_3013_; size_t v___x_3014_; 
v___x_3013_ = ((size_t)1ULL);
v___x_3014_ = lean_usize_add(v_i_3008_, v___x_3013_);
v_i_3008_ = v___x_3014_;
v_b_3010_ = v___y_3012_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3020_, lean_object* v_i_3021_, lean_object* v_stop_3022_, lean_object* v_b_3023_){
_start:
{
size_t v_i_boxed_3024_; size_t v_stop_boxed_3025_; lean_object* v_res_3026_; 
v_i_boxed_3024_ = lean_unbox_usize(v_i_3021_);
lean_dec(v_i_3021_);
v_stop_boxed_3025_ = lean_unbox_usize(v_stop_3022_);
lean_dec(v_stop_3022_);
v_res_3026_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_as_3020_, v_i_boxed_3024_, v_stop_boxed_3025_, v_b_3023_);
lean_dec_ref(v_as_3020_);
return v_res_3026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(lean_object* v_x_3027_, lean_object* v_x_3028_){
_start:
{
if (lean_obj_tag(v_x_3027_) == 0)
{
lean_object* v_cs_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; uint8_t v___x_3032_; 
v_cs_3029_ = lean_ctor_get(v_x_3027_, 0);
v___x_3030_ = lean_unsigned_to_nat(0u);
v___x_3031_ = lean_array_get_size(v_cs_3029_);
v___x_3032_ = lean_nat_dec_lt(v___x_3030_, v___x_3031_);
if (v___x_3032_ == 0)
{
return v_x_3028_;
}
else
{
uint8_t v___x_3033_; 
v___x_3033_ = lean_nat_dec_le(v___x_3031_, v___x_3031_);
if (v___x_3033_ == 0)
{
if (v___x_3032_ == 0)
{
return v_x_3028_;
}
else
{
size_t v___x_3034_; size_t v___x_3035_; lean_object* v___x_3036_; 
v___x_3034_ = ((size_t)0ULL);
v___x_3035_ = lean_usize_of_nat(v___x_3031_);
v___x_3036_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_cs_3029_, v___x_3034_, v___x_3035_, v_x_3028_);
return v___x_3036_;
}
}
else
{
size_t v___x_3037_; size_t v___x_3038_; lean_object* v___x_3039_; 
v___x_3037_ = ((size_t)0ULL);
v___x_3038_ = lean_usize_of_nat(v___x_3031_);
v___x_3039_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_cs_3029_, v___x_3037_, v___x_3038_, v_x_3028_);
return v___x_3039_;
}
}
}
else
{
lean_object* v_vs_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; uint8_t v___x_3043_; 
v_vs_3040_ = lean_ctor_get(v_x_3027_, 0);
v___x_3041_ = lean_unsigned_to_nat(0u);
v___x_3042_ = lean_array_get_size(v_vs_3040_);
v___x_3043_ = lean_nat_dec_lt(v___x_3041_, v___x_3042_);
if (v___x_3043_ == 0)
{
return v_x_3028_;
}
else
{
uint8_t v___x_3044_; 
v___x_3044_ = lean_nat_dec_le(v___x_3042_, v___x_3042_);
if (v___x_3044_ == 0)
{
if (v___x_3043_ == 0)
{
return v_x_3028_;
}
else
{
size_t v___x_3045_; size_t v___x_3046_; lean_object* v___x_3047_; 
v___x_3045_ = ((size_t)0ULL);
v___x_3046_ = lean_usize_of_nat(v___x_3042_);
v___x_3047_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_vs_3040_, v___x_3045_, v___x_3046_, v_x_3028_);
return v___x_3047_;
}
}
else
{
size_t v___x_3048_; size_t v___x_3049_; lean_object* v___x_3050_; 
v___x_3048_ = ((size_t)0ULL);
v___x_3049_ = lean_usize_of_nat(v___x_3042_);
v___x_3050_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_vs_3040_, v___x_3048_, v___x_3049_, v_x_3028_);
return v___x_3050_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(lean_object* v_as_3051_, size_t v_i_3052_, size_t v_stop_3053_, lean_object* v_b_3054_){
_start:
{
uint8_t v___x_3055_; 
v___x_3055_ = lean_usize_dec_eq(v_i_3052_, v_stop_3053_);
if (v___x_3055_ == 0)
{
lean_object* v___x_3056_; lean_object* v___x_3057_; size_t v___x_3058_; size_t v___x_3059_; 
v___x_3056_ = lean_array_uget_borrowed(v_as_3051_, v_i_3052_);
v___x_3057_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(v___x_3056_, v_b_3054_);
v___x_3058_ = ((size_t)1ULL);
v___x_3059_ = lean_usize_add(v_i_3052_, v___x_3058_);
v_i_3052_ = v___x_3059_;
v_b_3054_ = v___x_3057_;
goto _start;
}
else
{
return v_b_3054_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_as_3061_, lean_object* v_i_3062_, lean_object* v_stop_3063_, lean_object* v_b_3064_){
_start:
{
size_t v_i_boxed_3065_; size_t v_stop_boxed_3066_; lean_object* v_res_3067_; 
v_i_boxed_3065_ = lean_unbox_usize(v_i_3062_);
lean_dec(v_i_3062_);
v_stop_boxed_3066_ = lean_unbox_usize(v_stop_3063_);
lean_dec(v_stop_3063_);
v_res_3067_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_as_3061_, v_i_boxed_3065_, v_stop_boxed_3066_, v_b_3064_);
lean_dec_ref(v_as_3061_);
return v_res_3067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3___boxed(lean_object* v_x_3068_, lean_object* v_x_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(v_x_3068_, v_x_3069_);
lean_dec_ref(v_x_3068_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(lean_object* v_x_3071_, size_t v_x_3072_, size_t v_x_3073_, lean_object* v_x_3074_){
_start:
{
if (lean_obj_tag(v_x_3071_) == 0)
{
lean_object* v_cs_3075_; lean_object* v___x_3076_; size_t v___x_3077_; lean_object* v_j_3078_; lean_object* v___x_3079_; size_t v___x_3080_; size_t v___x_3081_; size_t v___x_3082_; size_t v___x_3083_; size_t v___x_3084_; size_t v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; uint8_t v___x_3090_; 
v_cs_3075_ = lean_ctor_get(v_x_3071_, 0);
v___x_3076_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0);
v___x_3077_ = lean_usize_shift_right(v_x_3072_, v_x_3073_);
v_j_3078_ = lean_usize_to_nat(v___x_3077_);
v___x_3079_ = lean_array_get_borrowed(v___x_3076_, v_cs_3075_, v_j_3078_);
v___x_3080_ = ((size_t)1ULL);
v___x_3081_ = lean_usize_shift_left(v___x_3080_, v_x_3073_);
v___x_3082_ = lean_usize_sub(v___x_3081_, v___x_3080_);
v___x_3083_ = lean_usize_land(v_x_3072_, v___x_3082_);
v___x_3084_ = ((size_t)5ULL);
v___x_3085_ = lean_usize_sub(v_x_3073_, v___x_3084_);
v___x_3086_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(v___x_3079_, v___x_3083_, v___x_3085_, v_x_3074_);
v___x_3087_ = lean_unsigned_to_nat(1u);
v___x_3088_ = lean_nat_add(v_j_3078_, v___x_3087_);
lean_dec(v_j_3078_);
v___x_3089_ = lean_array_get_size(v_cs_3075_);
v___x_3090_ = lean_nat_dec_lt(v___x_3088_, v___x_3089_);
if (v___x_3090_ == 0)
{
lean_dec(v___x_3088_);
return v___x_3086_;
}
else
{
uint8_t v___x_3091_; 
v___x_3091_ = lean_nat_dec_le(v___x_3089_, v___x_3089_);
if (v___x_3091_ == 0)
{
if (v___x_3090_ == 0)
{
lean_dec(v___x_3088_);
return v___x_3086_;
}
else
{
size_t v___x_3092_; size_t v___x_3093_; lean_object* v___x_3094_; 
v___x_3092_ = lean_usize_of_nat(v___x_3088_);
lean_dec(v___x_3088_);
v___x_3093_ = lean_usize_of_nat(v___x_3089_);
v___x_3094_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_cs_3075_, v___x_3092_, v___x_3093_, v___x_3086_);
return v___x_3094_;
}
}
else
{
size_t v___x_3095_; size_t v___x_3096_; lean_object* v___x_3097_; 
v___x_3095_ = lean_usize_of_nat(v___x_3088_);
lean_dec(v___x_3088_);
v___x_3096_ = lean_usize_of_nat(v___x_3089_);
v___x_3097_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_cs_3075_, v___x_3095_, v___x_3096_, v___x_3086_);
return v___x_3097_;
}
}
}
else
{
lean_object* v_vs_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; uint8_t v___x_3101_; 
v_vs_3098_ = lean_ctor_get(v_x_3071_, 0);
v___x_3099_ = lean_usize_to_nat(v_x_3072_);
v___x_3100_ = lean_array_get_size(v_vs_3098_);
v___x_3101_ = lean_nat_dec_lt(v___x_3099_, v___x_3100_);
if (v___x_3101_ == 0)
{
lean_dec(v___x_3099_);
return v_x_3074_;
}
else
{
uint8_t v___x_3102_; 
v___x_3102_ = lean_nat_dec_le(v___x_3100_, v___x_3100_);
if (v___x_3102_ == 0)
{
if (v___x_3101_ == 0)
{
lean_dec(v___x_3099_);
return v_x_3074_;
}
else
{
size_t v___x_3103_; size_t v___x_3104_; lean_object* v___x_3105_; 
v___x_3103_ = lean_usize_of_nat(v___x_3099_);
lean_dec(v___x_3099_);
v___x_3104_ = lean_usize_of_nat(v___x_3100_);
v___x_3105_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_vs_3098_, v___x_3103_, v___x_3104_, v_x_3074_);
return v___x_3105_;
}
}
else
{
size_t v___x_3106_; size_t v___x_3107_; lean_object* v___x_3108_; 
v___x_3106_ = lean_usize_of_nat(v___x_3099_);
lean_dec(v___x_3099_);
v___x_3107_ = lean_usize_of_nat(v___x_3100_);
v___x_3108_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_vs_3098_, v___x_3106_, v___x_3107_, v_x_3074_);
return v___x_3108_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3109_, lean_object* v_x_3110_, lean_object* v_x_3111_, lean_object* v_x_3112_){
_start:
{
size_t v_x_1557__boxed_3113_; size_t v_x_1558__boxed_3114_; lean_object* v_res_3115_; 
v_x_1557__boxed_3113_ = lean_unbox_usize(v_x_3110_);
lean_dec(v_x_3110_);
v_x_1558__boxed_3114_ = lean_unbox_usize(v_x_3111_);
lean_dec(v_x_3111_);
v_res_3115_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(v_x_3109_, v_x_1557__boxed_3113_, v_x_1558__boxed_3114_, v_x_3112_);
lean_dec_ref(v_x_3109_);
return v_res_3115_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(lean_object* v_t_3116_, lean_object* v_init_3117_, lean_object* v_start_3118_){
_start:
{
lean_object* v___x_3119_; uint8_t v___x_3120_; 
v___x_3119_ = lean_unsigned_to_nat(0u);
v___x_3120_ = lean_nat_dec_eq(v_start_3118_, v___x_3119_);
if (v___x_3120_ == 0)
{
lean_object* v_root_3121_; lean_object* v_tail_3122_; size_t v_shift_3123_; lean_object* v_tailOff_3124_; uint8_t v___x_3125_; 
v_root_3121_ = lean_ctor_get(v_t_3116_, 0);
v_tail_3122_ = lean_ctor_get(v_t_3116_, 1);
v_shift_3123_ = lean_ctor_get_usize(v_t_3116_, 4);
v_tailOff_3124_ = lean_ctor_get(v_t_3116_, 3);
v___x_3125_ = lean_nat_dec_le(v_tailOff_3124_, v_start_3118_);
if (v___x_3125_ == 0)
{
size_t v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; uint8_t v___x_3129_; 
v___x_3126_ = lean_usize_of_nat(v_start_3118_);
v___x_3127_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(v_root_3121_, v___x_3126_, v_shift_3123_, v_init_3117_);
v___x_3128_ = lean_array_get_size(v_tail_3122_);
v___x_3129_ = lean_nat_dec_lt(v___x_3119_, v___x_3128_);
if (v___x_3129_ == 0)
{
return v___x_3127_;
}
else
{
uint8_t v___x_3130_; 
v___x_3130_ = lean_nat_dec_le(v___x_3128_, v___x_3128_);
if (v___x_3130_ == 0)
{
if (v___x_3129_ == 0)
{
return v___x_3127_;
}
else
{
size_t v___x_3131_; size_t v___x_3132_; lean_object* v___x_3133_; 
v___x_3131_ = ((size_t)0ULL);
v___x_3132_ = lean_usize_of_nat(v___x_3128_);
v___x_3133_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3122_, v___x_3131_, v___x_3132_, v___x_3127_);
return v___x_3133_;
}
}
else
{
size_t v___x_3134_; size_t v___x_3135_; lean_object* v___x_3136_; 
v___x_3134_ = ((size_t)0ULL);
v___x_3135_ = lean_usize_of_nat(v___x_3128_);
v___x_3136_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3122_, v___x_3134_, v___x_3135_, v___x_3127_);
return v___x_3136_;
}
}
}
else
{
lean_object* v___x_3137_; lean_object* v___x_3138_; uint8_t v___x_3139_; 
v___x_3137_ = lean_nat_sub(v_start_3118_, v_tailOff_3124_);
v___x_3138_ = lean_array_get_size(v_tail_3122_);
v___x_3139_ = lean_nat_dec_lt(v___x_3137_, v___x_3138_);
if (v___x_3139_ == 0)
{
lean_dec(v___x_3137_);
return v_init_3117_;
}
else
{
uint8_t v___x_3140_; 
v___x_3140_ = lean_nat_dec_le(v___x_3138_, v___x_3138_);
if (v___x_3140_ == 0)
{
if (v___x_3139_ == 0)
{
lean_dec(v___x_3137_);
return v_init_3117_;
}
else
{
size_t v___x_3141_; size_t v___x_3142_; lean_object* v___x_3143_; 
v___x_3141_ = lean_usize_of_nat(v___x_3137_);
lean_dec(v___x_3137_);
v___x_3142_ = lean_usize_of_nat(v___x_3138_);
v___x_3143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3122_, v___x_3141_, v___x_3142_, v_init_3117_);
return v___x_3143_;
}
}
else
{
size_t v___x_3144_; size_t v___x_3145_; lean_object* v___x_3146_; 
v___x_3144_ = lean_usize_of_nat(v___x_3137_);
lean_dec(v___x_3137_);
v___x_3145_ = lean_usize_of_nat(v___x_3138_);
v___x_3146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3122_, v___x_3144_, v___x_3145_, v_init_3117_);
return v___x_3146_;
}
}
}
}
else
{
lean_object* v_root_3147_; lean_object* v_tail_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; uint8_t v___x_3151_; 
v_root_3147_ = lean_ctor_get(v_t_3116_, 0);
v_tail_3148_ = lean_ctor_get(v_t_3116_, 1);
v___x_3149_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(v_root_3147_, v_init_3117_);
v___x_3150_ = lean_array_get_size(v_tail_3148_);
v___x_3151_ = lean_nat_dec_lt(v___x_3119_, v___x_3150_);
if (v___x_3151_ == 0)
{
return v___x_3149_;
}
else
{
uint8_t v___x_3152_; 
v___x_3152_ = lean_nat_dec_le(v___x_3150_, v___x_3150_);
if (v___x_3152_ == 0)
{
if (v___x_3151_ == 0)
{
return v___x_3149_;
}
else
{
size_t v___x_3153_; size_t v___x_3154_; lean_object* v___x_3155_; 
v___x_3153_ = ((size_t)0ULL);
v___x_3154_ = lean_usize_of_nat(v___x_3150_);
v___x_3155_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3148_, v___x_3153_, v___x_3154_, v___x_3149_);
return v___x_3155_;
}
}
else
{
size_t v___x_3156_; size_t v___x_3157_; lean_object* v___x_3158_; 
v___x_3156_ = ((size_t)0ULL);
v___x_3157_ = lean_usize_of_nat(v___x_3150_);
v___x_3158_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3148_, v___x_3156_, v___x_3157_, v___x_3149_);
return v___x_3158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0___boxed(lean_object* v_t_3159_, lean_object* v_init_3160_, lean_object* v_start_3161_){
_start:
{
lean_object* v_res_3162_; 
v_res_3162_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(v_t_3159_, v_init_3160_, v_start_3161_);
lean_dec(v_start_3161_);
lean_dec_ref(v_t_3159_);
return v_res_3162_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(lean_object* v_lctx_3163_, lean_object* v_init_3164_, lean_object* v_start_3165_){
_start:
{
lean_object* v_decls_3166_; lean_object* v___x_3167_; 
v_decls_3166_ = lean_ctor_get(v_lctx_3163_, 1);
v___x_3167_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(v_decls_3166_, v_init_3164_, v_start_3165_);
return v___x_3167_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0___boxed(lean_object* v_lctx_3168_, lean_object* v_init_3169_, lean_object* v_start_3170_){
_start:
{
lean_object* v_res_3171_; 
v_res_3171_ = l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(v_lctx_3168_, v_init_3169_, v_start_3170_);
lean_dec(v_start_3170_);
lean_dec_ref(v_lctx_3168_);
return v_res_3171_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_size(lean_object* v_lctx_3172_){
_start:
{
lean_object* v___x_3173_; lean_object* v___x_3174_; 
v___x_3173_ = lean_unsigned_to_nat(0u);
v___x_3174_ = l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(v_lctx_3172_, v___x_3173_, v___x_3173_);
return v___x_3174_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_size___boxed(lean_object* v_lctx_3175_){
_start:
{
lean_object* v_res_3176_; 
v_res_3176_ = l_Lean_LocalContext_size(v_lctx_3175_);
lean_dec_ref(v_lctx_3175_);
return v_res_3176_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f___redArg___lam__0(lean_object* v_f_3177_, lean_object* v_x_3178_){
_start:
{
lean_object* v___x_3179_; 
v___x_3179_ = lean_apply_1(v_f_3177_, v_x_3178_);
return v___x_3179_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f___redArg(lean_object* v_lctx_3180_, lean_object* v_f_3181_){
_start:
{
lean_object* v___f_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; 
v___f_3182_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3182_, 0, v_f_3181_);
v___x_3183_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3184_ = l_Lean_LocalContext_findDeclM_x3f___redArg(v___x_3183_, v_lctx_3180_, v___f_3182_);
return v___x_3184_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f(lean_object* v_00_u03b2_3185_, lean_object* v_lctx_3186_, lean_object* v_f_3187_){
_start:
{
lean_object* v___f_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___f_3188_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3188_, 0, v_f_3187_);
v___x_3189_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3190_ = l_Lean_LocalContext_findDeclM_x3f___redArg(v___x_3189_, v_lctx_3186_, v___f_3188_);
return v___x_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRev_x3f___redArg(lean_object* v_lctx_3191_, lean_object* v_f_3192_){
_start:
{
lean_object* v___f_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; 
v___f_3193_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3193_, 0, v_f_3192_);
v___x_3194_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3195_ = l_Lean_LocalContext_findDeclRevM_x3f___redArg(v___x_3194_, v_lctx_3191_, v___f_3193_);
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRev_x3f(lean_object* v_00_u03b2_3196_, lean_object* v_lctx_3197_, lean_object* v_f_3198_){
_start:
{
lean_object* v___f_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; 
v___f_3199_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3199_, 0, v_f_3198_);
v___x_3200_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3201_ = l_Lean_LocalContext_findDeclRevM_x3f___redArg(v___x_3200_, v_lctx_3197_, v___f_3199_);
return v___x_3201_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(lean_object* v_val_3202_, lean_object* v_as_3203_, size_t v_i_3204_, size_t v_stop_3205_){
_start:
{
uint8_t v___x_3206_; 
v___x_3206_ = lean_usize_dec_eq(v_i_3204_, v_stop_3205_);
if (v___x_3206_ == 0)
{
uint8_t v___x_3207_; uint8_t v___y_3209_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v_fvarId_3215_; uint8_t v___x_3216_; 
v___x_3207_ = 1;
v___x_3213_ = lean_array_uget_borrowed(v_as_3203_, v_i_3204_);
v___x_3214_ = l_Lean_Expr_fvarId_x21(v___x_3213_);
v_fvarId_3215_ = lean_ctor_get(v_val_3202_, 1);
v___x_3216_ = l_Lean_instBEqFVarId_beq(v___x_3214_, v_fvarId_3215_);
lean_dec(v___x_3214_);
v___y_3209_ = v___x_3216_;
goto v___jp_3208_;
v___jp_3208_:
{
if (v___y_3209_ == 0)
{
size_t v___x_3210_; size_t v___x_3211_; 
v___x_3210_ = ((size_t)1ULL);
v___x_3211_ = lean_usize_add(v_i_3204_, v___x_3210_);
v_i_3204_ = v___x_3211_;
goto _start;
}
else
{
return v___x_3207_;
}
}
}
else
{
uint8_t v___x_3217_; 
v___x_3217_ = 0;
return v___x_3217_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0___boxed(lean_object* v_val_3218_, lean_object* v_as_3219_, lean_object* v_i_3220_, lean_object* v_stop_3221_){
_start:
{
size_t v_i_boxed_3222_; size_t v_stop_boxed_3223_; uint8_t v_res_3224_; lean_object* v_r_3225_; 
v_i_boxed_3222_ = lean_unbox_usize(v_i_3220_);
lean_dec(v_i_3220_);
v_stop_boxed_3223_ = lean_unbox_usize(v_stop_3221_);
lean_dec(v_stop_3221_);
v_res_3224_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(v_val_3218_, v_as_3219_, v_i_boxed_3222_, v_stop_boxed_3223_);
lean_dec_ref(v_as_3219_);
lean_dec_ref(v_val_3218_);
v_r_3225_ = lean_box(v_res_3224_);
return v_r_3225_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_isSubPrefixOfAux(lean_object* v_a_u2081_3226_, lean_object* v_a_u2082_3227_, lean_object* v_exceptFVars_3228_, lean_object* v_i_3229_, lean_object* v_j_3230_){
_start:
{
lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v_size_3246_; uint8_t v___x_3247_; 
v_size_3246_ = lean_ctor_get(v_a_u2081_3226_, 2);
v___x_3247_ = lean_nat_dec_lt(v_i_3229_, v_size_3246_);
if (v___x_3247_ == 0)
{
uint8_t v___x_3248_; 
lean_dec(v_j_3230_);
lean_dec(v_i_3229_);
lean_dec_ref(v_a_u2082_3227_);
lean_dec_ref(v_a_u2081_3226_);
v___x_3248_ = 1;
return v___x_3248_;
}
else
{
lean_object* v___x_3249_; lean_object* v___x_3250_; 
v___x_3249_ = lean_box(0);
lean_inc_ref(v_a_u2081_3226_);
v___x_3250_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3249_, v_a_u2081_3226_, v_i_3229_);
if (lean_obj_tag(v___x_3250_) == 0)
{
lean_object* v___x_3251_; lean_object* v___x_3252_; 
v___x_3251_ = lean_unsigned_to_nat(1u);
v___x_3252_ = lean_nat_add(v_i_3229_, v___x_3251_);
lean_dec(v_i_3229_);
v_i_3229_ = v___x_3252_;
goto _start;
}
else
{
lean_object* v_val_3254_; uint8_t v___y_3256_; lean_object* v___x_3265_; lean_object* v___x_3266_; uint8_t v___x_3267_; 
v_val_3254_ = lean_ctor_get(v___x_3250_, 0);
lean_inc(v_val_3254_);
lean_dec_ref(v___x_3250_);
v___x_3265_ = lean_unsigned_to_nat(0u);
v___x_3266_ = lean_array_get_size(v_exceptFVars_3228_);
v___x_3267_ = lean_nat_dec_lt(v___x_3265_, v___x_3266_);
if (v___x_3267_ == 0)
{
v___y_3256_ = v___x_3267_;
goto v___jp_3255_;
}
else
{
if (v___x_3267_ == 0)
{
v___y_3256_ = v___x_3267_;
goto v___jp_3255_;
}
else
{
size_t v___x_3268_; size_t v___x_3269_; uint8_t v___x_3270_; 
v___x_3268_ = ((size_t)0ULL);
v___x_3269_ = lean_usize_of_nat(v___x_3266_);
v___x_3270_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(v_val_3254_, v_exceptFVars_3228_, v___x_3268_, v___x_3269_);
if (v___x_3270_ == 0)
{
v___y_3256_ = v___x_3270_;
goto v___jp_3255_;
}
else
{
lean_object* v___x_3271_; lean_object* v___x_3272_; 
lean_dec(v_val_3254_);
v___x_3271_ = lean_unsigned_to_nat(1u);
v___x_3272_ = lean_nat_add(v_i_3229_, v___x_3271_);
lean_dec(v_i_3229_);
v_i_3229_ = v___x_3272_;
goto _start;
}
}
}
v___jp_3255_:
{
lean_object* v_size_3257_; uint8_t v___x_3258_; 
v_size_3257_ = lean_ctor_get(v_a_u2082_3227_, 2);
v___x_3258_ = lean_nat_dec_lt(v_j_3230_, v_size_3257_);
if (v___x_3258_ == 0)
{
lean_dec(v_val_3254_);
lean_dec(v_j_3230_);
lean_dec(v_i_3229_);
lean_dec_ref(v_a_u2082_3227_);
lean_dec_ref(v_a_u2081_3226_);
return v___y_3256_;
}
else
{
lean_object* v___x_3259_; 
lean_inc_ref(v_a_u2082_3227_);
v___x_3259_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3249_, v_a_u2082_3227_, v_j_3230_);
if (lean_obj_tag(v___x_3259_) == 0)
{
lean_object* v___x_3260_; lean_object* v___x_3261_; 
lean_dec(v_val_3254_);
v___x_3260_ = lean_unsigned_to_nat(1u);
v___x_3261_ = lean_nat_add(v_j_3230_, v___x_3260_);
lean_dec(v_j_3230_);
v_j_3230_ = v___x_3261_;
goto _start;
}
else
{
lean_object* v_val_3263_; lean_object* v_fvarId_3264_; 
v_val_3263_ = lean_ctor_get(v___x_3259_, 0);
lean_inc(v_val_3263_);
lean_dec_ref(v___x_3259_);
v_fvarId_3264_ = lean_ctor_get(v_val_3254_, 1);
lean_inc(v_fvarId_3264_);
lean_dec(v_val_3254_);
v___y_3243_ = v_val_3263_;
v___y_3244_ = v_fvarId_3264_;
goto v___jp_3242_;
}
}
}
}
}
v___jp_3231_:
{
uint8_t v___x_3234_; 
v___x_3234_ = l_Lean_instBEqFVarId_beq(v___y_3232_, v___y_3233_);
lean_dec(v___y_3233_);
lean_dec(v___y_3232_);
if (v___x_3234_ == 0)
{
lean_object* v___x_3235_; lean_object* v___x_3236_; 
v___x_3235_ = lean_unsigned_to_nat(1u);
v___x_3236_ = lean_nat_add(v_j_3230_, v___x_3235_);
lean_dec(v_j_3230_);
v_j_3230_ = v___x_3236_;
goto _start;
}
else
{
lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; 
v___x_3238_ = lean_unsigned_to_nat(1u);
v___x_3239_ = lean_nat_add(v_i_3229_, v___x_3238_);
lean_dec(v_i_3229_);
v___x_3240_ = lean_nat_add(v_j_3230_, v___x_3238_);
lean_dec(v_j_3230_);
v_i_3229_ = v___x_3239_;
v_j_3230_ = v___x_3240_;
goto _start;
}
}
v___jp_3242_:
{
lean_object* v_fvarId_3245_; 
v_fvarId_3245_ = lean_ctor_get(v___y_3243_, 1);
lean_inc(v_fvarId_3245_);
lean_dec_ref(v___y_3243_);
v___y_3232_ = v___y_3244_;
v___y_3233_ = v_fvarId_3245_;
goto v___jp_3231_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_isSubPrefixOfAux___boxed(lean_object* v_a_u2081_3274_, lean_object* v_a_u2082_3275_, lean_object* v_exceptFVars_3276_, lean_object* v_i_3277_, lean_object* v_j_3278_){
_start:
{
uint8_t v_res_3279_; lean_object* v_r_3280_; 
v_res_3279_ = l_Lean_LocalContext_isSubPrefixOfAux(v_a_u2081_3274_, v_a_u2082_3275_, v_exceptFVars_3276_, v_i_3277_, v_j_3278_);
lean_dec_ref(v_exceptFVars_3276_);
v_r_3280_ = lean_box(v_res_3279_);
return v_r_3280_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_isSubPrefixOf(lean_object* v_lctx_u2081_3281_, lean_object* v_lctx_u2082_3282_, lean_object* v_exceptFVars_3283_){
_start:
{
lean_object* v_decls_3284_; lean_object* v_decls_3285_; lean_object* v___x_3286_; uint8_t v___x_3287_; 
v_decls_3284_ = lean_ctor_get(v_lctx_u2081_3281_, 1);
lean_inc_ref(v_decls_3284_);
lean_dec_ref(v_lctx_u2081_3281_);
v_decls_3285_ = lean_ctor_get(v_lctx_u2082_3282_, 1);
lean_inc_ref(v_decls_3285_);
lean_dec_ref(v_lctx_u2082_3282_);
v___x_3286_ = lean_unsigned_to_nat(0u);
v___x_3287_ = l_Lean_LocalContext_isSubPrefixOfAux(v_decls_3284_, v_decls_3285_, v_exceptFVars_3283_, v___x_3286_, v___x_3286_);
return v___x_3287_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_isSubPrefixOf___boxed(lean_object* v_lctx_u2081_3288_, lean_object* v_lctx_u2082_3289_, lean_object* v_exceptFVars_3290_){
_start:
{
uint8_t v_res_3291_; lean_object* v_r_3292_; 
v_res_3291_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_u2081_3288_, v_lctx_u2082_3289_, v_exceptFVars_3290_);
lean_dec_ref(v_exceptFVars_3290_);
v_r_3292_ = lean_box(v_res_3291_);
return v_r_3292_;
}
}
static lean_object* _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; 
v___x_3294_ = ((lean_object*)(l_Lean_LocalContext_get_x21___closed__1));
v___x_3295_ = lean_unsigned_to_nat(14u);
v___x_3296_ = lean_unsigned_to_nat(573u);
v___x_3297_ = ((lean_object*)(l_Lean_LocalContext_mkBinding___lam__0___closed__0));
v___x_3298_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_3299_ = l_mkPanicMessageWithDecl(v___x_3298_, v___x_3297_, v___x_3296_, v___x_3295_, v___x_3294_);
return v___x_3299_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___lam__0(lean_object* v_xs_3300_, lean_object* v_lctx_3301_, lean_object* v___x_3302_, uint8_t v_isLambda_3303_, uint8_t v_usedLetOnly_3304_, uint8_t v_generalizeNondepLet_3305_, lean_object* v_i_3306_, lean_object* v_x_3307_, lean_object* v_b_3308_){
_start:
{
lean_object* v_n_3310_; lean_object* v_ty_3311_; uint8_t v_bi_3312_; lean_object* v_x_3316_; lean_object* v___x_3317_; 
v_x_3316_ = lean_array_fget_borrowed(v_xs_3300_, v_i_3306_);
v___x_3317_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3301_, v_x_3316_);
if (lean_obj_tag(v___x_3317_) == 0)
{
lean_object* v___x_3318_; lean_object* v___x_3319_; 
lean_dec_ref(v_b_3308_);
v___x_3318_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3319_ = l_panic___redArg(v___x_3302_, v___x_3318_);
return v___x_3319_;
}
else
{
lean_object* v_val_3320_; 
lean_dec_ref(v___x_3302_);
v_val_3320_ = lean_ctor_get(v___x_3317_, 0);
lean_inc(v_val_3320_);
lean_dec_ref(v___x_3317_);
if (lean_obj_tag(v_val_3320_) == 0)
{
lean_object* v_userName_3321_; lean_object* v_type_3322_; uint8_t v_bi_3323_; 
v_userName_3321_ = lean_ctor_get(v_val_3320_, 2);
lean_inc(v_userName_3321_);
v_type_3322_ = lean_ctor_get(v_val_3320_, 3);
lean_inc_ref(v_type_3322_);
v_bi_3323_ = lean_ctor_get_uint8(v_val_3320_, sizeof(void*)*4);
lean_dec_ref(v_val_3320_);
v_n_3310_ = v_userName_3321_;
v_ty_3311_ = v_type_3322_;
v_bi_3312_ = v_bi_3323_;
goto v___jp_3309_;
}
else
{
lean_object* v_userName_3324_; lean_object* v_type_3325_; lean_object* v_value_3326_; uint8_t v_nondep_3327_; uint8_t v___y_3333_; 
v_userName_3324_ = lean_ctor_get(v_val_3320_, 2);
lean_inc(v_userName_3324_);
v_type_3325_ = lean_ctor_get(v_val_3320_, 3);
lean_inc_ref(v_type_3325_);
v_value_3326_ = lean_ctor_get(v_val_3320_, 4);
lean_inc_ref(v_value_3326_);
v_nondep_3327_ = lean_ctor_get_uint8(v_val_3320_, sizeof(void*)*5);
lean_dec_ref(v_val_3320_);
if (v_nondep_3327_ == 0)
{
v___y_3333_ = v_nondep_3327_;
goto v___jp_3332_;
}
else
{
if (v_generalizeNondepLet_3305_ == 0)
{
v___y_3333_ = v_generalizeNondepLet_3305_;
goto v___jp_3332_;
}
else
{
uint8_t v___x_3338_; 
lean_dec_ref(v_value_3326_);
v___x_3338_ = 0;
v_n_3310_ = v_userName_3324_;
v_ty_3311_ = v_type_3325_;
v_bi_3312_ = v___x_3338_;
goto v___jp_3309_;
}
}
v___jp_3328_:
{
lean_object* v_ty_3329_; lean_object* v_val_3330_; lean_object* v___x_3331_; 
v_ty_3329_ = lean_expr_abstract_range(v_type_3325_, v_i_3306_, v_xs_3300_);
lean_dec_ref(v_type_3325_);
v_val_3330_ = lean_expr_abstract_range(v_value_3326_, v_i_3306_, v_xs_3300_);
lean_dec_ref(v_value_3326_);
v___x_3331_ = l_Lean_Expr_letE___override(v_userName_3324_, v_ty_3329_, v_val_3330_, v_b_3308_, v_nondep_3327_);
return v___x_3331_;
}
v___jp_3332_:
{
if (v_usedLetOnly_3304_ == 0)
{
goto v___jp_3328_;
}
else
{
if (v___y_3333_ == 0)
{
lean_object* v___x_3334_; uint8_t v___x_3335_; 
v___x_3334_ = lean_unsigned_to_nat(0u);
v___x_3335_ = lean_expr_has_loose_bvar(v_b_3308_, v___x_3334_);
if (v___x_3335_ == 0)
{
lean_object* v___x_3336_; lean_object* v___x_3337_; 
lean_dec_ref(v_value_3326_);
lean_dec_ref(v_type_3325_);
lean_dec(v_userName_3324_);
v___x_3336_ = lean_unsigned_to_nat(1u);
v___x_3337_ = lean_expr_lower_loose_bvars(v_b_3308_, v___x_3336_, v___x_3336_);
lean_dec_ref(v_b_3308_);
return v___x_3337_;
}
else
{
goto v___jp_3328_;
}
}
else
{
goto v___jp_3328_;
}
}
}
}
}
v___jp_3309_:
{
lean_object* v_ty_3313_; 
v_ty_3313_ = lean_expr_abstract_range(v_ty_3311_, v_i_3306_, v_xs_3300_);
lean_dec_ref(v_ty_3311_);
if (v_isLambda_3303_ == 0)
{
lean_object* v___x_3314_; 
v___x_3314_ = l_Lean_mkForall(v_n_3310_, v_bi_3312_, v_ty_3313_, v_b_3308_);
return v___x_3314_;
}
else
{
lean_object* v___x_3315_; 
v___x_3315_ = l_Lean_mkLambda(v_n_3310_, v_bi_3312_, v_ty_3313_, v_b_3308_);
return v___x_3315_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___lam__0___boxed(lean_object* v_xs_3339_, lean_object* v_lctx_3340_, lean_object* v___x_3341_, lean_object* v_isLambda_3342_, lean_object* v_usedLetOnly_3343_, lean_object* v_generalizeNondepLet_3344_, lean_object* v_i_3345_, lean_object* v_x_3346_, lean_object* v_b_3347_){
_start:
{
uint8_t v_isLambda_boxed_3348_; uint8_t v_usedLetOnly_boxed_3349_; uint8_t v_generalizeNondepLet_boxed_3350_; lean_object* v_res_3351_; 
v_isLambda_boxed_3348_ = lean_unbox(v_isLambda_3342_);
v_usedLetOnly_boxed_3349_ = lean_unbox(v_usedLetOnly_3343_);
v_generalizeNondepLet_boxed_3350_ = lean_unbox(v_generalizeNondepLet_3344_);
v_res_3351_ = l_Lean_LocalContext_mkBinding___lam__0(v_xs_3339_, v_lctx_3340_, v___x_3341_, v_isLambda_boxed_3348_, v_usedLetOnly_boxed_3349_, v_generalizeNondepLet_boxed_3350_, v_i_3345_, v_x_3346_, v_b_3347_);
lean_dec(v_i_3345_);
lean_dec_ref(v_xs_3339_);
return v_res_3351_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding(uint8_t v_isLambda_3352_, lean_object* v_lctx_3353_, lean_object* v_xs_3354_, lean_object* v_b_3355_, uint8_t v_usedLetOnly_3356_, uint8_t v_generalizeNondepLet_3357_){
_start:
{
lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___f_3362_; lean_object* v_b_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; 
v___x_3358_ = l_Lean_instInhabitedExpr;
v___x_3359_ = lean_box(v_isLambda_3352_);
v___x_3360_ = lean_box(v_usedLetOnly_3356_);
v___x_3361_ = lean_box(v_generalizeNondepLet_3357_);
lean_inc_ref(v_xs_3354_);
v___f_3362_ = lean_alloc_closure((void*)(l_Lean_LocalContext_mkBinding___lam__0___boxed), 9, 6);
lean_closure_set(v___f_3362_, 0, v_xs_3354_);
lean_closure_set(v___f_3362_, 1, v_lctx_3353_);
lean_closure_set(v___f_3362_, 2, v___x_3358_);
lean_closure_set(v___f_3362_, 3, v___x_3359_);
lean_closure_set(v___f_3362_, 4, v___x_3360_);
lean_closure_set(v___f_3362_, 5, v___x_3361_);
v_b_3363_ = lean_expr_abstract(v_b_3355_, v_xs_3354_);
v___x_3364_ = lean_array_get_size(v_xs_3354_);
lean_dec_ref(v_xs_3354_);
v___x_3365_ = l_Nat_foldRev___redArg(v___x_3364_, v___f_3362_, v_b_3363_);
return v___x_3365_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___boxed(lean_object* v_isLambda_3366_, lean_object* v_lctx_3367_, lean_object* v_xs_3368_, lean_object* v_b_3369_, lean_object* v_usedLetOnly_3370_, lean_object* v_generalizeNondepLet_3371_){
_start:
{
uint8_t v_isLambda_boxed_3372_; uint8_t v_usedLetOnly_boxed_3373_; uint8_t v_generalizeNondepLet_boxed_3374_; lean_object* v_res_3375_; 
v_isLambda_boxed_3372_ = lean_unbox(v_isLambda_3366_);
v_usedLetOnly_boxed_3373_ = lean_unbox(v_usedLetOnly_3370_);
v_generalizeNondepLet_boxed_3374_ = lean_unbox(v_generalizeNondepLet_3371_);
v_res_3375_ = l_Lean_LocalContext_mkBinding(v_isLambda_boxed_3372_, v_lctx_3367_, v_xs_3368_, v_b_3369_, v_usedLetOnly_boxed_3373_, v_generalizeNondepLet_boxed_3374_);
lean_dec_ref(v_b_3369_);
return v_res_3375_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(lean_object* v_xs_3376_, lean_object* v_lctx_3377_, uint8_t v_usedLetOnly_3378_, uint8_t v_generalizeNondepLet_3379_, lean_object* v_x_3380_, lean_object* v_x_3381_){
_start:
{
lean_object* v_zero_3382_; uint8_t v_isZero_3383_; 
v_zero_3382_ = lean_unsigned_to_nat(0u);
v_isZero_3383_ = lean_nat_dec_eq(v_x_3380_, v_zero_3382_);
if (v_isZero_3383_ == 1)
{
lean_dec(v_x_3380_);
lean_dec_ref(v_lctx_3377_);
return v_x_3381_;
}
else
{
lean_object* v_one_3384_; lean_object* v_n_3385_; lean_object* v_n_3387_; lean_object* v_ty_3388_; uint8_t v_bi_3389_; lean_object* v_x_3393_; lean_object* v___x_3394_; 
v_one_3384_ = lean_unsigned_to_nat(1u);
v_n_3385_ = lean_nat_sub(v_x_3380_, v_one_3384_);
lean_dec(v_x_3380_);
v_x_3393_ = lean_array_fget_borrowed(v_xs_3376_, v_n_3385_);
lean_inc_ref(v_lctx_3377_);
v___x_3394_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3377_, v_x_3393_);
if (lean_obj_tag(v___x_3394_) == 0)
{
lean_object* v___x_3395_; lean_object* v___x_3396_; 
lean_dec_ref(v_x_3381_);
v___x_3395_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3396_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3395_);
v_x_3380_ = v_n_3385_;
v_x_3381_ = v___x_3396_;
goto _start;
}
else
{
lean_object* v_val_3398_; 
v_val_3398_ = lean_ctor_get(v___x_3394_, 0);
lean_inc(v_val_3398_);
lean_dec_ref(v___x_3394_);
if (lean_obj_tag(v_val_3398_) == 0)
{
lean_object* v_userName_3399_; lean_object* v_type_3400_; uint8_t v_bi_3401_; 
v_userName_3399_ = lean_ctor_get(v_val_3398_, 2);
lean_inc(v_userName_3399_);
v_type_3400_ = lean_ctor_get(v_val_3398_, 3);
lean_inc_ref(v_type_3400_);
v_bi_3401_ = lean_ctor_get_uint8(v_val_3398_, sizeof(void*)*4);
lean_dec_ref(v_val_3398_);
v_n_3387_ = v_userName_3399_;
v_ty_3388_ = v_type_3400_;
v_bi_3389_ = v_bi_3401_;
goto v___jp_3386_;
}
else
{
lean_object* v_userName_3402_; lean_object* v_type_3403_; lean_object* v_value_3404_; uint8_t v_nondep_3405_; uint8_t v___y_3412_; 
v_userName_3402_ = lean_ctor_get(v_val_3398_, 2);
lean_inc(v_userName_3402_);
v_type_3403_ = lean_ctor_get(v_val_3398_, 3);
lean_inc_ref(v_type_3403_);
v_value_3404_ = lean_ctor_get(v_val_3398_, 4);
lean_inc_ref(v_value_3404_);
v_nondep_3405_ = lean_ctor_get_uint8(v_val_3398_, sizeof(void*)*5);
lean_dec_ref(v_val_3398_);
if (v_nondep_3405_ == 0)
{
v___y_3412_ = v_nondep_3405_;
goto v___jp_3411_;
}
else
{
if (v_generalizeNondepLet_3379_ == 0)
{
v___y_3412_ = v_generalizeNondepLet_3379_;
goto v___jp_3411_;
}
else
{
uint8_t v___x_3416_; 
lean_dec_ref(v_value_3404_);
v___x_3416_ = 0;
v_n_3387_ = v_userName_3402_;
v_ty_3388_ = v_type_3403_;
v_bi_3389_ = v___x_3416_;
goto v___jp_3386_;
}
}
v___jp_3406_:
{
lean_object* v_ty_3407_; lean_object* v_val_3408_; lean_object* v___x_3409_; 
v_ty_3407_ = lean_expr_abstract_range(v_type_3403_, v_n_3385_, v_xs_3376_);
lean_dec_ref(v_type_3403_);
v_val_3408_ = lean_expr_abstract_range(v_value_3404_, v_n_3385_, v_xs_3376_);
lean_dec_ref(v_value_3404_);
v___x_3409_ = l_Lean_Expr_letE___override(v_userName_3402_, v_ty_3407_, v_val_3408_, v_x_3381_, v_nondep_3405_);
v_x_3380_ = v_n_3385_;
v_x_3381_ = v___x_3409_;
goto _start;
}
v___jp_3411_:
{
if (v_usedLetOnly_3378_ == 0)
{
goto v___jp_3406_;
}
else
{
if (v___y_3412_ == 0)
{
uint8_t v___x_3413_; 
v___x_3413_ = lean_expr_has_loose_bvar(v_x_3381_, v_zero_3382_);
if (v___x_3413_ == 0)
{
lean_object* v___x_3414_; 
lean_dec_ref(v_value_3404_);
lean_dec_ref(v_type_3403_);
lean_dec(v_userName_3402_);
v___x_3414_ = lean_expr_lower_loose_bvars(v_x_3381_, v_one_3384_, v_one_3384_);
lean_dec_ref(v_x_3381_);
v_x_3380_ = v_n_3385_;
v_x_3381_ = v___x_3414_;
goto _start;
}
else
{
goto v___jp_3406_;
}
}
else
{
goto v___jp_3406_;
}
}
}
}
}
v___jp_3386_:
{
lean_object* v_ty_3390_; lean_object* v___x_3391_; 
v_ty_3390_ = lean_expr_abstract_range(v_ty_3388_, v_n_3385_, v_xs_3376_);
lean_dec_ref(v_ty_3388_);
v___x_3391_ = l_Lean_mkLambda(v_n_3387_, v_bi_3389_, v_ty_3390_, v_x_3381_);
v_x_3380_ = v_n_3385_;
v_x_3381_ = v___x_3391_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0___boxed(lean_object* v_xs_3417_, lean_object* v_lctx_3418_, lean_object* v_usedLetOnly_3419_, lean_object* v_generalizeNondepLet_3420_, lean_object* v_x_3421_, lean_object* v_x_3422_){
_start:
{
uint8_t v_usedLetOnly_boxed_3423_; uint8_t v_generalizeNondepLet_boxed_3424_; lean_object* v_res_3425_; 
v_usedLetOnly_boxed_3423_ = lean_unbox(v_usedLetOnly_3419_);
v_generalizeNondepLet_boxed_3424_ = lean_unbox(v_generalizeNondepLet_3420_);
v_res_3425_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3417_, v_lctx_3418_, v_usedLetOnly_boxed_3423_, v_generalizeNondepLet_boxed_3424_, v_x_3421_, v_x_3422_);
lean_dec_ref(v_xs_3417_);
return v_res_3425_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(lean_object* v_xs_3426_, lean_object* v_lctx_3427_, uint8_t v_usedLetOnly_3428_, uint8_t v_generalizeNondepLet_3429_, lean_object* v_x_3430_, lean_object* v_x_3431_){
_start:
{
lean_object* v_zero_3432_; uint8_t v_isZero_3433_; 
v_zero_3432_ = lean_unsigned_to_nat(0u);
v_isZero_3433_ = lean_nat_dec_eq(v_x_3430_, v_zero_3432_);
if (v_isZero_3433_ == 1)
{
lean_dec_ref(v_lctx_3427_);
return v_x_3431_;
}
else
{
lean_object* v_one_3434_; lean_object* v_n_3435_; lean_object* v_n_3437_; lean_object* v_ty_3438_; uint8_t v_bi_3439_; lean_object* v_x_3443_; lean_object* v___x_3444_; 
v_one_3434_ = lean_unsigned_to_nat(1u);
v_n_3435_ = lean_nat_sub(v_x_3430_, v_one_3434_);
v_x_3443_ = lean_array_fget_borrowed(v_xs_3426_, v_n_3435_);
lean_inc_ref(v_lctx_3427_);
v___x_3444_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3427_, v_x_3443_);
if (lean_obj_tag(v___x_3444_) == 0)
{
lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; 
lean_dec_ref(v_x_3431_);
v___x_3445_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3446_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3445_);
v___x_3447_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3426_, v_lctx_3427_, v_usedLetOnly_3428_, v_generalizeNondepLet_3429_, v_n_3435_, v___x_3446_);
return v___x_3447_;
}
else
{
lean_object* v_val_3448_; 
v_val_3448_ = lean_ctor_get(v___x_3444_, 0);
lean_inc(v_val_3448_);
lean_dec_ref(v___x_3444_);
if (lean_obj_tag(v_val_3448_) == 0)
{
lean_object* v_userName_3449_; lean_object* v_type_3450_; uint8_t v_bi_3451_; 
v_userName_3449_ = lean_ctor_get(v_val_3448_, 2);
lean_inc(v_userName_3449_);
v_type_3450_ = lean_ctor_get(v_val_3448_, 3);
lean_inc_ref(v_type_3450_);
v_bi_3451_ = lean_ctor_get_uint8(v_val_3448_, sizeof(void*)*4);
lean_dec_ref(v_val_3448_);
v_n_3437_ = v_userName_3449_;
v_ty_3438_ = v_type_3450_;
v_bi_3439_ = v_bi_3451_;
goto v___jp_3436_;
}
else
{
lean_object* v_userName_3452_; lean_object* v_type_3453_; lean_object* v_value_3454_; uint8_t v_nondep_3455_; uint8_t v___y_3462_; 
v_userName_3452_ = lean_ctor_get(v_val_3448_, 2);
lean_inc(v_userName_3452_);
v_type_3453_ = lean_ctor_get(v_val_3448_, 3);
lean_inc_ref(v_type_3453_);
v_value_3454_ = lean_ctor_get(v_val_3448_, 4);
lean_inc_ref(v_value_3454_);
v_nondep_3455_ = lean_ctor_get_uint8(v_val_3448_, sizeof(void*)*5);
lean_dec_ref(v_val_3448_);
if (v_nondep_3455_ == 0)
{
v___y_3462_ = v_nondep_3455_;
goto v___jp_3461_;
}
else
{
if (v_generalizeNondepLet_3429_ == 0)
{
v___y_3462_ = v_generalizeNondepLet_3429_;
goto v___jp_3461_;
}
else
{
uint8_t v___x_3466_; 
lean_dec_ref(v_value_3454_);
v___x_3466_ = 0;
v_n_3437_ = v_userName_3452_;
v_ty_3438_ = v_type_3453_;
v_bi_3439_ = v___x_3466_;
goto v___jp_3436_;
}
}
v___jp_3456_:
{
lean_object* v_ty_3457_; lean_object* v_val_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; 
v_ty_3457_ = lean_expr_abstract_range(v_type_3453_, v_n_3435_, v_xs_3426_);
lean_dec_ref(v_type_3453_);
v_val_3458_ = lean_expr_abstract_range(v_value_3454_, v_n_3435_, v_xs_3426_);
lean_dec_ref(v_value_3454_);
v___x_3459_ = l_Lean_Expr_letE___override(v_userName_3452_, v_ty_3457_, v_val_3458_, v_x_3431_, v_nondep_3455_);
v___x_3460_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3426_, v_lctx_3427_, v_usedLetOnly_3428_, v_generalizeNondepLet_3429_, v_n_3435_, v___x_3459_);
return v___x_3460_;
}
v___jp_3461_:
{
if (v_usedLetOnly_3428_ == 0)
{
goto v___jp_3456_;
}
else
{
if (v___y_3462_ == 0)
{
uint8_t v___x_3463_; 
v___x_3463_ = lean_expr_has_loose_bvar(v_x_3431_, v_zero_3432_);
if (v___x_3463_ == 0)
{
lean_object* v___x_3464_; lean_object* v___x_3465_; 
lean_dec_ref(v_value_3454_);
lean_dec_ref(v_type_3453_);
lean_dec(v_userName_3452_);
v___x_3464_ = lean_expr_lower_loose_bvars(v_x_3431_, v_one_3434_, v_one_3434_);
lean_dec_ref(v_x_3431_);
v___x_3465_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3426_, v_lctx_3427_, v_usedLetOnly_3428_, v_generalizeNondepLet_3429_, v_n_3435_, v___x_3464_);
return v___x_3465_;
}
else
{
goto v___jp_3456_;
}
}
else
{
goto v___jp_3456_;
}
}
}
}
}
v___jp_3436_:
{
lean_object* v_ty_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; 
v_ty_3440_ = lean_expr_abstract_range(v_ty_3438_, v_n_3435_, v_xs_3426_);
lean_dec_ref(v_ty_3438_);
v___x_3441_ = l_Lean_mkLambda(v_n_3437_, v_bi_3439_, v_ty_3440_, v_x_3431_);
v___x_3442_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3426_, v_lctx_3427_, v_usedLetOnly_3428_, v_generalizeNondepLet_3429_, v_n_3435_, v___x_3441_);
return v___x_3442_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0___boxed(lean_object* v_xs_3467_, lean_object* v_lctx_3468_, lean_object* v_usedLetOnly_3469_, lean_object* v_generalizeNondepLet_3470_, lean_object* v_x_3471_, lean_object* v_x_3472_){
_start:
{
uint8_t v_usedLetOnly_boxed_3473_; uint8_t v_generalizeNondepLet_boxed_3474_; lean_object* v_res_3475_; 
v_usedLetOnly_boxed_3473_ = lean_unbox(v_usedLetOnly_3469_);
v_generalizeNondepLet_boxed_3474_ = lean_unbox(v_generalizeNondepLet_3470_);
v_res_3475_ = l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(v_xs_3467_, v_lctx_3468_, v_usedLetOnly_boxed_3473_, v_generalizeNondepLet_boxed_3474_, v_x_3471_, v_x_3472_);
lean_dec(v_x_3471_);
lean_dec_ref(v_xs_3467_);
return v_res_3475_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLambda(lean_object* v_lctx_3476_, lean_object* v_xs_3477_, lean_object* v_b_3478_, uint8_t v_usedLetOnly_3479_, uint8_t v_generalizeNondepLet_3480_){
_start:
{
lean_object* v_b_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; 
v_b_3481_ = lean_expr_abstract(v_b_3478_, v_xs_3477_);
v___x_3482_ = lean_array_get_size(v_xs_3477_);
v___x_3483_ = l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(v_xs_3477_, v_lctx_3476_, v_usedLetOnly_3479_, v_generalizeNondepLet_3480_, v___x_3482_, v_b_3481_);
return v___x_3483_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLambda___boxed(lean_object* v_lctx_3484_, lean_object* v_xs_3485_, lean_object* v_b_3486_, lean_object* v_usedLetOnly_3487_, lean_object* v_generalizeNondepLet_3488_){
_start:
{
uint8_t v_usedLetOnly_boxed_3489_; uint8_t v_generalizeNondepLet_boxed_3490_; lean_object* v_res_3491_; 
v_usedLetOnly_boxed_3489_ = lean_unbox(v_usedLetOnly_3487_);
v_generalizeNondepLet_boxed_3490_ = lean_unbox(v_generalizeNondepLet_3488_);
v_res_3491_ = l_Lean_LocalContext_mkLambda(v_lctx_3484_, v_xs_3485_, v_b_3486_, v_usedLetOnly_boxed_3489_, v_generalizeNondepLet_boxed_3490_);
lean_dec_ref(v_b_3486_);
lean_dec_ref(v_xs_3485_);
return v_res_3491_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(lean_object* v_xs_3492_, lean_object* v_lctx_3493_, uint8_t v_usedLetOnly_3494_, uint8_t v_generalizeNondepLet_3495_, lean_object* v_x_3496_, lean_object* v_x_3497_){
_start:
{
lean_object* v_zero_3498_; uint8_t v_isZero_3499_; 
v_zero_3498_ = lean_unsigned_to_nat(0u);
v_isZero_3499_ = lean_nat_dec_eq(v_x_3496_, v_zero_3498_);
if (v_isZero_3499_ == 1)
{
lean_dec(v_x_3496_);
lean_dec_ref(v_lctx_3493_);
return v_x_3497_;
}
else
{
lean_object* v_one_3500_; lean_object* v_n_3501_; lean_object* v_n_3503_; lean_object* v_ty_3504_; uint8_t v_bi_3505_; lean_object* v_x_3509_; lean_object* v___x_3510_; 
v_one_3500_ = lean_unsigned_to_nat(1u);
v_n_3501_ = lean_nat_sub(v_x_3496_, v_one_3500_);
lean_dec(v_x_3496_);
v_x_3509_ = lean_array_fget_borrowed(v_xs_3492_, v_n_3501_);
lean_inc_ref(v_lctx_3493_);
v___x_3510_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3493_, v_x_3509_);
if (lean_obj_tag(v___x_3510_) == 0)
{
lean_object* v___x_3511_; lean_object* v___x_3512_; 
lean_dec_ref(v_x_3497_);
v___x_3511_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3512_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3511_);
v_x_3496_ = v_n_3501_;
v_x_3497_ = v___x_3512_;
goto _start;
}
else
{
lean_object* v_val_3514_; 
v_val_3514_ = lean_ctor_get(v___x_3510_, 0);
lean_inc(v_val_3514_);
lean_dec_ref(v___x_3510_);
if (lean_obj_tag(v_val_3514_) == 0)
{
lean_object* v_userName_3515_; lean_object* v_type_3516_; uint8_t v_bi_3517_; 
v_userName_3515_ = lean_ctor_get(v_val_3514_, 2);
lean_inc(v_userName_3515_);
v_type_3516_ = lean_ctor_get(v_val_3514_, 3);
lean_inc_ref(v_type_3516_);
v_bi_3517_ = lean_ctor_get_uint8(v_val_3514_, sizeof(void*)*4);
lean_dec_ref(v_val_3514_);
v_n_3503_ = v_userName_3515_;
v_ty_3504_ = v_type_3516_;
v_bi_3505_ = v_bi_3517_;
goto v___jp_3502_;
}
else
{
lean_object* v_userName_3518_; lean_object* v_type_3519_; lean_object* v_value_3520_; uint8_t v_nondep_3521_; uint8_t v___y_3528_; 
v_userName_3518_ = lean_ctor_get(v_val_3514_, 2);
lean_inc(v_userName_3518_);
v_type_3519_ = lean_ctor_get(v_val_3514_, 3);
lean_inc_ref(v_type_3519_);
v_value_3520_ = lean_ctor_get(v_val_3514_, 4);
lean_inc_ref(v_value_3520_);
v_nondep_3521_ = lean_ctor_get_uint8(v_val_3514_, sizeof(void*)*5);
lean_dec_ref(v_val_3514_);
if (v_nondep_3521_ == 0)
{
v___y_3528_ = v_nondep_3521_;
goto v___jp_3527_;
}
else
{
if (v_generalizeNondepLet_3495_ == 0)
{
v___y_3528_ = v_generalizeNondepLet_3495_;
goto v___jp_3527_;
}
else
{
uint8_t v___x_3532_; 
lean_dec_ref(v_value_3520_);
v___x_3532_ = 0;
v_n_3503_ = v_userName_3518_;
v_ty_3504_ = v_type_3519_;
v_bi_3505_ = v___x_3532_;
goto v___jp_3502_;
}
}
v___jp_3522_:
{
lean_object* v_ty_3523_; lean_object* v_val_3524_; lean_object* v___x_3525_; 
v_ty_3523_ = lean_expr_abstract_range(v_type_3519_, v_n_3501_, v_xs_3492_);
lean_dec_ref(v_type_3519_);
v_val_3524_ = lean_expr_abstract_range(v_value_3520_, v_n_3501_, v_xs_3492_);
lean_dec_ref(v_value_3520_);
v___x_3525_ = l_Lean_Expr_letE___override(v_userName_3518_, v_ty_3523_, v_val_3524_, v_x_3497_, v_nondep_3521_);
v_x_3496_ = v_n_3501_;
v_x_3497_ = v___x_3525_;
goto _start;
}
v___jp_3527_:
{
if (v_usedLetOnly_3494_ == 0)
{
goto v___jp_3522_;
}
else
{
if (v___y_3528_ == 0)
{
uint8_t v___x_3529_; 
v___x_3529_ = lean_expr_has_loose_bvar(v_x_3497_, v_zero_3498_);
if (v___x_3529_ == 0)
{
lean_object* v___x_3530_; 
lean_dec_ref(v_value_3520_);
lean_dec_ref(v_type_3519_);
lean_dec(v_userName_3518_);
v___x_3530_ = lean_expr_lower_loose_bvars(v_x_3497_, v_one_3500_, v_one_3500_);
lean_dec_ref(v_x_3497_);
v_x_3496_ = v_n_3501_;
v_x_3497_ = v___x_3530_;
goto _start;
}
else
{
goto v___jp_3522_;
}
}
else
{
goto v___jp_3522_;
}
}
}
}
}
v___jp_3502_:
{
lean_object* v_ty_3506_; lean_object* v___x_3507_; 
v_ty_3506_ = lean_expr_abstract_range(v_ty_3504_, v_n_3501_, v_xs_3492_);
lean_dec_ref(v_ty_3504_);
v___x_3507_ = l_Lean_mkForall(v_n_3503_, v_bi_3505_, v_ty_3506_, v_x_3497_);
v_x_3496_ = v_n_3501_;
v_x_3497_ = v___x_3507_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0___boxed(lean_object* v_xs_3533_, lean_object* v_lctx_3534_, lean_object* v_usedLetOnly_3535_, lean_object* v_generalizeNondepLet_3536_, lean_object* v_x_3537_, lean_object* v_x_3538_){
_start:
{
uint8_t v_usedLetOnly_boxed_3539_; uint8_t v_generalizeNondepLet_boxed_3540_; lean_object* v_res_3541_; 
v_usedLetOnly_boxed_3539_ = lean_unbox(v_usedLetOnly_3535_);
v_generalizeNondepLet_boxed_3540_ = lean_unbox(v_generalizeNondepLet_3536_);
v_res_3541_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3533_, v_lctx_3534_, v_usedLetOnly_boxed_3539_, v_generalizeNondepLet_boxed_3540_, v_x_3537_, v_x_3538_);
lean_dec_ref(v_xs_3533_);
return v_res_3541_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(lean_object* v_xs_3542_, lean_object* v_lctx_3543_, uint8_t v_usedLetOnly_3544_, uint8_t v_generalizeNondepLet_3545_, lean_object* v_x_3546_, lean_object* v_x_3547_){
_start:
{
lean_object* v_zero_3548_; uint8_t v_isZero_3549_; 
v_zero_3548_ = lean_unsigned_to_nat(0u);
v_isZero_3549_ = lean_nat_dec_eq(v_x_3546_, v_zero_3548_);
if (v_isZero_3549_ == 1)
{
lean_dec_ref(v_lctx_3543_);
return v_x_3547_;
}
else
{
lean_object* v_one_3550_; lean_object* v_n_3551_; lean_object* v_n_3553_; lean_object* v_ty_3554_; uint8_t v_bi_3555_; lean_object* v_x_3559_; lean_object* v___x_3560_; 
v_one_3550_ = lean_unsigned_to_nat(1u);
v_n_3551_ = lean_nat_sub(v_x_3546_, v_one_3550_);
v_x_3559_ = lean_array_fget_borrowed(v_xs_3542_, v_n_3551_);
lean_inc_ref(v_lctx_3543_);
v___x_3560_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3543_, v_x_3559_);
if (lean_obj_tag(v___x_3560_) == 0)
{
lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; 
lean_dec_ref(v_x_3547_);
v___x_3561_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3562_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3561_);
v___x_3563_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3542_, v_lctx_3543_, v_usedLetOnly_3544_, v_generalizeNondepLet_3545_, v_n_3551_, v___x_3562_);
return v___x_3563_;
}
else
{
lean_object* v_val_3564_; 
v_val_3564_ = lean_ctor_get(v___x_3560_, 0);
lean_inc(v_val_3564_);
lean_dec_ref(v___x_3560_);
if (lean_obj_tag(v_val_3564_) == 0)
{
lean_object* v_userName_3565_; lean_object* v_type_3566_; uint8_t v_bi_3567_; 
v_userName_3565_ = lean_ctor_get(v_val_3564_, 2);
lean_inc(v_userName_3565_);
v_type_3566_ = lean_ctor_get(v_val_3564_, 3);
lean_inc_ref(v_type_3566_);
v_bi_3567_ = lean_ctor_get_uint8(v_val_3564_, sizeof(void*)*4);
lean_dec_ref(v_val_3564_);
v_n_3553_ = v_userName_3565_;
v_ty_3554_ = v_type_3566_;
v_bi_3555_ = v_bi_3567_;
goto v___jp_3552_;
}
else
{
lean_object* v_userName_3568_; lean_object* v_type_3569_; lean_object* v_value_3570_; uint8_t v_nondep_3571_; uint8_t v___y_3578_; 
v_userName_3568_ = lean_ctor_get(v_val_3564_, 2);
lean_inc(v_userName_3568_);
v_type_3569_ = lean_ctor_get(v_val_3564_, 3);
lean_inc_ref(v_type_3569_);
v_value_3570_ = lean_ctor_get(v_val_3564_, 4);
lean_inc_ref(v_value_3570_);
v_nondep_3571_ = lean_ctor_get_uint8(v_val_3564_, sizeof(void*)*5);
lean_dec_ref(v_val_3564_);
if (v_nondep_3571_ == 0)
{
v___y_3578_ = v_nondep_3571_;
goto v___jp_3577_;
}
else
{
if (v_generalizeNondepLet_3545_ == 0)
{
v___y_3578_ = v_generalizeNondepLet_3545_;
goto v___jp_3577_;
}
else
{
uint8_t v___x_3582_; 
lean_dec_ref(v_value_3570_);
v___x_3582_ = 0;
v_n_3553_ = v_userName_3568_;
v_ty_3554_ = v_type_3569_;
v_bi_3555_ = v___x_3582_;
goto v___jp_3552_;
}
}
v___jp_3572_:
{
lean_object* v_ty_3573_; lean_object* v_val_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; 
v_ty_3573_ = lean_expr_abstract_range(v_type_3569_, v_n_3551_, v_xs_3542_);
lean_dec_ref(v_type_3569_);
v_val_3574_ = lean_expr_abstract_range(v_value_3570_, v_n_3551_, v_xs_3542_);
lean_dec_ref(v_value_3570_);
v___x_3575_ = l_Lean_Expr_letE___override(v_userName_3568_, v_ty_3573_, v_val_3574_, v_x_3547_, v_nondep_3571_);
v___x_3576_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3542_, v_lctx_3543_, v_usedLetOnly_3544_, v_generalizeNondepLet_3545_, v_n_3551_, v___x_3575_);
return v___x_3576_;
}
v___jp_3577_:
{
if (v_usedLetOnly_3544_ == 0)
{
goto v___jp_3572_;
}
else
{
if (v___y_3578_ == 0)
{
uint8_t v___x_3579_; 
v___x_3579_ = lean_expr_has_loose_bvar(v_x_3547_, v_zero_3548_);
if (v___x_3579_ == 0)
{
lean_object* v___x_3580_; lean_object* v___x_3581_; 
lean_dec_ref(v_value_3570_);
lean_dec_ref(v_type_3569_);
lean_dec(v_userName_3568_);
v___x_3580_ = lean_expr_lower_loose_bvars(v_x_3547_, v_one_3550_, v_one_3550_);
lean_dec_ref(v_x_3547_);
v___x_3581_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3542_, v_lctx_3543_, v_usedLetOnly_3544_, v_generalizeNondepLet_3545_, v_n_3551_, v___x_3580_);
return v___x_3581_;
}
else
{
goto v___jp_3572_;
}
}
else
{
goto v___jp_3572_;
}
}
}
}
}
v___jp_3552_:
{
lean_object* v_ty_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; 
v_ty_3556_ = lean_expr_abstract_range(v_ty_3554_, v_n_3551_, v_xs_3542_);
lean_dec_ref(v_ty_3554_);
v___x_3557_ = l_Lean_mkForall(v_n_3553_, v_bi_3555_, v_ty_3556_, v_x_3547_);
v___x_3558_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3542_, v_lctx_3543_, v_usedLetOnly_3544_, v_generalizeNondepLet_3545_, v_n_3551_, v___x_3557_);
return v___x_3558_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0___boxed(lean_object* v_xs_3583_, lean_object* v_lctx_3584_, lean_object* v_usedLetOnly_3585_, lean_object* v_generalizeNondepLet_3586_, lean_object* v_x_3587_, lean_object* v_x_3588_){
_start:
{
uint8_t v_usedLetOnly_boxed_3589_; uint8_t v_generalizeNondepLet_boxed_3590_; lean_object* v_res_3591_; 
v_usedLetOnly_boxed_3589_ = lean_unbox(v_usedLetOnly_3585_);
v_generalizeNondepLet_boxed_3590_ = lean_unbox(v_generalizeNondepLet_3586_);
v_res_3591_ = l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(v_xs_3583_, v_lctx_3584_, v_usedLetOnly_boxed_3589_, v_generalizeNondepLet_boxed_3590_, v_x_3587_, v_x_3588_);
lean_dec(v_x_3587_);
lean_dec_ref(v_xs_3583_);
return v_res_3591_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkForall(lean_object* v_lctx_3592_, lean_object* v_xs_3593_, lean_object* v_b_3594_, uint8_t v_usedLetOnly_3595_, uint8_t v_generalizeNondepLet_3596_){
_start:
{
lean_object* v_b_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; 
v_b_3597_ = lean_expr_abstract(v_b_3594_, v_xs_3593_);
v___x_3598_ = lean_array_get_size(v_xs_3593_);
v___x_3599_ = l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(v_xs_3593_, v_lctx_3592_, v_usedLetOnly_3595_, v_generalizeNondepLet_3596_, v___x_3598_, v_b_3597_);
return v___x_3599_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkForall___boxed(lean_object* v_lctx_3600_, lean_object* v_xs_3601_, lean_object* v_b_3602_, lean_object* v_usedLetOnly_3603_, lean_object* v_generalizeNondepLet_3604_){
_start:
{
uint8_t v_usedLetOnly_boxed_3605_; uint8_t v_generalizeNondepLet_boxed_3606_; lean_object* v_res_3607_; 
v_usedLetOnly_boxed_3605_ = lean_unbox(v_usedLetOnly_3603_);
v_generalizeNondepLet_boxed_3606_ = lean_unbox(v_generalizeNondepLet_3604_);
v_res_3607_ = l_Lean_LocalContext_mkForall(v_lctx_3600_, v_xs_3601_, v_b_3602_, v_usedLetOnly_boxed_3605_, v_generalizeNondepLet_boxed_3606_);
lean_dec_ref(v_b_3602_);
lean_dec_ref(v_xs_3601_);
return v_res_3607_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM___redArg___lam__0(lean_object* v_toPure_3608_, lean_object* v_p_3609_, lean_object* v_d_3610_){
_start:
{
if (lean_obj_tag(v_d_3610_) == 0)
{
uint8_t v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; 
lean_dec(v_p_3609_);
v___x_3611_ = 0;
v___x_3612_ = lean_box(v___x_3611_);
v___x_3613_ = lean_apply_2(v_toPure_3608_, lean_box(0), v___x_3612_);
return v___x_3613_;
}
else
{
lean_object* v_val_3614_; lean_object* v___x_3615_; 
lean_dec(v_toPure_3608_);
v_val_3614_ = lean_ctor_get(v_d_3610_, 0);
lean_inc(v_val_3614_);
lean_dec_ref(v_d_3610_);
v___x_3615_ = lean_apply_1(v_p_3609_, v_val_3614_);
return v___x_3615_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM___redArg(lean_object* v_inst_3616_, lean_object* v_lctx_3617_, lean_object* v_p_3618_){
_start:
{
lean_object* v_toApplicative_3619_; lean_object* v_decls_3620_; lean_object* v_toPure_3621_; lean_object* v___f_3622_; lean_object* v___x_3623_; 
v_toApplicative_3619_ = lean_ctor_get(v_inst_3616_, 0);
v_decls_3620_ = lean_ctor_get(v_lctx_3617_, 1);
lean_inc_ref(v_decls_3620_);
lean_dec_ref(v_lctx_3617_);
v_toPure_3621_ = lean_ctor_get(v_toApplicative_3619_, 1);
lean_inc(v_toPure_3621_);
v___f_3622_ = lean_alloc_closure((void*)(l_Lean_LocalContext_anyM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3622_, 0, v_toPure_3621_);
lean_closure_set(v___f_3622_, 1, v_p_3618_);
v___x_3623_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3616_, v_decls_3620_, v___f_3622_);
return v___x_3623_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM(lean_object* v_m_3624_, lean_object* v_inst_3625_, lean_object* v_lctx_3626_, lean_object* v_p_3627_){
_start:
{
lean_object* v_toApplicative_3628_; lean_object* v_decls_3629_; lean_object* v_toPure_3630_; lean_object* v___f_3631_; lean_object* v___x_3632_; 
v_toApplicative_3628_ = lean_ctor_get(v_inst_3625_, 0);
v_decls_3629_ = lean_ctor_get(v_lctx_3626_, 1);
lean_inc_ref(v_decls_3629_);
lean_dec_ref(v_lctx_3626_);
v_toPure_3630_ = lean_ctor_get(v_toApplicative_3628_, 1);
lean_inc(v_toPure_3630_);
v___f_3631_ = lean_alloc_closure((void*)(l_Lean_LocalContext_anyM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3631_, 0, v_toPure_3630_);
lean_closure_set(v___f_3631_, 1, v_p_3627_);
v___x_3632_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3625_, v_decls_3629_, v___f_3631_);
return v___x_3632_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__0(lean_object* v_toPure_3633_, uint8_t v_b_3634_){
_start:
{
if (v_b_3634_ == 0)
{
uint8_t v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; 
v___x_3635_ = 1;
v___x_3636_ = lean_box(v___x_3635_);
v___x_3637_ = lean_apply_2(v_toPure_3633_, lean_box(0), v___x_3636_);
return v___x_3637_;
}
else
{
uint8_t v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; 
v___x_3638_ = 0;
v___x_3639_ = lean_box(v___x_3638_);
v___x_3640_ = lean_apply_2(v_toPure_3633_, lean_box(0), v___x_3639_);
return v___x_3640_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__0___boxed(lean_object* v_toPure_3641_, lean_object* v_b_3642_){
_start:
{
uint8_t v_b_boxed_3643_; lean_object* v_res_3644_; 
v_b_boxed_3643_ = lean_unbox(v_b_3642_);
v_res_3644_ = l_Lean_LocalContext_allM___redArg___lam__0(v_toPure_3641_, v_b_boxed_3643_);
return v_res_3644_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__2(lean_object* v_toPure_3645_, lean_object* v_toBind_3646_, lean_object* v___f_3647_, lean_object* v_p_3648_, lean_object* v_v_3649_){
_start:
{
if (lean_obj_tag(v_v_3649_) == 0)
{
uint8_t v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; 
lean_dec(v_p_3648_);
v___x_3650_ = 1;
v___x_3651_ = lean_box(v___x_3650_);
v___x_3652_ = lean_apply_2(v_toPure_3645_, lean_box(0), v___x_3651_);
v___x_3653_ = lean_apply_4(v_toBind_3646_, lean_box(0), lean_box(0), v___x_3652_, v___f_3647_);
return v___x_3653_;
}
else
{
lean_object* v_val_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; 
lean_dec(v_toPure_3645_);
v_val_3654_ = lean_ctor_get(v_v_3649_, 0);
lean_inc(v_val_3654_);
lean_dec_ref(v_v_3649_);
v___x_3655_ = lean_apply_1(v_p_3648_, v_val_3654_);
v___x_3656_ = lean_apply_4(v_toBind_3646_, lean_box(0), lean_box(0), v___x_3655_, v___f_3647_);
return v___x_3656_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg(lean_object* v_inst_3657_, lean_object* v_lctx_3658_, lean_object* v_p_3659_){
_start:
{
lean_object* v_toApplicative_3660_; lean_object* v_decls_3661_; lean_object* v_toBind_3662_; lean_object* v_toPure_3663_; lean_object* v___f_3664_; lean_object* v___f_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; 
v_toApplicative_3660_ = lean_ctor_get(v_inst_3657_, 0);
v_decls_3661_ = lean_ctor_get(v_lctx_3658_, 1);
lean_inc_ref(v_decls_3661_);
lean_dec_ref(v_lctx_3658_);
v_toBind_3662_ = lean_ctor_get(v_inst_3657_, 1);
lean_inc(v_toBind_3662_);
v_toPure_3663_ = lean_ctor_get(v_toApplicative_3660_, 1);
lean_inc(v_toPure_3663_);
v___f_3664_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3664_, 0, v_toPure_3663_);
lean_inc_ref(v___f_3664_);
lean_inc(v_toBind_3662_);
lean_inc(v_toPure_3663_);
v___f_3665_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3665_, 0, v_toPure_3663_);
lean_closure_set(v___f_3665_, 1, v_toBind_3662_);
lean_closure_set(v___f_3665_, 2, v___f_3664_);
lean_closure_set(v___f_3665_, 3, v_p_3659_);
v___x_3666_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3657_, v_decls_3661_, v___f_3665_);
v___x_3667_ = lean_apply_4(v_toBind_3662_, lean_box(0), lean_box(0), v___x_3666_, v___f_3664_);
return v___x_3667_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM(lean_object* v_m_3668_, lean_object* v_inst_3669_, lean_object* v_lctx_3670_, lean_object* v_p_3671_){
_start:
{
lean_object* v_toApplicative_3672_; lean_object* v_decls_3673_; lean_object* v_toBind_3674_; lean_object* v_toPure_3675_; lean_object* v___f_3676_; lean_object* v___f_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; 
v_toApplicative_3672_ = lean_ctor_get(v_inst_3669_, 0);
v_decls_3673_ = lean_ctor_get(v_lctx_3670_, 1);
lean_inc_ref(v_decls_3673_);
lean_dec_ref(v_lctx_3670_);
v_toBind_3674_ = lean_ctor_get(v_inst_3669_, 1);
lean_inc(v_toBind_3674_);
v_toPure_3675_ = lean_ctor_get(v_toApplicative_3672_, 1);
lean_inc(v_toPure_3675_);
v___f_3676_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3676_, 0, v_toPure_3675_);
lean_inc_ref(v___f_3676_);
lean_inc(v_toBind_3674_);
lean_inc(v_toPure_3675_);
v___f_3677_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3677_, 0, v_toPure_3675_);
lean_closure_set(v___f_3677_, 1, v_toBind_3674_);
lean_closure_set(v___f_3677_, 2, v___f_3676_);
lean_closure_set(v___f_3677_, 3, v_p_3671_);
v___x_3678_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3669_, v_decls_3673_, v___f_3677_);
v___x_3679_ = lean_apply_4(v_toBind_3674_, lean_box(0), lean_box(0), v___x_3678_, v___f_3676_);
return v___x_3679_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_any___lam__0(lean_object* v_p_3680_, lean_object* v_d_3681_){
_start:
{
if (lean_obj_tag(v_d_3681_) == 0)
{
uint8_t v___x_3682_; 
lean_dec_ref(v_p_3680_);
v___x_3682_ = 0;
return v___x_3682_;
}
else
{
lean_object* v_val_3683_; lean_object* v___x_3684_; uint8_t v___x_3685_; 
v_val_3683_ = lean_ctor_get(v_d_3681_, 0);
lean_inc(v_val_3683_);
lean_dec_ref(v_d_3681_);
v___x_3684_ = lean_apply_1(v_p_3680_, v_val_3683_);
v___x_3685_ = lean_unbox(v___x_3684_);
return v___x_3685_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_any___lam__0___boxed(lean_object* v_p_3686_, lean_object* v_d_3687_){
_start:
{
uint8_t v_res_3688_; lean_object* v_r_3689_; 
v_res_3688_ = l_Lean_LocalContext_any___lam__0(v_p_3686_, v_d_3687_);
v_r_3689_ = lean_box(v_res_3688_);
return v_r_3689_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_any(lean_object* v_lctx_3690_, lean_object* v_p_3691_){
_start:
{
lean_object* v___x_3692_; lean_object* v_decls_3693_; lean_object* v___f_3694_; lean_object* v___x_3695_; uint8_t v___x_3696_; 
v___x_3692_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v_decls_3693_ = lean_ctor_get(v_lctx_3690_, 1);
lean_inc_ref(v_decls_3693_);
lean_dec_ref(v_lctx_3690_);
v___f_3694_ = lean_alloc_closure((void*)(l_Lean_LocalContext_any___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3694_, 0, v_p_3691_);
v___x_3695_ = l_Lean_PersistentArray_anyM___redArg(v___x_3692_, v_decls_3693_, v___f_3694_);
v___x_3696_ = lean_unbox(v___x_3695_);
lean_dec(v___x_3695_);
return v___x_3696_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_any___boxed(lean_object* v_lctx_3697_, lean_object* v_p_3698_){
_start:
{
uint8_t v_res_3699_; lean_object* v_r_3700_; 
v_res_3699_ = l_Lean_LocalContext_any(v_lctx_3697_, v_p_3698_);
v_r_3700_ = lean_box(v_res_3699_);
return v_r_3700_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_all___lam__0(lean_object* v_p_3701_, lean_object* v_v_3702_){
_start:
{
if (lean_obj_tag(v_v_3702_) == 0)
{
uint8_t v___x_3703_; 
lean_dec_ref(v_p_3701_);
v___x_3703_ = 0;
return v___x_3703_;
}
else
{
lean_object* v_val_3704_; lean_object* v___x_3705_; uint8_t v___x_3706_; 
v_val_3704_ = lean_ctor_get(v_v_3702_, 0);
lean_inc(v_val_3704_);
lean_dec_ref(v_v_3702_);
v___x_3705_ = lean_apply_1(v_p_3701_, v_val_3704_);
v___x_3706_ = lean_unbox(v___x_3705_);
if (v___x_3706_ == 0)
{
uint8_t v___x_3707_; 
v___x_3707_ = 1;
return v___x_3707_;
}
else
{
uint8_t v___x_3708_; 
v___x_3708_ = 0;
return v___x_3708_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_all___lam__0___boxed(lean_object* v_p_3709_, lean_object* v_v_3710_){
_start:
{
uint8_t v_res_3711_; lean_object* v_r_3712_; 
v_res_3711_ = l_Lean_LocalContext_all___lam__0(v_p_3709_, v_v_3710_);
v_r_3712_ = lean_box(v_res_3711_);
return v_r_3712_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_all(lean_object* v_lctx_3713_, lean_object* v_p_3714_){
_start:
{
lean_object* v___x_3715_; lean_object* v_decls_3716_; lean_object* v___f_3717_; lean_object* v___x_3718_; uint8_t v___x_3719_; 
v___x_3715_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v_decls_3716_ = lean_ctor_get(v_lctx_3713_, 1);
lean_inc_ref(v_decls_3716_);
lean_dec_ref(v_lctx_3713_);
v___f_3717_ = lean_alloc_closure((void*)(l_Lean_LocalContext_all___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3717_, 0, v_p_3714_);
v___x_3718_ = l_Lean_PersistentArray_anyM___redArg(v___x_3715_, v_decls_3716_, v___f_3717_);
v___x_3719_ = lean_unbox(v___x_3718_);
lean_dec(v___x_3718_);
if (v___x_3719_ == 0)
{
uint8_t v___x_3720_; 
v___x_3720_ = 1;
return v___x_3720_;
}
else
{
uint8_t v___x_3721_; 
v___x_3721_ = 0;
return v___x_3721_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_all___boxed(lean_object* v_lctx_3722_, lean_object* v_p_3723_){
_start:
{
uint8_t v_res_3724_; lean_object* v_r_3725_; 
v_res_3724_ = l_Lean_LocalContext_all(v_lctx_3722_, v_p_3723_);
v_r_3725_ = lean_box(v_res_3724_);
return v_r_3725_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(lean_object* v_i_3726_, lean_object* v_a_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_){
_start:
{
lean_object* v_zero_3730_; uint8_t v_isZero_3731_; 
v_zero_3730_ = lean_unsigned_to_nat(0u);
v_isZero_3731_ = lean_nat_dec_eq(v_i_3726_, v_zero_3730_);
if (v_isZero_3731_ == 1)
{
lean_object* v___x_3732_; lean_object* v___x_3733_; 
lean_dec(v_i_3726_);
v___x_3732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3732_, 0, v_a_3727_);
lean_ctor_set(v___x_3732_, 1, v___y_3728_);
v___x_3733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3732_);
lean_ctor_set(v___x_3733_, 1, v___y_3729_);
return v___x_3733_;
}
else
{
lean_object* v_decls_3734_; lean_object* v_size_3735_; lean_object* v_one_3736_; lean_object* v_n_3737_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v___y_3746_; lean_object* v___y_3747_; lean_object* v___y_3754_; lean_object* v___y_3755_; uint8_t v___y_3756_; lean_object* v___y_3760_; lean_object* v___y_3761_; lean_object* v___y_3766_; lean_object* v___x_3770_; uint8_t v___x_3771_; 
v_decls_3734_ = lean_ctor_get(v_a_3727_, 1);
v_size_3735_ = lean_ctor_get(v_decls_3734_, 2);
v_one_3736_ = lean_unsigned_to_nat(1u);
v_n_3737_ = lean_nat_sub(v_i_3726_, v_one_3736_);
lean_dec(v_i_3726_);
v___x_3770_ = lean_box(0);
v___x_3771_ = lean_nat_dec_lt(v_n_3737_, v_size_3735_);
if (v___x_3771_ == 0)
{
lean_object* v___x_3772_; 
v___x_3772_ = l_outOfBounds___redArg(v___x_3770_);
v___y_3766_ = v___x_3772_;
goto v___jp_3765_;
}
else
{
lean_object* v___x_3773_; 
lean_inc_ref(v_decls_3734_);
v___x_3773_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3770_, v_decls_3734_, v_n_3737_);
v___y_3766_ = v___x_3773_;
goto v___jp_3765_;
}
v___jp_3738_:
{
lean_object* v___x_3743_; 
v___x_3743_ = l_Lean_LocalContext_setUserName(v_a_3727_, v___y_3742_, v___y_3741_);
v_i_3726_ = v_n_3737_;
v_a_3727_ = v___x_3743_;
v___y_3728_ = v___y_3739_;
v___y_3729_ = v___y_3740_;
goto _start;
}
v___jp_3745_:
{
lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v_fst_3750_; lean_object* v_snd_3751_; lean_object* v_fvarId_3752_; 
lean_inc(v___y_3747_);
v___x_3748_ = l_Lean_NameSet_insert(v___y_3728_, v___y_3747_);
v___x_3749_ = l_Lean_sanitizeName(v___y_3747_, v___y_3729_);
v_fst_3750_ = lean_ctor_get(v___x_3749_, 0);
lean_inc(v_fst_3750_);
v_snd_3751_ = lean_ctor_get(v___x_3749_, 1);
lean_inc(v_snd_3751_);
lean_dec_ref(v___x_3749_);
v_fvarId_3752_ = lean_ctor_get(v___y_3746_, 1);
lean_inc(v_fvarId_3752_);
lean_dec_ref(v___y_3746_);
v___y_3739_ = v___x_3748_;
v___y_3740_ = v_snd_3751_;
v___y_3741_ = v_fst_3750_;
v___y_3742_ = v_fvarId_3752_;
goto v___jp_3738_;
}
v___jp_3753_:
{
if (v___y_3756_ == 0)
{
lean_object* v___x_3757_; 
lean_dec_ref(v___y_3754_);
v___x_3757_ = l_Lean_NameSet_insert(v___y_3728_, v___y_3755_);
v_i_3726_ = v_n_3737_;
v___y_3728_ = v___x_3757_;
goto _start;
}
else
{
v___y_3746_ = v___y_3754_;
v___y_3747_ = v___y_3755_;
goto v___jp_3745_;
}
}
v___jp_3759_:
{
uint8_t v___x_3762_; 
v___x_3762_ = l_Lean_Name_hasMacroScopes(v___y_3761_);
if (v___x_3762_ == 0)
{
lean_object* v_userName_3763_; uint8_t v___x_3764_; 
v_userName_3763_ = lean_ctor_get(v___y_3760_, 2);
v___x_3764_ = l_Lean_NameSet_contains(v___y_3728_, v_userName_3763_);
v___y_3754_ = v___y_3760_;
v___y_3755_ = v___y_3761_;
v___y_3756_ = v___x_3764_;
goto v___jp_3753_;
}
else
{
v___y_3746_ = v___y_3760_;
v___y_3747_ = v___y_3761_;
goto v___jp_3745_;
}
}
v___jp_3765_:
{
if (lean_obj_tag(v___y_3766_) == 0)
{
v_i_3726_ = v_n_3737_;
goto _start;
}
else
{
lean_object* v_val_3768_; lean_object* v_userName_3769_; 
v_val_3768_ = lean_ctor_get(v___y_3766_, 0);
lean_inc(v_val_3768_);
lean_dec_ref(v___y_3766_);
v_userName_3769_ = lean_ctor_get(v_val_3768_, 2);
lean_inc(v_userName_3769_);
v___y_3760_ = v_val_3768_;
v___y_3761_ = v_userName_3769_;
goto v___jp_3759_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_sanitizeNames(lean_object* v_lctx_3774_, lean_object* v_a_3775_){
_start:
{
lean_object* v_options_3776_; uint8_t v___x_3777_; 
v_options_3776_ = lean_ctor_get(v_a_3775_, 0);
v___x_3777_ = l_Lean_getSanitizeNames(v_options_3776_);
if (v___x_3777_ == 0)
{
lean_object* v___x_3778_; 
v___x_3778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3778_, 0, v_lctx_3774_);
lean_ctor_set(v___x_3778_, 1, v_a_3775_);
return v___x_3778_;
}
else
{
lean_object* v_decls_3779_; lean_object* v_size_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v_fst_3783_; lean_object* v_snd_3784_; lean_object* v_fst_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3792_; 
v_decls_3779_ = lean_ctor_get(v_lctx_3774_, 1);
v_size_3780_ = lean_ctor_get(v_decls_3779_, 2);
lean_inc(v_size_3780_);
v___x_3781_ = l_Lean_NameSet_empty;
v___x_3782_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(v_size_3780_, v_lctx_3774_, v___x_3781_, v_a_3775_);
v_fst_3783_ = lean_ctor_get(v___x_3782_, 0);
lean_inc(v_fst_3783_);
v_snd_3784_ = lean_ctor_get(v___x_3782_, 1);
lean_inc(v_snd_3784_);
lean_dec_ref(v___x_3782_);
v_fst_3785_ = lean_ctor_get(v_fst_3783_, 0);
v_isSharedCheck_3792_ = !lean_is_exclusive(v_fst_3783_);
if (v_isSharedCheck_3792_ == 0)
{
lean_object* v_unused_3793_; 
v_unused_3793_ = lean_ctor_get(v_fst_3783_, 1);
lean_dec(v_unused_3793_);
v___x_3787_ = v_fst_3783_;
v_isShared_3788_ = v_isSharedCheck_3792_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_fst_3785_);
lean_dec(v_fst_3783_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3792_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
lean_object* v___x_3790_; 
if (v_isShared_3788_ == 0)
{
lean_ctor_set(v___x_3787_, 1, v_snd_3784_);
v___x_3790_ = v___x_3787_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v_fst_3785_);
lean_ctor_set(v_reuseFailAlloc_3791_, 1, v_snd_3784_);
v___x_3790_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
return v___x_3790_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0(lean_object* v_n_3794_, lean_object* v_i_3795_, lean_object* v_a_3796_, lean_object* v_a_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_){
_start:
{
lean_object* v___x_3800_; 
v___x_3800_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(v_i_3795_, v_a_3797_, v___y_3798_, v___y_3799_);
return v___x_3800_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___boxed(lean_object* v_n_3801_, lean_object* v_i_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_){
_start:
{
lean_object* v_res_3807_; 
v_res_3807_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0(v_n_3801_, v_i_3802_, v_a_3803_, v_a_3804_, v___y_3805_, v___y_3806_);
lean_dec(v_n_3801_);
return v_res_3807_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getRoundtrippingUserName_x3f(lean_object* v_lctx_3808_, lean_object* v_fvarId_3809_){
_start:
{
lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3818_; lean_object* v___y_3819_; lean_object* v___y_3820_; lean_object* v___x_3822_; 
lean_inc_ref(v_lctx_3808_);
v___x_3822_ = lean_local_ctx_find(v_lctx_3808_, v_fvarId_3809_);
if (lean_obj_tag(v___x_3822_) == 0)
{
lean_object* v___x_3823_; 
lean_dec_ref(v_lctx_3808_);
v___x_3823_ = lean_box(0);
return v___x_3823_;
}
else
{
lean_object* v_val_3824_; lean_object* v___y_3826_; lean_object* v_userName_3831_; 
v_val_3824_ = lean_ctor_get(v___x_3822_, 0);
lean_inc(v_val_3824_);
lean_dec_ref(v___x_3822_);
v_userName_3831_ = lean_ctor_get(v_val_3824_, 2);
lean_inc(v_userName_3831_);
v___y_3826_ = v_userName_3831_;
goto v___jp_3825_;
v___jp_3825_:
{
lean_object* v___x_3827_; 
v___x_3827_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_3808_, v___y_3826_);
lean_dec_ref(v_lctx_3808_);
if (lean_obj_tag(v___x_3827_) == 0)
{
lean_object* v___x_3828_; 
lean_dec(v___y_3826_);
lean_dec(v_val_3824_);
v___x_3828_ = lean_box(0);
return v___x_3828_;
}
else
{
lean_object* v_val_3829_; lean_object* v_fvarId_3830_; 
v_val_3829_ = lean_ctor_get(v___x_3827_, 0);
lean_inc(v_val_3829_);
lean_dec_ref(v___x_3827_);
v_fvarId_3830_ = lean_ctor_get(v_val_3824_, 1);
lean_inc(v_fvarId_3830_);
lean_dec(v_val_3824_);
v___y_3818_ = v_val_3829_;
v___y_3819_ = v___y_3826_;
v___y_3820_ = v_fvarId_3830_;
goto v___jp_3817_;
}
}
}
v___jp_3810_:
{
uint8_t v___x_3814_; 
v___x_3814_ = l_Lean_instBEqFVarId_beq(v___y_3811_, v___y_3813_);
lean_dec(v___y_3813_);
lean_dec(v___y_3811_);
if (v___x_3814_ == 0)
{
lean_object* v___x_3815_; 
lean_dec(v___y_3812_);
v___x_3815_ = lean_box(0);
return v___x_3815_;
}
else
{
lean_object* v___x_3816_; 
v___x_3816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3816_, 0, v___y_3812_);
return v___x_3816_;
}
}
v___jp_3817_:
{
lean_object* v_fvarId_3821_; 
v_fvarId_3821_ = lean_ctor_get(v___y_3818_, 1);
lean_inc(v_fvarId_3821_);
lean_dec_ref(v___y_3818_);
v___y_3811_ = v___y_3820_;
v___y_3812_ = v___y_3819_;
v___y_3813_ = v_fvarId_3821_;
goto v___jp_3810_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(size_t v_sz_3832_, size_t v_i_3833_, lean_object* v_bs_3834_){
_start:
{
uint8_t v___x_3835_; 
v___x_3835_ = lean_usize_dec_lt(v_i_3833_, v_sz_3832_);
if (v___x_3835_ == 0)
{
return v_bs_3834_;
}
else
{
lean_object* v_v_3836_; lean_object* v_snd_3837_; lean_object* v___x_3838_; lean_object* v_bs_x27_3839_; size_t v___x_3840_; size_t v___x_3841_; lean_object* v___x_3842_; 
v_v_3836_ = lean_array_uget_borrowed(v_bs_3834_, v_i_3833_);
v_snd_3837_ = lean_ctor_get(v_v_3836_, 1);
lean_inc(v_snd_3837_);
v___x_3838_ = lean_unsigned_to_nat(0u);
v_bs_x27_3839_ = lean_array_uset(v_bs_3834_, v_i_3833_, v___x_3838_);
v___x_3840_ = ((size_t)1ULL);
v___x_3841_ = lean_usize_add(v_i_3833_, v___x_3840_);
v___x_3842_ = lean_array_uset(v_bs_x27_3839_, v_i_3833_, v_snd_3837_);
v_i_3833_ = v___x_3841_;
v_bs_3834_ = v___x_3842_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0___boxed(lean_object* v_sz_3844_, lean_object* v_i_3845_, lean_object* v_bs_3846_){
_start:
{
size_t v_sz_boxed_3847_; size_t v_i_boxed_3848_; lean_object* v_res_3849_; 
v_sz_boxed_3847_ = lean_unbox_usize(v_sz_3844_);
lean_dec(v_sz_3844_);
v_i_boxed_3848_ = lean_unbox_usize(v_i_3845_);
lean_dec(v_i_3845_);
v_res_3849_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(v_sz_boxed_3847_, v_i_boxed_3848_, v_bs_3846_);
return v_res_3849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(lean_object* v_lctx_3850_, size_t v_sz_3851_, size_t v_i_3852_, lean_object* v_bs_3853_){
_start:
{
uint8_t v___x_3854_; 
v___x_3854_ = lean_usize_dec_lt(v_i_3852_, v_sz_3851_);
if (v___x_3854_ == 0)
{
lean_dec_ref(v_lctx_3850_);
return v_bs_3853_;
}
else
{
lean_object* v_fvarIdToDecl_3855_; lean_object* v_v_3856_; lean_object* v___x_3857_; lean_object* v_bs_x27_3858_; lean_object* v___y_3860_; lean_object* v___x_3865_; 
v_fvarIdToDecl_3855_ = lean_ctor_get(v_lctx_3850_, 0);
v_v_3856_ = lean_array_uget(v_bs_3853_, v_i_3852_);
v___x_3857_ = lean_unsigned_to_nat(0u);
v_bs_x27_3858_ = lean_array_uset(v_bs_3853_, v_i_3852_, v___x_3857_);
lean_inc_ref(v_fvarIdToDecl_3855_);
v___x_3865_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_fvarIdToDecl_3855_, v_v_3856_);
if (lean_obj_tag(v___x_3865_) == 0)
{
lean_object* v___x_3866_; 
v___x_3866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3866_, 0, v___x_3857_);
lean_ctor_set(v___x_3866_, 1, v_v_3856_);
v___y_3860_ = v___x_3866_;
goto v___jp_3859_;
}
else
{
lean_object* v_val_3867_; lean_object* v_index_3868_; lean_object* v___x_3869_; 
v_val_3867_ = lean_ctor_get(v___x_3865_, 0);
lean_inc(v_val_3867_);
lean_dec_ref(v___x_3865_);
v_index_3868_ = lean_ctor_get(v_val_3867_, 0);
lean_inc(v_index_3868_);
lean_dec(v_val_3867_);
v___x_3869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3869_, 0, v_index_3868_);
lean_ctor_set(v___x_3869_, 1, v_v_3856_);
v___y_3860_ = v___x_3869_;
goto v___jp_3859_;
}
v___jp_3859_:
{
size_t v___x_3861_; size_t v___x_3862_; lean_object* v___x_3863_; 
v___x_3861_ = ((size_t)1ULL);
v___x_3862_ = lean_usize_add(v_i_3852_, v___x_3861_);
v___x_3863_ = lean_array_uset(v_bs_x27_3858_, v_i_3852_, v___y_3860_);
v_i_3852_ = v___x_3862_;
v_bs_3853_ = v___x_3863_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1___boxed(lean_object* v_lctx_3870_, lean_object* v_sz_3871_, lean_object* v_i_3872_, lean_object* v_bs_3873_){
_start:
{
size_t v_sz_boxed_3874_; size_t v_i_boxed_3875_; lean_object* v_res_3876_; 
v_sz_boxed_3874_ = lean_unbox_usize(v_sz_3871_);
lean_dec(v_sz_3871_);
v_i_boxed_3875_ = lean_unbox_usize(v_i_3872_);
lean_dec(v_i_3872_);
v_res_3876_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(v_lctx_3870_, v_sz_boxed_3874_, v_i_boxed_3875_, v_bs_3873_);
return v_res_3876_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(lean_object* v_h_3877_, lean_object* v_i_3878_){
_start:
{
lean_object* v_fst_3879_; lean_object* v_fst_3880_; uint8_t v___x_3881_; 
v_fst_3879_ = lean_ctor_get(v_h_3877_, 0);
v_fst_3880_ = lean_ctor_get(v_i_3878_, 0);
v___x_3881_ = lean_nat_dec_lt(v_fst_3879_, v_fst_3880_);
return v___x_3881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0___boxed(lean_object* v_h_3882_, lean_object* v_i_3883_){
_start:
{
uint8_t v_res_3884_; lean_object* v_r_3885_; 
v_res_3884_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v_h_3882_, v_i_3883_);
lean_dec_ref(v_i_3883_);
lean_dec_ref(v_h_3882_);
v_r_3885_ = lean_box(v_res_3884_);
return v_r_3885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(lean_object* v_as_3887_, lean_object* v_lo_3888_, lean_object* v_hi_3889_){
_start:
{
uint8_t v___x_3890_; 
v___x_3890_ = lean_nat_dec_lt(v_lo_3888_, v_hi_3889_);
if (v___x_3890_ == 0)
{
lean_dec(v_lo_3888_);
return v_as_3887_;
}
else
{
lean_object* v___f_3891_; lean_object* v___x_3892_; lean_object* v_fst_3893_; lean_object* v_snd_3894_; uint8_t v___x_3895_; 
v___f_3891_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___closed__0));
lean_inc(v_lo_3888_);
v___x_3892_ = l_Array_qpartition___redArg(v_as_3887_, v___f_3891_, v_lo_3888_, v_hi_3889_);
v_fst_3893_ = lean_ctor_get(v___x_3892_, 0);
lean_inc(v_fst_3893_);
v_snd_3894_ = lean_ctor_get(v___x_3892_, 1);
lean_inc(v_snd_3894_);
lean_dec_ref(v___x_3892_);
v___x_3895_ = lean_nat_dec_le(v_hi_3889_, v_fst_3893_);
if (v___x_3895_ == 0)
{
lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; 
v___x_3896_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v_snd_3894_, v_lo_3888_, v_fst_3893_);
v___x_3897_ = lean_unsigned_to_nat(1u);
v___x_3898_ = lean_nat_add(v_fst_3893_, v___x_3897_);
lean_dec(v_fst_3893_);
v_as_3887_ = v___x_3896_;
v_lo_3888_ = v___x_3898_;
goto _start;
}
else
{
lean_dec(v_fst_3893_);
lean_dec(v_lo_3888_);
return v_snd_3894_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___boxed(lean_object* v_as_3900_, lean_object* v_lo_3901_, lean_object* v_hi_3902_){
_start:
{
lean_object* v_res_3903_; 
v_res_3903_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v_as_3900_, v_lo_3901_, v_hi_3902_);
lean_dec(v_hi_3902_);
return v_res_3903_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_sortFVarsByContextOrder(lean_object* v_lctx_3904_, lean_object* v_hyps_3905_){
_start:
{
lean_object* v___y_3907_; size_t v_sz_3911_; size_t v___x_3912_; lean_object* v_hyps_3913_; lean_object* v___y_3915_; lean_object* v___y_3916_; lean_object* v___x_3918_; lean_object* v___x_3919_; uint8_t v___x_3920_; 
v_sz_3911_ = lean_array_size(v_hyps_3905_);
v___x_3912_ = ((size_t)0ULL);
v_hyps_3913_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(v_lctx_3904_, v_sz_3911_, v___x_3912_, v_hyps_3905_);
v___x_3918_ = lean_array_get_size(v_hyps_3913_);
v___x_3919_ = lean_unsigned_to_nat(0u);
v___x_3920_ = lean_nat_dec_eq(v___x_3918_, v___x_3919_);
if (v___x_3920_ == 0)
{
lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___y_3924_; uint8_t v___x_3926_; 
v___x_3921_ = lean_unsigned_to_nat(1u);
v___x_3922_ = lean_nat_sub(v___x_3918_, v___x_3921_);
v___x_3926_ = lean_nat_dec_le(v___x_3919_, v___x_3922_);
if (v___x_3926_ == 0)
{
lean_inc(v___x_3922_);
v___y_3924_ = v___x_3922_;
goto v___jp_3923_;
}
else
{
v___y_3924_ = v___x_3919_;
goto v___jp_3923_;
}
v___jp_3923_:
{
uint8_t v___x_3925_; 
v___x_3925_ = lean_nat_dec_le(v___y_3924_, v___x_3922_);
if (v___x_3925_ == 0)
{
lean_dec(v___x_3922_);
lean_inc(v___y_3924_);
v___y_3915_ = v___y_3924_;
v___y_3916_ = v___y_3924_;
goto v___jp_3914_;
}
else
{
v___y_3915_ = v___y_3924_;
v___y_3916_ = v___x_3922_;
goto v___jp_3914_;
}
}
}
else
{
v___y_3907_ = v_hyps_3913_;
goto v___jp_3906_;
}
v___jp_3906_:
{
size_t v_sz_3908_; size_t v___x_3909_; lean_object* v___x_3910_; 
v_sz_3908_ = lean_array_size(v___y_3907_);
v___x_3909_ = ((size_t)0ULL);
v___x_3910_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(v_sz_3908_, v___x_3909_, v___y_3907_);
return v___x_3910_;
}
v___jp_3914_:
{
lean_object* v___x_3917_; 
v___x_3917_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v_hyps_3913_, v___y_3915_, v___y_3916_);
lean_dec(v___y_3916_);
v___y_3907_ = v___x_3917_;
goto v___jp_3906_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2(lean_object* v_n_3927_, lean_object* v_as_3928_, lean_object* v_lo_3929_, lean_object* v_hi_3930_, lean_object* v_w_3931_, lean_object* v_hlo_3932_, lean_object* v_hhi_3933_){
_start:
{
lean_object* v___x_3934_; 
v___x_3934_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v_as_3928_, v_lo_3929_, v_hi_3930_);
return v___x_3934_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___boxed(lean_object* v_n_3935_, lean_object* v_as_3936_, lean_object* v_lo_3937_, lean_object* v_hi_3938_, lean_object* v_w_3939_, lean_object* v_hlo_3940_, lean_object* v_hhi_3941_){
_start:
{
lean_object* v_res_3942_; 
v_res_3942_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2(v_n_3935_, v_as_3936_, v_lo_3937_, v_hi_3938_, v_w_3939_, v_hlo_3940_, v_hhi_3941_);
lean_dec(v_hi_3938_);
lean_dec(v_n_3935_);
return v_res_3942_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(lean_object* v_a_3943_, lean_object* v_x_3944_){
_start:
{
if (lean_obj_tag(v_x_3944_) == 0)
{
uint8_t v___x_3945_; 
v___x_3945_ = 0;
return v___x_3945_;
}
else
{
lean_object* v_key_3946_; lean_object* v_tail_3947_; uint8_t v___x_3948_; 
v_key_3946_ = lean_ctor_get(v_x_3944_, 0);
v_tail_3947_ = lean_ctor_get(v_x_3944_, 2);
v___x_3948_ = lean_name_eq(v_key_3946_, v_a_3943_);
if (v___x_3948_ == 0)
{
v_x_3944_ = v_tail_3947_;
goto _start;
}
else
{
return v___x_3948_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg___boxed(lean_object* v_a_3950_, lean_object* v_x_3951_){
_start:
{
uint8_t v_res_3952_; lean_object* v_r_3953_; 
v_res_3952_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_3950_, v_x_3951_);
lean_dec(v_x_3951_);
lean_dec(v_a_3950_);
v_r_3953_ = lean_box(v_res_3952_);
return v_r_3953_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(lean_object* v_a_3954_, lean_object* v_x_3955_){
_start:
{
if (lean_obj_tag(v_x_3955_) == 0)
{
return v_x_3955_;
}
else
{
lean_object* v_key_3956_; lean_object* v_value_3957_; lean_object* v_tail_3958_; lean_object* v___x_3960_; uint8_t v_isShared_3961_; uint8_t v_isSharedCheck_3967_; 
v_key_3956_ = lean_ctor_get(v_x_3955_, 0);
v_value_3957_ = lean_ctor_get(v_x_3955_, 1);
v_tail_3958_ = lean_ctor_get(v_x_3955_, 2);
v_isSharedCheck_3967_ = !lean_is_exclusive(v_x_3955_);
if (v_isSharedCheck_3967_ == 0)
{
v___x_3960_ = v_x_3955_;
v_isShared_3961_ = v_isSharedCheck_3967_;
goto v_resetjp_3959_;
}
else
{
lean_inc(v_tail_3958_);
lean_inc(v_value_3957_);
lean_inc(v_key_3956_);
lean_dec(v_x_3955_);
v___x_3960_ = lean_box(0);
v_isShared_3961_ = v_isSharedCheck_3967_;
goto v_resetjp_3959_;
}
v_resetjp_3959_:
{
uint8_t v___x_3962_; 
v___x_3962_ = lean_name_eq(v_key_3956_, v_a_3954_);
if (v___x_3962_ == 0)
{
lean_object* v___x_3963_; lean_object* v___x_3965_; 
v___x_3963_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_3954_, v_tail_3958_);
if (v_isShared_3961_ == 0)
{
lean_ctor_set(v___x_3960_, 2, v___x_3963_);
v___x_3965_ = v___x_3960_;
goto v_reusejp_3964_;
}
else
{
lean_object* v_reuseFailAlloc_3966_; 
v_reuseFailAlloc_3966_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3966_, 0, v_key_3956_);
lean_ctor_set(v_reuseFailAlloc_3966_, 1, v_value_3957_);
lean_ctor_set(v_reuseFailAlloc_3966_, 2, v___x_3963_);
v___x_3965_ = v_reuseFailAlloc_3966_;
goto v_reusejp_3964_;
}
v_reusejp_3964_:
{
return v___x_3965_;
}
}
else
{
lean_del_object(v___x_3960_);
lean_dec(v_value_3957_);
lean_dec(v_key_3956_);
return v_tail_3958_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg___boxed(lean_object* v_a_3968_, lean_object* v_x_3969_){
_start:
{
lean_object* v_res_3970_; 
v_res_3970_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_3968_, v_x_3969_);
lean_dec(v_a_3968_);
return v_res_3970_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3971_; uint64_t v___x_3972_; 
v___x_3971_ = lean_unsigned_to_nat(1723u);
v___x_3972_ = lean_uint64_of_nat(v___x_3971_);
return v___x_3972_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(lean_object* v_m_3973_, lean_object* v_a_3974_){
_start:
{
lean_object* v_size_3975_; lean_object* v_buckets_3976_; lean_object* v___x_3977_; uint64_t v___y_3979_; 
v_size_3975_ = lean_ctor_get(v_m_3973_, 0);
v_buckets_3976_ = lean_ctor_get(v_m_3973_, 1);
v___x_3977_ = lean_array_get_size(v_buckets_3976_);
if (lean_obj_tag(v_a_3974_) == 0)
{
uint64_t v___x_4008_; 
v___x_4008_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0);
v___y_3979_ = v___x_4008_;
goto v___jp_3978_;
}
else
{
uint64_t v_hash_4009_; 
v_hash_4009_ = lean_ctor_get_uint64(v_a_3974_, sizeof(void*)*2);
v___y_3979_ = v_hash_4009_;
goto v___jp_3978_;
}
v___jp_3978_:
{
uint64_t v___x_3980_; uint64_t v___x_3981_; uint64_t v_fold_3982_; uint64_t v___x_3983_; uint64_t v___x_3984_; uint64_t v___x_3985_; size_t v___x_3986_; size_t v___x_3987_; size_t v___x_3988_; size_t v___x_3989_; size_t v___x_3990_; lean_object* v_bkt_3991_; uint8_t v___x_3992_; 
v___x_3980_ = 32ULL;
v___x_3981_ = lean_uint64_shift_right(v___y_3979_, v___x_3980_);
v_fold_3982_ = lean_uint64_xor(v___y_3979_, v___x_3981_);
v___x_3983_ = 16ULL;
v___x_3984_ = lean_uint64_shift_right(v_fold_3982_, v___x_3983_);
v___x_3985_ = lean_uint64_xor(v_fold_3982_, v___x_3984_);
v___x_3986_ = lean_uint64_to_usize(v___x_3985_);
v___x_3987_ = lean_usize_of_nat(v___x_3977_);
v___x_3988_ = ((size_t)1ULL);
v___x_3989_ = lean_usize_sub(v___x_3987_, v___x_3988_);
v___x_3990_ = lean_usize_land(v___x_3986_, v___x_3989_);
v_bkt_3991_ = lean_array_uget_borrowed(v_buckets_3976_, v___x_3990_);
v___x_3992_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_3974_, v_bkt_3991_);
if (v___x_3992_ == 0)
{
return v_m_3973_;
}
else
{
lean_object* v___x_3994_; uint8_t v_isShared_3995_; uint8_t v_isSharedCheck_4005_; 
lean_inc(v_bkt_3991_);
lean_inc_ref(v_buckets_3976_);
lean_inc(v_size_3975_);
v_isSharedCheck_4005_ = !lean_is_exclusive(v_m_3973_);
if (v_isSharedCheck_4005_ == 0)
{
lean_object* v_unused_4006_; lean_object* v_unused_4007_; 
v_unused_4006_ = lean_ctor_get(v_m_3973_, 1);
lean_dec(v_unused_4006_);
v_unused_4007_ = lean_ctor_get(v_m_3973_, 0);
lean_dec(v_unused_4007_);
v___x_3994_ = v_m_3973_;
v_isShared_3995_ = v_isSharedCheck_4005_;
goto v_resetjp_3993_;
}
else
{
lean_dec(v_m_3973_);
v___x_3994_ = lean_box(0);
v_isShared_3995_ = v_isSharedCheck_4005_;
goto v_resetjp_3993_;
}
v_resetjp_3993_:
{
lean_object* v___x_3996_; lean_object* v_buckets_x27_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4003_; 
v___x_3996_ = lean_box(0);
v_buckets_x27_3997_ = lean_array_uset(v_buckets_3976_, v___x_3990_, v___x_3996_);
v___x_3998_ = lean_unsigned_to_nat(1u);
v___x_3999_ = lean_nat_sub(v_size_3975_, v___x_3998_);
lean_dec(v_size_3975_);
v___x_4000_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_3974_, v_bkt_3991_);
v___x_4001_ = lean_array_uset(v_buckets_x27_3997_, v___x_3990_, v___x_4000_);
if (v_isShared_3995_ == 0)
{
lean_ctor_set(v___x_3994_, 1, v___x_4001_);
lean_ctor_set(v___x_3994_, 0, v___x_3999_);
v___x_4003_ = v___x_3994_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v___x_3999_);
lean_ctor_set(v_reuseFailAlloc_4004_, 1, v___x_4001_);
v___x_4003_ = v_reuseFailAlloc_4004_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
return v___x_4003_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___boxed(lean_object* v_m_4010_, lean_object* v_a_4011_){
_start:
{
lean_object* v_res_4012_; 
v_res_4012_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_m_4010_, v_a_4011_);
lean_dec(v_a_4011_);
return v_res_4012_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(lean_object* v_m_4013_, lean_object* v_a_4014_){
_start:
{
lean_object* v_buckets_4015_; lean_object* v___x_4016_; uint64_t v___y_4018_; 
v_buckets_4015_ = lean_ctor_get(v_m_4013_, 1);
v___x_4016_ = lean_array_get_size(v_buckets_4015_);
if (lean_obj_tag(v_a_4014_) == 0)
{
uint64_t v___x_4032_; 
v___x_4032_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0);
v___y_4018_ = v___x_4032_;
goto v___jp_4017_;
}
else
{
uint64_t v_hash_4033_; 
v_hash_4033_ = lean_ctor_get_uint64(v_a_4014_, sizeof(void*)*2);
v___y_4018_ = v_hash_4033_;
goto v___jp_4017_;
}
v___jp_4017_:
{
uint64_t v___x_4019_; uint64_t v___x_4020_; uint64_t v_fold_4021_; uint64_t v___x_4022_; uint64_t v___x_4023_; uint64_t v___x_4024_; size_t v___x_4025_; size_t v___x_4026_; size_t v___x_4027_; size_t v___x_4028_; size_t v___x_4029_; lean_object* v___x_4030_; uint8_t v___x_4031_; 
v___x_4019_ = 32ULL;
v___x_4020_ = lean_uint64_shift_right(v___y_4018_, v___x_4019_);
v_fold_4021_ = lean_uint64_xor(v___y_4018_, v___x_4020_);
v___x_4022_ = 16ULL;
v___x_4023_ = lean_uint64_shift_right(v_fold_4021_, v___x_4022_);
v___x_4024_ = lean_uint64_xor(v_fold_4021_, v___x_4023_);
v___x_4025_ = lean_uint64_to_usize(v___x_4024_);
v___x_4026_ = lean_usize_of_nat(v___x_4016_);
v___x_4027_ = ((size_t)1ULL);
v___x_4028_ = lean_usize_sub(v___x_4026_, v___x_4027_);
v___x_4029_ = lean_usize_land(v___x_4025_, v___x_4028_);
v___x_4030_ = lean_array_uget_borrowed(v_buckets_4015_, v___x_4029_);
v___x_4031_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_4014_, v___x_4030_);
return v___x_4031_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg___boxed(lean_object* v_m_4034_, lean_object* v_a_4035_){
_start:
{
uint8_t v_res_4036_; lean_object* v_r_4037_; 
v_res_4036_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(v_m_4034_, v_a_4035_);
lean_dec(v_a_4035_);
lean_dec_ref(v_m_4034_);
v_r_4037_ = lean_box(v_res_4036_);
return v_r_4037_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(lean_object* v_start_4038_, lean_object* v_as_4039_, size_t v_i_4040_, size_t v_stop_4041_, lean_object* v_b_4042_){
_start:
{
uint8_t v___x_4043_; 
v___x_4043_ = lean_usize_dec_eq(v_i_4040_, v_stop_4041_);
if (v___x_4043_ == 0)
{
size_t v___x_4044_; size_t v___x_4045_; lean_object* v___x_4046_; 
v___x_4044_ = ((size_t)1ULL);
v___x_4045_ = lean_usize_sub(v_i_4040_, v___x_4044_);
v___x_4046_ = lean_array_uget(v_as_4039_, v___x_4045_);
if (lean_obj_tag(v___x_4046_) == 0)
{
v_i_4040_ = v___x_4045_;
goto _start;
}
else
{
lean_object* v_val_4048_; lean_object* v___x_4050_; uint8_t v_isShared_4051_; uint8_t v_isSharedCheck_4082_; 
v_val_4048_ = lean_ctor_get(v___x_4046_, 0);
v_isSharedCheck_4082_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4082_ == 0)
{
v___x_4050_ = v___x_4046_;
v_isShared_4051_ = v_isSharedCheck_4082_;
goto v_resetjp_4049_;
}
else
{
lean_inc(v_val_4048_);
lean_dec(v___x_4046_);
v___x_4050_ = lean_box(0);
v_isShared_4051_ = v_isSharedCheck_4082_;
goto v_resetjp_4049_;
}
v_resetjp_4049_:
{
lean_object* v_fst_4052_; lean_object* v_snd_4053_; lean_object* v___y_4055_; lean_object* v___y_4071_; lean_object* v_size_4077_; lean_object* v___x_4078_; uint8_t v___x_4079_; 
v_fst_4052_ = lean_ctor_get(v_b_4042_, 0);
v_snd_4053_ = lean_ctor_get(v_b_4042_, 1);
v_size_4077_ = lean_ctor_get(v_fst_4052_, 0);
v___x_4078_ = lean_unsigned_to_nat(0u);
v___x_4079_ = lean_nat_dec_eq(v_size_4077_, v___x_4078_);
if (v___x_4079_ == 0)
{
lean_object* v_index_4080_; 
v_index_4080_ = lean_ctor_get(v_val_4048_, 0);
lean_inc(v_index_4080_);
v___y_4071_ = v_index_4080_;
goto v___jp_4070_;
}
else
{
lean_object* v___x_4081_; 
lean_inc(v_snd_4053_);
lean_del_object(v___x_4050_);
lean_dec(v_val_4048_);
lean_dec_ref(v_b_4042_);
v___x_4081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4081_, 0, v_snd_4053_);
return v___x_4081_;
}
v___jp_4054_:
{
uint8_t v___x_4056_; 
v___x_4056_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(v_fst_4052_, v___y_4055_);
if (v___x_4056_ == 0)
{
lean_dec(v___y_4055_);
lean_dec(v_val_4048_);
v_i_4040_ = v___x_4045_;
goto _start;
}
else
{
lean_object* v___x_4059_; uint8_t v_isShared_4060_; uint8_t v_isSharedCheck_4067_; 
lean_inc(v_snd_4053_);
lean_inc(v_fst_4052_);
v_isSharedCheck_4067_ = !lean_is_exclusive(v_b_4042_);
if (v_isSharedCheck_4067_ == 0)
{
lean_object* v_unused_4068_; lean_object* v_unused_4069_; 
v_unused_4068_ = lean_ctor_get(v_b_4042_, 1);
lean_dec(v_unused_4068_);
v_unused_4069_ = lean_ctor_get(v_b_4042_, 0);
lean_dec(v_unused_4069_);
v___x_4059_ = v_b_4042_;
v_isShared_4060_ = v_isSharedCheck_4067_;
goto v_resetjp_4058_;
}
else
{
lean_dec(v_b_4042_);
v___x_4059_ = lean_box(0);
v_isShared_4060_ = v_isSharedCheck_4067_;
goto v_resetjp_4058_;
}
v_resetjp_4058_:
{
lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4064_; 
v___x_4061_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_fst_4052_, v___y_4055_);
lean_dec(v___y_4055_);
v___x_4062_ = lean_array_push(v_snd_4053_, v_val_4048_);
if (v_isShared_4060_ == 0)
{
lean_ctor_set(v___x_4059_, 1, v___x_4062_);
lean_ctor_set(v___x_4059_, 0, v___x_4061_);
v___x_4064_ = v___x_4059_;
goto v_reusejp_4063_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v___x_4061_);
lean_ctor_set(v_reuseFailAlloc_4066_, 1, v___x_4062_);
v___x_4064_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4063_;
}
v_reusejp_4063_:
{
v_i_4040_ = v___x_4045_;
v_b_4042_ = v___x_4064_;
goto _start;
}
}
}
}
v___jp_4070_:
{
uint8_t v___x_4072_; 
v___x_4072_ = lean_nat_dec_lt(v___y_4071_, v_start_4038_);
lean_dec(v___y_4071_);
if (v___x_4072_ == 0)
{
lean_object* v_userName_4073_; 
lean_del_object(v___x_4050_);
v_userName_4073_ = lean_ctor_get(v_val_4048_, 2);
lean_inc(v_userName_4073_);
v___y_4055_ = v_userName_4073_;
goto v___jp_4054_;
}
else
{
lean_object* v___x_4075_; 
lean_inc(v_snd_4053_);
lean_dec(v_val_4048_);
lean_dec_ref(v_b_4042_);
if (v_isShared_4051_ == 0)
{
lean_ctor_set_tag(v___x_4050_, 0);
lean_ctor_set(v___x_4050_, 0, v_snd_4053_);
v___x_4075_ = v___x_4050_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v_snd_4053_);
v___x_4075_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
return v___x_4075_;
}
}
}
}
}
}
else
{
lean_object* v___x_4083_; 
v___x_4083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4083_, 0, v_b_4042_);
return v___x_4083_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_start_4084_, lean_object* v_as_4085_, lean_object* v_i_4086_, lean_object* v_stop_4087_, lean_object* v_b_4088_){
_start:
{
size_t v_i_boxed_4089_; size_t v_stop_boxed_4090_; lean_object* v_res_4091_; 
v_i_boxed_4089_ = lean_unbox_usize(v_i_4086_);
lean_dec(v_i_4086_);
v_stop_boxed_4090_ = lean_unbox_usize(v_stop_4087_);
lean_dec(v_stop_4087_);
v_res_4091_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4084_, v_as_4085_, v_i_boxed_4089_, v_stop_boxed_4090_, v_b_4088_);
lean_dec_ref(v_as_4085_);
lean_dec(v_start_4084_);
return v_res_4091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(lean_object* v_start_4092_, lean_object* v_x_4093_, lean_object* v_x_4094_){
_start:
{
if (lean_obj_tag(v_x_4093_) == 0)
{
lean_object* v_cs_4095_; lean_object* v___x_4097_; uint8_t v_isShared_4098_; uint8_t v_isSharedCheck_4108_; 
v_cs_4095_ = lean_ctor_get(v_x_4093_, 0);
v_isSharedCheck_4108_ = !lean_is_exclusive(v_x_4093_);
if (v_isSharedCheck_4108_ == 0)
{
v___x_4097_ = v_x_4093_;
v_isShared_4098_ = v_isSharedCheck_4108_;
goto v_resetjp_4096_;
}
else
{
lean_inc(v_cs_4095_);
lean_dec(v_x_4093_);
v___x_4097_ = lean_box(0);
v_isShared_4098_ = v_isSharedCheck_4108_;
goto v_resetjp_4096_;
}
v_resetjp_4096_:
{
lean_object* v___x_4099_; lean_object* v___x_4100_; uint8_t v___x_4101_; 
v___x_4099_ = lean_array_get_size(v_cs_4095_);
v___x_4100_ = lean_unsigned_to_nat(0u);
v___x_4101_ = lean_nat_dec_lt(v___x_4100_, v___x_4099_);
if (v___x_4101_ == 0)
{
lean_object* v___x_4103_; 
lean_dec_ref(v_cs_4095_);
if (v_isShared_4098_ == 0)
{
lean_ctor_set_tag(v___x_4097_, 1);
lean_ctor_set(v___x_4097_, 0, v_x_4094_);
v___x_4103_ = v___x_4097_;
goto v_reusejp_4102_;
}
else
{
lean_object* v_reuseFailAlloc_4104_; 
v_reuseFailAlloc_4104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4104_, 0, v_x_4094_);
v___x_4103_ = v_reuseFailAlloc_4104_;
goto v_reusejp_4102_;
}
v_reusejp_4102_:
{
return v___x_4103_;
}
}
else
{
size_t v___x_4105_; size_t v___x_4106_; lean_object* v___x_4107_; 
lean_del_object(v___x_4097_);
v___x_4105_ = lean_usize_of_nat(v___x_4099_);
v___x_4106_ = ((size_t)0ULL);
v___x_4107_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(v_start_4092_, v_cs_4095_, v___x_4105_, v___x_4106_, v_x_4094_);
lean_dec_ref(v_cs_4095_);
return v___x_4107_;
}
}
}
else
{
lean_object* v_vs_4109_; lean_object* v___x_4111_; uint8_t v_isShared_4112_; uint8_t v_isSharedCheck_4122_; 
v_vs_4109_ = lean_ctor_get(v_x_4093_, 0);
v_isSharedCheck_4122_ = !lean_is_exclusive(v_x_4093_);
if (v_isSharedCheck_4122_ == 0)
{
v___x_4111_ = v_x_4093_;
v_isShared_4112_ = v_isSharedCheck_4122_;
goto v_resetjp_4110_;
}
else
{
lean_inc(v_vs_4109_);
lean_dec(v_x_4093_);
v___x_4111_ = lean_box(0);
v_isShared_4112_ = v_isSharedCheck_4122_;
goto v_resetjp_4110_;
}
v_resetjp_4110_:
{
lean_object* v___x_4113_; lean_object* v___x_4114_; uint8_t v___x_4115_; 
v___x_4113_ = lean_array_get_size(v_vs_4109_);
v___x_4114_ = lean_unsigned_to_nat(0u);
v___x_4115_ = lean_nat_dec_lt(v___x_4114_, v___x_4113_);
if (v___x_4115_ == 0)
{
lean_object* v___x_4117_; 
lean_dec_ref(v_vs_4109_);
if (v_isShared_4112_ == 0)
{
lean_ctor_set(v___x_4111_, 0, v_x_4094_);
v___x_4117_ = v___x_4111_;
goto v_reusejp_4116_;
}
else
{
lean_object* v_reuseFailAlloc_4118_; 
v_reuseFailAlloc_4118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4118_, 0, v_x_4094_);
v___x_4117_ = v_reuseFailAlloc_4118_;
goto v_reusejp_4116_;
}
v_reusejp_4116_:
{
return v___x_4117_;
}
}
else
{
size_t v___x_4119_; size_t v___x_4120_; lean_object* v___x_4121_; 
lean_del_object(v___x_4111_);
v___x_4119_ = lean_usize_of_nat(v___x_4113_);
v___x_4120_ = ((size_t)0ULL);
v___x_4121_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4092_, v_vs_4109_, v___x_4119_, v___x_4120_, v_x_4094_);
lean_dec_ref(v_vs_4109_);
return v___x_4121_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_start_4123_, lean_object* v_as_4124_, size_t v_i_4125_, size_t v_stop_4126_, lean_object* v_b_4127_){
_start:
{
uint8_t v___x_4128_; 
v___x_4128_ = lean_usize_dec_eq(v_i_4125_, v_stop_4126_);
if (v___x_4128_ == 0)
{
size_t v___x_4129_; size_t v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; 
v___x_4129_ = ((size_t)1ULL);
v___x_4130_ = lean_usize_sub(v_i_4125_, v___x_4129_);
v___x_4131_ = lean_array_uget_borrowed(v_as_4124_, v___x_4130_);
lean_inc(v___x_4131_);
v___x_4132_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4123_, v___x_4131_, v_b_4127_);
if (lean_obj_tag(v___x_4132_) == 0)
{
return v___x_4132_;
}
else
{
lean_object* v_a_4133_; 
v_a_4133_ = lean_ctor_get(v___x_4132_, 0);
lean_inc(v_a_4133_);
lean_dec_ref(v___x_4132_);
v_i_4125_ = v___x_4130_;
v_b_4127_ = v_a_4133_;
goto _start;
}
}
else
{
lean_object* v___x_4135_; 
v___x_4135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4135_, 0, v_b_4127_);
return v___x_4135_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_start_4136_, lean_object* v_as_4137_, lean_object* v_i_4138_, lean_object* v_stop_4139_, lean_object* v_b_4140_){
_start:
{
size_t v_i_boxed_4141_; size_t v_stop_boxed_4142_; lean_object* v_res_4143_; 
v_i_boxed_4141_ = lean_unbox_usize(v_i_4138_);
lean_dec(v_i_4138_);
v_stop_boxed_4142_ = lean_unbox_usize(v_stop_4139_);
lean_dec(v_stop_4139_);
v_res_4143_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(v_start_4136_, v_as_4137_, v_i_boxed_4141_, v_stop_boxed_4142_, v_b_4140_);
lean_dec_ref(v_as_4137_);
lean_dec(v_start_4136_);
return v_res_4143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_start_4144_, lean_object* v_x_4145_, lean_object* v_x_4146_){
_start:
{
lean_object* v_res_4147_; 
v_res_4147_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4144_, v_x_4145_, v_x_4146_);
lean_dec(v_start_4144_);
return v_res_4147_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(lean_object* v_start_4148_, lean_object* v_t_4149_, lean_object* v_init_4150_){
_start:
{
lean_object* v_root_4151_; lean_object* v_tail_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; uint8_t v___x_4155_; 
v_root_4151_ = lean_ctor_get(v_t_4149_, 0);
lean_inc_ref(v_root_4151_);
v_tail_4152_ = lean_ctor_get(v_t_4149_, 1);
lean_inc_ref(v_tail_4152_);
lean_dec_ref(v_t_4149_);
v___x_4153_ = lean_array_get_size(v_tail_4152_);
v___x_4154_ = lean_unsigned_to_nat(0u);
v___x_4155_ = lean_nat_dec_lt(v___x_4154_, v___x_4153_);
if (v___x_4155_ == 0)
{
lean_object* v___x_4156_; 
lean_dec_ref(v_tail_4152_);
v___x_4156_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4148_, v_root_4151_, v_init_4150_);
return v___x_4156_;
}
else
{
size_t v___x_4157_; size_t v___x_4158_; lean_object* v___x_4159_; 
v___x_4157_ = lean_usize_of_nat(v___x_4153_);
v___x_4158_ = ((size_t)0ULL);
v___x_4159_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4148_, v_tail_4152_, v___x_4157_, v___x_4158_, v_init_4150_);
lean_dec_ref(v_tail_4152_);
if (lean_obj_tag(v___x_4159_) == 0)
{
lean_dec_ref(v_root_4151_);
return v___x_4159_;
}
else
{
lean_object* v_a_4160_; lean_object* v___x_4161_; 
v_a_4160_ = lean_ctor_get(v___x_4159_, 0);
lean_inc(v_a_4160_);
lean_dec_ref(v___x_4159_);
v___x_4161_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4148_, v_root_4151_, v_a_4160_);
return v___x_4161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg___boxed(lean_object* v_start_4162_, lean_object* v_t_4163_, lean_object* v_init_4164_){
_start:
{
lean_object* v_res_4165_; 
v_res_4165_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(v_start_4162_, v_t_4163_, v_init_4164_);
lean_dec(v_start_4162_);
return v_res_4165_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(lean_object* v_start_4166_, lean_object* v_lctx_4167_, lean_object* v_init_4168_){
_start:
{
lean_object* v_decls_4169_; lean_object* v___x_4170_; 
v_decls_4169_ = lean_ctor_get(v_lctx_4167_, 1);
lean_inc_ref(v_decls_4169_);
lean_dec_ref(v_lctx_4167_);
v___x_4170_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(v_start_4166_, v_decls_4169_, v_init_4168_);
return v___x_4170_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg___boxed(lean_object* v_start_4171_, lean_object* v_lctx_4172_, lean_object* v_init_4173_){
_start:
{
lean_object* v_res_4174_; 
v_res_4174_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(v_start_4171_, v_lctx_4172_, v_init_4173_);
lean_dec(v_start_4171_);
return v_res_4174_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___redArg(lean_object* v_lctx_4177_, lean_object* v_userNames_4178_, lean_object* v_start_4179_){
_start:
{
lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; 
v___x_4180_ = ((lean_object*)(l_Lean_LocalContext_findFromUserNames___redArg___closed__0));
v___x_4181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4181_, 0, v_userNames_4178_);
lean_ctor_set(v___x_4181_, 1, v___x_4180_);
v___x_4182_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(v_start_4179_, v_lctx_4177_, v___x_4181_);
if (lean_obj_tag(v___x_4182_) == 0)
{
lean_object* v_a_4183_; lean_object* v___x_4184_; 
v_a_4183_ = lean_ctor_get(v___x_4182_, 0);
lean_inc(v_a_4183_);
lean_dec_ref(v___x_4182_);
v___x_4184_ = l_Array_reverse___redArg(v_a_4183_);
return v___x_4184_;
}
else
{
lean_object* v_a_4185_; lean_object* v_snd_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; 
v_a_4185_ = lean_ctor_get(v___x_4182_, 0);
lean_inc(v_a_4185_);
lean_dec_ref(v___x_4182_);
v_snd_4186_ = lean_ctor_get(v_a_4185_, 1);
lean_inc(v_snd_4186_);
lean_dec(v_a_4185_);
v___x_4187_ = l_Array_reverse___redArg(v_snd_4186_);
v___x_4188_ = l_Array_reverse___redArg(v___x_4187_);
return v___x_4188_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___redArg___boxed(lean_object* v_lctx_4189_, lean_object* v_userNames_4190_, lean_object* v_start_4191_){
_start:
{
lean_object* v_res_4192_; 
v_res_4192_ = l_Lean_LocalContext_findFromUserNames___redArg(v_lctx_4189_, v_userNames_4190_, v_start_4191_);
lean_dec(v_start_4191_);
return v_res_4192_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames(lean_object* v_00_u03b1_4193_, lean_object* v_lctx_4194_, lean_object* v_userNames_4195_, lean_object* v_start_4196_){
_start:
{
lean_object* v___x_4197_; 
v___x_4197_ = l_Lean_LocalContext_findFromUserNames___redArg(v_lctx_4194_, v_userNames_4195_, v_start_4196_);
return v___x_4197_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___boxed(lean_object* v_00_u03b1_4198_, lean_object* v_lctx_4199_, lean_object* v_userNames_4200_, lean_object* v_start_4201_){
_start:
{
lean_object* v_res_4202_; 
v_res_4202_ = l_Lean_LocalContext_findFromUserNames(v_00_u03b1_4198_, v_lctx_4199_, v_userNames_4200_, v_start_4201_);
lean_dec(v_start_4201_);
return v_res_4202_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0(lean_object* v_00_u03b2_4203_, lean_object* v_m_4204_, lean_object* v_a_4205_){
_start:
{
uint8_t v___x_4206_; 
v___x_4206_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(v_m_4204_, v_a_4205_);
return v___x_4206_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___boxed(lean_object* v_00_u03b2_4207_, lean_object* v_m_4208_, lean_object* v_a_4209_){
_start:
{
uint8_t v_res_4210_; lean_object* v_r_4211_; 
v_res_4210_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0(v_00_u03b2_4207_, v_m_4208_, v_a_4209_);
lean_dec(v_a_4209_);
lean_dec_ref(v_m_4208_);
v_r_4211_ = lean_box(v_res_4210_);
return v_r_4211_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1(lean_object* v_00_u03b2_4212_, lean_object* v_m_4213_, lean_object* v_a_4214_){
_start:
{
lean_object* v___x_4215_; 
v___x_4215_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_m_4213_, v_a_4214_);
return v___x_4215_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___boxed(lean_object* v_00_u03b2_4216_, lean_object* v_m_4217_, lean_object* v_a_4218_){
_start:
{
lean_object* v_res_4219_; 
v_res_4219_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1(v_00_u03b2_4216_, v_m_4217_, v_a_4218_);
lean_dec(v_a_4218_);
return v_res_4219_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2(lean_object* v_00_u03b1_4220_, lean_object* v_start_4221_, lean_object* v_lctx_4222_, lean_object* v_init_4223_){
_start:
{
lean_object* v___x_4224_; 
v___x_4224_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(v_start_4221_, v_lctx_4222_, v_init_4223_);
return v___x_4224_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___boxed(lean_object* v_00_u03b1_4225_, lean_object* v_start_4226_, lean_object* v_lctx_4227_, lean_object* v_init_4228_){
_start:
{
lean_object* v_res_4229_; 
v_res_4229_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2(v_00_u03b1_4225_, v_start_4226_, v_lctx_4227_, v_init_4228_);
lean_dec(v_start_4226_);
return v_res_4229_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0(lean_object* v_00_u03b2_4230_, lean_object* v_a_4231_, lean_object* v_x_4232_){
_start:
{
uint8_t v___x_4233_; 
v___x_4233_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_4231_, v_x_4232_);
return v___x_4233_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4234_, lean_object* v_a_4235_, lean_object* v_x_4236_){
_start:
{
uint8_t v_res_4237_; lean_object* v_r_4238_; 
v_res_4237_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0(v_00_u03b2_4234_, v_a_4235_, v_x_4236_);
lean_dec(v_x_4236_);
lean_dec(v_a_4235_);
v_r_4238_ = lean_box(v_res_4237_);
return v_r_4238_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2(lean_object* v_00_u03b2_4239_, lean_object* v_a_4240_, lean_object* v_x_4241_){
_start:
{
lean_object* v___x_4242_; 
v___x_4242_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_4240_, v_x_4241_);
return v___x_4242_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4243_, lean_object* v_a_4244_, lean_object* v_x_4245_){
_start:
{
lean_object* v_res_4246_; 
v_res_4246_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2(v_00_u03b2_4243_, v_a_4244_, v_x_4245_);
lean_dec(v_a_4244_);
return v_res_4246_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4(lean_object* v_00_u03b1_4247_, lean_object* v_start_4248_, lean_object* v_t_4249_, lean_object* v_init_4250_){
_start:
{
lean_object* v___x_4251_; 
v___x_4251_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(v_start_4248_, v_t_4249_, v_init_4250_);
return v___x_4251_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___boxed(lean_object* v_00_u03b1_4252_, lean_object* v_start_4253_, lean_object* v_t_4254_, lean_object* v_init_4255_){
_start:
{
lean_object* v_res_4256_; 
v_res_4256_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4(v_00_u03b1_4252_, v_start_4253_, v_t_4254_, v_init_4255_);
lean_dec(v_start_4253_);
return v_res_4256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5(lean_object* v_00_u03b1_4257_, lean_object* v_start_4258_, lean_object* v_x_4259_, lean_object* v_x_4260_){
_start:
{
lean_object* v___x_4261_; 
v___x_4261_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4258_, v_x_4259_, v_x_4260_);
return v___x_4261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b1_4262_, lean_object* v_start_4263_, lean_object* v_x_4264_, lean_object* v_x_4265_){
_start:
{
lean_object* v_res_4266_; 
v_res_4266_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5(v_00_u03b1_4262_, v_start_4263_, v_x_4264_, v_x_4265_);
lean_dec(v_start_4263_);
return v_res_4266_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_4267_, lean_object* v_start_4268_, lean_object* v_as_4269_, size_t v_i_4270_, size_t v_stop_4271_, lean_object* v_b_4272_){
_start:
{
lean_object* v___x_4273_; 
v___x_4273_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4268_, v_as_4269_, v_i_4270_, v_stop_4271_, v_b_4272_);
return v___x_4273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_4274_, lean_object* v_start_4275_, lean_object* v_as_4276_, lean_object* v_i_4277_, lean_object* v_stop_4278_, lean_object* v_b_4279_){
_start:
{
size_t v_i_boxed_4280_; size_t v_stop_boxed_4281_; lean_object* v_res_4282_; 
v_i_boxed_4280_ = lean_unbox_usize(v_i_4277_);
lean_dec(v_i_4277_);
v_stop_boxed_4281_ = lean_unbox_usize(v_stop_4278_);
lean_dec(v_stop_4278_);
v_res_4282_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6(v_00_u03b1_4274_, v_start_4275_, v_as_4276_, v_i_boxed_4280_, v_stop_boxed_4281_, v_b_4279_);
lean_dec_ref(v_as_4276_);
lean_dec(v_start_4275_);
return v_res_4282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b1_4283_, lean_object* v_start_4284_, lean_object* v_as_4285_, size_t v_i_4286_, size_t v_stop_4287_, lean_object* v_b_4288_){
_start:
{
lean_object* v___x_4289_; 
v___x_4289_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(v_start_4284_, v_as_4285_, v_i_4286_, v_stop_4287_, v_b_4288_);
return v___x_4289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___boxed(lean_object* v_00_u03b1_4290_, lean_object* v_start_4291_, lean_object* v_as_4292_, lean_object* v_i_4293_, lean_object* v_stop_4294_, lean_object* v_b_4295_){
_start:
{
size_t v_i_boxed_4296_; size_t v_stop_boxed_4297_; lean_object* v_res_4298_; 
v_i_boxed_4296_ = lean_unbox_usize(v_i_4293_);
lean_dec(v_i_4293_);
v_stop_boxed_4297_ = lean_unbox_usize(v_stop_4294_);
lean_dec(v_stop_4294_);
v_res_4298_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6(v_00_u03b1_4290_, v_start_4291_, v_as_4292_, v_i_boxed_4296_, v_stop_boxed_4297_, v_b_4295_);
lean_dec_ref(v_as_4292_);
lean_dec(v_start_4291_);
return v_res_4298_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLCtxOfMonadLift___redArg(lean_object* v_inst_4299_, lean_object* v_inst_4300_){
_start:
{
lean_object* v___x_4301_; 
v___x_4301_ = lean_apply_2(v_inst_4299_, lean_box(0), v_inst_4300_);
return v___x_4301_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLCtxOfMonadLift(lean_object* v_m_4302_, lean_object* v_n_4303_, lean_object* v_inst_4304_, lean_object* v_inst_4305_){
_start:
{
lean_object* v___x_4306_; 
v___x_4306_ = lean_apply_2(v_inst_4304_, lean_box(0), v_inst_4305_);
return v___x_4306_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__0(lean_object* v_toPure_4307_, lean_object* v_d_x3f_4308_, lean_object* v_b_4309_){
_start:
{
if (lean_obj_tag(v_d_x3f_4308_) == 0)
{
lean_object* v___x_4310_; lean_object* v___x_4311_; 
v___x_4310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4310_, 0, v_b_4309_);
v___x_4311_ = lean_apply_2(v_toPure_4307_, lean_box(0), v___x_4310_);
return v___x_4311_;
}
else
{
lean_object* v_val_4312_; lean_object* v___x_4314_; uint8_t v_isShared_4315_; uint8_t v_isSharedCheck_4327_; 
v_val_4312_ = lean_ctor_get(v_d_x3f_4308_, 0);
v_isSharedCheck_4327_ = !lean_is_exclusive(v_d_x3f_4308_);
if (v_isSharedCheck_4327_ == 0)
{
v___x_4314_ = v_d_x3f_4308_;
v_isShared_4315_ = v_isSharedCheck_4327_;
goto v_resetjp_4313_;
}
else
{
lean_inc(v_val_4312_);
lean_dec(v_d_x3f_4308_);
v___x_4314_ = lean_box(0);
v_isShared_4315_ = v_isSharedCheck_4327_;
goto v_resetjp_4313_;
}
v_resetjp_4313_:
{
uint8_t v___x_4316_; 
v___x_4316_ = l_Lean_LocalDecl_isImplementationDetail(v_val_4312_);
if (v___x_4316_ == 0)
{
lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4320_; 
v___x_4317_ = l_Lean_LocalDecl_toExpr(v_val_4312_);
v___x_4318_ = lean_array_push(v_b_4309_, v___x_4317_);
if (v_isShared_4315_ == 0)
{
lean_ctor_set(v___x_4314_, 0, v___x_4318_);
v___x_4320_ = v___x_4314_;
goto v_reusejp_4319_;
}
else
{
lean_object* v_reuseFailAlloc_4322_; 
v_reuseFailAlloc_4322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4322_, 0, v___x_4318_);
v___x_4320_ = v_reuseFailAlloc_4322_;
goto v_reusejp_4319_;
}
v_reusejp_4319_:
{
lean_object* v___x_4321_; 
v___x_4321_ = lean_apply_2(v_toPure_4307_, lean_box(0), v___x_4320_);
return v___x_4321_;
}
}
else
{
lean_object* v___x_4324_; 
lean_dec(v_val_4312_);
if (v_isShared_4315_ == 0)
{
lean_ctor_set(v___x_4314_, 0, v_b_4309_);
v___x_4324_ = v___x_4314_;
goto v_reusejp_4323_;
}
else
{
lean_object* v_reuseFailAlloc_4326_; 
v_reuseFailAlloc_4326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4326_, 0, v_b_4309_);
v___x_4324_ = v_reuseFailAlloc_4326_;
goto v_reusejp_4323_;
}
v_reusejp_4323_:
{
lean_object* v___x_4325_; 
v___x_4325_ = lean_apply_2(v_toPure_4307_, lean_box(0), v___x_4324_);
return v___x_4325_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__1(lean_object* v_toPure_4328_, lean_object* v_____s_4329_){
_start:
{
lean_object* v___x_4330_; 
v___x_4330_ = lean_apply_2(v_toPure_4328_, lean_box(0), v_____s_4329_);
return v___x_4330_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__2(lean_object* v_inst_4331_, lean_object* v_hs_4332_, lean_object* v___f_4333_, lean_object* v_toBind_4334_, lean_object* v___f_4335_, lean_object* v_____do__lift_4336_){
_start:
{
lean_object* v_decls_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; 
v_decls_4337_ = lean_ctor_get(v_____do__lift_4336_, 1);
lean_inc_ref(v_decls_4337_);
lean_dec_ref(v_____do__lift_4336_);
v___x_4338_ = l_Lean_PersistentArray_forIn___redArg(v_inst_4331_, v_decls_4337_, v_hs_4332_, v___f_4333_);
v___x_4339_ = lean_apply_4(v_toBind_4334_, lean_box(0), lean_box(0), v___x_4338_, v___f_4335_);
return v___x_4339_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg(lean_object* v_inst_4342_, lean_object* v_inst_4343_){
_start:
{
lean_object* v_toApplicative_4344_; lean_object* v_toBind_4345_; lean_object* v_toPure_4346_; lean_object* v_hs_4347_; lean_object* v___f_4348_; lean_object* v___f_4349_; lean_object* v___f_4350_; lean_object* v___x_4351_; 
v_toApplicative_4344_ = lean_ctor_get(v_inst_4342_, 0);
v_toBind_4345_ = lean_ctor_get(v_inst_4342_, 1);
lean_inc(v_toBind_4345_);
v_toPure_4346_ = lean_ctor_get(v_toApplicative_4344_, 1);
v_hs_4347_ = ((lean_object*)(l_Lean_getLocalHyps___redArg___closed__0));
lean_inc(v_toPure_4346_);
v___f_4348_ = lean_alloc_closure((void*)(l_Lean_getLocalHyps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4348_, 0, v_toPure_4346_);
lean_inc(v_toPure_4346_);
v___f_4349_ = lean_alloc_closure((void*)(l_Lean_getLocalHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_4349_, 0, v_toPure_4346_);
lean_inc(v_toBind_4345_);
v___f_4350_ = lean_alloc_closure((void*)(l_Lean_getLocalHyps___redArg___lam__2), 6, 5);
lean_closure_set(v___f_4350_, 0, v_inst_4342_);
lean_closure_set(v___f_4350_, 1, v_hs_4347_);
lean_closure_set(v___f_4350_, 2, v___f_4348_);
lean_closure_set(v___f_4350_, 3, v_toBind_4345_);
lean_closure_set(v___f_4350_, 4, v___f_4349_);
v___x_4351_ = lean_apply_4(v_toBind_4345_, lean_box(0), lean_box(0), v_inst_4343_, v___f_4350_);
return v___x_4351_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps(lean_object* v_m_4352_, lean_object* v_inst_4353_, lean_object* v_inst_4354_){
_start:
{
lean_object* v___x_4355_; 
v___x_4355_ = l_Lean_getLocalHyps___redArg(v_inst_4353_, v_inst_4354_);
return v___x_4355_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_replaceFVarId(lean_object* v_fvarId_4356_, lean_object* v_e_4357_, lean_object* v_d_4358_){
_start:
{
lean_object* v___y_4360_; lean_object* v_fvarId_4392_; 
v_fvarId_4392_ = lean_ctor_get(v_d_4358_, 1);
lean_inc(v_fvarId_4392_);
v___y_4360_ = v_fvarId_4392_;
goto v___jp_4359_;
v___jp_4359_:
{
uint8_t v___x_4361_; 
v___x_4361_ = l_Lean_instBEqFVarId_beq(v___y_4360_, v_fvarId_4356_);
lean_dec(v___y_4360_);
if (v___x_4361_ == 0)
{
if (lean_obj_tag(v_d_4358_) == 0)
{
lean_object* v_index_4362_; lean_object* v_fvarId_4363_; lean_object* v_userName_4364_; lean_object* v_type_4365_; uint8_t v_bi_4366_; uint8_t v_kind_4367_; lean_object* v___x_4369_; uint8_t v_isShared_4370_; uint8_t v_isSharedCheck_4375_; 
v_index_4362_ = lean_ctor_get(v_d_4358_, 0);
v_fvarId_4363_ = lean_ctor_get(v_d_4358_, 1);
v_userName_4364_ = lean_ctor_get(v_d_4358_, 2);
v_type_4365_ = lean_ctor_get(v_d_4358_, 3);
v_bi_4366_ = lean_ctor_get_uint8(v_d_4358_, sizeof(void*)*4);
v_kind_4367_ = lean_ctor_get_uint8(v_d_4358_, sizeof(void*)*4 + 1);
v_isSharedCheck_4375_ = !lean_is_exclusive(v_d_4358_);
if (v_isSharedCheck_4375_ == 0)
{
v___x_4369_ = v_d_4358_;
v_isShared_4370_ = v_isSharedCheck_4375_;
goto v_resetjp_4368_;
}
else
{
lean_inc(v_type_4365_);
lean_inc(v_userName_4364_);
lean_inc(v_fvarId_4363_);
lean_inc(v_index_4362_);
lean_dec(v_d_4358_);
v___x_4369_ = lean_box(0);
v_isShared_4370_ = v_isSharedCheck_4375_;
goto v_resetjp_4368_;
}
v_resetjp_4368_:
{
lean_object* v___x_4371_; lean_object* v___x_4373_; 
v___x_4371_ = l_Lean_Expr_replaceFVarId(v_type_4365_, v_fvarId_4356_, v_e_4357_);
lean_dec_ref(v_type_4365_);
if (v_isShared_4370_ == 0)
{
lean_ctor_set(v___x_4369_, 3, v___x_4371_);
v___x_4373_ = v___x_4369_;
goto v_reusejp_4372_;
}
else
{
lean_object* v_reuseFailAlloc_4374_; 
v_reuseFailAlloc_4374_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4374_, 0, v_index_4362_);
lean_ctor_set(v_reuseFailAlloc_4374_, 1, v_fvarId_4363_);
lean_ctor_set(v_reuseFailAlloc_4374_, 2, v_userName_4364_);
lean_ctor_set(v_reuseFailAlloc_4374_, 3, v___x_4371_);
lean_ctor_set_uint8(v_reuseFailAlloc_4374_, sizeof(void*)*4, v_bi_4366_);
lean_ctor_set_uint8(v_reuseFailAlloc_4374_, sizeof(void*)*4 + 1, v_kind_4367_);
v___x_4373_ = v_reuseFailAlloc_4374_;
goto v_reusejp_4372_;
}
v_reusejp_4372_:
{
return v___x_4373_;
}
}
}
else
{
lean_object* v_index_4376_; lean_object* v_fvarId_4377_; lean_object* v_userName_4378_; lean_object* v_type_4379_; lean_object* v_value_4380_; uint8_t v_nondep_4381_; uint8_t v_kind_4382_; lean_object* v___x_4384_; uint8_t v_isShared_4385_; uint8_t v_isSharedCheck_4391_; 
v_index_4376_ = lean_ctor_get(v_d_4358_, 0);
v_fvarId_4377_ = lean_ctor_get(v_d_4358_, 1);
v_userName_4378_ = lean_ctor_get(v_d_4358_, 2);
v_type_4379_ = lean_ctor_get(v_d_4358_, 3);
v_value_4380_ = lean_ctor_get(v_d_4358_, 4);
v_nondep_4381_ = lean_ctor_get_uint8(v_d_4358_, sizeof(void*)*5);
v_kind_4382_ = lean_ctor_get_uint8(v_d_4358_, sizeof(void*)*5 + 1);
v_isSharedCheck_4391_ = !lean_is_exclusive(v_d_4358_);
if (v_isSharedCheck_4391_ == 0)
{
v___x_4384_ = v_d_4358_;
v_isShared_4385_ = v_isSharedCheck_4391_;
goto v_resetjp_4383_;
}
else
{
lean_inc(v_value_4380_);
lean_inc(v_type_4379_);
lean_inc(v_userName_4378_);
lean_inc(v_fvarId_4377_);
lean_inc(v_index_4376_);
lean_dec(v_d_4358_);
v___x_4384_ = lean_box(0);
v_isShared_4385_ = v_isSharedCheck_4391_;
goto v_resetjp_4383_;
}
v_resetjp_4383_:
{
lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4389_; 
lean_inc(v_fvarId_4356_);
v___x_4386_ = l_Lean_Expr_replaceFVarId(v_type_4379_, v_fvarId_4356_, v_e_4357_);
lean_dec_ref(v_type_4379_);
v___x_4387_ = l_Lean_Expr_replaceFVarId(v_value_4380_, v_fvarId_4356_, v_e_4357_);
lean_dec_ref(v_value_4380_);
if (v_isShared_4385_ == 0)
{
lean_ctor_set(v___x_4384_, 4, v___x_4387_);
lean_ctor_set(v___x_4384_, 3, v___x_4386_);
v___x_4389_ = v___x_4384_;
goto v_reusejp_4388_;
}
else
{
lean_object* v_reuseFailAlloc_4390_; 
v_reuseFailAlloc_4390_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_4390_, 0, v_index_4376_);
lean_ctor_set(v_reuseFailAlloc_4390_, 1, v_fvarId_4377_);
lean_ctor_set(v_reuseFailAlloc_4390_, 2, v_userName_4378_);
lean_ctor_set(v_reuseFailAlloc_4390_, 3, v___x_4386_);
lean_ctor_set(v_reuseFailAlloc_4390_, 4, v___x_4387_);
lean_ctor_set_uint8(v_reuseFailAlloc_4390_, sizeof(void*)*5, v_nondep_4381_);
lean_ctor_set_uint8(v_reuseFailAlloc_4390_, sizeof(void*)*5 + 1, v_kind_4382_);
v___x_4389_ = v_reuseFailAlloc_4390_;
goto v_reusejp_4388_;
}
v_reusejp_4388_:
{
return v___x_4389_;
}
}
}
}
else
{
lean_dec(v_fvarId_4356_);
return v_d_4358_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_replaceFVarId___boxed(lean_object* v_fvarId_4393_, lean_object* v_e_4394_, lean_object* v_d_4395_){
_start:
{
lean_object* v_res_4396_; 
v_res_4396_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_4393_, v_e_4394_, v_d_4395_);
lean_dec_ref(v_e_4394_);
return v_res_4396_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId___lam__0(lean_object* v_fvarId_4397_, lean_object* v_e_4398_, lean_object* v_x_4399_){
_start:
{
lean_object* v___x_4400_; 
v___x_4400_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_4397_, v_e_4398_, v_x_4399_);
return v___x_4400_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId___lam__0___boxed(lean_object* v_fvarId_4401_, lean_object* v_e_4402_, lean_object* v_x_4403_){
_start:
{
lean_object* v_res_4404_; 
v_res_4404_ = l_Lean_LocalContext_replaceFVarId___lam__0(v_fvarId_4401_, v_e_4402_, v_x_4403_);
lean_dec_ref(v_e_4402_);
return v_res_4404_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(lean_object* v_fvarId_4405_, lean_object* v_e_4406_, size_t v_sz_4407_, size_t v_i_4408_, lean_object* v_bs_4409_){
_start:
{
uint8_t v___x_4410_; 
v___x_4410_ = lean_usize_dec_lt(v_i_4408_, v_sz_4407_);
if (v___x_4410_ == 0)
{
lean_dec(v_fvarId_4405_);
return v_bs_4409_;
}
else
{
lean_object* v_v_4411_; lean_object* v___x_4412_; lean_object* v_bs_x27_4413_; lean_object* v___y_4415_; 
v_v_4411_ = lean_array_uget(v_bs_4409_, v_i_4408_);
v___x_4412_ = lean_unsigned_to_nat(0u);
v_bs_x27_4413_ = lean_array_uset(v_bs_4409_, v_i_4408_, v___x_4412_);
if (lean_obj_tag(v_v_4411_) == 0)
{
v___y_4415_ = v_v_4411_;
goto v___jp_4414_;
}
else
{
lean_object* v_val_4420_; lean_object* v___x_4422_; uint8_t v_isShared_4423_; uint8_t v_isSharedCheck_4428_; 
v_val_4420_ = lean_ctor_get(v_v_4411_, 0);
v_isSharedCheck_4428_ = !lean_is_exclusive(v_v_4411_);
if (v_isSharedCheck_4428_ == 0)
{
v___x_4422_ = v_v_4411_;
v_isShared_4423_ = v_isSharedCheck_4428_;
goto v_resetjp_4421_;
}
else
{
lean_inc(v_val_4420_);
lean_dec(v_v_4411_);
v___x_4422_ = lean_box(0);
v_isShared_4423_ = v_isSharedCheck_4428_;
goto v_resetjp_4421_;
}
v_resetjp_4421_:
{
lean_object* v___x_4424_; lean_object* v___x_4426_; 
lean_inc(v_fvarId_4405_);
v___x_4424_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_4405_, v_e_4406_, v_val_4420_);
if (v_isShared_4423_ == 0)
{
lean_ctor_set(v___x_4422_, 0, v___x_4424_);
v___x_4426_ = v___x_4422_;
goto v_reusejp_4425_;
}
else
{
lean_object* v_reuseFailAlloc_4427_; 
v_reuseFailAlloc_4427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4427_, 0, v___x_4424_);
v___x_4426_ = v_reuseFailAlloc_4427_;
goto v_reusejp_4425_;
}
v_reusejp_4425_:
{
v___y_4415_ = v___x_4426_;
goto v___jp_4414_;
}
}
}
v___jp_4414_:
{
size_t v___x_4416_; size_t v___x_4417_; lean_object* v___x_4418_; 
v___x_4416_ = ((size_t)1ULL);
v___x_4417_ = lean_usize_add(v_i_4408_, v___x_4416_);
v___x_4418_ = lean_array_uset(v_bs_x27_4413_, v_i_4408_, v___y_4415_);
v_i_4408_ = v___x_4417_;
v_bs_4409_ = v___x_4418_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3___boxed(lean_object* v_fvarId_4429_, lean_object* v_e_4430_, lean_object* v_sz_4431_, lean_object* v_i_4432_, lean_object* v_bs_4433_){
_start:
{
size_t v_sz_boxed_4434_; size_t v_i_boxed_4435_; lean_object* v_res_4436_; 
v_sz_boxed_4434_ = lean_unbox_usize(v_sz_4431_);
lean_dec(v_sz_4431_);
v_i_boxed_4435_ = lean_unbox_usize(v_i_4432_);
lean_dec(v_i_4432_);
v_res_4436_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(v_fvarId_4429_, v_e_4430_, v_sz_boxed_4434_, v_i_boxed_4435_, v_bs_4433_);
lean_dec_ref(v_e_4430_);
return v_res_4436_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(lean_object* v_fvarId_4437_, lean_object* v_e_4438_, size_t v_sz_4439_, size_t v_i_4440_, lean_object* v_bs_4441_){
_start:
{
uint8_t v___x_4442_; 
v___x_4442_ = lean_usize_dec_lt(v_i_4440_, v_sz_4439_);
if (v___x_4442_ == 0)
{
lean_dec(v_fvarId_4437_);
return v_bs_4441_;
}
else
{
lean_object* v_v_4443_; lean_object* v___x_4444_; lean_object* v_bs_x27_4445_; lean_object* v___x_4446_; size_t v___x_4447_; size_t v___x_4448_; lean_object* v___x_4449_; 
v_v_4443_ = lean_array_uget(v_bs_4441_, v_i_4440_);
v___x_4444_ = lean_unsigned_to_nat(0u);
v_bs_x27_4445_ = lean_array_uset(v_bs_4441_, v_i_4440_, v___x_4444_);
lean_inc(v_fvarId_4437_);
v___x_4446_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(v_fvarId_4437_, v_e_4438_, v_v_4443_);
v___x_4447_ = ((size_t)1ULL);
v___x_4448_ = lean_usize_add(v_i_4440_, v___x_4447_);
v___x_4449_ = lean_array_uset(v_bs_x27_4445_, v_i_4440_, v___x_4446_);
v_i_4440_ = v___x_4448_;
v_bs_4441_ = v___x_4449_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(lean_object* v_fvarId_4451_, lean_object* v_e_4452_, lean_object* v_x_4453_){
_start:
{
if (lean_obj_tag(v_x_4453_) == 0)
{
lean_object* v_cs_4454_; lean_object* v___x_4456_; uint8_t v_isShared_4457_; uint8_t v_isSharedCheck_4464_; 
v_cs_4454_ = lean_ctor_get(v_x_4453_, 0);
v_isSharedCheck_4464_ = !lean_is_exclusive(v_x_4453_);
if (v_isSharedCheck_4464_ == 0)
{
v___x_4456_ = v_x_4453_;
v_isShared_4457_ = v_isSharedCheck_4464_;
goto v_resetjp_4455_;
}
else
{
lean_inc(v_cs_4454_);
lean_dec(v_x_4453_);
v___x_4456_ = lean_box(0);
v_isShared_4457_ = v_isSharedCheck_4464_;
goto v_resetjp_4455_;
}
v_resetjp_4455_:
{
size_t v_sz_4458_; size_t v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4462_; 
v_sz_4458_ = lean_array_size(v_cs_4454_);
v___x_4459_ = ((size_t)0ULL);
v___x_4460_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(v_fvarId_4451_, v_e_4452_, v_sz_4458_, v___x_4459_, v_cs_4454_);
if (v_isShared_4457_ == 0)
{
lean_ctor_set(v___x_4456_, 0, v___x_4460_);
v___x_4462_ = v___x_4456_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4463_; 
v_reuseFailAlloc_4463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4463_, 0, v___x_4460_);
v___x_4462_ = v_reuseFailAlloc_4463_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
return v___x_4462_;
}
}
}
else
{
lean_object* v_vs_4465_; lean_object* v___x_4467_; uint8_t v_isShared_4468_; uint8_t v_isSharedCheck_4475_; 
v_vs_4465_ = lean_ctor_get(v_x_4453_, 0);
v_isSharedCheck_4475_ = !lean_is_exclusive(v_x_4453_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4467_ = v_x_4453_;
v_isShared_4468_ = v_isSharedCheck_4475_;
goto v_resetjp_4466_;
}
else
{
lean_inc(v_vs_4465_);
lean_dec(v_x_4453_);
v___x_4467_ = lean_box(0);
v_isShared_4468_ = v_isSharedCheck_4475_;
goto v_resetjp_4466_;
}
v_resetjp_4466_:
{
size_t v_sz_4469_; size_t v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4473_; 
v_sz_4469_ = lean_array_size(v_vs_4465_);
v___x_4470_ = ((size_t)0ULL);
v___x_4471_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(v_fvarId_4451_, v_e_4452_, v_sz_4469_, v___x_4470_, v_vs_4465_);
if (v_isShared_4468_ == 0)
{
lean_ctor_set(v___x_4467_, 0, v___x_4471_);
v___x_4473_ = v___x_4467_;
goto v_reusejp_4472_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v___x_4471_);
v___x_4473_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4472_;
}
v_reusejp_4472_:
{
return v___x_4473_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2___boxed(lean_object* v_fvarId_4476_, lean_object* v_e_4477_, lean_object* v_x_4478_){
_start:
{
lean_object* v_res_4479_; 
v_res_4479_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(v_fvarId_4476_, v_e_4477_, v_x_4478_);
lean_dec_ref(v_e_4477_);
return v_res_4479_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4___boxed(lean_object* v_fvarId_4480_, lean_object* v_e_4481_, lean_object* v_sz_4482_, lean_object* v_i_4483_, lean_object* v_bs_4484_){
_start:
{
size_t v_sz_boxed_4485_; size_t v_i_boxed_4486_; lean_object* v_res_4487_; 
v_sz_boxed_4485_ = lean_unbox_usize(v_sz_4482_);
lean_dec(v_sz_4482_);
v_i_boxed_4486_ = lean_unbox_usize(v_i_4483_);
lean_dec(v_i_4483_);
v_res_4487_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(v_fvarId_4480_, v_e_4481_, v_sz_boxed_4485_, v_i_boxed_4486_, v_bs_4484_);
lean_dec_ref(v_e_4481_);
return v_res_4487_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(lean_object* v_fvarId_4488_, lean_object* v_e_4489_, lean_object* v_t_4490_){
_start:
{
lean_object* v_root_4491_; lean_object* v_tail_4492_; lean_object* v_size_4493_; size_t v_shift_4494_; lean_object* v_tailOff_4495_; lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4506_; 
v_root_4491_ = lean_ctor_get(v_t_4490_, 0);
v_tail_4492_ = lean_ctor_get(v_t_4490_, 1);
v_size_4493_ = lean_ctor_get(v_t_4490_, 2);
v_shift_4494_ = lean_ctor_get_usize(v_t_4490_, 4);
v_tailOff_4495_ = lean_ctor_get(v_t_4490_, 3);
v_isSharedCheck_4506_ = !lean_is_exclusive(v_t_4490_);
if (v_isSharedCheck_4506_ == 0)
{
v___x_4497_ = v_t_4490_;
v_isShared_4498_ = v_isSharedCheck_4506_;
goto v_resetjp_4496_;
}
else
{
lean_inc(v_tailOff_4495_);
lean_inc(v_size_4493_);
lean_inc(v_tail_4492_);
lean_inc(v_root_4491_);
lean_dec(v_t_4490_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4506_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
lean_object* v___x_4499_; size_t v_sz_4500_; size_t v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4504_; 
lean_inc(v_fvarId_4488_);
v___x_4499_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(v_fvarId_4488_, v_e_4489_, v_root_4491_);
v_sz_4500_ = lean_array_size(v_tail_4492_);
v___x_4501_ = ((size_t)0ULL);
v___x_4502_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(v_fvarId_4488_, v_e_4489_, v_sz_4500_, v___x_4501_, v_tail_4492_);
if (v_isShared_4498_ == 0)
{
lean_ctor_set(v___x_4497_, 1, v___x_4502_);
lean_ctor_set(v___x_4497_, 0, v___x_4499_);
v___x_4504_ = v___x_4497_;
goto v_reusejp_4503_;
}
else
{
lean_object* v_reuseFailAlloc_4505_; 
v_reuseFailAlloc_4505_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_4505_, 0, v___x_4499_);
lean_ctor_set(v_reuseFailAlloc_4505_, 1, v___x_4502_);
lean_ctor_set(v_reuseFailAlloc_4505_, 2, v_size_4493_);
lean_ctor_set(v_reuseFailAlloc_4505_, 3, v_tailOff_4495_);
lean_ctor_set_usize(v_reuseFailAlloc_4505_, 4, v_shift_4494_);
v___x_4504_ = v_reuseFailAlloc_4505_;
goto v_reusejp_4503_;
}
v_reusejp_4503_:
{
return v___x_4504_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1___boxed(lean_object* v_fvarId_4507_, lean_object* v_e_4508_, lean_object* v_t_4509_){
_start:
{
lean_object* v_res_4510_; 
v_res_4510_ = l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(v_fvarId_4507_, v_e_4508_, v_t_4509_);
lean_dec_ref(v_e_4508_);
return v_res_4510_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg___lam__0(lean_object* v_f_4511_, lean_object* v_x_4512_){
_start:
{
lean_object* v___x_4513_; 
v___x_4513_ = lean_apply_1(v_f_4511_, v_x_4512_);
return v___x_4513_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(lean_object* v_f_4514_, lean_object* v_as_4515_, lean_object* v_i_4516_, lean_object* v_acc_4517_){
_start:
{
lean_object* v___x_4518_; uint8_t v___x_4519_; 
v___x_4518_ = lean_array_get_size(v_as_4515_);
v___x_4519_ = lean_nat_dec_eq(v_i_4516_, v___x_4518_);
if (v___x_4519_ == 0)
{
lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; 
v___x_4520_ = lean_array_fget_borrowed(v_as_4515_, v_i_4516_);
lean_inc(v_f_4514_);
lean_inc(v___x_4520_);
v___x_4521_ = lean_apply_1(v_f_4514_, v___x_4520_);
v___x_4522_ = lean_unsigned_to_nat(1u);
v___x_4523_ = lean_nat_add(v_i_4516_, v___x_4522_);
lean_dec(v_i_4516_);
v___x_4524_ = lean_array_push(v_acc_4517_, v___x_4521_);
v_i_4516_ = v___x_4523_;
v_acc_4517_ = v___x_4524_;
goto _start;
}
else
{
lean_dec(v_i_4516_);
lean_dec(v_f_4514_);
return v_acc_4517_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg___boxed(lean_object* v_f_4526_, lean_object* v_as_4527_, lean_object* v_i_4528_, lean_object* v_acc_4529_){
_start:
{
lean_object* v_res_4530_; 
v_res_4530_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_f_4526_, v_as_4527_, v_i_4528_, v_acc_4529_);
lean_dec_ref(v_as_4527_);
return v_res_4530_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_f_4531_, lean_object* v_as_4532_){
_start:
{
lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; 
v___x_4533_ = lean_unsigned_to_nat(0u);
v___x_4534_ = lean_array_get_size(v_as_4532_);
v___x_4535_ = lean_mk_empty_array_with_capacity(v___x_4534_);
v___x_4536_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_f_4531_, v_as_4532_, v___x_4533_, v___x_4535_);
return v___x_4536_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_f_4537_, lean_object* v_as_4538_){
_start:
{
lean_object* v_res_4539_; 
v_res_4539_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(v_f_4537_, v_as_4538_);
lean_dec_ref(v_as_4538_);
return v_res_4539_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_4540_, size_t v_sz_4541_, size_t v_i_4542_, lean_object* v_bs_4543_){
_start:
{
uint8_t v___x_4544_; 
v___x_4544_ = lean_usize_dec_lt(v_i_4542_, v_sz_4541_);
if (v___x_4544_ == 0)
{
lean_dec(v_f_4540_);
return v_bs_4543_;
}
else
{
lean_object* v_v_4545_; lean_object* v___x_4546_; lean_object* v_bs_x27_4547_; lean_object* v___y_4549_; 
v_v_4545_ = lean_array_uget(v_bs_4543_, v_i_4542_);
v___x_4546_ = lean_unsigned_to_nat(0u);
v_bs_x27_4547_ = lean_array_uset(v_bs_4543_, v_i_4542_, v___x_4546_);
switch(lean_obj_tag(v_v_4545_))
{
case 0:
{
lean_object* v_key_4554_; lean_object* v_val_4555_; lean_object* v___x_4557_; uint8_t v_isShared_4558_; uint8_t v_isSharedCheck_4563_; 
v_key_4554_ = lean_ctor_get(v_v_4545_, 0);
v_val_4555_ = lean_ctor_get(v_v_4545_, 1);
v_isSharedCheck_4563_ = !lean_is_exclusive(v_v_4545_);
if (v_isSharedCheck_4563_ == 0)
{
v___x_4557_ = v_v_4545_;
v_isShared_4558_ = v_isSharedCheck_4563_;
goto v_resetjp_4556_;
}
else
{
lean_inc(v_val_4555_);
lean_inc(v_key_4554_);
lean_dec(v_v_4545_);
v___x_4557_ = lean_box(0);
v_isShared_4558_ = v_isSharedCheck_4563_;
goto v_resetjp_4556_;
}
v_resetjp_4556_:
{
lean_object* v___x_4559_; lean_object* v___x_4561_; 
lean_inc(v_f_4540_);
v___x_4559_ = lean_apply_1(v_f_4540_, v_val_4555_);
if (v_isShared_4558_ == 0)
{
lean_ctor_set(v___x_4557_, 1, v___x_4559_);
v___x_4561_ = v___x_4557_;
goto v_reusejp_4560_;
}
else
{
lean_object* v_reuseFailAlloc_4562_; 
v_reuseFailAlloc_4562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4562_, 0, v_key_4554_);
lean_ctor_set(v_reuseFailAlloc_4562_, 1, v___x_4559_);
v___x_4561_ = v_reuseFailAlloc_4562_;
goto v_reusejp_4560_;
}
v_reusejp_4560_:
{
v___y_4549_ = v___x_4561_;
goto v___jp_4548_;
}
}
}
case 1:
{
lean_object* v_node_4564_; lean_object* v___x_4566_; uint8_t v_isShared_4567_; uint8_t v_isSharedCheck_4572_; 
v_node_4564_ = lean_ctor_get(v_v_4545_, 0);
v_isSharedCheck_4572_ = !lean_is_exclusive(v_v_4545_);
if (v_isSharedCheck_4572_ == 0)
{
v___x_4566_ = v_v_4545_;
v_isShared_4567_ = v_isSharedCheck_4572_;
goto v_resetjp_4565_;
}
else
{
lean_inc(v_node_4564_);
lean_dec(v_v_4545_);
v___x_4566_ = lean_box(0);
v_isShared_4567_ = v_isSharedCheck_4572_;
goto v_resetjp_4565_;
}
v_resetjp_4565_:
{
lean_object* v___x_4568_; lean_object* v___x_4570_; 
lean_inc(v_f_4540_);
v___x_4568_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4540_, v_node_4564_);
if (v_isShared_4567_ == 0)
{
lean_ctor_set(v___x_4566_, 0, v___x_4568_);
v___x_4570_ = v___x_4566_;
goto v_reusejp_4569_;
}
else
{
lean_object* v_reuseFailAlloc_4571_; 
v_reuseFailAlloc_4571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4571_, 0, v___x_4568_);
v___x_4570_ = v_reuseFailAlloc_4571_;
goto v_reusejp_4569_;
}
v_reusejp_4569_:
{
v___y_4549_ = v___x_4570_;
goto v___jp_4548_;
}
}
}
default: 
{
lean_object* v___x_4573_; 
v___x_4573_ = lean_box(2);
v___y_4549_ = v___x_4573_;
goto v___jp_4548_;
}
}
v___jp_4548_:
{
size_t v___x_4550_; size_t v___x_4551_; lean_object* v___x_4552_; 
v___x_4550_ = ((size_t)1ULL);
v___x_4551_ = lean_usize_add(v_i_4542_, v___x_4550_);
v___x_4552_ = lean_array_uset(v_bs_x27_4547_, v_i_4542_, v___y_4549_);
v_i_4542_ = v___x_4551_;
v_bs_4543_ = v___x_4552_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(lean_object* v_f_4574_, lean_object* v_n_4575_){
_start:
{
if (lean_obj_tag(v_n_4575_) == 0)
{
lean_object* v_es_4576_; lean_object* v___x_4578_; uint8_t v_isShared_4579_; uint8_t v_isSharedCheck_4586_; 
v_es_4576_ = lean_ctor_get(v_n_4575_, 0);
v_isSharedCheck_4586_ = !lean_is_exclusive(v_n_4575_);
if (v_isSharedCheck_4586_ == 0)
{
v___x_4578_ = v_n_4575_;
v_isShared_4579_ = v_isSharedCheck_4586_;
goto v_resetjp_4577_;
}
else
{
lean_inc(v_es_4576_);
lean_dec(v_n_4575_);
v___x_4578_ = lean_box(0);
v_isShared_4579_ = v_isSharedCheck_4586_;
goto v_resetjp_4577_;
}
v_resetjp_4577_:
{
size_t v_sz_4580_; size_t v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4584_; 
v_sz_4580_ = lean_array_size(v_es_4576_);
v___x_4581_ = ((size_t)0ULL);
v___x_4582_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(v_f_4574_, v_sz_4580_, v___x_4581_, v_es_4576_);
if (v_isShared_4579_ == 0)
{
lean_ctor_set(v___x_4578_, 0, v___x_4582_);
v___x_4584_ = v___x_4578_;
goto v_reusejp_4583_;
}
else
{
lean_object* v_reuseFailAlloc_4585_; 
v_reuseFailAlloc_4585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4585_, 0, v___x_4582_);
v___x_4584_ = v_reuseFailAlloc_4585_;
goto v_reusejp_4583_;
}
v_reusejp_4583_:
{
return v___x_4584_;
}
}
}
else
{
lean_object* v_ks_4587_; lean_object* v_vs_4588_; lean_object* v___x_4590_; uint8_t v_isShared_4591_; uint8_t v_isSharedCheck_4596_; 
v_ks_4587_ = lean_ctor_get(v_n_4575_, 0);
v_vs_4588_ = lean_ctor_get(v_n_4575_, 1);
v_isSharedCheck_4596_ = !lean_is_exclusive(v_n_4575_);
if (v_isSharedCheck_4596_ == 0)
{
v___x_4590_ = v_n_4575_;
v_isShared_4591_ = v_isSharedCheck_4596_;
goto v_resetjp_4589_;
}
else
{
lean_inc(v_vs_4588_);
lean_inc(v_ks_4587_);
lean_dec(v_n_4575_);
v___x_4590_ = lean_box(0);
v_isShared_4591_ = v_isSharedCheck_4596_;
goto v_resetjp_4589_;
}
v_resetjp_4589_:
{
lean_object* v_val_4592_; lean_object* v___x_4594_; 
v_val_4592_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(v_f_4574_, v_vs_4588_);
lean_dec_ref(v_vs_4588_);
if (v_isShared_4591_ == 0)
{
lean_ctor_set(v___x_4590_, 1, v_val_4592_);
v___x_4594_ = v___x_4590_;
goto v_reusejp_4593_;
}
else
{
lean_object* v_reuseFailAlloc_4595_; 
v_reuseFailAlloc_4595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4595_, 0, v_ks_4587_);
lean_ctor_set(v_reuseFailAlloc_4595_, 1, v_val_4592_);
v___x_4594_ = v_reuseFailAlloc_4595_;
goto v_reusejp_4593_;
}
v_reusejp_4593_:
{
return v___x_4594_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_4597_, lean_object* v_sz_4598_, lean_object* v_i_4599_, lean_object* v_bs_4600_){
_start:
{
size_t v_sz_boxed_4601_; size_t v_i_boxed_4602_; lean_object* v_res_4603_; 
v_sz_boxed_4601_ = lean_unbox_usize(v_sz_4598_);
lean_dec(v_sz_4598_);
v_i_boxed_4602_ = lean_unbox_usize(v_i_4599_);
lean_dec(v_i_4599_);
v_res_4603_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(v_f_4597_, v_sz_boxed_4601_, v_i_boxed_4602_, v_bs_4600_);
return v_res_4603_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(lean_object* v_pm_4604_, lean_object* v_f_4605_){
_start:
{
lean_object* v___f_4606_; lean_object* v___x_4607_; 
v___f_4606_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4606_, 0, v_f_4605_);
v___x_4607_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v___f_4606_, v_pm_4604_);
return v___x_4607_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId(lean_object* v_fvarId_4608_, lean_object* v_e_4609_, lean_object* v_lctx_4610_){
_start:
{
lean_object* v_lctx_4611_; lean_object* v_fvarIdToDecl_4612_; lean_object* v_decls_4613_; lean_object* v_auxDeclToFullName_4614_; lean_object* v___x_4616_; uint8_t v_isShared_4617_; uint8_t v_isSharedCheck_4624_; 
lean_inc(v_fvarId_4608_);
v_lctx_4611_ = lean_local_ctx_erase(v_lctx_4610_, v_fvarId_4608_);
v_fvarIdToDecl_4612_ = lean_ctor_get(v_lctx_4611_, 0);
v_decls_4613_ = lean_ctor_get(v_lctx_4611_, 1);
v_auxDeclToFullName_4614_ = lean_ctor_get(v_lctx_4611_, 2);
v_isSharedCheck_4624_ = !lean_is_exclusive(v_lctx_4611_);
if (v_isSharedCheck_4624_ == 0)
{
v___x_4616_ = v_lctx_4611_;
v_isShared_4617_ = v_isSharedCheck_4624_;
goto v_resetjp_4615_;
}
else
{
lean_inc(v_auxDeclToFullName_4614_);
lean_inc(v_decls_4613_);
lean_inc(v_fvarIdToDecl_4612_);
lean_dec(v_lctx_4611_);
v___x_4616_ = lean_box(0);
v_isShared_4617_ = v_isSharedCheck_4624_;
goto v_resetjp_4615_;
}
v_resetjp_4615_:
{
lean_object* v___f_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4622_; 
lean_inc_ref(v_e_4609_);
lean_inc(v_fvarId_4608_);
v___f_4618_ = lean_alloc_closure((void*)(l_Lean_LocalContext_replaceFVarId___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4618_, 0, v_fvarId_4608_);
lean_closure_set(v___f_4618_, 1, v_e_4609_);
v___x_4619_ = l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(v_fvarIdToDecl_4612_, v___f_4618_);
v___x_4620_ = l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(v_fvarId_4608_, v_e_4609_, v_decls_4613_);
lean_dec_ref(v_e_4609_);
if (v_isShared_4617_ == 0)
{
lean_ctor_set(v___x_4616_, 1, v___x_4620_);
lean_ctor_set(v___x_4616_, 0, v___x_4619_);
v___x_4622_ = v___x_4616_;
goto v_reusejp_4621_;
}
else
{
lean_object* v_reuseFailAlloc_4623_; 
v_reuseFailAlloc_4623_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4623_, 0, v___x_4619_);
lean_ctor_set(v_reuseFailAlloc_4623_, 1, v___x_4620_);
lean_ctor_set(v_reuseFailAlloc_4623_, 2, v_auxDeclToFullName_4614_);
v___x_4622_ = v_reuseFailAlloc_4623_;
goto v_reusejp_4621_;
}
v_reusejp_4621_:
{
return v___x_4622_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0(lean_object* v_00_u03b2_4625_, lean_object* v_00_u03c3_4626_, lean_object* v_pm_4627_, lean_object* v_f_4628_){
_start:
{
lean_object* v___x_4629_; 
v___x_4629_ = l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(v_pm_4627_, v_f_4628_);
return v___x_4629_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0___redArg(lean_object* v_pm_4630_, lean_object* v_f_4631_){
_start:
{
lean_object* v___x_4632_; 
v___x_4632_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4631_, v_pm_4630_);
return v___x_4632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0(lean_object* v_00_u03b2_4633_, lean_object* v_00_u03c3_4634_, lean_object* v_pm_4635_, lean_object* v_f_4636_){
_start:
{
lean_object* v___x_4637_; 
v___x_4637_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4636_, v_pm_4635_);
return v___x_4637_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_4638_, lean_object* v_00_u03b2_4639_, lean_object* v_00_u03c3_4640_, lean_object* v_f_4641_, lean_object* v_n_4642_){
_start:
{
lean_object* v___x_4643_; 
v___x_4643_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4641_, v_n_4642_);
return v___x_4643_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_4644_, lean_object* v_00_u03b2_4645_, lean_object* v_00_u03c3_4646_, lean_object* v_f_4647_, size_t v_sz_4648_, size_t v_i_4649_, lean_object* v_bs_4650_){
_start:
{
lean_object* v___x_4651_; 
v___x_4651_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(v_f_4647_, v_sz_4648_, v_i_4649_, v_bs_4650_);
return v___x_4651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_4652_, lean_object* v_00_u03b2_4653_, lean_object* v_00_u03c3_4654_, lean_object* v_f_4655_, lean_object* v_sz_4656_, lean_object* v_i_4657_, lean_object* v_bs_4658_){
_start:
{
size_t v_sz_boxed_4659_; size_t v_i_boxed_4660_; lean_object* v_res_4661_; 
v_sz_boxed_4659_ = lean_unbox_usize(v_sz_4656_);
lean_dec(v_sz_4656_);
v_i_boxed_4660_ = lean_unbox_usize(v_i_4657_);
lean_dec(v_i_4657_);
v_res_4661_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_4652_, v_00_u03b2_4653_, v_00_u03c3_4654_, v_f_4655_, v_sz_boxed_4659_, v_i_boxed_4660_, v_bs_4658_);
return v_res_4661_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_4662_, lean_object* v_00_u03b2_4663_, lean_object* v_f_4664_, lean_object* v_as_4665_){
_start:
{
lean_object* v___x_4666_; 
v___x_4666_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(v_f_4664_, v_as_4665_);
return v___x_4666_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_4667_, lean_object* v_00_u03b2_4668_, lean_object* v_f_4669_, lean_object* v_as_4670_){
_start:
{
lean_object* v_res_4671_; 
v_res_4671_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_4667_, v_00_u03b2_4668_, v_f_4669_, v_as_4670_);
lean_dec_ref(v_as_4670_);
return v_res_4671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7(lean_object* v_00_u03b1_4672_, lean_object* v_00_u03b2_4673_, lean_object* v_f_4674_, lean_object* v_as_4675_, lean_object* v_i_4676_, lean_object* v_acc_4677_, lean_object* v_hle_4678_){
_start:
{
lean_object* v___x_4679_; 
v___x_4679_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_f_4674_, v_as_4675_, v_i_4676_, v_acc_4677_);
return v___x_4679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___boxed(lean_object* v_00_u03b1_4680_, lean_object* v_00_u03b2_4681_, lean_object* v_f_4682_, lean_object* v_as_4683_, lean_object* v_i_4684_, lean_object* v_acc_4685_, lean_object* v_hle_4686_){
_start:
{
lean_object* v_res_4687_; 
v_res_4687_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7(v_00_u03b1_4680_, v_00_u03b2_4681_, v_f_4682_, v_as_4683_, v_i_4684_, v_acc_4685_, v_hle_4686_);
lean_dec_ref(v_as_4683_);
return v_res_4687_;
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
