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
lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg();
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_set___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
uint8_t l_Lean_Name_isImplementationDetail(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_pop___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
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
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_sanitizeName(lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Nat_foldRev___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_getSanitizeNames(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_LocalDeclKind_ofBinderName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ofBinderName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkEmpty___redArg();
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkEmpty___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_LocalContext_mkEmpty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LocalContext_mkEmpty___closed__0;
LEAN_EXPORT lean_object* lean_mk_empty_local_ctx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_empty;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_isEmpty(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_LocalContext_erase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_erase___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Lean_LocalDeclKind_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_LocalDeclKind_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Lean_LocalDeclKind_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim___redArg(lean_object* v_default_22_){
_start:
{
lean_inc(v_default_22_);
return v_default_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim___redArg___boxed(lean_object* v_default_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_LocalDeclKind_default_elim___redArg(v_default_23_);
lean_dec(v_default_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_default_28_){
_start:
{
lean_inc(v_default_28_);
return v_default_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_default_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Lean_LocalDeclKind_default_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_default_32_);
lean_dec(v_default_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim___redArg(lean_object* v_implDetail_35_){
_start:
{
lean_inc(v_implDetail_35_);
return v_implDetail_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim___redArg___boxed(lean_object* v_implDetail_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_LocalDeclKind_implDetail_elim___redArg(v_implDetail_36_);
lean_dec(v_implDetail_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_implDetail_41_){
_start:
{
lean_inc(v_implDetail_41_);
return v_implDetail_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_implDetail_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Lean_LocalDeclKind_implDetail_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_implDetail_45_);
lean_dec(v_implDetail_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim___redArg(lean_object* v_auxDecl_48_){
_start:
{
lean_inc(v_auxDecl_48_);
return v_auxDecl_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim___redArg___boxed(lean_object* v_auxDecl_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_LocalDeclKind_auxDecl_elim___redArg(v_auxDecl_49_);
lean_dec(v_auxDecl_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim(lean_object* v_motive_51_, uint8_t v_t_52_, lean_object* v_h_53_, lean_object* v_auxDecl_54_){
_start:
{
lean_inc(v_auxDecl_54_);
return v_auxDecl_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim___boxed(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_auxDecl_58_){
_start:
{
uint8_t v_t_boxed_59_; lean_object* v_res_60_; 
v_t_boxed_59_ = lean_unbox(v_t_56_);
v_res_60_ = l_Lean_LocalDeclKind_auxDecl_elim(v_motive_55_, v_t_boxed_59_, v_h_57_, v_auxDecl_58_);
lean_dec(v_auxDecl_58_);
return v_res_60_;
}
}
static uint8_t _init_l_Lean_instInhabitedLocalDeclKind_default(void){
_start:
{
uint8_t v___x_61_; 
v___x_61_ = 0;
return v___x_61_;
}
}
static uint8_t _init_l_Lean_instInhabitedLocalDeclKind(void){
_start:
{
uint8_t v___x_62_; 
v___x_62_ = 0;
return v___x_62_;
}
}
static lean_object* _init_l_Lean_instReprLocalDeclKind_repr___closed__6(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = lean_unsigned_to_nat(2u);
v___x_73_ = lean_nat_to_int(v___x_72_);
return v___x_73_;
}
}
static lean_object* _init_l_Lean_instReprLocalDeclKind_repr___closed__7(void){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = lean_unsigned_to_nat(1u);
v___x_75_ = lean_nat_to_int(v___x_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLocalDeclKind_repr(uint8_t v_x_76_, lean_object* v_prec_77_){
_start:
{
lean_object* v___y_79_; lean_object* v___y_86_; lean_object* v___y_93_; 
switch(v_x_76_)
{
case 0:
{
lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_99_ = lean_unsigned_to_nat(1024u);
v___x_100_ = lean_nat_dec_le(v___x_99_, v_prec_77_);
if (v___x_100_ == 0)
{
lean_object* v___x_101_; 
v___x_101_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__6, &l_Lean_instReprLocalDeclKind_repr___closed__6_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__6);
v___y_79_ = v___x_101_;
goto v___jp_78_;
}
else
{
lean_object* v___x_102_; 
v___x_102_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__7, &l_Lean_instReprLocalDeclKind_repr___closed__7_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__7);
v___y_79_ = v___x_102_;
goto v___jp_78_;
}
}
case 1:
{
lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_103_ = lean_unsigned_to_nat(1024u);
v___x_104_ = lean_nat_dec_le(v___x_103_, v_prec_77_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; 
v___x_105_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__6, &l_Lean_instReprLocalDeclKind_repr___closed__6_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__6);
v___y_86_ = v___x_105_;
goto v___jp_85_;
}
else
{
lean_object* v___x_106_; 
v___x_106_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__7, &l_Lean_instReprLocalDeclKind_repr___closed__7_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__7);
v___y_86_ = v___x_106_;
goto v___jp_85_;
}
}
default: 
{
lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_107_ = lean_unsigned_to_nat(1024u);
v___x_108_ = lean_nat_dec_le(v___x_107_, v_prec_77_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; 
v___x_109_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__6, &l_Lean_instReprLocalDeclKind_repr___closed__6_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__6);
v___y_93_ = v___x_109_;
goto v___jp_92_;
}
else
{
lean_object* v___x_110_; 
v___x_110_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__7, &l_Lean_instReprLocalDeclKind_repr___closed__7_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__7);
v___y_93_ = v___x_110_;
goto v___jp_92_;
}
}
}
v___jp_78_:
{
lean_object* v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_80_ = ((lean_object*)(l_Lean_instReprLocalDeclKind_repr___closed__1));
lean_inc(v___y_79_);
v___x_81_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_81_, 0, v___y_79_);
lean_ctor_set(v___x_81_, 1, v___x_80_);
v___x_82_ = 0;
v___x_83_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_83_, 0, v___x_81_);
lean_ctor_set_uint8(v___x_83_, sizeof(void*)*1, v___x_82_);
v___x_84_ = l_Repr_addAppParen(v___x_83_, v_prec_77_);
return v___x_84_;
}
v___jp_85_:
{
lean_object* v___x_87_; lean_object* v___x_88_; uint8_t v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_87_ = ((lean_object*)(l_Lean_instReprLocalDeclKind_repr___closed__3));
lean_inc(v___y_86_);
v___x_88_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_88_, 0, v___y_86_);
lean_ctor_set(v___x_88_, 1, v___x_87_);
v___x_89_ = 0;
v___x_90_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_90_, 0, v___x_88_);
lean_ctor_set_uint8(v___x_90_, sizeof(void*)*1, v___x_89_);
v___x_91_ = l_Repr_addAppParen(v___x_90_, v_prec_77_);
return v___x_91_;
}
v___jp_92_:
{
lean_object* v___x_94_; lean_object* v___x_95_; uint8_t v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_94_ = ((lean_object*)(l_Lean_instReprLocalDeclKind_repr___closed__5));
lean_inc(v___y_93_);
v___x_95_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_95_, 0, v___y_93_);
lean_ctor_set(v___x_95_, 1, v___x_94_);
v___x_96_ = 0;
v___x_97_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_97_, 0, v___x_95_);
lean_ctor_set_uint8(v___x_97_, sizeof(void*)*1, v___x_96_);
v___x_98_ = l_Repr_addAppParen(v___x_97_, v_prec_77_);
return v___x_98_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLocalDeclKind_repr___boxed(lean_object* v_x_111_, lean_object* v_prec_112_){
_start:
{
uint8_t v_x_171__boxed_113_; lean_object* v_res_114_; 
v_x_171__boxed_113_ = lean_unbox(v_x_111_);
v_res_114_ = l_Lean_instReprLocalDeclKind_repr(v_x_171__boxed_113_, v_prec_112_);
lean_dec(v_prec_112_);
return v_res_114_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDeclKind_ofNat(lean_object* v_n_117_){
_start:
{
lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_118_ = lean_unsigned_to_nat(0u);
v___x_119_ = lean_nat_dec_le(v_n_117_, v___x_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_120_ = lean_unsigned_to_nat(1u);
v___x_121_ = lean_nat_dec_le(v_n_117_, v___x_120_);
if (v___x_121_ == 0)
{
uint8_t v___x_122_; 
v___x_122_ = 2;
return v___x_122_;
}
else
{
uint8_t v___x_123_; 
v___x_123_ = 1;
return v___x_123_;
}
}
else
{
uint8_t v___x_124_; 
v___x_124_ = 0;
return v___x_124_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ofNat___boxed(lean_object* v_n_125_){
_start:
{
uint8_t v_res_126_; lean_object* v_r_127_; 
v_res_126_ = l_Lean_LocalDeclKind_ofNat(v_n_125_);
lean_dec(v_n_125_);
v_r_127_ = lean_box(v_res_126_);
return v_r_127_;
}
}
LEAN_EXPORT uint8_t l_Lean_instDecidableEqLocalDeclKind(uint8_t v_x_128_, uint8_t v_y_129_){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; uint8_t v___x_134_; 
v___x_130_ = lean_box(v_x_128_);
v___x_131_ = lean_obj_tag_nat(v___x_130_);
lean_dec(v___x_130_);
v___x_132_ = lean_box(v_y_129_);
v___x_133_ = lean_obj_tag_nat(v___x_132_);
lean_dec(v___x_132_);
v___x_134_ = lean_nat_dec_eq(v___x_131_, v___x_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_instDecidableEqLocalDeclKind___boxed(lean_object* v_x_135_, lean_object* v_y_136_){
_start:
{
uint8_t v_x_23__boxed_137_; uint8_t v_y_24__boxed_138_; uint8_t v_res_139_; lean_object* v_r_140_; 
v_x_23__boxed_137_ = lean_unbox(v_x_135_);
v_y_24__boxed_138_ = lean_unbox(v_y_136_);
v_res_139_ = l_Lean_instDecidableEqLocalDeclKind(v_x_23__boxed_137_, v_y_24__boxed_138_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableLocalDeclKind_hash(uint8_t v_x_141_){
_start:
{
switch(v_x_141_)
{
case 0:
{
uint64_t v___x_142_; 
v___x_142_ = 0ULL;
return v___x_142_;
}
case 1:
{
uint64_t v___x_143_; 
v___x_143_ = 1ULL;
return v___x_143_;
}
default: 
{
uint64_t v___x_144_; 
v___x_144_ = 2ULL;
return v___x_144_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableLocalDeclKind_hash___boxed(lean_object* v_x_145_){
_start:
{
uint8_t v_x_40__boxed_146_; uint64_t v_res_147_; lean_object* v_r_148_; 
v_x_40__boxed_146_ = lean_unbox(v_x_145_);
v_res_147_ = l_Lean_instHashableLocalDeclKind_hash(v_x_40__boxed_146_);
v_r_148_ = lean_box_uint64(v_res_147_);
return v_r_148_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDeclKind_ofBinderName(lean_object* v_binderName_151_){
_start:
{
uint8_t v___x_152_; 
v___x_152_ = l_Lean_Name_isImplementationDetail(v_binderName_151_);
if (v___x_152_ == 0)
{
uint8_t v___x_153_; 
v___x_153_ = 0;
return v___x_153_;
}
else
{
uint8_t v___x_154_; 
v___x_154_ = 1;
return v___x_154_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ofBinderName___boxed(lean_object* v_binderName_155_){
_start:
{
uint8_t v_res_156_; lean_object* v_r_157_; 
v_res_156_ = l_Lean_LocalDeclKind_ofBinderName(v_binderName_155_);
lean_dec(v_binderName_155_);
v_r_157_ = lean_box(v_res_156_);
return v_r_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorIdx___impl(lean_object* v_x_158_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = lean_obj_tag_nat(v_x_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorIdx___impl___boxed(lean_object* v_x_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Lean_LocalDecl_ctorIdx___impl(v_x_160_);
lean_dec_ref(v_x_160_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim___redArg(lean_object* v_t_162_, lean_object* v_k_163_){
_start:
{
if (lean_obj_tag(v_t_162_) == 0)
{
lean_object* v_index_164_; lean_object* v_fvarId_165_; lean_object* v_userName_166_; lean_object* v_type_167_; uint8_t v_bi_168_; uint8_t v_kind_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v_index_164_ = lean_ctor_get(v_t_162_, 0);
lean_inc(v_index_164_);
v_fvarId_165_ = lean_ctor_get(v_t_162_, 1);
lean_inc(v_fvarId_165_);
v_userName_166_ = lean_ctor_get(v_t_162_, 2);
lean_inc(v_userName_166_);
v_type_167_ = lean_ctor_get(v_t_162_, 3);
lean_inc_ref(v_type_167_);
v_bi_168_ = lean_ctor_get_uint8(v_t_162_, sizeof(void*)*4);
v_kind_169_ = lean_ctor_get_uint8(v_t_162_, sizeof(void*)*4 + 1);
lean_dec_ref_known(v_t_162_, 4);
v___x_170_ = lean_box(v_bi_168_);
v___x_171_ = lean_box(v_kind_169_);
v___x_172_ = lean_apply_6(v_k_163_, v_index_164_, v_fvarId_165_, v_userName_166_, v_type_167_, v___x_170_, v___x_171_);
return v___x_172_;
}
else
{
lean_object* v_index_173_; lean_object* v_fvarId_174_; lean_object* v_userName_175_; lean_object* v_type_176_; lean_object* v_value_177_; uint8_t v_nondep_178_; uint8_t v_kind_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v_index_173_ = lean_ctor_get(v_t_162_, 0);
lean_inc(v_index_173_);
v_fvarId_174_ = lean_ctor_get(v_t_162_, 1);
lean_inc(v_fvarId_174_);
v_userName_175_ = lean_ctor_get(v_t_162_, 2);
lean_inc(v_userName_175_);
v_type_176_ = lean_ctor_get(v_t_162_, 3);
lean_inc_ref(v_type_176_);
v_value_177_ = lean_ctor_get(v_t_162_, 4);
lean_inc_ref(v_value_177_);
v_nondep_178_ = lean_ctor_get_uint8(v_t_162_, sizeof(void*)*5);
v_kind_179_ = lean_ctor_get_uint8(v_t_162_, sizeof(void*)*5 + 1);
lean_dec_ref_known(v_t_162_, 5);
v___x_180_ = lean_box(v_nondep_178_);
v___x_181_ = lean_box(v_kind_179_);
v___x_182_ = lean_apply_7(v_k_163_, v_index_173_, v_fvarId_174_, v_userName_175_, v_type_176_, v_value_177_, v___x_180_, v___x_181_);
return v___x_182_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim(lean_object* v_motive_183_, lean_object* v_ctorIdx_184_, lean_object* v_t_185_, lean_object* v_h_186_, lean_object* v_k_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_185_, v_k_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim___boxed(lean_object* v_motive_189_, lean_object* v_ctorIdx_190_, lean_object* v_t_191_, lean_object* v_h_192_, lean_object* v_k_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Lean_LocalDecl_ctorElim(v_motive_189_, v_ctorIdx_190_, v_t_191_, v_h_192_, v_k_193_);
lean_dec(v_ctorIdx_190_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_cdecl_elim___redArg(lean_object* v_t_195_, lean_object* v_cdecl_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_195_, v_cdecl_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_cdecl_elim(lean_object* v_motive_198_, lean_object* v_t_199_, lean_object* v_h_200_, lean_object* v_cdecl_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_199_, v_cdecl_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ldecl_elim___redArg(lean_object* v_t_203_, lean_object* v_ldecl_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_203_, v_ldecl_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ldecl_elim(lean_object* v_motive_206_, lean_object* v_t_207_, lean_object* v_h_208_, lean_object* v_ldecl_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_207_, v_ldecl_209_);
return v___x_210_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl_default___closed__2(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_214_ = lean_box(0);
v___x_215_ = ((lean_object*)(l_Lean_instInhabitedLocalDecl_default___closed__1));
v___x_216_ = l_Lean_Expr_const___override(v___x_215_, v___x_214_);
return v___x_216_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl_default___closed__3(void){
_start:
{
uint8_t v___x_217_; uint8_t v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_217_ = 0;
v___x_218_ = 0;
v___x_219_ = lean_obj_once(&l_Lean_instInhabitedLocalDecl_default___closed__2, &l_Lean_instInhabitedLocalDecl_default___closed__2_once, _init_l_Lean_instInhabitedLocalDecl_default___closed__2);
v___x_220_ = lean_box(0);
v___x_221_ = lean_unsigned_to_nat(0u);
v___x_222_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_222_, 0, v___x_221_);
lean_ctor_set(v___x_222_, 1, v___x_220_);
lean_ctor_set(v___x_222_, 2, v___x_220_);
lean_ctor_set(v___x_222_, 3, v___x_219_);
lean_ctor_set_uint8(v___x_222_, sizeof(void*)*4, v___x_218_);
lean_ctor_set_uint8(v___x_222_, sizeof(void*)*4 + 1, v___x_217_);
return v___x_222_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl_default(void){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = lean_obj_once(&l_Lean_instInhabitedLocalDecl_default___closed__3, &l_Lean_instInhabitedLocalDecl_default___closed__3_once, _init_l_Lean_instInhabitedLocalDecl_default___closed__3);
return v___x_223_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl(void){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Lean_instInhabitedLocalDecl_default;
return v___x_224_;
}
}
LEAN_EXPORT lean_object* lean_mk_local_decl(lean_object* v_index_225_, lean_object* v_fvarId_226_, lean_object* v_userName_227_, lean_object* v_type_228_, uint8_t v_bi_229_){
_start:
{
uint8_t v___x_230_; lean_object* v___x_231_; 
v___x_230_ = 0;
v___x_231_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_231_, 0, v_index_225_);
lean_ctor_set(v___x_231_, 1, v_fvarId_226_);
lean_ctor_set(v___x_231_, 2, v_userName_227_);
lean_ctor_set(v___x_231_, 3, v_type_228_);
lean_ctor_set_uint8(v___x_231_, sizeof(void*)*4, v_bi_229_);
lean_ctor_set_uint8(v___x_231_, sizeof(void*)*4 + 1, v___x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLocalDeclEx___boxed(lean_object* v_index_232_, lean_object* v_fvarId_233_, lean_object* v_userName_234_, lean_object* v_type_235_, lean_object* v_bi_236_){
_start:
{
uint8_t v_bi_boxed_237_; lean_object* v_res_238_; 
v_bi_boxed_237_ = lean_unbox(v_bi_236_);
v_res_238_ = lean_mk_local_decl(v_index_232_, v_fvarId_233_, v_userName_234_, v_type_235_, v_bi_boxed_237_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* lean_mk_let_decl(lean_object* v_index_239_, lean_object* v_fvarId_240_, lean_object* v_userName_241_, lean_object* v_type_242_, lean_object* v_val_243_){
_start:
{
uint8_t v___x_244_; uint8_t v___x_245_; lean_object* v___x_246_; 
v___x_244_ = 0;
v___x_245_ = 0;
v___x_246_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v___x_246_, 0, v_index_239_);
lean_ctor_set(v___x_246_, 1, v_fvarId_240_);
lean_ctor_set(v___x_246_, 2, v_userName_241_);
lean_ctor_set(v___x_246_, 3, v_type_242_);
lean_ctor_set(v___x_246_, 4, v_val_243_);
lean_ctor_set_uint8(v___x_246_, sizeof(void*)*5, v___x_244_);
lean_ctor_set_uint8(v___x_246_, sizeof(void*)*5 + 1, v___x_245_);
return v___x_246_;
}
}
LEAN_EXPORT uint8_t lean_local_decl_binder_info(lean_object* v_x_247_){
_start:
{
if (lean_obj_tag(v_x_247_) == 0)
{
uint8_t v_bi_248_; 
v_bi_248_ = lean_ctor_get_uint8(v_x_247_, sizeof(void*)*4);
lean_dec_ref_known(v_x_247_, 4);
return v_bi_248_;
}
else
{
uint8_t v___x_249_; 
lean_dec_ref(v_x_247_);
v___x_249_ = 0;
return v___x_249_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_binderInfoEx___boxed(lean_object* v_x_250_){
_start:
{
uint8_t v_res_251_; lean_object* v_r_252_; 
v_res_251_ = lean_local_decl_binder_info(v_x_250_);
v_r_252_ = lean_box(v_res_251_);
return v_r_252_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isLet(lean_object* v_x_253_, uint8_t v_x_254_){
_start:
{
if (lean_obj_tag(v_x_253_) == 0)
{
uint8_t v___x_255_; 
v___x_255_ = 0;
return v___x_255_;
}
else
{
uint8_t v_nondep_256_; 
v_nondep_256_ = lean_ctor_get_uint8(v_x_253_, sizeof(void*)*5);
if (v_nondep_256_ == 0)
{
uint8_t v___x_257_; 
v___x_257_ = 1;
return v___x_257_;
}
else
{
return v_x_254_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isLet___boxed(lean_object* v_x_258_, lean_object* v_x_259_){
_start:
{
uint8_t v_x_53__boxed_260_; uint8_t v_res_261_; lean_object* v_r_262_; 
v_x_53__boxed_260_ = lean_unbox(v_x_259_);
v_res_261_ = l_Lean_LocalDecl_isLet(v_x_258_, v_x_53__boxed_260_);
lean_dec_ref(v_x_258_);
v_r_262_ = lean_box(v_res_261_);
return v_r_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_index(lean_object* v_x_263_){
_start:
{
lean_object* v_index_264_; 
v_index_264_ = lean_ctor_get(v_x_263_, 0);
lean_inc(v_index_264_);
return v_index_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_index___boxed(lean_object* v_x_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_LocalDecl_index(v_x_265_);
lean_dec_ref(v_x_265_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setIndex(lean_object* v_x_267_, lean_object* v_x_268_){
_start:
{
if (lean_obj_tag(v_x_267_) == 0)
{
lean_object* v_fvarId_269_; lean_object* v_userName_270_; lean_object* v_type_271_; uint8_t v_bi_272_; uint8_t v_kind_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_280_; 
v_fvarId_269_ = lean_ctor_get(v_x_267_, 1);
v_userName_270_ = lean_ctor_get(v_x_267_, 2);
v_type_271_ = lean_ctor_get(v_x_267_, 3);
v_bi_272_ = lean_ctor_get_uint8(v_x_267_, sizeof(void*)*4);
v_kind_273_ = lean_ctor_get_uint8(v_x_267_, sizeof(void*)*4 + 1);
v_isSharedCheck_280_ = !lean_is_exclusive(v_x_267_);
if (v_isSharedCheck_280_ == 0)
{
lean_object* v_unused_281_; 
v_unused_281_ = lean_ctor_get(v_x_267_, 0);
lean_dec(v_unused_281_);
v___x_275_ = v_x_267_;
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_type_271_);
lean_inc(v_userName_270_);
lean_inc(v_fvarId_269_);
lean_dec(v_x_267_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_278_; 
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 0, v_x_268_);
v___x_278_ = v___x_275_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_x_268_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_fvarId_269_);
lean_ctor_set(v_reuseFailAlloc_279_, 2, v_userName_270_);
lean_ctor_set(v_reuseFailAlloc_279_, 3, v_type_271_);
lean_ctor_set_uint8(v_reuseFailAlloc_279_, sizeof(void*)*4, v_bi_272_);
lean_ctor_set_uint8(v_reuseFailAlloc_279_, sizeof(void*)*4 + 1, v_kind_273_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
else
{
lean_object* v_fvarId_282_; lean_object* v_userName_283_; lean_object* v_type_284_; lean_object* v_value_285_; uint8_t v_nondep_286_; uint8_t v_kind_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_294_; 
v_fvarId_282_ = lean_ctor_get(v_x_267_, 1);
v_userName_283_ = lean_ctor_get(v_x_267_, 2);
v_type_284_ = lean_ctor_get(v_x_267_, 3);
v_value_285_ = lean_ctor_get(v_x_267_, 4);
v_nondep_286_ = lean_ctor_get_uint8(v_x_267_, sizeof(void*)*5);
v_kind_287_ = lean_ctor_get_uint8(v_x_267_, sizeof(void*)*5 + 1);
v_isSharedCheck_294_ = !lean_is_exclusive(v_x_267_);
if (v_isSharedCheck_294_ == 0)
{
lean_object* v_unused_295_; 
v_unused_295_ = lean_ctor_get(v_x_267_, 0);
lean_dec(v_unused_295_);
v___x_289_ = v_x_267_;
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_value_285_);
lean_inc(v_type_284_);
lean_inc(v_userName_283_);
lean_inc(v_fvarId_282_);
lean_dec(v_x_267_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v_x_268_);
v___x_292_ = v___x_289_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_x_268_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v_fvarId_282_);
lean_ctor_set(v_reuseFailAlloc_293_, 2, v_userName_283_);
lean_ctor_set(v_reuseFailAlloc_293_, 3, v_type_284_);
lean_ctor_set(v_reuseFailAlloc_293_, 4, v_value_285_);
lean_ctor_set_uint8(v_reuseFailAlloc_293_, sizeof(void*)*5, v_nondep_286_);
lean_ctor_set_uint8(v_reuseFailAlloc_293_, sizeof(void*)*5 + 1, v_kind_287_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_fvarId(lean_object* v_x_296_){
_start:
{
lean_object* v_fvarId_297_; 
v_fvarId_297_ = lean_ctor_get(v_x_296_, 1);
lean_inc(v_fvarId_297_);
return v_fvarId_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_fvarId___boxed(lean_object* v_x_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_LocalDecl_fvarId(v_x_298_);
lean_dec_ref(v_x_298_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_userName(lean_object* v_x_300_){
_start:
{
lean_object* v_userName_301_; 
v_userName_301_ = lean_ctor_get(v_x_300_, 2);
lean_inc(v_userName_301_);
return v_userName_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_userName___boxed(lean_object* v_x_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_LocalDecl_userName(v_x_302_);
lean_dec_ref(v_x_302_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_type(lean_object* v_x_304_){
_start:
{
lean_object* v_type_305_; 
v_type_305_ = lean_ctor_get(v_x_304_, 3);
lean_inc_ref(v_type_305_);
return v_type_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_type___boxed(lean_object* v_x_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_LocalDecl_type(v_x_306_);
lean_dec_ref(v_x_306_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setType(lean_object* v_x_308_, lean_object* v_x_309_){
_start:
{
if (lean_obj_tag(v_x_308_) == 0)
{
lean_object* v_index_310_; lean_object* v_fvarId_311_; lean_object* v_userName_312_; uint8_t v_bi_313_; uint8_t v_kind_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_321_; 
v_index_310_ = lean_ctor_get(v_x_308_, 0);
v_fvarId_311_ = lean_ctor_get(v_x_308_, 1);
v_userName_312_ = lean_ctor_get(v_x_308_, 2);
v_bi_313_ = lean_ctor_get_uint8(v_x_308_, sizeof(void*)*4);
v_kind_314_ = lean_ctor_get_uint8(v_x_308_, sizeof(void*)*4 + 1);
v_isSharedCheck_321_ = !lean_is_exclusive(v_x_308_);
if (v_isSharedCheck_321_ == 0)
{
lean_object* v_unused_322_; 
v_unused_322_ = lean_ctor_get(v_x_308_, 3);
lean_dec(v_unused_322_);
v___x_316_ = v_x_308_;
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_userName_312_);
lean_inc(v_fvarId_311_);
lean_inc(v_index_310_);
lean_dec(v_x_308_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 3, v_x_309_);
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_index_310_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v_fvarId_311_);
lean_ctor_set(v_reuseFailAlloc_320_, 2, v_userName_312_);
lean_ctor_set(v_reuseFailAlloc_320_, 3, v_x_309_);
lean_ctor_set_uint8(v_reuseFailAlloc_320_, sizeof(void*)*4, v_bi_313_);
lean_ctor_set_uint8(v_reuseFailAlloc_320_, sizeof(void*)*4 + 1, v_kind_314_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
else
{
lean_object* v_index_323_; lean_object* v_fvarId_324_; lean_object* v_userName_325_; lean_object* v_value_326_; uint8_t v_nondep_327_; uint8_t v_kind_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_335_; 
v_index_323_ = lean_ctor_get(v_x_308_, 0);
v_fvarId_324_ = lean_ctor_get(v_x_308_, 1);
v_userName_325_ = lean_ctor_get(v_x_308_, 2);
v_value_326_ = lean_ctor_get(v_x_308_, 4);
v_nondep_327_ = lean_ctor_get_uint8(v_x_308_, sizeof(void*)*5);
v_kind_328_ = lean_ctor_get_uint8(v_x_308_, sizeof(void*)*5 + 1);
v_isSharedCheck_335_ = !lean_is_exclusive(v_x_308_);
if (v_isSharedCheck_335_ == 0)
{
lean_object* v_unused_336_; 
v_unused_336_ = lean_ctor_get(v_x_308_, 3);
lean_dec(v_unused_336_);
v___x_330_ = v_x_308_;
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_value_326_);
lean_inc(v_userName_325_);
lean_inc(v_fvarId_324_);
lean_inc(v_index_323_);
lean_dec(v_x_308_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_333_; 
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 3, v_x_309_);
v___x_333_ = v___x_330_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_index_323_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_fvarId_324_);
lean_ctor_set(v_reuseFailAlloc_334_, 2, v_userName_325_);
lean_ctor_set(v_reuseFailAlloc_334_, 3, v_x_309_);
lean_ctor_set(v_reuseFailAlloc_334_, 4, v_value_326_);
lean_ctor_set_uint8(v_reuseFailAlloc_334_, sizeof(void*)*5, v_nondep_327_);
lean_ctor_set_uint8(v_reuseFailAlloc_334_, sizeof(void*)*5 + 1, v_kind_328_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_binderInfo(lean_object* v_x_337_){
_start:
{
if (lean_obj_tag(v_x_337_) == 0)
{
uint8_t v_bi_338_; 
v_bi_338_ = lean_ctor_get_uint8(v_x_337_, sizeof(void*)*4);
return v_bi_338_;
}
else
{
uint8_t v___x_339_; 
v___x_339_ = 0;
return v___x_339_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_binderInfo___boxed(lean_object* v_x_340_){
_start:
{
uint8_t v_res_341_; lean_object* v_r_342_; 
v_res_341_ = l_Lean_LocalDecl_binderInfo(v_x_340_);
lean_dec_ref(v_x_340_);
v_r_342_ = lean_box(v_res_341_);
return v_r_342_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_kind(lean_object* v_x_343_){
_start:
{
if (lean_obj_tag(v_x_343_) == 0)
{
uint8_t v_kind_344_; 
v_kind_344_ = lean_ctor_get_uint8(v_x_343_, sizeof(void*)*4 + 1);
return v_kind_344_;
}
else
{
uint8_t v_kind_345_; 
v_kind_345_ = lean_ctor_get_uint8(v_x_343_, sizeof(void*)*5 + 1);
return v_kind_345_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_kind___boxed(lean_object* v_x_346_){
_start:
{
uint8_t v_res_347_; lean_object* v_r_348_; 
v_res_347_ = l_Lean_LocalDecl_kind(v_x_346_);
lean_dec_ref(v_x_346_);
v_r_348_ = lean_box(v_res_347_);
return v_r_348_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object* v_d_349_){
_start:
{
uint8_t v___y_351_; 
if (lean_obj_tag(v_d_349_) == 0)
{
uint8_t v_kind_356_; 
v_kind_356_ = lean_ctor_get_uint8(v_d_349_, sizeof(void*)*4 + 1);
v___y_351_ = v_kind_356_;
goto v___jp_350_;
}
else
{
uint8_t v_kind_357_; 
v_kind_357_ = lean_ctor_get_uint8(v_d_349_, sizeof(void*)*5 + 1);
v___y_351_ = v_kind_357_;
goto v___jp_350_;
}
v___jp_350_:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; uint8_t v___x_355_; 
v___x_352_ = lean_box(v___y_351_);
v___x_353_ = lean_obj_tag_nat(v___x_352_);
lean_dec(v___x_352_);
v___x_354_ = lean_unsigned_to_nat(2u);
v___x_355_ = lean_nat_dec_eq(v___x_353_, v___x_354_);
return v___x_355_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isAuxDecl___boxed(lean_object* v_d_358_){
_start:
{
uint8_t v_res_359_; lean_object* v_r_360_; 
v_res_359_ = l_Lean_LocalDecl_isAuxDecl(v_d_358_);
lean_dec_ref(v_d_358_);
v_r_360_ = lean_box(v_res_359_);
return v_r_360_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object* v_d_361_){
_start:
{
uint8_t v___y_363_; 
if (lean_obj_tag(v_d_361_) == 0)
{
uint8_t v_kind_370_; 
v_kind_370_ = lean_ctor_get_uint8(v_d_361_, sizeof(void*)*4 + 1);
v___y_363_ = v_kind_370_;
goto v___jp_362_;
}
else
{
uint8_t v_kind_371_; 
v_kind_371_ = lean_ctor_get_uint8(v_d_361_, sizeof(void*)*5 + 1);
v___y_363_ = v_kind_371_;
goto v___jp_362_;
}
v___jp_362_:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; uint8_t v___x_367_; 
v___x_364_ = lean_box(v___y_363_);
v___x_365_ = lean_obj_tag_nat(v___x_364_);
lean_dec(v___x_364_);
v___x_366_ = lean_unsigned_to_nat(0u);
v___x_367_ = lean_nat_dec_eq(v___x_365_, v___x_366_);
if (v___x_367_ == 0)
{
uint8_t v___x_368_; 
v___x_368_ = 1;
return v___x_368_;
}
else
{
uint8_t v___x_369_; 
v___x_369_ = 0;
return v___x_369_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isImplementationDetail___boxed(lean_object* v_d_372_){
_start:
{
uint8_t v_res_373_; lean_object* v_r_374_; 
v_res_373_ = l_Lean_LocalDecl_isImplementationDetail(v_d_372_);
lean_dec_ref(v_d_372_);
v_r_374_ = lean_box(v_res_373_);
return v_r_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value_x3f(lean_object* v_x_375_, uint8_t v_x_376_){
_start:
{
if (lean_obj_tag(v_x_375_) == 1)
{
uint8_t v_nondep_377_; 
v_nondep_377_ = lean_ctor_get_uint8(v_x_375_, sizeof(void*)*5);
if (v_nondep_377_ == 0)
{
lean_object* v_value_378_; lean_object* v___x_379_; 
v_value_378_ = lean_ctor_get(v_x_375_, 4);
lean_inc_ref(v_value_378_);
v___x_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_379_, 0, v_value_378_);
return v___x_379_;
}
else
{
if (v_x_376_ == 1)
{
lean_object* v_value_380_; lean_object* v___x_381_; 
v_value_380_ = lean_ctor_get(v_x_375_, 4);
lean_inc_ref(v_value_380_);
v___x_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_381_, 0, v_value_380_);
return v___x_381_;
}
else
{
lean_object* v___x_382_; 
v___x_382_ = lean_box(0);
return v___x_382_;
}
}
}
else
{
lean_object* v___x_383_; 
v___x_383_ = lean_box(0);
return v___x_383_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value_x3f___boxed(lean_object* v_x_384_, lean_object* v_x_385_){
_start:
{
uint8_t v_x_47__boxed_386_; lean_object* v_res_387_; 
v_x_47__boxed_386_ = lean_unbox(v_x_385_);
v_res_387_ = l_Lean_LocalDecl_value_x3f(v_x_384_, v_x_47__boxed_386_);
lean_dec_ref(v_x_384_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_LocalDecl_value_spec__0(lean_object* v_msg_388_){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = l_Lean_instInhabitedExpr;
v___x_390_ = lean_panic_fn_borrowed(v___x_389_, v_msg_388_);
return v___x_390_;
}
}
static lean_object* _init_l_Lean_LocalDecl_value___closed__3(void){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_394_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__2));
v___x_395_ = lean_unsigned_to_nat(54u);
v___x_396_ = lean_unsigned_to_nat(183u);
v___x_397_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__1));
v___x_398_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_399_ = l_mkPanicMessageWithDecl(v___x_398_, v___x_397_, v___x_396_, v___x_395_, v___x_394_);
return v___x_399_;
}
}
static lean_object* _init_l_Lean_LocalDecl_value___closed__5(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_401_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__4));
v___x_402_ = lean_unsigned_to_nat(54u);
v___x_403_ = lean_unsigned_to_nat(186u);
v___x_404_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__1));
v___x_405_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_406_ = l_mkPanicMessageWithDecl(v___x_405_, v___x_404_, v___x_403_, v___x_402_, v___x_401_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value(lean_object* v_x_407_, uint8_t v_x_408_){
_start:
{
if (lean_obj_tag(v_x_407_) == 0)
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = lean_obj_once(&l_Lean_LocalDecl_value___closed__3, &l_Lean_LocalDecl_value___closed__3_once, _init_l_Lean_LocalDecl_value___closed__3);
v___x_410_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_409_);
return v___x_410_;
}
else
{
uint8_t v_nondep_411_; 
v_nondep_411_ = lean_ctor_get_uint8(v_x_407_, sizeof(void*)*5);
if (v_nondep_411_ == 0)
{
lean_object* v_value_412_; 
v_value_412_ = lean_ctor_get(v_x_407_, 4);
lean_inc_ref(v_value_412_);
return v_value_412_;
}
else
{
if (v_x_408_ == 0)
{
lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_413_ = lean_obj_once(&l_Lean_LocalDecl_value___closed__5, &l_Lean_LocalDecl_value___closed__5_once, _init_l_Lean_LocalDecl_value___closed__5);
v___x_414_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_413_);
return v___x_414_;
}
else
{
lean_object* v_value_415_; 
v_value_415_ = lean_ctor_get(v_x_407_, 4);
lean_inc_ref(v_value_415_);
return v_value_415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value___boxed(lean_object* v_x_416_, lean_object* v_x_417_){
_start:
{
uint8_t v_x_143__boxed_418_; lean_object* v_res_419_; 
v_x_143__boxed_418_ = lean_unbox(v_x_417_);
v_res_419_ = l_Lean_LocalDecl_value(v_x_416_, v_x_143__boxed_418_);
lean_dec_ref(v_x_416_);
return v_res_419_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_hasValue(lean_object* v_x_420_, uint8_t v_x_421_){
_start:
{
if (lean_obj_tag(v_x_420_) == 0)
{
uint8_t v___x_422_; 
v___x_422_ = 0;
return v___x_422_;
}
else
{
uint8_t v_nondep_423_; 
v_nondep_423_ = lean_ctor_get_uint8(v_x_420_, sizeof(void*)*5);
if (v_nondep_423_ == 0)
{
uint8_t v___x_424_; 
v___x_424_ = 1;
return v___x_424_;
}
else
{
return v_x_421_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_hasValue___boxed(lean_object* v_x_425_, lean_object* v_x_426_){
_start:
{
uint8_t v_x_72__boxed_427_; uint8_t v_res_428_; lean_object* v_r_429_; 
v_x_72__boxed_427_ = lean_unbox(v_x_426_);
v_res_428_ = l_Lean_LocalDecl_hasValue(v_x_425_, v_x_72__boxed_427_);
lean_dec_ref(v_x_425_);
v_r_429_ = lean_box(v_res_428_);
return v_r_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setValue(lean_object* v_x_430_, lean_object* v_x_431_){
_start:
{
if (lean_obj_tag(v_x_430_) == 1)
{
lean_object* v_index_432_; lean_object* v_fvarId_433_; lean_object* v_userName_434_; lean_object* v_type_435_; uint8_t v_nondep_436_; uint8_t v_kind_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_444_; 
v_index_432_ = lean_ctor_get(v_x_430_, 0);
v_fvarId_433_ = lean_ctor_get(v_x_430_, 1);
v_userName_434_ = lean_ctor_get(v_x_430_, 2);
v_type_435_ = lean_ctor_get(v_x_430_, 3);
v_nondep_436_ = lean_ctor_get_uint8(v_x_430_, sizeof(void*)*5);
v_kind_437_ = lean_ctor_get_uint8(v_x_430_, sizeof(void*)*5 + 1);
v_isSharedCheck_444_ = !lean_is_exclusive(v_x_430_);
if (v_isSharedCheck_444_ == 0)
{
lean_object* v_unused_445_; 
v_unused_445_ = lean_ctor_get(v_x_430_, 4);
lean_dec(v_unused_445_);
v___x_439_ = v_x_430_;
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_type_435_);
lean_inc(v_userName_434_);
lean_inc(v_fvarId_433_);
lean_inc(v_index_432_);
lean_dec(v_x_430_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_442_; 
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 4, v_x_431_);
v___x_442_ = v___x_439_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_index_432_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v_fvarId_433_);
lean_ctor_set(v_reuseFailAlloc_443_, 2, v_userName_434_);
lean_ctor_set(v_reuseFailAlloc_443_, 3, v_type_435_);
lean_ctor_set(v_reuseFailAlloc_443_, 4, v_x_431_);
lean_ctor_set_uint8(v_reuseFailAlloc_443_, sizeof(void*)*5, v_nondep_436_);
lean_ctor_set_uint8(v_reuseFailAlloc_443_, sizeof(void*)*5 + 1, v_kind_437_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
else
{
lean_dec_ref(v_x_431_);
return v_x_430_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setNondep(lean_object* v_x_446_, uint8_t v_x_447_){
_start:
{
if (lean_obj_tag(v_x_446_) == 1)
{
lean_object* v_index_448_; lean_object* v_fvarId_449_; lean_object* v_userName_450_; lean_object* v_type_451_; lean_object* v_value_452_; uint8_t v_kind_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_460_; 
v_index_448_ = lean_ctor_get(v_x_446_, 0);
v_fvarId_449_ = lean_ctor_get(v_x_446_, 1);
v_userName_450_ = lean_ctor_get(v_x_446_, 2);
v_type_451_ = lean_ctor_get(v_x_446_, 3);
v_value_452_ = lean_ctor_get(v_x_446_, 4);
v_kind_453_ = lean_ctor_get_uint8(v_x_446_, sizeof(void*)*5 + 1);
v_isSharedCheck_460_ = !lean_is_exclusive(v_x_446_);
if (v_isSharedCheck_460_ == 0)
{
v___x_455_ = v_x_446_;
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_value_452_);
lean_inc(v_type_451_);
lean_inc(v_userName_450_);
lean_inc(v_fvarId_449_);
lean_inc(v_index_448_);
lean_dec(v_x_446_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_458_; 
if (v_isShared_456_ == 0)
{
v___x_458_ = v___x_455_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_index_448_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v_fvarId_449_);
lean_ctor_set(v_reuseFailAlloc_459_, 2, v_userName_450_);
lean_ctor_set(v_reuseFailAlloc_459_, 3, v_type_451_);
lean_ctor_set(v_reuseFailAlloc_459_, 4, v_value_452_);
lean_ctor_set_uint8(v_reuseFailAlloc_459_, sizeof(void*)*5 + 1, v_kind_453_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
lean_ctor_set_uint8(v___x_458_, sizeof(void*)*5, v_x_447_);
return v___x_458_;
}
}
}
else
{
return v_x_446_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setNondep___boxed(lean_object* v_x_461_, lean_object* v_x_462_){
_start:
{
uint8_t v_x_23__boxed_463_; lean_object* v_res_464_; 
v_x_23__boxed_463_ = lean_unbox(v_x_462_);
v_res_464_ = l_Lean_LocalDecl_setNondep(v_x_461_, v_x_23__boxed_463_);
return v_res_464_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isNondep(lean_object* v_x_465_){
_start:
{
if (lean_obj_tag(v_x_465_) == 1)
{
uint8_t v_nondep_466_; 
v_nondep_466_ = lean_ctor_get_uint8(v_x_465_, sizeof(void*)*5);
return v_nondep_466_;
}
else
{
uint8_t v___x_467_; 
v___x_467_ = 0;
return v___x_467_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isNondep___boxed(lean_object* v_x_468_){
_start:
{
uint8_t v_res_469_; lean_object* v_r_470_; 
v_res_469_ = l_Lean_LocalDecl_isNondep(v_x_468_);
lean_dec_ref(v_x_468_);
v_r_470_ = lean_box(v_res_469_);
return v_r_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setUserName(lean_object* v_x_471_, lean_object* v_x_472_){
_start:
{
if (lean_obj_tag(v_x_471_) == 0)
{
lean_object* v_index_473_; lean_object* v_fvarId_474_; lean_object* v_type_475_; uint8_t v_bi_476_; uint8_t v_kind_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_484_; 
v_index_473_ = lean_ctor_get(v_x_471_, 0);
v_fvarId_474_ = lean_ctor_get(v_x_471_, 1);
v_type_475_ = lean_ctor_get(v_x_471_, 3);
v_bi_476_ = lean_ctor_get_uint8(v_x_471_, sizeof(void*)*4);
v_kind_477_ = lean_ctor_get_uint8(v_x_471_, sizeof(void*)*4 + 1);
v_isSharedCheck_484_ = !lean_is_exclusive(v_x_471_);
if (v_isSharedCheck_484_ == 0)
{
lean_object* v_unused_485_; 
v_unused_485_ = lean_ctor_get(v_x_471_, 2);
lean_dec(v_unused_485_);
v___x_479_ = v_x_471_;
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_type_475_);
lean_inc(v_fvarId_474_);
lean_inc(v_index_473_);
lean_dec(v_x_471_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_482_; 
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 2, v_x_472_);
v___x_482_ = v___x_479_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_index_473_);
lean_ctor_set(v_reuseFailAlloc_483_, 1, v_fvarId_474_);
lean_ctor_set(v_reuseFailAlloc_483_, 2, v_x_472_);
lean_ctor_set(v_reuseFailAlloc_483_, 3, v_type_475_);
lean_ctor_set_uint8(v_reuseFailAlloc_483_, sizeof(void*)*4, v_bi_476_);
lean_ctor_set_uint8(v_reuseFailAlloc_483_, sizeof(void*)*4 + 1, v_kind_477_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
else
{
lean_object* v_index_486_; lean_object* v_fvarId_487_; lean_object* v_type_488_; lean_object* v_value_489_; uint8_t v_nondep_490_; uint8_t v_kind_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
v_index_486_ = lean_ctor_get(v_x_471_, 0);
v_fvarId_487_ = lean_ctor_get(v_x_471_, 1);
v_type_488_ = lean_ctor_get(v_x_471_, 3);
v_value_489_ = lean_ctor_get(v_x_471_, 4);
v_nondep_490_ = lean_ctor_get_uint8(v_x_471_, sizeof(void*)*5);
v_kind_491_ = lean_ctor_get_uint8(v_x_471_, sizeof(void*)*5 + 1);
v_isSharedCheck_498_ = !lean_is_exclusive(v_x_471_);
if (v_isSharedCheck_498_ == 0)
{
lean_object* v_unused_499_; 
v_unused_499_ = lean_ctor_get(v_x_471_, 2);
lean_dec(v_unused_499_);
v___x_493_ = v_x_471_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_value_489_);
lean_inc(v_type_488_);
lean_inc(v_fvarId_487_);
lean_inc(v_index_486_);
lean_dec(v_x_471_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 2, v_x_472_);
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_index_486_);
lean_ctor_set(v_reuseFailAlloc_497_, 1, v_fvarId_487_);
lean_ctor_set(v_reuseFailAlloc_497_, 2, v_x_472_);
lean_ctor_set(v_reuseFailAlloc_497_, 3, v_type_488_);
lean_ctor_set(v_reuseFailAlloc_497_, 4, v_value_489_);
lean_ctor_set_uint8(v_reuseFailAlloc_497_, sizeof(void*)*5, v_nondep_490_);
lean_ctor_set_uint8(v_reuseFailAlloc_497_, sizeof(void*)*5 + 1, v_kind_491_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(lean_object* v_msg_500_){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = l_Lean_instInhabitedLocalDecl_default;
v___x_502_ = lean_panic_fn_borrowed(v___x_501_, v_msg_500_);
return v___x_502_;
}
}
static lean_object* _init_l_Lean_LocalDecl_setBinderInfo___closed__2(void){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_505_ = ((lean_object*)(l_Lean_LocalDecl_setBinderInfo___closed__1));
v___x_506_ = lean_unsigned_to_nat(38u);
v___x_507_ = lean_unsigned_to_nat(248u);
v___x_508_ = ((lean_object*)(l_Lean_LocalDecl_setBinderInfo___closed__0));
v___x_509_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_510_ = l_mkPanicMessageWithDecl(v___x_509_, v___x_508_, v___x_507_, v___x_506_, v___x_505_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setBinderInfo(lean_object* v_x_511_, uint8_t v_x_512_){
_start:
{
if (lean_obj_tag(v_x_511_) == 0)
{
lean_object* v_index_513_; lean_object* v_fvarId_514_; lean_object* v_userName_515_; lean_object* v_type_516_; uint8_t v_kind_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_524_; 
v_index_513_ = lean_ctor_get(v_x_511_, 0);
v_fvarId_514_ = lean_ctor_get(v_x_511_, 1);
v_userName_515_ = lean_ctor_get(v_x_511_, 2);
v_type_516_ = lean_ctor_get(v_x_511_, 3);
v_kind_517_ = lean_ctor_get_uint8(v_x_511_, sizeof(void*)*4 + 1);
v_isSharedCheck_524_ = !lean_is_exclusive(v_x_511_);
if (v_isSharedCheck_524_ == 0)
{
v___x_519_ = v_x_511_;
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_type_516_);
lean_inc(v_userName_515_);
lean_inc(v_fvarId_514_);
lean_inc(v_index_513_);
lean_dec(v_x_511_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_522_; 
if (v_isShared_520_ == 0)
{
v___x_522_ = v___x_519_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_index_513_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v_fvarId_514_);
lean_ctor_set(v_reuseFailAlloc_523_, 2, v_userName_515_);
lean_ctor_set(v_reuseFailAlloc_523_, 3, v_type_516_);
lean_ctor_set_uint8(v_reuseFailAlloc_523_, sizeof(void*)*4 + 1, v_kind_517_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_ctor_set_uint8(v___x_522_, sizeof(void*)*4, v_x_512_);
return v___x_522_;
}
}
}
else
{
lean_object* v___x_525_; lean_object* v___x_526_; 
lean_dec_ref_known(v_x_511_, 5);
v___x_525_ = lean_obj_once(&l_Lean_LocalDecl_setBinderInfo___closed__2, &l_Lean_LocalDecl_setBinderInfo___closed__2_once, _init_l_Lean_LocalDecl_setBinderInfo___closed__2);
v___x_526_ = l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(v___x_525_);
return v___x_526_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setBinderInfo___boxed(lean_object* v_x_527_, lean_object* v_x_528_){
_start:
{
uint8_t v_x_84__boxed_529_; lean_object* v_res_530_; 
v_x_84__boxed_529_ = lean_unbox(v_x_528_);
v_res_530_ = l_Lean_LocalDecl_setBinderInfo(v_x_527_, v_x_84__boxed_529_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_toExpr(lean_object* v_decl_531_){
_start:
{
lean_object* v_fvarId_532_; lean_object* v___x_533_; 
v_fvarId_532_ = lean_ctor_get(v_decl_531_, 1);
lean_inc(v_fvarId_532_);
lean_dec_ref(v_decl_531_);
v___x_533_ = l_Lean_mkFVar(v_fvarId_532_);
return v___x_533_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_hasExprMVar(lean_object* v_x_534_){
_start:
{
if (lean_obj_tag(v_x_534_) == 0)
{
lean_object* v_type_535_; uint8_t v___x_536_; 
v_type_535_ = lean_ctor_get(v_x_534_, 3);
v___x_536_ = l_Lean_Expr_hasExprMVar(v_type_535_);
return v___x_536_;
}
else
{
lean_object* v_type_537_; lean_object* v_value_538_; uint8_t v___x_539_; 
v_type_537_ = lean_ctor_get(v_x_534_, 3);
v_value_538_ = lean_ctor_get(v_x_534_, 4);
v___x_539_ = l_Lean_Expr_hasExprMVar(v_type_537_);
if (v___x_539_ == 0)
{
uint8_t v___x_540_; 
v___x_540_ = l_Lean_Expr_hasExprMVar(v_value_538_);
return v___x_540_;
}
else
{
return v___x_539_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_hasExprMVar___boxed(lean_object* v_x_541_){
_start:
{
uint8_t v_res_542_; lean_object* v_r_543_; 
v_res_542_ = l_Lean_LocalDecl_hasExprMVar(v_x_541_);
lean_dec_ref(v_x_541_);
v_r_543_ = lean_box(v_res_542_);
return v_r_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setKind(lean_object* v_x_544_, uint8_t v_x_545_){
_start:
{
if (lean_obj_tag(v_x_544_) == 0)
{
lean_object* v_index_546_; lean_object* v_fvarId_547_; lean_object* v_userName_548_; lean_object* v_type_549_; uint8_t v_bi_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_557_; 
v_index_546_ = lean_ctor_get(v_x_544_, 0);
v_fvarId_547_ = lean_ctor_get(v_x_544_, 1);
v_userName_548_ = lean_ctor_get(v_x_544_, 2);
v_type_549_ = lean_ctor_get(v_x_544_, 3);
v_bi_550_ = lean_ctor_get_uint8(v_x_544_, sizeof(void*)*4);
v_isSharedCheck_557_ = !lean_is_exclusive(v_x_544_);
if (v_isSharedCheck_557_ == 0)
{
v___x_552_ = v_x_544_;
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_type_549_);
lean_inc(v_userName_548_);
lean_inc(v_fvarId_547_);
lean_inc(v_index_546_);
lean_dec(v_x_544_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_553_ == 0)
{
v___x_555_ = v___x_552_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_index_546_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v_fvarId_547_);
lean_ctor_set(v_reuseFailAlloc_556_, 2, v_userName_548_);
lean_ctor_set(v_reuseFailAlloc_556_, 3, v_type_549_);
lean_ctor_set_uint8(v_reuseFailAlloc_556_, sizeof(void*)*4, v_bi_550_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
lean_ctor_set_uint8(v___x_555_, sizeof(void*)*4 + 1, v_x_545_);
return v___x_555_;
}
}
}
else
{
lean_object* v_index_558_; lean_object* v_fvarId_559_; lean_object* v_userName_560_; lean_object* v_type_561_; lean_object* v_value_562_; uint8_t v_nondep_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_570_; 
v_index_558_ = lean_ctor_get(v_x_544_, 0);
v_fvarId_559_ = lean_ctor_get(v_x_544_, 1);
v_userName_560_ = lean_ctor_get(v_x_544_, 2);
v_type_561_ = lean_ctor_get(v_x_544_, 3);
v_value_562_ = lean_ctor_get(v_x_544_, 4);
v_nondep_563_ = lean_ctor_get_uint8(v_x_544_, sizeof(void*)*5);
v_isSharedCheck_570_ = !lean_is_exclusive(v_x_544_);
if (v_isSharedCheck_570_ == 0)
{
v___x_565_ = v_x_544_;
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_value_562_);
lean_inc(v_type_561_);
lean_inc(v_userName_560_);
lean_inc(v_fvarId_559_);
lean_inc(v_index_558_);
lean_dec(v_x_544_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
if (v_isShared_566_ == 0)
{
v___x_568_ = v___x_565_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_index_558_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v_fvarId_559_);
lean_ctor_set(v_reuseFailAlloc_569_, 2, v_userName_560_);
lean_ctor_set(v_reuseFailAlloc_569_, 3, v_type_561_);
lean_ctor_set(v_reuseFailAlloc_569_, 4, v_value_562_);
lean_ctor_set_uint8(v_reuseFailAlloc_569_, sizeof(void*)*5, v_nondep_563_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
lean_ctor_set_uint8(v___x_568_, sizeof(void*)*5 + 1, v_x_545_);
return v___x_568_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setKind___boxed(lean_object* v_x_571_, lean_object* v_x_572_){
_start:
{
uint8_t v_x_31__boxed_573_; lean_object* v_res_574_; 
v_x_31__boxed_573_ = lean_unbox(v_x_572_);
v_res_574_ = l_Lean_LocalDecl_setKind(v_x_571_, v_x_31__boxed_573_);
return v_res_574_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__0(void){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_575_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__1(void){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__0, &l_Lean_instInhabitedLocalContext_default___closed__0_once, _init_l_Lean_instInhabitedLocalContext_default___closed__0);
v___x_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
return v___x_577_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__2(void){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_578_ = lean_unsigned_to_nat(32u);
v___x_579_ = lean_mk_empty_array_with_capacity(v___x_578_);
v___x_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
return v___x_580_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__3(void){
_start:
{
size_t v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_581_ = ((size_t)5ULL);
v___x_582_ = lean_unsigned_to_nat(0u);
v___x_583_ = lean_unsigned_to_nat(32u);
v___x_584_ = lean_mk_empty_array_with_capacity(v___x_583_);
v___x_585_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__2, &l_Lean_instInhabitedLocalContext_default___closed__2_once, _init_l_Lean_instInhabitedLocalContext_default___closed__2);
v___x_586_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_586_, 0, v___x_585_);
lean_ctor_set(v___x_586_, 1, v___x_584_);
lean_ctor_set(v___x_586_, 2, v___x_582_);
lean_ctor_set(v___x_586_, 3, v___x_582_);
lean_ctor_set_usize(v___x_586_, 4, v___x_581_);
return v___x_586_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__4(void){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_587_ = lean_box(1);
v___x_588_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__3, &l_Lean_instInhabitedLocalContext_default___closed__3_once, _init_l_Lean_instInhabitedLocalContext_default___closed__3);
v___x_589_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__1, &l_Lean_instInhabitedLocalContext_default___closed__1_once, _init_l_Lean_instInhabitedLocalContext_default___closed__1);
v___x_590_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
lean_ctor_set(v___x_590_, 1, v___x_588_);
lean_ctor_set(v___x_590_, 2, v___x_587_);
return v___x_590_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default(void){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__4, &l_Lean_instInhabitedLocalContext_default___closed__4_once, _init_l_Lean_instInhabitedLocalContext_default___closed__4);
return v___x_591_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext(void){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Lean_instInhabitedLocalContext_default;
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkEmpty___redArg(){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_594_ = lean_unsigned_to_nat(32u);
v___x_595_ = lean_mk_empty_array_with_capacity(v___x_594_);
lean_dec_ref(v___x_595_);
v___x_596_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__4, &l_Lean_instInhabitedLocalContext_default___closed__4_once, _init_l_Lean_instInhabitedLocalContext_default___closed__4);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkEmpty___redArg___boxed(lean_object* v___dummy_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lean_LocalContext_mkEmpty___redArg();
return v_res_598_;
}
}
static lean_object* _init_l_Lean_LocalContext_mkEmpty___closed__0(void){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Lean_LocalContext_mkEmpty___redArg();
return v___x_599_;
}
}
LEAN_EXPORT lean_object* lean_mk_empty_local_ctx(lean_object* v_x_600_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = lean_obj_once(&l_Lean_LocalContext_mkEmpty___closed__0, &l_Lean_LocalContext_mkEmpty___closed__0_once, _init_l_Lean_LocalContext_mkEmpty___closed__0);
return v___x_601_;
}
}
static lean_object* _init_l_Lean_LocalContext_empty(void){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_602_ = lean_unsigned_to_nat(32u);
v___x_603_ = lean_mk_empty_array_with_capacity(v___x_602_);
lean_dec_ref(v___x_603_);
v___x_604_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__4, &l_Lean_instInhabitedLocalContext_default___closed__4_once, _init_l_Lean_instInhabitedLocalContext_default___closed__4);
return v___x_604_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg(lean_object* v_x_605_){
_start:
{
uint8_t v___x_606_; 
v___x_606_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg___boxed(lean_object* v_x_607_){
_start:
{
uint8_t v_res_608_; lean_object* v_r_609_; 
v_res_608_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg(v_x_607_);
lean_dec_ref(v_x_607_);
v_r_609_ = lean_box(v_res_608_);
return v_r_609_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0(lean_object* v_00_u03b2_610_, lean_object* v_x_611_){
_start:
{
uint8_t v___x_612_; 
v___x_612_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___boxed(lean_object* v_00_u03b2_613_, lean_object* v_x_614_){
_start:
{
uint8_t v_res_615_; lean_object* v_r_616_; 
v_res_615_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0(v_00_u03b2_613_, v_x_614_);
lean_dec_ref(v_x_614_);
v_r_616_ = lean_box(v_res_615_);
return v_r_616_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_isEmpty(lean_object* v_lctx_617_){
_start:
{
lean_object* v_fvarIdToDecl_618_; uint8_t v___x_619_; 
v_fvarIdToDecl_618_ = lean_ctor_get(v_lctx_617_, 0);
v___x_619_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_fvarIdToDecl_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_isEmpty___boxed(lean_object* v_lctx_620_){
_start:
{
uint8_t v_res_621_; lean_object* v_r_622_; 
v_res_621_ = l_Lean_LocalContext_isEmpty(v_lctx_620_);
lean_dec_ref(v_lctx_620_);
v_r_622_ = lean_box(v_res_621_);
return v_r_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_623_, lean_object* v_x_624_, lean_object* v_x_625_, lean_object* v_x_626_){
_start:
{
lean_object* v_ks_627_; lean_object* v_vs_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_652_; 
v_ks_627_ = lean_ctor_get(v_x_623_, 0);
v_vs_628_ = lean_ctor_get(v_x_623_, 1);
v_isSharedCheck_652_ = !lean_is_exclusive(v_x_623_);
if (v_isSharedCheck_652_ == 0)
{
v___x_630_ = v_x_623_;
v_isShared_631_ = v_isSharedCheck_652_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_vs_628_);
lean_inc(v_ks_627_);
lean_dec(v_x_623_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_652_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_632_; uint8_t v___x_633_; 
v___x_632_ = lean_array_get_size(v_ks_627_);
v___x_633_ = lean_nat_dec_lt(v_x_624_, v___x_632_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_637_; 
lean_dec(v_x_624_);
v___x_634_ = lean_array_push(v_ks_627_, v_x_625_);
v___x_635_ = lean_array_push(v_vs_628_, v_x_626_);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 1, v___x_635_);
lean_ctor_set(v___x_630_, 0, v___x_634_);
v___x_637_ = v___x_630_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v___x_635_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
else
{
lean_object* v_k_x27_639_; uint8_t v___x_640_; 
v_k_x27_639_ = lean_array_fget_borrowed(v_ks_627_, v_x_624_);
v___x_640_ = l_Lean_instBEqFVarId_beq(v_x_625_, v_k_x27_639_);
if (v___x_640_ == 0)
{
lean_object* v___x_642_; 
if (v_isShared_631_ == 0)
{
v___x_642_ = v___x_630_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_ks_627_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v_vs_628_);
v___x_642_ = v_reuseFailAlloc_646_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = lean_unsigned_to_nat(1u);
v___x_644_ = lean_nat_add(v_x_624_, v___x_643_);
lean_dec(v_x_624_);
v_x_623_ = v___x_642_;
v_x_624_ = v___x_644_;
goto _start;
}
}
else
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_650_; 
v___x_647_ = lean_array_fset(v_ks_627_, v_x_624_, v_x_625_);
v___x_648_ = lean_array_fset(v_vs_628_, v_x_624_, v_x_626_);
lean_dec(v_x_624_);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 1, v___x_648_);
lean_ctor_set(v___x_630_, 0, v___x_647_);
v___x_650_ = v___x_630_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_647_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v___x_648_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1___redArg(lean_object* v_n_653_, lean_object* v_k_654_, lean_object* v_v_655_){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = lean_unsigned_to_nat(0u);
v___x_657_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2___redArg(v_n_653_, v___x_656_, v_k_654_, v_v_655_);
return v___x_657_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(lean_object* v_x_659_, size_t v_x_660_, size_t v_x_661_, lean_object* v_x_662_, lean_object* v_x_663_){
_start:
{
if (lean_obj_tag(v_x_659_) == 0)
{
lean_object* v_es_664_; size_t v___x_665_; size_t v___x_666_; lean_object* v_j_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v_es_664_ = lean_ctor_get(v_x_659_, 0);
v___x_665_ = ((size_t)31ULL);
v___x_666_ = lean_usize_land(v_x_660_, v___x_665_);
v_j_667_ = lean_usize_to_nat(v___x_666_);
v___x_668_ = lean_array_get_size(v_es_664_);
v___x_669_ = lean_nat_dec_lt(v_j_667_, v___x_668_);
if (v___x_669_ == 0)
{
lean_dec(v_j_667_);
lean_dec(v_x_663_);
lean_dec(v_x_662_);
return v_x_659_;
}
else
{
lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_708_; 
lean_inc_ref(v_es_664_);
v_isSharedCheck_708_ = !lean_is_exclusive(v_x_659_);
if (v_isSharedCheck_708_ == 0)
{
lean_object* v_unused_709_; 
v_unused_709_ = lean_ctor_get(v_x_659_, 0);
lean_dec(v_unused_709_);
v___x_671_ = v_x_659_;
v_isShared_672_ = v_isSharedCheck_708_;
goto v_resetjp_670_;
}
else
{
lean_dec(v_x_659_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_708_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v_v_673_; lean_object* v___x_674_; lean_object* v_xs_x27_675_; lean_object* v___y_677_; 
v_v_673_ = lean_array_fget(v_es_664_, v_j_667_);
v___x_674_ = lean_box(0);
v_xs_x27_675_ = lean_array_fset(v_es_664_, v_j_667_, v___x_674_);
switch(lean_obj_tag(v_v_673_))
{
case 0:
{
lean_object* v_key_682_; lean_object* v_val_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_693_; 
v_key_682_ = lean_ctor_get(v_v_673_, 0);
v_val_683_ = lean_ctor_get(v_v_673_, 1);
v_isSharedCheck_693_ = !lean_is_exclusive(v_v_673_);
if (v_isSharedCheck_693_ == 0)
{
v___x_685_ = v_v_673_;
v_isShared_686_ = v_isSharedCheck_693_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_val_683_);
lean_inc(v_key_682_);
lean_dec(v_v_673_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_693_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
uint8_t v___x_687_; 
v___x_687_ = l_Lean_instBEqFVarId_beq(v_x_662_, v_key_682_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; lean_object* v___x_689_; 
lean_del_object(v___x_685_);
v___x_688_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_682_, v_val_683_, v_x_662_, v_x_663_);
v___x_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
v___y_677_ = v___x_689_;
goto v___jp_676_;
}
else
{
lean_object* v___x_691_; 
lean_dec(v_val_683_);
lean_dec(v_key_682_);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 1, v_x_663_);
lean_ctor_set(v___x_685_, 0, v_x_662_);
v___x_691_ = v___x_685_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_x_662_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_x_663_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
v___y_677_ = v___x_691_;
goto v___jp_676_;
}
}
}
}
case 1:
{
lean_object* v_node_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_706_; 
v_node_694_ = lean_ctor_get(v_v_673_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v_v_673_);
if (v_isSharedCheck_706_ == 0)
{
v___x_696_ = v_v_673_;
v_isShared_697_ = v_isSharedCheck_706_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_node_694_);
lean_dec(v_v_673_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_706_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
size_t v___x_698_; size_t v___x_699_; size_t v___x_700_; size_t v___x_701_; lean_object* v___x_702_; lean_object* v___x_704_; 
v___x_698_ = ((size_t)5ULL);
v___x_699_ = lean_usize_shift_right(v_x_660_, v___x_698_);
v___x_700_ = ((size_t)1ULL);
v___x_701_ = lean_usize_add(v_x_661_, v___x_700_);
v___x_702_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_node_694_, v___x_699_, v___x_701_, v_x_662_, v_x_663_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 0, v___x_702_);
v___x_704_ = v___x_696_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_702_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
v___y_677_ = v___x_704_;
goto v___jp_676_;
}
}
}
default: 
{
lean_object* v___x_707_; 
v___x_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_707_, 0, v_x_662_);
lean_ctor_set(v___x_707_, 1, v_x_663_);
v___y_677_ = v___x_707_;
goto v___jp_676_;
}
}
v___jp_676_:
{
lean_object* v___x_678_; lean_object* v___x_680_; 
v___x_678_ = lean_array_fset(v_xs_x27_675_, v_j_667_, v___y_677_);
lean_dec(v_j_667_);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_678_);
v___x_680_ = v___x_671_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_678_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
}
else
{
lean_object* v_ks_710_; lean_object* v_vs_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_729_; 
v_ks_710_ = lean_ctor_get(v_x_659_, 0);
v_vs_711_ = lean_ctor_get(v_x_659_, 1);
v_isSharedCheck_729_ = !lean_is_exclusive(v_x_659_);
if (v_isSharedCheck_729_ == 0)
{
v___x_713_ = v_x_659_;
v_isShared_714_ = v_isSharedCheck_729_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_vs_711_);
lean_inc(v_ks_710_);
lean_dec(v_x_659_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_729_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
if (v_isShared_714_ == 0)
{
v___x_716_ = v___x_713_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_ks_710_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v_vs_711_);
v___x_716_ = v_reuseFailAlloc_728_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_object* v_newNode_717_; size_t v___x_718_; uint8_t v___x_719_; 
v_newNode_717_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1___redArg(v___x_716_, v_x_662_, v_x_663_);
v___x_718_ = ((size_t)7ULL);
v___x_719_ = lean_usize_dec_le(v___x_718_, v_x_661_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_720_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_717_);
v___x_721_ = lean_unsigned_to_nat(4u);
v___x_722_ = lean_nat_dec_lt(v___x_720_, v___x_721_);
lean_dec(v___x_720_);
if (v___x_722_ == 0)
{
lean_object* v_ks_723_; lean_object* v_vs_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v_ks_723_ = lean_ctor_get(v_newNode_717_, 0);
lean_inc_ref(v_ks_723_);
v_vs_724_ = lean_ctor_get(v_newNode_717_, 1);
lean_inc_ref(v_vs_724_);
lean_dec_ref(v_newNode_717_);
v___x_725_ = lean_unsigned_to_nat(0u);
v___x_726_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0);
v___x_727_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(v_x_661_, v_ks_723_, v_vs_724_, v___x_725_, v___x_726_);
lean_dec_ref(v_vs_724_);
lean_dec_ref(v_ks_723_);
return v___x_727_;
}
else
{
return v_newNode_717_;
}
}
else
{
return v_newNode_717_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(size_t v_depth_730_, lean_object* v_keys_731_, lean_object* v_vals_732_, lean_object* v_i_733_, lean_object* v_entries_734_){
_start:
{
lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_735_ = lean_array_get_size(v_keys_731_);
v___x_736_ = lean_nat_dec_lt(v_i_733_, v___x_735_);
if (v___x_736_ == 0)
{
lean_dec(v_i_733_);
return v_entries_734_;
}
else
{
lean_object* v_k_737_; lean_object* v_v_738_; uint64_t v___x_739_; size_t v_h_740_; size_t v___x_741_; lean_object* v___x_742_; size_t v___x_743_; size_t v___x_744_; size_t v___x_745_; size_t v_h_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v_k_737_ = lean_array_fget_borrowed(v_keys_731_, v_i_733_);
v_v_738_ = lean_array_fget_borrowed(v_vals_732_, v_i_733_);
v___x_739_ = l_Lean_instHashableFVarId_hash(v_k_737_);
v_h_740_ = lean_uint64_to_usize(v___x_739_);
v___x_741_ = ((size_t)5ULL);
v___x_742_ = lean_unsigned_to_nat(1u);
v___x_743_ = ((size_t)1ULL);
v___x_744_ = lean_usize_sub(v_depth_730_, v___x_743_);
v___x_745_ = lean_usize_mul(v___x_741_, v___x_744_);
v_h_746_ = lean_usize_shift_right(v_h_740_, v___x_745_);
v___x_747_ = lean_nat_add(v_i_733_, v___x_742_);
lean_dec(v_i_733_);
lean_inc(v_v_738_);
lean_inc(v_k_737_);
v___x_748_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_entries_734_, v_h_746_, v_depth_730_, v_k_737_, v_v_738_);
v_i_733_ = v___x_747_;
v_entries_734_ = v___x_748_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_750_, lean_object* v_keys_751_, lean_object* v_vals_752_, lean_object* v_i_753_, lean_object* v_entries_754_){
_start:
{
size_t v_depth_boxed_755_; lean_object* v_res_756_; 
v_depth_boxed_755_ = lean_unbox_usize(v_depth_750_);
lean_dec(v_depth_750_);
v_res_756_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(v_depth_boxed_755_, v_keys_751_, v_vals_752_, v_i_753_, v_entries_754_);
lean_dec_ref(v_vals_752_);
lean_dec_ref(v_keys_751_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___boxed(lean_object* v_x_757_, lean_object* v_x_758_, lean_object* v_x_759_, lean_object* v_x_760_, lean_object* v_x_761_){
_start:
{
size_t v_x_365__boxed_762_; size_t v_x_366__boxed_763_; lean_object* v_res_764_; 
v_x_365__boxed_762_ = lean_unbox_usize(v_x_758_);
lean_dec(v_x_758_);
v_x_366__boxed_763_ = lean_unbox_usize(v_x_759_);
lean_dec(v_x_759_);
v_res_764_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_x_757_, v_x_365__boxed_762_, v_x_366__boxed_763_, v_x_760_, v_x_761_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(lean_object* v_x_765_, lean_object* v_x_766_, lean_object* v_x_767_){
_start:
{
uint64_t v___x_768_; size_t v___x_769_; size_t v___x_770_; lean_object* v___x_771_; 
v___x_768_ = l_Lean_instHashableFVarId_hash(v_x_766_);
v___x_769_ = lean_uint64_to_usize(v___x_768_);
v___x_770_ = ((size_t)1ULL);
v___x_771_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_x_765_, v___x_769_, v___x_770_, v_x_766_, v_x_767_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object* v_lctx_772_, lean_object* v_fvarId_773_, lean_object* v_userName_774_, lean_object* v_type_775_, uint8_t v_bi_776_, uint8_t v_kind_777_){
_start:
{
lean_object* v_decls_778_; lean_object* v_fvarIdToDecl_779_; lean_object* v_auxDeclToFullName_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_792_; 
v_decls_778_ = lean_ctor_get(v_lctx_772_, 1);
v_fvarIdToDecl_779_ = lean_ctor_get(v_lctx_772_, 0);
v_auxDeclToFullName_780_ = lean_ctor_get(v_lctx_772_, 2);
v_isSharedCheck_792_ = !lean_is_exclusive(v_lctx_772_);
if (v_isSharedCheck_792_ == 0)
{
v___x_782_ = v_lctx_772_;
v_isShared_783_ = v_isSharedCheck_792_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_auxDeclToFullName_780_);
lean_inc(v_decls_778_);
lean_inc(v_fvarIdToDecl_779_);
lean_dec(v_lctx_772_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_792_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v_size_784_; lean_object* v_decl_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_790_; 
v_size_784_ = lean_ctor_get(v_decls_778_, 2);
lean_inc(v_fvarId_773_);
lean_inc(v_size_784_);
v_decl_785_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_decl_785_, 0, v_size_784_);
lean_ctor_set(v_decl_785_, 1, v_fvarId_773_);
lean_ctor_set(v_decl_785_, 2, v_userName_774_);
lean_ctor_set(v_decl_785_, 3, v_type_775_);
lean_ctor_set_uint8(v_decl_785_, sizeof(void*)*4, v_bi_776_);
lean_ctor_set_uint8(v_decl_785_, sizeof(void*)*4 + 1, v_kind_777_);
lean_inc_ref(v_decl_785_);
v___x_786_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_779_, v_fvarId_773_, v_decl_785_);
v___x_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_787_, 0, v_decl_785_);
v___x_788_ = l_Lean_PersistentArray_push___redArg(v_decls_778_, v___x_787_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 1, v___x_788_);
lean_ctor_set(v___x_782_, 0, v___x_786_);
v___x_790_ = v___x_782_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_786_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_791_, 2, v_auxDeclToFullName_780_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLocalDecl___boxed(lean_object* v_lctx_793_, lean_object* v_fvarId_794_, lean_object* v_userName_795_, lean_object* v_type_796_, lean_object* v_bi_797_, lean_object* v_kind_798_){
_start:
{
uint8_t v_bi_boxed_799_; uint8_t v_kind_boxed_800_; lean_object* v_res_801_; 
v_bi_boxed_799_ = lean_unbox(v_bi_797_);
v_kind_boxed_800_ = lean_unbox(v_kind_798_);
v_res_801_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_793_, v_fvarId_794_, v_userName_795_, v_type_796_, v_bi_boxed_799_, v_kind_boxed_800_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0(lean_object* v_00_u03b2_802_, lean_object* v_x_803_, lean_object* v_x_804_, lean_object* v_x_805_){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_x_803_, v_x_804_, v_x_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0(lean_object* v_00_u03b2_807_, lean_object* v_x_808_, size_t v_x_809_, size_t v_x_810_, lean_object* v_x_811_, lean_object* v_x_812_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_x_808_, v_x_809_, v_x_810_, v_x_811_, v_x_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_814_, lean_object* v_x_815_, lean_object* v_x_816_, lean_object* v_x_817_, lean_object* v_x_818_, lean_object* v_x_819_){
_start:
{
size_t v_x_565__boxed_820_; size_t v_x_566__boxed_821_; lean_object* v_res_822_; 
v_x_565__boxed_820_ = lean_unbox_usize(v_x_816_);
lean_dec(v_x_816_);
v_x_566__boxed_821_ = lean_unbox_usize(v_x_817_);
lean_dec(v_x_817_);
v_res_822_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0(v_00_u03b2_814_, v_x_815_, v_x_565__boxed_820_, v_x_566__boxed_821_, v_x_818_, v_x_819_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_823_, lean_object* v_n_824_, lean_object* v_k_825_, lean_object* v_v_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1___redArg(v_n_824_, v_k_825_, v_v_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_828_, size_t v_depth_829_, lean_object* v_keys_830_, lean_object* v_vals_831_, lean_object* v_heq_832_, lean_object* v_i_833_, lean_object* v_entries_834_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(v_depth_829_, v_keys_830_, v_vals_831_, v_i_833_, v_entries_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_836_, lean_object* v_depth_837_, lean_object* v_keys_838_, lean_object* v_vals_839_, lean_object* v_heq_840_, lean_object* v_i_841_, lean_object* v_entries_842_){
_start:
{
size_t v_depth_boxed_843_; lean_object* v_res_844_; 
v_depth_boxed_843_ = lean_unbox_usize(v_depth_837_);
lean_dec(v_depth_837_);
v_res_844_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2(v_00_u03b2_836_, v_depth_boxed_843_, v_keys_838_, v_vals_839_, v_heq_840_, v_i_841_, v_entries_842_);
lean_dec_ref(v_vals_839_);
lean_dec_ref(v_keys_838_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_845_, lean_object* v_x_846_, lean_object* v_x_847_, lean_object* v_x_848_, lean_object* v_x_849_){
_start:
{
lean_object* v___x_850_; 
v___x_850_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2___redArg(v_x_846_, v_x_847_, v_x_848_, v_x_849_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_mk_local_decl(lean_object* v_lctx_851_, lean_object* v_fvarId_852_, lean_object* v_userName_853_, lean_object* v_type_854_, uint8_t v_bi_855_){
_start:
{
uint8_t v___x_856_; lean_object* v___x_857_; 
v___x_856_ = 0;
v___x_857_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_851_, v_fvarId_852_, v_userName_853_, v_type_854_, v_bi_855_, v___x_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_mkLocalDeclExported___boxed(lean_object* v_lctx_858_, lean_object* v_fvarId_859_, lean_object* v_userName_860_, lean_object* v_type_861_, lean_object* v_bi_862_){
_start:
{
uint8_t v_bi_boxed_863_; lean_object* v_res_864_; 
v_bi_boxed_863_ = lean_unbox(v_bi_862_);
v_res_864_ = lean_local_ctx_mk_local_decl(v_lctx_858_, v_fvarId_859_, v_userName_860_, v_type_861_, v_bi_boxed_863_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLetDecl(lean_object* v_lctx_865_, lean_object* v_fvarId_866_, lean_object* v_userName_867_, lean_object* v_type_868_, lean_object* v_value_869_, uint8_t v_nondep_870_, uint8_t v_kind_871_){
_start:
{
lean_object* v_decls_872_; lean_object* v_fvarIdToDecl_873_; lean_object* v_auxDeclToFullName_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_886_; 
v_decls_872_ = lean_ctor_get(v_lctx_865_, 1);
v_fvarIdToDecl_873_ = lean_ctor_get(v_lctx_865_, 0);
v_auxDeclToFullName_874_ = lean_ctor_get(v_lctx_865_, 2);
v_isSharedCheck_886_ = !lean_is_exclusive(v_lctx_865_);
if (v_isSharedCheck_886_ == 0)
{
v___x_876_ = v_lctx_865_;
v_isShared_877_ = v_isSharedCheck_886_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_auxDeclToFullName_874_);
lean_inc(v_decls_872_);
lean_inc(v_fvarIdToDecl_873_);
lean_dec(v_lctx_865_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_886_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v_size_878_; lean_object* v_decl_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_884_; 
v_size_878_ = lean_ctor_get(v_decls_872_, 2);
lean_inc(v_fvarId_866_);
lean_inc(v_size_878_);
v_decl_879_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_decl_879_, 0, v_size_878_);
lean_ctor_set(v_decl_879_, 1, v_fvarId_866_);
lean_ctor_set(v_decl_879_, 2, v_userName_867_);
lean_ctor_set(v_decl_879_, 3, v_type_868_);
lean_ctor_set(v_decl_879_, 4, v_value_869_);
lean_ctor_set_uint8(v_decl_879_, sizeof(void*)*5, v_nondep_870_);
lean_ctor_set_uint8(v_decl_879_, sizeof(void*)*5 + 1, v_kind_871_);
lean_inc_ref(v_decl_879_);
v___x_880_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_873_, v_fvarId_866_, v_decl_879_);
v___x_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_881_, 0, v_decl_879_);
v___x_882_ = l_Lean_PersistentArray_push___redArg(v_decls_872_, v___x_881_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 1, v___x_882_);
lean_ctor_set(v___x_876_, 0, v___x_880_);
v___x_884_ = v___x_876_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_880_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v___x_882_);
lean_ctor_set(v_reuseFailAlloc_885_, 2, v_auxDeclToFullName_874_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLetDecl___boxed(lean_object* v_lctx_887_, lean_object* v_fvarId_888_, lean_object* v_userName_889_, lean_object* v_type_890_, lean_object* v_value_891_, lean_object* v_nondep_892_, lean_object* v_kind_893_){
_start:
{
uint8_t v_nondep_boxed_894_; uint8_t v_kind_boxed_895_; lean_object* v_res_896_; 
v_nondep_boxed_894_ = lean_unbox(v_nondep_892_);
v_kind_boxed_895_ = lean_unbox(v_kind_893_);
v_res_896_ = l_Lean_LocalContext_mkLetDecl(v_lctx_887_, v_fvarId_888_, v_userName_889_, v_type_890_, v_value_891_, v_nondep_boxed_894_, v_kind_boxed_895_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_mk_let_decl(lean_object* v_lctx_897_, lean_object* v_fvarId_898_, lean_object* v_userName_899_, lean_object* v_type_900_, lean_object* v_value_901_, uint8_t v_nondep_902_){
_start:
{
uint8_t v___x_903_; lean_object* v___x_904_; 
v___x_903_ = 0;
v___x_904_ = l_Lean_LocalContext_mkLetDecl(v_lctx_897_, v_fvarId_898_, v_userName_899_, v_type_900_, v_value_901_, v_nondep_902_, v___x_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_mkLetDeclExported___boxed(lean_object* v_lctx_905_, lean_object* v_fvarId_906_, lean_object* v_userName_907_, lean_object* v_type_908_, lean_object* v_value_909_, lean_object* v_nondep_910_){
_start:
{
uint8_t v_nondep_boxed_911_; lean_object* v_res_912_; 
v_nondep_boxed_911_ = lean_unbox(v_nondep_910_);
v_res_912_ = lean_local_ctx_mk_let_decl(v_lctx_905_, v_fvarId_906_, v_userName_907_, v_type_908_, v_value_909_, v_nondep_boxed_911_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkAuxDecl(lean_object* v_lctx_913_, lean_object* v_fvarId_914_, lean_object* v_userName_915_, lean_object* v_type_916_, lean_object* v_fullName_917_){
_start:
{
lean_object* v_decls_918_; lean_object* v_fvarIdToDecl_919_; lean_object* v_auxDeclToFullName_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_935_; 
v_decls_918_ = lean_ctor_get(v_lctx_913_, 1);
v_fvarIdToDecl_919_ = lean_ctor_get(v_lctx_913_, 0);
v_auxDeclToFullName_920_ = lean_ctor_get(v_lctx_913_, 2);
v_isSharedCheck_935_ = !lean_is_exclusive(v_lctx_913_);
if (v_isSharedCheck_935_ == 0)
{
v___x_922_ = v_lctx_913_;
v_isShared_923_ = v_isSharedCheck_935_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_auxDeclToFullName_920_);
lean_inc(v_decls_918_);
lean_inc(v_fvarIdToDecl_919_);
lean_dec(v_lctx_913_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_935_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v_size_924_; uint8_t v___x_925_; uint8_t v___x_926_; lean_object* v_decl_927_; lean_object* v_auxDeclToFullName_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_933_; 
v_size_924_ = lean_ctor_get(v_decls_918_, 2);
v___x_925_ = 0;
v___x_926_ = 2;
lean_inc_n(v_fvarId_914_, 2);
lean_inc(v_size_924_);
v_decl_927_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_decl_927_, 0, v_size_924_);
lean_ctor_set(v_decl_927_, 1, v_fvarId_914_);
lean_ctor_set(v_decl_927_, 2, v_userName_915_);
lean_ctor_set(v_decl_927_, 3, v_type_916_);
lean_ctor_set_uint8(v_decl_927_, sizeof(void*)*4, v___x_925_);
lean_ctor_set_uint8(v_decl_927_, sizeof(void*)*4 + 1, v___x_926_);
v_auxDeclToFullName_928_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_914_, v_fullName_917_, v_auxDeclToFullName_920_);
lean_inc_ref(v_decl_927_);
v___x_929_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_919_, v_fvarId_914_, v_decl_927_);
v___x_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_930_, 0, v_decl_927_);
v___x_931_ = l_Lean_PersistentArray_push___redArg(v_decls_918_, v___x_930_);
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 2, v_auxDeclToFullName_928_);
lean_ctor_set(v___x_922_, 1, v___x_931_);
lean_ctor_set(v___x_922_, 0, v___x_929_);
v___x_933_ = v___x_922_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_929_);
lean_ctor_set(v_reuseFailAlloc_934_, 1, v___x_931_);
lean_ctor_set(v_reuseFailAlloc_934_, 2, v_auxDeclToFullName_928_);
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
LEAN_EXPORT lean_object* l_Lean_LocalContext_addDecl(lean_object* v_lctx_936_, lean_object* v_newDecl_937_){
_start:
{
lean_object* v_decls_938_; lean_object* v_fvarIdToDecl_939_; lean_object* v_auxDeclToFullName_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_955_; 
v_decls_938_ = lean_ctor_get(v_lctx_936_, 1);
v_fvarIdToDecl_939_ = lean_ctor_get(v_lctx_936_, 0);
v_auxDeclToFullName_940_ = lean_ctor_get(v_lctx_936_, 2);
v_isSharedCheck_955_ = !lean_is_exclusive(v_lctx_936_);
if (v_isSharedCheck_955_ == 0)
{
v___x_942_ = v_lctx_936_;
v_isShared_943_ = v_isSharedCheck_955_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_auxDeclToFullName_940_);
lean_inc(v_decls_938_);
lean_inc(v_fvarIdToDecl_939_);
lean_dec(v_lctx_936_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_955_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v_size_944_; lean_object* v_newDecl_945_; lean_object* v___y_947_; lean_object* v_fvarId_954_; 
v_size_944_ = lean_ctor_get(v_decls_938_, 2);
lean_inc(v_size_944_);
v_newDecl_945_ = l_Lean_LocalDecl_setIndex(v_newDecl_937_, v_size_944_);
v_fvarId_954_ = lean_ctor_get(v_newDecl_945_, 1);
lean_inc(v_fvarId_954_);
v___y_947_ = v_fvarId_954_;
goto v___jp_946_;
v___jp_946_:
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_952_; 
lean_inc_ref(v_newDecl_945_);
v___x_948_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_939_, v___y_947_, v_newDecl_945_);
v___x_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_949_, 0, v_newDecl_945_);
v___x_950_ = l_Lean_PersistentArray_push___redArg(v_decls_938_, v___x_949_);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 1, v___x_950_);
lean_ctor_set(v___x_942_, 0, v___x_948_);
v___x_952_ = v___x_942_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_948_);
lean_ctor_set(v_reuseFailAlloc_953_, 1, v___x_950_);
lean_ctor_set(v_reuseFailAlloc_953_, 2, v_auxDeclToFullName_940_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_956_, lean_object* v_vals_957_, lean_object* v_i_958_, lean_object* v_k_959_){
_start:
{
lean_object* v___x_960_; uint8_t v___x_961_; 
v___x_960_ = lean_array_get_size(v_keys_956_);
v___x_961_ = lean_nat_dec_lt(v_i_958_, v___x_960_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; 
lean_dec(v_i_958_);
v___x_962_ = lean_box(0);
return v___x_962_;
}
else
{
lean_object* v_k_x27_963_; uint8_t v___x_964_; 
v_k_x27_963_ = lean_array_fget_borrowed(v_keys_956_, v_i_958_);
v___x_964_ = l_Lean_instBEqFVarId_beq(v_k_959_, v_k_x27_963_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_965_ = lean_unsigned_to_nat(1u);
v___x_966_ = lean_nat_add(v_i_958_, v___x_965_);
lean_dec(v_i_958_);
v_i_958_ = v___x_966_;
goto _start;
}
else
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = lean_array_fget_borrowed(v_vals_957_, v_i_958_);
lean_dec(v_i_958_);
lean_inc(v___x_968_);
v___x_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
return v___x_969_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_970_, lean_object* v_vals_971_, lean_object* v_i_972_, lean_object* v_k_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_970_, v_vals_971_, v_i_972_, v_k_973_);
lean_dec(v_k_973_);
lean_dec_ref(v_vals_971_);
lean_dec_ref(v_keys_970_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(lean_object* v_x_975_, size_t v_x_976_, lean_object* v_x_977_){
_start:
{
if (lean_obj_tag(v_x_975_) == 0)
{
lean_object* v_es_978_; lean_object* v___x_979_; size_t v___x_980_; size_t v___x_981_; lean_object* v_j_982_; lean_object* v___x_983_; 
v_es_978_ = lean_ctor_get(v_x_975_, 0);
v___x_979_ = lean_box(2);
v___x_980_ = ((size_t)31ULL);
v___x_981_ = lean_usize_land(v_x_976_, v___x_980_);
v_j_982_ = lean_usize_to_nat(v___x_981_);
v___x_983_ = lean_array_get_borrowed(v___x_979_, v_es_978_, v_j_982_);
lean_dec(v_j_982_);
switch(lean_obj_tag(v___x_983_))
{
case 0:
{
lean_object* v_key_984_; lean_object* v_val_985_; uint8_t v___x_986_; 
v_key_984_ = lean_ctor_get(v___x_983_, 0);
v_val_985_ = lean_ctor_get(v___x_983_, 1);
v___x_986_ = l_Lean_instBEqFVarId_beq(v_x_977_, v_key_984_);
if (v___x_986_ == 0)
{
lean_object* v___x_987_; 
v___x_987_ = lean_box(0);
return v___x_987_;
}
else
{
lean_object* v___x_988_; 
lean_inc(v_val_985_);
v___x_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_988_, 0, v_val_985_);
return v___x_988_;
}
}
case 1:
{
lean_object* v_node_989_; size_t v___x_990_; size_t v___x_991_; 
v_node_989_ = lean_ctor_get(v___x_983_, 0);
v___x_990_ = ((size_t)5ULL);
v___x_991_ = lean_usize_shift_right(v_x_976_, v___x_990_);
v_x_975_ = v_node_989_;
v_x_976_ = v___x_991_;
goto _start;
}
default: 
{
lean_object* v___x_993_; 
v___x_993_ = lean_box(0);
return v___x_993_;
}
}
}
else
{
lean_object* v_ks_994_; lean_object* v_vs_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v_ks_994_ = lean_ctor_get(v_x_975_, 0);
v_vs_995_ = lean_ctor_get(v_x_975_, 1);
v___x_996_ = lean_unsigned_to_nat(0u);
v___x_997_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(v_ks_994_, v_vs_995_, v___x_996_, v_x_977_);
return v___x_997_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_998_, lean_object* v_x_999_, lean_object* v_x_1000_){
_start:
{
size_t v_x_135__boxed_1001_; lean_object* v_res_1002_; 
v_x_135__boxed_1001_ = lean_unbox_usize(v_x_999_);
lean_dec(v_x_999_);
v_res_1002_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(v_x_998_, v_x_135__boxed_1001_, v_x_1000_);
lean_dec(v_x_1000_);
lean_dec_ref(v_x_998_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(lean_object* v_x_1003_, lean_object* v_x_1004_){
_start:
{
uint64_t v___x_1005_; size_t v___x_1006_; lean_object* v___x_1007_; 
v___x_1005_ = l_Lean_instHashableFVarId_hash(v_x_1004_);
v___x_1006_ = lean_uint64_to_usize(v___x_1005_);
v___x_1007_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(v_x_1003_, v___x_1006_, v_x_1004_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg___boxed(lean_object* v_x_1008_, lean_object* v_x_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_x_1008_, v_x_1009_);
lean_dec(v_x_1009_);
lean_dec_ref(v_x_1008_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_find(lean_object* v_lctx_1011_, lean_object* v_fvarId_1012_){
_start:
{
lean_object* v_fvarIdToDecl_1013_; lean_object* v___x_1014_; 
v_fvarIdToDecl_1013_ = lean_ctor_get(v_lctx_1011_, 0);
lean_inc_ref(v_fvarIdToDecl_1013_);
lean_dec_ref(v_lctx_1011_);
v___x_1014_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_fvarIdToDecl_1013_, v_fvarId_1012_);
lean_dec(v_fvarId_1012_);
lean_dec_ref(v_fvarIdToDecl_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0(lean_object* v_00_u03b2_1015_, lean_object* v_x_1016_, lean_object* v_x_1017_){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_x_1016_, v_x_1017_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___boxed(lean_object* v_00_u03b2_1019_, lean_object* v_x_1020_, lean_object* v_x_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0(v_00_u03b2_1019_, v_x_1020_, v_x_1021_);
lean_dec(v_x_1021_);
lean_dec_ref(v_x_1020_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1023_, lean_object* v_x_1024_, size_t v_x_1025_, lean_object* v_x_1026_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(v_x_1024_, v_x_1025_, v_x_1026_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1028_, lean_object* v_x_1029_, lean_object* v_x_1030_, lean_object* v_x_1031_){
_start:
{
size_t v_x_204__boxed_1032_; lean_object* v_res_1033_; 
v_x_204__boxed_1032_ = lean_unbox_usize(v_x_1030_);
lean_dec(v_x_1030_);
v_res_1033_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0(v_00_u03b2_1028_, v_x_1029_, v_x_204__boxed_1032_, v_x_1031_);
lean_dec(v_x_1031_);
lean_dec_ref(v_x_1029_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1034_, lean_object* v_keys_1035_, lean_object* v_vals_1036_, lean_object* v_heq_1037_, lean_object* v_i_1038_, lean_object* v_k_1039_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1035_, v_vals_1036_, v_i_1038_, v_k_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1041_, lean_object* v_keys_1042_, lean_object* v_vals_1043_, lean_object* v_heq_1044_, lean_object* v_i_1045_, lean_object* v_k_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1041_, v_keys_1042_, v_vals_1043_, v_heq_1044_, v_i_1045_, v_k_1046_);
lean_dec(v_k_1046_);
lean_dec_ref(v_vals_1043_);
lean_dec_ref(v_keys_1042_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFVar_x3f(lean_object* v_lctx_1048_, lean_object* v_e_1049_){
_start:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = l_Lean_Expr_fvarId_x21(v_e_1049_);
v___x_1051_ = lean_local_ctx_find(v_lctx_1048_, v___x_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFVar_x3f___boxed(lean_object* v_lctx_1052_, lean_object* v_e_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_1052_, v_e_1053_);
lean_dec_ref(v_e_1053_);
return v_res_1054_;
}
}
static lean_object* _init_l_Lean_LocalContext_get_x21___closed__2(void){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1057_ = ((lean_object*)(l_Lean_LocalContext_get_x21___closed__1));
v___x_1058_ = lean_unsigned_to_nat(14u);
v___x_1059_ = lean_unsigned_to_nat(350u);
v___x_1060_ = ((lean_object*)(l_Lean_LocalContext_get_x21___closed__0));
v___x_1061_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_1062_ = l_mkPanicMessageWithDecl(v___x_1061_, v___x_1060_, v___x_1059_, v___x_1058_, v___x_1057_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_get_x21(lean_object* v_lctx_1063_, lean_object* v_fvarId_1064_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = lean_local_ctx_find(v_lctx_1063_, v_fvarId_1064_);
if (lean_obj_tag(v___x_1065_) == 0)
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = lean_obj_once(&l_Lean_LocalContext_get_x21___closed__2, &l_Lean_LocalContext_get_x21___closed__2_once, _init_l_Lean_LocalContext_get_x21___closed__2);
v___x_1067_ = l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(v___x_1066_);
return v___x_1067_;
}
else
{
lean_object* v_val_1068_; 
v_val_1068_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_val_1068_);
lean_dec_ref_known(v___x_1065_, 1);
return v_val_1068_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVar_x21(lean_object* v_lctx_1069_, lean_object* v_e_1070_){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = l_Lean_Expr_fvarId_x21(v_e_1070_);
v___x_1072_ = l_Lean_LocalContext_get_x21(v_lctx_1069_, v___x_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVar_x21___boxed(lean_object* v_lctx_1073_, lean_object* v_e_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Lean_LocalContext_getFVar_x21(v_lctx_1073_, v_e_1074_);
lean_dec_ref(v_e_1074_);
return v_res_1075_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1076_, lean_object* v_i_1077_, lean_object* v_k_1078_){
_start:
{
lean_object* v___x_1079_; uint8_t v___x_1080_; 
v___x_1079_ = lean_array_get_size(v_keys_1076_);
v___x_1080_ = lean_nat_dec_lt(v_i_1077_, v___x_1079_);
if (v___x_1080_ == 0)
{
lean_dec(v_i_1077_);
return v___x_1080_;
}
else
{
lean_object* v_k_x27_1081_; uint8_t v___x_1082_; 
v_k_x27_1081_ = lean_array_fget_borrowed(v_keys_1076_, v_i_1077_);
v___x_1082_ = l_Lean_instBEqFVarId_beq(v_k_1078_, v_k_x27_1081_);
if (v___x_1082_ == 0)
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = lean_unsigned_to_nat(1u);
v___x_1084_ = lean_nat_add(v_i_1077_, v___x_1083_);
lean_dec(v_i_1077_);
v_i_1077_ = v___x_1084_;
goto _start;
}
else
{
lean_dec(v_i_1077_);
return v___x_1080_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1086_, lean_object* v_i_1087_, lean_object* v_k_1088_){
_start:
{
uint8_t v_res_1089_; lean_object* v_r_1090_; 
v_res_1089_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(v_keys_1086_, v_i_1087_, v_k_1088_);
lean_dec(v_k_1088_);
lean_dec_ref(v_keys_1086_);
v_r_1090_ = lean_box(v_res_1089_);
return v_r_1090_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(lean_object* v_x_1091_, size_t v_x_1092_, lean_object* v_x_1093_){
_start:
{
if (lean_obj_tag(v_x_1091_) == 0)
{
lean_object* v_es_1094_; lean_object* v___x_1095_; size_t v___x_1096_; size_t v___x_1097_; lean_object* v_j_1098_; lean_object* v___x_1099_; 
v_es_1094_ = lean_ctor_get(v_x_1091_, 0);
v___x_1095_ = lean_box(2);
v___x_1096_ = ((size_t)31ULL);
v___x_1097_ = lean_usize_land(v_x_1092_, v___x_1096_);
v_j_1098_ = lean_usize_to_nat(v___x_1097_);
v___x_1099_ = lean_array_get_borrowed(v___x_1095_, v_es_1094_, v_j_1098_);
lean_dec(v_j_1098_);
switch(lean_obj_tag(v___x_1099_))
{
case 0:
{
lean_object* v_key_1100_; uint8_t v___x_1101_; 
v_key_1100_ = lean_ctor_get(v___x_1099_, 0);
v___x_1101_ = l_Lean_instBEqFVarId_beq(v_x_1093_, v_key_1100_);
return v___x_1101_;
}
case 1:
{
lean_object* v_node_1102_; size_t v___x_1103_; size_t v___x_1104_; 
v_node_1102_ = lean_ctor_get(v___x_1099_, 0);
v___x_1103_ = ((size_t)5ULL);
v___x_1104_ = lean_usize_shift_right(v_x_1092_, v___x_1103_);
v_x_1091_ = v_node_1102_;
v_x_1092_ = v___x_1104_;
goto _start;
}
default: 
{
uint8_t v___x_1106_; 
v___x_1106_ = 0;
return v___x_1106_;
}
}
}
else
{
lean_object* v_ks_1107_; lean_object* v___x_1108_; uint8_t v___x_1109_; 
v_ks_1107_ = lean_ctor_get(v_x_1091_, 0);
v___x_1108_ = lean_unsigned_to_nat(0u);
v___x_1109_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(v_ks_1107_, v___x_1108_, v_x_1093_);
return v___x_1109_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg___boxed(lean_object* v_x_1110_, lean_object* v_x_1111_, lean_object* v_x_1112_){
_start:
{
size_t v_x_119__boxed_1113_; uint8_t v_res_1114_; lean_object* v_r_1115_; 
v_x_119__boxed_1113_ = lean_unbox_usize(v_x_1111_);
lean_dec(v_x_1111_);
v_res_1114_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(v_x_1110_, v_x_119__boxed_1113_, v_x_1112_);
lean_dec(v_x_1112_);
lean_dec_ref(v_x_1110_);
v_r_1115_ = lean_box(v_res_1114_);
return v_r_1115_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(lean_object* v_x_1116_, lean_object* v_x_1117_){
_start:
{
uint64_t v___x_1118_; size_t v___x_1119_; uint8_t v___x_1120_; 
v___x_1118_ = l_Lean_instHashableFVarId_hash(v_x_1117_);
v___x_1119_ = lean_uint64_to_usize(v___x_1118_);
v___x_1120_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(v_x_1116_, v___x_1119_, v_x_1117_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg___boxed(lean_object* v_x_1121_, lean_object* v_x_1122_){
_start:
{
uint8_t v_res_1123_; lean_object* v_r_1124_; 
v_res_1123_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(v_x_1121_, v_x_1122_);
lean_dec(v_x_1122_);
lean_dec_ref(v_x_1121_);
v_r_1124_ = lean_box(v_res_1123_);
return v_r_1124_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_contains(lean_object* v_lctx_1125_, lean_object* v_fvarId_1126_){
_start:
{
lean_object* v_fvarIdToDecl_1127_; uint8_t v___x_1128_; 
v_fvarIdToDecl_1127_ = lean_ctor_get(v_lctx_1125_, 0);
v___x_1128_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(v_fvarIdToDecl_1127_, v_fvarId_1126_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_contains___boxed(lean_object* v_lctx_1129_, lean_object* v_fvarId_1130_){
_start:
{
uint8_t v_res_1131_; lean_object* v_r_1132_; 
v_res_1131_ = l_Lean_LocalContext_contains(v_lctx_1129_, v_fvarId_1130_);
lean_dec(v_fvarId_1130_);
lean_dec_ref(v_lctx_1129_);
v_r_1132_ = lean_box(v_res_1131_);
return v_r_1132_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0(lean_object* v_00_u03b2_1133_, lean_object* v_x_1134_, lean_object* v_x_1135_){
_start:
{
uint8_t v___x_1136_; 
v___x_1136_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(v_x_1134_, v_x_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___boxed(lean_object* v_00_u03b2_1137_, lean_object* v_x_1138_, lean_object* v_x_1139_){
_start:
{
uint8_t v_res_1140_; lean_object* v_r_1141_; 
v_res_1140_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0(v_00_u03b2_1137_, v_x_1138_, v_x_1139_);
lean_dec(v_x_1139_);
lean_dec_ref(v_x_1138_);
v_r_1141_ = lean_box(v_res_1140_);
return v_r_1141_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0(lean_object* v_00_u03b2_1142_, lean_object* v_x_1143_, size_t v_x_1144_, lean_object* v_x_1145_){
_start:
{
uint8_t v___x_1146_; 
v___x_1146_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(v_x_1143_, v_x_1144_, v_x_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1147_, lean_object* v_x_1148_, lean_object* v_x_1149_, lean_object* v_x_1150_){
_start:
{
size_t v_x_182__boxed_1151_; uint8_t v_res_1152_; lean_object* v_r_1153_; 
v_x_182__boxed_1151_ = lean_unbox_usize(v_x_1149_);
lean_dec(v_x_1149_);
v_res_1152_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0(v_00_u03b2_1147_, v_x_1148_, v_x_182__boxed_1151_, v_x_1150_);
lean_dec(v_x_1150_);
lean_dec_ref(v_x_1148_);
v_r_1153_ = lean_box(v_res_1152_);
return v_r_1153_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1154_, lean_object* v_keys_1155_, lean_object* v_vals_1156_, lean_object* v_heq_1157_, lean_object* v_i_1158_, lean_object* v_k_1159_){
_start:
{
uint8_t v___x_1160_; 
v___x_1160_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(v_keys_1155_, v_i_1158_, v_k_1159_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1161_, lean_object* v_keys_1162_, lean_object* v_vals_1163_, lean_object* v_heq_1164_, lean_object* v_i_1165_, lean_object* v_k_1166_){
_start:
{
uint8_t v_res_1167_; lean_object* v_r_1168_; 
v_res_1167_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1(v_00_u03b2_1161_, v_keys_1162_, v_vals_1163_, v_heq_1164_, v_i_1165_, v_k_1166_);
lean_dec(v_k_1166_);
lean_dec_ref(v_vals_1163_);
lean_dec_ref(v_keys_1162_);
v_r_1168_ = lean_box(v_res_1167_);
return v_r_1168_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_containsFVar(lean_object* v_lctx_1169_, lean_object* v_e_1170_){
_start:
{
lean_object* v___x_1171_; uint8_t v___x_1172_; 
v___x_1171_ = l_Lean_Expr_fvarId_x21(v_e_1170_);
v___x_1172_ = l_Lean_LocalContext_contains(v_lctx_1169_, v___x_1171_);
lean_dec(v___x_1171_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_containsFVar___boxed(lean_object* v_lctx_1173_, lean_object* v_e_1174_){
_start:
{
uint8_t v_res_1175_; lean_object* v_r_1176_; 
v_res_1175_ = l_Lean_LocalContext_containsFVar(v_lctx_1173_, v_e_1174_);
lean_dec_ref(v_e_1174_);
lean_dec_ref(v_lctx_1173_);
v_r_1176_ = lean_box(v_res_1175_);
return v_r_1176_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(lean_object* v_as_1177_, size_t v_i_1178_, size_t v_stop_1179_, lean_object* v_b_1180_){
_start:
{
lean_object* v___y_1182_; uint8_t v___x_1186_; 
v___x_1186_ = lean_usize_dec_eq(v_i_1178_, v_stop_1179_);
if (v___x_1186_ == 0)
{
lean_object* v___x_1187_; 
v___x_1187_ = lean_array_uget_borrowed(v_as_1177_, v_i_1178_);
if (lean_obj_tag(v___x_1187_) == 0)
{
v___y_1182_ = v_b_1180_;
goto v___jp_1181_;
}
else
{
lean_object* v_val_1188_; lean_object* v_fvarId_1189_; lean_object* v___x_1190_; 
v_val_1188_ = lean_ctor_get(v___x_1187_, 0);
v_fvarId_1189_ = lean_ctor_get(v_val_1188_, 1);
lean_inc(v_fvarId_1189_);
v___x_1190_ = lean_array_push(v_b_1180_, v_fvarId_1189_);
v___y_1182_ = v___x_1190_;
goto v___jp_1181_;
}
}
else
{
return v_b_1180_;
}
v___jp_1181_:
{
size_t v___x_1183_; size_t v___x_1184_; 
v___x_1183_ = ((size_t)1ULL);
v___x_1184_ = lean_usize_add(v_i_1178_, v___x_1183_);
v_i_1178_ = v___x_1184_;
v_b_1180_ = v___y_1182_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1___boxed(lean_object* v_as_1191_, lean_object* v_i_1192_, lean_object* v_stop_1193_, lean_object* v_b_1194_){
_start:
{
size_t v_i_boxed_1195_; size_t v_stop_boxed_1196_; lean_object* v_res_1197_; 
v_i_boxed_1195_ = lean_unbox_usize(v_i_1192_);
lean_dec(v_i_1192_);
v_stop_boxed_1196_ = lean_unbox_usize(v_stop_1193_);
lean_dec(v_stop_1193_);
v_res_1197_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_as_1191_, v_i_boxed_1195_, v_stop_boxed_1196_, v_b_1194_);
lean_dec_ref(v_as_1191_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(lean_object* v_x_1198_, lean_object* v_x_1199_){
_start:
{
if (lean_obj_tag(v_x_1198_) == 0)
{
lean_object* v_cs_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; uint8_t v___x_1203_; 
v_cs_1200_ = lean_ctor_get(v_x_1198_, 0);
v___x_1201_ = lean_unsigned_to_nat(0u);
v___x_1202_ = lean_array_get_size(v_cs_1200_);
v___x_1203_ = lean_nat_dec_lt(v___x_1201_, v___x_1202_);
if (v___x_1203_ == 0)
{
return v_x_1199_;
}
else
{
size_t v___x_1204_; size_t v___x_1205_; lean_object* v___x_1206_; 
v___x_1204_ = ((size_t)0ULL);
v___x_1205_ = lean_usize_of_nat(v___x_1202_);
v___x_1206_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_cs_1200_, v___x_1204_, v___x_1205_, v_x_1199_);
return v___x_1206_;
}
}
else
{
lean_object* v_vs_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; uint8_t v___x_1210_; 
v_vs_1207_ = lean_ctor_get(v_x_1198_, 0);
v___x_1208_ = lean_unsigned_to_nat(0u);
v___x_1209_ = lean_array_get_size(v_vs_1207_);
v___x_1210_ = lean_nat_dec_lt(v___x_1208_, v___x_1209_);
if (v___x_1210_ == 0)
{
return v_x_1199_;
}
else
{
size_t v___x_1211_; size_t v___x_1212_; lean_object* v___x_1213_; 
v___x_1211_ = ((size_t)0ULL);
v___x_1212_ = lean_usize_of_nat(v___x_1209_);
v___x_1213_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_vs_1207_, v___x_1211_, v___x_1212_, v_x_1199_);
return v___x_1213_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(lean_object* v_as_1214_, size_t v_i_1215_, size_t v_stop_1216_, lean_object* v_b_1217_){
_start:
{
uint8_t v___x_1218_; 
v___x_1218_ = lean_usize_dec_eq(v_i_1215_, v_stop_1216_);
if (v___x_1218_ == 0)
{
lean_object* v___x_1219_; lean_object* v___x_1220_; size_t v___x_1221_; size_t v___x_1222_; 
v___x_1219_ = lean_array_uget_borrowed(v_as_1214_, v_i_1215_);
v___x_1220_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(v___x_1219_, v_b_1217_);
v___x_1221_ = ((size_t)1ULL);
v___x_1222_ = lean_usize_add(v_i_1215_, v___x_1221_);
v_i_1215_ = v___x_1222_;
v_b_1217_ = v___x_1220_;
goto _start;
}
else
{
return v_b_1217_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1___boxed(lean_object* v_as_1224_, lean_object* v_i_1225_, lean_object* v_stop_1226_, lean_object* v_b_1227_){
_start:
{
size_t v_i_boxed_1228_; size_t v_stop_boxed_1229_; lean_object* v_res_1230_; 
v_i_boxed_1228_ = lean_unbox_usize(v_i_1225_);
lean_dec(v_i_1225_);
v_stop_boxed_1229_ = lean_unbox_usize(v_stop_1226_);
lean_dec(v_stop_1226_);
v_res_1230_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_as_1224_, v_i_boxed_1228_, v_stop_boxed_1229_, v_b_1227_);
lean_dec_ref(v_as_1224_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2___boxed(lean_object* v_x_1231_, lean_object* v_x_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(v_x_1231_, v_x_1232_);
lean_dec_ref(v_x_1231_);
return v_res_1233_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1234_; 
v___x_1234_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(lean_object* v_x_1235_, size_t v_x_1236_, size_t v_x_1237_, lean_object* v_x_1238_){
_start:
{
if (lean_obj_tag(v_x_1235_) == 0)
{
lean_object* v_cs_1239_; lean_object* v___x_1240_; size_t v___x_1241_; lean_object* v_j_1242_; lean_object* v___x_1243_; size_t v___x_1244_; size_t v___x_1245_; size_t v___x_1246_; size_t v___x_1247_; size_t v___x_1248_; size_t v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; uint8_t v___x_1254_; 
v_cs_1239_ = lean_ctor_get(v_x_1235_, 0);
v___x_1240_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0);
v___x_1241_ = lean_usize_shift_right(v_x_1236_, v_x_1237_);
v_j_1242_ = lean_usize_to_nat(v___x_1241_);
v___x_1243_ = lean_array_get_borrowed(v___x_1240_, v_cs_1239_, v_j_1242_);
v___x_1244_ = ((size_t)1ULL);
v___x_1245_ = lean_usize_shift_left(v___x_1244_, v_x_1237_);
v___x_1246_ = lean_usize_sub(v___x_1245_, v___x_1244_);
v___x_1247_ = lean_usize_land(v_x_1236_, v___x_1246_);
v___x_1248_ = ((size_t)5ULL);
v___x_1249_ = lean_usize_sub(v_x_1237_, v___x_1248_);
v___x_1250_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(v___x_1243_, v___x_1247_, v___x_1249_, v_x_1238_);
v___x_1251_ = lean_unsigned_to_nat(1u);
v___x_1252_ = lean_nat_add(v_j_1242_, v___x_1251_);
lean_dec(v_j_1242_);
v___x_1253_ = lean_array_get_size(v_cs_1239_);
v___x_1254_ = lean_nat_dec_lt(v___x_1252_, v___x_1253_);
if (v___x_1254_ == 0)
{
lean_dec(v___x_1252_);
return v___x_1250_;
}
else
{
size_t v___x_1255_; size_t v___x_1256_; lean_object* v___x_1257_; 
v___x_1255_ = lean_usize_of_nat(v___x_1252_);
lean_dec(v___x_1252_);
v___x_1256_ = lean_usize_of_nat(v___x_1253_);
v___x_1257_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_cs_1239_, v___x_1255_, v___x_1256_, v___x_1250_);
return v___x_1257_;
}
}
else
{
lean_object* v_vs_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; uint8_t v___x_1261_; 
v_vs_1258_ = lean_ctor_get(v_x_1235_, 0);
v___x_1259_ = lean_usize_to_nat(v_x_1236_);
v___x_1260_ = lean_array_get_size(v_vs_1258_);
v___x_1261_ = lean_nat_dec_lt(v___x_1259_, v___x_1260_);
if (v___x_1261_ == 0)
{
lean_dec(v___x_1259_);
return v_x_1238_;
}
else
{
size_t v___x_1262_; size_t v___x_1263_; lean_object* v___x_1264_; 
v___x_1262_ = lean_usize_of_nat(v___x_1259_);
lean_dec(v___x_1259_);
v___x_1263_ = lean_usize_of_nat(v___x_1260_);
v___x_1264_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_vs_1258_, v___x_1262_, v___x_1263_, v_x_1238_);
return v___x_1264_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___boxed(lean_object* v_x_1265_, lean_object* v_x_1266_, lean_object* v_x_1267_, lean_object* v_x_1268_){
_start:
{
size_t v_x_1260__boxed_1269_; size_t v_x_1261__boxed_1270_; lean_object* v_res_1271_; 
v_x_1260__boxed_1269_ = lean_unbox_usize(v_x_1266_);
lean_dec(v_x_1266_);
v_x_1261__boxed_1270_ = lean_unbox_usize(v_x_1267_);
lean_dec(v_x_1267_);
v_res_1271_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(v_x_1265_, v_x_1260__boxed_1269_, v_x_1261__boxed_1270_, v_x_1268_);
lean_dec_ref(v_x_1265_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0(lean_object* v_t_1272_, lean_object* v_init_1273_, lean_object* v_start_1274_){
_start:
{
lean_object* v___x_1275_; uint8_t v___x_1276_; 
v___x_1275_ = lean_unsigned_to_nat(0u);
v___x_1276_ = lean_nat_dec_eq(v_start_1274_, v___x_1275_);
if (v___x_1276_ == 0)
{
lean_object* v_root_1277_; lean_object* v_tail_1278_; size_t v_shift_1279_; lean_object* v_tailOff_1280_; uint8_t v___x_1281_; 
v_root_1277_ = lean_ctor_get(v_t_1272_, 0);
v_tail_1278_ = lean_ctor_get(v_t_1272_, 1);
v_shift_1279_ = lean_ctor_get_usize(v_t_1272_, 4);
v_tailOff_1280_ = lean_ctor_get(v_t_1272_, 3);
v___x_1281_ = lean_nat_dec_le(v_tailOff_1280_, v_start_1274_);
if (v___x_1281_ == 0)
{
size_t v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; uint8_t v___x_1285_; 
v___x_1282_ = lean_usize_of_nat(v_start_1274_);
v___x_1283_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(v_root_1277_, v___x_1282_, v_shift_1279_, v_init_1273_);
v___x_1284_ = lean_array_get_size(v_tail_1278_);
v___x_1285_ = lean_nat_dec_lt(v___x_1275_, v___x_1284_);
if (v___x_1285_ == 0)
{
return v___x_1283_;
}
else
{
size_t v___x_1286_; size_t v___x_1287_; lean_object* v___x_1288_; 
v___x_1286_ = ((size_t)0ULL);
v___x_1287_ = lean_usize_of_nat(v___x_1284_);
v___x_1288_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1278_, v___x_1286_, v___x_1287_, v___x_1283_);
return v___x_1288_;
}
}
else
{
lean_object* v___x_1289_; lean_object* v___x_1290_; uint8_t v___x_1291_; 
v___x_1289_ = lean_nat_sub(v_start_1274_, v_tailOff_1280_);
v___x_1290_ = lean_array_get_size(v_tail_1278_);
v___x_1291_ = lean_nat_dec_lt(v___x_1289_, v___x_1290_);
if (v___x_1291_ == 0)
{
lean_dec(v___x_1289_);
return v_init_1273_;
}
else
{
size_t v___x_1292_; size_t v___x_1293_; lean_object* v___x_1294_; 
v___x_1292_ = lean_usize_of_nat(v___x_1289_);
lean_dec(v___x_1289_);
v___x_1293_ = lean_usize_of_nat(v___x_1290_);
v___x_1294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1278_, v___x_1292_, v___x_1293_, v_init_1273_);
return v___x_1294_;
}
}
}
else
{
lean_object* v_root_1295_; lean_object* v_tail_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; uint8_t v___x_1299_; 
v_root_1295_ = lean_ctor_get(v_t_1272_, 0);
v_tail_1296_ = lean_ctor_get(v_t_1272_, 1);
v___x_1297_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(v_root_1295_, v_init_1273_);
v___x_1298_ = lean_array_get_size(v_tail_1296_);
v___x_1299_ = lean_nat_dec_lt(v___x_1275_, v___x_1298_);
if (v___x_1299_ == 0)
{
return v___x_1297_;
}
else
{
size_t v___x_1300_; size_t v___x_1301_; lean_object* v___x_1302_; 
v___x_1300_ = ((size_t)0ULL);
v___x_1301_ = lean_usize_of_nat(v___x_1298_);
v___x_1302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1296_, v___x_1300_, v___x_1301_, v___x_1297_);
return v___x_1302_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0___boxed(lean_object* v_t_1303_, lean_object* v_init_1304_, lean_object* v_start_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0(v_t_1303_, v_init_1304_, v_start_1305_);
lean_dec(v_start_1305_);
lean_dec_ref(v_t_1303_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVarIds(lean_object* v_lctx_1309_){
_start:
{
lean_object* v_decls_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v_decls_1310_ = lean_ctor_get(v_lctx_1309_, 1);
v___x_1311_ = lean_unsigned_to_nat(0u);
v___x_1312_ = ((lean_object*)(l_Lean_LocalContext_getFVarIds___closed__0));
v___x_1313_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0(v_decls_1310_, v___x_1312_, v___x_1311_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVarIds___boxed(lean_object* v_lctx_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l_Lean_LocalContext_getFVarIds(v_lctx_1314_);
lean_dec_ref(v_lctx_1314_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0(size_t v_sz_1316_, size_t v_i_1317_, lean_object* v_bs_1318_){
_start:
{
uint8_t v___x_1319_; 
v___x_1319_ = lean_usize_dec_lt(v_i_1317_, v_sz_1316_);
if (v___x_1319_ == 0)
{
return v_bs_1318_;
}
else
{
lean_object* v_v_1320_; lean_object* v___x_1321_; lean_object* v_bs_x27_1322_; lean_object* v___x_1323_; size_t v___x_1324_; size_t v___x_1325_; lean_object* v___x_1326_; 
v_v_1320_ = lean_array_uget(v_bs_1318_, v_i_1317_);
v___x_1321_ = lean_unsigned_to_nat(0u);
v_bs_x27_1322_ = lean_array_uset(v_bs_1318_, v_i_1317_, v___x_1321_);
v___x_1323_ = l_Lean_mkFVar(v_v_1320_);
v___x_1324_ = ((size_t)1ULL);
v___x_1325_ = lean_usize_add(v_i_1317_, v___x_1324_);
v___x_1326_ = lean_array_uset(v_bs_x27_1322_, v_i_1317_, v___x_1323_);
v_i_1317_ = v___x_1325_;
v_bs_1318_ = v___x_1326_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0___boxed(lean_object* v_sz_1328_, lean_object* v_i_1329_, lean_object* v_bs_1330_){
_start:
{
size_t v_sz_boxed_1331_; size_t v_i_boxed_1332_; lean_object* v_res_1333_; 
v_sz_boxed_1331_ = lean_unbox_usize(v_sz_1328_);
lean_dec(v_sz_1328_);
v_i_boxed_1332_ = lean_unbox_usize(v_i_1329_);
lean_dec(v_i_1329_);
v_res_1333_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0(v_sz_boxed_1331_, v_i_boxed_1332_, v_bs_1330_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVars(lean_object* v_lctx_1334_){
_start:
{
lean_object* v___x_1335_; size_t v_sz_1336_; size_t v___x_1337_; lean_object* v___x_1338_; 
v___x_1335_ = l_Lean_LocalContext_getFVarIds(v_lctx_1334_);
v_sz_1336_ = lean_array_size(v___x_1335_);
v___x_1337_ = ((size_t)0ULL);
v___x_1338_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0(v_sz_1336_, v___x_1337_, v___x_1335_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVars___boxed(lean_object* v_lctx_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l_Lean_LocalContext_getFVars(v_lctx_1339_);
lean_dec_ref(v_lctx_1339_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(lean_object* v_a_1341_){
_start:
{
lean_object* v_size_1342_; lean_object* v___x_1343_; uint8_t v___x_1344_; 
v_size_1342_ = lean_ctor_get(v_a_1341_, 2);
v___x_1343_ = lean_unsigned_to_nat(0u);
v___x_1344_ = lean_nat_dec_eq(v_size_1342_, v___x_1343_);
if (v___x_1344_ == 0)
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1345_ = lean_box(0);
v___x_1346_ = lean_unsigned_to_nat(1u);
v___x_1347_ = lean_nat_sub(v_size_1342_, v___x_1346_);
v___x_1348_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1345_, v_a_1341_, v___x_1347_);
lean_dec(v___x_1347_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v___x_1349_; 
v___x_1349_ = l_Lean_PersistentArray_pop___redArg(v_a_1341_);
v_a_1341_ = v___x_1349_;
goto _start;
}
else
{
lean_dec_ref_known(v___x_1348_, 1);
return v_a_1341_;
}
}
else
{
return v_a_1341_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(lean_object* v_k_1351_, lean_object* v_t_1352_){
_start:
{
if (lean_obj_tag(v_t_1352_) == 0)
{
lean_object* v_k_1353_; lean_object* v_v_1354_; lean_object* v_l_1355_; lean_object* v_r_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_2010_; 
v_k_1353_ = lean_ctor_get(v_t_1352_, 1);
v_v_1354_ = lean_ctor_get(v_t_1352_, 2);
v_l_1355_ = lean_ctor_get(v_t_1352_, 3);
v_r_1356_ = lean_ctor_get(v_t_1352_, 4);
v_isSharedCheck_2010_ = !lean_is_exclusive(v_t_1352_);
if (v_isSharedCheck_2010_ == 0)
{
lean_object* v_unused_2011_; 
v_unused_2011_ = lean_ctor_get(v_t_1352_, 0);
lean_dec(v_unused_2011_);
v___x_1358_ = v_t_1352_;
v_isShared_1359_ = v_isSharedCheck_2010_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_r_1356_);
lean_inc(v_l_1355_);
lean_inc(v_v_1354_);
lean_inc(v_k_1353_);
lean_dec(v_t_1352_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_2010_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
uint8_t v___x_1360_; 
v___x_1360_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1351_, v_k_1353_);
switch(v___x_1360_)
{
case 0:
{
lean_object* v_impl_1361_; lean_object* v___x_1362_; 
v_impl_1361_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_1351_, v_l_1355_);
v___x_1362_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1361_) == 0)
{
if (lean_obj_tag(v_r_1356_) == 0)
{
lean_object* v_size_1363_; lean_object* v_size_1364_; lean_object* v_k_1365_; lean_object* v_v_1366_; lean_object* v_l_1367_; lean_object* v_r_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; uint8_t v___x_1371_; 
v_size_1363_ = lean_ctor_get(v_impl_1361_, 0);
v_size_1364_ = lean_ctor_get(v_r_1356_, 0);
v_k_1365_ = lean_ctor_get(v_r_1356_, 1);
v_v_1366_ = lean_ctor_get(v_r_1356_, 2);
v_l_1367_ = lean_ctor_get(v_r_1356_, 3);
lean_inc(v_l_1367_);
v_r_1368_ = lean_ctor_get(v_r_1356_, 4);
v___x_1369_ = lean_unsigned_to_nat(3u);
v___x_1370_ = lean_nat_mul(v___x_1369_, v_size_1363_);
v___x_1371_ = lean_nat_dec_lt(v___x_1370_, v_size_1364_);
lean_dec(v___x_1370_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1375_; 
lean_dec(v_l_1367_);
v___x_1372_ = lean_nat_add(v___x_1362_, v_size_1363_);
v___x_1373_ = lean_nat_add(v___x_1372_, v_size_1364_);
lean_dec(v___x_1372_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 3, v_impl_1361_);
lean_ctor_set(v___x_1358_, 0, v___x_1373_);
v___x_1375_ = v___x_1358_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1373_);
lean_ctor_set(v_reuseFailAlloc_1376_, 1, v_k_1353_);
lean_ctor_set(v_reuseFailAlloc_1376_, 2, v_v_1354_);
lean_ctor_set(v_reuseFailAlloc_1376_, 3, v_impl_1361_);
lean_ctor_set(v_reuseFailAlloc_1376_, 4, v_r_1356_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
else
{
lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1440_; 
lean_inc(v_r_1368_);
lean_inc(v_v_1366_);
lean_inc(v_k_1365_);
lean_inc(v_size_1364_);
v_isSharedCheck_1440_ = !lean_is_exclusive(v_r_1356_);
if (v_isSharedCheck_1440_ == 0)
{
lean_object* v_unused_1441_; lean_object* v_unused_1442_; lean_object* v_unused_1443_; lean_object* v_unused_1444_; lean_object* v_unused_1445_; 
v_unused_1441_ = lean_ctor_get(v_r_1356_, 4);
lean_dec(v_unused_1441_);
v_unused_1442_ = lean_ctor_get(v_r_1356_, 3);
lean_dec(v_unused_1442_);
v_unused_1443_ = lean_ctor_get(v_r_1356_, 2);
lean_dec(v_unused_1443_);
v_unused_1444_ = lean_ctor_get(v_r_1356_, 1);
lean_dec(v_unused_1444_);
v_unused_1445_ = lean_ctor_get(v_r_1356_, 0);
lean_dec(v_unused_1445_);
v___x_1378_ = v_r_1356_;
v_isShared_1379_ = v_isSharedCheck_1440_;
goto v_resetjp_1377_;
}
else
{
lean_dec(v_r_1356_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1440_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v_size_1380_; lean_object* v_k_1381_; lean_object* v_v_1382_; lean_object* v_l_1383_; lean_object* v_r_1384_; lean_object* v_size_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; uint8_t v___x_1388_; 
v_size_1380_ = lean_ctor_get(v_l_1367_, 0);
v_k_1381_ = lean_ctor_get(v_l_1367_, 1);
v_v_1382_ = lean_ctor_get(v_l_1367_, 2);
v_l_1383_ = lean_ctor_get(v_l_1367_, 3);
v_r_1384_ = lean_ctor_get(v_l_1367_, 4);
v_size_1385_ = lean_ctor_get(v_r_1368_, 0);
v___x_1386_ = lean_unsigned_to_nat(2u);
v___x_1387_ = lean_nat_mul(v___x_1386_, v_size_1385_);
v___x_1388_ = lean_nat_dec_lt(v_size_1380_, v___x_1387_);
lean_dec(v___x_1387_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1416_; 
lean_inc(v_r_1384_);
lean_inc(v_l_1383_);
lean_inc(v_v_1382_);
lean_inc(v_k_1381_);
v_isSharedCheck_1416_ = !lean_is_exclusive(v_l_1367_);
if (v_isSharedCheck_1416_ == 0)
{
lean_object* v_unused_1417_; lean_object* v_unused_1418_; lean_object* v_unused_1419_; lean_object* v_unused_1420_; lean_object* v_unused_1421_; 
v_unused_1417_ = lean_ctor_get(v_l_1367_, 4);
lean_dec(v_unused_1417_);
v_unused_1418_ = lean_ctor_get(v_l_1367_, 3);
lean_dec(v_unused_1418_);
v_unused_1419_ = lean_ctor_get(v_l_1367_, 2);
lean_dec(v_unused_1419_);
v_unused_1420_ = lean_ctor_get(v_l_1367_, 1);
lean_dec(v_unused_1420_);
v_unused_1421_ = lean_ctor_get(v_l_1367_, 0);
lean_dec(v_unused_1421_);
v___x_1390_ = v_l_1367_;
v_isShared_1391_ = v_isSharedCheck_1416_;
goto v_resetjp_1389_;
}
else
{
lean_dec(v_l_1367_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1416_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1406_; 
v___x_1392_ = lean_nat_add(v___x_1362_, v_size_1363_);
v___x_1393_ = lean_nat_add(v___x_1392_, v_size_1364_);
lean_dec(v_size_1364_);
if (lean_obj_tag(v_l_1383_) == 0)
{
lean_object* v_size_1414_; 
v_size_1414_ = lean_ctor_get(v_l_1383_, 0);
lean_inc(v_size_1414_);
v___y_1406_ = v_size_1414_;
goto v___jp_1405_;
}
else
{
lean_object* v___x_1415_; 
v___x_1415_ = lean_unsigned_to_nat(0u);
v___y_1406_ = v___x_1415_;
goto v___jp_1405_;
}
v___jp_1394_:
{
lean_object* v___x_1398_; lean_object* v___x_1400_; 
v___x_1398_ = lean_nat_add(v___y_1396_, v___y_1397_);
lean_dec(v___y_1397_);
lean_dec(v___y_1396_);
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 4, v_r_1368_);
lean_ctor_set(v___x_1390_, 3, v_r_1384_);
lean_ctor_set(v___x_1390_, 2, v_v_1366_);
lean_ctor_set(v___x_1390_, 1, v_k_1365_);
lean_ctor_set(v___x_1390_, 0, v___x_1398_);
v___x_1400_ = v___x_1390_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1398_);
lean_ctor_set(v_reuseFailAlloc_1404_, 1, v_k_1365_);
lean_ctor_set(v_reuseFailAlloc_1404_, 2, v_v_1366_);
lean_ctor_set(v_reuseFailAlloc_1404_, 3, v_r_1384_);
lean_ctor_set(v_reuseFailAlloc_1404_, 4, v_r_1368_);
v___x_1400_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
lean_object* v___x_1402_; 
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 4, v___x_1400_);
lean_ctor_set(v___x_1378_, 3, v___y_1395_);
lean_ctor_set(v___x_1378_, 2, v_v_1382_);
lean_ctor_set(v___x_1378_, 1, v_k_1381_);
lean_ctor_set(v___x_1378_, 0, v___x_1393_);
v___x_1402_ = v___x_1378_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1393_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v_k_1381_);
lean_ctor_set(v_reuseFailAlloc_1403_, 2, v_v_1382_);
lean_ctor_set(v_reuseFailAlloc_1403_, 3, v___y_1395_);
lean_ctor_set(v_reuseFailAlloc_1403_, 4, v___x_1400_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
v___jp_1405_:
{
lean_object* v___x_1407_; lean_object* v___x_1409_; 
v___x_1407_ = lean_nat_add(v___x_1392_, v___y_1406_);
lean_dec(v___y_1406_);
lean_dec(v___x_1392_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 4, v_l_1383_);
lean_ctor_set(v___x_1358_, 3, v_impl_1361_);
lean_ctor_set(v___x_1358_, 0, v___x_1407_);
v___x_1409_ = v___x_1358_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1407_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v_k_1353_);
lean_ctor_set(v_reuseFailAlloc_1413_, 2, v_v_1354_);
lean_ctor_set(v_reuseFailAlloc_1413_, 3, v_impl_1361_);
lean_ctor_set(v_reuseFailAlloc_1413_, 4, v_l_1383_);
v___x_1409_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
lean_object* v___x_1410_; 
v___x_1410_ = lean_nat_add(v___x_1362_, v_size_1385_);
if (lean_obj_tag(v_r_1384_) == 0)
{
lean_object* v_size_1411_; 
v_size_1411_ = lean_ctor_get(v_r_1384_, 0);
lean_inc(v_size_1411_);
v___y_1395_ = v___x_1409_;
v___y_1396_ = v___x_1410_;
v___y_1397_ = v_size_1411_;
goto v___jp_1394_;
}
else
{
lean_object* v___x_1412_; 
v___x_1412_ = lean_unsigned_to_nat(0u);
v___y_1395_ = v___x_1409_;
v___y_1396_ = v___x_1410_;
v___y_1397_ = v___x_1412_;
goto v___jp_1394_;
}
}
}
}
}
else
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1426_; 
lean_del_object(v___x_1358_);
v___x_1422_ = lean_nat_add(v___x_1362_, v_size_1363_);
v___x_1423_ = lean_nat_add(v___x_1422_, v_size_1364_);
lean_dec(v_size_1364_);
v___x_1424_ = lean_nat_add(v___x_1422_, v_size_1380_);
lean_dec(v___x_1422_);
lean_inc_ref(v_impl_1361_);
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 4, v_l_1367_);
lean_ctor_set(v___x_1378_, 3, v_impl_1361_);
lean_ctor_set(v___x_1378_, 2, v_v_1354_);
lean_ctor_set(v___x_1378_, 1, v_k_1353_);
lean_ctor_set(v___x_1378_, 0, v___x_1424_);
v___x_1426_ = v___x_1378_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1424_);
lean_ctor_set(v_reuseFailAlloc_1439_, 1, v_k_1353_);
lean_ctor_set(v_reuseFailAlloc_1439_, 2, v_v_1354_);
lean_ctor_set(v_reuseFailAlloc_1439_, 3, v_impl_1361_);
lean_ctor_set(v_reuseFailAlloc_1439_, 4, v_l_1367_);
v___x_1426_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1433_; 
v_isSharedCheck_1433_ = !lean_is_exclusive(v_impl_1361_);
if (v_isSharedCheck_1433_ == 0)
{
lean_object* v_unused_1434_; lean_object* v_unused_1435_; lean_object* v_unused_1436_; lean_object* v_unused_1437_; lean_object* v_unused_1438_; 
v_unused_1434_ = lean_ctor_get(v_impl_1361_, 4);
lean_dec(v_unused_1434_);
v_unused_1435_ = lean_ctor_get(v_impl_1361_, 3);
lean_dec(v_unused_1435_);
v_unused_1436_ = lean_ctor_get(v_impl_1361_, 2);
lean_dec(v_unused_1436_);
v_unused_1437_ = lean_ctor_get(v_impl_1361_, 1);
lean_dec(v_unused_1437_);
v_unused_1438_ = lean_ctor_get(v_impl_1361_, 0);
lean_dec(v_unused_1438_);
v___x_1428_ = v_impl_1361_;
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
else
{
lean_dec(v_impl_1361_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1431_; 
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 4, v_r_1368_);
lean_ctor_set(v___x_1428_, 3, v___x_1426_);
lean_ctor_set(v___x_1428_, 2, v_v_1366_);
lean_ctor_set(v___x_1428_, 1, v_k_1365_);
lean_ctor_set(v___x_1428_, 0, v___x_1423_);
v___x_1431_ = v___x_1428_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1423_);
lean_ctor_set(v_reuseFailAlloc_1432_, 1, v_k_1365_);
lean_ctor_set(v_reuseFailAlloc_1432_, 2, v_v_1366_);
lean_ctor_set(v_reuseFailAlloc_1432_, 3, v___x_1426_);
lean_ctor_set(v_reuseFailAlloc_1432_, 4, v_r_1368_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1446_; lean_object* v___x_1447_; lean_object* v___x_1449_; 
v_size_1446_ = lean_ctor_get(v_impl_1361_, 0);
v___x_1447_ = lean_nat_add(v___x_1362_, v_size_1446_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 3, v_impl_1361_);
lean_ctor_set(v___x_1358_, 0, v___x_1447_);
v___x_1449_ = v___x_1358_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1447_);
lean_ctor_set(v_reuseFailAlloc_1450_, 1, v_k_1353_);
lean_ctor_set(v_reuseFailAlloc_1450_, 2, v_v_1354_);
lean_ctor_set(v_reuseFailAlloc_1450_, 3, v_impl_1361_);
lean_ctor_set(v_reuseFailAlloc_1450_, 4, v_r_1356_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
else
{
if (lean_obj_tag(v_r_1356_) == 0)
{
lean_object* v_l_1451_; 
v_l_1451_ = lean_ctor_get(v_r_1356_, 3);
lean_inc(v_l_1451_);
if (lean_obj_tag(v_l_1451_) == 0)
{
lean_object* v_r_1452_; 
v_r_1452_ = lean_ctor_get(v_r_1356_, 4);
lean_inc(v_r_1452_);
if (lean_obj_tag(v_r_1452_) == 0)
{
lean_object* v_size_1453_; lean_object* v_k_1454_; lean_object* v_v_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1468_; 
v_size_1453_ = lean_ctor_get(v_r_1356_, 0);
v_k_1454_ = lean_ctor_get(v_r_1356_, 1);
v_v_1455_ = lean_ctor_get(v_r_1356_, 2);
v_isSharedCheck_1468_ = !lean_is_exclusive(v_r_1356_);
if (v_isSharedCheck_1468_ == 0)
{
lean_object* v_unused_1469_; lean_object* v_unused_1470_; 
v_unused_1469_ = lean_ctor_get(v_r_1356_, 4);
lean_dec(v_unused_1469_);
v_unused_1470_ = lean_ctor_get(v_r_1356_, 3);
lean_dec(v_unused_1470_);
v___x_1457_ = v_r_1356_;
v_isShared_1458_ = v_isSharedCheck_1468_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_v_1455_);
lean_inc(v_k_1454_);
lean_inc(v_size_1453_);
lean_dec(v_r_1356_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1468_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v_size_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1463_; 
v_size_1459_ = lean_ctor_get(v_l_1451_, 0);
v___x_1460_ = lean_nat_add(v___x_1362_, v_size_1453_);
lean_dec(v_size_1453_);
v___x_1461_ = lean_nat_add(v___x_1362_, v_size_1459_);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 4, v_l_1451_);
lean_ctor_set(v___x_1457_, 3, v_impl_1361_);
lean_ctor_set(v___x_1457_, 2, v_v_1354_);
lean_ctor_set(v___x_1457_, 1, v_k_1353_);
lean_ctor_set(v___x_1457_, 0, v___x_1461_);
v___x_1463_ = v___x_1457_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1461_);
lean_ctor_set(v_reuseFailAlloc_1467_, 1, v_k_1353_);
lean_ctor_set(v_reuseFailAlloc_1467_, 2, v_v_1354_);
lean_ctor_set(v_reuseFailAlloc_1467_, 3, v_impl_1361_);
lean_ctor_set(v_reuseFailAlloc_1467_, 4, v_l_1451_);
v___x_1463_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
lean_object* v___x_1465_; 
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 4, v_r_1452_);
lean_ctor_set(v___x_1358_, 3, v___x_1463_);
lean_ctor_set(v___x_1358_, 2, v_v_1455_);
lean_ctor_set(v___x_1358_, 1, v_k_1454_);
lean_ctor_set(v___x_1358_, 0, v___x_1460_);
v___x_1465_ = v___x_1358_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1460_);
lean_ctor_set(v_reuseFailAlloc_1466_, 1, v_k_1454_);
lean_ctor_set(v_reuseFailAlloc_1466_, 2, v_v_1455_);
lean_ctor_set(v_reuseFailAlloc_1466_, 3, v___x_1463_);
lean_ctor_set(v_reuseFailAlloc_1466_, 4, v_r_1452_);
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
else
{
lean_object* v_k_1471_; lean_object* v_v_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1495_; 
v_k_1471_ = lean_ctor_get(v_r_1356_, 1);
v_v_1472_ = lean_ctor_get(v_r_1356_, 2);
v_isSharedCheck_1495_ = !lean_is_exclusive(v_r_1356_);
if (v_isSharedCheck_1495_ == 0)
{
lean_object* v_unused_1496_; lean_object* v_unused_1497_; lean_object* v_unused_1498_; 
v_unused_1496_ = lean_ctor_get(v_r_1356_, 4);
lean_dec(v_unused_1496_);
v_unused_1497_ = lean_ctor_get(v_r_1356_, 3);
lean_dec(v_unused_1497_);
v_unused_1498_ = lean_ctor_get(v_r_1356_, 0);
lean_dec(v_unused_1498_);
v___x_1474_ = v_r_1356_;
v_isShared_1475_ = v_isSharedCheck_1495_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_v_1472_);
lean_inc(v_k_1471_);
lean_dec(v_r_1356_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1495_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v_k_1476_; lean_object* v_v_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1491_; 
v_k_1476_ = lean_ctor_get(v_l_1451_, 1);
v_v_1477_ = lean_ctor_get(v_l_1451_, 2);
v_isSharedCheck_1491_ = !lean_is_exclusive(v_l_1451_);
if (v_isSharedCheck_1491_ == 0)
{
lean_object* v_unused_1492_; lean_object* v_unused_1493_; lean_object* v_unused_1494_; 
v_unused_1492_ = lean_ctor_get(v_l_1451_, 4);
lean_dec(v_unused_1492_);
v_unused_1493_ = lean_ctor_get(v_l_1451_, 3);
lean_dec(v_unused_1493_);
v_unused_1494_ = lean_ctor_get(v_l_1451_, 0);
lean_dec(v_unused_1494_);
v___x_1479_ = v_l_1451_;
v_isShared_1480_ = v_isSharedCheck_1491_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_v_1477_);
lean_inc(v_k_1476_);
lean_dec(v_l_1451_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1491_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1481_; lean_object* v___x_1483_; 
v___x_1481_ = lean_unsigned_to_nat(3u);
if (v_isShared_1480_ == 0)
{
lean_ctor_set(v___x_1479_, 4, v_r_1452_);
lean_ctor_set(v___x_1479_, 3, v_r_1452_);
lean_ctor_set(v___x_1479_, 2, v_v_1354_);
lean_ctor_set(v___x_1479_, 1, v_k_1353_);
lean_ctor_set(v___x_1479_, 0, v___x_1362_);
v___x_1483_ = v___x_1479_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1362_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v_k_1353_);
lean_ctor_set(v_reuseFailAlloc_1490_, 2, v_v_1354_);
lean_ctor_set(v_reuseFailAlloc_1490_, 3, v_r_1452_);
lean_ctor_set(v_reuseFailAlloc_1490_, 4, v_r_1452_);
v___x_1483_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
lean_object* v___x_1485_; 
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 3, v_r_1452_);
lean_ctor_set(v___x_1474_, 0, v___x_1362_);
v___x_1485_ = v___x_1474_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1362_);
lean_ctor_set(v_reuseFailAlloc_1489_, 1, v_k_1471_);
lean_ctor_set(v_reuseFailAlloc_1489_, 2, v_v_1472_);
lean_ctor_set(v_reuseFailAlloc_1489_, 3, v_r_1452_);
lean_ctor_set(v_reuseFailAlloc_1489_, 4, v_r_1452_);
v___x_1485_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
lean_object* v___x_1487_; 
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 4, v___x_1485_);
lean_ctor_set(v___x_1358_, 3, v___x_1483_);
lean_ctor_set(v___x_1358_, 2, v_v_1477_);
lean_ctor_set(v___x_1358_, 1, v_k_1476_);
lean_ctor_set(v___x_1358_, 0, v___x_1481_);
v___x_1487_ = v___x_1358_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v___x_1481_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v_k_1476_);
lean_ctor_set(v_reuseFailAlloc_1488_, 2, v_v_1477_);
lean_ctor_set(v_reuseFailAlloc_1488_, 3, v___x_1483_);
lean_ctor_set(v_reuseFailAlloc_1488_, 4, v___x_1485_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1499_; 
v_r_1499_ = lean_ctor_get(v_r_1356_, 4);
lean_inc(v_r_1499_);
if (lean_obj_tag(v_r_1499_) == 0)
{
lean_object* v_k_1500_; lean_object* v_v_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1512_; 
v_k_1500_ = lean_ctor_get(v_r_1356_, 1);
v_v_1501_ = lean_ctor_get(v_r_1356_, 2);
v_isSharedCheck_1512_ = !lean_is_exclusive(v_r_1356_);
if (v_isSharedCheck_1512_ == 0)
{
lean_object* v_unused_1513_; lean_object* v_unused_1514_; lean_object* v_unused_1515_; 
v_unused_1513_ = lean_ctor_get(v_r_1356_, 4);
lean_dec(v_unused_1513_);
v_unused_1514_ = lean_ctor_get(v_r_1356_, 3);
lean_dec(v_unused_1514_);
v_unused_1515_ = lean_ctor_get(v_r_1356_, 0);
lean_dec(v_unused_1515_);
v___x_1503_ = v_r_1356_;
v_isShared_1504_ = v_isSharedCheck_1512_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_v_1501_);
lean_inc(v_k_1500_);
lean_dec(v_r_1356_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1512_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1505_; lean_object* v___x_1507_; 
v___x_1505_ = lean_unsigned_to_nat(3u);
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 4, v_l_1451_);
lean_ctor_set(v___x_1503_, 2, v_v_1354_);
lean_ctor_set(v___x_1503_, 1, v_k_1353_);
lean_ctor_set(v___x_1503_, 0, v___x_1362_);
v___x_1507_ = v___x_1503_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1362_);
lean_ctor_set(v_reuseFailAlloc_1511_, 1, v_k_1353_);
lean_ctor_set(v_reuseFailAlloc_1511_, 2, v_v_1354_);
lean_ctor_set(v_reuseFailAlloc_1511_, 3, v_l_1451_);
lean_ctor_set(v_reuseFailAlloc_1511_, 4, v_l_1451_);
v___x_1507_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
lean_object* v___x_1509_; 
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 4, v_r_1499_);
lean_ctor_set(v___x_1358_, 3, v___x_1507_);
lean_ctor_set(v___x_1358_, 2, v_v_1501_);
lean_ctor_set(v___x_1358_, 1, v_k_1500_);
lean_ctor_set(v___x_1358_, 0, v___x_1505_);
v___x_1509_ = v___x_1358_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1505_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v_k_1500_);
lean_ctor_set(v_reuseFailAlloc_1510_, 2, v_v_1501_);
lean_ctor_set(v_reuseFailAlloc_1510_, 3, v___x_1507_);
lean_ctor_set(v_reuseFailAlloc_1510_, 4, v_r_1499_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
else
{
lean_object* v_size_1516_; lean_object* v_k_1517_; lean_object* v_v_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1529_; 
v_size_1516_ = lean_ctor_get(v_r_1356_, 0);
v_k_1517_ = lean_ctor_get(v_r_1356_, 1);
v_v_1518_ = lean_ctor_get(v_r_1356_, 2);
v_isSharedCheck_1529_ = !lean_is_exclusive(v_r_1356_);
if (v_isSharedCheck_1529_ == 0)
{
lean_object* v_unused_1530_; lean_object* v_unused_1531_; 
v_unused_1530_ = lean_ctor_get(v_r_1356_, 4);
lean_dec(v_unused_1530_);
v_unused_1531_ = lean_ctor_get(v_r_1356_, 3);
lean_dec(v_unused_1531_);
v___x_1520_ = v_r_1356_;
v_isShared_1521_ = v_isSharedCheck_1529_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_v_1518_);
lean_inc(v_k_1517_);
lean_inc(v_size_1516_);
lean_dec(v_r_1356_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1529_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1523_; 
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 3, v_r_1499_);
v___x_1523_ = v___x_1520_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_size_1516_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v_k_1517_);
lean_ctor_set(v_reuseFailAlloc_1528_, 2, v_v_1518_);
lean_ctor_set(v_reuseFailAlloc_1528_, 3, v_r_1499_);
lean_ctor_set(v_reuseFailAlloc_1528_, 4, v_r_1499_);
v___x_1523_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
lean_object* v___x_1524_; lean_object* v___x_1526_; 
v___x_1524_ = lean_unsigned_to_nat(2u);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 4, v___x_1523_);
lean_ctor_set(v___x_1358_, 3, v_r_1499_);
lean_ctor_set(v___x_1358_, 0, v___x_1524_);
v___x_1526_ = v___x_1358_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___x_1524_);
lean_ctor_set(v_reuseFailAlloc_1527_, 1, v_k_1353_);
lean_ctor_set(v_reuseFailAlloc_1527_, 2, v_v_1354_);
lean_ctor_set(v_reuseFailAlloc_1527_, 3, v_r_1499_);
lean_ctor_set(v_reuseFailAlloc_1527_, 4, v___x_1523_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
}
}
}
else
{
lean_object* v___x_1533_; 
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 3, v_r_1356_);
lean_ctor_set(v___x_1358_, 0, v___x_1362_);
v___x_1533_ = v___x_1358_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v___x_1362_);
lean_ctor_set(v_reuseFailAlloc_1534_, 1, v_k_1353_);
lean_ctor_set(v_reuseFailAlloc_1534_, 2, v_v_1354_);
lean_ctor_set(v_reuseFailAlloc_1534_, 3, v_r_1356_);
lean_ctor_set(v_reuseFailAlloc_1534_, 4, v_r_1356_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
}
case 1:
{
lean_del_object(v___x_1358_);
lean_dec(v_v_1354_);
lean_dec(v_k_1353_);
if (lean_obj_tag(v_l_1355_) == 0)
{
if (lean_obj_tag(v_r_1356_) == 0)
{
lean_object* v_size_1535_; lean_object* v_k_1536_; lean_object* v_v_1537_; lean_object* v_l_1538_; lean_object* v_r_1539_; lean_object* v_size_1540_; lean_object* v_k_1541_; lean_object* v_v_1542_; lean_object* v_l_1543_; lean_object* v_r_1544_; lean_object* v___x_1545_; uint8_t v___x_1546_; 
v_size_1535_ = lean_ctor_get(v_l_1355_, 0);
v_k_1536_ = lean_ctor_get(v_l_1355_, 1);
v_v_1537_ = lean_ctor_get(v_l_1355_, 2);
v_l_1538_ = lean_ctor_get(v_l_1355_, 3);
v_r_1539_ = lean_ctor_get(v_l_1355_, 4);
lean_inc(v_r_1539_);
v_size_1540_ = lean_ctor_get(v_r_1356_, 0);
v_k_1541_ = lean_ctor_get(v_r_1356_, 1);
v_v_1542_ = lean_ctor_get(v_r_1356_, 2);
v_l_1543_ = lean_ctor_get(v_r_1356_, 3);
lean_inc(v_l_1543_);
v_r_1544_ = lean_ctor_get(v_r_1356_, 4);
v___x_1545_ = lean_unsigned_to_nat(1u);
v___x_1546_ = lean_nat_dec_lt(v_size_1535_, v_size_1540_);
if (v___x_1546_ == 0)
{
lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1682_; 
lean_inc(v_l_1538_);
lean_inc(v_v_1537_);
lean_inc(v_k_1536_);
v_isSharedCheck_1682_ = !lean_is_exclusive(v_l_1355_);
if (v_isSharedCheck_1682_ == 0)
{
lean_object* v_unused_1683_; lean_object* v_unused_1684_; lean_object* v_unused_1685_; lean_object* v_unused_1686_; lean_object* v_unused_1687_; 
v_unused_1683_ = lean_ctor_get(v_l_1355_, 4);
lean_dec(v_unused_1683_);
v_unused_1684_ = lean_ctor_get(v_l_1355_, 3);
lean_dec(v_unused_1684_);
v_unused_1685_ = lean_ctor_get(v_l_1355_, 2);
lean_dec(v_unused_1685_);
v_unused_1686_ = lean_ctor_get(v_l_1355_, 1);
lean_dec(v_unused_1686_);
v_unused_1687_ = lean_ctor_get(v_l_1355_, 0);
lean_dec(v_unused_1687_);
v___x_1548_ = v_l_1355_;
v_isShared_1549_ = v_isSharedCheck_1682_;
goto v_resetjp_1547_;
}
else
{
lean_dec(v_l_1355_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1682_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1550_; lean_object* v_tree_1551_; 
v___x_1550_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_1536_, v_v_1537_, v_l_1538_, v_r_1539_);
v_tree_1551_ = lean_ctor_get(v___x_1550_, 2);
if (lean_obj_tag(v_tree_1551_) == 0)
{
lean_object* v_k_1552_; lean_object* v_v_1553_; lean_object* v_size_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; uint8_t v___x_1557_; 
lean_inc_ref(v_tree_1551_);
v_k_1552_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_k_1552_);
v_v_1553_ = lean_ctor_get(v___x_1550_, 1);
lean_inc(v_v_1553_);
lean_dec_ref(v___x_1550_);
v_size_1554_ = lean_ctor_get(v_tree_1551_, 0);
v___x_1555_ = lean_unsigned_to_nat(3u);
v___x_1556_ = lean_nat_mul(v___x_1555_, v_size_1554_);
v___x_1557_ = lean_nat_dec_lt(v___x_1556_, v_size_1540_);
lean_dec(v___x_1556_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1561_; 
lean_dec(v_l_1543_);
v___x_1558_ = lean_nat_add(v___x_1545_, v_size_1554_);
v___x_1559_ = lean_nat_add(v___x_1558_, v_size_1540_);
lean_dec(v___x_1558_);
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 4, v_r_1356_);
lean_ctor_set(v___x_1548_, 3, v_tree_1551_);
lean_ctor_set(v___x_1548_, 2, v_v_1553_);
lean_ctor_set(v___x_1548_, 1, v_k_1552_);
lean_ctor_set(v___x_1548_, 0, v___x_1559_);
v___x_1561_ = v___x_1548_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1559_);
lean_ctor_set(v_reuseFailAlloc_1562_, 1, v_k_1552_);
lean_ctor_set(v_reuseFailAlloc_1562_, 2, v_v_1553_);
lean_ctor_set(v_reuseFailAlloc_1562_, 3, v_tree_1551_);
lean_ctor_set(v_reuseFailAlloc_1562_, 4, v_r_1356_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
else
{
lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1617_; 
lean_inc(v_r_1544_);
lean_inc(v_v_1542_);
lean_inc(v_k_1541_);
lean_inc(v_size_1540_);
v_isSharedCheck_1617_ = !lean_is_exclusive(v_r_1356_);
if (v_isSharedCheck_1617_ == 0)
{
lean_object* v_unused_1618_; lean_object* v_unused_1619_; lean_object* v_unused_1620_; lean_object* v_unused_1621_; lean_object* v_unused_1622_; 
v_unused_1618_ = lean_ctor_get(v_r_1356_, 4);
lean_dec(v_unused_1618_);
v_unused_1619_ = lean_ctor_get(v_r_1356_, 3);
lean_dec(v_unused_1619_);
v_unused_1620_ = lean_ctor_get(v_r_1356_, 2);
lean_dec(v_unused_1620_);
v_unused_1621_ = lean_ctor_get(v_r_1356_, 1);
lean_dec(v_unused_1621_);
v_unused_1622_ = lean_ctor_get(v_r_1356_, 0);
lean_dec(v_unused_1622_);
v___x_1564_ = v_r_1356_;
v_isShared_1565_ = v_isSharedCheck_1617_;
goto v_resetjp_1563_;
}
else
{
lean_dec(v_r_1356_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1617_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v_size_1566_; lean_object* v_k_1567_; lean_object* v_v_1568_; lean_object* v_l_1569_; lean_object* v_r_1570_; lean_object* v_size_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; uint8_t v___x_1574_; 
v_size_1566_ = lean_ctor_get(v_l_1543_, 0);
v_k_1567_ = lean_ctor_get(v_l_1543_, 1);
v_v_1568_ = lean_ctor_get(v_l_1543_, 2);
v_l_1569_ = lean_ctor_get(v_l_1543_, 3);
v_r_1570_ = lean_ctor_get(v_l_1543_, 4);
v_size_1571_ = lean_ctor_get(v_r_1544_, 0);
v___x_1572_ = lean_unsigned_to_nat(2u);
v___x_1573_ = lean_nat_mul(v___x_1572_, v_size_1571_);
v___x_1574_ = lean_nat_dec_lt(v_size_1566_, v___x_1573_);
lean_dec(v___x_1573_);
if (v___x_1574_ == 0)
{
lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1602_; 
lean_inc(v_r_1570_);
lean_inc(v_l_1569_);
lean_inc(v_v_1568_);
lean_inc(v_k_1567_);
v_isSharedCheck_1602_ = !lean_is_exclusive(v_l_1543_);
if (v_isSharedCheck_1602_ == 0)
{
lean_object* v_unused_1603_; lean_object* v_unused_1604_; lean_object* v_unused_1605_; lean_object* v_unused_1606_; lean_object* v_unused_1607_; 
v_unused_1603_ = lean_ctor_get(v_l_1543_, 4);
lean_dec(v_unused_1603_);
v_unused_1604_ = lean_ctor_get(v_l_1543_, 3);
lean_dec(v_unused_1604_);
v_unused_1605_ = lean_ctor_get(v_l_1543_, 2);
lean_dec(v_unused_1605_);
v_unused_1606_ = lean_ctor_get(v_l_1543_, 1);
lean_dec(v_unused_1606_);
v_unused_1607_ = lean_ctor_get(v_l_1543_, 0);
lean_dec(v_unused_1607_);
v___x_1576_ = v_l_1543_;
v_isShared_1577_ = v_isSharedCheck_1602_;
goto v_resetjp_1575_;
}
else
{
lean_dec(v_l_1543_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1602_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v___y_1592_; 
v___x_1578_ = lean_nat_add(v___x_1545_, v_size_1554_);
v___x_1579_ = lean_nat_add(v___x_1578_, v_size_1540_);
lean_dec(v_size_1540_);
if (lean_obj_tag(v_l_1569_) == 0)
{
lean_object* v_size_1600_; 
v_size_1600_ = lean_ctor_get(v_l_1569_, 0);
lean_inc(v_size_1600_);
v___y_1592_ = v_size_1600_;
goto v___jp_1591_;
}
else
{
lean_object* v___x_1601_; 
v___x_1601_ = lean_unsigned_to_nat(0u);
v___y_1592_ = v___x_1601_;
goto v___jp_1591_;
}
v___jp_1580_:
{
lean_object* v___x_1584_; lean_object* v___x_1586_; 
v___x_1584_ = lean_nat_add(v___y_1582_, v___y_1583_);
lean_dec(v___y_1583_);
lean_dec(v___y_1582_);
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 4, v_r_1544_);
lean_ctor_set(v___x_1576_, 3, v_r_1570_);
lean_ctor_set(v___x_1576_, 2, v_v_1542_);
lean_ctor_set(v___x_1576_, 1, v_k_1541_);
lean_ctor_set(v___x_1576_, 0, v___x_1584_);
v___x_1586_ = v___x_1576_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1584_);
lean_ctor_set(v_reuseFailAlloc_1590_, 1, v_k_1541_);
lean_ctor_set(v_reuseFailAlloc_1590_, 2, v_v_1542_);
lean_ctor_set(v_reuseFailAlloc_1590_, 3, v_r_1570_);
lean_ctor_set(v_reuseFailAlloc_1590_, 4, v_r_1544_);
v___x_1586_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
lean_object* v___x_1588_; 
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 4, v___x_1586_);
lean_ctor_set(v___x_1564_, 3, v___y_1581_);
lean_ctor_set(v___x_1564_, 2, v_v_1568_);
lean_ctor_set(v___x_1564_, 1, v_k_1567_);
lean_ctor_set(v___x_1564_, 0, v___x_1579_);
v___x_1588_ = v___x_1564_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1579_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v_k_1567_);
lean_ctor_set(v_reuseFailAlloc_1589_, 2, v_v_1568_);
lean_ctor_set(v_reuseFailAlloc_1589_, 3, v___y_1581_);
lean_ctor_set(v_reuseFailAlloc_1589_, 4, v___x_1586_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
v___jp_1591_:
{
lean_object* v___x_1593_; lean_object* v___x_1595_; 
v___x_1593_ = lean_nat_add(v___x_1578_, v___y_1592_);
lean_dec(v___y_1592_);
lean_dec(v___x_1578_);
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 4, v_l_1569_);
lean_ctor_set(v___x_1548_, 3, v_tree_1551_);
lean_ctor_set(v___x_1548_, 2, v_v_1553_);
lean_ctor_set(v___x_1548_, 1, v_k_1552_);
lean_ctor_set(v___x_1548_, 0, v___x_1593_);
v___x_1595_ = v___x_1548_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v___x_1593_);
lean_ctor_set(v_reuseFailAlloc_1599_, 1, v_k_1552_);
lean_ctor_set(v_reuseFailAlloc_1599_, 2, v_v_1553_);
lean_ctor_set(v_reuseFailAlloc_1599_, 3, v_tree_1551_);
lean_ctor_set(v_reuseFailAlloc_1599_, 4, v_l_1569_);
v___x_1595_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
lean_object* v___x_1596_; 
v___x_1596_ = lean_nat_add(v___x_1545_, v_size_1571_);
if (lean_obj_tag(v_r_1570_) == 0)
{
lean_object* v_size_1597_; 
v_size_1597_ = lean_ctor_get(v_r_1570_, 0);
lean_inc(v_size_1597_);
v___y_1581_ = v___x_1595_;
v___y_1582_ = v___x_1596_;
v___y_1583_ = v_size_1597_;
goto v___jp_1580_;
}
else
{
lean_object* v___x_1598_; 
v___x_1598_ = lean_unsigned_to_nat(0u);
v___y_1581_ = v___x_1595_;
v___y_1582_ = v___x_1596_;
v___y_1583_ = v___x_1598_;
goto v___jp_1580_;
}
}
}
}
}
else
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1612_; 
v___x_1608_ = lean_nat_add(v___x_1545_, v_size_1554_);
v___x_1609_ = lean_nat_add(v___x_1608_, v_size_1540_);
lean_dec(v_size_1540_);
v___x_1610_ = lean_nat_add(v___x_1608_, v_size_1566_);
lean_dec(v___x_1608_);
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 4, v_l_1543_);
lean_ctor_set(v___x_1564_, 3, v_tree_1551_);
lean_ctor_set(v___x_1564_, 2, v_v_1553_);
lean_ctor_set(v___x_1564_, 1, v_k_1552_);
lean_ctor_set(v___x_1564_, 0, v___x_1610_);
v___x_1612_ = v___x_1564_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v___x_1610_);
lean_ctor_set(v_reuseFailAlloc_1616_, 1, v_k_1552_);
lean_ctor_set(v_reuseFailAlloc_1616_, 2, v_v_1553_);
lean_ctor_set(v_reuseFailAlloc_1616_, 3, v_tree_1551_);
lean_ctor_set(v_reuseFailAlloc_1616_, 4, v_l_1543_);
v___x_1612_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
lean_object* v___x_1614_; 
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 4, v_r_1544_);
lean_ctor_set(v___x_1548_, 3, v___x_1612_);
lean_ctor_set(v___x_1548_, 2, v_v_1542_);
lean_ctor_set(v___x_1548_, 1, v_k_1541_);
lean_ctor_set(v___x_1548_, 0, v___x_1609_);
v___x_1614_ = v___x_1548_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v___x_1609_);
lean_ctor_set(v_reuseFailAlloc_1615_, 1, v_k_1541_);
lean_ctor_set(v_reuseFailAlloc_1615_, 2, v_v_1542_);
lean_ctor_set(v_reuseFailAlloc_1615_, 3, v___x_1612_);
lean_ctor_set(v_reuseFailAlloc_1615_, 4, v_r_1544_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
}
}
}
else
{
lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1676_; 
lean_inc(v_r_1544_);
lean_inc(v_v_1542_);
lean_inc(v_k_1541_);
lean_inc(v_size_1540_);
v_isSharedCheck_1676_ = !lean_is_exclusive(v_r_1356_);
if (v_isSharedCheck_1676_ == 0)
{
lean_object* v_unused_1677_; lean_object* v_unused_1678_; lean_object* v_unused_1679_; lean_object* v_unused_1680_; lean_object* v_unused_1681_; 
v_unused_1677_ = lean_ctor_get(v_r_1356_, 4);
lean_dec(v_unused_1677_);
v_unused_1678_ = lean_ctor_get(v_r_1356_, 3);
lean_dec(v_unused_1678_);
v_unused_1679_ = lean_ctor_get(v_r_1356_, 2);
lean_dec(v_unused_1679_);
v_unused_1680_ = lean_ctor_get(v_r_1356_, 1);
lean_dec(v_unused_1680_);
v_unused_1681_ = lean_ctor_get(v_r_1356_, 0);
lean_dec(v_unused_1681_);
v___x_1624_ = v_r_1356_;
v_isShared_1625_ = v_isSharedCheck_1676_;
goto v_resetjp_1623_;
}
else
{
lean_dec(v_r_1356_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1676_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
if (lean_obj_tag(v_l_1543_) == 0)
{
if (lean_obj_tag(v_r_1544_) == 0)
{
lean_object* v_k_1626_; lean_object* v_v_1627_; lean_object* v_size_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1632_; 
lean_inc(v_tree_1551_);
v_k_1626_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_k_1626_);
v_v_1627_ = lean_ctor_get(v___x_1550_, 1);
lean_inc(v_v_1627_);
lean_dec_ref(v___x_1550_);
v_size_1628_ = lean_ctor_get(v_l_1543_, 0);
v___x_1629_ = lean_nat_add(v___x_1545_, v_size_1540_);
lean_dec(v_size_1540_);
v___x_1630_ = lean_nat_add(v___x_1545_, v_size_1628_);
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 4, v_l_1543_);
lean_ctor_set(v___x_1624_, 3, v_tree_1551_);
lean_ctor_set(v___x_1624_, 2, v_v_1627_);
lean_ctor_set(v___x_1624_, 1, v_k_1626_);
lean_ctor_set(v___x_1624_, 0, v___x_1630_);
v___x_1632_ = v___x_1624_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1630_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v_k_1626_);
lean_ctor_set(v_reuseFailAlloc_1636_, 2, v_v_1627_);
lean_ctor_set(v_reuseFailAlloc_1636_, 3, v_tree_1551_);
lean_ctor_set(v_reuseFailAlloc_1636_, 4, v_l_1543_);
v___x_1632_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
lean_object* v___x_1634_; 
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 4, v_r_1544_);
lean_ctor_set(v___x_1548_, 3, v___x_1632_);
lean_ctor_set(v___x_1548_, 2, v_v_1542_);
lean_ctor_set(v___x_1548_, 1, v_k_1541_);
lean_ctor_set(v___x_1548_, 0, v___x_1629_);
v___x_1634_ = v___x_1548_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v___x_1629_);
lean_ctor_set(v_reuseFailAlloc_1635_, 1, v_k_1541_);
lean_ctor_set(v_reuseFailAlloc_1635_, 2, v_v_1542_);
lean_ctor_set(v_reuseFailAlloc_1635_, 3, v___x_1632_);
lean_ctor_set(v_reuseFailAlloc_1635_, 4, v_r_1544_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
else
{
lean_object* v_k_1637_; lean_object* v_v_1638_; lean_object* v_k_1639_; lean_object* v_v_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1654_; 
lean_dec(v_size_1540_);
v_k_1637_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_k_1637_);
v_v_1638_ = lean_ctor_get(v___x_1550_, 1);
lean_inc(v_v_1638_);
lean_dec_ref(v___x_1550_);
v_k_1639_ = lean_ctor_get(v_l_1543_, 1);
v_v_1640_ = lean_ctor_get(v_l_1543_, 2);
v_isSharedCheck_1654_ = !lean_is_exclusive(v_l_1543_);
if (v_isSharedCheck_1654_ == 0)
{
lean_object* v_unused_1655_; lean_object* v_unused_1656_; lean_object* v_unused_1657_; 
v_unused_1655_ = lean_ctor_get(v_l_1543_, 4);
lean_dec(v_unused_1655_);
v_unused_1656_ = lean_ctor_get(v_l_1543_, 3);
lean_dec(v_unused_1656_);
v_unused_1657_ = lean_ctor_get(v_l_1543_, 0);
lean_dec(v_unused_1657_);
v___x_1642_ = v_l_1543_;
v_isShared_1643_ = v_isSharedCheck_1654_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_v_1640_);
lean_inc(v_k_1639_);
lean_dec(v_l_1543_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1654_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1644_; lean_object* v___x_1646_; 
v___x_1644_ = lean_unsigned_to_nat(3u);
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 4, v_r_1544_);
lean_ctor_set(v___x_1642_, 3, v_r_1544_);
lean_ctor_set(v___x_1642_, 2, v_v_1638_);
lean_ctor_set(v___x_1642_, 1, v_k_1637_);
lean_ctor_set(v___x_1642_, 0, v___x_1545_);
v___x_1646_ = v___x_1642_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v___x_1545_);
lean_ctor_set(v_reuseFailAlloc_1653_, 1, v_k_1637_);
lean_ctor_set(v_reuseFailAlloc_1653_, 2, v_v_1638_);
lean_ctor_set(v_reuseFailAlloc_1653_, 3, v_r_1544_);
lean_ctor_set(v_reuseFailAlloc_1653_, 4, v_r_1544_);
v___x_1646_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
lean_object* v___x_1648_; 
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 3, v_r_1544_);
lean_ctor_set(v___x_1624_, 0, v___x_1545_);
v___x_1648_ = v___x_1624_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v___x_1545_);
lean_ctor_set(v_reuseFailAlloc_1652_, 1, v_k_1541_);
lean_ctor_set(v_reuseFailAlloc_1652_, 2, v_v_1542_);
lean_ctor_set(v_reuseFailAlloc_1652_, 3, v_r_1544_);
lean_ctor_set(v_reuseFailAlloc_1652_, 4, v_r_1544_);
v___x_1648_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
lean_object* v___x_1650_; 
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 4, v___x_1648_);
lean_ctor_set(v___x_1548_, 3, v___x_1646_);
lean_ctor_set(v___x_1548_, 2, v_v_1640_);
lean_ctor_set(v___x_1548_, 1, v_k_1639_);
lean_ctor_set(v___x_1548_, 0, v___x_1644_);
v___x_1650_ = v___x_1548_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v___x_1644_);
lean_ctor_set(v_reuseFailAlloc_1651_, 1, v_k_1639_);
lean_ctor_set(v_reuseFailAlloc_1651_, 2, v_v_1640_);
lean_ctor_set(v_reuseFailAlloc_1651_, 3, v___x_1646_);
lean_ctor_set(v_reuseFailAlloc_1651_, 4, v___x_1648_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1544_) == 0)
{
lean_object* v_k_1658_; lean_object* v_v_1659_; lean_object* v___x_1660_; lean_object* v___x_1662_; 
lean_dec(v_size_1540_);
v_k_1658_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_k_1658_);
v_v_1659_ = lean_ctor_get(v___x_1550_, 1);
lean_inc(v_v_1659_);
lean_dec_ref(v___x_1550_);
v___x_1660_ = lean_unsigned_to_nat(3u);
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 4, v_l_1543_);
lean_ctor_set(v___x_1624_, 2, v_v_1659_);
lean_ctor_set(v___x_1624_, 1, v_k_1658_);
lean_ctor_set(v___x_1624_, 0, v___x_1545_);
v___x_1662_ = v___x_1624_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1545_);
lean_ctor_set(v_reuseFailAlloc_1666_, 1, v_k_1658_);
lean_ctor_set(v_reuseFailAlloc_1666_, 2, v_v_1659_);
lean_ctor_set(v_reuseFailAlloc_1666_, 3, v_l_1543_);
lean_ctor_set(v_reuseFailAlloc_1666_, 4, v_l_1543_);
v___x_1662_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
lean_object* v___x_1664_; 
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 4, v_r_1544_);
lean_ctor_set(v___x_1548_, 3, v___x_1662_);
lean_ctor_set(v___x_1548_, 2, v_v_1542_);
lean_ctor_set(v___x_1548_, 1, v_k_1541_);
lean_ctor_set(v___x_1548_, 0, v___x_1660_);
v___x_1664_ = v___x_1548_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v___x_1660_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v_k_1541_);
lean_ctor_set(v_reuseFailAlloc_1665_, 2, v_v_1542_);
lean_ctor_set(v_reuseFailAlloc_1665_, 3, v___x_1662_);
lean_ctor_set(v_reuseFailAlloc_1665_, 4, v_r_1544_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
else
{
lean_object* v_k_1667_; lean_object* v_v_1668_; lean_object* v___x_1670_; 
v_k_1667_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_k_1667_);
v_v_1668_ = lean_ctor_get(v___x_1550_, 1);
lean_inc(v_v_1668_);
lean_dec_ref(v___x_1550_);
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 3, v_r_1544_);
v___x_1670_ = v___x_1624_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_size_1540_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v_k_1541_);
lean_ctor_set(v_reuseFailAlloc_1675_, 2, v_v_1542_);
lean_ctor_set(v_reuseFailAlloc_1675_, 3, v_r_1544_);
lean_ctor_set(v_reuseFailAlloc_1675_, 4, v_r_1544_);
v___x_1670_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
lean_object* v___x_1671_; lean_object* v___x_1673_; 
v___x_1671_ = lean_unsigned_to_nat(2u);
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 4, v___x_1670_);
lean_ctor_set(v___x_1548_, 3, v_r_1544_);
lean_ctor_set(v___x_1548_, 2, v_v_1668_);
lean_ctor_set(v___x_1548_, 1, v_k_1667_);
lean_ctor_set(v___x_1548_, 0, v___x_1671_);
v___x_1673_ = v___x_1548_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v___x_1671_);
lean_ctor_set(v_reuseFailAlloc_1674_, 1, v_k_1667_);
lean_ctor_set(v_reuseFailAlloc_1674_, 2, v_v_1668_);
lean_ctor_set(v_reuseFailAlloc_1674_, 3, v_r_1544_);
lean_ctor_set(v_reuseFailAlloc_1674_, 4, v___x_1670_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
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
lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1840_; 
lean_inc(v_r_1544_);
lean_inc(v_v_1542_);
lean_inc(v_k_1541_);
v_isSharedCheck_1840_ = !lean_is_exclusive(v_r_1356_);
if (v_isSharedCheck_1840_ == 0)
{
lean_object* v_unused_1841_; lean_object* v_unused_1842_; lean_object* v_unused_1843_; lean_object* v_unused_1844_; lean_object* v_unused_1845_; 
v_unused_1841_ = lean_ctor_get(v_r_1356_, 4);
lean_dec(v_unused_1841_);
v_unused_1842_ = lean_ctor_get(v_r_1356_, 3);
lean_dec(v_unused_1842_);
v_unused_1843_ = lean_ctor_get(v_r_1356_, 2);
lean_dec(v_unused_1843_);
v_unused_1844_ = lean_ctor_get(v_r_1356_, 1);
lean_dec(v_unused_1844_);
v_unused_1845_ = lean_ctor_get(v_r_1356_, 0);
lean_dec(v_unused_1845_);
v___x_1689_ = v_r_1356_;
v_isShared_1690_ = v_isSharedCheck_1840_;
goto v_resetjp_1688_;
}
else
{
lean_dec(v_r_1356_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1840_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1691_; lean_object* v_tree_1692_; 
v___x_1691_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_1541_, v_v_1542_, v_l_1543_, v_r_1544_);
v_tree_1692_ = lean_ctor_get(v___x_1691_, 2);
lean_inc(v_tree_1692_);
if (lean_obj_tag(v_tree_1692_) == 0)
{
lean_object* v_k_1693_; lean_object* v_v_1694_; lean_object* v_size_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; uint8_t v___x_1698_; 
v_k_1693_ = lean_ctor_get(v___x_1691_, 0);
lean_inc(v_k_1693_);
v_v_1694_ = lean_ctor_get(v___x_1691_, 1);
lean_inc(v_v_1694_);
lean_dec_ref(v___x_1691_);
v_size_1695_ = lean_ctor_get(v_tree_1692_, 0);
v___x_1696_ = lean_unsigned_to_nat(3u);
v___x_1697_ = lean_nat_mul(v___x_1696_, v_size_1695_);
v___x_1698_ = lean_nat_dec_lt(v___x_1697_, v_size_1535_);
lean_dec(v___x_1697_);
if (v___x_1698_ == 0)
{
lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1702_; 
lean_dec(v_r_1539_);
v___x_1699_ = lean_nat_add(v___x_1545_, v_size_1535_);
v___x_1700_ = lean_nat_add(v___x_1699_, v_size_1695_);
lean_dec(v___x_1699_);
if (v_isShared_1690_ == 0)
{
lean_ctor_set(v___x_1689_, 4, v_tree_1692_);
lean_ctor_set(v___x_1689_, 3, v_l_1355_);
lean_ctor_set(v___x_1689_, 2, v_v_1694_);
lean_ctor_set(v___x_1689_, 1, v_k_1693_);
lean_ctor_set(v___x_1689_, 0, v___x_1700_);
v___x_1702_ = v___x_1689_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v___x_1700_);
lean_ctor_set(v_reuseFailAlloc_1703_, 1, v_k_1693_);
lean_ctor_set(v_reuseFailAlloc_1703_, 2, v_v_1694_);
lean_ctor_set(v_reuseFailAlloc_1703_, 3, v_l_1355_);
lean_ctor_set(v_reuseFailAlloc_1703_, 4, v_tree_1692_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
else
{
lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1769_; 
lean_inc(v_l_1538_);
lean_inc(v_v_1537_);
lean_inc(v_k_1536_);
lean_inc(v_size_1535_);
v_isSharedCheck_1769_ = !lean_is_exclusive(v_l_1355_);
if (v_isSharedCheck_1769_ == 0)
{
lean_object* v_unused_1770_; lean_object* v_unused_1771_; lean_object* v_unused_1772_; lean_object* v_unused_1773_; lean_object* v_unused_1774_; 
v_unused_1770_ = lean_ctor_get(v_l_1355_, 4);
lean_dec(v_unused_1770_);
v_unused_1771_ = lean_ctor_get(v_l_1355_, 3);
lean_dec(v_unused_1771_);
v_unused_1772_ = lean_ctor_get(v_l_1355_, 2);
lean_dec(v_unused_1772_);
v_unused_1773_ = lean_ctor_get(v_l_1355_, 1);
lean_dec(v_unused_1773_);
v_unused_1774_ = lean_ctor_get(v_l_1355_, 0);
lean_dec(v_unused_1774_);
v___x_1705_ = v_l_1355_;
v_isShared_1706_ = v_isSharedCheck_1769_;
goto v_resetjp_1704_;
}
else
{
lean_dec(v_l_1355_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1769_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v_size_1707_; lean_object* v_size_1708_; lean_object* v_k_1709_; lean_object* v_v_1710_; lean_object* v_l_1711_; lean_object* v_r_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; uint8_t v___x_1715_; 
v_size_1707_ = lean_ctor_get(v_l_1538_, 0);
v_size_1708_ = lean_ctor_get(v_r_1539_, 0);
v_k_1709_ = lean_ctor_get(v_r_1539_, 1);
v_v_1710_ = lean_ctor_get(v_r_1539_, 2);
v_l_1711_ = lean_ctor_get(v_r_1539_, 3);
v_r_1712_ = lean_ctor_get(v_r_1539_, 4);
v___x_1713_ = lean_unsigned_to_nat(2u);
v___x_1714_ = lean_nat_mul(v___x_1713_, v_size_1707_);
v___x_1715_ = lean_nat_dec_lt(v_size_1708_, v___x_1714_);
lean_dec(v___x_1714_);
if (v___x_1715_ == 0)
{
lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1753_; 
lean_inc(v_r_1712_);
lean_inc(v_l_1711_);
lean_inc(v_v_1710_);
lean_inc(v_k_1709_);
lean_del_object(v___x_1705_);
v_isSharedCheck_1753_ = !lean_is_exclusive(v_r_1539_);
if (v_isSharedCheck_1753_ == 0)
{
lean_object* v_unused_1754_; lean_object* v_unused_1755_; lean_object* v_unused_1756_; lean_object* v_unused_1757_; lean_object* v_unused_1758_; 
v_unused_1754_ = lean_ctor_get(v_r_1539_, 4);
lean_dec(v_unused_1754_);
v_unused_1755_ = lean_ctor_get(v_r_1539_, 3);
lean_dec(v_unused_1755_);
v_unused_1756_ = lean_ctor_get(v_r_1539_, 2);
lean_dec(v_unused_1756_);
v_unused_1757_ = lean_ctor_get(v_r_1539_, 1);
lean_dec(v_unused_1757_);
v_unused_1758_ = lean_ctor_get(v_r_1539_, 0);
lean_dec(v_unused_1758_);
v___x_1717_ = v_r_1539_;
v_isShared_1718_ = v_isSharedCheck_1753_;
goto v_resetjp_1716_;
}
else
{
lean_dec(v_r_1539_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1753_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___x_1741_; lean_object* v___y_1743_; 
v___x_1719_ = lean_nat_add(v___x_1545_, v_size_1535_);
lean_dec(v_size_1535_);
v___x_1720_ = lean_nat_add(v___x_1719_, v_size_1695_);
lean_dec(v___x_1719_);
v___x_1741_ = lean_nat_add(v___x_1545_, v_size_1707_);
if (lean_obj_tag(v_l_1711_) == 0)
{
lean_object* v_size_1751_; 
v_size_1751_ = lean_ctor_get(v_l_1711_, 0);
lean_inc(v_size_1751_);
v___y_1743_ = v_size_1751_;
goto v___jp_1742_;
}
else
{
lean_object* v___x_1752_; 
v___x_1752_ = lean_unsigned_to_nat(0u);
v___y_1743_ = v___x_1752_;
goto v___jp_1742_;
}
v___jp_1721_:
{
lean_object* v___x_1725_; lean_object* v___x_1727_; 
v___x_1725_ = lean_nat_add(v___y_1723_, v___y_1724_);
lean_dec(v___y_1724_);
lean_dec(v___y_1723_);
lean_inc_ref(v_tree_1692_);
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 4, v_tree_1692_);
lean_ctor_set(v___x_1717_, 3, v_r_1712_);
lean_ctor_set(v___x_1717_, 2, v_v_1694_);
lean_ctor_set(v___x_1717_, 1, v_k_1693_);
lean_ctor_set(v___x_1717_, 0, v___x_1725_);
v___x_1727_ = v___x_1717_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1725_);
lean_ctor_set(v_reuseFailAlloc_1740_, 1, v_k_1693_);
lean_ctor_set(v_reuseFailAlloc_1740_, 2, v_v_1694_);
lean_ctor_set(v_reuseFailAlloc_1740_, 3, v_r_1712_);
lean_ctor_set(v_reuseFailAlloc_1740_, 4, v_tree_1692_);
v___x_1727_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1734_; 
v_isSharedCheck_1734_ = !lean_is_exclusive(v_tree_1692_);
if (v_isSharedCheck_1734_ == 0)
{
lean_object* v_unused_1735_; lean_object* v_unused_1736_; lean_object* v_unused_1737_; lean_object* v_unused_1738_; lean_object* v_unused_1739_; 
v_unused_1735_ = lean_ctor_get(v_tree_1692_, 4);
lean_dec(v_unused_1735_);
v_unused_1736_ = lean_ctor_get(v_tree_1692_, 3);
lean_dec(v_unused_1736_);
v_unused_1737_ = lean_ctor_get(v_tree_1692_, 2);
lean_dec(v_unused_1737_);
v_unused_1738_ = lean_ctor_get(v_tree_1692_, 1);
lean_dec(v_unused_1738_);
v_unused_1739_ = lean_ctor_get(v_tree_1692_, 0);
lean_dec(v_unused_1739_);
v___x_1729_ = v_tree_1692_;
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
else
{
lean_dec(v_tree_1692_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1732_; 
if (v_isShared_1730_ == 0)
{
lean_ctor_set(v___x_1729_, 4, v___x_1727_);
lean_ctor_set(v___x_1729_, 3, v___y_1722_);
lean_ctor_set(v___x_1729_, 2, v_v_1710_);
lean_ctor_set(v___x_1729_, 1, v_k_1709_);
lean_ctor_set(v___x_1729_, 0, v___x_1720_);
v___x_1732_ = v___x_1729_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v___x_1720_);
lean_ctor_set(v_reuseFailAlloc_1733_, 1, v_k_1709_);
lean_ctor_set(v_reuseFailAlloc_1733_, 2, v_v_1710_);
lean_ctor_set(v_reuseFailAlloc_1733_, 3, v___y_1722_);
lean_ctor_set(v_reuseFailAlloc_1733_, 4, v___x_1727_);
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
v___jp_1742_:
{
lean_object* v___x_1744_; lean_object* v___x_1746_; 
v___x_1744_ = lean_nat_add(v___x_1741_, v___y_1743_);
lean_dec(v___y_1743_);
lean_dec(v___x_1741_);
if (v_isShared_1690_ == 0)
{
lean_ctor_set(v___x_1689_, 4, v_l_1711_);
lean_ctor_set(v___x_1689_, 3, v_l_1538_);
lean_ctor_set(v___x_1689_, 2, v_v_1537_);
lean_ctor_set(v___x_1689_, 1, v_k_1536_);
lean_ctor_set(v___x_1689_, 0, v___x_1744_);
v___x_1746_ = v___x_1689_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1744_);
lean_ctor_set(v_reuseFailAlloc_1750_, 1, v_k_1536_);
lean_ctor_set(v_reuseFailAlloc_1750_, 2, v_v_1537_);
lean_ctor_set(v_reuseFailAlloc_1750_, 3, v_l_1538_);
lean_ctor_set(v_reuseFailAlloc_1750_, 4, v_l_1711_);
v___x_1746_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
lean_object* v___x_1747_; 
v___x_1747_ = lean_nat_add(v___x_1545_, v_size_1695_);
if (lean_obj_tag(v_r_1712_) == 0)
{
lean_object* v_size_1748_; 
v_size_1748_ = lean_ctor_get(v_r_1712_, 0);
lean_inc(v_size_1748_);
v___y_1722_ = v___x_1746_;
v___y_1723_ = v___x_1747_;
v___y_1724_ = v_size_1748_;
goto v___jp_1721_;
}
else
{
lean_object* v___x_1749_; 
v___x_1749_ = lean_unsigned_to_nat(0u);
v___y_1722_ = v___x_1746_;
v___y_1723_ = v___x_1747_;
v___y_1724_ = v___x_1749_;
goto v___jp_1721_;
}
}
}
}
}
else
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1764_; 
v___x_1759_ = lean_nat_add(v___x_1545_, v_size_1535_);
lean_dec(v_size_1535_);
v___x_1760_ = lean_nat_add(v___x_1759_, v_size_1695_);
lean_dec(v___x_1759_);
v___x_1761_ = lean_nat_add(v___x_1545_, v_size_1695_);
v___x_1762_ = lean_nat_add(v___x_1761_, v_size_1708_);
lean_dec(v___x_1761_);
if (v_isShared_1690_ == 0)
{
lean_ctor_set(v___x_1689_, 4, v_tree_1692_);
lean_ctor_set(v___x_1689_, 3, v_r_1539_);
lean_ctor_set(v___x_1689_, 2, v_v_1694_);
lean_ctor_set(v___x_1689_, 1, v_k_1693_);
lean_ctor_set(v___x_1689_, 0, v___x_1762_);
v___x_1764_ = v___x_1689_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1762_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v_k_1693_);
lean_ctor_set(v_reuseFailAlloc_1768_, 2, v_v_1694_);
lean_ctor_set(v_reuseFailAlloc_1768_, 3, v_r_1539_);
lean_ctor_set(v_reuseFailAlloc_1768_, 4, v_tree_1692_);
v___x_1764_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
lean_object* v___x_1766_; 
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 4, v___x_1764_);
lean_ctor_set(v___x_1705_, 0, v___x_1760_);
v___x_1766_ = v___x_1705_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1760_);
lean_ctor_set(v_reuseFailAlloc_1767_, 1, v_k_1536_);
lean_ctor_set(v_reuseFailAlloc_1767_, 2, v_v_1537_);
lean_ctor_set(v_reuseFailAlloc_1767_, 3, v_l_1538_);
lean_ctor_set(v_reuseFailAlloc_1767_, 4, v___x_1764_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_1538_) == 0)
{
lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1798_; 
lean_inc_ref(v_l_1538_);
lean_inc(v_v_1537_);
lean_inc(v_k_1536_);
lean_inc(v_size_1535_);
v_isSharedCheck_1798_ = !lean_is_exclusive(v_l_1355_);
if (v_isSharedCheck_1798_ == 0)
{
lean_object* v_unused_1799_; lean_object* v_unused_1800_; lean_object* v_unused_1801_; lean_object* v_unused_1802_; lean_object* v_unused_1803_; 
v_unused_1799_ = lean_ctor_get(v_l_1355_, 4);
lean_dec(v_unused_1799_);
v_unused_1800_ = lean_ctor_get(v_l_1355_, 3);
lean_dec(v_unused_1800_);
v_unused_1801_ = lean_ctor_get(v_l_1355_, 2);
lean_dec(v_unused_1801_);
v_unused_1802_ = lean_ctor_get(v_l_1355_, 1);
lean_dec(v_unused_1802_);
v_unused_1803_ = lean_ctor_get(v_l_1355_, 0);
lean_dec(v_unused_1803_);
v___x_1776_ = v_l_1355_;
v_isShared_1777_ = v_isSharedCheck_1798_;
goto v_resetjp_1775_;
}
else
{
lean_dec(v_l_1355_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1798_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
if (lean_obj_tag(v_r_1539_) == 0)
{
lean_object* v_k_1778_; lean_object* v_v_1779_; lean_object* v_size_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1784_; 
v_k_1778_ = lean_ctor_get(v___x_1691_, 0);
lean_inc(v_k_1778_);
v_v_1779_ = lean_ctor_get(v___x_1691_, 1);
lean_inc(v_v_1779_);
lean_dec_ref(v___x_1691_);
v_size_1780_ = lean_ctor_get(v_r_1539_, 0);
v___x_1781_ = lean_nat_add(v___x_1545_, v_size_1535_);
lean_dec(v_size_1535_);
v___x_1782_ = lean_nat_add(v___x_1545_, v_size_1780_);
if (v_isShared_1690_ == 0)
{
lean_ctor_set(v___x_1689_, 4, v_tree_1692_);
lean_ctor_set(v___x_1689_, 3, v_r_1539_);
lean_ctor_set(v___x_1689_, 2, v_v_1779_);
lean_ctor_set(v___x_1689_, 1, v_k_1778_);
lean_ctor_set(v___x_1689_, 0, v___x_1782_);
v___x_1784_ = v___x_1689_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1782_);
lean_ctor_set(v_reuseFailAlloc_1788_, 1, v_k_1778_);
lean_ctor_set(v_reuseFailAlloc_1788_, 2, v_v_1779_);
lean_ctor_set(v_reuseFailAlloc_1788_, 3, v_r_1539_);
lean_ctor_set(v_reuseFailAlloc_1788_, 4, v_tree_1692_);
v___x_1784_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
lean_object* v___x_1786_; 
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 4, v___x_1784_);
lean_ctor_set(v___x_1776_, 0, v___x_1781_);
v___x_1786_ = v___x_1776_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1781_);
lean_ctor_set(v_reuseFailAlloc_1787_, 1, v_k_1536_);
lean_ctor_set(v_reuseFailAlloc_1787_, 2, v_v_1537_);
lean_ctor_set(v_reuseFailAlloc_1787_, 3, v_l_1538_);
lean_ctor_set(v_reuseFailAlloc_1787_, 4, v___x_1784_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
else
{
lean_object* v_k_1789_; lean_object* v_v_1790_; lean_object* v___x_1791_; lean_object* v___x_1793_; 
lean_dec(v_size_1535_);
v_k_1789_ = lean_ctor_get(v___x_1691_, 0);
lean_inc(v_k_1789_);
v_v_1790_ = lean_ctor_get(v___x_1691_, 1);
lean_inc(v_v_1790_);
lean_dec_ref(v___x_1691_);
v___x_1791_ = lean_unsigned_to_nat(3u);
if (v_isShared_1690_ == 0)
{
lean_ctor_set(v___x_1689_, 4, v_r_1539_);
lean_ctor_set(v___x_1689_, 3, v_r_1539_);
lean_ctor_set(v___x_1689_, 2, v_v_1790_);
lean_ctor_set(v___x_1689_, 1, v_k_1789_);
lean_ctor_set(v___x_1689_, 0, v___x_1545_);
v___x_1793_ = v___x_1689_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v___x_1545_);
lean_ctor_set(v_reuseFailAlloc_1797_, 1, v_k_1789_);
lean_ctor_set(v_reuseFailAlloc_1797_, 2, v_v_1790_);
lean_ctor_set(v_reuseFailAlloc_1797_, 3, v_r_1539_);
lean_ctor_set(v_reuseFailAlloc_1797_, 4, v_r_1539_);
v___x_1793_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
lean_object* v___x_1795_; 
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 4, v___x_1793_);
lean_ctor_set(v___x_1776_, 0, v___x_1791_);
v___x_1795_ = v___x_1776_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v___x_1791_);
lean_ctor_set(v_reuseFailAlloc_1796_, 1, v_k_1536_);
lean_ctor_set(v_reuseFailAlloc_1796_, 2, v_v_1537_);
lean_ctor_set(v_reuseFailAlloc_1796_, 3, v_l_1538_);
lean_ctor_set(v_reuseFailAlloc_1796_, 4, v___x_1793_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1539_) == 0)
{
lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1828_; 
lean_inc(v_l_1538_);
lean_inc(v_v_1537_);
lean_inc(v_k_1536_);
v_isSharedCheck_1828_ = !lean_is_exclusive(v_l_1355_);
if (v_isSharedCheck_1828_ == 0)
{
lean_object* v_unused_1829_; lean_object* v_unused_1830_; lean_object* v_unused_1831_; lean_object* v_unused_1832_; lean_object* v_unused_1833_; 
v_unused_1829_ = lean_ctor_get(v_l_1355_, 4);
lean_dec(v_unused_1829_);
v_unused_1830_ = lean_ctor_get(v_l_1355_, 3);
lean_dec(v_unused_1830_);
v_unused_1831_ = lean_ctor_get(v_l_1355_, 2);
lean_dec(v_unused_1831_);
v_unused_1832_ = lean_ctor_get(v_l_1355_, 1);
lean_dec(v_unused_1832_);
v_unused_1833_ = lean_ctor_get(v_l_1355_, 0);
lean_dec(v_unused_1833_);
v___x_1805_ = v_l_1355_;
v_isShared_1806_ = v_isSharedCheck_1828_;
goto v_resetjp_1804_;
}
else
{
lean_dec(v_l_1355_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1828_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v_k_1807_; lean_object* v_v_1808_; lean_object* v_k_1809_; lean_object* v_v_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1824_; 
v_k_1807_ = lean_ctor_get(v___x_1691_, 0);
lean_inc(v_k_1807_);
v_v_1808_ = lean_ctor_get(v___x_1691_, 1);
lean_inc(v_v_1808_);
lean_dec_ref(v___x_1691_);
v_k_1809_ = lean_ctor_get(v_r_1539_, 1);
v_v_1810_ = lean_ctor_get(v_r_1539_, 2);
v_isSharedCheck_1824_ = !lean_is_exclusive(v_r_1539_);
if (v_isSharedCheck_1824_ == 0)
{
lean_object* v_unused_1825_; lean_object* v_unused_1826_; lean_object* v_unused_1827_; 
v_unused_1825_ = lean_ctor_get(v_r_1539_, 4);
lean_dec(v_unused_1825_);
v_unused_1826_ = lean_ctor_get(v_r_1539_, 3);
lean_dec(v_unused_1826_);
v_unused_1827_ = lean_ctor_get(v_r_1539_, 0);
lean_dec(v_unused_1827_);
v___x_1812_ = v_r_1539_;
v_isShared_1813_ = v_isSharedCheck_1824_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_v_1810_);
lean_inc(v_k_1809_);
lean_dec(v_r_1539_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1824_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1814_; lean_object* v___x_1816_; 
v___x_1814_ = lean_unsigned_to_nat(3u);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 4, v_l_1538_);
lean_ctor_set(v___x_1812_, 3, v_l_1538_);
lean_ctor_set(v___x_1812_, 2, v_v_1537_);
lean_ctor_set(v___x_1812_, 1, v_k_1536_);
lean_ctor_set(v___x_1812_, 0, v___x_1545_);
v___x_1816_ = v___x_1812_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v___x_1545_);
lean_ctor_set(v_reuseFailAlloc_1823_, 1, v_k_1536_);
lean_ctor_set(v_reuseFailAlloc_1823_, 2, v_v_1537_);
lean_ctor_set(v_reuseFailAlloc_1823_, 3, v_l_1538_);
lean_ctor_set(v_reuseFailAlloc_1823_, 4, v_l_1538_);
v___x_1816_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
lean_object* v___x_1818_; 
if (v_isShared_1690_ == 0)
{
lean_ctor_set(v___x_1689_, 4, v_l_1538_);
lean_ctor_set(v___x_1689_, 3, v_l_1538_);
lean_ctor_set(v___x_1689_, 2, v_v_1808_);
lean_ctor_set(v___x_1689_, 1, v_k_1807_);
lean_ctor_set(v___x_1689_, 0, v___x_1545_);
v___x_1818_ = v___x_1689_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1545_);
lean_ctor_set(v_reuseFailAlloc_1822_, 1, v_k_1807_);
lean_ctor_set(v_reuseFailAlloc_1822_, 2, v_v_1808_);
lean_ctor_set(v_reuseFailAlloc_1822_, 3, v_l_1538_);
lean_ctor_set(v_reuseFailAlloc_1822_, 4, v_l_1538_);
v___x_1818_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
lean_object* v___x_1820_; 
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 4, v___x_1818_);
lean_ctor_set(v___x_1805_, 3, v___x_1816_);
lean_ctor_set(v___x_1805_, 2, v_v_1810_);
lean_ctor_set(v___x_1805_, 1, v_k_1809_);
lean_ctor_set(v___x_1805_, 0, v___x_1814_);
v___x_1820_ = v___x_1805_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v___x_1814_);
lean_ctor_set(v_reuseFailAlloc_1821_, 1, v_k_1809_);
lean_ctor_set(v_reuseFailAlloc_1821_, 2, v_v_1810_);
lean_ctor_set(v_reuseFailAlloc_1821_, 3, v___x_1816_);
lean_ctor_set(v_reuseFailAlloc_1821_, 4, v___x_1818_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
}
}
}
}
else
{
lean_object* v_k_1834_; lean_object* v_v_1835_; lean_object* v___x_1836_; lean_object* v___x_1838_; 
v_k_1834_ = lean_ctor_get(v___x_1691_, 0);
lean_inc(v_k_1834_);
v_v_1835_ = lean_ctor_get(v___x_1691_, 1);
lean_inc(v_v_1835_);
lean_dec_ref(v___x_1691_);
v___x_1836_ = lean_unsigned_to_nat(2u);
if (v_isShared_1690_ == 0)
{
lean_ctor_set(v___x_1689_, 4, v_r_1539_);
lean_ctor_set(v___x_1689_, 3, v_l_1355_);
lean_ctor_set(v___x_1689_, 2, v_v_1835_);
lean_ctor_set(v___x_1689_, 1, v_k_1834_);
lean_ctor_set(v___x_1689_, 0, v___x_1836_);
v___x_1838_ = v___x_1689_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1836_);
lean_ctor_set(v_reuseFailAlloc_1839_, 1, v_k_1834_);
lean_ctor_set(v_reuseFailAlloc_1839_, 2, v_v_1835_);
lean_ctor_set(v_reuseFailAlloc_1839_, 3, v_l_1355_);
lean_ctor_set(v_reuseFailAlloc_1839_, 4, v_r_1539_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
}
}
}
}
else
{
return v_l_1355_;
}
}
else
{
return v_r_1356_;
}
}
default: 
{
lean_object* v_impl_1846_; lean_object* v___x_1847_; 
v_impl_1846_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_1351_, v_r_1356_);
v___x_1847_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1846_) == 0)
{
if (lean_obj_tag(v_l_1355_) == 0)
{
lean_object* v_size_1848_; lean_object* v_size_1849_; lean_object* v_k_1850_; lean_object* v_v_1851_; lean_object* v_l_1852_; lean_object* v_r_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; uint8_t v___x_1856_; 
v_size_1848_ = lean_ctor_get(v_impl_1846_, 0);
v_size_1849_ = lean_ctor_get(v_l_1355_, 0);
v_k_1850_ = lean_ctor_get(v_l_1355_, 1);
v_v_1851_ = lean_ctor_get(v_l_1355_, 2);
v_l_1852_ = lean_ctor_get(v_l_1355_, 3);
v_r_1853_ = lean_ctor_get(v_l_1355_, 4);
lean_inc(v_r_1853_);
v___x_1854_ = lean_unsigned_to_nat(3u);
v___x_1855_ = lean_nat_mul(v___x_1854_, v_size_1848_);
v___x_1856_ = lean_nat_dec_lt(v___x_1855_, v_size_1849_);
lean_dec(v___x_1855_);
if (v___x_1856_ == 0)
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1860_; 
lean_dec(v_r_1853_);
v___x_1857_ = lean_nat_add(v___x_1847_, v_size_1849_);
v___x_1858_ = lean_nat_add(v___x_1857_, v_size_1848_);
lean_dec(v___x_1857_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 4, v_impl_1846_);
lean_ctor_set(v___x_1358_, 0, v___x_1858_);
v___x_1860_ = v___x_1358_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v___x_1858_);
lean_ctor_set(v_reuseFailAlloc_1861_, 1, v_k_1353_);
lean_ctor_set(v_reuseFailAlloc_1861_, 2, v_v_1354_);
lean_ctor_set(v_reuseFailAlloc_1861_, 3, v_l_1355_);
lean_ctor_set(v_reuseFailAlloc_1861_, 4, v_impl_1846_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
else
{
lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1927_; 
lean_inc(v_l_1852_);
lean_inc(v_v_1851_);
lean_inc(v_k_1850_);
lean_inc(v_size_1849_);
v_isSharedCheck_1927_ = !lean_is_exclusive(v_l_1355_);
if (v_isSharedCheck_1927_ == 0)
{
lean_object* v_unused_1928_; lean_object* v_unused_1929_; lean_object* v_unused_1930_; lean_object* v_unused_1931_; lean_object* v_unused_1932_; 
v_unused_1928_ = lean_ctor_get(v_l_1355_, 4);
lean_dec(v_unused_1928_);
v_unused_1929_ = lean_ctor_get(v_l_1355_, 3);
lean_dec(v_unused_1929_);
v_unused_1930_ = lean_ctor_get(v_l_1355_, 2);
lean_dec(v_unused_1930_);
v_unused_1931_ = lean_ctor_get(v_l_1355_, 1);
lean_dec(v_unused_1931_);
v_unused_1932_ = lean_ctor_get(v_l_1355_, 0);
lean_dec(v_unused_1932_);
v___x_1863_ = v_l_1355_;
v_isShared_1864_ = v_isSharedCheck_1927_;
goto v_resetjp_1862_;
}
else
{
lean_dec(v_l_1355_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1927_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v_size_1865_; lean_object* v_size_1866_; lean_object* v_k_1867_; lean_object* v_v_1868_; lean_object* v_l_1869_; lean_object* v_r_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; uint8_t v___x_1873_; 
v_size_1865_ = lean_ctor_get(v_l_1852_, 0);
v_size_1866_ = lean_ctor_get(v_r_1853_, 0);
v_k_1867_ = lean_ctor_get(v_r_1853_, 1);
v_v_1868_ = lean_ctor_get(v_r_1853_, 2);
v_l_1869_ = lean_ctor_get(v_r_1853_, 3);
v_r_1870_ = lean_ctor_get(v_r_1853_, 4);
v___x_1871_ = lean_unsigned_to_nat(2u);
v___x_1872_ = lean_nat_mul(v___x_1871_, v_size_1865_);
v___x_1873_ = lean_nat_dec_lt(v_size_1866_, v___x_1872_);
lean_dec(v___x_1872_);
if (v___x_1873_ == 0)
{
lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1902_; 
lean_inc(v_r_1870_);
lean_inc(v_l_1869_);
lean_inc(v_v_1868_);
lean_inc(v_k_1867_);
v_isSharedCheck_1902_ = !lean_is_exclusive(v_r_1853_);
if (v_isSharedCheck_1902_ == 0)
{
lean_object* v_unused_1903_; lean_object* v_unused_1904_; lean_object* v_unused_1905_; lean_object* v_unused_1906_; lean_object* v_unused_1907_; 
v_unused_1903_ = lean_ctor_get(v_r_1853_, 4);
lean_dec(v_unused_1903_);
v_unused_1904_ = lean_ctor_get(v_r_1853_, 3);
lean_dec(v_unused_1904_);
v_unused_1905_ = lean_ctor_get(v_r_1853_, 2);
lean_dec(v_unused_1905_);
v_unused_1906_ = lean_ctor_get(v_r_1853_, 1);
lean_dec(v_unused_1906_);
v_unused_1907_ = lean_ctor_get(v_r_1853_, 0);
lean_dec(v_unused_1907_);
v___x_1875_ = v_r_1853_;
v_isShared_1876_ = v_isSharedCheck_1902_;
goto v_resetjp_1874_;
}
else
{
lean_dec(v_r_1853_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1902_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___x_1890_; lean_object* v___y_1892_; 
v___x_1877_ = lean_nat_add(v___x_1847_, v_size_1849_);
lean_dec(v_size_1849_);
v___x_1878_ = lean_nat_add(v___x_1877_, v_size_1848_);
lean_dec(v___x_1877_);
v___x_1890_ = lean_nat_add(v___x_1847_, v_size_1865_);
if (lean_obj_tag(v_l_1869_) == 0)
{
lean_object* v_size_1900_; 
v_size_1900_ = lean_ctor_get(v_l_1869_, 0);
lean_inc(v_size_1900_);
v___y_1892_ = v_size_1900_;
goto v___jp_1891_;
}
else
{
lean_object* v___x_1901_; 
v___x_1901_ = lean_unsigned_to_nat(0u);
v___y_1892_ = v___x_1901_;
goto v___jp_1891_;
}
v___jp_1879_:
{
lean_object* v___x_1883_; lean_object* v___x_1885_; 
v___x_1883_ = lean_nat_add(v___y_1880_, v___y_1882_);
lean_dec(v___y_1882_);
lean_dec(v___y_1880_);
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 4, v_impl_1846_);
lean_ctor_set(v___x_1875_, 3, v_r_1870_);
lean_ctor_set(v___x_1875_, 2, v_v_1354_);
lean_ctor_set(v___x_1875_, 1, v_k_1353_);
lean_ctor_set(v___x_1875_, 0, v___x_1883_);
v___x_1885_ = v___x_1875_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v___x_1883_);
lean_ctor_set(v_reuseFailAlloc_1889_, 1, v_k_1353_);
lean_ctor_set(v_reuseFailAlloc_1889_, 2, v_v_1354_);
lean_ctor_set(v_reuseFailAlloc_1889_, 3, v_r_1870_);
lean_ctor_set(v_reuseFailAlloc_1889_, 4, v_impl_1846_);
v___x_1885_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
lean_object* v___x_1887_; 
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 4, v___x_1885_);
lean_ctor_set(v___x_1863_, 3, v___y_1881_);
lean_ctor_set(v___x_1863_, 2, v_v_1868_);
lean_ctor_set(v___x_1863_, 1, v_k_1867_);
lean_ctor_set(v___x_1863_, 0, v___x_1878_);
v___x_1887_ = v___x_1863_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v___x_1878_);
lean_ctor_set(v_reuseFailAlloc_1888_, 1, v_k_1867_);
lean_ctor_set(v_reuseFailAlloc_1888_, 2, v_v_1868_);
lean_ctor_set(v_reuseFailAlloc_1888_, 3, v___y_1881_);
lean_ctor_set(v_reuseFailAlloc_1888_, 4, v___x_1885_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
v___jp_1891_:
{
lean_object* v___x_1893_; lean_object* v___x_1895_; 
v___x_1893_ = lean_nat_add(v___x_1890_, v___y_1892_);
lean_dec(v___y_1892_);
lean_dec(v___x_1890_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 4, v_l_1869_);
lean_ctor_set(v___x_1358_, 3, v_l_1852_);
lean_ctor_set(v___x_1358_, 2, v_v_1851_);
lean_ctor_set(v___x_1358_, 1, v_k_1850_);
lean_ctor_set(v___x_1358_, 0, v___x_1893_);
v___x_1895_ = v___x_1358_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1893_);
lean_ctor_set(v_reuseFailAlloc_1899_, 1, v_k_1850_);
lean_ctor_set(v_reuseFailAlloc_1899_, 2, v_v_1851_);
lean_ctor_set(v_reuseFailAlloc_1899_, 3, v_l_1852_);
lean_ctor_set(v_reuseFailAlloc_1899_, 4, v_l_1869_);
v___x_1895_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
lean_object* v___x_1896_; 
v___x_1896_ = lean_nat_add(v___x_1847_, v_size_1848_);
if (lean_obj_tag(v_r_1870_) == 0)
{
lean_object* v_size_1897_; 
v_size_1897_ = lean_ctor_get(v_r_1870_, 0);
lean_inc(v_size_1897_);
v___y_1880_ = v___x_1896_;
v___y_1881_ = v___x_1895_;
v___y_1882_ = v_size_1897_;
goto v___jp_1879_;
}
else
{
lean_object* v___x_1898_; 
v___x_1898_ = lean_unsigned_to_nat(0u);
v___y_1880_ = v___x_1896_;
v___y_1881_ = v___x_1895_;
v___y_1882_ = v___x_1898_;
goto v___jp_1879_;
}
}
}
}
}
else
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1913_; 
lean_del_object(v___x_1358_);
v___x_1908_ = lean_nat_add(v___x_1847_, v_size_1849_);
lean_dec(v_size_1849_);
v___x_1909_ = lean_nat_add(v___x_1908_, v_size_1848_);
lean_dec(v___x_1908_);
v___x_1910_ = lean_nat_add(v___x_1847_, v_size_1848_);
v___x_1911_ = lean_nat_add(v___x_1910_, v_size_1866_);
lean_dec(v___x_1910_);
lean_inc_ref(v_impl_1846_);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 4, v_impl_1846_);
lean_ctor_set(v___x_1863_, 3, v_r_1853_);
lean_ctor_set(v___x_1863_, 2, v_v_1354_);
lean_ctor_set(v___x_1863_, 1, v_k_1353_);
lean_ctor_set(v___x_1863_, 0, v___x_1911_);
v___x_1913_ = v___x_1863_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v___x_1911_);
lean_ctor_set(v_reuseFailAlloc_1926_, 1, v_k_1353_);
lean_ctor_set(v_reuseFailAlloc_1926_, 2, v_v_1354_);
lean_ctor_set(v_reuseFailAlloc_1926_, 3, v_r_1853_);
lean_ctor_set(v_reuseFailAlloc_1926_, 4, v_impl_1846_);
v___x_1913_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1920_; 
v_isSharedCheck_1920_ = !lean_is_exclusive(v_impl_1846_);
if (v_isSharedCheck_1920_ == 0)
{
lean_object* v_unused_1921_; lean_object* v_unused_1922_; lean_object* v_unused_1923_; lean_object* v_unused_1924_; lean_object* v_unused_1925_; 
v_unused_1921_ = lean_ctor_get(v_impl_1846_, 4);
lean_dec(v_unused_1921_);
v_unused_1922_ = lean_ctor_get(v_impl_1846_, 3);
lean_dec(v_unused_1922_);
v_unused_1923_ = lean_ctor_get(v_impl_1846_, 2);
lean_dec(v_unused_1923_);
v_unused_1924_ = lean_ctor_get(v_impl_1846_, 1);
lean_dec(v_unused_1924_);
v_unused_1925_ = lean_ctor_get(v_impl_1846_, 0);
lean_dec(v_unused_1925_);
v___x_1915_ = v_impl_1846_;
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
else
{
lean_dec(v_impl_1846_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1918_; 
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 4, v___x_1913_);
lean_ctor_set(v___x_1915_, 3, v_l_1852_);
lean_ctor_set(v___x_1915_, 2, v_v_1851_);
lean_ctor_set(v___x_1915_, 1, v_k_1850_);
lean_ctor_set(v___x_1915_, 0, v___x_1909_);
v___x_1918_ = v___x_1915_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v___x_1909_);
lean_ctor_set(v_reuseFailAlloc_1919_, 1, v_k_1850_);
lean_ctor_set(v_reuseFailAlloc_1919_, 2, v_v_1851_);
lean_ctor_set(v_reuseFailAlloc_1919_, 3, v_l_1852_);
lean_ctor_set(v_reuseFailAlloc_1919_, 4, v___x_1913_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1933_; lean_object* v___x_1934_; lean_object* v___x_1936_; 
v_size_1933_ = lean_ctor_get(v_impl_1846_, 0);
v___x_1934_ = lean_nat_add(v___x_1847_, v_size_1933_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 4, v_impl_1846_);
lean_ctor_set(v___x_1358_, 0, v___x_1934_);
v___x_1936_ = v___x_1358_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v___x_1934_);
lean_ctor_set(v_reuseFailAlloc_1937_, 1, v_k_1353_);
lean_ctor_set(v_reuseFailAlloc_1937_, 2, v_v_1354_);
lean_ctor_set(v_reuseFailAlloc_1937_, 3, v_l_1355_);
lean_ctor_set(v_reuseFailAlloc_1937_, 4, v_impl_1846_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
else
{
if (lean_obj_tag(v_l_1355_) == 0)
{
lean_object* v_l_1938_; 
v_l_1938_ = lean_ctor_get(v_l_1355_, 3);
if (lean_obj_tag(v_l_1938_) == 0)
{
lean_object* v_r_1939_; 
lean_inc_ref(v_l_1938_);
v_r_1939_ = lean_ctor_get(v_l_1355_, 4);
lean_inc(v_r_1939_);
if (lean_obj_tag(v_r_1939_) == 0)
{
lean_object* v_size_1940_; lean_object* v_k_1941_; lean_object* v_v_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1955_; 
v_size_1940_ = lean_ctor_get(v_l_1355_, 0);
v_k_1941_ = lean_ctor_get(v_l_1355_, 1);
v_v_1942_ = lean_ctor_get(v_l_1355_, 2);
v_isSharedCheck_1955_ = !lean_is_exclusive(v_l_1355_);
if (v_isSharedCheck_1955_ == 0)
{
lean_object* v_unused_1956_; lean_object* v_unused_1957_; 
v_unused_1956_ = lean_ctor_get(v_l_1355_, 4);
lean_dec(v_unused_1956_);
v_unused_1957_ = lean_ctor_get(v_l_1355_, 3);
lean_dec(v_unused_1957_);
v___x_1944_ = v_l_1355_;
v_isShared_1945_ = v_isSharedCheck_1955_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_v_1942_);
lean_inc(v_k_1941_);
lean_inc(v_size_1940_);
lean_dec(v_l_1355_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1955_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v_size_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1950_; 
v_size_1946_ = lean_ctor_get(v_r_1939_, 0);
v___x_1947_ = lean_nat_add(v___x_1847_, v_size_1940_);
lean_dec(v_size_1940_);
v___x_1948_ = lean_nat_add(v___x_1847_, v_size_1946_);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 4, v_impl_1846_);
lean_ctor_set(v___x_1944_, 3, v_r_1939_);
lean_ctor_set(v___x_1944_, 2, v_v_1354_);
lean_ctor_set(v___x_1944_, 1, v_k_1353_);
lean_ctor_set(v___x_1944_, 0, v___x_1948_);
v___x_1950_ = v___x_1944_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v___x_1948_);
lean_ctor_set(v_reuseFailAlloc_1954_, 1, v_k_1353_);
lean_ctor_set(v_reuseFailAlloc_1954_, 2, v_v_1354_);
lean_ctor_set(v_reuseFailAlloc_1954_, 3, v_r_1939_);
lean_ctor_set(v_reuseFailAlloc_1954_, 4, v_impl_1846_);
v___x_1950_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
lean_object* v___x_1952_; 
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 4, v___x_1950_);
lean_ctor_set(v___x_1358_, 3, v_l_1938_);
lean_ctor_set(v___x_1358_, 2, v_v_1942_);
lean_ctor_set(v___x_1358_, 1, v_k_1941_);
lean_ctor_set(v___x_1358_, 0, v___x_1947_);
v___x_1952_ = v___x_1358_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v___x_1947_);
lean_ctor_set(v_reuseFailAlloc_1953_, 1, v_k_1941_);
lean_ctor_set(v_reuseFailAlloc_1953_, 2, v_v_1942_);
lean_ctor_set(v_reuseFailAlloc_1953_, 3, v_l_1938_);
lean_ctor_set(v_reuseFailAlloc_1953_, 4, v___x_1950_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
else
{
lean_object* v_k_1958_; lean_object* v_v_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1970_; 
v_k_1958_ = lean_ctor_get(v_l_1355_, 1);
v_v_1959_ = lean_ctor_get(v_l_1355_, 2);
v_isSharedCheck_1970_ = !lean_is_exclusive(v_l_1355_);
if (v_isSharedCheck_1970_ == 0)
{
lean_object* v_unused_1971_; lean_object* v_unused_1972_; lean_object* v_unused_1973_; 
v_unused_1971_ = lean_ctor_get(v_l_1355_, 4);
lean_dec(v_unused_1971_);
v_unused_1972_ = lean_ctor_get(v_l_1355_, 3);
lean_dec(v_unused_1972_);
v_unused_1973_ = lean_ctor_get(v_l_1355_, 0);
lean_dec(v_unused_1973_);
v___x_1961_ = v_l_1355_;
v_isShared_1962_ = v_isSharedCheck_1970_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_v_1959_);
lean_inc(v_k_1958_);
lean_dec(v_l_1355_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1970_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1963_; lean_object* v___x_1965_; 
v___x_1963_ = lean_unsigned_to_nat(3u);
if (v_isShared_1962_ == 0)
{
lean_ctor_set(v___x_1961_, 3, v_r_1939_);
lean_ctor_set(v___x_1961_, 2, v_v_1354_);
lean_ctor_set(v___x_1961_, 1, v_k_1353_);
lean_ctor_set(v___x_1961_, 0, v___x_1847_);
v___x_1965_ = v___x_1961_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v___x_1847_);
lean_ctor_set(v_reuseFailAlloc_1969_, 1, v_k_1353_);
lean_ctor_set(v_reuseFailAlloc_1969_, 2, v_v_1354_);
lean_ctor_set(v_reuseFailAlloc_1969_, 3, v_r_1939_);
lean_ctor_set(v_reuseFailAlloc_1969_, 4, v_r_1939_);
v___x_1965_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
lean_object* v___x_1967_; 
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 4, v___x_1965_);
lean_ctor_set(v___x_1358_, 3, v_l_1938_);
lean_ctor_set(v___x_1358_, 2, v_v_1959_);
lean_ctor_set(v___x_1358_, 1, v_k_1958_);
lean_ctor_set(v___x_1358_, 0, v___x_1963_);
v___x_1967_ = v___x_1358_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v___x_1963_);
lean_ctor_set(v_reuseFailAlloc_1968_, 1, v_k_1958_);
lean_ctor_set(v_reuseFailAlloc_1968_, 2, v_v_1959_);
lean_ctor_set(v_reuseFailAlloc_1968_, 3, v_l_1938_);
lean_ctor_set(v_reuseFailAlloc_1968_, 4, v___x_1965_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
}
else
{
lean_object* v_r_1974_; 
v_r_1974_ = lean_ctor_get(v_l_1355_, 4);
lean_inc(v_r_1974_);
if (lean_obj_tag(v_r_1974_) == 0)
{
lean_object* v_k_1975_; lean_object* v_v_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1999_; 
lean_inc(v_l_1938_);
v_k_1975_ = lean_ctor_get(v_l_1355_, 1);
v_v_1976_ = lean_ctor_get(v_l_1355_, 2);
v_isSharedCheck_1999_ = !lean_is_exclusive(v_l_1355_);
if (v_isSharedCheck_1999_ == 0)
{
lean_object* v_unused_2000_; lean_object* v_unused_2001_; lean_object* v_unused_2002_; 
v_unused_2000_ = lean_ctor_get(v_l_1355_, 4);
lean_dec(v_unused_2000_);
v_unused_2001_ = lean_ctor_get(v_l_1355_, 3);
lean_dec(v_unused_2001_);
v_unused_2002_ = lean_ctor_get(v_l_1355_, 0);
lean_dec(v_unused_2002_);
v___x_1978_ = v_l_1355_;
v_isShared_1979_ = v_isSharedCheck_1999_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_v_1976_);
lean_inc(v_k_1975_);
lean_dec(v_l_1355_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1999_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v_k_1980_; lean_object* v_v_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1995_; 
v_k_1980_ = lean_ctor_get(v_r_1974_, 1);
v_v_1981_ = lean_ctor_get(v_r_1974_, 2);
v_isSharedCheck_1995_ = !lean_is_exclusive(v_r_1974_);
if (v_isSharedCheck_1995_ == 0)
{
lean_object* v_unused_1996_; lean_object* v_unused_1997_; lean_object* v_unused_1998_; 
v_unused_1996_ = lean_ctor_get(v_r_1974_, 4);
lean_dec(v_unused_1996_);
v_unused_1997_ = lean_ctor_get(v_r_1974_, 3);
lean_dec(v_unused_1997_);
v_unused_1998_ = lean_ctor_get(v_r_1974_, 0);
lean_dec(v_unused_1998_);
v___x_1983_ = v_r_1974_;
v_isShared_1984_ = v_isSharedCheck_1995_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_v_1981_);
lean_inc(v_k_1980_);
lean_dec(v_r_1974_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1995_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1985_; lean_object* v___x_1987_; 
v___x_1985_ = lean_unsigned_to_nat(3u);
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 4, v_l_1938_);
lean_ctor_set(v___x_1983_, 3, v_l_1938_);
lean_ctor_set(v___x_1983_, 2, v_v_1976_);
lean_ctor_set(v___x_1983_, 1, v_k_1975_);
lean_ctor_set(v___x_1983_, 0, v___x_1847_);
v___x_1987_ = v___x_1983_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1847_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v_k_1975_);
lean_ctor_set(v_reuseFailAlloc_1994_, 2, v_v_1976_);
lean_ctor_set(v_reuseFailAlloc_1994_, 3, v_l_1938_);
lean_ctor_set(v_reuseFailAlloc_1994_, 4, v_l_1938_);
v___x_1987_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
lean_object* v___x_1989_; 
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 4, v_l_1938_);
lean_ctor_set(v___x_1978_, 2, v_v_1354_);
lean_ctor_set(v___x_1978_, 1, v_k_1353_);
lean_ctor_set(v___x_1978_, 0, v___x_1847_);
v___x_1989_ = v___x_1978_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1847_);
lean_ctor_set(v_reuseFailAlloc_1993_, 1, v_k_1353_);
lean_ctor_set(v_reuseFailAlloc_1993_, 2, v_v_1354_);
lean_ctor_set(v_reuseFailAlloc_1993_, 3, v_l_1938_);
lean_ctor_set(v_reuseFailAlloc_1993_, 4, v_l_1938_);
v___x_1989_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
lean_object* v___x_1991_; 
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 4, v___x_1989_);
lean_ctor_set(v___x_1358_, 3, v___x_1987_);
lean_ctor_set(v___x_1358_, 2, v_v_1981_);
lean_ctor_set(v___x_1358_, 1, v_k_1980_);
lean_ctor_set(v___x_1358_, 0, v___x_1985_);
v___x_1991_ = v___x_1358_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v___x_1985_);
lean_ctor_set(v_reuseFailAlloc_1992_, 1, v_k_1980_);
lean_ctor_set(v_reuseFailAlloc_1992_, 2, v_v_1981_);
lean_ctor_set(v_reuseFailAlloc_1992_, 3, v___x_1987_);
lean_ctor_set(v_reuseFailAlloc_1992_, 4, v___x_1989_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
}
}
else
{
lean_object* v___x_2003_; lean_object* v___x_2005_; 
v___x_2003_ = lean_unsigned_to_nat(2u);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 4, v_r_1974_);
lean_ctor_set(v___x_1358_, 0, v___x_2003_);
v___x_2005_ = v___x_1358_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_2003_);
lean_ctor_set(v_reuseFailAlloc_2006_, 1, v_k_1353_);
lean_ctor_set(v_reuseFailAlloc_2006_, 2, v_v_1354_);
lean_ctor_set(v_reuseFailAlloc_2006_, 3, v_l_1355_);
lean_ctor_set(v_reuseFailAlloc_2006_, 4, v_r_1974_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
}
else
{
lean_object* v___x_2008_; 
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 4, v_l_1355_);
lean_ctor_set(v___x_1358_, 0, v___x_1847_);
v___x_2008_ = v___x_1358_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v___x_1847_);
lean_ctor_set(v_reuseFailAlloc_2009_, 1, v_k_1353_);
lean_ctor_set(v_reuseFailAlloc_2009_, 2, v_v_1354_);
lean_ctor_set(v_reuseFailAlloc_2009_, 3, v_l_1355_);
lean_ctor_set(v_reuseFailAlloc_2009_, 4, v_l_1355_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
}
}
}
}
else
{
return v_t_1352_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg___boxed(lean_object* v_k_2012_, lean_object* v_t_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_2012_, v_t_2013_);
lean_dec(v_k_2012_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3(lean_object* v_xs_2015_, lean_object* v_v_2016_, lean_object* v_i_2017_){
_start:
{
lean_object* v___x_2018_; uint8_t v___x_2019_; 
v___x_2018_ = lean_array_get_size(v_xs_2015_);
v___x_2019_ = lean_nat_dec_lt(v_i_2017_, v___x_2018_);
if (v___x_2019_ == 0)
{
lean_object* v___x_2020_; 
lean_dec(v_i_2017_);
v___x_2020_ = lean_box(0);
return v___x_2020_;
}
else
{
lean_object* v___x_2021_; uint8_t v___x_2022_; 
v___x_2021_ = lean_array_fget_borrowed(v_xs_2015_, v_i_2017_);
v___x_2022_ = l_Lean_instBEqFVarId_beq(v___x_2021_, v_v_2016_);
if (v___x_2022_ == 0)
{
lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___x_2023_ = lean_unsigned_to_nat(1u);
v___x_2024_ = lean_nat_add(v_i_2017_, v___x_2023_);
lean_dec(v_i_2017_);
v_i_2017_ = v___x_2024_;
goto _start;
}
else
{
lean_object* v___x_2026_; 
v___x_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2026_, 0, v_i_2017_);
return v___x_2026_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_xs_2027_, lean_object* v_v_2028_, lean_object* v_i_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3(v_xs_2027_, v_v_2028_, v_i_2029_);
lean_dec(v_v_2028_);
lean_dec_ref(v_xs_2027_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1(lean_object* v_xs_2031_, lean_object* v_v_2032_){
_start:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2033_ = lean_unsigned_to_nat(0u);
v___x_2034_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3(v_xs_2031_, v_v_2032_, v___x_2033_);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_2035_, lean_object* v_v_2036_){
_start:
{
lean_object* v_res_2037_; 
v_res_2037_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1(v_xs_2035_, v_v_2036_);
lean_dec(v_v_2036_);
lean_dec_ref(v_xs_2035_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(lean_object* v_x_2038_, size_t v_x_2039_, lean_object* v_x_2040_){
_start:
{
if (lean_obj_tag(v_x_2038_) == 0)
{
lean_object* v_es_2041_; lean_object* v___x_2042_; size_t v___x_2043_; size_t v___x_2044_; lean_object* v_j_2045_; lean_object* v_entry_2046_; 
v_es_2041_ = lean_ctor_get(v_x_2038_, 0);
v___x_2042_ = lean_box(2);
v___x_2043_ = ((size_t)31ULL);
v___x_2044_ = lean_usize_land(v_x_2039_, v___x_2043_);
v_j_2045_ = lean_usize_to_nat(v___x_2044_);
v_entry_2046_ = lean_array_get(v___x_2042_, v_es_2041_, v_j_2045_);
switch(lean_obj_tag(v_entry_2046_))
{
case 0:
{
lean_object* v_key_2047_; uint8_t v___x_2048_; 
v_key_2047_ = lean_ctor_get(v_entry_2046_, 0);
lean_inc(v_key_2047_);
lean_dec_ref_known(v_entry_2046_, 2);
v___x_2048_ = l_Lean_instBEqFVarId_beq(v_x_2040_, v_key_2047_);
lean_dec(v_key_2047_);
if (v___x_2048_ == 0)
{
lean_dec(v_j_2045_);
return v_x_2038_;
}
else
{
lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2056_; 
lean_inc_ref(v_es_2041_);
v_isSharedCheck_2056_ = !lean_is_exclusive(v_x_2038_);
if (v_isSharedCheck_2056_ == 0)
{
lean_object* v_unused_2057_; 
v_unused_2057_ = lean_ctor_get(v_x_2038_, 0);
lean_dec(v_unused_2057_);
v___x_2050_ = v_x_2038_;
v_isShared_2051_ = v_isSharedCheck_2056_;
goto v_resetjp_2049_;
}
else
{
lean_dec(v_x_2038_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2056_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2052_; lean_object* v___x_2054_; 
v___x_2052_ = lean_array_set(v_es_2041_, v_j_2045_, v___x_2042_);
lean_dec(v_j_2045_);
if (v_isShared_2051_ == 0)
{
lean_ctor_set(v___x_2050_, 0, v___x_2052_);
v___x_2054_ = v___x_2050_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v___x_2052_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
case 1:
{
lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2092_; 
lean_inc_ref(v_es_2041_);
v_isSharedCheck_2092_ = !lean_is_exclusive(v_x_2038_);
if (v_isSharedCheck_2092_ == 0)
{
lean_object* v_unused_2093_; 
v_unused_2093_ = lean_ctor_get(v_x_2038_, 0);
lean_dec(v_unused_2093_);
v___x_2059_ = v_x_2038_;
v_isShared_2060_ = v_isSharedCheck_2092_;
goto v_resetjp_2058_;
}
else
{
lean_dec(v_x_2038_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2092_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v_node_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2091_; 
v_node_2061_ = lean_ctor_get(v_entry_2046_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v_entry_2046_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2063_ = v_entry_2046_;
v_isShared_2064_ = v_isSharedCheck_2091_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_node_2061_);
lean_dec(v_entry_2046_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2091_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
size_t v___x_2065_; lean_object* v_entries_2066_; size_t v___x_2067_; lean_object* v_newNode_2068_; lean_object* v___x_2069_; 
v___x_2065_ = ((size_t)5ULL);
v_entries_2066_ = lean_array_set(v_es_2041_, v_j_2045_, v___x_2042_);
v___x_2067_ = lean_usize_shift_right(v_x_2039_, v___x_2065_);
v_newNode_2068_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_node_2061_, v___x_2067_, v_x_2040_);
lean_inc_ref(v_newNode_2068_);
v___x_2069_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_2068_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v___x_2071_; 
if (v_isShared_2064_ == 0)
{
lean_ctor_set(v___x_2063_, 0, v_newNode_2068_);
v___x_2071_ = v___x_2063_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_newNode_2068_);
v___x_2071_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
lean_object* v___x_2072_; lean_object* v___x_2074_; 
v___x_2072_ = lean_array_set(v_entries_2066_, v_j_2045_, v___x_2071_);
lean_dec(v_j_2045_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 0, v___x_2072_);
v___x_2074_ = v___x_2059_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_2072_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
else
{
lean_object* v_val_2077_; lean_object* v_fst_2078_; lean_object* v_snd_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2090_; 
lean_dec_ref(v_newNode_2068_);
lean_del_object(v___x_2063_);
v_val_2077_ = lean_ctor_get(v___x_2069_, 0);
lean_inc(v_val_2077_);
lean_dec_ref_known(v___x_2069_, 1);
v_fst_2078_ = lean_ctor_get(v_val_2077_, 0);
v_snd_2079_ = lean_ctor_get(v_val_2077_, 1);
v_isSharedCheck_2090_ = !lean_is_exclusive(v_val_2077_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2081_ = v_val_2077_;
v_isShared_2082_ = v_isSharedCheck_2090_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_snd_2079_);
lean_inc(v_fst_2078_);
lean_dec(v_val_2077_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2090_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2084_; 
if (v_isShared_2082_ == 0)
{
v___x_2084_ = v___x_2081_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_fst_2078_);
lean_ctor_set(v_reuseFailAlloc_2089_, 1, v_snd_2079_);
v___x_2084_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
lean_object* v___x_2085_; lean_object* v___x_2087_; 
v___x_2085_ = lean_array_set(v_entries_2066_, v_j_2045_, v___x_2084_);
lean_dec(v_j_2045_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 0, v___x_2085_);
v___x_2087_ = v___x_2059_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v___x_2085_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_2045_);
return v_x_2038_;
}
}
}
else
{
lean_object* v_ks_2094_; lean_object* v_vs_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2109_; 
v_ks_2094_ = lean_ctor_get(v_x_2038_, 0);
v_vs_2095_ = lean_ctor_get(v_x_2038_, 1);
v_isSharedCheck_2109_ = !lean_is_exclusive(v_x_2038_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2097_ = v_x_2038_;
v_isShared_2098_ = v_isSharedCheck_2109_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_vs_2095_);
lean_inc(v_ks_2094_);
lean_dec(v_x_2038_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2109_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2099_; 
v___x_2099_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1(v_ks_2094_, v_x_2040_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v___x_2101_; 
if (v_isShared_2098_ == 0)
{
v___x_2101_ = v___x_2097_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_ks_2094_);
lean_ctor_set(v_reuseFailAlloc_2102_, 1, v_vs_2095_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
else
{
lean_object* v_val_2103_; lean_object* v_keys_x27_2104_; lean_object* v_vals_x27_2105_; lean_object* v___x_2107_; 
v_val_2103_ = lean_ctor_get(v___x_2099_, 0);
lean_inc_n(v_val_2103_, 2);
lean_dec_ref_known(v___x_2099_, 1);
v_keys_x27_2104_ = l_Array_eraseIdx___redArg(v_ks_2094_, v_val_2103_);
v_vals_x27_2105_ = l_Array_eraseIdx___redArg(v_vs_2095_, v_val_2103_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 1, v_vals_x27_2105_);
lean_ctor_set(v___x_2097_, 0, v_keys_x27_2104_);
v___x_2107_ = v___x_2097_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_keys_x27_2104_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v_vals_x27_2105_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg___boxed(lean_object* v_x_2110_, lean_object* v_x_2111_, lean_object* v_x_2112_){
_start:
{
size_t v_x_2640__boxed_2113_; lean_object* v_res_2114_; 
v_x_2640__boxed_2113_ = lean_unbox_usize(v_x_2111_);
lean_dec(v_x_2111_);
v_res_2114_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_x_2110_, v_x_2640__boxed_2113_, v_x_2112_);
lean_dec(v_x_2112_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(lean_object* v_x_2115_, lean_object* v_x_2116_){
_start:
{
uint64_t v___x_2117_; size_t v_h_2118_; lean_object* v___x_2119_; 
v___x_2117_ = l_Lean_instHashableFVarId_hash(v_x_2116_);
v_h_2118_ = lean_uint64_to_usize(v___x_2117_);
v___x_2119_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_x_2115_, v_h_2118_, v_x_2116_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg___boxed(lean_object* v_x_2120_, lean_object* v_x_2121_){
_start:
{
lean_object* v_res_2122_; 
v_res_2122_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_x_2120_, v_x_2121_);
lean_dec(v_x_2121_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_erase(lean_object* v_lctx_2123_, lean_object* v_fvarId_2124_){
_start:
{
lean_object* v_fvarIdToDecl_2125_; lean_object* v_decls_2126_; lean_object* v_auxDeclToFullName_2127_; lean_object* v___x_2128_; 
v_fvarIdToDecl_2125_ = lean_ctor_get(v_lctx_2123_, 0);
v_decls_2126_ = lean_ctor_get(v_lctx_2123_, 1);
v_auxDeclToFullName_2127_ = lean_ctor_get(v_lctx_2123_, 2);
v___x_2128_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_fvarIdToDecl_2125_, v_fvarId_2124_);
if (lean_obj_tag(v___x_2128_) == 0)
{
return v_lctx_2123_;
}
else
{
lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2148_; 
lean_inc(v_auxDeclToFullName_2127_);
lean_inc_ref(v_decls_2126_);
lean_inc_ref(v_fvarIdToDecl_2125_);
v_isSharedCheck_2148_ = !lean_is_exclusive(v_lctx_2123_);
if (v_isSharedCheck_2148_ == 0)
{
lean_object* v_unused_2149_; lean_object* v_unused_2150_; lean_object* v_unused_2151_; 
v_unused_2149_ = lean_ctor_get(v_lctx_2123_, 2);
lean_dec(v_unused_2149_);
v_unused_2150_ = lean_ctor_get(v_lctx_2123_, 1);
lean_dec(v_unused_2150_);
v_unused_2151_ = lean_ctor_get(v_lctx_2123_, 0);
lean_dec(v_unused_2151_);
v___x_2130_ = v_lctx_2123_;
v_isShared_2131_ = v_isSharedCheck_2148_;
goto v_resetjp_2129_;
}
else
{
lean_dec(v_lctx_2123_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2148_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v_val_2132_; lean_object* v___x_2133_; lean_object* v___y_2135_; lean_object* v_index_2147_; 
v_val_2132_ = lean_ctor_get(v___x_2128_, 0);
lean_inc(v_val_2132_);
lean_dec_ref_known(v___x_2128_, 1);
v___x_2133_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_fvarIdToDecl_2125_, v_fvarId_2124_);
v_index_2147_ = lean_ctor_get(v_val_2132_, 0);
lean_inc(v_index_2147_);
v___y_2135_ = v_index_2147_;
goto v___jp_2134_;
v___jp_2134_:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; uint8_t v___x_2139_; 
v___x_2136_ = lean_box(0);
v___x_2137_ = l_Lean_PersistentArray_set___redArg(v_decls_2126_, v___y_2135_, v___x_2136_);
lean_dec(v___y_2135_);
v___x_2138_ = l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(v___x_2137_);
v___x_2139_ = l_Lean_LocalDecl_isAuxDecl(v_val_2132_);
lean_dec(v_val_2132_);
if (v___x_2139_ == 0)
{
lean_object* v___x_2141_; 
if (v_isShared_2131_ == 0)
{
lean_ctor_set(v___x_2130_, 1, v___x_2138_);
lean_ctor_set(v___x_2130_, 0, v___x_2133_);
v___x_2141_ = v___x_2130_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2133_);
lean_ctor_set(v_reuseFailAlloc_2142_, 1, v___x_2138_);
lean_ctor_set(v_reuseFailAlloc_2142_, 2, v_auxDeclToFullName_2127_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
else
{
lean_object* v___x_2143_; lean_object* v___x_2145_; 
v___x_2143_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_fvarId_2124_, v_auxDeclToFullName_2127_);
if (v_isShared_2131_ == 0)
{
lean_ctor_set(v___x_2130_, 2, v___x_2143_);
lean_ctor_set(v___x_2130_, 1, v___x_2138_);
lean_ctor_set(v___x_2130_, 0, v___x_2133_);
v___x_2145_ = v___x_2130_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2133_);
lean_ctor_set(v_reuseFailAlloc_2146_, 1, v___x_2138_);
lean_ctor_set(v_reuseFailAlloc_2146_, 2, v___x_2143_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_erase___boxed(lean_object* v_lctx_2152_, lean_object* v_fvarId_2153_){
_start:
{
lean_object* v_res_2154_; 
v_res_2154_ = l_Lean_LocalContext_erase(v_lctx_2152_, v_fvarId_2153_);
lean_dec(v_fvarId_2153_);
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0(lean_object* v_00_u03b2_2155_, lean_object* v_x_2156_, lean_object* v_x_2157_){
_start:
{
lean_object* v___x_2158_; 
v___x_2158_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_x_2156_, v_x_2157_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___boxed(lean_object* v_00_u03b2_2159_, lean_object* v_x_2160_, lean_object* v_x_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0(v_00_u03b2_2159_, v_x_2160_, v_x_2161_);
lean_dec(v_x_2161_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1(lean_object* v_00_u03b2_2163_, lean_object* v_k_2164_, lean_object* v_t_2165_, lean_object* v_h_2166_){
_start:
{
lean_object* v___x_2167_; 
v___x_2167_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_2164_, v_t_2165_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___boxed(lean_object* v_00_u03b2_2168_, lean_object* v_k_2169_, lean_object* v_t_2170_, lean_object* v_h_2171_){
_start:
{
lean_object* v_res_2172_; 
v_res_2172_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1(v_00_u03b2_2168_, v_k_2169_, v_t_2170_, v_h_2171_);
lean_dec(v_k_2169_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0(lean_object* v_00_u03b2_2173_, lean_object* v_x_2174_, size_t v_x_2175_, lean_object* v_x_2176_){
_start:
{
lean_object* v___x_2177_; 
v___x_2177_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_x_2174_, v_x_2175_, v_x_2176_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2178_, lean_object* v_x_2179_, lean_object* v_x_2180_, lean_object* v_x_2181_){
_start:
{
size_t v_x_2862__boxed_2182_; lean_object* v_res_2183_; 
v_x_2862__boxed_2182_ = lean_unbox_usize(v_x_2180_);
lean_dec(v_x_2180_);
v_res_2183_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0(v_00_u03b2_2178_, v_x_2179_, v_x_2862__boxed_2182_, v_x_2181_);
lean_dec(v_x_2181_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_pop(lean_object* v_lctx_2184_){
_start:
{
lean_object* v_decls_2185_; lean_object* v_fvarIdToDecl_2186_; lean_object* v_auxDeclToFullName_2187_; lean_object* v_size_2188_; lean_object* v___x_2189_; uint8_t v___x_2190_; 
v_decls_2185_ = lean_ctor_get(v_lctx_2184_, 1);
v_fvarIdToDecl_2186_ = lean_ctor_get(v_lctx_2184_, 0);
v_auxDeclToFullName_2187_ = lean_ctor_get(v_lctx_2184_, 2);
v_size_2188_ = lean_ctor_get(v_decls_2185_, 2);
v___x_2189_ = lean_unsigned_to_nat(0u);
v___x_2190_ = lean_nat_dec_eq(v_size_2188_, v___x_2189_);
if (v___x_2190_ == 0)
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2191_ = lean_box(0);
v___x_2192_ = lean_unsigned_to_nat(1u);
v___x_2193_ = lean_nat_sub(v_size_2188_, v___x_2192_);
v___x_2194_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2191_, v_decls_2185_, v___x_2193_);
lean_dec(v___x_2193_);
if (lean_obj_tag(v___x_2194_) == 0)
{
return v_lctx_2184_;
}
else
{
lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2213_; 
lean_inc(v_auxDeclToFullName_2187_);
lean_inc_ref(v_fvarIdToDecl_2186_);
lean_inc_ref(v_decls_2185_);
v_isSharedCheck_2213_ = !lean_is_exclusive(v_lctx_2184_);
if (v_isSharedCheck_2213_ == 0)
{
lean_object* v_unused_2214_; lean_object* v_unused_2215_; lean_object* v_unused_2216_; 
v_unused_2214_ = lean_ctor_get(v_lctx_2184_, 2);
lean_dec(v_unused_2214_);
v_unused_2215_ = lean_ctor_get(v_lctx_2184_, 1);
lean_dec(v_unused_2215_);
v_unused_2216_ = lean_ctor_get(v_lctx_2184_, 0);
lean_dec(v_unused_2216_);
v___x_2196_ = v_lctx_2184_;
v_isShared_2197_ = v_isSharedCheck_2213_;
goto v_resetjp_2195_;
}
else
{
lean_dec(v_lctx_2184_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2213_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v_val_2198_; lean_object* v___y_2200_; lean_object* v_fvarId_2212_; 
v_val_2198_ = lean_ctor_get(v___x_2194_, 0);
lean_inc(v_val_2198_);
lean_dec_ref_known(v___x_2194_, 1);
v_fvarId_2212_ = lean_ctor_get(v_val_2198_, 1);
lean_inc(v_fvarId_2212_);
v___y_2200_ = v_fvarId_2212_;
goto v___jp_2199_;
v___jp_2199_:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; uint8_t v___x_2204_; 
v___x_2201_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_fvarIdToDecl_2186_, v___y_2200_);
v___x_2202_ = l_Lean_PersistentArray_pop___redArg(v_decls_2185_);
v___x_2203_ = l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(v___x_2202_);
v___x_2204_ = l_Lean_LocalDecl_isAuxDecl(v_val_2198_);
lean_dec(v_val_2198_);
if (v___x_2204_ == 0)
{
lean_object* v___x_2206_; 
lean_dec(v___y_2200_);
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 1, v___x_2203_);
lean_ctor_set(v___x_2196_, 0, v___x_2201_);
v___x_2206_ = v___x_2196_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v___x_2201_);
lean_ctor_set(v_reuseFailAlloc_2207_, 1, v___x_2203_);
lean_ctor_set(v_reuseFailAlloc_2207_, 2, v_auxDeclToFullName_2187_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
else
{
lean_object* v___x_2208_; lean_object* v___x_2210_; 
v___x_2208_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v___y_2200_, v_auxDeclToFullName_2187_);
lean_dec(v___y_2200_);
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 2, v___x_2208_);
lean_ctor_set(v___x_2196_, 1, v___x_2203_);
lean_ctor_set(v___x_2196_, 0, v___x_2201_);
v___x_2210_ = v___x_2196_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2201_);
lean_ctor_set(v_reuseFailAlloc_2211_, 1, v___x_2203_);
lean_ctor_set(v_reuseFailAlloc_2211_, 2, v___x_2208_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
}
}
else
{
return v_lctx_2184_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(lean_object* v_userName_2217_, lean_object* v_as_2218_, lean_object* v_i_2219_){
_start:
{
lean_object* v_zero_2220_; uint8_t v_isZero_2221_; 
v_zero_2220_ = lean_unsigned_to_nat(0u);
v_isZero_2221_ = lean_nat_dec_eq(v_i_2219_, v_zero_2220_);
if (v_isZero_2221_ == 1)
{
lean_object* v___x_2222_; 
lean_dec(v_i_2219_);
v___x_2222_ = lean_box(0);
return v___x_2222_;
}
else
{
lean_object* v_one_2223_; lean_object* v_n_2224_; lean_object* v___x_2225_; lean_object* v___y_2227_; 
v_one_2223_ = lean_unsigned_to_nat(1u);
v_n_2224_ = lean_nat_sub(v_i_2219_, v_one_2223_);
lean_dec(v_i_2219_);
v___x_2225_ = lean_array_fget_borrowed(v_as_2218_, v_n_2224_);
if (lean_obj_tag(v___x_2225_) == 0)
{
v_i_2219_ = v_n_2224_;
goto _start;
}
else
{
lean_object* v_val_2231_; lean_object* v_userName_2232_; 
v_val_2231_ = lean_ctor_get(v___x_2225_, 0);
v_userName_2232_ = lean_ctor_get(v_val_2231_, 2);
v___y_2227_ = v_userName_2232_;
goto v___jp_2226_;
}
v___jp_2226_:
{
uint8_t v___x_2228_; 
v___x_2228_ = lean_name_eq(v___y_2227_, v_userName_2217_);
if (v___x_2228_ == 0)
{
v_i_2219_ = v_n_2224_;
goto _start;
}
else
{
lean_dec(v_n_2224_);
lean_inc(v___x_2225_);
return v___x_2225_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_userName_2233_, lean_object* v_as_2234_, lean_object* v_i_2235_){
_start:
{
lean_object* v_res_2236_; 
v_res_2236_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2233_, v_as_2234_, v_i_2235_);
lean_dec_ref(v_as_2234_);
lean_dec(v_userName_2233_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(lean_object* v_userName_2237_, lean_object* v_as_2238_, lean_object* v_i_2239_){
_start:
{
lean_object* v_zero_2240_; uint8_t v_isZero_2241_; 
v_zero_2240_ = lean_unsigned_to_nat(0u);
v_isZero_2241_ = lean_nat_dec_eq(v_i_2239_, v_zero_2240_);
if (v_isZero_2241_ == 1)
{
lean_object* v___x_2242_; 
lean_dec(v_i_2239_);
v___x_2242_ = lean_box(0);
return v___x_2242_;
}
else
{
lean_object* v_one_2243_; lean_object* v_n_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v_one_2243_ = lean_unsigned_to_nat(1u);
v_n_2244_ = lean_nat_sub(v_i_2239_, v_one_2243_);
lean_dec(v_i_2239_);
v___x_2245_ = lean_array_fget_borrowed(v_as_2238_, v_n_2244_);
v___x_2246_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(v_userName_2237_, v___x_2245_);
if (lean_obj_tag(v___x_2246_) == 0)
{
v_i_2239_ = v_n_2244_;
goto _start;
}
else
{
lean_dec(v_n_2244_);
return v___x_2246_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(lean_object* v_userName_2248_, lean_object* v_x_2249_){
_start:
{
if (lean_obj_tag(v_x_2249_) == 0)
{
lean_object* v_cs_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v_cs_2250_ = lean_ctor_get(v_x_2249_, 0);
v___x_2251_ = lean_array_get_size(v_cs_2250_);
v___x_2252_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(v_userName_2248_, v_cs_2250_, v___x_2251_);
return v___x_2252_;
}
else
{
lean_object* v_vs_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v_vs_2253_ = lean_ctor_get(v_x_2249_, 0);
v___x_2254_ = lean_array_get_size(v_vs_2253_);
v___x_2255_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2248_, v_vs_2253_, v___x_2254_);
return v___x_2255_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1___boxed(lean_object* v_userName_2256_, lean_object* v_x_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(v_userName_2256_, v_x_2257_);
lean_dec_ref(v_x_2257_);
lean_dec(v_userName_2256_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_userName_2259_, lean_object* v_as_2260_, lean_object* v_i_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(v_userName_2259_, v_as_2260_, v_i_2261_);
lean_dec_ref(v_as_2260_);
lean_dec(v_userName_2259_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0(lean_object* v_userName_2263_, lean_object* v_t_2264_){
_start:
{
lean_object* v_root_2265_; lean_object* v_tail_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
v_root_2265_ = lean_ctor_get(v_t_2264_, 0);
v_tail_2266_ = lean_ctor_get(v_t_2264_, 1);
v___x_2267_ = lean_array_get_size(v_tail_2266_);
v___x_2268_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2263_, v_tail_2266_, v___x_2267_);
if (lean_obj_tag(v___x_2268_) == 0)
{
lean_object* v___x_2269_; 
v___x_2269_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(v_userName_2263_, v_root_2265_);
return v___x_2269_;
}
else
{
return v___x_2268_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0___boxed(lean_object* v_userName_2270_, lean_object* v_t_2271_){
_start:
{
lean_object* v_res_2272_; 
v_res_2272_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0(v_userName_2270_, v_t_2271_);
lean_dec_ref(v_t_2271_);
lean_dec(v_userName_2270_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object* v_lctx_2273_, lean_object* v_userName_2274_){
_start:
{
lean_object* v_decls_2275_; lean_object* v___x_2276_; 
v_decls_2275_ = lean_ctor_get(v_lctx_2273_, 1);
v___x_2276_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0(v_userName_2274_, v_decls_2275_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserName_x3f___boxed(lean_object* v_lctx_2277_, lean_object* v_userName_2278_){
_start:
{
lean_object* v_res_2279_; 
v_res_2279_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2277_, v_userName_2278_);
lean_dec(v_userName_2278_);
lean_dec_ref(v_lctx_2277_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0(lean_object* v_userName_2280_, lean_object* v_as_2281_, lean_object* v_i_2282_, lean_object* v_a_2283_){
_start:
{
lean_object* v___x_2284_; 
v___x_2284_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2280_, v_as_2281_, v_i_2282_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___boxed(lean_object* v_userName_2285_, lean_object* v_as_2286_, lean_object* v_i_2287_, lean_object* v_a_2288_){
_start:
{
lean_object* v_res_2289_; 
v_res_2289_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0(v_userName_2285_, v_as_2286_, v_i_2287_, v_a_2288_);
lean_dec_ref(v_as_2286_);
lean_dec(v_userName_2285_);
return v_res_2289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2(lean_object* v_userName_2290_, lean_object* v_as_2291_, lean_object* v_i_2292_, lean_object* v_a_2293_){
_start:
{
lean_object* v___x_2294_; 
v___x_2294_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(v_userName_2290_, v_as_2291_, v_i_2292_);
return v___x_2294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___boxed(lean_object* v_userName_2295_, lean_object* v_as_2296_, lean_object* v_i_2297_, lean_object* v_a_2298_){
_start:
{
lean_object* v_res_2299_; 
v_res_2299_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2(v_userName_2295_, v_as_2296_, v_i_2297_, v_a_2298_);
lean_dec_ref(v_as_2296_);
lean_dec(v_userName_2295_);
return v_res_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFromUserName_x21(lean_object* v_lctx_2303_, lean_object* v_userName_2304_){
_start:
{
lean_object* v___x_2305_; 
v___x_2305_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2303_, v_userName_2304_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; uint8_t v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2306_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_2307_ = ((lean_object*)(l_Lean_LocalContext_getFromUserName_x21___closed__0));
v___x_2308_ = lean_unsigned_to_nat(412u);
v___x_2309_ = lean_unsigned_to_nat(17u);
v___x_2310_ = ((lean_object*)(l_Lean_LocalContext_getFromUserName_x21___closed__1));
v___x_2311_ = 1;
v___x_2312_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_userName_2304_, v___x_2311_);
v___x_2313_ = lean_string_append(v___x_2310_, v___x_2312_);
lean_dec_ref(v___x_2312_);
v___x_2314_ = ((lean_object*)(l_Lean_LocalContext_getFromUserName_x21___closed__2));
v___x_2315_ = lean_string_append(v___x_2313_, v___x_2314_);
v___x_2316_ = l_mkPanicMessageWithDecl(v___x_2306_, v___x_2307_, v___x_2308_, v___x_2309_, v___x_2315_);
lean_dec_ref(v___x_2315_);
v___x_2317_ = l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(v___x_2316_);
return v___x_2317_;
}
else
{
lean_object* v_val_2318_; 
lean_dec(v_userName_2304_);
v_val_2318_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_val_2318_);
lean_dec_ref_known(v___x_2305_, 1);
return v_val_2318_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFromUserName_x21___boxed(lean_object* v_lctx_2319_, lean_object* v_userName_2320_){
_start:
{
lean_object* v_res_2321_; 
v_res_2321_ = l_Lean_LocalContext_getFromUserName_x21(v_lctx_2319_, v_userName_2320_);
lean_dec_ref(v_lctx_2319_);
return v_res_2321_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_usesUserName(lean_object* v_lctx_2322_, lean_object* v_userName_2323_){
_start:
{
lean_object* v___x_2324_; 
v___x_2324_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2322_, v_userName_2323_);
if (lean_obj_tag(v___x_2324_) == 0)
{
uint8_t v___x_2325_; 
v___x_2325_ = 0;
return v___x_2325_;
}
else
{
uint8_t v___x_2326_; 
lean_dec_ref_known(v___x_2324_, 1);
v___x_2326_ = 1;
return v___x_2326_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_usesUserName___boxed(lean_object* v_lctx_2327_, lean_object* v_userName_2328_){
_start:
{
uint8_t v_res_2329_; lean_object* v_r_2330_; 
v_res_2329_ = l_Lean_LocalContext_usesUserName(v_lctx_2327_, v_userName_2328_);
lean_dec(v_userName_2328_);
lean_dec_ref(v_lctx_2327_);
v_r_2330_ = lean_box(v_res_2329_);
return v_r_2330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(lean_object* v_lctx_2331_, lean_object* v_suggestion_2332_, lean_object* v_i_2333_){
_start:
{
lean_object* v_curr_2334_; uint8_t v___x_2335_; 
lean_inc(v_i_2333_);
lean_inc(v_suggestion_2332_);
v_curr_2334_ = lean_name_append_index_after(v_suggestion_2332_, v_i_2333_);
v___x_2335_ = l_Lean_LocalContext_usesUserName(v_lctx_2331_, v_curr_2334_);
if (v___x_2335_ == 0)
{
lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; 
lean_dec(v_suggestion_2332_);
v___x_2336_ = lean_unsigned_to_nat(1u);
v___x_2337_ = lean_nat_add(v_i_2333_, v___x_2336_);
lean_dec(v_i_2333_);
v___x_2338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2338_, 0, v_curr_2334_);
lean_ctor_set(v___x_2338_, 1, v___x_2337_);
return v___x_2338_;
}
else
{
lean_object* v___x_2339_; lean_object* v___x_2340_; 
lean_dec(v_curr_2334_);
v___x_2339_ = lean_unsigned_to_nat(1u);
v___x_2340_ = lean_nat_add(v_i_2333_, v___x_2339_);
lean_dec(v_i_2333_);
v_i_2333_ = v___x_2340_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux___boxed(lean_object* v_lctx_2342_, lean_object* v_suggestion_2343_, lean_object* v_i_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(v_lctx_2342_, v_suggestion_2343_, v_i_2344_);
lean_dec_ref(v_lctx_2342_);
return v_res_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getUnusedName(lean_object* v_lctx_2346_, lean_object* v_suggestion_2347_){
_start:
{
lean_object* v_suggestion_2348_; uint8_t v___x_2349_; 
v_suggestion_2348_ = l_Lean_Name_eraseMacroScopes(v_suggestion_2347_);
v___x_2349_ = l_Lean_LocalContext_usesUserName(v_lctx_2346_, v_suggestion_2348_);
if (v___x_2349_ == 0)
{
return v_suggestion_2348_;
}
else
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v_fst_2352_; 
v___x_2350_ = lean_unsigned_to_nat(1u);
v___x_2351_ = l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(v_lctx_2346_, v_suggestion_2348_, v___x_2350_);
v_fst_2352_ = lean_ctor_get(v___x_2351_, 0);
lean_inc(v_fst_2352_);
lean_dec_ref(v___x_2351_);
return v_fst_2352_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getUnusedName___boxed(lean_object* v_lctx_2353_, lean_object* v_suggestion_2354_){
_start:
{
lean_object* v_res_2355_; 
v_res_2355_ = l_Lean_LocalContext_getUnusedName(v_lctx_2353_, v_suggestion_2354_);
lean_dec(v_suggestion_2354_);
lean_dec_ref(v_lctx_2353_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_lastDecl(lean_object* v_lctx_2356_){
_start:
{
lean_object* v_decls_2357_; lean_object* v_size_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; uint8_t v___x_2362_; 
v_decls_2357_ = lean_ctor_get(v_lctx_2356_, 1);
v_size_2358_ = lean_ctor_get(v_decls_2357_, 2);
v___x_2359_ = lean_box(0);
v___x_2360_ = lean_unsigned_to_nat(1u);
v___x_2361_ = lean_nat_sub(v_size_2358_, v___x_2360_);
v___x_2362_ = lean_nat_dec_lt(v___x_2361_, v_size_2358_);
if (v___x_2362_ == 0)
{
lean_object* v___x_2363_; 
lean_dec(v___x_2361_);
v___x_2363_ = l_outOfBounds___redArg(v___x_2359_);
return v___x_2363_;
}
else
{
lean_object* v___x_2364_; 
v___x_2364_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2359_, v_decls_2357_, v___x_2361_);
lean_dec(v___x_2361_);
return v___x_2364_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_lastDecl___boxed(lean_object* v_lctx_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l_Lean_LocalContext_lastDecl(v_lctx_2365_);
lean_dec_ref(v_lctx_2365_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setUserName(lean_object* v_lctx_2367_, lean_object* v_fvarId_2368_, lean_object* v_userName_2369_){
_start:
{
lean_object* v_fvarIdToDecl_2370_; lean_object* v_decls_2371_; lean_object* v_auxDeclToFullName_2372_; lean_object* v_decl_2373_; lean_object* v_decl_2374_; lean_object* v___y_2376_; lean_object* v___y_2377_; lean_object* v___y_2382_; lean_object* v_fvarId_2385_; 
v_fvarIdToDecl_2370_ = lean_ctor_get(v_lctx_2367_, 0);
lean_inc_ref(v_fvarIdToDecl_2370_);
v_decls_2371_ = lean_ctor_get(v_lctx_2367_, 1);
lean_inc_ref(v_decls_2371_);
v_auxDeclToFullName_2372_ = lean_ctor_get(v_lctx_2367_, 2);
lean_inc(v_auxDeclToFullName_2372_);
v_decl_2373_ = l_Lean_LocalContext_get_x21(v_lctx_2367_, v_fvarId_2368_);
v_decl_2374_ = l_Lean_LocalDecl_setUserName(v_decl_2373_, v_userName_2369_);
v_fvarId_2385_ = lean_ctor_get(v_decl_2374_, 1);
lean_inc(v_fvarId_2385_);
v___y_2382_ = v_fvarId_2385_;
goto v___jp_2381_;
v___jp_2375_:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2378_, 0, v_decl_2374_);
v___x_2379_ = l_Lean_PersistentArray_set___redArg(v_decls_2371_, v___y_2377_, v___x_2378_);
lean_dec(v___y_2377_);
v___x_2380_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2380_, 0, v___y_2376_);
lean_ctor_set(v___x_2380_, 1, v___x_2379_);
lean_ctor_set(v___x_2380_, 2, v_auxDeclToFullName_2372_);
return v___x_2380_;
}
v___jp_2381_:
{
lean_object* v___x_2383_; lean_object* v_index_2384_; 
lean_inc_ref(v_decl_2374_);
v___x_2383_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2370_, v___y_2382_, v_decl_2374_);
v_index_2384_ = lean_ctor_get(v_decl_2374_, 0);
lean_inc(v_index_2384_);
v___y_2376_ = v___x_2383_;
v___y_2377_ = v_index_2384_;
goto v___jp_2375_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_renameUserName(lean_object* v_lctx_2386_, lean_object* v_fromName_2387_, lean_object* v_toName_2388_){
_start:
{
lean_object* v_fvarIdToDecl_2389_; lean_object* v_decls_2390_; lean_object* v_auxDeclToFullName_2391_; lean_object* v___x_2392_; 
v_fvarIdToDecl_2389_ = lean_ctor_get(v_lctx_2386_, 0);
v_decls_2390_ = lean_ctor_get(v_lctx_2386_, 1);
v_auxDeclToFullName_2391_ = lean_ctor_get(v_lctx_2386_, 2);
v___x_2392_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2386_, v_fromName_2387_);
if (lean_obj_tag(v___x_2392_) == 0)
{
lean_dec(v_toName_2388_);
return v_lctx_2386_;
}
else
{
lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2417_; 
lean_inc(v_auxDeclToFullName_2391_);
lean_inc_ref(v_decls_2390_);
lean_inc_ref(v_fvarIdToDecl_2389_);
v_isSharedCheck_2417_ = !lean_is_exclusive(v_lctx_2386_);
if (v_isSharedCheck_2417_ == 0)
{
lean_object* v_unused_2418_; lean_object* v_unused_2419_; lean_object* v_unused_2420_; 
v_unused_2418_ = lean_ctor_get(v_lctx_2386_, 2);
lean_dec(v_unused_2418_);
v_unused_2419_ = lean_ctor_get(v_lctx_2386_, 1);
lean_dec(v_unused_2419_);
v_unused_2420_ = lean_ctor_get(v_lctx_2386_, 0);
lean_dec(v_unused_2420_);
v___x_2394_ = v_lctx_2386_;
v_isShared_2395_ = v_isSharedCheck_2417_;
goto v_resetjp_2393_;
}
else
{
lean_dec(v_lctx_2386_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2417_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v_val_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2416_; 
v_val_2396_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2398_ = v___x_2392_;
v_isShared_2399_ = v_isSharedCheck_2416_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_val_2396_);
lean_dec(v___x_2392_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2416_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v_decl_2400_; lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2412_; lean_object* v_fvarId_2415_; 
v_decl_2400_ = l_Lean_LocalDecl_setUserName(v_val_2396_, v_toName_2388_);
v_fvarId_2415_ = lean_ctor_get(v_decl_2400_, 1);
lean_inc(v_fvarId_2415_);
v___y_2412_ = v_fvarId_2415_;
goto v___jp_2411_;
v___jp_2401_:
{
lean_object* v___x_2405_; 
if (v_isShared_2399_ == 0)
{
lean_ctor_set(v___x_2398_, 0, v_decl_2400_);
v___x_2405_ = v___x_2398_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_decl_2400_);
v___x_2405_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
lean_object* v___x_2406_; lean_object* v___x_2408_; 
v___x_2406_ = l_Lean_PersistentArray_set___redArg(v_decls_2390_, v___y_2403_, v___x_2405_);
lean_dec(v___y_2403_);
if (v_isShared_2395_ == 0)
{
lean_ctor_set(v___x_2394_, 1, v___x_2406_);
lean_ctor_set(v___x_2394_, 0, v___y_2402_);
v___x_2408_ = v___x_2394_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v___y_2402_);
lean_ctor_set(v_reuseFailAlloc_2409_, 1, v___x_2406_);
lean_ctor_set(v_reuseFailAlloc_2409_, 2, v_auxDeclToFullName_2391_);
v___x_2408_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
return v___x_2408_;
}
}
}
v___jp_2411_:
{
lean_object* v___x_2413_; lean_object* v_index_2414_; 
lean_inc_ref(v_decl_2400_);
v___x_2413_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2389_, v___y_2412_, v_decl_2400_);
v_index_2414_ = lean_ctor_get(v_decl_2400_, 0);
lean_inc(v_index_2414_);
v___y_2402_ = v___x_2413_;
v___y_2403_ = v_index_2414_;
goto v___jp_2401_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_renameUserName___boxed(lean_object* v_lctx_2421_, lean_object* v_fromName_2422_, lean_object* v_toName_2423_){
_start:
{
lean_object* v_res_2424_; 
v_res_2424_ = l_Lean_LocalContext_renameUserName(v_lctx_2421_, v_fromName_2422_, v_toName_2423_);
lean_dec(v_fromName_2422_);
return v_res_2424_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_modifyLocalDecl(lean_object* v_lctx_2427_, lean_object* v_fvarId_2428_, lean_object* v_f_2429_){
_start:
{
lean_object* v_fvarIdToDecl_2430_; lean_object* v_decls_2431_; lean_object* v_auxDeclToFullName_2432_; lean_object* v___x_2433_; 
v_fvarIdToDecl_2430_ = lean_ctor_get(v_lctx_2427_, 0);
v_decls_2431_ = lean_ctor_get(v_lctx_2427_, 1);
v_auxDeclToFullName_2432_ = lean_ctor_get(v_lctx_2427_, 2);
lean_inc_ref(v_lctx_2427_);
v___x_2433_ = lean_local_ctx_find(v_lctx_2427_, v_fvarId_2428_);
if (lean_obj_tag(v___x_2433_) == 0)
{
lean_dec_ref(v_f_2429_);
return v_lctx_2427_;
}
else
{
lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2460_; 
lean_inc(v_auxDeclToFullName_2432_);
lean_inc_ref(v_decls_2431_);
lean_inc_ref(v_fvarIdToDecl_2430_);
v_isSharedCheck_2460_ = !lean_is_exclusive(v_lctx_2427_);
if (v_isSharedCheck_2460_ == 0)
{
lean_object* v_unused_2461_; lean_object* v_unused_2462_; lean_object* v_unused_2463_; 
v_unused_2461_ = lean_ctor_get(v_lctx_2427_, 2);
lean_dec(v_unused_2461_);
v_unused_2462_ = lean_ctor_get(v_lctx_2427_, 1);
lean_dec(v_unused_2462_);
v_unused_2463_ = lean_ctor_get(v_lctx_2427_, 0);
lean_dec(v_unused_2463_);
v___x_2435_ = v_lctx_2427_;
v_isShared_2436_ = v_isSharedCheck_2460_;
goto v_resetjp_2434_;
}
else
{
lean_dec(v_lctx_2427_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2460_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v_val_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2459_; 
v_val_2437_ = lean_ctor_get(v___x_2433_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2439_ = v___x_2433_;
v_isShared_2440_ = v_isSharedCheck_2459_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_val_2437_);
lean_dec(v___x_2433_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2459_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v_decl_2443_; lean_object* v___y_2445_; lean_object* v___y_2446_; lean_object* v___y_2455_; lean_object* v_fvarId_2458_; 
v___x_2441_ = ((lean_object*)(l_Lean_LocalContext_modifyLocalDecl___closed__0));
v___x_2442_ = ((lean_object*)(l_Lean_LocalContext_modifyLocalDecl___closed__1));
v_decl_2443_ = lean_apply_1(v_f_2429_, v_val_2437_);
v_fvarId_2458_ = lean_ctor_get(v_decl_2443_, 1);
lean_inc(v_fvarId_2458_);
v___y_2455_ = v_fvarId_2458_;
goto v___jp_2454_;
v___jp_2444_:
{
lean_object* v___x_2448_; 
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 0, v_decl_2443_);
v___x_2448_ = v___x_2439_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_decl_2443_);
v___x_2448_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
lean_object* v___x_2449_; lean_object* v___x_2451_; 
v___x_2449_ = l_Lean_PersistentArray_set___redArg(v_decls_2431_, v___y_2446_, v___x_2448_);
lean_dec(v___y_2446_);
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 1, v___x_2449_);
lean_ctor_set(v___x_2435_, 0, v___y_2445_);
v___x_2451_ = v___x_2435_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v___y_2445_);
lean_ctor_set(v_reuseFailAlloc_2452_, 1, v___x_2449_);
lean_ctor_set(v_reuseFailAlloc_2452_, 2, v_auxDeclToFullName_2432_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
v___jp_2454_:
{
lean_object* v___x_2456_; lean_object* v_index_2457_; 
lean_inc_ref(v_decl_2443_);
v___x_2456_ = l_Lean_PersistentHashMap_insert___redArg(v___x_2441_, v___x_2442_, v_fvarIdToDecl_2430_, v___y_2455_, v_decl_2443_);
v_index_2457_ = lean_ctor_get(v_decl_2443_, 0);
lean_inc(v_index_2457_);
v___y_2445_ = v___x_2456_;
v___y_2446_ = v_index_2457_;
goto v___jp_2444_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(lean_object* v_f_2464_, lean_object* v_as_2465_, size_t v_i_2466_, size_t v_stop_2467_, lean_object* v_b_2468_){
_start:
{
lean_object* v___y_2470_; uint8_t v___x_2474_; 
v___x_2474_ = lean_usize_dec_eq(v_i_2466_, v_stop_2467_);
if (v___x_2474_ == 0)
{
lean_object* v___x_2475_; 
v___x_2475_ = lean_array_uget(v_as_2465_, v_i_2466_);
if (lean_obj_tag(v___x_2475_) == 0)
{
v___y_2470_ = v_b_2468_;
goto v___jp_2469_;
}
else
{
lean_object* v_val_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2503_; 
v_val_2476_ = lean_ctor_get(v___x_2475_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2478_ = v___x_2475_;
v_isShared_2479_ = v_isSharedCheck_2503_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_val_2476_);
lean_dec(v___x_2475_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2503_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v_fvarIdToDecl_2480_; lean_object* v_decls_2481_; lean_object* v_auxDeclToFullName_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2502_; 
v_fvarIdToDecl_2480_ = lean_ctor_get(v_b_2468_, 0);
v_decls_2481_ = lean_ctor_get(v_b_2468_, 1);
v_auxDeclToFullName_2482_ = lean_ctor_get(v_b_2468_, 2);
v_isSharedCheck_2502_ = !lean_is_exclusive(v_b_2468_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2484_ = v_b_2468_;
v_isShared_2485_ = v_isSharedCheck_2502_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_auxDeclToFullName_2482_);
lean_inc(v_decls_2481_);
lean_inc(v_fvarIdToDecl_2480_);
lean_dec(v_b_2468_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2502_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v_decl_2486_; lean_object* v___y_2488_; lean_object* v___y_2489_; lean_object* v___y_2498_; lean_object* v_fvarId_2501_; 
lean_inc_ref(v_f_2464_);
v_decl_2486_ = lean_apply_1(v_f_2464_, v_val_2476_);
v_fvarId_2501_ = lean_ctor_get(v_decl_2486_, 1);
lean_inc(v_fvarId_2501_);
v___y_2498_ = v_fvarId_2501_;
goto v___jp_2497_;
v___jp_2487_:
{
lean_object* v___x_2491_; 
if (v_isShared_2479_ == 0)
{
lean_ctor_set(v___x_2478_, 0, v_decl_2486_);
v___x_2491_ = v___x_2478_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_decl_2486_);
v___x_2491_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
lean_object* v___x_2492_; lean_object* v___x_2494_; 
v___x_2492_ = l_Lean_PersistentArray_set___redArg(v_decls_2481_, v___y_2489_, v___x_2491_);
lean_dec(v___y_2489_);
if (v_isShared_2485_ == 0)
{
lean_ctor_set(v___x_2484_, 1, v___x_2492_);
lean_ctor_set(v___x_2484_, 0, v___y_2488_);
v___x_2494_ = v___x_2484_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v___y_2488_);
lean_ctor_set(v_reuseFailAlloc_2495_, 1, v___x_2492_);
lean_ctor_set(v_reuseFailAlloc_2495_, 2, v_auxDeclToFullName_2482_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
v___y_2470_ = v___x_2494_;
goto v___jp_2469_;
}
}
}
v___jp_2497_:
{
lean_object* v___x_2499_; lean_object* v_index_2500_; 
lean_inc_ref(v_decl_2486_);
v___x_2499_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2480_, v___y_2498_, v_decl_2486_);
v_index_2500_ = lean_ctor_get(v_decl_2486_, 0);
lean_inc(v_index_2500_);
v___y_2488_ = v___x_2499_;
v___y_2489_ = v_index_2500_;
goto v___jp_2487_;
}
}
}
}
}
else
{
lean_dec_ref(v_f_2464_);
return v_b_2468_;
}
v___jp_2469_:
{
size_t v___x_2471_; size_t v___x_2472_; 
v___x_2471_ = ((size_t)1ULL);
v___x_2472_ = lean_usize_add(v_i_2466_, v___x_2471_);
v_i_2466_ = v___x_2472_;
v_b_2468_ = v___y_2470_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1___boxed(lean_object* v_f_2504_, lean_object* v_as_2505_, lean_object* v_i_2506_, lean_object* v_stop_2507_, lean_object* v_b_2508_){
_start:
{
size_t v_i_boxed_2509_; size_t v_stop_boxed_2510_; lean_object* v_res_2511_; 
v_i_boxed_2509_ = lean_unbox_usize(v_i_2506_);
lean_dec(v_i_2506_);
v_stop_boxed_2510_ = lean_unbox_usize(v_stop_2507_);
lean_dec(v_stop_2507_);
v_res_2511_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2504_, v_as_2505_, v_i_boxed_2509_, v_stop_boxed_2510_, v_b_2508_);
lean_dec_ref(v_as_2505_);
return v_res_2511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(lean_object* v_f_2512_, lean_object* v_x_2513_, lean_object* v_x_2514_){
_start:
{
if (lean_obj_tag(v_x_2513_) == 0)
{
lean_object* v_cs_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; uint8_t v___x_2518_; 
v_cs_2515_ = lean_ctor_get(v_x_2513_, 0);
v___x_2516_ = lean_unsigned_to_nat(0u);
v___x_2517_ = lean_array_get_size(v_cs_2515_);
v___x_2518_ = lean_nat_dec_lt(v___x_2516_, v___x_2517_);
if (v___x_2518_ == 0)
{
lean_dec_ref(v_f_2512_);
return v_x_2514_;
}
else
{
size_t v___x_2519_; size_t v___x_2520_; lean_object* v___x_2521_; 
v___x_2519_ = ((size_t)0ULL);
v___x_2520_ = lean_usize_of_nat(v___x_2517_);
v___x_2521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2512_, v_cs_2515_, v___x_2519_, v___x_2520_, v_x_2514_);
return v___x_2521_;
}
}
else
{
lean_object* v_vs_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; uint8_t v___x_2525_; 
v_vs_2522_ = lean_ctor_get(v_x_2513_, 0);
v___x_2523_ = lean_unsigned_to_nat(0u);
v___x_2524_ = lean_array_get_size(v_vs_2522_);
v___x_2525_ = lean_nat_dec_lt(v___x_2523_, v___x_2524_);
if (v___x_2525_ == 0)
{
lean_dec_ref(v_f_2512_);
return v_x_2514_;
}
else
{
size_t v___x_2526_; size_t v___x_2527_; lean_object* v___x_2528_; 
v___x_2526_ = ((size_t)0ULL);
v___x_2527_ = lean_usize_of_nat(v___x_2524_);
v___x_2528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2512_, v_vs_2522_, v___x_2526_, v___x_2527_, v_x_2514_);
return v___x_2528_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(lean_object* v_f_2529_, lean_object* v_as_2530_, size_t v_i_2531_, size_t v_stop_2532_, lean_object* v_b_2533_){
_start:
{
uint8_t v___x_2534_; 
v___x_2534_ = lean_usize_dec_eq(v_i_2531_, v_stop_2532_);
if (v___x_2534_ == 0)
{
lean_object* v___x_2535_; lean_object* v___x_2536_; size_t v___x_2537_; size_t v___x_2538_; 
v___x_2535_ = lean_array_uget_borrowed(v_as_2530_, v_i_2531_);
lean_inc_ref(v_f_2529_);
v___x_2536_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(v_f_2529_, v___x_2535_, v_b_2533_);
v___x_2537_ = ((size_t)1ULL);
v___x_2538_ = lean_usize_add(v_i_2531_, v___x_2537_);
v_i_2531_ = v___x_2538_;
v_b_2533_ = v___x_2536_;
goto _start;
}
else
{
lean_dec_ref(v_f_2529_);
return v_b_2533_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1___boxed(lean_object* v_f_2540_, lean_object* v_as_2541_, lean_object* v_i_2542_, lean_object* v_stop_2543_, lean_object* v_b_2544_){
_start:
{
size_t v_i_boxed_2545_; size_t v_stop_boxed_2546_; lean_object* v_res_2547_; 
v_i_boxed_2545_ = lean_unbox_usize(v_i_2542_);
lean_dec(v_i_2542_);
v_stop_boxed_2546_ = lean_unbox_usize(v_stop_2543_);
lean_dec(v_stop_2543_);
v_res_2547_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2540_, v_as_2541_, v_i_boxed_2545_, v_stop_boxed_2546_, v_b_2544_);
lean_dec_ref(v_as_2541_);
return v_res_2547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2___boxed(lean_object* v_f_2548_, lean_object* v_x_2549_, lean_object* v_x_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(v_f_2548_, v_x_2549_, v_x_2550_);
lean_dec_ref(v_x_2549_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(lean_object* v_f_2552_, lean_object* v_x_2553_, size_t v_x_2554_, size_t v_x_2555_, lean_object* v_x_2556_){
_start:
{
if (lean_obj_tag(v_x_2553_) == 0)
{
lean_object* v_cs_2557_; lean_object* v___x_2558_; size_t v___x_2559_; lean_object* v_j_2560_; lean_object* v___x_2561_; size_t v___x_2562_; size_t v___x_2563_; size_t v___x_2564_; size_t v___x_2565_; size_t v___x_2566_; size_t v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; uint8_t v___x_2572_; 
v_cs_2557_ = lean_ctor_get(v_x_2553_, 0);
v___x_2558_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0);
v___x_2559_ = lean_usize_shift_right(v_x_2554_, v_x_2555_);
v_j_2560_ = lean_usize_to_nat(v___x_2559_);
v___x_2561_ = lean_array_get_borrowed(v___x_2558_, v_cs_2557_, v_j_2560_);
v___x_2562_ = ((size_t)1ULL);
v___x_2563_ = lean_usize_shift_left(v___x_2562_, v_x_2555_);
v___x_2564_ = lean_usize_sub(v___x_2563_, v___x_2562_);
v___x_2565_ = lean_usize_land(v_x_2554_, v___x_2564_);
v___x_2566_ = ((size_t)5ULL);
v___x_2567_ = lean_usize_sub(v_x_2555_, v___x_2566_);
lean_inc_ref(v_f_2552_);
v___x_2568_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(v_f_2552_, v___x_2561_, v___x_2565_, v___x_2567_, v_x_2556_);
v___x_2569_ = lean_unsigned_to_nat(1u);
v___x_2570_ = lean_nat_add(v_j_2560_, v___x_2569_);
lean_dec(v_j_2560_);
v___x_2571_ = lean_array_get_size(v_cs_2557_);
v___x_2572_ = lean_nat_dec_lt(v___x_2570_, v___x_2571_);
if (v___x_2572_ == 0)
{
lean_dec(v___x_2570_);
lean_dec_ref(v_f_2552_);
return v___x_2568_;
}
else
{
size_t v___x_2573_; size_t v___x_2574_; lean_object* v___x_2575_; 
v___x_2573_ = lean_usize_of_nat(v___x_2570_);
lean_dec(v___x_2570_);
v___x_2574_ = lean_usize_of_nat(v___x_2571_);
v___x_2575_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2552_, v_cs_2557_, v___x_2573_, v___x_2574_, v___x_2568_);
return v___x_2575_;
}
}
else
{
lean_object* v_vs_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; uint8_t v___x_2579_; 
v_vs_2576_ = lean_ctor_get(v_x_2553_, 0);
v___x_2577_ = lean_usize_to_nat(v_x_2554_);
v___x_2578_ = lean_array_get_size(v_vs_2576_);
v___x_2579_ = lean_nat_dec_lt(v___x_2577_, v___x_2578_);
if (v___x_2579_ == 0)
{
lean_dec(v___x_2577_);
lean_dec_ref(v_f_2552_);
return v_x_2556_;
}
else
{
size_t v___x_2580_; size_t v___x_2581_; lean_object* v___x_2582_; 
v___x_2580_ = lean_usize_of_nat(v___x_2577_);
lean_dec(v___x_2577_);
v___x_2581_ = lean_usize_of_nat(v___x_2578_);
v___x_2582_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2552_, v_vs_2576_, v___x_2580_, v___x_2581_, v_x_2556_);
return v___x_2582_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0___boxed(lean_object* v_f_2583_, lean_object* v_x_2584_, lean_object* v_x_2585_, lean_object* v_x_2586_, lean_object* v_x_2587_){
_start:
{
size_t v_x_1489__boxed_2588_; size_t v_x_1490__boxed_2589_; lean_object* v_res_2590_; 
v_x_1489__boxed_2588_ = lean_unbox_usize(v_x_2585_);
lean_dec(v_x_2585_);
v_x_1490__boxed_2589_ = lean_unbox_usize(v_x_2586_);
lean_dec(v_x_2586_);
v_res_2590_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(v_f_2583_, v_x_2584_, v_x_1489__boxed_2588_, v_x_1490__boxed_2589_, v_x_2587_);
lean_dec_ref(v_x_2584_);
return v_res_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0(lean_object* v_f_2591_, lean_object* v_t_2592_, lean_object* v_init_2593_, lean_object* v_start_2594_){
_start:
{
lean_object* v___x_2595_; uint8_t v___x_2596_; 
v___x_2595_ = lean_unsigned_to_nat(0u);
v___x_2596_ = lean_nat_dec_eq(v_start_2594_, v___x_2595_);
if (v___x_2596_ == 0)
{
lean_object* v_root_2597_; lean_object* v_tail_2598_; size_t v_shift_2599_; lean_object* v_tailOff_2600_; uint8_t v___x_2601_; 
v_root_2597_ = lean_ctor_get(v_t_2592_, 0);
v_tail_2598_ = lean_ctor_get(v_t_2592_, 1);
v_shift_2599_ = lean_ctor_get_usize(v_t_2592_, 4);
v_tailOff_2600_ = lean_ctor_get(v_t_2592_, 3);
v___x_2601_ = lean_nat_dec_le(v_tailOff_2600_, v_start_2594_);
if (v___x_2601_ == 0)
{
size_t v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; uint8_t v___x_2605_; 
v___x_2602_ = lean_usize_of_nat(v_start_2594_);
lean_inc_ref(v_f_2591_);
v___x_2603_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(v_f_2591_, v_root_2597_, v___x_2602_, v_shift_2599_, v_init_2593_);
v___x_2604_ = lean_array_get_size(v_tail_2598_);
v___x_2605_ = lean_nat_dec_lt(v___x_2595_, v___x_2604_);
if (v___x_2605_ == 0)
{
lean_dec_ref(v_f_2591_);
return v___x_2603_;
}
else
{
size_t v___x_2606_; size_t v___x_2607_; lean_object* v___x_2608_; 
v___x_2606_ = ((size_t)0ULL);
v___x_2607_ = lean_usize_of_nat(v___x_2604_);
v___x_2608_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2591_, v_tail_2598_, v___x_2606_, v___x_2607_, v___x_2603_);
return v___x_2608_;
}
}
else
{
lean_object* v___x_2609_; lean_object* v___x_2610_; uint8_t v___x_2611_; 
v___x_2609_ = lean_nat_sub(v_start_2594_, v_tailOff_2600_);
v___x_2610_ = lean_array_get_size(v_tail_2598_);
v___x_2611_ = lean_nat_dec_lt(v___x_2609_, v___x_2610_);
if (v___x_2611_ == 0)
{
lean_dec(v___x_2609_);
lean_dec_ref(v_f_2591_);
return v_init_2593_;
}
else
{
size_t v___x_2612_; size_t v___x_2613_; lean_object* v___x_2614_; 
v___x_2612_ = lean_usize_of_nat(v___x_2609_);
lean_dec(v___x_2609_);
v___x_2613_ = lean_usize_of_nat(v___x_2610_);
v___x_2614_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2591_, v_tail_2598_, v___x_2612_, v___x_2613_, v_init_2593_);
return v___x_2614_;
}
}
}
else
{
lean_object* v_root_2615_; lean_object* v_tail_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; uint8_t v___x_2619_; 
v_root_2615_ = lean_ctor_get(v_t_2592_, 0);
v_tail_2616_ = lean_ctor_get(v_t_2592_, 1);
lean_inc_ref(v_f_2591_);
v___x_2617_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(v_f_2591_, v_root_2615_, v_init_2593_);
v___x_2618_ = lean_array_get_size(v_tail_2616_);
v___x_2619_ = lean_nat_dec_lt(v___x_2595_, v___x_2618_);
if (v___x_2619_ == 0)
{
lean_dec_ref(v_f_2591_);
return v___x_2617_;
}
else
{
size_t v___x_2620_; size_t v___x_2621_; lean_object* v___x_2622_; 
v___x_2620_ = ((size_t)0ULL);
v___x_2621_ = lean_usize_of_nat(v___x_2618_);
v___x_2622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2591_, v_tail_2616_, v___x_2620_, v___x_2621_, v___x_2617_);
return v___x_2622_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0___boxed(lean_object* v_f_2623_, lean_object* v_t_2624_, lean_object* v_init_2625_, lean_object* v_start_2626_){
_start:
{
lean_object* v_res_2627_; 
v_res_2627_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0(v_f_2623_, v_t_2624_, v_init_2625_, v_start_2626_);
lean_dec(v_start_2626_);
lean_dec_ref(v_t_2624_);
return v_res_2627_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_modifyLocalDecls(lean_object* v_lctx_2628_, lean_object* v_f_2629_){
_start:
{
lean_object* v_decls_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; 
v_decls_2630_ = lean_ctor_get(v_lctx_2628_, 1);
lean_inc_ref(v_decls_2630_);
v___x_2631_ = lean_unsigned_to_nat(0u);
v___x_2632_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0(v_f_2629_, v_decls_2630_, v_lctx_2628_, v___x_2631_);
lean_dec_ref(v_decls_2630_);
return v___x_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setKind(lean_object* v_lctx_2633_, lean_object* v_fvarId_2634_, uint8_t v_kind_2635_){
_start:
{
lean_object* v_fvarIdToDecl_2636_; lean_object* v_decls_2637_; lean_object* v_auxDeclToFullName_2638_; lean_object* v___x_2639_; 
v_fvarIdToDecl_2636_ = lean_ctor_get(v_lctx_2633_, 0);
v_decls_2637_ = lean_ctor_get(v_lctx_2633_, 1);
v_auxDeclToFullName_2638_ = lean_ctor_get(v_lctx_2633_, 2);
lean_inc_ref(v_lctx_2633_);
v___x_2639_ = lean_local_ctx_find(v_lctx_2633_, v_fvarId_2634_);
if (lean_obj_tag(v___x_2639_) == 0)
{
return v_lctx_2633_;
}
else
{
lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2664_; 
lean_inc(v_auxDeclToFullName_2638_);
lean_inc_ref(v_decls_2637_);
lean_inc_ref(v_fvarIdToDecl_2636_);
v_isSharedCheck_2664_ = !lean_is_exclusive(v_lctx_2633_);
if (v_isSharedCheck_2664_ == 0)
{
lean_object* v_unused_2665_; lean_object* v_unused_2666_; lean_object* v_unused_2667_; 
v_unused_2665_ = lean_ctor_get(v_lctx_2633_, 2);
lean_dec(v_unused_2665_);
v_unused_2666_ = lean_ctor_get(v_lctx_2633_, 1);
lean_dec(v_unused_2666_);
v_unused_2667_ = lean_ctor_get(v_lctx_2633_, 0);
lean_dec(v_unused_2667_);
v___x_2641_ = v_lctx_2633_;
v_isShared_2642_ = v_isSharedCheck_2664_;
goto v_resetjp_2640_;
}
else
{
lean_dec(v_lctx_2633_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2664_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v_val_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2663_; 
v_val_2643_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2645_ = v___x_2639_;
v_isShared_2646_ = v_isSharedCheck_2663_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_val_2643_);
lean_dec(v___x_2639_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2663_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v_decl_2647_; lean_object* v___y_2649_; lean_object* v___y_2650_; lean_object* v___y_2659_; lean_object* v_fvarId_2662_; 
v_decl_2647_ = l_Lean_LocalDecl_setKind(v_val_2643_, v_kind_2635_);
v_fvarId_2662_ = lean_ctor_get(v_decl_2647_, 1);
lean_inc(v_fvarId_2662_);
v___y_2659_ = v_fvarId_2662_;
goto v___jp_2658_;
v___jp_2648_:
{
lean_object* v___x_2652_; 
if (v_isShared_2646_ == 0)
{
lean_ctor_set(v___x_2645_, 0, v_decl_2647_);
v___x_2652_ = v___x_2645_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_decl_2647_);
v___x_2652_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
lean_object* v___x_2653_; lean_object* v___x_2655_; 
v___x_2653_ = l_Lean_PersistentArray_set___redArg(v_decls_2637_, v___y_2650_, v___x_2652_);
lean_dec(v___y_2650_);
if (v_isShared_2642_ == 0)
{
lean_ctor_set(v___x_2641_, 1, v___x_2653_);
lean_ctor_set(v___x_2641_, 0, v___y_2649_);
v___x_2655_ = v___x_2641_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v___y_2649_);
lean_ctor_set(v_reuseFailAlloc_2656_, 1, v___x_2653_);
lean_ctor_set(v_reuseFailAlloc_2656_, 2, v_auxDeclToFullName_2638_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
}
v___jp_2658_:
{
lean_object* v___x_2660_; lean_object* v_index_2661_; 
lean_inc_ref(v_decl_2647_);
v___x_2660_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2636_, v___y_2659_, v_decl_2647_);
v_index_2661_ = lean_ctor_get(v_decl_2647_, 0);
lean_inc(v_index_2661_);
v___y_2649_ = v___x_2660_;
v___y_2650_ = v_index_2661_;
goto v___jp_2648_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setKind___boxed(lean_object* v_lctx_2668_, lean_object* v_fvarId_2669_, lean_object* v_kind_2670_){
_start:
{
uint8_t v_kind_boxed_2671_; lean_object* v_res_2672_; 
v_kind_boxed_2671_ = lean_unbox(v_kind_2670_);
v_res_2672_ = l_Lean_LocalContext_setKind(v_lctx_2668_, v_fvarId_2669_, v_kind_boxed_2671_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setBinderInfo(lean_object* v_lctx_2673_, lean_object* v_fvarId_2674_, uint8_t v_bi_2675_){
_start:
{
lean_object* v_fvarIdToDecl_2676_; lean_object* v_decls_2677_; lean_object* v_auxDeclToFullName_2678_; lean_object* v___x_2679_; 
v_fvarIdToDecl_2676_ = lean_ctor_get(v_lctx_2673_, 0);
v_decls_2677_ = lean_ctor_get(v_lctx_2673_, 1);
v_auxDeclToFullName_2678_ = lean_ctor_get(v_lctx_2673_, 2);
lean_inc_ref(v_lctx_2673_);
v___x_2679_ = lean_local_ctx_find(v_lctx_2673_, v_fvarId_2674_);
if (lean_obj_tag(v___x_2679_) == 0)
{
return v_lctx_2673_;
}
else
{
lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2704_; 
lean_inc(v_auxDeclToFullName_2678_);
lean_inc_ref(v_decls_2677_);
lean_inc_ref(v_fvarIdToDecl_2676_);
v_isSharedCheck_2704_ = !lean_is_exclusive(v_lctx_2673_);
if (v_isSharedCheck_2704_ == 0)
{
lean_object* v_unused_2705_; lean_object* v_unused_2706_; lean_object* v_unused_2707_; 
v_unused_2705_ = lean_ctor_get(v_lctx_2673_, 2);
lean_dec(v_unused_2705_);
v_unused_2706_ = lean_ctor_get(v_lctx_2673_, 1);
lean_dec(v_unused_2706_);
v_unused_2707_ = lean_ctor_get(v_lctx_2673_, 0);
lean_dec(v_unused_2707_);
v___x_2681_ = v_lctx_2673_;
v_isShared_2682_ = v_isSharedCheck_2704_;
goto v_resetjp_2680_;
}
else
{
lean_dec(v_lctx_2673_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2704_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v_val_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2703_; 
v_val_2683_ = lean_ctor_get(v___x_2679_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2685_ = v___x_2679_;
v_isShared_2686_ = v_isSharedCheck_2703_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_val_2683_);
lean_dec(v___x_2679_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2703_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v_decl_2687_; lean_object* v___y_2689_; lean_object* v___y_2690_; lean_object* v___y_2699_; lean_object* v_fvarId_2702_; 
v_decl_2687_ = l_Lean_LocalDecl_setBinderInfo(v_val_2683_, v_bi_2675_);
v_fvarId_2702_ = lean_ctor_get(v_decl_2687_, 1);
lean_inc(v_fvarId_2702_);
v___y_2699_ = v_fvarId_2702_;
goto v___jp_2698_;
v___jp_2688_:
{
lean_object* v___x_2692_; 
if (v_isShared_2686_ == 0)
{
lean_ctor_set(v___x_2685_, 0, v_decl_2687_);
v___x_2692_ = v___x_2685_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_decl_2687_);
v___x_2692_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
lean_object* v___x_2693_; lean_object* v___x_2695_; 
v___x_2693_ = l_Lean_PersistentArray_set___redArg(v_decls_2677_, v___y_2690_, v___x_2692_);
lean_dec(v___y_2690_);
if (v_isShared_2682_ == 0)
{
lean_ctor_set(v___x_2681_, 1, v___x_2693_);
lean_ctor_set(v___x_2681_, 0, v___y_2689_);
v___x_2695_ = v___x_2681_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v___y_2689_);
lean_ctor_set(v_reuseFailAlloc_2696_, 1, v___x_2693_);
lean_ctor_set(v_reuseFailAlloc_2696_, 2, v_auxDeclToFullName_2678_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
}
v___jp_2698_:
{
lean_object* v___x_2700_; lean_object* v_index_2701_; 
lean_inc_ref(v_decl_2687_);
v___x_2700_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2676_, v___y_2699_, v_decl_2687_);
v_index_2701_ = lean_ctor_get(v_decl_2687_, 0);
lean_inc(v_index_2701_);
v___y_2689_ = v___x_2700_;
v___y_2690_ = v_index_2701_;
goto v___jp_2688_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setBinderInfo___boxed(lean_object* v_lctx_2708_, lean_object* v_fvarId_2709_, lean_object* v_bi_2710_){
_start:
{
uint8_t v_bi_boxed_2711_; lean_object* v_res_2712_; 
v_bi_boxed_2711_ = lean_unbox(v_bi_2710_);
v_res_2712_ = l_Lean_LocalContext_setBinderInfo(v_lctx_2708_, v_fvarId_2709_, v_bi_boxed_2711_);
return v_res_2712_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setType(lean_object* v_lctx_2713_, lean_object* v_fvarId_2714_, lean_object* v_type_2715_){
_start:
{
lean_object* v_fvarIdToDecl_2716_; lean_object* v_decls_2717_; lean_object* v_auxDeclToFullName_2718_; lean_object* v___x_2719_; 
v_fvarIdToDecl_2716_ = lean_ctor_get(v_lctx_2713_, 0);
v_decls_2717_ = lean_ctor_get(v_lctx_2713_, 1);
v_auxDeclToFullName_2718_ = lean_ctor_get(v_lctx_2713_, 2);
lean_inc_ref(v_lctx_2713_);
v___x_2719_ = lean_local_ctx_find(v_lctx_2713_, v_fvarId_2714_);
if (lean_obj_tag(v___x_2719_) == 0)
{
lean_dec_ref(v_type_2715_);
return v_lctx_2713_;
}
else
{
lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2744_; 
lean_inc(v_auxDeclToFullName_2718_);
lean_inc_ref(v_decls_2717_);
lean_inc_ref(v_fvarIdToDecl_2716_);
v_isSharedCheck_2744_ = !lean_is_exclusive(v_lctx_2713_);
if (v_isSharedCheck_2744_ == 0)
{
lean_object* v_unused_2745_; lean_object* v_unused_2746_; lean_object* v_unused_2747_; 
v_unused_2745_ = lean_ctor_get(v_lctx_2713_, 2);
lean_dec(v_unused_2745_);
v_unused_2746_ = lean_ctor_get(v_lctx_2713_, 1);
lean_dec(v_unused_2746_);
v_unused_2747_ = lean_ctor_get(v_lctx_2713_, 0);
lean_dec(v_unused_2747_);
v___x_2721_ = v_lctx_2713_;
v_isShared_2722_ = v_isSharedCheck_2744_;
goto v_resetjp_2720_;
}
else
{
lean_dec(v_lctx_2713_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2744_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v_val_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2743_; 
v_val_2723_ = lean_ctor_get(v___x_2719_, 0);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2719_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2725_ = v___x_2719_;
v_isShared_2726_ = v_isSharedCheck_2743_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_val_2723_);
lean_dec(v___x_2719_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2743_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v_decl_2727_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v___y_2739_; lean_object* v_fvarId_2742_; 
v_decl_2727_ = l_Lean_LocalDecl_setType(v_val_2723_, v_type_2715_);
v_fvarId_2742_ = lean_ctor_get(v_decl_2727_, 1);
lean_inc(v_fvarId_2742_);
v___y_2739_ = v_fvarId_2742_;
goto v___jp_2738_;
v___jp_2728_:
{
lean_object* v___x_2732_; 
if (v_isShared_2726_ == 0)
{
lean_ctor_set(v___x_2725_, 0, v_decl_2727_);
v___x_2732_ = v___x_2725_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_decl_2727_);
v___x_2732_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
lean_object* v___x_2733_; lean_object* v___x_2735_; 
v___x_2733_ = l_Lean_PersistentArray_set___redArg(v_decls_2717_, v___y_2730_, v___x_2732_);
lean_dec(v___y_2730_);
if (v_isShared_2722_ == 0)
{
lean_ctor_set(v___x_2721_, 1, v___x_2733_);
lean_ctor_set(v___x_2721_, 0, v___y_2729_);
v___x_2735_ = v___x_2721_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v___y_2729_);
lean_ctor_set(v_reuseFailAlloc_2736_, 1, v___x_2733_);
lean_ctor_set(v_reuseFailAlloc_2736_, 2, v_auxDeclToFullName_2718_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
}
v___jp_2738_:
{
lean_object* v___x_2740_; lean_object* v_index_2741_; 
lean_inc_ref(v_decl_2727_);
v___x_2740_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2716_, v___y_2739_, v_decl_2727_);
v_index_2741_ = lean_ctor_get(v_decl_2727_, 0);
lean_inc(v_index_2741_);
v___y_2729_ = v___x_2740_;
v___y_2730_ = v_index_2741_;
goto v___jp_2728_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lean_local_ctx_num_indices(lean_object* v_lctx_2748_){
_start:
{
lean_object* v_decls_2749_; lean_object* v_size_2750_; 
v_decls_2749_ = lean_ctor_get(v_lctx_2748_, 1);
lean_inc_ref(v_decls_2749_);
lean_dec_ref(v_lctx_2748_);
v_size_2750_ = lean_ctor_get(v_decls_2749_, 2);
lean_inc(v_size_2750_);
lean_dec_ref(v_decls_2749_);
return v_size_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getAt_x3f(lean_object* v_lctx_2751_, lean_object* v_i_2752_){
_start:
{
lean_object* v_decls_2753_; lean_object* v_size_2754_; lean_object* v___x_2755_; uint8_t v___x_2756_; 
v_decls_2753_ = lean_ctor_get(v_lctx_2751_, 1);
v_size_2754_ = lean_ctor_get(v_decls_2753_, 2);
v___x_2755_ = lean_box(0);
v___x_2756_ = lean_nat_dec_lt(v_i_2752_, v_size_2754_);
if (v___x_2756_ == 0)
{
lean_object* v___x_2757_; 
v___x_2757_ = l_outOfBounds___redArg(v___x_2755_);
return v___x_2757_;
}
else
{
lean_object* v___x_2758_; 
v___x_2758_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2755_, v_decls_2753_, v_i_2752_);
return v___x_2758_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getAt_x3f___boxed(lean_object* v_lctx_2759_, lean_object* v_i_2760_){
_start:
{
lean_object* v_res_2761_; 
v_res_2761_ = l_Lean_LocalContext_getAt_x3f(v_lctx_2759_, v_i_2760_);
lean_dec(v_i_2760_);
lean_dec_ref(v_lctx_2759_);
return v_res_2761_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg___lam__0(lean_object* v_toPure_2762_, lean_object* v_f_2763_, lean_object* v_b_2764_, lean_object* v_decl_2765_){
_start:
{
if (lean_obj_tag(v_decl_2765_) == 0)
{
lean_object* v___x_2766_; 
lean_dec(v_f_2763_);
v___x_2766_ = lean_apply_2(v_toPure_2762_, lean_box(0), v_b_2764_);
return v___x_2766_;
}
else
{
lean_object* v_val_2767_; lean_object* v___x_2768_; 
lean_dec(v_toPure_2762_);
v_val_2767_ = lean_ctor_get(v_decl_2765_, 0);
lean_inc(v_val_2767_);
lean_dec_ref_known(v_decl_2765_, 1);
v___x_2768_ = lean_apply_2(v_f_2763_, v_b_2764_, v_val_2767_);
return v___x_2768_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg(lean_object* v_inst_2769_, lean_object* v_lctx_2770_, lean_object* v_f_2771_, lean_object* v_init_2772_, lean_object* v_start_2773_){
_start:
{
lean_object* v_toApplicative_2774_; lean_object* v_decls_2775_; lean_object* v_toPure_2776_; lean_object* v___f_2777_; lean_object* v___x_2778_; 
v_toApplicative_2774_ = lean_ctor_get(v_inst_2769_, 0);
v_decls_2775_ = lean_ctor_get(v_lctx_2770_, 1);
lean_inc_ref(v_decls_2775_);
lean_dec_ref(v_lctx_2770_);
v_toPure_2776_ = lean_ctor_get(v_toApplicative_2774_, 1);
lean_inc(v_toPure_2776_);
v___f_2777_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldlM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2777_, 0, v_toPure_2776_);
lean_closure_set(v___f_2777_, 1, v_f_2771_);
v___x_2778_ = l_Lean_PersistentArray_foldlM___redArg(v_inst_2769_, v_decls_2775_, v___f_2777_, v_init_2772_, v_start_2773_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg___boxed(lean_object* v_inst_2779_, lean_object* v_lctx_2780_, lean_object* v_f_2781_, lean_object* v_init_2782_, lean_object* v_start_2783_){
_start:
{
lean_object* v_res_2784_; 
v_res_2784_ = l_Lean_LocalContext_foldlM___redArg(v_inst_2779_, v_lctx_2780_, v_f_2781_, v_init_2782_, v_start_2783_);
lean_dec(v_start_2783_);
return v_res_2784_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM(lean_object* v_m_2785_, lean_object* v_00_u03b2_2786_, lean_object* v_inst_2787_, lean_object* v_lctx_2788_, lean_object* v_f_2789_, lean_object* v_init_2790_, lean_object* v_start_2791_){
_start:
{
lean_object* v___x_2792_; 
v___x_2792_ = l_Lean_LocalContext_foldlM___redArg(v_inst_2787_, v_lctx_2788_, v_f_2789_, v_init_2790_, v_start_2791_);
return v___x_2792_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___boxed(lean_object* v_m_2793_, lean_object* v_00_u03b2_2794_, lean_object* v_inst_2795_, lean_object* v_lctx_2796_, lean_object* v_f_2797_, lean_object* v_init_2798_, lean_object* v_start_2799_){
_start:
{
lean_object* v_res_2800_; 
v_res_2800_ = l_Lean_LocalContext_foldlM(v_m_2793_, v_00_u03b2_2794_, v_inst_2795_, v_lctx_2796_, v_f_2797_, v_init_2798_, v_start_2799_);
lean_dec(v_start_2799_);
return v_res_2800_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___redArg___lam__0(lean_object* v_toPure_2801_, lean_object* v_f_2802_, lean_object* v_decl_2803_, lean_object* v_b_2804_){
_start:
{
if (lean_obj_tag(v_decl_2803_) == 0)
{
lean_object* v___x_2805_; 
lean_dec(v_f_2802_);
v___x_2805_ = lean_apply_2(v_toPure_2801_, lean_box(0), v_b_2804_);
return v___x_2805_;
}
else
{
lean_object* v_val_2806_; lean_object* v___x_2807_; 
lean_dec(v_toPure_2801_);
v_val_2806_ = lean_ctor_get(v_decl_2803_, 0);
lean_inc(v_val_2806_);
lean_dec_ref_known(v_decl_2803_, 1);
v___x_2807_ = lean_apply_2(v_f_2802_, v_val_2806_, v_b_2804_);
return v___x_2807_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___redArg(lean_object* v_inst_2808_, lean_object* v_lctx_2809_, lean_object* v_f_2810_, lean_object* v_init_2811_){
_start:
{
lean_object* v_toApplicative_2812_; lean_object* v_decls_2813_; lean_object* v_toPure_2814_; lean_object* v___f_2815_; lean_object* v___x_2816_; 
v_toApplicative_2812_ = lean_ctor_get(v_inst_2808_, 0);
v_decls_2813_ = lean_ctor_get(v_lctx_2809_, 1);
lean_inc_ref(v_decls_2813_);
lean_dec_ref(v_lctx_2809_);
v_toPure_2814_ = lean_ctor_get(v_toApplicative_2812_, 1);
lean_inc(v_toPure_2814_);
v___f_2815_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldrM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2815_, 0, v_toPure_2814_);
lean_closure_set(v___f_2815_, 1, v_f_2810_);
v___x_2816_ = l_Lean_PersistentArray_foldrM___redArg(v_inst_2808_, v_decls_2813_, v___f_2815_, v_init_2811_);
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM(lean_object* v_m_2817_, lean_object* v_00_u03b2_2818_, lean_object* v_inst_2819_, lean_object* v_lctx_2820_, lean_object* v_f_2821_, lean_object* v_init_2822_){
_start:
{
lean_object* v___x_2823_; 
v___x_2823_ = l_Lean_LocalContext_foldrM___redArg(v_inst_2819_, v_lctx_2820_, v_f_2821_, v_init_2822_);
return v___x_2823_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg___lam__0(lean_object* v_toPure_2824_, lean_object* v_f_2825_, lean_object* v_decl_2826_){
_start:
{
if (lean_obj_tag(v_decl_2826_) == 0)
{
lean_object* v___x_2827_; lean_object* v___x_2828_; 
lean_dec(v_f_2825_);
v___x_2827_ = lean_box(0);
v___x_2828_ = lean_apply_2(v_toPure_2824_, lean_box(0), v___x_2827_);
return v___x_2828_;
}
else
{
lean_object* v_val_2829_; lean_object* v___x_2830_; 
lean_dec(v_toPure_2824_);
v_val_2829_ = lean_ctor_get(v_decl_2826_, 0);
lean_inc(v_val_2829_);
lean_dec_ref_known(v_decl_2826_, 1);
v___x_2830_ = lean_apply_1(v_f_2825_, v_val_2829_);
return v___x_2830_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg(lean_object* v_inst_2831_, lean_object* v_lctx_2832_, lean_object* v_f_2833_, lean_object* v_start_2834_){
_start:
{
lean_object* v_toApplicative_2835_; lean_object* v_decls_2836_; lean_object* v_toPure_2837_; lean_object* v___f_2838_; lean_object* v___x_2839_; 
v_toApplicative_2835_ = lean_ctor_get(v_inst_2831_, 0);
v_decls_2836_ = lean_ctor_get(v_lctx_2832_, 1);
lean_inc_ref(v_decls_2836_);
lean_dec_ref(v_lctx_2832_);
v_toPure_2837_ = lean_ctor_get(v_toApplicative_2835_, 1);
lean_inc(v_toPure_2837_);
v___f_2838_ = lean_alloc_closure((void*)(l_Lean_LocalContext_forM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2838_, 0, v_toPure_2837_);
lean_closure_set(v___f_2838_, 1, v_f_2833_);
v___x_2839_ = l_Lean_PersistentArray_forM___redArg(v_inst_2831_, v_decls_2836_, v___f_2838_, v_start_2834_);
return v___x_2839_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg___boxed(lean_object* v_inst_2840_, lean_object* v_lctx_2841_, lean_object* v_f_2842_, lean_object* v_start_2843_){
_start:
{
lean_object* v_res_2844_; 
v_res_2844_ = l_Lean_LocalContext_forM___redArg(v_inst_2840_, v_lctx_2841_, v_f_2842_, v_start_2843_);
lean_dec(v_start_2843_);
return v_res_2844_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM(lean_object* v_m_2845_, lean_object* v_inst_2846_, lean_object* v_lctx_2847_, lean_object* v_f_2848_, lean_object* v_start_2849_){
_start:
{
lean_object* v___x_2850_; 
v___x_2850_ = l_Lean_LocalContext_forM___redArg(v_inst_2846_, v_lctx_2847_, v_f_2848_, v_start_2849_);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___boxed(lean_object* v_m_2851_, lean_object* v_inst_2852_, lean_object* v_lctx_2853_, lean_object* v_f_2854_, lean_object* v_start_2855_){
_start:
{
lean_object* v_res_2856_; 
v_res_2856_ = l_Lean_LocalContext_forM(v_m_2851_, v_inst_2852_, v_lctx_2853_, v_f_2854_, v_start_2855_);
lean_dec(v_start_2855_);
return v_res_2856_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0(lean_object* v_toPure_2857_, lean_object* v_f_2858_, lean_object* v_decl_2859_){
_start:
{
if (lean_obj_tag(v_decl_2859_) == 0)
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
lean_dec(v_f_2858_);
v___x_2860_ = lean_box(0);
v___x_2861_ = lean_apply_2(v_toPure_2857_, lean_box(0), v___x_2860_);
return v___x_2861_;
}
else
{
lean_object* v_val_2862_; lean_object* v___x_2863_; 
lean_dec(v_toPure_2857_);
v_val_2862_ = lean_ctor_get(v_decl_2859_, 0);
lean_inc(v_val_2862_);
lean_dec_ref_known(v_decl_2859_, 1);
v___x_2863_ = lean_apply_1(v_f_2858_, v_val_2862_);
return v___x_2863_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___redArg(lean_object* v_inst_2864_, lean_object* v_lctx_2865_, lean_object* v_f_2866_){
_start:
{
lean_object* v_toApplicative_2867_; lean_object* v_decls_2868_; lean_object* v_toPure_2869_; lean_object* v___f_2870_; lean_object* v___x_2871_; 
v_toApplicative_2867_ = lean_ctor_get(v_inst_2864_, 0);
v_decls_2868_ = lean_ctor_get(v_lctx_2865_, 1);
lean_inc_ref(v_decls_2868_);
lean_dec_ref(v_lctx_2865_);
v_toPure_2869_ = lean_ctor_get(v_toApplicative_2867_, 1);
lean_inc(v_toPure_2869_);
v___f_2870_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2870_, 0, v_toPure_2869_);
lean_closure_set(v___f_2870_, 1, v_f_2866_);
v___x_2871_ = l_Lean_PersistentArray_findSomeM_x3f___redArg(v_inst_2864_, v_decls_2868_, v___f_2870_);
return v___x_2871_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f(lean_object* v_m_2872_, lean_object* v_00_u03b2_2873_, lean_object* v_inst_2874_, lean_object* v_lctx_2875_, lean_object* v_f_2876_){
_start:
{
lean_object* v___x_2877_; 
v___x_2877_ = l_Lean_LocalContext_findDeclM_x3f___redArg(v_inst_2874_, v_lctx_2875_, v_f_2876_);
return v___x_2877_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___redArg(lean_object* v_inst_2878_, lean_object* v_lctx_2879_, lean_object* v_f_2880_){
_start:
{
lean_object* v_toApplicative_2881_; lean_object* v_decls_2882_; lean_object* v_toPure_2883_; lean_object* v___f_2884_; lean_object* v___x_2885_; 
v_toApplicative_2881_ = lean_ctor_get(v_inst_2878_, 0);
v_decls_2882_ = lean_ctor_get(v_lctx_2879_, 1);
lean_inc_ref(v_decls_2882_);
lean_dec_ref(v_lctx_2879_);
v_toPure_2883_ = lean_ctor_get(v_toApplicative_2881_, 1);
lean_inc(v_toPure_2883_);
v___f_2884_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2884_, 0, v_toPure_2883_);
lean_closure_set(v___f_2884_, 1, v_f_2880_);
v___x_2885_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v_inst_2878_, v_decls_2882_, v___f_2884_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f(lean_object* v_m_2886_, lean_object* v_00_u03b2_2887_, lean_object* v_inst_2888_, lean_object* v_lctx_2889_, lean_object* v_f_2890_){
_start:
{
lean_object* v___x_2891_; 
v___x_2891_ = l_Lean_LocalContext_findDeclRevM_x3f___redArg(v_inst_2888_, v_lctx_2889_, v_f_2890_);
return v___x_2891_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__0(lean_object* v_toPure_2892_, lean_object* v_f_2893_, lean_object* v_d_x3f_2894_, lean_object* v_b_2895_){
_start:
{
if (lean_obj_tag(v_d_x3f_2894_) == 0)
{
lean_object* v___x_2896_; lean_object* v___x_2897_; 
lean_dec(v_f_2893_);
v___x_2896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2896_, 0, v_b_2895_);
v___x_2897_ = lean_apply_2(v_toPure_2892_, lean_box(0), v___x_2896_);
return v___x_2897_;
}
else
{
lean_object* v_val_2898_; lean_object* v___x_2899_; 
lean_dec(v_toPure_2892_);
v_val_2898_ = lean_ctor_get(v_d_x3f_2894_, 0);
lean_inc(v_val_2898_);
lean_dec_ref_known(v_d_x3f_2894_, 1);
v___x_2899_ = lean_apply_2(v_f_2893_, v_val_2898_, v_b_2895_);
return v___x_2899_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1(lean_object* v_toPure_2900_, lean_object* v_inst_2901_, lean_object* v_00_u03b2_2902_, lean_object* v_lctx_2903_, lean_object* v_init_2904_, lean_object* v_f_2905_){
_start:
{
lean_object* v_decls_2906_; lean_object* v___f_2907_; lean_object* v___x_2908_; 
v_decls_2906_ = lean_ctor_get(v_lctx_2903_, 1);
v___f_2907_ = lean_alloc_closure((void*)(l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2907_, 0, v_toPure_2900_);
lean_closure_set(v___f_2907_, 1, v_f_2905_);
v___x_2908_ = l_Lean_PersistentArray_forIn___redArg(v_inst_2901_, v_decls_2906_, v_init_2904_, v___f_2907_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1___boxed(lean_object* v_toPure_2909_, lean_object* v_inst_2910_, lean_object* v_00_u03b2_2911_, lean_object* v_lctx_2912_, lean_object* v_init_2913_, lean_object* v_f_2914_){
_start:
{
lean_object* v_res_2915_; 
v_res_2915_ = l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1(v_toPure_2909_, v_inst_2910_, v_00_u03b2_2911_, v_lctx_2912_, v_init_2913_, v_f_2914_);
lean_dec_ref(v_lctx_2912_);
return v_res_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg(lean_object* v_inst_2916_){
_start:
{
lean_object* v_toApplicative_2917_; lean_object* v_toPure_2918_; lean_object* v___f_2919_; 
v_toApplicative_2917_ = lean_ctor_get(v_inst_2916_, 0);
v_toPure_2918_ = lean_ctor_get(v_toApplicative_2917_, 1);
lean_inc(v_toPure_2918_);
v___f_2919_ = lean_alloc_closure((void*)(l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1___boxed), 6, 2);
lean_closure_set(v___f_2919_, 0, v_toPure_2918_);
lean_closure_set(v___f_2919_, 1, v_inst_2916_);
return v___f_2919_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad(lean_object* v_m_2920_, lean_object* v_inst_2921_){
_start:
{
lean_object* v___x_2922_; 
v___x_2922_ = l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg(v_inst_2921_);
return v___x_2922_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg___lam__0(lean_object* v_f_2923_, lean_object* v_x1_2924_, lean_object* v_x2_2925_){
_start:
{
lean_object* v___x_2926_; 
v___x_2926_ = lean_apply_2(v_f_2923_, v_x1_2924_, v_x2_2925_);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg(lean_object* v_lctx_2946_, lean_object* v_f_2947_, lean_object* v_init_2948_, lean_object* v_start_2949_){
_start:
{
lean_object* v___f_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; 
v___f_2950_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2950_, 0, v_f_2947_);
v___x_2951_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_2952_ = l_Lean_LocalContext_foldlM___redArg(v___x_2951_, v_lctx_2946_, v___f_2950_, v_init_2948_, v_start_2949_);
return v___x_2952_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg___boxed(lean_object* v_lctx_2953_, lean_object* v_f_2954_, lean_object* v_init_2955_, lean_object* v_start_2956_){
_start:
{
lean_object* v_res_2957_; 
v_res_2957_ = l_Lean_LocalContext_foldl___redArg(v_lctx_2953_, v_f_2954_, v_init_2955_, v_start_2956_);
lean_dec(v_start_2956_);
return v_res_2957_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl(lean_object* v_00_u03b2_2958_, lean_object* v_lctx_2959_, lean_object* v_f_2960_, lean_object* v_init_2961_, lean_object* v_start_2962_){
_start:
{
lean_object* v___f_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
v___f_2963_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2963_, 0, v_f_2960_);
v___x_2964_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_2965_ = l_Lean_LocalContext_foldlM___redArg(v___x_2964_, v_lctx_2959_, v___f_2963_, v_init_2961_, v_start_2962_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___boxed(lean_object* v_00_u03b2_2966_, lean_object* v_lctx_2967_, lean_object* v_f_2968_, lean_object* v_init_2969_, lean_object* v_start_2970_){
_start:
{
lean_object* v_res_2971_; 
v_res_2971_ = l_Lean_LocalContext_foldl(v_00_u03b2_2966_, v_lctx_2967_, v_f_2968_, v_init_2969_, v_start_2970_);
lean_dec(v_start_2970_);
return v_res_2971_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr___redArg___lam__0(lean_object* v_f_2972_, lean_object* v_x1_2973_, lean_object* v_x2_2974_){
_start:
{
lean_object* v___x_2975_; 
v___x_2975_ = lean_apply_2(v_f_2972_, v_x1_2973_, v_x2_2974_);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr___redArg(lean_object* v_lctx_2976_, lean_object* v_f_2977_, lean_object* v_init_2978_){
_start:
{
lean_object* v___f_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v___f_2979_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2979_, 0, v_f_2977_);
v___x_2980_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_2981_ = l_Lean_LocalContext_foldrM___redArg(v___x_2980_, v_lctx_2976_, v___f_2979_, v_init_2978_);
return v___x_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr(lean_object* v_00_u03b2_2982_, lean_object* v_lctx_2983_, lean_object* v_f_2984_, lean_object* v_init_2985_){
_start:
{
lean_object* v___f_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___f_2986_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2986_, 0, v_f_2984_);
v___x_2987_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_2988_ = l_Lean_LocalContext_foldrM___redArg(v___x_2987_, v_lctx_2983_, v___f_2986_, v_init_2985_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(lean_object* v_as_2989_, size_t v_i_2990_, size_t v_stop_2991_, lean_object* v_b_2992_){
_start:
{
lean_object* v___y_2994_; uint8_t v___x_2998_; 
v___x_2998_ = lean_usize_dec_eq(v_i_2990_, v_stop_2991_);
if (v___x_2998_ == 0)
{
lean_object* v___x_2999_; 
v___x_2999_ = lean_array_uget_borrowed(v_as_2989_, v_i_2990_);
if (lean_obj_tag(v___x_2999_) == 0)
{
v___y_2994_ = v_b_2992_;
goto v___jp_2993_;
}
else
{
lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_3000_ = lean_unsigned_to_nat(1u);
v___x_3001_ = lean_nat_add(v_b_2992_, v___x_3000_);
lean_dec(v_b_2992_);
v___y_2994_ = v___x_3001_;
goto v___jp_2993_;
}
}
else
{
return v_b_2992_;
}
v___jp_2993_:
{
size_t v___x_2995_; size_t v___x_2996_; 
v___x_2995_ = ((size_t)1ULL);
v___x_2996_ = lean_usize_add(v_i_2990_, v___x_2995_);
v_i_2990_ = v___x_2996_;
v_b_2992_ = v___y_2994_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3002_, lean_object* v_i_3003_, lean_object* v_stop_3004_, lean_object* v_b_3005_){
_start:
{
size_t v_i_boxed_3006_; size_t v_stop_boxed_3007_; lean_object* v_res_3008_; 
v_i_boxed_3006_ = lean_unbox_usize(v_i_3003_);
lean_dec(v_i_3003_);
v_stop_boxed_3007_ = lean_unbox_usize(v_stop_3004_);
lean_dec(v_stop_3004_);
v_res_3008_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_as_3002_, v_i_boxed_3006_, v_stop_boxed_3007_, v_b_3005_);
lean_dec_ref(v_as_3002_);
return v_res_3008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(lean_object* v_x_3009_, lean_object* v_x_3010_){
_start:
{
if (lean_obj_tag(v_x_3009_) == 0)
{
lean_object* v_cs_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; uint8_t v___x_3014_; 
v_cs_3011_ = lean_ctor_get(v_x_3009_, 0);
v___x_3012_ = lean_unsigned_to_nat(0u);
v___x_3013_ = lean_array_get_size(v_cs_3011_);
v___x_3014_ = lean_nat_dec_lt(v___x_3012_, v___x_3013_);
if (v___x_3014_ == 0)
{
return v_x_3010_;
}
else
{
size_t v___x_3015_; size_t v___x_3016_; lean_object* v___x_3017_; 
v___x_3015_ = ((size_t)0ULL);
v___x_3016_ = lean_usize_of_nat(v___x_3013_);
v___x_3017_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_cs_3011_, v___x_3015_, v___x_3016_, v_x_3010_);
return v___x_3017_;
}
}
else
{
lean_object* v_vs_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; uint8_t v___x_3021_; 
v_vs_3018_ = lean_ctor_get(v_x_3009_, 0);
v___x_3019_ = lean_unsigned_to_nat(0u);
v___x_3020_ = lean_array_get_size(v_vs_3018_);
v___x_3021_ = lean_nat_dec_lt(v___x_3019_, v___x_3020_);
if (v___x_3021_ == 0)
{
return v_x_3010_;
}
else
{
size_t v___x_3022_; size_t v___x_3023_; lean_object* v___x_3024_; 
v___x_3022_ = ((size_t)0ULL);
v___x_3023_ = lean_usize_of_nat(v___x_3020_);
v___x_3024_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_vs_3018_, v___x_3022_, v___x_3023_, v_x_3010_);
return v___x_3024_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(lean_object* v_as_3025_, size_t v_i_3026_, size_t v_stop_3027_, lean_object* v_b_3028_){
_start:
{
uint8_t v___x_3029_; 
v___x_3029_ = lean_usize_dec_eq(v_i_3026_, v_stop_3027_);
if (v___x_3029_ == 0)
{
lean_object* v___x_3030_; lean_object* v___x_3031_; size_t v___x_3032_; size_t v___x_3033_; 
v___x_3030_ = lean_array_uget_borrowed(v_as_3025_, v_i_3026_);
v___x_3031_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(v___x_3030_, v_b_3028_);
v___x_3032_ = ((size_t)1ULL);
v___x_3033_ = lean_usize_add(v_i_3026_, v___x_3032_);
v_i_3026_ = v___x_3033_;
v_b_3028_ = v___x_3031_;
goto _start;
}
else
{
return v_b_3028_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_as_3035_, lean_object* v_i_3036_, lean_object* v_stop_3037_, lean_object* v_b_3038_){
_start:
{
size_t v_i_boxed_3039_; size_t v_stop_boxed_3040_; lean_object* v_res_3041_; 
v_i_boxed_3039_ = lean_unbox_usize(v_i_3036_);
lean_dec(v_i_3036_);
v_stop_boxed_3040_ = lean_unbox_usize(v_stop_3037_);
lean_dec(v_stop_3037_);
v_res_3041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_as_3035_, v_i_boxed_3039_, v_stop_boxed_3040_, v_b_3038_);
lean_dec_ref(v_as_3035_);
return v_res_3041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3___boxed(lean_object* v_x_3042_, lean_object* v_x_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(v_x_3042_, v_x_3043_);
lean_dec_ref(v_x_3042_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(lean_object* v_x_3045_, size_t v_x_3046_, size_t v_x_3047_, lean_object* v_x_3048_){
_start:
{
if (lean_obj_tag(v_x_3045_) == 0)
{
lean_object* v_cs_3049_; lean_object* v___x_3050_; size_t v___x_3051_; lean_object* v_j_3052_; lean_object* v___x_3053_; size_t v___x_3054_; size_t v___x_3055_; size_t v___x_3056_; size_t v___x_3057_; size_t v___x_3058_; size_t v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; uint8_t v___x_3064_; 
v_cs_3049_ = lean_ctor_get(v_x_3045_, 0);
v___x_3050_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0);
v___x_3051_ = lean_usize_shift_right(v_x_3046_, v_x_3047_);
v_j_3052_ = lean_usize_to_nat(v___x_3051_);
v___x_3053_ = lean_array_get_borrowed(v___x_3050_, v_cs_3049_, v_j_3052_);
v___x_3054_ = ((size_t)1ULL);
v___x_3055_ = lean_usize_shift_left(v___x_3054_, v_x_3047_);
v___x_3056_ = lean_usize_sub(v___x_3055_, v___x_3054_);
v___x_3057_ = lean_usize_land(v_x_3046_, v___x_3056_);
v___x_3058_ = ((size_t)5ULL);
v___x_3059_ = lean_usize_sub(v_x_3047_, v___x_3058_);
v___x_3060_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(v___x_3053_, v___x_3057_, v___x_3059_, v_x_3048_);
v___x_3061_ = lean_unsigned_to_nat(1u);
v___x_3062_ = lean_nat_add(v_j_3052_, v___x_3061_);
lean_dec(v_j_3052_);
v___x_3063_ = lean_array_get_size(v_cs_3049_);
v___x_3064_ = lean_nat_dec_lt(v___x_3062_, v___x_3063_);
if (v___x_3064_ == 0)
{
lean_dec(v___x_3062_);
return v___x_3060_;
}
else
{
size_t v___x_3065_; size_t v___x_3066_; lean_object* v___x_3067_; 
v___x_3065_ = lean_usize_of_nat(v___x_3062_);
lean_dec(v___x_3062_);
v___x_3066_ = lean_usize_of_nat(v___x_3063_);
v___x_3067_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_cs_3049_, v___x_3065_, v___x_3066_, v___x_3060_);
return v___x_3067_;
}
}
else
{
lean_object* v_vs_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; uint8_t v___x_3071_; 
v_vs_3068_ = lean_ctor_get(v_x_3045_, 0);
v___x_3069_ = lean_usize_to_nat(v_x_3046_);
v___x_3070_ = lean_array_get_size(v_vs_3068_);
v___x_3071_ = lean_nat_dec_lt(v___x_3069_, v___x_3070_);
if (v___x_3071_ == 0)
{
lean_dec(v___x_3069_);
return v_x_3048_;
}
else
{
size_t v___x_3072_; size_t v___x_3073_; lean_object* v___x_3074_; 
v___x_3072_ = lean_usize_of_nat(v___x_3069_);
lean_dec(v___x_3069_);
v___x_3073_ = lean_usize_of_nat(v___x_3070_);
v___x_3074_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_vs_3068_, v___x_3072_, v___x_3073_, v_x_3048_);
return v___x_3074_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3075_, lean_object* v_x_3076_, lean_object* v_x_3077_, lean_object* v_x_3078_){
_start:
{
size_t v_x_1185__boxed_3079_; size_t v_x_1186__boxed_3080_; lean_object* v_res_3081_; 
v_x_1185__boxed_3079_ = lean_unbox_usize(v_x_3076_);
lean_dec(v_x_3076_);
v_x_1186__boxed_3080_ = lean_unbox_usize(v_x_3077_);
lean_dec(v_x_3077_);
v_res_3081_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(v_x_3075_, v_x_1185__boxed_3079_, v_x_1186__boxed_3080_, v_x_3078_);
lean_dec_ref(v_x_3075_);
return v_res_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(lean_object* v_t_3082_, lean_object* v_init_3083_, lean_object* v_start_3084_){
_start:
{
lean_object* v___x_3085_; uint8_t v___x_3086_; 
v___x_3085_ = lean_unsigned_to_nat(0u);
v___x_3086_ = lean_nat_dec_eq(v_start_3084_, v___x_3085_);
if (v___x_3086_ == 0)
{
lean_object* v_root_3087_; lean_object* v_tail_3088_; size_t v_shift_3089_; lean_object* v_tailOff_3090_; uint8_t v___x_3091_; 
v_root_3087_ = lean_ctor_get(v_t_3082_, 0);
v_tail_3088_ = lean_ctor_get(v_t_3082_, 1);
v_shift_3089_ = lean_ctor_get_usize(v_t_3082_, 4);
v_tailOff_3090_ = lean_ctor_get(v_t_3082_, 3);
v___x_3091_ = lean_nat_dec_le(v_tailOff_3090_, v_start_3084_);
if (v___x_3091_ == 0)
{
size_t v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; uint8_t v___x_3095_; 
v___x_3092_ = lean_usize_of_nat(v_start_3084_);
v___x_3093_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(v_root_3087_, v___x_3092_, v_shift_3089_, v_init_3083_);
v___x_3094_ = lean_array_get_size(v_tail_3088_);
v___x_3095_ = lean_nat_dec_lt(v___x_3085_, v___x_3094_);
if (v___x_3095_ == 0)
{
return v___x_3093_;
}
else
{
size_t v___x_3096_; size_t v___x_3097_; lean_object* v___x_3098_; 
v___x_3096_ = ((size_t)0ULL);
v___x_3097_ = lean_usize_of_nat(v___x_3094_);
v___x_3098_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3088_, v___x_3096_, v___x_3097_, v___x_3093_);
return v___x_3098_;
}
}
else
{
lean_object* v___x_3099_; lean_object* v___x_3100_; uint8_t v___x_3101_; 
v___x_3099_ = lean_nat_sub(v_start_3084_, v_tailOff_3090_);
v___x_3100_ = lean_array_get_size(v_tail_3088_);
v___x_3101_ = lean_nat_dec_lt(v___x_3099_, v___x_3100_);
if (v___x_3101_ == 0)
{
lean_dec(v___x_3099_);
return v_init_3083_;
}
else
{
size_t v___x_3102_; size_t v___x_3103_; lean_object* v___x_3104_; 
v___x_3102_ = lean_usize_of_nat(v___x_3099_);
lean_dec(v___x_3099_);
v___x_3103_ = lean_usize_of_nat(v___x_3100_);
v___x_3104_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3088_, v___x_3102_, v___x_3103_, v_init_3083_);
return v___x_3104_;
}
}
}
else
{
lean_object* v_root_3105_; lean_object* v_tail_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; uint8_t v___x_3109_; 
v_root_3105_ = lean_ctor_get(v_t_3082_, 0);
v_tail_3106_ = lean_ctor_get(v_t_3082_, 1);
v___x_3107_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(v_root_3105_, v_init_3083_);
v___x_3108_ = lean_array_get_size(v_tail_3106_);
v___x_3109_ = lean_nat_dec_lt(v___x_3085_, v___x_3108_);
if (v___x_3109_ == 0)
{
return v___x_3107_;
}
else
{
size_t v___x_3110_; size_t v___x_3111_; lean_object* v___x_3112_; 
v___x_3110_ = ((size_t)0ULL);
v___x_3111_ = lean_usize_of_nat(v___x_3108_);
v___x_3112_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3106_, v___x_3110_, v___x_3111_, v___x_3107_);
return v___x_3112_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0___boxed(lean_object* v_t_3113_, lean_object* v_init_3114_, lean_object* v_start_3115_){
_start:
{
lean_object* v_res_3116_; 
v_res_3116_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(v_t_3113_, v_init_3114_, v_start_3115_);
lean_dec(v_start_3115_);
lean_dec_ref(v_t_3113_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(lean_object* v_lctx_3117_, lean_object* v_init_3118_, lean_object* v_start_3119_){
_start:
{
lean_object* v_decls_3120_; lean_object* v___x_3121_; 
v_decls_3120_ = lean_ctor_get(v_lctx_3117_, 1);
v___x_3121_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(v_decls_3120_, v_init_3118_, v_start_3119_);
return v___x_3121_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0___boxed(lean_object* v_lctx_3122_, lean_object* v_init_3123_, lean_object* v_start_3124_){
_start:
{
lean_object* v_res_3125_; 
v_res_3125_ = l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(v_lctx_3122_, v_init_3123_, v_start_3124_);
lean_dec(v_start_3124_);
lean_dec_ref(v_lctx_3122_);
return v_res_3125_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_size(lean_object* v_lctx_3126_){
_start:
{
lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___x_3127_ = lean_unsigned_to_nat(0u);
v___x_3128_ = l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(v_lctx_3126_, v___x_3127_, v___x_3127_);
return v___x_3128_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_size___boxed(lean_object* v_lctx_3129_){
_start:
{
lean_object* v_res_3130_; 
v_res_3130_ = l_Lean_LocalContext_size(v_lctx_3129_);
lean_dec_ref(v_lctx_3129_);
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f___redArg___lam__0(lean_object* v_f_3131_, lean_object* v_x_3132_){
_start:
{
lean_object* v___x_3133_; 
v___x_3133_ = lean_apply_1(v_f_3131_, v_x_3132_);
return v___x_3133_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f___redArg(lean_object* v_lctx_3134_, lean_object* v_f_3135_){
_start:
{
lean_object* v___f_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___f_3136_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3136_, 0, v_f_3135_);
v___x_3137_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3138_ = l_Lean_LocalContext_findDeclM_x3f___redArg(v___x_3137_, v_lctx_3134_, v___f_3136_);
return v___x_3138_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f(lean_object* v_00_u03b2_3139_, lean_object* v_lctx_3140_, lean_object* v_f_3141_){
_start:
{
lean_object* v___f_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___f_3142_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3142_, 0, v_f_3141_);
v___x_3143_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3144_ = l_Lean_LocalContext_findDeclM_x3f___redArg(v___x_3143_, v_lctx_3140_, v___f_3142_);
return v___x_3144_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRev_x3f___redArg(lean_object* v_lctx_3145_, lean_object* v_f_3146_){
_start:
{
lean_object* v___f_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; 
v___f_3147_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3147_, 0, v_f_3146_);
v___x_3148_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3149_ = l_Lean_LocalContext_findDeclRevM_x3f___redArg(v___x_3148_, v_lctx_3145_, v___f_3147_);
return v___x_3149_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRev_x3f(lean_object* v_00_u03b2_3150_, lean_object* v_lctx_3151_, lean_object* v_f_3152_){
_start:
{
lean_object* v___f_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; 
v___f_3153_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3153_, 0, v_f_3152_);
v___x_3154_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3155_ = l_Lean_LocalContext_findDeclRevM_x3f___redArg(v___x_3154_, v_lctx_3151_, v___f_3153_);
return v___x_3155_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(lean_object* v_val_3156_, lean_object* v_as_3157_, size_t v_i_3158_, size_t v_stop_3159_){
_start:
{
uint8_t v___x_3160_; 
v___x_3160_ = lean_usize_dec_eq(v_i_3158_, v_stop_3159_);
if (v___x_3160_ == 0)
{
uint8_t v___x_3161_; uint8_t v___y_3163_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v_fvarId_3169_; uint8_t v___x_3170_; 
v___x_3161_ = 1;
v___x_3167_ = lean_array_uget_borrowed(v_as_3157_, v_i_3158_);
v___x_3168_ = l_Lean_Expr_fvarId_x21(v___x_3167_);
v_fvarId_3169_ = lean_ctor_get(v_val_3156_, 1);
v___x_3170_ = l_Lean_instBEqFVarId_beq(v___x_3168_, v_fvarId_3169_);
lean_dec(v___x_3168_);
v___y_3163_ = v___x_3170_;
goto v___jp_3162_;
v___jp_3162_:
{
if (v___y_3163_ == 0)
{
size_t v___x_3164_; size_t v___x_3165_; 
v___x_3164_ = ((size_t)1ULL);
v___x_3165_ = lean_usize_add(v_i_3158_, v___x_3164_);
v_i_3158_ = v___x_3165_;
goto _start;
}
else
{
return v___x_3161_;
}
}
}
else
{
uint8_t v___x_3171_; 
v___x_3171_ = 0;
return v___x_3171_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0___boxed(lean_object* v_val_3172_, lean_object* v_as_3173_, lean_object* v_i_3174_, lean_object* v_stop_3175_){
_start:
{
size_t v_i_boxed_3176_; size_t v_stop_boxed_3177_; uint8_t v_res_3178_; lean_object* v_r_3179_; 
v_i_boxed_3176_ = lean_unbox_usize(v_i_3174_);
lean_dec(v_i_3174_);
v_stop_boxed_3177_ = lean_unbox_usize(v_stop_3175_);
lean_dec(v_stop_3175_);
v_res_3178_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(v_val_3172_, v_as_3173_, v_i_boxed_3176_, v_stop_boxed_3177_);
lean_dec_ref(v_as_3173_);
lean_dec_ref(v_val_3172_);
v_r_3179_ = lean_box(v_res_3178_);
return v_r_3179_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_isSubPrefixOfAux(lean_object* v_a_u2081_3180_, lean_object* v_a_u2082_3181_, lean_object* v_exceptFVars_3182_, lean_object* v_i_3183_, lean_object* v_j_3184_){
_start:
{
lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v_size_3200_; uint8_t v___x_3201_; 
v_size_3200_ = lean_ctor_get(v_a_u2081_3180_, 2);
v___x_3201_ = lean_nat_dec_lt(v_i_3183_, v_size_3200_);
if (v___x_3201_ == 0)
{
uint8_t v___x_3202_; 
lean_dec(v_j_3184_);
lean_dec(v_i_3183_);
v___x_3202_ = 1;
return v___x_3202_;
}
else
{
lean_object* v___x_3203_; lean_object* v___x_3204_; 
v___x_3203_ = lean_box(0);
v___x_3204_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3203_, v_a_u2081_3180_, v_i_3183_);
if (lean_obj_tag(v___x_3204_) == 0)
{
lean_object* v___x_3205_; lean_object* v___x_3206_; 
v___x_3205_ = lean_unsigned_to_nat(1u);
v___x_3206_ = lean_nat_add(v_i_3183_, v___x_3205_);
lean_dec(v_i_3183_);
v_i_3183_ = v___x_3206_;
goto _start;
}
else
{
lean_object* v_val_3208_; lean_object* v___x_3218_; lean_object* v___x_3219_; uint8_t v___x_3220_; 
v_val_3208_ = lean_ctor_get(v___x_3204_, 0);
lean_inc(v_val_3208_);
lean_dec_ref_known(v___x_3204_, 1);
v___x_3218_ = lean_unsigned_to_nat(0u);
v___x_3219_ = lean_array_get_size(v_exceptFVars_3182_);
v___x_3220_ = lean_nat_dec_lt(v___x_3218_, v___x_3219_);
if (v___x_3220_ == 0)
{
goto v___jp_3209_;
}
else
{
if (v___x_3220_ == 0)
{
goto v___jp_3209_;
}
else
{
size_t v___x_3221_; size_t v___x_3222_; uint8_t v___x_3223_; 
v___x_3221_ = ((size_t)0ULL);
v___x_3222_ = lean_usize_of_nat(v___x_3219_);
v___x_3223_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(v_val_3208_, v_exceptFVars_3182_, v___x_3221_, v___x_3222_);
if (v___x_3223_ == 0)
{
goto v___jp_3209_;
}
else
{
lean_object* v___x_3224_; lean_object* v___x_3225_; 
lean_dec(v_val_3208_);
v___x_3224_ = lean_unsigned_to_nat(1u);
v___x_3225_ = lean_nat_add(v_i_3183_, v___x_3224_);
lean_dec(v_i_3183_);
v_i_3183_ = v___x_3225_;
goto _start;
}
}
}
v___jp_3209_:
{
lean_object* v_size_3210_; uint8_t v___x_3211_; 
v_size_3210_ = lean_ctor_get(v_a_u2082_3181_, 2);
v___x_3211_ = lean_nat_dec_lt(v_j_3184_, v_size_3210_);
if (v___x_3211_ == 0)
{
lean_dec(v_val_3208_);
lean_dec(v_j_3184_);
lean_dec(v_i_3183_);
return v___x_3211_;
}
else
{
lean_object* v___x_3212_; 
v___x_3212_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3203_, v_a_u2082_3181_, v_j_3184_);
if (lean_obj_tag(v___x_3212_) == 0)
{
lean_object* v___x_3213_; lean_object* v___x_3214_; 
lean_dec(v_val_3208_);
v___x_3213_ = lean_unsigned_to_nat(1u);
v___x_3214_ = lean_nat_add(v_j_3184_, v___x_3213_);
lean_dec(v_j_3184_);
v_j_3184_ = v___x_3214_;
goto _start;
}
else
{
lean_object* v_val_3216_; lean_object* v_fvarId_3217_; 
v_val_3216_ = lean_ctor_get(v___x_3212_, 0);
lean_inc(v_val_3216_);
lean_dec_ref_known(v___x_3212_, 1);
v_fvarId_3217_ = lean_ctor_get(v_val_3208_, 1);
lean_inc(v_fvarId_3217_);
lean_dec(v_val_3208_);
v___y_3197_ = v_val_3216_;
v___y_3198_ = v_fvarId_3217_;
goto v___jp_3196_;
}
}
}
}
}
v___jp_3185_:
{
uint8_t v___x_3188_; 
v___x_3188_ = l_Lean_instBEqFVarId_beq(v___y_3186_, v___y_3187_);
lean_dec(v___y_3187_);
lean_dec(v___y_3186_);
if (v___x_3188_ == 0)
{
lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3189_ = lean_unsigned_to_nat(1u);
v___x_3190_ = lean_nat_add(v_j_3184_, v___x_3189_);
lean_dec(v_j_3184_);
v_j_3184_ = v___x_3190_;
goto _start;
}
else
{
lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3192_ = lean_unsigned_to_nat(1u);
v___x_3193_ = lean_nat_add(v_i_3183_, v___x_3192_);
lean_dec(v_i_3183_);
v___x_3194_ = lean_nat_add(v_j_3184_, v___x_3192_);
lean_dec(v_j_3184_);
v_i_3183_ = v___x_3193_;
v_j_3184_ = v___x_3194_;
goto _start;
}
}
v___jp_3196_:
{
lean_object* v_fvarId_3199_; 
v_fvarId_3199_ = lean_ctor_get(v___y_3197_, 1);
lean_inc(v_fvarId_3199_);
lean_dec_ref(v___y_3197_);
v___y_3186_ = v___y_3198_;
v___y_3187_ = v_fvarId_3199_;
goto v___jp_3185_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_isSubPrefixOfAux___boxed(lean_object* v_a_u2081_3227_, lean_object* v_a_u2082_3228_, lean_object* v_exceptFVars_3229_, lean_object* v_i_3230_, lean_object* v_j_3231_){
_start:
{
uint8_t v_res_3232_; lean_object* v_r_3233_; 
v_res_3232_ = l_Lean_LocalContext_isSubPrefixOfAux(v_a_u2081_3227_, v_a_u2082_3228_, v_exceptFVars_3229_, v_i_3230_, v_j_3231_);
lean_dec_ref(v_exceptFVars_3229_);
lean_dec_ref(v_a_u2082_3228_);
lean_dec_ref(v_a_u2081_3227_);
v_r_3233_ = lean_box(v_res_3232_);
return v_r_3233_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_isSubPrefixOf(lean_object* v_lctx_u2081_3234_, lean_object* v_lctx_u2082_3235_, lean_object* v_exceptFVars_3236_){
_start:
{
lean_object* v_decls_3237_; lean_object* v_decls_3238_; lean_object* v___x_3239_; uint8_t v___x_3240_; 
v_decls_3237_ = lean_ctor_get(v_lctx_u2081_3234_, 1);
v_decls_3238_ = lean_ctor_get(v_lctx_u2082_3235_, 1);
v___x_3239_ = lean_unsigned_to_nat(0u);
v___x_3240_ = l_Lean_LocalContext_isSubPrefixOfAux(v_decls_3237_, v_decls_3238_, v_exceptFVars_3236_, v___x_3239_, v___x_3239_);
return v___x_3240_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_isSubPrefixOf___boxed(lean_object* v_lctx_u2081_3241_, lean_object* v_lctx_u2082_3242_, lean_object* v_exceptFVars_3243_){
_start:
{
uint8_t v_res_3244_; lean_object* v_r_3245_; 
v_res_3244_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_u2081_3241_, v_lctx_u2082_3242_, v_exceptFVars_3243_);
lean_dec_ref(v_exceptFVars_3243_);
lean_dec_ref(v_lctx_u2082_3242_);
lean_dec_ref(v_lctx_u2081_3241_);
v_r_3245_ = lean_box(v_res_3244_);
return v_r_3245_;
}
}
static lean_object* _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; 
v___x_3247_ = ((lean_object*)(l_Lean_LocalContext_get_x21___closed__1));
v___x_3248_ = lean_unsigned_to_nat(14u);
v___x_3249_ = lean_unsigned_to_nat(585u);
v___x_3250_ = ((lean_object*)(l_Lean_LocalContext_mkBinding___lam__0___closed__0));
v___x_3251_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_3252_ = l_mkPanicMessageWithDecl(v___x_3251_, v___x_3250_, v___x_3249_, v___x_3248_, v___x_3247_);
return v___x_3252_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___lam__0(lean_object* v_xs_3253_, lean_object* v_lctx_3254_, lean_object* v___x_3255_, uint8_t v_isLambda_3256_, uint8_t v_usedLetOnly_3257_, uint8_t v_generalizeNondepLet_3258_, lean_object* v_i_3259_, lean_object* v_x_3260_, lean_object* v_b_3261_){
_start:
{
lean_object* v_n_3263_; lean_object* v_ty_3264_; uint8_t v_bi_3265_; lean_object* v_x_3269_; lean_object* v___x_3270_; 
v_x_3269_ = lean_array_fget_borrowed(v_xs_3253_, v_i_3259_);
v___x_3270_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3254_, v_x_3269_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v___x_3271_; lean_object* v___x_3272_; 
lean_dec_ref(v_b_3261_);
v___x_3271_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3272_ = l_panic___redArg(v___x_3255_, v___x_3271_);
return v___x_3272_;
}
else
{
lean_object* v_val_3273_; 
v_val_3273_ = lean_ctor_get(v___x_3270_, 0);
lean_inc(v_val_3273_);
lean_dec_ref_known(v___x_3270_, 1);
if (lean_obj_tag(v_val_3273_) == 0)
{
lean_object* v_userName_3274_; lean_object* v_type_3275_; uint8_t v_bi_3276_; 
v_userName_3274_ = lean_ctor_get(v_val_3273_, 2);
lean_inc(v_userName_3274_);
v_type_3275_ = lean_ctor_get(v_val_3273_, 3);
lean_inc_ref(v_type_3275_);
v_bi_3276_ = lean_ctor_get_uint8(v_val_3273_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3273_, 4);
v_n_3263_ = v_userName_3274_;
v_ty_3264_ = v_type_3275_;
v_bi_3265_ = v_bi_3276_;
goto v___jp_3262_;
}
else
{
lean_object* v_userName_3277_; lean_object* v_type_3278_; lean_object* v_value_3279_; uint8_t v_nondep_3280_; uint8_t v___y_3286_; 
v_userName_3277_ = lean_ctor_get(v_val_3273_, 2);
lean_inc(v_userName_3277_);
v_type_3278_ = lean_ctor_get(v_val_3273_, 3);
lean_inc_ref(v_type_3278_);
v_value_3279_ = lean_ctor_get(v_val_3273_, 4);
lean_inc_ref(v_value_3279_);
v_nondep_3280_ = lean_ctor_get_uint8(v_val_3273_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3273_, 5);
if (v_nondep_3280_ == 0)
{
v___y_3286_ = v_nondep_3280_;
goto v___jp_3285_;
}
else
{
if (v_generalizeNondepLet_3258_ == 0)
{
v___y_3286_ = v_generalizeNondepLet_3258_;
goto v___jp_3285_;
}
else
{
uint8_t v___x_3291_; 
lean_dec_ref(v_value_3279_);
v___x_3291_ = 0;
v_n_3263_ = v_userName_3277_;
v_ty_3264_ = v_type_3278_;
v_bi_3265_ = v___x_3291_;
goto v___jp_3262_;
}
}
v___jp_3281_:
{
lean_object* v_ty_3282_; lean_object* v_val_3283_; lean_object* v___x_3284_; 
v_ty_3282_ = lean_expr_abstract_range(v_type_3278_, v_i_3259_, v_xs_3253_);
lean_dec_ref(v_type_3278_);
v_val_3283_ = lean_expr_abstract_range(v_value_3279_, v_i_3259_, v_xs_3253_);
lean_dec_ref(v_value_3279_);
v___x_3284_ = l_Lean_Expr_letE___override(v_userName_3277_, v_ty_3282_, v_val_3283_, v_b_3261_, v_nondep_3280_);
return v___x_3284_;
}
v___jp_3285_:
{
if (v_usedLetOnly_3257_ == 0)
{
goto v___jp_3281_;
}
else
{
if (v___y_3286_ == 0)
{
lean_object* v___x_3287_; uint8_t v___x_3288_; 
v___x_3287_ = lean_unsigned_to_nat(0u);
v___x_3288_ = lean_expr_has_loose_bvar(v_b_3261_, v___x_3287_);
if (v___x_3288_ == 0)
{
lean_object* v___x_3289_; lean_object* v___x_3290_; 
lean_dec_ref(v_value_3279_);
lean_dec_ref(v_type_3278_);
lean_dec(v_userName_3277_);
v___x_3289_ = lean_unsigned_to_nat(1u);
v___x_3290_ = lean_expr_lower_loose_bvars(v_b_3261_, v___x_3289_, v___x_3289_);
lean_dec_ref(v_b_3261_);
return v___x_3290_;
}
else
{
goto v___jp_3281_;
}
}
else
{
goto v___jp_3281_;
}
}
}
}
}
v___jp_3262_:
{
lean_object* v_ty_3266_; 
v_ty_3266_ = lean_expr_abstract_range(v_ty_3264_, v_i_3259_, v_xs_3253_);
lean_dec_ref(v_ty_3264_);
if (v_isLambda_3256_ == 0)
{
lean_object* v___x_3267_; 
v___x_3267_ = l_Lean_mkForall(v_n_3263_, v_bi_3265_, v_ty_3266_, v_b_3261_);
return v___x_3267_;
}
else
{
lean_object* v___x_3268_; 
v___x_3268_ = l_Lean_mkLambda(v_n_3263_, v_bi_3265_, v_ty_3266_, v_b_3261_);
return v___x_3268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___lam__0___boxed(lean_object* v_xs_3292_, lean_object* v_lctx_3293_, lean_object* v___x_3294_, lean_object* v_isLambda_3295_, lean_object* v_usedLetOnly_3296_, lean_object* v_generalizeNondepLet_3297_, lean_object* v_i_3298_, lean_object* v_x_3299_, lean_object* v_b_3300_){
_start:
{
uint8_t v_isLambda_boxed_3301_; uint8_t v_usedLetOnly_boxed_3302_; uint8_t v_generalizeNondepLet_boxed_3303_; lean_object* v_res_3304_; 
v_isLambda_boxed_3301_ = lean_unbox(v_isLambda_3295_);
v_usedLetOnly_boxed_3302_ = lean_unbox(v_usedLetOnly_3296_);
v_generalizeNondepLet_boxed_3303_ = lean_unbox(v_generalizeNondepLet_3297_);
v_res_3304_ = l_Lean_LocalContext_mkBinding___lam__0(v_xs_3292_, v_lctx_3293_, v___x_3294_, v_isLambda_boxed_3301_, v_usedLetOnly_boxed_3302_, v_generalizeNondepLet_boxed_3303_, v_i_3298_, v_x_3299_, v_b_3300_);
lean_dec(v_i_3298_);
lean_dec_ref(v___x_3294_);
lean_dec_ref(v_xs_3292_);
return v_res_3304_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding(uint8_t v_isLambda_3305_, lean_object* v_lctx_3306_, lean_object* v_xs_3307_, lean_object* v_b_3308_, uint8_t v_usedLetOnly_3309_, uint8_t v_generalizeNondepLet_3310_){
_start:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___f_3315_; lean_object* v_b_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; 
v___x_3311_ = l_Lean_instInhabitedExpr;
v___x_3312_ = lean_box(v_isLambda_3305_);
v___x_3313_ = lean_box(v_usedLetOnly_3309_);
v___x_3314_ = lean_box(v_generalizeNondepLet_3310_);
lean_inc_ref(v_xs_3307_);
v___f_3315_ = lean_alloc_closure((void*)(l_Lean_LocalContext_mkBinding___lam__0___boxed), 9, 6);
lean_closure_set(v___f_3315_, 0, v_xs_3307_);
lean_closure_set(v___f_3315_, 1, v_lctx_3306_);
lean_closure_set(v___f_3315_, 2, v___x_3311_);
lean_closure_set(v___f_3315_, 3, v___x_3312_);
lean_closure_set(v___f_3315_, 4, v___x_3313_);
lean_closure_set(v___f_3315_, 5, v___x_3314_);
v_b_3316_ = lean_expr_abstract(v_b_3308_, v_xs_3307_);
v___x_3317_ = lean_array_get_size(v_xs_3307_);
lean_dec_ref(v_xs_3307_);
v___x_3318_ = l_Nat_foldRev___redArg(v___x_3317_, v___f_3315_, v_b_3316_);
return v___x_3318_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___boxed(lean_object* v_isLambda_3319_, lean_object* v_lctx_3320_, lean_object* v_xs_3321_, lean_object* v_b_3322_, lean_object* v_usedLetOnly_3323_, lean_object* v_generalizeNondepLet_3324_){
_start:
{
uint8_t v_isLambda_boxed_3325_; uint8_t v_usedLetOnly_boxed_3326_; uint8_t v_generalizeNondepLet_boxed_3327_; lean_object* v_res_3328_; 
v_isLambda_boxed_3325_ = lean_unbox(v_isLambda_3319_);
v_usedLetOnly_boxed_3326_ = lean_unbox(v_usedLetOnly_3323_);
v_generalizeNondepLet_boxed_3327_ = lean_unbox(v_generalizeNondepLet_3324_);
v_res_3328_ = l_Lean_LocalContext_mkBinding(v_isLambda_boxed_3325_, v_lctx_3320_, v_xs_3321_, v_b_3322_, v_usedLetOnly_boxed_3326_, v_generalizeNondepLet_boxed_3327_);
lean_dec_ref(v_b_3322_);
return v_res_3328_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(lean_object* v_xs_3329_, lean_object* v_lctx_3330_, uint8_t v_usedLetOnly_3331_, uint8_t v_generalizeNondepLet_3332_, lean_object* v_x_3333_, lean_object* v_x_3334_){
_start:
{
lean_object* v_zero_3335_; uint8_t v_isZero_3336_; 
v_zero_3335_ = lean_unsigned_to_nat(0u);
v_isZero_3336_ = lean_nat_dec_eq(v_x_3333_, v_zero_3335_);
if (v_isZero_3336_ == 1)
{
lean_dec(v_x_3333_);
lean_dec_ref(v_lctx_3330_);
return v_x_3334_;
}
else
{
lean_object* v_one_3337_; lean_object* v_n_3338_; lean_object* v_n_3340_; lean_object* v_ty_3341_; uint8_t v_bi_3342_; lean_object* v_x_3346_; lean_object* v___x_3347_; 
v_one_3337_ = lean_unsigned_to_nat(1u);
v_n_3338_ = lean_nat_sub(v_x_3333_, v_one_3337_);
lean_dec(v_x_3333_);
v_x_3346_ = lean_array_fget_borrowed(v_xs_3329_, v_n_3338_);
lean_inc_ref(v_lctx_3330_);
v___x_3347_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3330_, v_x_3346_);
if (lean_obj_tag(v___x_3347_) == 0)
{
lean_object* v___x_3348_; lean_object* v___x_3349_; 
lean_dec_ref(v_x_3334_);
v___x_3348_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3349_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3348_);
v_x_3333_ = v_n_3338_;
v_x_3334_ = v___x_3349_;
goto _start;
}
else
{
lean_object* v_val_3351_; 
v_val_3351_ = lean_ctor_get(v___x_3347_, 0);
lean_inc(v_val_3351_);
lean_dec_ref_known(v___x_3347_, 1);
if (lean_obj_tag(v_val_3351_) == 0)
{
lean_object* v_userName_3352_; lean_object* v_type_3353_; uint8_t v_bi_3354_; 
v_userName_3352_ = lean_ctor_get(v_val_3351_, 2);
lean_inc(v_userName_3352_);
v_type_3353_ = lean_ctor_get(v_val_3351_, 3);
lean_inc_ref(v_type_3353_);
v_bi_3354_ = lean_ctor_get_uint8(v_val_3351_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3351_, 4);
v_n_3340_ = v_userName_3352_;
v_ty_3341_ = v_type_3353_;
v_bi_3342_ = v_bi_3354_;
goto v___jp_3339_;
}
else
{
lean_object* v_userName_3355_; lean_object* v_type_3356_; lean_object* v_value_3357_; uint8_t v_nondep_3358_; uint8_t v___y_3365_; 
v_userName_3355_ = lean_ctor_get(v_val_3351_, 2);
lean_inc(v_userName_3355_);
v_type_3356_ = lean_ctor_get(v_val_3351_, 3);
lean_inc_ref(v_type_3356_);
v_value_3357_ = lean_ctor_get(v_val_3351_, 4);
lean_inc_ref(v_value_3357_);
v_nondep_3358_ = lean_ctor_get_uint8(v_val_3351_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3351_, 5);
if (v_nondep_3358_ == 0)
{
v___y_3365_ = v_nondep_3358_;
goto v___jp_3364_;
}
else
{
if (v_generalizeNondepLet_3332_ == 0)
{
v___y_3365_ = v_generalizeNondepLet_3332_;
goto v___jp_3364_;
}
else
{
uint8_t v___x_3369_; 
lean_dec_ref(v_value_3357_);
v___x_3369_ = 0;
v_n_3340_ = v_userName_3355_;
v_ty_3341_ = v_type_3356_;
v_bi_3342_ = v___x_3369_;
goto v___jp_3339_;
}
}
v___jp_3359_:
{
lean_object* v_ty_3360_; lean_object* v_val_3361_; lean_object* v___x_3362_; 
v_ty_3360_ = lean_expr_abstract_range(v_type_3356_, v_n_3338_, v_xs_3329_);
lean_dec_ref(v_type_3356_);
v_val_3361_ = lean_expr_abstract_range(v_value_3357_, v_n_3338_, v_xs_3329_);
lean_dec_ref(v_value_3357_);
v___x_3362_ = l_Lean_Expr_letE___override(v_userName_3355_, v_ty_3360_, v_val_3361_, v_x_3334_, v_nondep_3358_);
v_x_3333_ = v_n_3338_;
v_x_3334_ = v___x_3362_;
goto _start;
}
v___jp_3364_:
{
if (v_usedLetOnly_3331_ == 0)
{
goto v___jp_3359_;
}
else
{
if (v___y_3365_ == 0)
{
uint8_t v___x_3366_; 
v___x_3366_ = lean_expr_has_loose_bvar(v_x_3334_, v_zero_3335_);
if (v___x_3366_ == 0)
{
lean_object* v___x_3367_; 
lean_dec_ref(v_value_3357_);
lean_dec_ref(v_type_3356_);
lean_dec(v_userName_3355_);
v___x_3367_ = lean_expr_lower_loose_bvars(v_x_3334_, v_one_3337_, v_one_3337_);
lean_dec_ref(v_x_3334_);
v_x_3333_ = v_n_3338_;
v_x_3334_ = v___x_3367_;
goto _start;
}
else
{
goto v___jp_3359_;
}
}
else
{
goto v___jp_3359_;
}
}
}
}
}
v___jp_3339_:
{
lean_object* v_ty_3343_; lean_object* v___x_3344_; 
v_ty_3343_ = lean_expr_abstract_range(v_ty_3341_, v_n_3338_, v_xs_3329_);
lean_dec_ref(v_ty_3341_);
v___x_3344_ = l_Lean_mkLambda(v_n_3340_, v_bi_3342_, v_ty_3343_, v_x_3334_);
v_x_3333_ = v_n_3338_;
v_x_3334_ = v___x_3344_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0___boxed(lean_object* v_xs_3370_, lean_object* v_lctx_3371_, lean_object* v_usedLetOnly_3372_, lean_object* v_generalizeNondepLet_3373_, lean_object* v_x_3374_, lean_object* v_x_3375_){
_start:
{
uint8_t v_usedLetOnly_boxed_3376_; uint8_t v_generalizeNondepLet_boxed_3377_; lean_object* v_res_3378_; 
v_usedLetOnly_boxed_3376_ = lean_unbox(v_usedLetOnly_3372_);
v_generalizeNondepLet_boxed_3377_ = lean_unbox(v_generalizeNondepLet_3373_);
v_res_3378_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3370_, v_lctx_3371_, v_usedLetOnly_boxed_3376_, v_generalizeNondepLet_boxed_3377_, v_x_3374_, v_x_3375_);
lean_dec_ref(v_xs_3370_);
return v_res_3378_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(lean_object* v_xs_3379_, lean_object* v_lctx_3380_, uint8_t v_usedLetOnly_3381_, uint8_t v_generalizeNondepLet_3382_, lean_object* v_x_3383_, lean_object* v_x_3384_){
_start:
{
lean_object* v_zero_3385_; uint8_t v_isZero_3386_; 
v_zero_3385_ = lean_unsigned_to_nat(0u);
v_isZero_3386_ = lean_nat_dec_eq(v_x_3383_, v_zero_3385_);
if (v_isZero_3386_ == 1)
{
lean_dec_ref(v_lctx_3380_);
return v_x_3384_;
}
else
{
lean_object* v_one_3387_; lean_object* v_n_3388_; lean_object* v_n_3390_; lean_object* v_ty_3391_; uint8_t v_bi_3392_; lean_object* v_x_3396_; lean_object* v___x_3397_; 
v_one_3387_ = lean_unsigned_to_nat(1u);
v_n_3388_ = lean_nat_sub(v_x_3383_, v_one_3387_);
v_x_3396_ = lean_array_fget_borrowed(v_xs_3379_, v_n_3388_);
lean_inc_ref(v_lctx_3380_);
v___x_3397_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3380_, v_x_3396_);
if (lean_obj_tag(v___x_3397_) == 0)
{
lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; 
lean_dec_ref(v_x_3384_);
v___x_3398_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3399_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3398_);
v___x_3400_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3379_, v_lctx_3380_, v_usedLetOnly_3381_, v_generalizeNondepLet_3382_, v_n_3388_, v___x_3399_);
return v___x_3400_;
}
else
{
lean_object* v_val_3401_; 
v_val_3401_ = lean_ctor_get(v___x_3397_, 0);
lean_inc(v_val_3401_);
lean_dec_ref_known(v___x_3397_, 1);
if (lean_obj_tag(v_val_3401_) == 0)
{
lean_object* v_userName_3402_; lean_object* v_type_3403_; uint8_t v_bi_3404_; 
v_userName_3402_ = lean_ctor_get(v_val_3401_, 2);
lean_inc(v_userName_3402_);
v_type_3403_ = lean_ctor_get(v_val_3401_, 3);
lean_inc_ref(v_type_3403_);
v_bi_3404_ = lean_ctor_get_uint8(v_val_3401_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3401_, 4);
v_n_3390_ = v_userName_3402_;
v_ty_3391_ = v_type_3403_;
v_bi_3392_ = v_bi_3404_;
goto v___jp_3389_;
}
else
{
lean_object* v_userName_3405_; lean_object* v_type_3406_; lean_object* v_value_3407_; uint8_t v_nondep_3408_; uint8_t v___y_3415_; 
v_userName_3405_ = lean_ctor_get(v_val_3401_, 2);
lean_inc(v_userName_3405_);
v_type_3406_ = lean_ctor_get(v_val_3401_, 3);
lean_inc_ref(v_type_3406_);
v_value_3407_ = lean_ctor_get(v_val_3401_, 4);
lean_inc_ref(v_value_3407_);
v_nondep_3408_ = lean_ctor_get_uint8(v_val_3401_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3401_, 5);
if (v_nondep_3408_ == 0)
{
v___y_3415_ = v_nondep_3408_;
goto v___jp_3414_;
}
else
{
if (v_generalizeNondepLet_3382_ == 0)
{
v___y_3415_ = v_generalizeNondepLet_3382_;
goto v___jp_3414_;
}
else
{
uint8_t v___x_3419_; 
lean_dec_ref(v_value_3407_);
v___x_3419_ = 0;
v_n_3390_ = v_userName_3405_;
v_ty_3391_ = v_type_3406_;
v_bi_3392_ = v___x_3419_;
goto v___jp_3389_;
}
}
v___jp_3409_:
{
lean_object* v_ty_3410_; lean_object* v_val_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; 
v_ty_3410_ = lean_expr_abstract_range(v_type_3406_, v_n_3388_, v_xs_3379_);
lean_dec_ref(v_type_3406_);
v_val_3411_ = lean_expr_abstract_range(v_value_3407_, v_n_3388_, v_xs_3379_);
lean_dec_ref(v_value_3407_);
v___x_3412_ = l_Lean_Expr_letE___override(v_userName_3405_, v_ty_3410_, v_val_3411_, v_x_3384_, v_nondep_3408_);
v___x_3413_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3379_, v_lctx_3380_, v_usedLetOnly_3381_, v_generalizeNondepLet_3382_, v_n_3388_, v___x_3412_);
return v___x_3413_;
}
v___jp_3414_:
{
if (v_usedLetOnly_3381_ == 0)
{
goto v___jp_3409_;
}
else
{
if (v___y_3415_ == 0)
{
uint8_t v___x_3416_; 
v___x_3416_ = lean_expr_has_loose_bvar(v_x_3384_, v_zero_3385_);
if (v___x_3416_ == 0)
{
lean_object* v___x_3417_; lean_object* v___x_3418_; 
lean_dec_ref(v_value_3407_);
lean_dec_ref(v_type_3406_);
lean_dec(v_userName_3405_);
v___x_3417_ = lean_expr_lower_loose_bvars(v_x_3384_, v_one_3387_, v_one_3387_);
lean_dec_ref(v_x_3384_);
v___x_3418_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3379_, v_lctx_3380_, v_usedLetOnly_3381_, v_generalizeNondepLet_3382_, v_n_3388_, v___x_3417_);
return v___x_3418_;
}
else
{
goto v___jp_3409_;
}
}
else
{
goto v___jp_3409_;
}
}
}
}
}
v___jp_3389_:
{
lean_object* v_ty_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; 
v_ty_3393_ = lean_expr_abstract_range(v_ty_3391_, v_n_3388_, v_xs_3379_);
lean_dec_ref(v_ty_3391_);
v___x_3394_ = l_Lean_mkLambda(v_n_3390_, v_bi_3392_, v_ty_3393_, v_x_3384_);
v___x_3395_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3379_, v_lctx_3380_, v_usedLetOnly_3381_, v_generalizeNondepLet_3382_, v_n_3388_, v___x_3394_);
return v___x_3395_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0___boxed(lean_object* v_xs_3420_, lean_object* v_lctx_3421_, lean_object* v_usedLetOnly_3422_, lean_object* v_generalizeNondepLet_3423_, lean_object* v_x_3424_, lean_object* v_x_3425_){
_start:
{
uint8_t v_usedLetOnly_boxed_3426_; uint8_t v_generalizeNondepLet_boxed_3427_; lean_object* v_res_3428_; 
v_usedLetOnly_boxed_3426_ = lean_unbox(v_usedLetOnly_3422_);
v_generalizeNondepLet_boxed_3427_ = lean_unbox(v_generalizeNondepLet_3423_);
v_res_3428_ = l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(v_xs_3420_, v_lctx_3421_, v_usedLetOnly_boxed_3426_, v_generalizeNondepLet_boxed_3427_, v_x_3424_, v_x_3425_);
lean_dec(v_x_3424_);
lean_dec_ref(v_xs_3420_);
return v_res_3428_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLambda(lean_object* v_lctx_3429_, lean_object* v_xs_3430_, lean_object* v_b_3431_, uint8_t v_usedLetOnly_3432_, uint8_t v_generalizeNondepLet_3433_){
_start:
{
lean_object* v_b_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; 
v_b_3434_ = lean_expr_abstract(v_b_3431_, v_xs_3430_);
v___x_3435_ = lean_array_get_size(v_xs_3430_);
v___x_3436_ = l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(v_xs_3430_, v_lctx_3429_, v_usedLetOnly_3432_, v_generalizeNondepLet_3433_, v___x_3435_, v_b_3434_);
return v___x_3436_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLambda___boxed(lean_object* v_lctx_3437_, lean_object* v_xs_3438_, lean_object* v_b_3439_, lean_object* v_usedLetOnly_3440_, lean_object* v_generalizeNondepLet_3441_){
_start:
{
uint8_t v_usedLetOnly_boxed_3442_; uint8_t v_generalizeNondepLet_boxed_3443_; lean_object* v_res_3444_; 
v_usedLetOnly_boxed_3442_ = lean_unbox(v_usedLetOnly_3440_);
v_generalizeNondepLet_boxed_3443_ = lean_unbox(v_generalizeNondepLet_3441_);
v_res_3444_ = l_Lean_LocalContext_mkLambda(v_lctx_3437_, v_xs_3438_, v_b_3439_, v_usedLetOnly_boxed_3442_, v_generalizeNondepLet_boxed_3443_);
lean_dec_ref(v_b_3439_);
lean_dec_ref(v_xs_3438_);
return v_res_3444_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(lean_object* v_xs_3445_, lean_object* v_lctx_3446_, uint8_t v_usedLetOnly_3447_, uint8_t v_generalizeNondepLet_3448_, lean_object* v_x_3449_, lean_object* v_x_3450_){
_start:
{
lean_object* v_zero_3451_; uint8_t v_isZero_3452_; 
v_zero_3451_ = lean_unsigned_to_nat(0u);
v_isZero_3452_ = lean_nat_dec_eq(v_x_3449_, v_zero_3451_);
if (v_isZero_3452_ == 1)
{
lean_dec(v_x_3449_);
lean_dec_ref(v_lctx_3446_);
return v_x_3450_;
}
else
{
lean_object* v_one_3453_; lean_object* v_n_3454_; lean_object* v_n_3456_; lean_object* v_ty_3457_; uint8_t v_bi_3458_; lean_object* v_x_3462_; lean_object* v___x_3463_; 
v_one_3453_ = lean_unsigned_to_nat(1u);
v_n_3454_ = lean_nat_sub(v_x_3449_, v_one_3453_);
lean_dec(v_x_3449_);
v_x_3462_ = lean_array_fget_borrowed(v_xs_3445_, v_n_3454_);
lean_inc_ref(v_lctx_3446_);
v___x_3463_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3446_, v_x_3462_);
if (lean_obj_tag(v___x_3463_) == 0)
{
lean_object* v___x_3464_; lean_object* v___x_3465_; 
lean_dec_ref(v_x_3450_);
v___x_3464_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3465_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3464_);
v_x_3449_ = v_n_3454_;
v_x_3450_ = v___x_3465_;
goto _start;
}
else
{
lean_object* v_val_3467_; 
v_val_3467_ = lean_ctor_get(v___x_3463_, 0);
lean_inc(v_val_3467_);
lean_dec_ref_known(v___x_3463_, 1);
if (lean_obj_tag(v_val_3467_) == 0)
{
lean_object* v_userName_3468_; lean_object* v_type_3469_; uint8_t v_bi_3470_; 
v_userName_3468_ = lean_ctor_get(v_val_3467_, 2);
lean_inc(v_userName_3468_);
v_type_3469_ = lean_ctor_get(v_val_3467_, 3);
lean_inc_ref(v_type_3469_);
v_bi_3470_ = lean_ctor_get_uint8(v_val_3467_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3467_, 4);
v_n_3456_ = v_userName_3468_;
v_ty_3457_ = v_type_3469_;
v_bi_3458_ = v_bi_3470_;
goto v___jp_3455_;
}
else
{
lean_object* v_userName_3471_; lean_object* v_type_3472_; lean_object* v_value_3473_; uint8_t v_nondep_3474_; uint8_t v___y_3481_; 
v_userName_3471_ = lean_ctor_get(v_val_3467_, 2);
lean_inc(v_userName_3471_);
v_type_3472_ = lean_ctor_get(v_val_3467_, 3);
lean_inc_ref(v_type_3472_);
v_value_3473_ = lean_ctor_get(v_val_3467_, 4);
lean_inc_ref(v_value_3473_);
v_nondep_3474_ = lean_ctor_get_uint8(v_val_3467_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3467_, 5);
if (v_nondep_3474_ == 0)
{
v___y_3481_ = v_nondep_3474_;
goto v___jp_3480_;
}
else
{
if (v_generalizeNondepLet_3448_ == 0)
{
v___y_3481_ = v_generalizeNondepLet_3448_;
goto v___jp_3480_;
}
else
{
uint8_t v___x_3485_; 
lean_dec_ref(v_value_3473_);
v___x_3485_ = 0;
v_n_3456_ = v_userName_3471_;
v_ty_3457_ = v_type_3472_;
v_bi_3458_ = v___x_3485_;
goto v___jp_3455_;
}
}
v___jp_3475_:
{
lean_object* v_ty_3476_; lean_object* v_val_3477_; lean_object* v___x_3478_; 
v_ty_3476_ = lean_expr_abstract_range(v_type_3472_, v_n_3454_, v_xs_3445_);
lean_dec_ref(v_type_3472_);
v_val_3477_ = lean_expr_abstract_range(v_value_3473_, v_n_3454_, v_xs_3445_);
lean_dec_ref(v_value_3473_);
v___x_3478_ = l_Lean_Expr_letE___override(v_userName_3471_, v_ty_3476_, v_val_3477_, v_x_3450_, v_nondep_3474_);
v_x_3449_ = v_n_3454_;
v_x_3450_ = v___x_3478_;
goto _start;
}
v___jp_3480_:
{
if (v_usedLetOnly_3447_ == 0)
{
goto v___jp_3475_;
}
else
{
if (v___y_3481_ == 0)
{
uint8_t v___x_3482_; 
v___x_3482_ = lean_expr_has_loose_bvar(v_x_3450_, v_zero_3451_);
if (v___x_3482_ == 0)
{
lean_object* v___x_3483_; 
lean_dec_ref(v_value_3473_);
lean_dec_ref(v_type_3472_);
lean_dec(v_userName_3471_);
v___x_3483_ = lean_expr_lower_loose_bvars(v_x_3450_, v_one_3453_, v_one_3453_);
lean_dec_ref(v_x_3450_);
v_x_3449_ = v_n_3454_;
v_x_3450_ = v___x_3483_;
goto _start;
}
else
{
goto v___jp_3475_;
}
}
else
{
goto v___jp_3475_;
}
}
}
}
}
v___jp_3455_:
{
lean_object* v_ty_3459_; lean_object* v___x_3460_; 
v_ty_3459_ = lean_expr_abstract_range(v_ty_3457_, v_n_3454_, v_xs_3445_);
lean_dec_ref(v_ty_3457_);
v___x_3460_ = l_Lean_mkForall(v_n_3456_, v_bi_3458_, v_ty_3459_, v_x_3450_);
v_x_3449_ = v_n_3454_;
v_x_3450_ = v___x_3460_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0___boxed(lean_object* v_xs_3486_, lean_object* v_lctx_3487_, lean_object* v_usedLetOnly_3488_, lean_object* v_generalizeNondepLet_3489_, lean_object* v_x_3490_, lean_object* v_x_3491_){
_start:
{
uint8_t v_usedLetOnly_boxed_3492_; uint8_t v_generalizeNondepLet_boxed_3493_; lean_object* v_res_3494_; 
v_usedLetOnly_boxed_3492_ = lean_unbox(v_usedLetOnly_3488_);
v_generalizeNondepLet_boxed_3493_ = lean_unbox(v_generalizeNondepLet_3489_);
v_res_3494_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3486_, v_lctx_3487_, v_usedLetOnly_boxed_3492_, v_generalizeNondepLet_boxed_3493_, v_x_3490_, v_x_3491_);
lean_dec_ref(v_xs_3486_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(lean_object* v_xs_3495_, lean_object* v_lctx_3496_, uint8_t v_usedLetOnly_3497_, uint8_t v_generalizeNondepLet_3498_, lean_object* v_x_3499_, lean_object* v_x_3500_){
_start:
{
lean_object* v_zero_3501_; uint8_t v_isZero_3502_; 
v_zero_3501_ = lean_unsigned_to_nat(0u);
v_isZero_3502_ = lean_nat_dec_eq(v_x_3499_, v_zero_3501_);
if (v_isZero_3502_ == 1)
{
lean_dec_ref(v_lctx_3496_);
return v_x_3500_;
}
else
{
lean_object* v_one_3503_; lean_object* v_n_3504_; lean_object* v_n_3506_; lean_object* v_ty_3507_; uint8_t v_bi_3508_; lean_object* v_x_3512_; lean_object* v___x_3513_; 
v_one_3503_ = lean_unsigned_to_nat(1u);
v_n_3504_ = lean_nat_sub(v_x_3499_, v_one_3503_);
v_x_3512_ = lean_array_fget_borrowed(v_xs_3495_, v_n_3504_);
lean_inc_ref(v_lctx_3496_);
v___x_3513_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3496_, v_x_3512_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; 
lean_dec_ref(v_x_3500_);
v___x_3514_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3515_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3514_);
v___x_3516_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3495_, v_lctx_3496_, v_usedLetOnly_3497_, v_generalizeNondepLet_3498_, v_n_3504_, v___x_3515_);
return v___x_3516_;
}
else
{
lean_object* v_val_3517_; 
v_val_3517_ = lean_ctor_get(v___x_3513_, 0);
lean_inc(v_val_3517_);
lean_dec_ref_known(v___x_3513_, 1);
if (lean_obj_tag(v_val_3517_) == 0)
{
lean_object* v_userName_3518_; lean_object* v_type_3519_; uint8_t v_bi_3520_; 
v_userName_3518_ = lean_ctor_get(v_val_3517_, 2);
lean_inc(v_userName_3518_);
v_type_3519_ = lean_ctor_get(v_val_3517_, 3);
lean_inc_ref(v_type_3519_);
v_bi_3520_ = lean_ctor_get_uint8(v_val_3517_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3517_, 4);
v_n_3506_ = v_userName_3518_;
v_ty_3507_ = v_type_3519_;
v_bi_3508_ = v_bi_3520_;
goto v___jp_3505_;
}
else
{
lean_object* v_userName_3521_; lean_object* v_type_3522_; lean_object* v_value_3523_; uint8_t v_nondep_3524_; uint8_t v___y_3531_; 
v_userName_3521_ = lean_ctor_get(v_val_3517_, 2);
lean_inc(v_userName_3521_);
v_type_3522_ = lean_ctor_get(v_val_3517_, 3);
lean_inc_ref(v_type_3522_);
v_value_3523_ = lean_ctor_get(v_val_3517_, 4);
lean_inc_ref(v_value_3523_);
v_nondep_3524_ = lean_ctor_get_uint8(v_val_3517_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3517_, 5);
if (v_nondep_3524_ == 0)
{
v___y_3531_ = v_nondep_3524_;
goto v___jp_3530_;
}
else
{
if (v_generalizeNondepLet_3498_ == 0)
{
v___y_3531_ = v_generalizeNondepLet_3498_;
goto v___jp_3530_;
}
else
{
uint8_t v___x_3535_; 
lean_dec_ref(v_value_3523_);
v___x_3535_ = 0;
v_n_3506_ = v_userName_3521_;
v_ty_3507_ = v_type_3522_;
v_bi_3508_ = v___x_3535_;
goto v___jp_3505_;
}
}
v___jp_3525_:
{
lean_object* v_ty_3526_; lean_object* v_val_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; 
v_ty_3526_ = lean_expr_abstract_range(v_type_3522_, v_n_3504_, v_xs_3495_);
lean_dec_ref(v_type_3522_);
v_val_3527_ = lean_expr_abstract_range(v_value_3523_, v_n_3504_, v_xs_3495_);
lean_dec_ref(v_value_3523_);
v___x_3528_ = l_Lean_Expr_letE___override(v_userName_3521_, v_ty_3526_, v_val_3527_, v_x_3500_, v_nondep_3524_);
v___x_3529_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3495_, v_lctx_3496_, v_usedLetOnly_3497_, v_generalizeNondepLet_3498_, v_n_3504_, v___x_3528_);
return v___x_3529_;
}
v___jp_3530_:
{
if (v_usedLetOnly_3497_ == 0)
{
goto v___jp_3525_;
}
else
{
if (v___y_3531_ == 0)
{
uint8_t v___x_3532_; 
v___x_3532_ = lean_expr_has_loose_bvar(v_x_3500_, v_zero_3501_);
if (v___x_3532_ == 0)
{
lean_object* v___x_3533_; lean_object* v___x_3534_; 
lean_dec_ref(v_value_3523_);
lean_dec_ref(v_type_3522_);
lean_dec(v_userName_3521_);
v___x_3533_ = lean_expr_lower_loose_bvars(v_x_3500_, v_one_3503_, v_one_3503_);
lean_dec_ref(v_x_3500_);
v___x_3534_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3495_, v_lctx_3496_, v_usedLetOnly_3497_, v_generalizeNondepLet_3498_, v_n_3504_, v___x_3533_);
return v___x_3534_;
}
else
{
goto v___jp_3525_;
}
}
else
{
goto v___jp_3525_;
}
}
}
}
}
v___jp_3505_:
{
lean_object* v_ty_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; 
v_ty_3509_ = lean_expr_abstract_range(v_ty_3507_, v_n_3504_, v_xs_3495_);
lean_dec_ref(v_ty_3507_);
v___x_3510_ = l_Lean_mkForall(v_n_3506_, v_bi_3508_, v_ty_3509_, v_x_3500_);
v___x_3511_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3495_, v_lctx_3496_, v_usedLetOnly_3497_, v_generalizeNondepLet_3498_, v_n_3504_, v___x_3510_);
return v___x_3511_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0___boxed(lean_object* v_xs_3536_, lean_object* v_lctx_3537_, lean_object* v_usedLetOnly_3538_, lean_object* v_generalizeNondepLet_3539_, lean_object* v_x_3540_, lean_object* v_x_3541_){
_start:
{
uint8_t v_usedLetOnly_boxed_3542_; uint8_t v_generalizeNondepLet_boxed_3543_; lean_object* v_res_3544_; 
v_usedLetOnly_boxed_3542_ = lean_unbox(v_usedLetOnly_3538_);
v_generalizeNondepLet_boxed_3543_ = lean_unbox(v_generalizeNondepLet_3539_);
v_res_3544_ = l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(v_xs_3536_, v_lctx_3537_, v_usedLetOnly_boxed_3542_, v_generalizeNondepLet_boxed_3543_, v_x_3540_, v_x_3541_);
lean_dec(v_x_3540_);
lean_dec_ref(v_xs_3536_);
return v_res_3544_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkForall(lean_object* v_lctx_3545_, lean_object* v_xs_3546_, lean_object* v_b_3547_, uint8_t v_usedLetOnly_3548_, uint8_t v_generalizeNondepLet_3549_){
_start:
{
lean_object* v_b_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; 
v_b_3550_ = lean_expr_abstract(v_b_3547_, v_xs_3546_);
v___x_3551_ = lean_array_get_size(v_xs_3546_);
v___x_3552_ = l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(v_xs_3546_, v_lctx_3545_, v_usedLetOnly_3548_, v_generalizeNondepLet_3549_, v___x_3551_, v_b_3550_);
return v___x_3552_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkForall___boxed(lean_object* v_lctx_3553_, lean_object* v_xs_3554_, lean_object* v_b_3555_, lean_object* v_usedLetOnly_3556_, lean_object* v_generalizeNondepLet_3557_){
_start:
{
uint8_t v_usedLetOnly_boxed_3558_; uint8_t v_generalizeNondepLet_boxed_3559_; lean_object* v_res_3560_; 
v_usedLetOnly_boxed_3558_ = lean_unbox(v_usedLetOnly_3556_);
v_generalizeNondepLet_boxed_3559_ = lean_unbox(v_generalizeNondepLet_3557_);
v_res_3560_ = l_Lean_LocalContext_mkForall(v_lctx_3553_, v_xs_3554_, v_b_3555_, v_usedLetOnly_boxed_3558_, v_generalizeNondepLet_boxed_3559_);
lean_dec_ref(v_b_3555_);
lean_dec_ref(v_xs_3554_);
return v_res_3560_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM___redArg___lam__0(lean_object* v_toPure_3561_, lean_object* v_p_3562_, lean_object* v_d_3563_){
_start:
{
if (lean_obj_tag(v_d_3563_) == 0)
{
uint8_t v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; 
lean_dec(v_p_3562_);
v___x_3564_ = 0;
v___x_3565_ = lean_box(v___x_3564_);
v___x_3566_ = lean_apply_2(v_toPure_3561_, lean_box(0), v___x_3565_);
return v___x_3566_;
}
else
{
lean_object* v_val_3567_; lean_object* v___x_3568_; 
lean_dec(v_toPure_3561_);
v_val_3567_ = lean_ctor_get(v_d_3563_, 0);
lean_inc(v_val_3567_);
lean_dec_ref_known(v_d_3563_, 1);
v___x_3568_ = lean_apply_1(v_p_3562_, v_val_3567_);
return v___x_3568_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM___redArg(lean_object* v_inst_3569_, lean_object* v_lctx_3570_, lean_object* v_p_3571_){
_start:
{
lean_object* v_toApplicative_3572_; lean_object* v_decls_3573_; lean_object* v_toPure_3574_; lean_object* v___f_3575_; lean_object* v___x_3576_; 
v_toApplicative_3572_ = lean_ctor_get(v_inst_3569_, 0);
v_decls_3573_ = lean_ctor_get(v_lctx_3570_, 1);
lean_inc_ref(v_decls_3573_);
lean_dec_ref(v_lctx_3570_);
v_toPure_3574_ = lean_ctor_get(v_toApplicative_3572_, 1);
lean_inc(v_toPure_3574_);
v___f_3575_ = lean_alloc_closure((void*)(l_Lean_LocalContext_anyM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3575_, 0, v_toPure_3574_);
lean_closure_set(v___f_3575_, 1, v_p_3571_);
v___x_3576_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3569_, v_decls_3573_, v___f_3575_);
return v___x_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM(lean_object* v_m_3577_, lean_object* v_inst_3578_, lean_object* v_lctx_3579_, lean_object* v_p_3580_){
_start:
{
lean_object* v_toApplicative_3581_; lean_object* v_decls_3582_; lean_object* v_toPure_3583_; lean_object* v___f_3584_; lean_object* v___x_3585_; 
v_toApplicative_3581_ = lean_ctor_get(v_inst_3578_, 0);
v_decls_3582_ = lean_ctor_get(v_lctx_3579_, 1);
lean_inc_ref(v_decls_3582_);
lean_dec_ref(v_lctx_3579_);
v_toPure_3583_ = lean_ctor_get(v_toApplicative_3581_, 1);
lean_inc(v_toPure_3583_);
v___f_3584_ = lean_alloc_closure((void*)(l_Lean_LocalContext_anyM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3584_, 0, v_toPure_3583_);
lean_closure_set(v___f_3584_, 1, v_p_3580_);
v___x_3585_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3578_, v_decls_3582_, v___f_3584_);
return v___x_3585_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__0(lean_object* v_toPure_3586_, uint8_t v_b_3587_){
_start:
{
if (v_b_3587_ == 0)
{
uint8_t v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; 
v___x_3588_ = 1;
v___x_3589_ = lean_box(v___x_3588_);
v___x_3590_ = lean_apply_2(v_toPure_3586_, lean_box(0), v___x_3589_);
return v___x_3590_;
}
else
{
uint8_t v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; 
v___x_3591_ = 0;
v___x_3592_ = lean_box(v___x_3591_);
v___x_3593_ = lean_apply_2(v_toPure_3586_, lean_box(0), v___x_3592_);
return v___x_3593_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__0___boxed(lean_object* v_toPure_3594_, lean_object* v_b_3595_){
_start:
{
uint8_t v_b_boxed_3596_; lean_object* v_res_3597_; 
v_b_boxed_3596_ = lean_unbox(v_b_3595_);
v_res_3597_ = l_Lean_LocalContext_allM___redArg___lam__0(v_toPure_3594_, v_b_boxed_3596_);
return v_res_3597_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__2(lean_object* v_toPure_3598_, lean_object* v_toBind_3599_, lean_object* v___f_3600_, lean_object* v_p_3601_, lean_object* v_v_3602_){
_start:
{
if (lean_obj_tag(v_v_3602_) == 0)
{
uint8_t v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; 
lean_dec(v_p_3601_);
v___x_3603_ = 1;
v___x_3604_ = lean_box(v___x_3603_);
v___x_3605_ = lean_apply_2(v_toPure_3598_, lean_box(0), v___x_3604_);
v___x_3606_ = lean_apply_4(v_toBind_3599_, lean_box(0), lean_box(0), v___x_3605_, v___f_3600_);
return v___x_3606_;
}
else
{
lean_object* v_val_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; 
lean_dec(v_toPure_3598_);
v_val_3607_ = lean_ctor_get(v_v_3602_, 0);
lean_inc(v_val_3607_);
lean_dec_ref_known(v_v_3602_, 1);
v___x_3608_ = lean_apply_1(v_p_3601_, v_val_3607_);
v___x_3609_ = lean_apply_4(v_toBind_3599_, lean_box(0), lean_box(0), v___x_3608_, v___f_3600_);
return v___x_3609_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg(lean_object* v_inst_3610_, lean_object* v_lctx_3611_, lean_object* v_p_3612_){
_start:
{
lean_object* v_toApplicative_3613_; lean_object* v_decls_3614_; lean_object* v_toBind_3615_; lean_object* v_toPure_3616_; lean_object* v___f_3617_; lean_object* v___f_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; 
v_toApplicative_3613_ = lean_ctor_get(v_inst_3610_, 0);
v_decls_3614_ = lean_ctor_get(v_lctx_3611_, 1);
lean_inc_ref(v_decls_3614_);
lean_dec_ref(v_lctx_3611_);
v_toBind_3615_ = lean_ctor_get(v_inst_3610_, 1);
lean_inc_n(v_toBind_3615_, 2);
v_toPure_3616_ = lean_ctor_get(v_toApplicative_3613_, 1);
lean_inc_n(v_toPure_3616_, 2);
v___f_3617_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3617_, 0, v_toPure_3616_);
lean_inc_ref(v___f_3617_);
v___f_3618_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3618_, 0, v_toPure_3616_);
lean_closure_set(v___f_3618_, 1, v_toBind_3615_);
lean_closure_set(v___f_3618_, 2, v___f_3617_);
lean_closure_set(v___f_3618_, 3, v_p_3612_);
v___x_3619_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3610_, v_decls_3614_, v___f_3618_);
v___x_3620_ = lean_apply_4(v_toBind_3615_, lean_box(0), lean_box(0), v___x_3619_, v___f_3617_);
return v___x_3620_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM(lean_object* v_m_3621_, lean_object* v_inst_3622_, lean_object* v_lctx_3623_, lean_object* v_p_3624_){
_start:
{
lean_object* v_toApplicative_3625_; lean_object* v_decls_3626_; lean_object* v_toBind_3627_; lean_object* v_toPure_3628_; lean_object* v___f_3629_; lean_object* v___f_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; 
v_toApplicative_3625_ = lean_ctor_get(v_inst_3622_, 0);
v_decls_3626_ = lean_ctor_get(v_lctx_3623_, 1);
lean_inc_ref(v_decls_3626_);
lean_dec_ref(v_lctx_3623_);
v_toBind_3627_ = lean_ctor_get(v_inst_3622_, 1);
lean_inc_n(v_toBind_3627_, 2);
v_toPure_3628_ = lean_ctor_get(v_toApplicative_3625_, 1);
lean_inc_n(v_toPure_3628_, 2);
v___f_3629_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3629_, 0, v_toPure_3628_);
lean_inc_ref(v___f_3629_);
v___f_3630_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3630_, 0, v_toPure_3628_);
lean_closure_set(v___f_3630_, 1, v_toBind_3627_);
lean_closure_set(v___f_3630_, 2, v___f_3629_);
lean_closure_set(v___f_3630_, 3, v_p_3624_);
v___x_3631_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3622_, v_decls_3626_, v___f_3630_);
v___x_3632_ = lean_apply_4(v_toBind_3627_, lean_box(0), lean_box(0), v___x_3631_, v___f_3629_);
return v___x_3632_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_any___lam__0(lean_object* v_p_3633_, lean_object* v_d_3634_){
_start:
{
if (lean_obj_tag(v_d_3634_) == 0)
{
uint8_t v___x_3635_; 
lean_dec_ref(v_p_3633_);
v___x_3635_ = 0;
return v___x_3635_;
}
else
{
lean_object* v_val_3636_; lean_object* v___x_3637_; uint8_t v___x_3638_; 
v_val_3636_ = lean_ctor_get(v_d_3634_, 0);
lean_inc(v_val_3636_);
lean_dec_ref_known(v_d_3634_, 1);
v___x_3637_ = lean_apply_1(v_p_3633_, v_val_3636_);
v___x_3638_ = lean_unbox(v___x_3637_);
return v___x_3638_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_any___lam__0___boxed(lean_object* v_p_3639_, lean_object* v_d_3640_){
_start:
{
uint8_t v_res_3641_; lean_object* v_r_3642_; 
v_res_3641_ = l_Lean_LocalContext_any___lam__0(v_p_3639_, v_d_3640_);
v_r_3642_ = lean_box(v_res_3641_);
return v_r_3642_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_any(lean_object* v_lctx_3643_, lean_object* v_p_3644_){
_start:
{
lean_object* v___x_3645_; lean_object* v_decls_3646_; lean_object* v___f_3647_; lean_object* v___x_3648_; uint8_t v___x_3649_; 
v___x_3645_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v_decls_3646_ = lean_ctor_get(v_lctx_3643_, 1);
lean_inc_ref(v_decls_3646_);
lean_dec_ref(v_lctx_3643_);
v___f_3647_ = lean_alloc_closure((void*)(l_Lean_LocalContext_any___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3647_, 0, v_p_3644_);
v___x_3648_ = l_Lean_PersistentArray_anyM___redArg(v___x_3645_, v_decls_3646_, v___f_3647_);
v___x_3649_ = lean_unbox(v___x_3648_);
lean_dec(v___x_3648_);
return v___x_3649_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_any___boxed(lean_object* v_lctx_3650_, lean_object* v_p_3651_){
_start:
{
uint8_t v_res_3652_; lean_object* v_r_3653_; 
v_res_3652_ = l_Lean_LocalContext_any(v_lctx_3650_, v_p_3651_);
v_r_3653_ = lean_box(v_res_3652_);
return v_r_3653_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_all___lam__0(lean_object* v_p_3654_, lean_object* v_v_3655_){
_start:
{
if (lean_obj_tag(v_v_3655_) == 0)
{
uint8_t v___x_3656_; 
lean_dec_ref(v_p_3654_);
v___x_3656_ = 0;
return v___x_3656_;
}
else
{
lean_object* v_val_3657_; lean_object* v___x_3658_; uint8_t v___x_3659_; 
v_val_3657_ = lean_ctor_get(v_v_3655_, 0);
lean_inc(v_val_3657_);
lean_dec_ref_known(v_v_3655_, 1);
v___x_3658_ = lean_apply_1(v_p_3654_, v_val_3657_);
v___x_3659_ = lean_unbox(v___x_3658_);
if (v___x_3659_ == 0)
{
uint8_t v___x_3660_; 
v___x_3660_ = 1;
return v___x_3660_;
}
else
{
uint8_t v___x_3661_; 
v___x_3661_ = 0;
return v___x_3661_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_all___lam__0___boxed(lean_object* v_p_3662_, lean_object* v_v_3663_){
_start:
{
uint8_t v_res_3664_; lean_object* v_r_3665_; 
v_res_3664_ = l_Lean_LocalContext_all___lam__0(v_p_3662_, v_v_3663_);
v_r_3665_ = lean_box(v_res_3664_);
return v_r_3665_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_all(lean_object* v_lctx_3666_, lean_object* v_p_3667_){
_start:
{
lean_object* v___x_3668_; lean_object* v_decls_3669_; lean_object* v___f_3670_; lean_object* v___x_3671_; uint8_t v___x_3672_; 
v___x_3668_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v_decls_3669_ = lean_ctor_get(v_lctx_3666_, 1);
lean_inc_ref(v_decls_3669_);
lean_dec_ref(v_lctx_3666_);
v___f_3670_ = lean_alloc_closure((void*)(l_Lean_LocalContext_all___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3670_, 0, v_p_3667_);
v___x_3671_ = l_Lean_PersistentArray_anyM___redArg(v___x_3668_, v_decls_3669_, v___f_3670_);
v___x_3672_ = lean_unbox(v___x_3671_);
lean_dec(v___x_3671_);
if (v___x_3672_ == 0)
{
uint8_t v___x_3673_; 
v___x_3673_ = 1;
return v___x_3673_;
}
else
{
uint8_t v___x_3674_; 
v___x_3674_ = 0;
return v___x_3674_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_all___boxed(lean_object* v_lctx_3675_, lean_object* v_p_3676_){
_start:
{
uint8_t v_res_3677_; lean_object* v_r_3678_; 
v_res_3677_ = l_Lean_LocalContext_all(v_lctx_3675_, v_p_3676_);
v_r_3678_ = lean_box(v_res_3677_);
return v_r_3678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(lean_object* v_i_3679_, lean_object* v_a_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_){
_start:
{
lean_object* v_zero_3683_; uint8_t v_isZero_3684_; 
v_zero_3683_ = lean_unsigned_to_nat(0u);
v_isZero_3684_ = lean_nat_dec_eq(v_i_3679_, v_zero_3683_);
if (v_isZero_3684_ == 1)
{
lean_object* v___x_3685_; lean_object* v___x_3686_; 
lean_dec(v_i_3679_);
v___x_3685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3685_, 0, v_a_3680_);
lean_ctor_set(v___x_3685_, 1, v___y_3681_);
v___x_3686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3686_, 0, v___x_3685_);
lean_ctor_set(v___x_3686_, 1, v___y_3682_);
return v___x_3686_;
}
else
{
lean_object* v_decls_3687_; lean_object* v_size_3688_; lean_object* v___x_3689_; lean_object* v_one_3690_; lean_object* v_n_3691_; lean_object* v___y_3693_; lean_object* v___y_3694_; lean_object* v___y_3695_; lean_object* v___y_3696_; lean_object* v___y_3700_; lean_object* v___y_3701_; lean_object* v___y_3708_; lean_object* v___y_3709_; uint8_t v___y_3710_; lean_object* v___y_3714_; lean_object* v___y_3715_; lean_object* v___y_3720_; uint8_t v___x_3724_; 
v_decls_3687_ = lean_ctor_get(v_a_3680_, 1);
v_size_3688_ = lean_ctor_get(v_decls_3687_, 2);
v___x_3689_ = lean_box(0);
v_one_3690_ = lean_unsigned_to_nat(1u);
v_n_3691_ = lean_nat_sub(v_i_3679_, v_one_3690_);
lean_dec(v_i_3679_);
v___x_3724_ = lean_nat_dec_lt(v_n_3691_, v_size_3688_);
if (v___x_3724_ == 0)
{
lean_object* v___x_3725_; 
v___x_3725_ = l_outOfBounds___redArg(v___x_3689_);
v___y_3720_ = v___x_3725_;
goto v___jp_3719_;
}
else
{
lean_object* v___x_3726_; 
v___x_3726_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3689_, v_decls_3687_, v_n_3691_);
v___y_3720_ = v___x_3726_;
goto v___jp_3719_;
}
v___jp_3692_:
{
lean_object* v___x_3697_; 
v___x_3697_ = l_Lean_LocalContext_setUserName(v_a_3680_, v___y_3696_, v___y_3695_);
v_i_3679_ = v_n_3691_;
v_a_3680_ = v___x_3697_;
v___y_3681_ = v___y_3694_;
v___y_3682_ = v___y_3693_;
goto _start;
}
v___jp_3699_:
{
lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v_fst_3704_; lean_object* v_snd_3705_; lean_object* v_fvarId_3706_; 
lean_inc(v___y_3700_);
v___x_3702_ = l_Lean_NameSet_insert(v___y_3681_, v___y_3700_);
v___x_3703_ = l_Lean_sanitizeName(v___y_3700_, v___y_3682_);
v_fst_3704_ = lean_ctor_get(v___x_3703_, 0);
lean_inc(v_fst_3704_);
v_snd_3705_ = lean_ctor_get(v___x_3703_, 1);
lean_inc(v_snd_3705_);
lean_dec_ref(v___x_3703_);
v_fvarId_3706_ = lean_ctor_get(v___y_3701_, 1);
lean_inc(v_fvarId_3706_);
lean_dec_ref(v___y_3701_);
v___y_3693_ = v_snd_3705_;
v___y_3694_ = v___x_3702_;
v___y_3695_ = v_fst_3704_;
v___y_3696_ = v_fvarId_3706_;
goto v___jp_3692_;
}
v___jp_3707_:
{
if (v___y_3710_ == 0)
{
lean_object* v___x_3711_; 
lean_dec_ref(v___y_3709_);
v___x_3711_ = l_Lean_NameSet_insert(v___y_3681_, v___y_3708_);
v_i_3679_ = v_n_3691_;
v___y_3681_ = v___x_3711_;
goto _start;
}
else
{
v___y_3700_ = v___y_3708_;
v___y_3701_ = v___y_3709_;
goto v___jp_3699_;
}
}
v___jp_3713_:
{
uint8_t v___x_3716_; 
v___x_3716_ = l_Lean_Name_hasMacroScopes(v___y_3715_);
if (v___x_3716_ == 0)
{
lean_object* v_userName_3717_; uint8_t v___x_3718_; 
v_userName_3717_ = lean_ctor_get(v___y_3714_, 2);
v___x_3718_ = l_Lean_NameSet_contains(v___y_3681_, v_userName_3717_);
v___y_3708_ = v___y_3715_;
v___y_3709_ = v___y_3714_;
v___y_3710_ = v___x_3718_;
goto v___jp_3707_;
}
else
{
v___y_3700_ = v___y_3715_;
v___y_3701_ = v___y_3714_;
goto v___jp_3699_;
}
}
v___jp_3719_:
{
if (lean_obj_tag(v___y_3720_) == 0)
{
v_i_3679_ = v_n_3691_;
goto _start;
}
else
{
lean_object* v_val_3722_; lean_object* v_userName_3723_; 
v_val_3722_ = lean_ctor_get(v___y_3720_, 0);
lean_inc(v_val_3722_);
lean_dec_ref_known(v___y_3720_, 1);
v_userName_3723_ = lean_ctor_get(v_val_3722_, 2);
lean_inc(v_userName_3723_);
v___y_3714_ = v_val_3722_;
v___y_3715_ = v_userName_3723_;
goto v___jp_3713_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_sanitizeNames(lean_object* v_lctx_3727_, lean_object* v_a_3728_){
_start:
{
lean_object* v_options_3729_; uint8_t v___x_3730_; 
v_options_3729_ = lean_ctor_get(v_a_3728_, 0);
v___x_3730_ = l_Lean_getSanitizeNames(v_options_3729_);
if (v___x_3730_ == 0)
{
lean_object* v___x_3731_; 
v___x_3731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3731_, 0, v_lctx_3727_);
lean_ctor_set(v___x_3731_, 1, v_a_3728_);
return v___x_3731_;
}
else
{
lean_object* v_decls_3732_; lean_object* v_size_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v_fst_3736_; lean_object* v_snd_3737_; lean_object* v_fst_3738_; lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3745_; 
v_decls_3732_ = lean_ctor_get(v_lctx_3727_, 1);
v_size_3733_ = lean_ctor_get(v_decls_3732_, 2);
lean_inc(v_size_3733_);
v___x_3734_ = l_Lean_NameSet_empty;
v___x_3735_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(v_size_3733_, v_lctx_3727_, v___x_3734_, v_a_3728_);
v_fst_3736_ = lean_ctor_get(v___x_3735_, 0);
lean_inc(v_fst_3736_);
v_snd_3737_ = lean_ctor_get(v___x_3735_, 1);
lean_inc(v_snd_3737_);
lean_dec_ref(v___x_3735_);
v_fst_3738_ = lean_ctor_get(v_fst_3736_, 0);
v_isSharedCheck_3745_ = !lean_is_exclusive(v_fst_3736_);
if (v_isSharedCheck_3745_ == 0)
{
lean_object* v_unused_3746_; 
v_unused_3746_ = lean_ctor_get(v_fst_3736_, 1);
lean_dec(v_unused_3746_);
v___x_3740_ = v_fst_3736_;
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
else
{
lean_inc(v_fst_3738_);
lean_dec(v_fst_3736_);
v___x_3740_ = lean_box(0);
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
v_resetjp_3739_:
{
lean_object* v___x_3743_; 
if (v_isShared_3741_ == 0)
{
lean_ctor_set(v___x_3740_, 1, v_snd_3737_);
v___x_3743_ = v___x_3740_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v_fst_3738_);
lean_ctor_set(v_reuseFailAlloc_3744_, 1, v_snd_3737_);
v___x_3743_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
return v___x_3743_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0(lean_object* v_n_3747_, lean_object* v_i_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_){
_start:
{
lean_object* v___x_3753_; 
v___x_3753_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(v_i_3748_, v_a_3750_, v___y_3751_, v___y_3752_);
return v___x_3753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___boxed(lean_object* v_n_3754_, lean_object* v_i_3755_, lean_object* v_a_3756_, lean_object* v_a_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_){
_start:
{
lean_object* v_res_3760_; 
v_res_3760_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0(v_n_3754_, v_i_3755_, v_a_3756_, v_a_3757_, v___y_3758_, v___y_3759_);
lean_dec(v_n_3754_);
return v_res_3760_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getRoundtrippingUserName_x3f(lean_object* v_lctx_3761_, lean_object* v_fvarId_3762_){
_start:
{
lean_object* v___y_3764_; lean_object* v___y_3765_; lean_object* v___y_3766_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3773_; lean_object* v___x_3775_; 
lean_inc_ref(v_lctx_3761_);
v___x_3775_ = lean_local_ctx_find(v_lctx_3761_, v_fvarId_3762_);
if (lean_obj_tag(v___x_3775_) == 0)
{
lean_object* v___x_3776_; 
lean_dec_ref(v_lctx_3761_);
v___x_3776_ = lean_box(0);
return v___x_3776_;
}
else
{
lean_object* v_val_3777_; lean_object* v___y_3779_; lean_object* v_userName_3784_; 
v_val_3777_ = lean_ctor_get(v___x_3775_, 0);
lean_inc(v_val_3777_);
lean_dec_ref_known(v___x_3775_, 1);
v_userName_3784_ = lean_ctor_get(v_val_3777_, 2);
lean_inc(v_userName_3784_);
v___y_3779_ = v_userName_3784_;
goto v___jp_3778_;
v___jp_3778_:
{
lean_object* v___x_3780_; 
v___x_3780_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_3761_, v___y_3779_);
lean_dec_ref(v_lctx_3761_);
if (lean_obj_tag(v___x_3780_) == 0)
{
lean_object* v___x_3781_; 
lean_dec(v___y_3779_);
lean_dec(v_val_3777_);
v___x_3781_ = lean_box(0);
return v___x_3781_;
}
else
{
lean_object* v_val_3782_; lean_object* v_fvarId_3783_; 
v_val_3782_ = lean_ctor_get(v___x_3780_, 0);
lean_inc(v_val_3782_);
lean_dec_ref_known(v___x_3780_, 1);
v_fvarId_3783_ = lean_ctor_get(v_val_3777_, 1);
lean_inc(v_fvarId_3783_);
lean_dec(v_val_3777_);
v___y_3771_ = v___y_3779_;
v___y_3772_ = v_val_3782_;
v___y_3773_ = v_fvarId_3783_;
goto v___jp_3770_;
}
}
}
v___jp_3763_:
{
uint8_t v___x_3767_; 
v___x_3767_ = l_Lean_instBEqFVarId_beq(v___y_3765_, v___y_3766_);
lean_dec(v___y_3766_);
lean_dec(v___y_3765_);
if (v___x_3767_ == 0)
{
lean_object* v___x_3768_; 
lean_dec(v___y_3764_);
v___x_3768_ = lean_box(0);
return v___x_3768_;
}
else
{
lean_object* v___x_3769_; 
v___x_3769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3769_, 0, v___y_3764_);
return v___x_3769_;
}
}
v___jp_3770_:
{
lean_object* v_fvarId_3774_; 
v_fvarId_3774_ = lean_ctor_get(v___y_3772_, 1);
lean_inc(v_fvarId_3774_);
lean_dec_ref(v___y_3772_);
v___y_3764_ = v___y_3771_;
v___y_3765_ = v___y_3773_;
v___y_3766_ = v_fvarId_3774_;
goto v___jp_3763_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(size_t v_sz_3785_, size_t v_i_3786_, lean_object* v_bs_3787_){
_start:
{
uint8_t v___x_3788_; 
v___x_3788_ = lean_usize_dec_lt(v_i_3786_, v_sz_3785_);
if (v___x_3788_ == 0)
{
return v_bs_3787_;
}
else
{
lean_object* v_v_3789_; lean_object* v_snd_3790_; lean_object* v___x_3791_; lean_object* v_bs_x27_3792_; size_t v___x_3793_; size_t v___x_3794_; lean_object* v___x_3795_; 
v_v_3789_ = lean_array_uget_borrowed(v_bs_3787_, v_i_3786_);
v_snd_3790_ = lean_ctor_get(v_v_3789_, 1);
lean_inc(v_snd_3790_);
v___x_3791_ = lean_unsigned_to_nat(0u);
v_bs_x27_3792_ = lean_array_uset(v_bs_3787_, v_i_3786_, v___x_3791_);
v___x_3793_ = ((size_t)1ULL);
v___x_3794_ = lean_usize_add(v_i_3786_, v___x_3793_);
v___x_3795_ = lean_array_uset(v_bs_x27_3792_, v_i_3786_, v_snd_3790_);
v_i_3786_ = v___x_3794_;
v_bs_3787_ = v___x_3795_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0___boxed(lean_object* v_sz_3797_, lean_object* v_i_3798_, lean_object* v_bs_3799_){
_start:
{
size_t v_sz_boxed_3800_; size_t v_i_boxed_3801_; lean_object* v_res_3802_; 
v_sz_boxed_3800_ = lean_unbox_usize(v_sz_3797_);
lean_dec(v_sz_3797_);
v_i_boxed_3801_ = lean_unbox_usize(v_i_3798_);
lean_dec(v_i_3798_);
v_res_3802_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(v_sz_boxed_3800_, v_i_boxed_3801_, v_bs_3799_);
return v_res_3802_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(lean_object* v_lctx_3803_, size_t v_sz_3804_, size_t v_i_3805_, lean_object* v_bs_3806_){
_start:
{
uint8_t v___x_3807_; 
v___x_3807_ = lean_usize_dec_lt(v_i_3805_, v_sz_3804_);
if (v___x_3807_ == 0)
{
return v_bs_3806_;
}
else
{
lean_object* v_fvarIdToDecl_3808_; lean_object* v_v_3809_; lean_object* v___x_3810_; lean_object* v_bs_x27_3811_; lean_object* v___y_3813_; lean_object* v___x_3818_; 
v_fvarIdToDecl_3808_ = lean_ctor_get(v_lctx_3803_, 0);
v_v_3809_ = lean_array_uget(v_bs_3806_, v_i_3805_);
v___x_3810_ = lean_unsigned_to_nat(0u);
v_bs_x27_3811_ = lean_array_uset(v_bs_3806_, v_i_3805_, v___x_3810_);
v___x_3818_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_fvarIdToDecl_3808_, v_v_3809_);
if (lean_obj_tag(v___x_3818_) == 0)
{
lean_object* v___x_3819_; 
v___x_3819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3819_, 0, v___x_3810_);
lean_ctor_set(v___x_3819_, 1, v_v_3809_);
v___y_3813_ = v___x_3819_;
goto v___jp_3812_;
}
else
{
lean_object* v_val_3820_; lean_object* v_index_3821_; lean_object* v___x_3822_; 
v_val_3820_ = lean_ctor_get(v___x_3818_, 0);
lean_inc(v_val_3820_);
lean_dec_ref_known(v___x_3818_, 1);
v_index_3821_ = lean_ctor_get(v_val_3820_, 0);
lean_inc(v_index_3821_);
lean_dec(v_val_3820_);
v___x_3822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3822_, 0, v_index_3821_);
lean_ctor_set(v___x_3822_, 1, v_v_3809_);
v___y_3813_ = v___x_3822_;
goto v___jp_3812_;
}
v___jp_3812_:
{
size_t v___x_3814_; size_t v___x_3815_; lean_object* v___x_3816_; 
v___x_3814_ = ((size_t)1ULL);
v___x_3815_ = lean_usize_add(v_i_3805_, v___x_3814_);
v___x_3816_ = lean_array_uset(v_bs_x27_3811_, v_i_3805_, v___y_3813_);
v_i_3805_ = v___x_3815_;
v_bs_3806_ = v___x_3816_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1___boxed(lean_object* v_lctx_3823_, lean_object* v_sz_3824_, lean_object* v_i_3825_, lean_object* v_bs_3826_){
_start:
{
size_t v_sz_boxed_3827_; size_t v_i_boxed_3828_; lean_object* v_res_3829_; 
v_sz_boxed_3827_ = lean_unbox_usize(v_sz_3824_);
lean_dec(v_sz_3824_);
v_i_boxed_3828_ = lean_unbox_usize(v_i_3825_);
lean_dec(v_i_3825_);
v_res_3829_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(v_lctx_3823_, v_sz_boxed_3827_, v_i_boxed_3828_, v_bs_3826_);
lean_dec_ref(v_lctx_3823_);
return v_res_3829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(lean_object* v_hi_3830_, lean_object* v_pivot_3831_, lean_object* v_as_3832_, lean_object* v_i_3833_, lean_object* v_k_3834_){
_start:
{
uint8_t v___x_3835_; 
v___x_3835_ = lean_nat_dec_lt(v_k_3834_, v_hi_3830_);
if (v___x_3835_ == 0)
{
lean_object* v___x_3836_; lean_object* v___x_3837_; 
lean_dec(v_k_3834_);
v___x_3836_ = lean_array_fswap(v_as_3832_, v_i_3833_, v_hi_3830_);
v___x_3837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3837_, 0, v_i_3833_);
lean_ctor_set(v___x_3837_, 1, v___x_3836_);
return v___x_3837_;
}
else
{
lean_object* v___x_3838_; lean_object* v_fst_3839_; lean_object* v_fst_3840_; uint8_t v___x_3841_; 
v___x_3838_ = lean_array_fget_borrowed(v_as_3832_, v_k_3834_);
v_fst_3839_ = lean_ctor_get(v___x_3838_, 0);
v_fst_3840_ = lean_ctor_get(v_pivot_3831_, 0);
v___x_3841_ = lean_nat_dec_lt(v_fst_3839_, v_fst_3840_);
if (v___x_3841_ == 0)
{
lean_object* v___x_3842_; lean_object* v___x_3843_; 
v___x_3842_ = lean_unsigned_to_nat(1u);
v___x_3843_ = lean_nat_add(v_k_3834_, v___x_3842_);
lean_dec(v_k_3834_);
v_k_3834_ = v___x_3843_;
goto _start;
}
else
{
lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; 
v___x_3845_ = lean_array_fswap(v_as_3832_, v_i_3833_, v_k_3834_);
v___x_3846_ = lean_unsigned_to_nat(1u);
v___x_3847_ = lean_nat_add(v_i_3833_, v___x_3846_);
lean_dec(v_i_3833_);
v___x_3848_ = lean_nat_add(v_k_3834_, v___x_3846_);
lean_dec(v_k_3834_);
v_as_3832_ = v___x_3845_;
v_i_3833_ = v___x_3847_;
v_k_3834_ = v___x_3848_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg___boxed(lean_object* v_hi_3850_, lean_object* v_pivot_3851_, lean_object* v_as_3852_, lean_object* v_i_3853_, lean_object* v_k_3854_){
_start:
{
lean_object* v_res_3855_; 
v_res_3855_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(v_hi_3850_, v_pivot_3851_, v_as_3852_, v_i_3853_, v_k_3854_);
lean_dec_ref(v_pivot_3851_);
lean_dec(v_hi_3850_);
return v_res_3855_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(lean_object* v_h_3856_, lean_object* v_i_3857_){
_start:
{
lean_object* v_fst_3858_; lean_object* v_fst_3859_; uint8_t v___x_3860_; 
v_fst_3858_ = lean_ctor_get(v_h_3856_, 0);
v_fst_3859_ = lean_ctor_get(v_i_3857_, 0);
v___x_3860_ = lean_nat_dec_lt(v_fst_3858_, v_fst_3859_);
return v___x_3860_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0___boxed(lean_object* v_h_3861_, lean_object* v_i_3862_){
_start:
{
uint8_t v_res_3863_; lean_object* v_r_3864_; 
v_res_3863_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v_h_3861_, v_i_3862_);
lean_dec_ref(v_i_3862_);
lean_dec_ref(v_h_3861_);
v_r_3864_ = lean_box(v_res_3863_);
return v_r_3864_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(lean_object* v_n_3865_, lean_object* v_as_3866_, lean_object* v_lo_3867_, lean_object* v_hi_3868_){
_start:
{
lean_object* v___y_3870_; uint8_t v___x_3880_; 
v___x_3880_ = lean_nat_dec_lt(v_lo_3867_, v_hi_3868_);
if (v___x_3880_ == 0)
{
lean_dec(v_lo_3867_);
return v_as_3866_;
}
else
{
lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v_mid_3883_; lean_object* v___y_3885_; lean_object* v___y_3891_; lean_object* v___x_3896_; lean_object* v___x_3897_; uint8_t v___x_3898_; 
v___x_3881_ = lean_nat_add(v_lo_3867_, v_hi_3868_);
v___x_3882_ = lean_unsigned_to_nat(1u);
v_mid_3883_ = lean_nat_shiftr(v___x_3881_, v___x_3882_);
lean_dec(v___x_3881_);
v___x_3896_ = lean_array_fget_borrowed(v_as_3866_, v_mid_3883_);
v___x_3897_ = lean_array_fget_borrowed(v_as_3866_, v_lo_3867_);
v___x_3898_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v___x_3896_, v___x_3897_);
if (v___x_3898_ == 0)
{
v___y_3891_ = v_as_3866_;
goto v___jp_3890_;
}
else
{
lean_object* v___x_3899_; 
v___x_3899_ = lean_array_fswap(v_as_3866_, v_lo_3867_, v_mid_3883_);
v___y_3891_ = v___x_3899_;
goto v___jp_3890_;
}
v___jp_3884_:
{
lean_object* v___x_3886_; lean_object* v___x_3887_; uint8_t v___x_3888_; 
v___x_3886_ = lean_array_fget_borrowed(v___y_3885_, v_mid_3883_);
v___x_3887_ = lean_array_fget_borrowed(v___y_3885_, v_hi_3868_);
v___x_3888_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v___x_3886_, v___x_3887_);
if (v___x_3888_ == 0)
{
lean_dec(v_mid_3883_);
v___y_3870_ = v___y_3885_;
goto v___jp_3869_;
}
else
{
lean_object* v___x_3889_; 
v___x_3889_ = lean_array_fswap(v___y_3885_, v_mid_3883_, v_hi_3868_);
lean_dec(v_mid_3883_);
v___y_3870_ = v___x_3889_;
goto v___jp_3869_;
}
}
v___jp_3890_:
{
lean_object* v___x_3892_; lean_object* v___x_3893_; uint8_t v___x_3894_; 
v___x_3892_ = lean_array_fget_borrowed(v___y_3891_, v_hi_3868_);
v___x_3893_ = lean_array_fget_borrowed(v___y_3891_, v_lo_3867_);
v___x_3894_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v___x_3892_, v___x_3893_);
if (v___x_3894_ == 0)
{
v___y_3885_ = v___y_3891_;
goto v___jp_3884_;
}
else
{
lean_object* v___x_3895_; 
v___x_3895_ = lean_array_fswap(v___y_3891_, v_lo_3867_, v_hi_3868_);
v___y_3885_ = v___x_3895_;
goto v___jp_3884_;
}
}
}
v___jp_3869_:
{
lean_object* v_pivot_3871_; lean_object* v___x_3872_; lean_object* v_fst_3873_; lean_object* v_snd_3874_; uint8_t v___x_3875_; 
v_pivot_3871_ = lean_array_fget(v___y_3870_, v_hi_3868_);
lean_inc_n(v_lo_3867_, 2);
v___x_3872_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(v_hi_3868_, v_pivot_3871_, v___y_3870_, v_lo_3867_, v_lo_3867_);
lean_dec(v_pivot_3871_);
v_fst_3873_ = lean_ctor_get(v___x_3872_, 0);
lean_inc(v_fst_3873_);
v_snd_3874_ = lean_ctor_get(v___x_3872_, 1);
lean_inc(v_snd_3874_);
lean_dec_ref(v___x_3872_);
v___x_3875_ = lean_nat_dec_le(v_hi_3868_, v_fst_3873_);
if (v___x_3875_ == 0)
{
lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; 
v___x_3876_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v_n_3865_, v_snd_3874_, v_lo_3867_, v_fst_3873_);
v___x_3877_ = lean_unsigned_to_nat(1u);
v___x_3878_ = lean_nat_add(v_fst_3873_, v___x_3877_);
lean_dec(v_fst_3873_);
v_as_3866_ = v___x_3876_;
v_lo_3867_ = v___x_3878_;
goto _start;
}
else
{
lean_dec(v_fst_3873_);
lean_dec(v_lo_3867_);
return v_snd_3874_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___boxed(lean_object* v_n_3900_, lean_object* v_as_3901_, lean_object* v_lo_3902_, lean_object* v_hi_3903_){
_start:
{
lean_object* v_res_3904_; 
v_res_3904_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v_n_3900_, v_as_3901_, v_lo_3902_, v_hi_3903_);
lean_dec(v_hi_3903_);
lean_dec(v_n_3900_);
return v_res_3904_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_sortFVarsByContextOrder(lean_object* v_lctx_3905_, lean_object* v_hyps_3906_){
_start:
{
lean_object* v___y_3908_; size_t v_sz_3912_; size_t v___x_3913_; lean_object* v_hyps_3914_; lean_object* v___x_3915_; lean_object* v___y_3917_; lean_object* v___y_3918_; lean_object* v___x_3920_; uint8_t v___x_3921_; 
v_sz_3912_ = lean_array_size(v_hyps_3906_);
v___x_3913_ = ((size_t)0ULL);
v_hyps_3914_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(v_lctx_3905_, v_sz_3912_, v___x_3913_, v_hyps_3906_);
v___x_3915_ = lean_array_get_size(v_hyps_3914_);
v___x_3920_ = lean_unsigned_to_nat(0u);
v___x_3921_ = lean_nat_dec_eq(v___x_3915_, v___x_3920_);
if (v___x_3921_ == 0)
{
lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___y_3925_; uint8_t v___x_3927_; 
v___x_3922_ = lean_unsigned_to_nat(1u);
v___x_3923_ = lean_nat_sub(v___x_3915_, v___x_3922_);
v___x_3927_ = lean_nat_dec_le(v___x_3920_, v___x_3923_);
if (v___x_3927_ == 0)
{
lean_inc(v___x_3923_);
v___y_3925_ = v___x_3923_;
goto v___jp_3924_;
}
else
{
v___y_3925_ = v___x_3920_;
goto v___jp_3924_;
}
v___jp_3924_:
{
uint8_t v___x_3926_; 
v___x_3926_ = lean_nat_dec_le(v___y_3925_, v___x_3923_);
if (v___x_3926_ == 0)
{
lean_dec(v___x_3923_);
lean_inc(v___y_3925_);
v___y_3917_ = v___y_3925_;
v___y_3918_ = v___y_3925_;
goto v___jp_3916_;
}
else
{
v___y_3917_ = v___y_3925_;
v___y_3918_ = v___x_3923_;
goto v___jp_3916_;
}
}
}
else
{
v___y_3908_ = v_hyps_3914_;
goto v___jp_3907_;
}
v___jp_3907_:
{
size_t v_sz_3909_; size_t v___x_3910_; lean_object* v___x_3911_; 
v_sz_3909_ = lean_array_size(v___y_3908_);
v___x_3910_ = ((size_t)0ULL);
v___x_3911_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(v_sz_3909_, v___x_3910_, v___y_3908_);
return v___x_3911_;
}
v___jp_3916_:
{
lean_object* v___x_3919_; 
v___x_3919_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v___x_3915_, v_hyps_3914_, v___y_3917_, v___y_3918_);
lean_dec(v___y_3918_);
v___y_3908_ = v___x_3919_;
goto v___jp_3907_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_sortFVarsByContextOrder___boxed(lean_object* v_lctx_3928_, lean_object* v_hyps_3929_){
_start:
{
lean_object* v_res_3930_; 
v_res_3930_ = l_Lean_LocalContext_sortFVarsByContextOrder(v_lctx_3928_, v_hyps_3929_);
lean_dec_ref(v_lctx_3928_);
return v_res_3930_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2(lean_object* v_n_3931_, lean_object* v_as_3932_, lean_object* v_lo_3933_, lean_object* v_hi_3934_, lean_object* v_w_3935_, lean_object* v_hlo_3936_, lean_object* v_hhi_3937_){
_start:
{
lean_object* v___x_3938_; 
v___x_3938_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v_n_3931_, v_as_3932_, v_lo_3933_, v_hi_3934_);
return v___x_3938_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___boxed(lean_object* v_n_3939_, lean_object* v_as_3940_, lean_object* v_lo_3941_, lean_object* v_hi_3942_, lean_object* v_w_3943_, lean_object* v_hlo_3944_, lean_object* v_hhi_3945_){
_start:
{
lean_object* v_res_3946_; 
v_res_3946_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2(v_n_3939_, v_as_3940_, v_lo_3941_, v_hi_3942_, v_w_3943_, v_hlo_3944_, v_hhi_3945_);
lean_dec(v_hi_3942_);
lean_dec(v_n_3939_);
return v_res_3946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2(lean_object* v_n_3947_, lean_object* v_lo_3948_, lean_object* v_hi_3949_, lean_object* v_hhi_3950_, lean_object* v_pivot_3951_, lean_object* v_as_3952_, lean_object* v_i_3953_, lean_object* v_k_3954_, lean_object* v_ilo_3955_, lean_object* v_ik_3956_, lean_object* v_w_3957_){
_start:
{
lean_object* v___x_3958_; 
v___x_3958_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(v_hi_3949_, v_pivot_3951_, v_as_3952_, v_i_3953_, v_k_3954_);
return v___x_3958_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___boxed(lean_object* v_n_3959_, lean_object* v_lo_3960_, lean_object* v_hi_3961_, lean_object* v_hhi_3962_, lean_object* v_pivot_3963_, lean_object* v_as_3964_, lean_object* v_i_3965_, lean_object* v_k_3966_, lean_object* v_ilo_3967_, lean_object* v_ik_3968_, lean_object* v_w_3969_){
_start:
{
lean_object* v_res_3970_; 
v_res_3970_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2(v_n_3959_, v_lo_3960_, v_hi_3961_, v_hhi_3962_, v_pivot_3963_, v_as_3964_, v_i_3965_, v_k_3966_, v_ilo_3967_, v_ik_3968_, v_w_3969_);
lean_dec_ref(v_pivot_3963_);
lean_dec(v_hi_3961_);
lean_dec(v_lo_3960_);
lean_dec(v_n_3959_);
return v_res_3970_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(lean_object* v_a_3971_, lean_object* v_x_3972_){
_start:
{
if (lean_obj_tag(v_x_3972_) == 0)
{
uint8_t v___x_3973_; 
v___x_3973_ = 0;
return v___x_3973_;
}
else
{
lean_object* v_key_3974_; lean_object* v_tail_3975_; uint8_t v___x_3976_; 
v_key_3974_ = lean_ctor_get(v_x_3972_, 0);
v_tail_3975_ = lean_ctor_get(v_x_3972_, 2);
v___x_3976_ = lean_name_eq(v_key_3974_, v_a_3971_);
if (v___x_3976_ == 0)
{
v_x_3972_ = v_tail_3975_;
goto _start;
}
else
{
return v___x_3976_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg___boxed(lean_object* v_a_3978_, lean_object* v_x_3979_){
_start:
{
uint8_t v_res_3980_; lean_object* v_r_3981_; 
v_res_3980_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_3978_, v_x_3979_);
lean_dec(v_x_3979_);
lean_dec(v_a_3978_);
v_r_3981_ = lean_box(v_res_3980_);
return v_r_3981_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(lean_object* v_a_3982_, lean_object* v_x_3983_){
_start:
{
if (lean_obj_tag(v_x_3983_) == 0)
{
return v_x_3983_;
}
else
{
lean_object* v_key_3984_; lean_object* v_value_3985_; lean_object* v_tail_3986_; lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_3995_; 
v_key_3984_ = lean_ctor_get(v_x_3983_, 0);
v_value_3985_ = lean_ctor_get(v_x_3983_, 1);
v_tail_3986_ = lean_ctor_get(v_x_3983_, 2);
v_isSharedCheck_3995_ = !lean_is_exclusive(v_x_3983_);
if (v_isSharedCheck_3995_ == 0)
{
v___x_3988_ = v_x_3983_;
v_isShared_3989_ = v_isSharedCheck_3995_;
goto v_resetjp_3987_;
}
else
{
lean_inc(v_tail_3986_);
lean_inc(v_value_3985_);
lean_inc(v_key_3984_);
lean_dec(v_x_3983_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_3995_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
uint8_t v___x_3990_; 
v___x_3990_ = lean_name_eq(v_key_3984_, v_a_3982_);
if (v___x_3990_ == 0)
{
lean_object* v___x_3991_; lean_object* v___x_3993_; 
v___x_3991_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_3982_, v_tail_3986_);
if (v_isShared_3989_ == 0)
{
lean_ctor_set(v___x_3988_, 2, v___x_3991_);
v___x_3993_ = v___x_3988_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v_key_3984_);
lean_ctor_set(v_reuseFailAlloc_3994_, 1, v_value_3985_);
lean_ctor_set(v_reuseFailAlloc_3994_, 2, v___x_3991_);
v___x_3993_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
return v___x_3993_;
}
}
else
{
lean_del_object(v___x_3988_);
lean_dec(v_value_3985_);
lean_dec(v_key_3984_);
return v_tail_3986_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg___boxed(lean_object* v_a_3996_, lean_object* v_x_3997_){
_start:
{
lean_object* v_res_3998_; 
v_res_3998_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_3996_, v_x_3997_);
lean_dec(v_a_3996_);
return v_res_3998_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(lean_object* v_m_3999_, lean_object* v_a_4000_){
_start:
{
lean_object* v_size_4001_; lean_object* v_buckets_4002_; lean_object* v___x_4003_; uint64_t v___y_4005_; 
v_size_4001_ = lean_ctor_get(v_m_3999_, 0);
v_buckets_4002_ = lean_ctor_get(v_m_3999_, 1);
v___x_4003_ = lean_array_get_size(v_buckets_4002_);
if (lean_obj_tag(v_a_4000_) == 0)
{
uint64_t v___x_4034_; 
v___x_4034_ = 1723ULL;
v___y_4005_ = v___x_4034_;
goto v___jp_4004_;
}
else
{
uint64_t v_hash_4035_; 
v_hash_4035_ = lean_ctor_get_uint64(v_a_4000_, sizeof(void*)*2);
v___y_4005_ = v_hash_4035_;
goto v___jp_4004_;
}
v___jp_4004_:
{
uint64_t v___x_4006_; uint64_t v___x_4007_; uint64_t v_fold_4008_; uint64_t v___x_4009_; uint64_t v___x_4010_; uint64_t v___x_4011_; size_t v___x_4012_; size_t v___x_4013_; size_t v___x_4014_; size_t v___x_4015_; size_t v___x_4016_; lean_object* v_bkt_4017_; uint8_t v___x_4018_; 
v___x_4006_ = 32ULL;
v___x_4007_ = lean_uint64_shift_right(v___y_4005_, v___x_4006_);
v_fold_4008_ = lean_uint64_xor(v___y_4005_, v___x_4007_);
v___x_4009_ = 16ULL;
v___x_4010_ = lean_uint64_shift_right(v_fold_4008_, v___x_4009_);
v___x_4011_ = lean_uint64_xor(v_fold_4008_, v___x_4010_);
v___x_4012_ = lean_uint64_to_usize(v___x_4011_);
v___x_4013_ = lean_usize_of_nat(v___x_4003_);
v___x_4014_ = ((size_t)1ULL);
v___x_4015_ = lean_usize_sub(v___x_4013_, v___x_4014_);
v___x_4016_ = lean_usize_land(v___x_4012_, v___x_4015_);
v_bkt_4017_ = lean_array_uget_borrowed(v_buckets_4002_, v___x_4016_);
v___x_4018_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_4000_, v_bkt_4017_);
if (v___x_4018_ == 0)
{
return v_m_3999_;
}
else
{
lean_object* v___x_4020_; uint8_t v_isShared_4021_; uint8_t v_isSharedCheck_4031_; 
lean_inc(v_bkt_4017_);
lean_inc_ref(v_buckets_4002_);
lean_inc(v_size_4001_);
v_isSharedCheck_4031_ = !lean_is_exclusive(v_m_3999_);
if (v_isSharedCheck_4031_ == 0)
{
lean_object* v_unused_4032_; lean_object* v_unused_4033_; 
v_unused_4032_ = lean_ctor_get(v_m_3999_, 1);
lean_dec(v_unused_4032_);
v_unused_4033_ = lean_ctor_get(v_m_3999_, 0);
lean_dec(v_unused_4033_);
v___x_4020_ = v_m_3999_;
v_isShared_4021_ = v_isSharedCheck_4031_;
goto v_resetjp_4019_;
}
else
{
lean_dec(v_m_3999_);
v___x_4020_ = lean_box(0);
v_isShared_4021_ = v_isSharedCheck_4031_;
goto v_resetjp_4019_;
}
v_resetjp_4019_:
{
lean_object* v___x_4022_; lean_object* v_buckets_x27_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4029_; 
v___x_4022_ = lean_box(0);
v_buckets_x27_4023_ = lean_array_uset(v_buckets_4002_, v___x_4016_, v___x_4022_);
v___x_4024_ = lean_unsigned_to_nat(1u);
v___x_4025_ = lean_nat_sub(v_size_4001_, v___x_4024_);
lean_dec(v_size_4001_);
v___x_4026_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_4000_, v_bkt_4017_);
v___x_4027_ = lean_array_uset(v_buckets_x27_4023_, v___x_4016_, v___x_4026_);
if (v_isShared_4021_ == 0)
{
lean_ctor_set(v___x_4020_, 1, v___x_4027_);
lean_ctor_set(v___x_4020_, 0, v___x_4025_);
v___x_4029_ = v___x_4020_;
goto v_reusejp_4028_;
}
else
{
lean_object* v_reuseFailAlloc_4030_; 
v_reuseFailAlloc_4030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4030_, 0, v___x_4025_);
lean_ctor_set(v_reuseFailAlloc_4030_, 1, v___x_4027_);
v___x_4029_ = v_reuseFailAlloc_4030_;
goto v_reusejp_4028_;
}
v_reusejp_4028_:
{
return v___x_4029_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___boxed(lean_object* v_m_4036_, lean_object* v_a_4037_){
_start:
{
lean_object* v_res_4038_; 
v_res_4038_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_m_4036_, v_a_4037_);
lean_dec(v_a_4037_);
return v_res_4038_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(lean_object* v_m_4039_, lean_object* v_a_4040_){
_start:
{
lean_object* v_buckets_4041_; lean_object* v___x_4042_; uint64_t v___y_4044_; 
v_buckets_4041_ = lean_ctor_get(v_m_4039_, 1);
v___x_4042_ = lean_array_get_size(v_buckets_4041_);
if (lean_obj_tag(v_a_4040_) == 0)
{
uint64_t v___x_4058_; 
v___x_4058_ = 1723ULL;
v___y_4044_ = v___x_4058_;
goto v___jp_4043_;
}
else
{
uint64_t v_hash_4059_; 
v_hash_4059_ = lean_ctor_get_uint64(v_a_4040_, sizeof(void*)*2);
v___y_4044_ = v_hash_4059_;
goto v___jp_4043_;
}
v___jp_4043_:
{
uint64_t v___x_4045_; uint64_t v___x_4046_; uint64_t v_fold_4047_; uint64_t v___x_4048_; uint64_t v___x_4049_; uint64_t v___x_4050_; size_t v___x_4051_; size_t v___x_4052_; size_t v___x_4053_; size_t v___x_4054_; size_t v___x_4055_; lean_object* v___x_4056_; uint8_t v___x_4057_; 
v___x_4045_ = 32ULL;
v___x_4046_ = lean_uint64_shift_right(v___y_4044_, v___x_4045_);
v_fold_4047_ = lean_uint64_xor(v___y_4044_, v___x_4046_);
v___x_4048_ = 16ULL;
v___x_4049_ = lean_uint64_shift_right(v_fold_4047_, v___x_4048_);
v___x_4050_ = lean_uint64_xor(v_fold_4047_, v___x_4049_);
v___x_4051_ = lean_uint64_to_usize(v___x_4050_);
v___x_4052_ = lean_usize_of_nat(v___x_4042_);
v___x_4053_ = ((size_t)1ULL);
v___x_4054_ = lean_usize_sub(v___x_4052_, v___x_4053_);
v___x_4055_ = lean_usize_land(v___x_4051_, v___x_4054_);
v___x_4056_ = lean_array_uget_borrowed(v_buckets_4041_, v___x_4055_);
v___x_4057_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_4040_, v___x_4056_);
return v___x_4057_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg___boxed(lean_object* v_m_4060_, lean_object* v_a_4061_){
_start:
{
uint8_t v_res_4062_; lean_object* v_r_4063_; 
v_res_4062_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(v_m_4060_, v_a_4061_);
lean_dec(v_a_4061_);
lean_dec_ref(v_m_4060_);
v_r_4063_ = lean_box(v_res_4062_);
return v_r_4063_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(lean_object* v_start_4064_, lean_object* v_as_4065_, size_t v_i_4066_, size_t v_stop_4067_, lean_object* v_b_4068_){
_start:
{
uint8_t v___x_4069_; 
v___x_4069_ = lean_usize_dec_eq(v_i_4066_, v_stop_4067_);
if (v___x_4069_ == 0)
{
size_t v___x_4070_; size_t v___x_4071_; lean_object* v___x_4072_; 
v___x_4070_ = ((size_t)1ULL);
v___x_4071_ = lean_usize_sub(v_i_4066_, v___x_4070_);
v___x_4072_ = lean_array_uget(v_as_4065_, v___x_4071_);
if (lean_obj_tag(v___x_4072_) == 0)
{
v_i_4066_ = v___x_4071_;
goto _start;
}
else
{
lean_object* v_val_4074_; lean_object* v___x_4076_; uint8_t v_isShared_4077_; uint8_t v_isSharedCheck_4108_; 
v_val_4074_ = lean_ctor_get(v___x_4072_, 0);
v_isSharedCheck_4108_ = !lean_is_exclusive(v___x_4072_);
if (v_isSharedCheck_4108_ == 0)
{
v___x_4076_ = v___x_4072_;
v_isShared_4077_ = v_isSharedCheck_4108_;
goto v_resetjp_4075_;
}
else
{
lean_inc(v_val_4074_);
lean_dec(v___x_4072_);
v___x_4076_ = lean_box(0);
v_isShared_4077_ = v_isSharedCheck_4108_;
goto v_resetjp_4075_;
}
v_resetjp_4075_:
{
lean_object* v_fst_4078_; lean_object* v_snd_4079_; lean_object* v___y_4081_; lean_object* v___y_4097_; lean_object* v_size_4103_; lean_object* v___x_4104_; uint8_t v___x_4105_; 
v_fst_4078_ = lean_ctor_get(v_b_4068_, 0);
v_snd_4079_ = lean_ctor_get(v_b_4068_, 1);
v_size_4103_ = lean_ctor_get(v_fst_4078_, 0);
v___x_4104_ = lean_unsigned_to_nat(0u);
v___x_4105_ = lean_nat_dec_eq(v_size_4103_, v___x_4104_);
if (v___x_4105_ == 0)
{
lean_object* v_index_4106_; 
v_index_4106_ = lean_ctor_get(v_val_4074_, 0);
lean_inc(v_index_4106_);
v___y_4097_ = v_index_4106_;
goto v___jp_4096_;
}
else
{
lean_object* v___x_4107_; 
lean_inc(v_snd_4079_);
lean_del_object(v___x_4076_);
lean_dec(v_val_4074_);
lean_dec_ref(v_b_4068_);
v___x_4107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4107_, 0, v_snd_4079_);
return v___x_4107_;
}
v___jp_4080_:
{
uint8_t v___x_4082_; 
v___x_4082_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(v_fst_4078_, v___y_4081_);
if (v___x_4082_ == 0)
{
lean_dec(v___y_4081_);
lean_dec(v_val_4074_);
v_i_4066_ = v___x_4071_;
goto _start;
}
else
{
lean_object* v___x_4085_; uint8_t v_isShared_4086_; uint8_t v_isSharedCheck_4093_; 
lean_inc(v_snd_4079_);
lean_inc(v_fst_4078_);
v_isSharedCheck_4093_ = !lean_is_exclusive(v_b_4068_);
if (v_isSharedCheck_4093_ == 0)
{
lean_object* v_unused_4094_; lean_object* v_unused_4095_; 
v_unused_4094_ = lean_ctor_get(v_b_4068_, 1);
lean_dec(v_unused_4094_);
v_unused_4095_ = lean_ctor_get(v_b_4068_, 0);
lean_dec(v_unused_4095_);
v___x_4085_ = v_b_4068_;
v_isShared_4086_ = v_isSharedCheck_4093_;
goto v_resetjp_4084_;
}
else
{
lean_dec(v_b_4068_);
v___x_4085_ = lean_box(0);
v_isShared_4086_ = v_isSharedCheck_4093_;
goto v_resetjp_4084_;
}
v_resetjp_4084_:
{
lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4090_; 
v___x_4087_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_fst_4078_, v___y_4081_);
lean_dec(v___y_4081_);
v___x_4088_ = lean_array_push(v_snd_4079_, v_val_4074_);
if (v_isShared_4086_ == 0)
{
lean_ctor_set(v___x_4085_, 1, v___x_4088_);
lean_ctor_set(v___x_4085_, 0, v___x_4087_);
v___x_4090_ = v___x_4085_;
goto v_reusejp_4089_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v___x_4087_);
lean_ctor_set(v_reuseFailAlloc_4092_, 1, v___x_4088_);
v___x_4090_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4089_;
}
v_reusejp_4089_:
{
v_i_4066_ = v___x_4071_;
v_b_4068_ = v___x_4090_;
goto _start;
}
}
}
}
v___jp_4096_:
{
uint8_t v___x_4098_; 
v___x_4098_ = lean_nat_dec_lt(v___y_4097_, v_start_4064_);
lean_dec(v___y_4097_);
if (v___x_4098_ == 0)
{
lean_object* v_userName_4099_; 
lean_del_object(v___x_4076_);
v_userName_4099_ = lean_ctor_get(v_val_4074_, 2);
lean_inc(v_userName_4099_);
v___y_4081_ = v_userName_4099_;
goto v___jp_4080_;
}
else
{
lean_object* v___x_4101_; 
lean_inc(v_snd_4079_);
lean_dec(v_val_4074_);
lean_dec_ref(v_b_4068_);
if (v_isShared_4077_ == 0)
{
lean_ctor_set_tag(v___x_4076_, 0);
lean_ctor_set(v___x_4076_, 0, v_snd_4079_);
v___x_4101_ = v___x_4076_;
goto v_reusejp_4100_;
}
else
{
lean_object* v_reuseFailAlloc_4102_; 
v_reuseFailAlloc_4102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4102_, 0, v_snd_4079_);
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
}
}
else
{
lean_object* v___x_4109_; 
v___x_4109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4109_, 0, v_b_4068_);
return v___x_4109_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_start_4110_, lean_object* v_as_4111_, lean_object* v_i_4112_, lean_object* v_stop_4113_, lean_object* v_b_4114_){
_start:
{
size_t v_i_boxed_4115_; size_t v_stop_boxed_4116_; lean_object* v_res_4117_; 
v_i_boxed_4115_ = lean_unbox_usize(v_i_4112_);
lean_dec(v_i_4112_);
v_stop_boxed_4116_ = lean_unbox_usize(v_stop_4113_);
lean_dec(v_stop_4113_);
v_res_4117_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4110_, v_as_4111_, v_i_boxed_4115_, v_stop_boxed_4116_, v_b_4114_);
lean_dec_ref(v_as_4111_);
lean_dec(v_start_4110_);
return v_res_4117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(lean_object* v_start_4118_, lean_object* v_x_4119_, lean_object* v_x_4120_){
_start:
{
if (lean_obj_tag(v_x_4119_) == 0)
{
lean_object* v_cs_4121_; lean_object* v___x_4123_; uint8_t v_isShared_4124_; uint8_t v_isSharedCheck_4134_; 
v_cs_4121_ = lean_ctor_get(v_x_4119_, 0);
v_isSharedCheck_4134_ = !lean_is_exclusive(v_x_4119_);
if (v_isSharedCheck_4134_ == 0)
{
v___x_4123_ = v_x_4119_;
v_isShared_4124_ = v_isSharedCheck_4134_;
goto v_resetjp_4122_;
}
else
{
lean_inc(v_cs_4121_);
lean_dec(v_x_4119_);
v___x_4123_ = lean_box(0);
v_isShared_4124_ = v_isSharedCheck_4134_;
goto v_resetjp_4122_;
}
v_resetjp_4122_:
{
lean_object* v___x_4125_; lean_object* v___x_4126_; uint8_t v___x_4127_; 
v___x_4125_ = lean_array_get_size(v_cs_4121_);
v___x_4126_ = lean_unsigned_to_nat(0u);
v___x_4127_ = lean_nat_dec_lt(v___x_4126_, v___x_4125_);
if (v___x_4127_ == 0)
{
lean_object* v___x_4129_; 
lean_dec_ref(v_cs_4121_);
if (v_isShared_4124_ == 0)
{
lean_ctor_set_tag(v___x_4123_, 1);
lean_ctor_set(v___x_4123_, 0, v_x_4120_);
v___x_4129_ = v___x_4123_;
goto v_reusejp_4128_;
}
else
{
lean_object* v_reuseFailAlloc_4130_; 
v_reuseFailAlloc_4130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4130_, 0, v_x_4120_);
v___x_4129_ = v_reuseFailAlloc_4130_;
goto v_reusejp_4128_;
}
v_reusejp_4128_:
{
return v___x_4129_;
}
}
else
{
size_t v___x_4131_; size_t v___x_4132_; lean_object* v___x_4133_; 
lean_del_object(v___x_4123_);
v___x_4131_ = lean_usize_of_nat(v___x_4125_);
v___x_4132_ = ((size_t)0ULL);
v___x_4133_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(v_start_4118_, v_cs_4121_, v___x_4131_, v___x_4132_, v_x_4120_);
lean_dec_ref(v_cs_4121_);
return v___x_4133_;
}
}
}
else
{
lean_object* v_vs_4135_; lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4148_; 
v_vs_4135_ = lean_ctor_get(v_x_4119_, 0);
v_isSharedCheck_4148_ = !lean_is_exclusive(v_x_4119_);
if (v_isSharedCheck_4148_ == 0)
{
v___x_4137_ = v_x_4119_;
v_isShared_4138_ = v_isSharedCheck_4148_;
goto v_resetjp_4136_;
}
else
{
lean_inc(v_vs_4135_);
lean_dec(v_x_4119_);
v___x_4137_ = lean_box(0);
v_isShared_4138_ = v_isSharedCheck_4148_;
goto v_resetjp_4136_;
}
v_resetjp_4136_:
{
lean_object* v___x_4139_; lean_object* v___x_4140_; uint8_t v___x_4141_; 
v___x_4139_ = lean_array_get_size(v_vs_4135_);
v___x_4140_ = lean_unsigned_to_nat(0u);
v___x_4141_ = lean_nat_dec_lt(v___x_4140_, v___x_4139_);
if (v___x_4141_ == 0)
{
lean_object* v___x_4143_; 
lean_dec_ref(v_vs_4135_);
if (v_isShared_4138_ == 0)
{
lean_ctor_set(v___x_4137_, 0, v_x_4120_);
v___x_4143_ = v___x_4137_;
goto v_reusejp_4142_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v_x_4120_);
v___x_4143_ = v_reuseFailAlloc_4144_;
goto v_reusejp_4142_;
}
v_reusejp_4142_:
{
return v___x_4143_;
}
}
else
{
size_t v___x_4145_; size_t v___x_4146_; lean_object* v___x_4147_; 
lean_del_object(v___x_4137_);
v___x_4145_ = lean_usize_of_nat(v___x_4139_);
v___x_4146_ = ((size_t)0ULL);
v___x_4147_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4118_, v_vs_4135_, v___x_4145_, v___x_4146_, v_x_4120_);
lean_dec_ref(v_vs_4135_);
return v___x_4147_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_start_4149_, lean_object* v_as_4150_, size_t v_i_4151_, size_t v_stop_4152_, lean_object* v_b_4153_){
_start:
{
uint8_t v___x_4154_; 
v___x_4154_ = lean_usize_dec_eq(v_i_4151_, v_stop_4152_);
if (v___x_4154_ == 0)
{
size_t v___x_4155_; size_t v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; 
v___x_4155_ = ((size_t)1ULL);
v___x_4156_ = lean_usize_sub(v_i_4151_, v___x_4155_);
v___x_4157_ = lean_array_uget_borrowed(v_as_4150_, v___x_4156_);
lean_inc(v___x_4157_);
v___x_4158_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4149_, v___x_4157_, v_b_4153_);
if (lean_obj_tag(v___x_4158_) == 0)
{
return v___x_4158_;
}
else
{
lean_object* v_a_4159_; 
v_a_4159_ = lean_ctor_get(v___x_4158_, 0);
lean_inc(v_a_4159_);
lean_dec_ref_known(v___x_4158_, 1);
v_i_4151_ = v___x_4156_;
v_b_4153_ = v_a_4159_;
goto _start;
}
}
else
{
lean_object* v___x_4161_; 
v___x_4161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4161_, 0, v_b_4153_);
return v___x_4161_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_start_4162_, lean_object* v_as_4163_, lean_object* v_i_4164_, lean_object* v_stop_4165_, lean_object* v_b_4166_){
_start:
{
size_t v_i_boxed_4167_; size_t v_stop_boxed_4168_; lean_object* v_res_4169_; 
v_i_boxed_4167_ = lean_unbox_usize(v_i_4164_);
lean_dec(v_i_4164_);
v_stop_boxed_4168_ = lean_unbox_usize(v_stop_4165_);
lean_dec(v_stop_4165_);
v_res_4169_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(v_start_4162_, v_as_4163_, v_i_boxed_4167_, v_stop_boxed_4168_, v_b_4166_);
lean_dec_ref(v_as_4163_);
lean_dec(v_start_4162_);
return v_res_4169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_start_4170_, lean_object* v_x_4171_, lean_object* v_x_4172_){
_start:
{
lean_object* v_res_4173_; 
v_res_4173_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4170_, v_x_4171_, v_x_4172_);
lean_dec(v_start_4170_);
return v_res_4173_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(lean_object* v_start_4174_, lean_object* v_t_4175_, lean_object* v_init_4176_){
_start:
{
lean_object* v_root_4177_; lean_object* v_tail_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; uint8_t v___x_4181_; 
v_root_4177_ = lean_ctor_get(v_t_4175_, 0);
lean_inc_ref(v_root_4177_);
v_tail_4178_ = lean_ctor_get(v_t_4175_, 1);
lean_inc_ref(v_tail_4178_);
lean_dec_ref(v_t_4175_);
v___x_4179_ = lean_array_get_size(v_tail_4178_);
v___x_4180_ = lean_unsigned_to_nat(0u);
v___x_4181_ = lean_nat_dec_lt(v___x_4180_, v___x_4179_);
if (v___x_4181_ == 0)
{
lean_object* v___x_4182_; 
lean_dec_ref(v_tail_4178_);
v___x_4182_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4174_, v_root_4177_, v_init_4176_);
return v___x_4182_;
}
else
{
size_t v___x_4183_; size_t v___x_4184_; lean_object* v___x_4185_; 
v___x_4183_ = lean_usize_of_nat(v___x_4179_);
v___x_4184_ = ((size_t)0ULL);
v___x_4185_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4174_, v_tail_4178_, v___x_4183_, v___x_4184_, v_init_4176_);
lean_dec_ref(v_tail_4178_);
if (lean_obj_tag(v___x_4185_) == 0)
{
lean_dec_ref(v_root_4177_);
return v___x_4185_;
}
else
{
lean_object* v_a_4186_; lean_object* v___x_4187_; 
v_a_4186_ = lean_ctor_get(v___x_4185_, 0);
lean_inc(v_a_4186_);
lean_dec_ref_known(v___x_4185_, 1);
v___x_4187_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4174_, v_root_4177_, v_a_4186_);
return v___x_4187_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg___boxed(lean_object* v_start_4188_, lean_object* v_t_4189_, lean_object* v_init_4190_){
_start:
{
lean_object* v_res_4191_; 
v_res_4191_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(v_start_4188_, v_t_4189_, v_init_4190_);
lean_dec(v_start_4188_);
return v_res_4191_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(lean_object* v_start_4192_, lean_object* v_lctx_4193_, lean_object* v_init_4194_){
_start:
{
lean_object* v_decls_4195_; lean_object* v___x_4196_; 
v_decls_4195_ = lean_ctor_get(v_lctx_4193_, 1);
lean_inc_ref(v_decls_4195_);
lean_dec_ref(v_lctx_4193_);
v___x_4196_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(v_start_4192_, v_decls_4195_, v_init_4194_);
return v___x_4196_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg___boxed(lean_object* v_start_4197_, lean_object* v_lctx_4198_, lean_object* v_init_4199_){
_start:
{
lean_object* v_res_4200_; 
v_res_4200_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(v_start_4197_, v_lctx_4198_, v_init_4199_);
lean_dec(v_start_4197_);
return v_res_4200_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___redArg(lean_object* v_lctx_4203_, lean_object* v_userNames_4204_, lean_object* v_start_4205_){
_start:
{
lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; 
v___x_4206_ = ((lean_object*)(l_Lean_LocalContext_findFromUserNames___redArg___closed__0));
v___x_4207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4207_, 0, v_userNames_4204_);
lean_ctor_set(v___x_4207_, 1, v___x_4206_);
v___x_4208_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(v_start_4205_, v_lctx_4203_, v___x_4207_);
if (lean_obj_tag(v___x_4208_) == 0)
{
lean_object* v_a_4209_; lean_object* v___x_4210_; 
v_a_4209_ = lean_ctor_get(v___x_4208_, 0);
lean_inc(v_a_4209_);
lean_dec_ref_known(v___x_4208_, 1);
v___x_4210_ = l_Array_reverse___redArg(v_a_4209_);
return v___x_4210_;
}
else
{
lean_object* v_a_4211_; lean_object* v_snd_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; 
v_a_4211_ = lean_ctor_get(v___x_4208_, 0);
lean_inc(v_a_4211_);
lean_dec_ref_known(v___x_4208_, 1);
v_snd_4212_ = lean_ctor_get(v_a_4211_, 1);
lean_inc(v_snd_4212_);
lean_dec(v_a_4211_);
v___x_4213_ = l_Array_reverse___redArg(v_snd_4212_);
v___x_4214_ = l_Array_reverse___redArg(v___x_4213_);
return v___x_4214_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___redArg___boxed(lean_object* v_lctx_4215_, lean_object* v_userNames_4216_, lean_object* v_start_4217_){
_start:
{
lean_object* v_res_4218_; 
v_res_4218_ = l_Lean_LocalContext_findFromUserNames___redArg(v_lctx_4215_, v_userNames_4216_, v_start_4217_);
lean_dec(v_start_4217_);
return v_res_4218_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames(lean_object* v_00_u03b1_4219_, lean_object* v_lctx_4220_, lean_object* v_userNames_4221_, lean_object* v_start_4222_){
_start:
{
lean_object* v___x_4223_; 
v___x_4223_ = l_Lean_LocalContext_findFromUserNames___redArg(v_lctx_4220_, v_userNames_4221_, v_start_4222_);
return v___x_4223_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___boxed(lean_object* v_00_u03b1_4224_, lean_object* v_lctx_4225_, lean_object* v_userNames_4226_, lean_object* v_start_4227_){
_start:
{
lean_object* v_res_4228_; 
v_res_4228_ = l_Lean_LocalContext_findFromUserNames(v_00_u03b1_4224_, v_lctx_4225_, v_userNames_4226_, v_start_4227_);
lean_dec(v_start_4227_);
return v_res_4228_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0(lean_object* v_00_u03b2_4229_, lean_object* v_m_4230_, lean_object* v_a_4231_){
_start:
{
uint8_t v___x_4232_; 
v___x_4232_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(v_m_4230_, v_a_4231_);
return v___x_4232_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___boxed(lean_object* v_00_u03b2_4233_, lean_object* v_m_4234_, lean_object* v_a_4235_){
_start:
{
uint8_t v_res_4236_; lean_object* v_r_4237_; 
v_res_4236_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0(v_00_u03b2_4233_, v_m_4234_, v_a_4235_);
lean_dec(v_a_4235_);
lean_dec_ref(v_m_4234_);
v_r_4237_ = lean_box(v_res_4236_);
return v_r_4237_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1(lean_object* v_00_u03b2_4238_, lean_object* v_m_4239_, lean_object* v_a_4240_){
_start:
{
lean_object* v___x_4241_; 
v___x_4241_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_m_4239_, v_a_4240_);
return v___x_4241_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___boxed(lean_object* v_00_u03b2_4242_, lean_object* v_m_4243_, lean_object* v_a_4244_){
_start:
{
lean_object* v_res_4245_; 
v_res_4245_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1(v_00_u03b2_4242_, v_m_4243_, v_a_4244_);
lean_dec(v_a_4244_);
return v_res_4245_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2(lean_object* v_00_u03b1_4246_, lean_object* v_start_4247_, lean_object* v_lctx_4248_, lean_object* v_init_4249_){
_start:
{
lean_object* v___x_4250_; 
v___x_4250_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(v_start_4247_, v_lctx_4248_, v_init_4249_);
return v___x_4250_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___boxed(lean_object* v_00_u03b1_4251_, lean_object* v_start_4252_, lean_object* v_lctx_4253_, lean_object* v_init_4254_){
_start:
{
lean_object* v_res_4255_; 
v_res_4255_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2(v_00_u03b1_4251_, v_start_4252_, v_lctx_4253_, v_init_4254_);
lean_dec(v_start_4252_);
return v_res_4255_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0(lean_object* v_00_u03b2_4256_, lean_object* v_a_4257_, lean_object* v_x_4258_){
_start:
{
uint8_t v___x_4259_; 
v___x_4259_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_4257_, v_x_4258_);
return v___x_4259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4260_, lean_object* v_a_4261_, lean_object* v_x_4262_){
_start:
{
uint8_t v_res_4263_; lean_object* v_r_4264_; 
v_res_4263_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0(v_00_u03b2_4260_, v_a_4261_, v_x_4262_);
lean_dec(v_x_4262_);
lean_dec(v_a_4261_);
v_r_4264_ = lean_box(v_res_4263_);
return v_r_4264_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2(lean_object* v_00_u03b2_4265_, lean_object* v_a_4266_, lean_object* v_x_4267_){
_start:
{
lean_object* v___x_4268_; 
v___x_4268_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_4266_, v_x_4267_);
return v___x_4268_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4269_, lean_object* v_a_4270_, lean_object* v_x_4271_){
_start:
{
lean_object* v_res_4272_; 
v_res_4272_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2(v_00_u03b2_4269_, v_a_4270_, v_x_4271_);
lean_dec(v_a_4270_);
return v_res_4272_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4(lean_object* v_00_u03b1_4273_, lean_object* v_start_4274_, lean_object* v_t_4275_, lean_object* v_init_4276_){
_start:
{
lean_object* v___x_4277_; 
v___x_4277_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(v_start_4274_, v_t_4275_, v_init_4276_);
return v___x_4277_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___boxed(lean_object* v_00_u03b1_4278_, lean_object* v_start_4279_, lean_object* v_t_4280_, lean_object* v_init_4281_){
_start:
{
lean_object* v_res_4282_; 
v_res_4282_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4(v_00_u03b1_4278_, v_start_4279_, v_t_4280_, v_init_4281_);
lean_dec(v_start_4279_);
return v_res_4282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5(lean_object* v_00_u03b1_4283_, lean_object* v_start_4284_, lean_object* v_x_4285_, lean_object* v_x_4286_){
_start:
{
lean_object* v___x_4287_; 
v___x_4287_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4284_, v_x_4285_, v_x_4286_);
return v___x_4287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b1_4288_, lean_object* v_start_4289_, lean_object* v_x_4290_, lean_object* v_x_4291_){
_start:
{
lean_object* v_res_4292_; 
v_res_4292_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5(v_00_u03b1_4288_, v_start_4289_, v_x_4290_, v_x_4291_);
lean_dec(v_start_4289_);
return v_res_4292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_4293_, lean_object* v_start_4294_, lean_object* v_as_4295_, size_t v_i_4296_, size_t v_stop_4297_, lean_object* v_b_4298_){
_start:
{
lean_object* v___x_4299_; 
v___x_4299_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4294_, v_as_4295_, v_i_4296_, v_stop_4297_, v_b_4298_);
return v___x_4299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_4300_, lean_object* v_start_4301_, lean_object* v_as_4302_, lean_object* v_i_4303_, lean_object* v_stop_4304_, lean_object* v_b_4305_){
_start:
{
size_t v_i_boxed_4306_; size_t v_stop_boxed_4307_; lean_object* v_res_4308_; 
v_i_boxed_4306_ = lean_unbox_usize(v_i_4303_);
lean_dec(v_i_4303_);
v_stop_boxed_4307_ = lean_unbox_usize(v_stop_4304_);
lean_dec(v_stop_4304_);
v_res_4308_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6(v_00_u03b1_4300_, v_start_4301_, v_as_4302_, v_i_boxed_4306_, v_stop_boxed_4307_, v_b_4305_);
lean_dec_ref(v_as_4302_);
lean_dec(v_start_4301_);
return v_res_4308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b1_4309_, lean_object* v_start_4310_, lean_object* v_as_4311_, size_t v_i_4312_, size_t v_stop_4313_, lean_object* v_b_4314_){
_start:
{
lean_object* v___x_4315_; 
v___x_4315_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(v_start_4310_, v_as_4311_, v_i_4312_, v_stop_4313_, v_b_4314_);
return v___x_4315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___boxed(lean_object* v_00_u03b1_4316_, lean_object* v_start_4317_, lean_object* v_as_4318_, lean_object* v_i_4319_, lean_object* v_stop_4320_, lean_object* v_b_4321_){
_start:
{
size_t v_i_boxed_4322_; size_t v_stop_boxed_4323_; lean_object* v_res_4324_; 
v_i_boxed_4322_ = lean_unbox_usize(v_i_4319_);
lean_dec(v_i_4319_);
v_stop_boxed_4323_ = lean_unbox_usize(v_stop_4320_);
lean_dec(v_stop_4320_);
v_res_4324_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6(v_00_u03b1_4316_, v_start_4317_, v_as_4318_, v_i_boxed_4322_, v_stop_boxed_4323_, v_b_4321_);
lean_dec_ref(v_as_4318_);
lean_dec(v_start_4317_);
return v_res_4324_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLCtxOfMonadLift___redArg(lean_object* v_inst_4325_, lean_object* v_inst_4326_){
_start:
{
lean_object* v___x_4327_; 
v___x_4327_ = lean_apply_2(v_inst_4325_, lean_box(0), v_inst_4326_);
return v___x_4327_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLCtxOfMonadLift(lean_object* v_m_4328_, lean_object* v_n_4329_, lean_object* v_inst_4330_, lean_object* v_inst_4331_){
_start:
{
lean_object* v___x_4332_; 
v___x_4332_ = lean_apply_2(v_inst_4330_, lean_box(0), v_inst_4331_);
return v___x_4332_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__0(lean_object* v_toPure_4333_, lean_object* v_d_x3f_4334_, lean_object* v_b_4335_){
_start:
{
if (lean_obj_tag(v_d_x3f_4334_) == 0)
{
lean_object* v___x_4336_; lean_object* v___x_4337_; 
v___x_4336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4336_, 0, v_b_4335_);
v___x_4337_ = lean_apply_2(v_toPure_4333_, lean_box(0), v___x_4336_);
return v___x_4337_;
}
else
{
lean_object* v_val_4338_; lean_object* v___x_4340_; uint8_t v_isShared_4341_; uint8_t v_isSharedCheck_4353_; 
v_val_4338_ = lean_ctor_get(v_d_x3f_4334_, 0);
v_isSharedCheck_4353_ = !lean_is_exclusive(v_d_x3f_4334_);
if (v_isSharedCheck_4353_ == 0)
{
v___x_4340_ = v_d_x3f_4334_;
v_isShared_4341_ = v_isSharedCheck_4353_;
goto v_resetjp_4339_;
}
else
{
lean_inc(v_val_4338_);
lean_dec(v_d_x3f_4334_);
v___x_4340_ = lean_box(0);
v_isShared_4341_ = v_isSharedCheck_4353_;
goto v_resetjp_4339_;
}
v_resetjp_4339_:
{
uint8_t v___x_4342_; 
v___x_4342_ = l_Lean_LocalDecl_isImplementationDetail(v_val_4338_);
if (v___x_4342_ == 0)
{
lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4346_; 
v___x_4343_ = l_Lean_LocalDecl_toExpr(v_val_4338_);
v___x_4344_ = lean_array_push(v_b_4335_, v___x_4343_);
if (v_isShared_4341_ == 0)
{
lean_ctor_set(v___x_4340_, 0, v___x_4344_);
v___x_4346_ = v___x_4340_;
goto v_reusejp_4345_;
}
else
{
lean_object* v_reuseFailAlloc_4348_; 
v_reuseFailAlloc_4348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4348_, 0, v___x_4344_);
v___x_4346_ = v_reuseFailAlloc_4348_;
goto v_reusejp_4345_;
}
v_reusejp_4345_:
{
lean_object* v___x_4347_; 
v___x_4347_ = lean_apply_2(v_toPure_4333_, lean_box(0), v___x_4346_);
return v___x_4347_;
}
}
else
{
lean_object* v___x_4350_; 
lean_dec(v_val_4338_);
if (v_isShared_4341_ == 0)
{
lean_ctor_set(v___x_4340_, 0, v_b_4335_);
v___x_4350_ = v___x_4340_;
goto v_reusejp_4349_;
}
else
{
lean_object* v_reuseFailAlloc_4352_; 
v_reuseFailAlloc_4352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4352_, 0, v_b_4335_);
v___x_4350_ = v_reuseFailAlloc_4352_;
goto v_reusejp_4349_;
}
v_reusejp_4349_:
{
lean_object* v___x_4351_; 
v___x_4351_ = lean_apply_2(v_toPure_4333_, lean_box(0), v___x_4350_);
return v___x_4351_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__1(lean_object* v_toPure_4354_, lean_object* v_____s_4355_){
_start:
{
lean_object* v___x_4356_; 
v___x_4356_ = lean_apply_2(v_toPure_4354_, lean_box(0), v_____s_4355_);
return v___x_4356_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__2(lean_object* v_inst_4357_, lean_object* v_hs_4358_, lean_object* v___f_4359_, lean_object* v_toBind_4360_, lean_object* v___f_4361_, lean_object* v_____do__lift_4362_){
_start:
{
lean_object* v_decls_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; 
v_decls_4363_ = lean_ctor_get(v_____do__lift_4362_, 1);
v___x_4364_ = l_Lean_PersistentArray_forIn___redArg(v_inst_4357_, v_decls_4363_, v_hs_4358_, v___f_4359_);
v___x_4365_ = lean_apply_4(v_toBind_4360_, lean_box(0), lean_box(0), v___x_4364_, v___f_4361_);
return v___x_4365_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__2___boxed(lean_object* v_inst_4366_, lean_object* v_hs_4367_, lean_object* v___f_4368_, lean_object* v_toBind_4369_, lean_object* v___f_4370_, lean_object* v_____do__lift_4371_){
_start:
{
lean_object* v_res_4372_; 
v_res_4372_ = l_Lean_getLocalHyps___redArg___lam__2(v_inst_4366_, v_hs_4367_, v___f_4368_, v_toBind_4369_, v___f_4370_, v_____do__lift_4371_);
lean_dec_ref(v_____do__lift_4371_);
return v_res_4372_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg(lean_object* v_inst_4375_, lean_object* v_inst_4376_){
_start:
{
lean_object* v_toApplicative_4377_; lean_object* v_toBind_4378_; lean_object* v_toPure_4379_; lean_object* v_hs_4380_; lean_object* v___f_4381_; lean_object* v___f_4382_; lean_object* v___f_4383_; lean_object* v___x_4384_; 
v_toApplicative_4377_ = lean_ctor_get(v_inst_4375_, 0);
v_toBind_4378_ = lean_ctor_get(v_inst_4375_, 1);
lean_inc_n(v_toBind_4378_, 2);
v_toPure_4379_ = lean_ctor_get(v_toApplicative_4377_, 1);
v_hs_4380_ = ((lean_object*)(l_Lean_getLocalHyps___redArg___closed__0));
lean_inc_n(v_toPure_4379_, 2);
v___f_4381_ = lean_alloc_closure((void*)(l_Lean_getLocalHyps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4381_, 0, v_toPure_4379_);
v___f_4382_ = lean_alloc_closure((void*)(l_Lean_getLocalHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_4382_, 0, v_toPure_4379_);
v___f_4383_ = lean_alloc_closure((void*)(l_Lean_getLocalHyps___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_4383_, 0, v_inst_4375_);
lean_closure_set(v___f_4383_, 1, v_hs_4380_);
lean_closure_set(v___f_4383_, 2, v___f_4381_);
lean_closure_set(v___f_4383_, 3, v_toBind_4378_);
lean_closure_set(v___f_4383_, 4, v___f_4382_);
v___x_4384_ = lean_apply_4(v_toBind_4378_, lean_box(0), lean_box(0), v_inst_4376_, v___f_4383_);
return v___x_4384_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps(lean_object* v_m_4385_, lean_object* v_inst_4386_, lean_object* v_inst_4387_){
_start:
{
lean_object* v___x_4388_; 
v___x_4388_ = l_Lean_getLocalHyps___redArg(v_inst_4386_, v_inst_4387_);
return v___x_4388_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_replaceFVarId(lean_object* v_fvarId_4389_, lean_object* v_e_4390_, lean_object* v_d_4391_){
_start:
{
lean_object* v___y_4393_; lean_object* v_fvarId_4425_; 
v_fvarId_4425_ = lean_ctor_get(v_d_4391_, 1);
lean_inc(v_fvarId_4425_);
v___y_4393_ = v_fvarId_4425_;
goto v___jp_4392_;
v___jp_4392_:
{
uint8_t v___x_4394_; 
v___x_4394_ = l_Lean_instBEqFVarId_beq(v___y_4393_, v_fvarId_4389_);
lean_dec(v___y_4393_);
if (v___x_4394_ == 0)
{
if (lean_obj_tag(v_d_4391_) == 0)
{
lean_object* v_index_4395_; lean_object* v_fvarId_4396_; lean_object* v_userName_4397_; lean_object* v_type_4398_; uint8_t v_bi_4399_; uint8_t v_kind_4400_; lean_object* v___x_4402_; uint8_t v_isShared_4403_; uint8_t v_isSharedCheck_4408_; 
v_index_4395_ = lean_ctor_get(v_d_4391_, 0);
v_fvarId_4396_ = lean_ctor_get(v_d_4391_, 1);
v_userName_4397_ = lean_ctor_get(v_d_4391_, 2);
v_type_4398_ = lean_ctor_get(v_d_4391_, 3);
v_bi_4399_ = lean_ctor_get_uint8(v_d_4391_, sizeof(void*)*4);
v_kind_4400_ = lean_ctor_get_uint8(v_d_4391_, sizeof(void*)*4 + 1);
v_isSharedCheck_4408_ = !lean_is_exclusive(v_d_4391_);
if (v_isSharedCheck_4408_ == 0)
{
v___x_4402_ = v_d_4391_;
v_isShared_4403_ = v_isSharedCheck_4408_;
goto v_resetjp_4401_;
}
else
{
lean_inc(v_type_4398_);
lean_inc(v_userName_4397_);
lean_inc(v_fvarId_4396_);
lean_inc(v_index_4395_);
lean_dec(v_d_4391_);
v___x_4402_ = lean_box(0);
v_isShared_4403_ = v_isSharedCheck_4408_;
goto v_resetjp_4401_;
}
v_resetjp_4401_:
{
lean_object* v___x_4404_; lean_object* v___x_4406_; 
v___x_4404_ = l_Lean_Expr_replaceFVarId(v_type_4398_, v_fvarId_4389_, v_e_4390_);
lean_dec_ref(v_type_4398_);
if (v_isShared_4403_ == 0)
{
lean_ctor_set(v___x_4402_, 3, v___x_4404_);
v___x_4406_ = v___x_4402_;
goto v_reusejp_4405_;
}
else
{
lean_object* v_reuseFailAlloc_4407_; 
v_reuseFailAlloc_4407_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4407_, 0, v_index_4395_);
lean_ctor_set(v_reuseFailAlloc_4407_, 1, v_fvarId_4396_);
lean_ctor_set(v_reuseFailAlloc_4407_, 2, v_userName_4397_);
lean_ctor_set(v_reuseFailAlloc_4407_, 3, v___x_4404_);
lean_ctor_set_uint8(v_reuseFailAlloc_4407_, sizeof(void*)*4, v_bi_4399_);
lean_ctor_set_uint8(v_reuseFailAlloc_4407_, sizeof(void*)*4 + 1, v_kind_4400_);
v___x_4406_ = v_reuseFailAlloc_4407_;
goto v_reusejp_4405_;
}
v_reusejp_4405_:
{
return v___x_4406_;
}
}
}
else
{
lean_object* v_index_4409_; lean_object* v_fvarId_4410_; lean_object* v_userName_4411_; lean_object* v_type_4412_; lean_object* v_value_4413_; uint8_t v_nondep_4414_; uint8_t v_kind_4415_; lean_object* v___x_4417_; uint8_t v_isShared_4418_; uint8_t v_isSharedCheck_4424_; 
v_index_4409_ = lean_ctor_get(v_d_4391_, 0);
v_fvarId_4410_ = lean_ctor_get(v_d_4391_, 1);
v_userName_4411_ = lean_ctor_get(v_d_4391_, 2);
v_type_4412_ = lean_ctor_get(v_d_4391_, 3);
v_value_4413_ = lean_ctor_get(v_d_4391_, 4);
v_nondep_4414_ = lean_ctor_get_uint8(v_d_4391_, sizeof(void*)*5);
v_kind_4415_ = lean_ctor_get_uint8(v_d_4391_, sizeof(void*)*5 + 1);
v_isSharedCheck_4424_ = !lean_is_exclusive(v_d_4391_);
if (v_isSharedCheck_4424_ == 0)
{
v___x_4417_ = v_d_4391_;
v_isShared_4418_ = v_isSharedCheck_4424_;
goto v_resetjp_4416_;
}
else
{
lean_inc(v_value_4413_);
lean_inc(v_type_4412_);
lean_inc(v_userName_4411_);
lean_inc(v_fvarId_4410_);
lean_inc(v_index_4409_);
lean_dec(v_d_4391_);
v___x_4417_ = lean_box(0);
v_isShared_4418_ = v_isSharedCheck_4424_;
goto v_resetjp_4416_;
}
v_resetjp_4416_:
{
lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4422_; 
lean_inc(v_fvarId_4389_);
v___x_4419_ = l_Lean_Expr_replaceFVarId(v_type_4412_, v_fvarId_4389_, v_e_4390_);
lean_dec_ref(v_type_4412_);
v___x_4420_ = l_Lean_Expr_replaceFVarId(v_value_4413_, v_fvarId_4389_, v_e_4390_);
lean_dec_ref(v_value_4413_);
if (v_isShared_4418_ == 0)
{
lean_ctor_set(v___x_4417_, 4, v___x_4420_);
lean_ctor_set(v___x_4417_, 3, v___x_4419_);
v___x_4422_ = v___x_4417_;
goto v_reusejp_4421_;
}
else
{
lean_object* v_reuseFailAlloc_4423_; 
v_reuseFailAlloc_4423_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_4423_, 0, v_index_4409_);
lean_ctor_set(v_reuseFailAlloc_4423_, 1, v_fvarId_4410_);
lean_ctor_set(v_reuseFailAlloc_4423_, 2, v_userName_4411_);
lean_ctor_set(v_reuseFailAlloc_4423_, 3, v___x_4419_);
lean_ctor_set(v_reuseFailAlloc_4423_, 4, v___x_4420_);
lean_ctor_set_uint8(v_reuseFailAlloc_4423_, sizeof(void*)*5, v_nondep_4414_);
lean_ctor_set_uint8(v_reuseFailAlloc_4423_, sizeof(void*)*5 + 1, v_kind_4415_);
v___x_4422_ = v_reuseFailAlloc_4423_;
goto v_reusejp_4421_;
}
v_reusejp_4421_:
{
return v___x_4422_;
}
}
}
}
else
{
lean_dec(v_fvarId_4389_);
return v_d_4391_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_replaceFVarId___boxed(lean_object* v_fvarId_4426_, lean_object* v_e_4427_, lean_object* v_d_4428_){
_start:
{
lean_object* v_res_4429_; 
v_res_4429_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_4426_, v_e_4427_, v_d_4428_);
lean_dec_ref(v_e_4427_);
return v_res_4429_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId___lam__0(lean_object* v_fvarId_4430_, lean_object* v_e_4431_, lean_object* v_x_4432_){
_start:
{
lean_object* v___x_4433_; 
v___x_4433_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_4430_, v_e_4431_, v_x_4432_);
return v___x_4433_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId___lam__0___boxed(lean_object* v_fvarId_4434_, lean_object* v_e_4435_, lean_object* v_x_4436_){
_start:
{
lean_object* v_res_4437_; 
v_res_4437_ = l_Lean_LocalContext_replaceFVarId___lam__0(v_fvarId_4434_, v_e_4435_, v_x_4436_);
lean_dec_ref(v_e_4435_);
return v_res_4437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(lean_object* v_fvarId_4438_, lean_object* v_e_4439_, size_t v_sz_4440_, size_t v_i_4441_, lean_object* v_bs_4442_){
_start:
{
uint8_t v___x_4443_; 
v___x_4443_ = lean_usize_dec_lt(v_i_4441_, v_sz_4440_);
if (v___x_4443_ == 0)
{
lean_dec(v_fvarId_4438_);
return v_bs_4442_;
}
else
{
lean_object* v_v_4444_; lean_object* v___x_4445_; lean_object* v_bs_x27_4446_; lean_object* v___y_4448_; 
v_v_4444_ = lean_array_uget(v_bs_4442_, v_i_4441_);
v___x_4445_ = lean_unsigned_to_nat(0u);
v_bs_x27_4446_ = lean_array_uset(v_bs_4442_, v_i_4441_, v___x_4445_);
if (lean_obj_tag(v_v_4444_) == 0)
{
v___y_4448_ = v_v_4444_;
goto v___jp_4447_;
}
else
{
lean_object* v_val_4453_; lean_object* v___x_4455_; uint8_t v_isShared_4456_; uint8_t v_isSharedCheck_4461_; 
v_val_4453_ = lean_ctor_get(v_v_4444_, 0);
v_isSharedCheck_4461_ = !lean_is_exclusive(v_v_4444_);
if (v_isSharedCheck_4461_ == 0)
{
v___x_4455_ = v_v_4444_;
v_isShared_4456_ = v_isSharedCheck_4461_;
goto v_resetjp_4454_;
}
else
{
lean_inc(v_val_4453_);
lean_dec(v_v_4444_);
v___x_4455_ = lean_box(0);
v_isShared_4456_ = v_isSharedCheck_4461_;
goto v_resetjp_4454_;
}
v_resetjp_4454_:
{
lean_object* v___x_4457_; lean_object* v___x_4459_; 
lean_inc(v_fvarId_4438_);
v___x_4457_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_4438_, v_e_4439_, v_val_4453_);
if (v_isShared_4456_ == 0)
{
lean_ctor_set(v___x_4455_, 0, v___x_4457_);
v___x_4459_ = v___x_4455_;
goto v_reusejp_4458_;
}
else
{
lean_object* v_reuseFailAlloc_4460_; 
v_reuseFailAlloc_4460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4460_, 0, v___x_4457_);
v___x_4459_ = v_reuseFailAlloc_4460_;
goto v_reusejp_4458_;
}
v_reusejp_4458_:
{
v___y_4448_ = v___x_4459_;
goto v___jp_4447_;
}
}
}
v___jp_4447_:
{
size_t v___x_4449_; size_t v___x_4450_; lean_object* v___x_4451_; 
v___x_4449_ = ((size_t)1ULL);
v___x_4450_ = lean_usize_add(v_i_4441_, v___x_4449_);
v___x_4451_ = lean_array_uset(v_bs_x27_4446_, v_i_4441_, v___y_4448_);
v_i_4441_ = v___x_4450_;
v_bs_4442_ = v___x_4451_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3___boxed(lean_object* v_fvarId_4462_, lean_object* v_e_4463_, lean_object* v_sz_4464_, lean_object* v_i_4465_, lean_object* v_bs_4466_){
_start:
{
size_t v_sz_boxed_4467_; size_t v_i_boxed_4468_; lean_object* v_res_4469_; 
v_sz_boxed_4467_ = lean_unbox_usize(v_sz_4464_);
lean_dec(v_sz_4464_);
v_i_boxed_4468_ = lean_unbox_usize(v_i_4465_);
lean_dec(v_i_4465_);
v_res_4469_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(v_fvarId_4462_, v_e_4463_, v_sz_boxed_4467_, v_i_boxed_4468_, v_bs_4466_);
lean_dec_ref(v_e_4463_);
return v_res_4469_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(lean_object* v_fvarId_4470_, lean_object* v_e_4471_, size_t v_sz_4472_, size_t v_i_4473_, lean_object* v_bs_4474_){
_start:
{
uint8_t v___x_4475_; 
v___x_4475_ = lean_usize_dec_lt(v_i_4473_, v_sz_4472_);
if (v___x_4475_ == 0)
{
lean_dec(v_fvarId_4470_);
return v_bs_4474_;
}
else
{
lean_object* v_v_4476_; lean_object* v___x_4477_; lean_object* v_bs_x27_4478_; lean_object* v___x_4479_; size_t v___x_4480_; size_t v___x_4481_; lean_object* v___x_4482_; 
v_v_4476_ = lean_array_uget(v_bs_4474_, v_i_4473_);
v___x_4477_ = lean_unsigned_to_nat(0u);
v_bs_x27_4478_ = lean_array_uset(v_bs_4474_, v_i_4473_, v___x_4477_);
lean_inc(v_fvarId_4470_);
v___x_4479_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(v_fvarId_4470_, v_e_4471_, v_v_4476_);
v___x_4480_ = ((size_t)1ULL);
v___x_4481_ = lean_usize_add(v_i_4473_, v___x_4480_);
v___x_4482_ = lean_array_uset(v_bs_x27_4478_, v_i_4473_, v___x_4479_);
v_i_4473_ = v___x_4481_;
v_bs_4474_ = v___x_4482_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(lean_object* v_fvarId_4484_, lean_object* v_e_4485_, lean_object* v_x_4486_){
_start:
{
if (lean_obj_tag(v_x_4486_) == 0)
{
lean_object* v_cs_4487_; lean_object* v___x_4489_; uint8_t v_isShared_4490_; uint8_t v_isSharedCheck_4497_; 
v_cs_4487_ = lean_ctor_get(v_x_4486_, 0);
v_isSharedCheck_4497_ = !lean_is_exclusive(v_x_4486_);
if (v_isSharedCheck_4497_ == 0)
{
v___x_4489_ = v_x_4486_;
v_isShared_4490_ = v_isSharedCheck_4497_;
goto v_resetjp_4488_;
}
else
{
lean_inc(v_cs_4487_);
lean_dec(v_x_4486_);
v___x_4489_ = lean_box(0);
v_isShared_4490_ = v_isSharedCheck_4497_;
goto v_resetjp_4488_;
}
v_resetjp_4488_:
{
size_t v_sz_4491_; size_t v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4495_; 
v_sz_4491_ = lean_array_size(v_cs_4487_);
v___x_4492_ = ((size_t)0ULL);
v___x_4493_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(v_fvarId_4484_, v_e_4485_, v_sz_4491_, v___x_4492_, v_cs_4487_);
if (v_isShared_4490_ == 0)
{
lean_ctor_set(v___x_4489_, 0, v___x_4493_);
v___x_4495_ = v___x_4489_;
goto v_reusejp_4494_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v___x_4493_);
v___x_4495_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4494_;
}
v_reusejp_4494_:
{
return v___x_4495_;
}
}
}
else
{
lean_object* v_vs_4498_; lean_object* v___x_4500_; uint8_t v_isShared_4501_; uint8_t v_isSharedCheck_4508_; 
v_vs_4498_ = lean_ctor_get(v_x_4486_, 0);
v_isSharedCheck_4508_ = !lean_is_exclusive(v_x_4486_);
if (v_isSharedCheck_4508_ == 0)
{
v___x_4500_ = v_x_4486_;
v_isShared_4501_ = v_isSharedCheck_4508_;
goto v_resetjp_4499_;
}
else
{
lean_inc(v_vs_4498_);
lean_dec(v_x_4486_);
v___x_4500_ = lean_box(0);
v_isShared_4501_ = v_isSharedCheck_4508_;
goto v_resetjp_4499_;
}
v_resetjp_4499_:
{
size_t v_sz_4502_; size_t v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4506_; 
v_sz_4502_ = lean_array_size(v_vs_4498_);
v___x_4503_ = ((size_t)0ULL);
v___x_4504_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(v_fvarId_4484_, v_e_4485_, v_sz_4502_, v___x_4503_, v_vs_4498_);
if (v_isShared_4501_ == 0)
{
lean_ctor_set(v___x_4500_, 0, v___x_4504_);
v___x_4506_ = v___x_4500_;
goto v_reusejp_4505_;
}
else
{
lean_object* v_reuseFailAlloc_4507_; 
v_reuseFailAlloc_4507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4507_, 0, v___x_4504_);
v___x_4506_ = v_reuseFailAlloc_4507_;
goto v_reusejp_4505_;
}
v_reusejp_4505_:
{
return v___x_4506_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2___boxed(lean_object* v_fvarId_4509_, lean_object* v_e_4510_, lean_object* v_x_4511_){
_start:
{
lean_object* v_res_4512_; 
v_res_4512_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(v_fvarId_4509_, v_e_4510_, v_x_4511_);
lean_dec_ref(v_e_4510_);
return v_res_4512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4___boxed(lean_object* v_fvarId_4513_, lean_object* v_e_4514_, lean_object* v_sz_4515_, lean_object* v_i_4516_, lean_object* v_bs_4517_){
_start:
{
size_t v_sz_boxed_4518_; size_t v_i_boxed_4519_; lean_object* v_res_4520_; 
v_sz_boxed_4518_ = lean_unbox_usize(v_sz_4515_);
lean_dec(v_sz_4515_);
v_i_boxed_4519_ = lean_unbox_usize(v_i_4516_);
lean_dec(v_i_4516_);
v_res_4520_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(v_fvarId_4513_, v_e_4514_, v_sz_boxed_4518_, v_i_boxed_4519_, v_bs_4517_);
lean_dec_ref(v_e_4514_);
return v_res_4520_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(lean_object* v_fvarId_4521_, lean_object* v_e_4522_, lean_object* v_t_4523_){
_start:
{
lean_object* v_root_4524_; lean_object* v_tail_4525_; lean_object* v_size_4526_; size_t v_shift_4527_; lean_object* v_tailOff_4528_; lean_object* v___x_4530_; uint8_t v_isShared_4531_; uint8_t v_isSharedCheck_4539_; 
v_root_4524_ = lean_ctor_get(v_t_4523_, 0);
v_tail_4525_ = lean_ctor_get(v_t_4523_, 1);
v_size_4526_ = lean_ctor_get(v_t_4523_, 2);
v_shift_4527_ = lean_ctor_get_usize(v_t_4523_, 4);
v_tailOff_4528_ = lean_ctor_get(v_t_4523_, 3);
v_isSharedCheck_4539_ = !lean_is_exclusive(v_t_4523_);
if (v_isSharedCheck_4539_ == 0)
{
v___x_4530_ = v_t_4523_;
v_isShared_4531_ = v_isSharedCheck_4539_;
goto v_resetjp_4529_;
}
else
{
lean_inc(v_tailOff_4528_);
lean_inc(v_size_4526_);
lean_inc(v_tail_4525_);
lean_inc(v_root_4524_);
lean_dec(v_t_4523_);
v___x_4530_ = lean_box(0);
v_isShared_4531_ = v_isSharedCheck_4539_;
goto v_resetjp_4529_;
}
v_resetjp_4529_:
{
lean_object* v___x_4532_; size_t v_sz_4533_; size_t v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4537_; 
lean_inc(v_fvarId_4521_);
v___x_4532_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(v_fvarId_4521_, v_e_4522_, v_root_4524_);
v_sz_4533_ = lean_array_size(v_tail_4525_);
v___x_4534_ = ((size_t)0ULL);
v___x_4535_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(v_fvarId_4521_, v_e_4522_, v_sz_4533_, v___x_4534_, v_tail_4525_);
if (v_isShared_4531_ == 0)
{
lean_ctor_set(v___x_4530_, 1, v___x_4535_);
lean_ctor_set(v___x_4530_, 0, v___x_4532_);
v___x_4537_ = v___x_4530_;
goto v_reusejp_4536_;
}
else
{
lean_object* v_reuseFailAlloc_4538_; 
v_reuseFailAlloc_4538_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_4538_, 0, v___x_4532_);
lean_ctor_set(v_reuseFailAlloc_4538_, 1, v___x_4535_);
lean_ctor_set(v_reuseFailAlloc_4538_, 2, v_size_4526_);
lean_ctor_set(v_reuseFailAlloc_4538_, 3, v_tailOff_4528_);
lean_ctor_set_usize(v_reuseFailAlloc_4538_, 4, v_shift_4527_);
v___x_4537_ = v_reuseFailAlloc_4538_;
goto v_reusejp_4536_;
}
v_reusejp_4536_:
{
return v___x_4537_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1___boxed(lean_object* v_fvarId_4540_, lean_object* v_e_4541_, lean_object* v_t_4542_){
_start:
{
lean_object* v_res_4543_; 
v_res_4543_ = l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(v_fvarId_4540_, v_e_4541_, v_t_4542_);
lean_dec_ref(v_e_4541_);
return v_res_4543_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg___lam__0(lean_object* v_f_4544_, lean_object* v_x_4545_){
_start:
{
lean_object* v___x_4546_; 
v___x_4546_ = lean_apply_1(v_f_4544_, v_x_4545_);
return v___x_4546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(lean_object* v_f_4547_, lean_object* v_as_4548_, lean_object* v_i_4549_, lean_object* v_acc_4550_){
_start:
{
lean_object* v___x_4551_; uint8_t v___x_4552_; 
v___x_4551_ = lean_array_get_size(v_as_4548_);
v___x_4552_ = lean_nat_dec_eq(v_i_4549_, v___x_4551_);
if (v___x_4552_ == 0)
{
lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; 
v___x_4553_ = lean_array_fget_borrowed(v_as_4548_, v_i_4549_);
lean_inc(v_f_4547_);
lean_inc(v___x_4553_);
v___x_4554_ = lean_apply_1(v_f_4547_, v___x_4553_);
v___x_4555_ = lean_unsigned_to_nat(1u);
v___x_4556_ = lean_nat_add(v_i_4549_, v___x_4555_);
lean_dec(v_i_4549_);
v___x_4557_ = lean_array_push(v_acc_4550_, v___x_4554_);
v_i_4549_ = v___x_4556_;
v_acc_4550_ = v___x_4557_;
goto _start;
}
else
{
lean_dec(v_i_4549_);
lean_dec(v_f_4547_);
return v_acc_4550_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg___boxed(lean_object* v_f_4559_, lean_object* v_as_4560_, lean_object* v_i_4561_, lean_object* v_acc_4562_){
_start:
{
lean_object* v_res_4563_; 
v_res_4563_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_f_4559_, v_as_4560_, v_i_4561_, v_acc_4562_);
lean_dec_ref(v_as_4560_);
return v_res_4563_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_f_4564_, lean_object* v_as_4565_){
_start:
{
lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; 
v___x_4566_ = lean_unsigned_to_nat(0u);
v___x_4567_ = lean_array_get_size(v_as_4565_);
v___x_4568_ = lean_mk_empty_array_with_capacity(v___x_4567_);
v___x_4569_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_f_4564_, v_as_4565_, v___x_4566_, v___x_4568_);
return v___x_4569_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_f_4570_, lean_object* v_as_4571_){
_start:
{
lean_object* v_res_4572_; 
v_res_4572_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(v_f_4570_, v_as_4571_);
lean_dec_ref(v_as_4571_);
return v_res_4572_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_4573_, size_t v_sz_4574_, size_t v_i_4575_, lean_object* v_bs_4576_){
_start:
{
uint8_t v___x_4577_; 
v___x_4577_ = lean_usize_dec_lt(v_i_4575_, v_sz_4574_);
if (v___x_4577_ == 0)
{
lean_dec(v_f_4573_);
return v_bs_4576_;
}
else
{
lean_object* v_v_4578_; lean_object* v___x_4579_; lean_object* v_bs_x27_4580_; lean_object* v___y_4582_; 
v_v_4578_ = lean_array_uget(v_bs_4576_, v_i_4575_);
v___x_4579_ = lean_unsigned_to_nat(0u);
v_bs_x27_4580_ = lean_array_uset(v_bs_4576_, v_i_4575_, v___x_4579_);
switch(lean_obj_tag(v_v_4578_))
{
case 0:
{
lean_object* v_key_4587_; lean_object* v_val_4588_; lean_object* v___x_4590_; uint8_t v_isShared_4591_; uint8_t v_isSharedCheck_4596_; 
v_key_4587_ = lean_ctor_get(v_v_4578_, 0);
v_val_4588_ = lean_ctor_get(v_v_4578_, 1);
v_isSharedCheck_4596_ = !lean_is_exclusive(v_v_4578_);
if (v_isSharedCheck_4596_ == 0)
{
v___x_4590_ = v_v_4578_;
v_isShared_4591_ = v_isSharedCheck_4596_;
goto v_resetjp_4589_;
}
else
{
lean_inc(v_val_4588_);
lean_inc(v_key_4587_);
lean_dec(v_v_4578_);
v___x_4590_ = lean_box(0);
v_isShared_4591_ = v_isSharedCheck_4596_;
goto v_resetjp_4589_;
}
v_resetjp_4589_:
{
lean_object* v___x_4592_; lean_object* v___x_4594_; 
lean_inc(v_f_4573_);
v___x_4592_ = lean_apply_1(v_f_4573_, v_val_4588_);
if (v_isShared_4591_ == 0)
{
lean_ctor_set(v___x_4590_, 1, v___x_4592_);
v___x_4594_ = v___x_4590_;
goto v_reusejp_4593_;
}
else
{
lean_object* v_reuseFailAlloc_4595_; 
v_reuseFailAlloc_4595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4595_, 0, v_key_4587_);
lean_ctor_set(v_reuseFailAlloc_4595_, 1, v___x_4592_);
v___x_4594_ = v_reuseFailAlloc_4595_;
goto v_reusejp_4593_;
}
v_reusejp_4593_:
{
v___y_4582_ = v___x_4594_;
goto v___jp_4581_;
}
}
}
case 1:
{
lean_object* v_node_4597_; lean_object* v___x_4599_; uint8_t v_isShared_4600_; uint8_t v_isSharedCheck_4605_; 
v_node_4597_ = lean_ctor_get(v_v_4578_, 0);
v_isSharedCheck_4605_ = !lean_is_exclusive(v_v_4578_);
if (v_isSharedCheck_4605_ == 0)
{
v___x_4599_ = v_v_4578_;
v_isShared_4600_ = v_isSharedCheck_4605_;
goto v_resetjp_4598_;
}
else
{
lean_inc(v_node_4597_);
lean_dec(v_v_4578_);
v___x_4599_ = lean_box(0);
v_isShared_4600_ = v_isSharedCheck_4605_;
goto v_resetjp_4598_;
}
v_resetjp_4598_:
{
lean_object* v___x_4601_; lean_object* v___x_4603_; 
lean_inc(v_f_4573_);
v___x_4601_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4573_, v_node_4597_);
if (v_isShared_4600_ == 0)
{
lean_ctor_set(v___x_4599_, 0, v___x_4601_);
v___x_4603_ = v___x_4599_;
goto v_reusejp_4602_;
}
else
{
lean_object* v_reuseFailAlloc_4604_; 
v_reuseFailAlloc_4604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4604_, 0, v___x_4601_);
v___x_4603_ = v_reuseFailAlloc_4604_;
goto v_reusejp_4602_;
}
v_reusejp_4602_:
{
v___y_4582_ = v___x_4603_;
goto v___jp_4581_;
}
}
}
default: 
{
lean_object* v___x_4606_; 
v___x_4606_ = lean_box(2);
v___y_4582_ = v___x_4606_;
goto v___jp_4581_;
}
}
v___jp_4581_:
{
size_t v___x_4583_; size_t v___x_4584_; lean_object* v___x_4585_; 
v___x_4583_ = ((size_t)1ULL);
v___x_4584_ = lean_usize_add(v_i_4575_, v___x_4583_);
v___x_4585_ = lean_array_uset(v_bs_x27_4580_, v_i_4575_, v___y_4582_);
v_i_4575_ = v___x_4584_;
v_bs_4576_ = v___x_4585_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(lean_object* v_f_4607_, lean_object* v_n_4608_){
_start:
{
if (lean_obj_tag(v_n_4608_) == 0)
{
lean_object* v_es_4609_; lean_object* v___x_4611_; uint8_t v_isShared_4612_; uint8_t v_isSharedCheck_4619_; 
v_es_4609_ = lean_ctor_get(v_n_4608_, 0);
v_isSharedCheck_4619_ = !lean_is_exclusive(v_n_4608_);
if (v_isSharedCheck_4619_ == 0)
{
v___x_4611_ = v_n_4608_;
v_isShared_4612_ = v_isSharedCheck_4619_;
goto v_resetjp_4610_;
}
else
{
lean_inc(v_es_4609_);
lean_dec(v_n_4608_);
v___x_4611_ = lean_box(0);
v_isShared_4612_ = v_isSharedCheck_4619_;
goto v_resetjp_4610_;
}
v_resetjp_4610_:
{
size_t v_sz_4613_; size_t v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4617_; 
v_sz_4613_ = lean_array_size(v_es_4609_);
v___x_4614_ = ((size_t)0ULL);
v___x_4615_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(v_f_4607_, v_sz_4613_, v___x_4614_, v_es_4609_);
if (v_isShared_4612_ == 0)
{
lean_ctor_set(v___x_4611_, 0, v___x_4615_);
v___x_4617_ = v___x_4611_;
goto v_reusejp_4616_;
}
else
{
lean_object* v_reuseFailAlloc_4618_; 
v_reuseFailAlloc_4618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4618_, 0, v___x_4615_);
v___x_4617_ = v_reuseFailAlloc_4618_;
goto v_reusejp_4616_;
}
v_reusejp_4616_:
{
return v___x_4617_;
}
}
}
else
{
lean_object* v_ks_4620_; lean_object* v_vs_4621_; lean_object* v___x_4623_; uint8_t v_isShared_4624_; uint8_t v_isSharedCheck_4629_; 
v_ks_4620_ = lean_ctor_get(v_n_4608_, 0);
v_vs_4621_ = lean_ctor_get(v_n_4608_, 1);
v_isSharedCheck_4629_ = !lean_is_exclusive(v_n_4608_);
if (v_isSharedCheck_4629_ == 0)
{
v___x_4623_ = v_n_4608_;
v_isShared_4624_ = v_isSharedCheck_4629_;
goto v_resetjp_4622_;
}
else
{
lean_inc(v_vs_4621_);
lean_inc(v_ks_4620_);
lean_dec(v_n_4608_);
v___x_4623_ = lean_box(0);
v_isShared_4624_ = v_isSharedCheck_4629_;
goto v_resetjp_4622_;
}
v_resetjp_4622_:
{
lean_object* v_val_4625_; lean_object* v___x_4627_; 
v_val_4625_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(v_f_4607_, v_vs_4621_);
lean_dec_ref(v_vs_4621_);
if (v_isShared_4624_ == 0)
{
lean_ctor_set(v___x_4623_, 1, v_val_4625_);
v___x_4627_ = v___x_4623_;
goto v_reusejp_4626_;
}
else
{
lean_object* v_reuseFailAlloc_4628_; 
v_reuseFailAlloc_4628_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4628_, 0, v_ks_4620_);
lean_ctor_set(v_reuseFailAlloc_4628_, 1, v_val_4625_);
v___x_4627_ = v_reuseFailAlloc_4628_;
goto v_reusejp_4626_;
}
v_reusejp_4626_:
{
return v___x_4627_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_4630_, lean_object* v_sz_4631_, lean_object* v_i_4632_, lean_object* v_bs_4633_){
_start:
{
size_t v_sz_boxed_4634_; size_t v_i_boxed_4635_; lean_object* v_res_4636_; 
v_sz_boxed_4634_ = lean_unbox_usize(v_sz_4631_);
lean_dec(v_sz_4631_);
v_i_boxed_4635_ = lean_unbox_usize(v_i_4632_);
lean_dec(v_i_4632_);
v_res_4636_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(v_f_4630_, v_sz_boxed_4634_, v_i_boxed_4635_, v_bs_4633_);
return v_res_4636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(lean_object* v_pm_4637_, lean_object* v_f_4638_){
_start:
{
lean_object* v___f_4639_; lean_object* v___x_4640_; 
v___f_4639_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4639_, 0, v_f_4638_);
v___x_4640_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v___f_4639_, v_pm_4637_);
return v___x_4640_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId(lean_object* v_fvarId_4641_, lean_object* v_e_4642_, lean_object* v_lctx_4643_){
_start:
{
lean_object* v_lctx_4644_; lean_object* v_fvarIdToDecl_4645_; lean_object* v_decls_4646_; lean_object* v_auxDeclToFullName_4647_; lean_object* v___x_4649_; uint8_t v_isShared_4650_; uint8_t v_isSharedCheck_4657_; 
v_lctx_4644_ = l_Lean_LocalContext_erase(v_lctx_4643_, v_fvarId_4641_);
v_fvarIdToDecl_4645_ = lean_ctor_get(v_lctx_4644_, 0);
v_decls_4646_ = lean_ctor_get(v_lctx_4644_, 1);
v_auxDeclToFullName_4647_ = lean_ctor_get(v_lctx_4644_, 2);
v_isSharedCheck_4657_ = !lean_is_exclusive(v_lctx_4644_);
if (v_isSharedCheck_4657_ == 0)
{
v___x_4649_ = v_lctx_4644_;
v_isShared_4650_ = v_isSharedCheck_4657_;
goto v_resetjp_4648_;
}
else
{
lean_inc(v_auxDeclToFullName_4647_);
lean_inc(v_decls_4646_);
lean_inc(v_fvarIdToDecl_4645_);
lean_dec(v_lctx_4644_);
v___x_4649_ = lean_box(0);
v_isShared_4650_ = v_isSharedCheck_4657_;
goto v_resetjp_4648_;
}
v_resetjp_4648_:
{
lean_object* v___f_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4655_; 
lean_inc_ref(v_e_4642_);
lean_inc(v_fvarId_4641_);
v___f_4651_ = lean_alloc_closure((void*)(l_Lean_LocalContext_replaceFVarId___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4651_, 0, v_fvarId_4641_);
lean_closure_set(v___f_4651_, 1, v_e_4642_);
v___x_4652_ = l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(v_fvarIdToDecl_4645_, v___f_4651_);
v___x_4653_ = l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(v_fvarId_4641_, v_e_4642_, v_decls_4646_);
lean_dec_ref(v_e_4642_);
if (v_isShared_4650_ == 0)
{
lean_ctor_set(v___x_4649_, 1, v___x_4653_);
lean_ctor_set(v___x_4649_, 0, v___x_4652_);
v___x_4655_ = v___x_4649_;
goto v_reusejp_4654_;
}
else
{
lean_object* v_reuseFailAlloc_4656_; 
v_reuseFailAlloc_4656_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4656_, 0, v___x_4652_);
lean_ctor_set(v_reuseFailAlloc_4656_, 1, v___x_4653_);
lean_ctor_set(v_reuseFailAlloc_4656_, 2, v_auxDeclToFullName_4647_);
v___x_4655_ = v_reuseFailAlloc_4656_;
goto v_reusejp_4654_;
}
v_reusejp_4654_:
{
return v___x_4655_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0(lean_object* v_00_u03b2_4658_, lean_object* v_00_u03c3_4659_, lean_object* v_pm_4660_, lean_object* v_f_4661_){
_start:
{
lean_object* v___x_4662_; 
v___x_4662_ = l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(v_pm_4660_, v_f_4661_);
return v___x_4662_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0___redArg(lean_object* v_pm_4663_, lean_object* v_f_4664_){
_start:
{
lean_object* v___x_4665_; 
v___x_4665_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4664_, v_pm_4663_);
return v___x_4665_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0(lean_object* v_00_u03b2_4666_, lean_object* v_00_u03c3_4667_, lean_object* v_pm_4668_, lean_object* v_f_4669_){
_start:
{
lean_object* v___x_4670_; 
v___x_4670_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4669_, v_pm_4668_);
return v___x_4670_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_4671_, lean_object* v_00_u03b2_4672_, lean_object* v_00_u03c3_4673_, lean_object* v_f_4674_, lean_object* v_n_4675_){
_start:
{
lean_object* v___x_4676_; 
v___x_4676_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4674_, v_n_4675_);
return v___x_4676_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_4677_, lean_object* v_00_u03b2_4678_, lean_object* v_00_u03c3_4679_, lean_object* v_f_4680_, size_t v_sz_4681_, size_t v_i_4682_, lean_object* v_bs_4683_){
_start:
{
lean_object* v___x_4684_; 
v___x_4684_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(v_f_4680_, v_sz_4681_, v_i_4682_, v_bs_4683_);
return v___x_4684_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_4685_, lean_object* v_00_u03b2_4686_, lean_object* v_00_u03c3_4687_, lean_object* v_f_4688_, lean_object* v_sz_4689_, lean_object* v_i_4690_, lean_object* v_bs_4691_){
_start:
{
size_t v_sz_boxed_4692_; size_t v_i_boxed_4693_; lean_object* v_res_4694_; 
v_sz_boxed_4692_ = lean_unbox_usize(v_sz_4689_);
lean_dec(v_sz_4689_);
v_i_boxed_4693_ = lean_unbox_usize(v_i_4690_);
lean_dec(v_i_4690_);
v_res_4694_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_4685_, v_00_u03b2_4686_, v_00_u03c3_4687_, v_f_4688_, v_sz_boxed_4692_, v_i_boxed_4693_, v_bs_4691_);
return v_res_4694_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_4695_, lean_object* v_00_u03b2_4696_, lean_object* v_f_4697_, lean_object* v_as_4698_){
_start:
{
lean_object* v___x_4699_; 
v___x_4699_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(v_f_4697_, v_as_4698_);
return v___x_4699_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_4700_, lean_object* v_00_u03b2_4701_, lean_object* v_f_4702_, lean_object* v_as_4703_){
_start:
{
lean_object* v_res_4704_; 
v_res_4704_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_4700_, v_00_u03b2_4701_, v_f_4702_, v_as_4703_);
lean_dec_ref(v_as_4703_);
return v_res_4704_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7(lean_object* v_00_u03b1_4705_, lean_object* v_00_u03b2_4706_, lean_object* v_f_4707_, lean_object* v_as_4708_, lean_object* v_i_4709_, lean_object* v_acc_4710_, lean_object* v_hle_4711_){
_start:
{
lean_object* v___x_4712_; 
v___x_4712_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_f_4707_, v_as_4708_, v_i_4709_, v_acc_4710_);
return v___x_4712_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___boxed(lean_object* v_00_u03b1_4713_, lean_object* v_00_u03b2_4714_, lean_object* v_f_4715_, lean_object* v_as_4716_, lean_object* v_i_4717_, lean_object* v_acc_4718_, lean_object* v_hle_4719_){
_start:
{
lean_object* v_res_4720_; 
v_res_4720_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7(v_00_u03b1_4713_, v_00_u03b2_4714_, v_f_4715_, v_as_4716_, v_i_4717_, v_acc_4718_, v_hle_4719_);
lean_dec_ref(v_as_4716_);
return v_res_4720_;
}
}
lean_object* runtime_initialize_Init_Data_Nat_Control(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_PersistentArray(uint8_t builtin);
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_LocalContext(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
