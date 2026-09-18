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
static lean_once_cell_t l_Lean_LocalDecl_isAuxDecl___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LocalDecl_isAuxDecl___closed__0;
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isAuxDecl___boxed(lean_object*);
static lean_once_cell_t l_Lean_LocalDecl_isImplementationDetail___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LocalDecl_isImplementationDetail___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_LocalDeclKind_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
uint8_t v_t_boxed_21_; lean_object* v_res_22_; 
v_t_boxed_21_ = lean_unbox(v_t_18_);
v_res_22_ = l_Lean_LocalDeclKind_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_boxed_21_, v_h_19_, v_k_20_);
lean_dec(v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim___redArg(lean_object* v_default_23_){
_start:
{
lean_inc(v_default_23_);
return v_default_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim___redArg___boxed(lean_object* v_default_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_LocalDeclKind_default_elim___redArg(v_default_24_);
lean_dec(v_default_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim(lean_object* v_motive_26_, uint8_t v_t_27_, lean_object* v_h_28_, lean_object* v_default_29_){
_start:
{
lean_inc(v_default_29_);
return v_default_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim___boxed(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_default_33_){
_start:
{
uint8_t v_t_boxed_34_; lean_object* v_res_35_; 
v_t_boxed_34_ = lean_unbox(v_t_31_);
v_res_35_ = l_Lean_LocalDeclKind_default_elim(v_motive_30_, v_t_boxed_34_, v_h_32_, v_default_33_);
lean_dec(v_default_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim___redArg(lean_object* v_implDetail_36_){
_start:
{
lean_inc(v_implDetail_36_);
return v_implDetail_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim___redArg___boxed(lean_object* v_implDetail_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_LocalDeclKind_implDetail_elim___redArg(v_implDetail_37_);
lean_dec(v_implDetail_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim(lean_object* v_motive_39_, uint8_t v_t_40_, lean_object* v_h_41_, lean_object* v_implDetail_42_){
_start:
{
lean_inc(v_implDetail_42_);
return v_implDetail_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim___boxed(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_implDetail_46_){
_start:
{
uint8_t v_t_boxed_47_; lean_object* v_res_48_; 
v_t_boxed_47_ = lean_unbox(v_t_44_);
v_res_48_ = l_Lean_LocalDeclKind_implDetail_elim(v_motive_43_, v_t_boxed_47_, v_h_45_, v_implDetail_46_);
lean_dec(v_implDetail_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim___redArg(lean_object* v_auxDecl_49_){
_start:
{
lean_inc(v_auxDecl_49_);
return v_auxDecl_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim___redArg___boxed(lean_object* v_auxDecl_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_LocalDeclKind_auxDecl_elim___redArg(v_auxDecl_50_);
lean_dec(v_auxDecl_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim(lean_object* v_motive_52_, uint8_t v_t_53_, lean_object* v_h_54_, lean_object* v_auxDecl_55_){
_start:
{
lean_inc(v_auxDecl_55_);
return v_auxDecl_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim___boxed(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_auxDecl_59_){
_start:
{
uint8_t v_t_boxed_60_; lean_object* v_res_61_; 
v_t_boxed_60_ = lean_unbox(v_t_57_);
v_res_61_ = l_Lean_LocalDeclKind_auxDecl_elim(v_motive_56_, v_t_boxed_60_, v_h_58_, v_auxDecl_59_);
lean_dec(v_auxDecl_59_);
return v_res_61_;
}
}
static uint8_t _init_l_Lean_instInhabitedLocalDeclKind_default(void){
_start:
{
uint8_t v___x_62_; 
v___x_62_ = 0;
return v___x_62_;
}
}
static uint8_t _init_l_Lean_instInhabitedLocalDeclKind(void){
_start:
{
uint8_t v___x_63_; 
v___x_63_ = 0;
return v___x_63_;
}
}
static lean_object* _init_l_Lean_instReprLocalDeclKind_repr___closed__6(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = lean_unsigned_to_nat(2u);
v___x_74_ = lean_nat_to_int(v___x_73_);
return v___x_74_;
}
}
static lean_object* _init_l_Lean_instReprLocalDeclKind_repr___closed__7(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = lean_unsigned_to_nat(1u);
v___x_76_ = lean_nat_to_int(v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLocalDeclKind_repr(uint8_t v_x_77_, lean_object* v_prec_78_){
_start:
{
lean_object* v___y_80_; lean_object* v___y_87_; lean_object* v___y_94_; 
switch(v_x_77_)
{
case 0:
{
lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_100_ = lean_unsigned_to_nat(1024u);
v___x_101_ = lean_nat_dec_le(v___x_100_, v_prec_78_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; 
v___x_102_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__6, &l_Lean_instReprLocalDeclKind_repr___closed__6_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__6);
v___y_80_ = v___x_102_;
goto v___jp_79_;
}
else
{
lean_object* v___x_103_; 
v___x_103_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__7, &l_Lean_instReprLocalDeclKind_repr___closed__7_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__7);
v___y_80_ = v___x_103_;
goto v___jp_79_;
}
}
case 1:
{
lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_104_ = lean_unsigned_to_nat(1024u);
v___x_105_ = lean_nat_dec_le(v___x_104_, v_prec_78_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; 
v___x_106_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__6, &l_Lean_instReprLocalDeclKind_repr___closed__6_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__6);
v___y_87_ = v___x_106_;
goto v___jp_86_;
}
else
{
lean_object* v___x_107_; 
v___x_107_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__7, &l_Lean_instReprLocalDeclKind_repr___closed__7_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__7);
v___y_87_ = v___x_107_;
goto v___jp_86_;
}
}
default: 
{
lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_108_ = lean_unsigned_to_nat(1024u);
v___x_109_ = lean_nat_dec_le(v___x_108_, v_prec_78_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; 
v___x_110_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__6, &l_Lean_instReprLocalDeclKind_repr___closed__6_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__6);
v___y_94_ = v___x_110_;
goto v___jp_93_;
}
else
{
lean_object* v___x_111_; 
v___x_111_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__7, &l_Lean_instReprLocalDeclKind_repr___closed__7_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__7);
v___y_94_ = v___x_111_;
goto v___jp_93_;
}
}
}
v___jp_79_:
{
lean_object* v___x_81_; lean_object* v___x_82_; uint8_t v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_81_ = ((lean_object*)(l_Lean_instReprLocalDeclKind_repr___closed__1));
lean_inc(v___y_80_);
v___x_82_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_82_, 0, v___y_80_);
lean_ctor_set(v___x_82_, 1, v___x_81_);
v___x_83_ = 0;
v___x_84_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_84_, 0, v___x_82_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*1, v___x_83_);
v___x_85_ = l_Repr_addAppParen(v___x_84_, v_prec_78_);
return v___x_85_;
}
v___jp_86_:
{
lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_88_ = ((lean_object*)(l_Lean_instReprLocalDeclKind_repr___closed__3));
lean_inc(v___y_87_);
v___x_89_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_89_, 0, v___y_87_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
v___x_90_ = 0;
v___x_91_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_91_, 0, v___x_89_);
lean_ctor_set_uint8(v___x_91_, sizeof(void*)*1, v___x_90_);
v___x_92_ = l_Repr_addAppParen(v___x_91_, v_prec_78_);
return v___x_92_;
}
v___jp_93_:
{
lean_object* v___x_95_; lean_object* v___x_96_; uint8_t v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_95_ = ((lean_object*)(l_Lean_instReprLocalDeclKind_repr___closed__5));
lean_inc(v___y_94_);
v___x_96_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_96_, 0, v___y_94_);
lean_ctor_set(v___x_96_, 1, v___x_95_);
v___x_97_ = 0;
v___x_98_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_98_, 0, v___x_96_);
lean_ctor_set_uint8(v___x_98_, sizeof(void*)*1, v___x_97_);
v___x_99_ = l_Repr_addAppParen(v___x_98_, v_prec_78_);
return v___x_99_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLocalDeclKind_repr___boxed(lean_object* v_x_112_, lean_object* v_prec_113_){
_start:
{
uint8_t v_x_171__boxed_114_; lean_object* v_res_115_; 
v_x_171__boxed_114_ = lean_unbox(v_x_112_);
v_res_115_ = l_Lean_instReprLocalDeclKind_repr(v_x_171__boxed_114_, v_prec_113_);
lean_dec(v_prec_113_);
return v_res_115_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDeclKind_ofNat(lean_object* v_n_118_){
_start:
{
lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_119_ = lean_unsigned_to_nat(0u);
v___x_120_ = lean_nat_dec_le(v_n_118_, v___x_119_);
if (v___x_120_ == 0)
{
lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_121_ = lean_unsigned_to_nat(1u);
v___x_122_ = lean_nat_dec_le(v_n_118_, v___x_121_);
if (v___x_122_ == 0)
{
uint8_t v___x_123_; 
v___x_123_ = 2;
return v___x_123_;
}
else
{
uint8_t v___x_124_; 
v___x_124_ = 1;
return v___x_124_;
}
}
else
{
uint8_t v___x_125_; 
v___x_125_ = 0;
return v___x_125_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ofNat___boxed(lean_object* v_n_126_){
_start:
{
uint8_t v_res_127_; lean_object* v_r_128_; 
v_res_127_ = l_Lean_LocalDeclKind_ofNat(v_n_126_);
lean_dec(v_n_126_);
v_r_128_ = lean_box(v_res_127_);
return v_r_128_;
}
}
LEAN_EXPORT uint8_t l_Lean_instDecidableEqLocalDeclKind(uint8_t v_x_129_, uint8_t v_y_130_){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_131_ = l_Lean_LocalDeclKind_ctorIdx(v_x_129_);
v___x_132_ = l_Lean_LocalDeclKind_ctorIdx(v_y_130_);
v___x_133_ = lean_nat_dec_eq(v___x_131_, v___x_132_);
lean_dec(v___x_132_);
lean_dec(v___x_131_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_instDecidableEqLocalDeclKind___boxed(lean_object* v_x_134_, lean_object* v_y_135_){
_start:
{
uint8_t v_x_20__boxed_136_; uint8_t v_y_21__boxed_137_; uint8_t v_res_138_; lean_object* v_r_139_; 
v_x_20__boxed_136_ = lean_unbox(v_x_134_);
v_y_21__boxed_137_ = lean_unbox(v_y_135_);
v_res_138_ = l_Lean_instDecidableEqLocalDeclKind(v_x_20__boxed_136_, v_y_21__boxed_137_);
v_r_139_ = lean_box(v_res_138_);
return v_r_139_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableLocalDeclKind_hash(uint8_t v_x_140_){
_start:
{
switch(v_x_140_)
{
case 0:
{
uint64_t v___x_141_; 
v___x_141_ = 0ULL;
return v___x_141_;
}
case 1:
{
uint64_t v___x_142_; 
v___x_142_ = 1ULL;
return v___x_142_;
}
default: 
{
uint64_t v___x_143_; 
v___x_143_ = 2ULL;
return v___x_143_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableLocalDeclKind_hash___boxed(lean_object* v_x_144_){
_start:
{
uint8_t v_x_40__boxed_145_; uint64_t v_res_146_; lean_object* v_r_147_; 
v_x_40__boxed_145_ = lean_unbox(v_x_144_);
v_res_146_ = l_Lean_instHashableLocalDeclKind_hash(v_x_40__boxed_145_);
v_r_147_ = lean_box_uint64(v_res_146_);
return v_r_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorIdx(lean_object* v_x_150_){
_start:
{
if (lean_obj_tag(v_x_150_) == 0)
{
lean_object* v___x_151_; 
v___x_151_ = lean_unsigned_to_nat(0u);
return v___x_151_;
}
else
{
lean_object* v___x_152_; 
v___x_152_ = lean_unsigned_to_nat(1u);
return v___x_152_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorIdx___boxed(lean_object* v_x_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Lean_LocalDecl_ctorIdx(v_x_153_);
lean_dec_ref(v_x_153_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim___redArg(lean_object* v_t_155_, lean_object* v_k_156_){
_start:
{
if (lean_obj_tag(v_t_155_) == 0)
{
lean_object* v_index_157_; lean_object* v_fvarId_158_; lean_object* v_userName_159_; lean_object* v_type_160_; uint8_t v_bi_161_; uint8_t v_kind_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v_index_157_ = lean_ctor_get(v_t_155_, 0);
lean_inc(v_index_157_);
v_fvarId_158_ = lean_ctor_get(v_t_155_, 1);
lean_inc(v_fvarId_158_);
v_userName_159_ = lean_ctor_get(v_t_155_, 2);
lean_inc(v_userName_159_);
v_type_160_ = lean_ctor_get(v_t_155_, 3);
lean_inc_ref(v_type_160_);
v_bi_161_ = lean_ctor_get_uint8(v_t_155_, sizeof(void*)*4);
v_kind_162_ = lean_ctor_get_uint8(v_t_155_, sizeof(void*)*4 + 1);
lean_dec_ref_known(v_t_155_, 4);
v___x_163_ = lean_box(v_bi_161_);
v___x_164_ = lean_box(v_kind_162_);
v___x_165_ = lean_apply_6(v_k_156_, v_index_157_, v_fvarId_158_, v_userName_159_, v_type_160_, v___x_163_, v___x_164_);
return v___x_165_;
}
else
{
lean_object* v_index_166_; lean_object* v_fvarId_167_; lean_object* v_userName_168_; lean_object* v_type_169_; lean_object* v_value_170_; uint8_t v_nondep_171_; uint8_t v_kind_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v_index_166_ = lean_ctor_get(v_t_155_, 0);
lean_inc(v_index_166_);
v_fvarId_167_ = lean_ctor_get(v_t_155_, 1);
lean_inc(v_fvarId_167_);
v_userName_168_ = lean_ctor_get(v_t_155_, 2);
lean_inc(v_userName_168_);
v_type_169_ = lean_ctor_get(v_t_155_, 3);
lean_inc_ref(v_type_169_);
v_value_170_ = lean_ctor_get(v_t_155_, 4);
lean_inc_ref(v_value_170_);
v_nondep_171_ = lean_ctor_get_uint8(v_t_155_, sizeof(void*)*5);
v_kind_172_ = lean_ctor_get_uint8(v_t_155_, sizeof(void*)*5 + 1);
lean_dec_ref_known(v_t_155_, 5);
v___x_173_ = lean_box(v_nondep_171_);
v___x_174_ = lean_box(v_kind_172_);
v___x_175_ = lean_apply_7(v_k_156_, v_index_166_, v_fvarId_167_, v_userName_168_, v_type_169_, v_value_170_, v___x_173_, v___x_174_);
return v___x_175_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim(lean_object* v_motive_176_, lean_object* v_ctorIdx_177_, lean_object* v_t_178_, lean_object* v_h_179_, lean_object* v_k_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_178_, v_k_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim___boxed(lean_object* v_motive_182_, lean_object* v_ctorIdx_183_, lean_object* v_t_184_, lean_object* v_h_185_, lean_object* v_k_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_LocalDecl_ctorElim(v_motive_182_, v_ctorIdx_183_, v_t_184_, v_h_185_, v_k_186_);
lean_dec(v_ctorIdx_183_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_cdecl_elim___redArg(lean_object* v_t_188_, lean_object* v_cdecl_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_188_, v_cdecl_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_cdecl_elim(lean_object* v_motive_191_, lean_object* v_t_192_, lean_object* v_h_193_, lean_object* v_cdecl_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_192_, v_cdecl_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ldecl_elim___redArg(lean_object* v_t_196_, lean_object* v_ldecl_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_196_, v_ldecl_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ldecl_elim(lean_object* v_motive_199_, lean_object* v_t_200_, lean_object* v_h_201_, lean_object* v_ldecl_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_200_, v_ldecl_202_);
return v___x_203_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl_default___closed__2(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_207_ = lean_box(0);
v___x_208_ = ((lean_object*)(l_Lean_instInhabitedLocalDecl_default___closed__1));
v___x_209_ = l_Lean_Expr_const___override(v___x_208_, v___x_207_);
return v___x_209_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl_default___closed__3(void){
_start:
{
uint8_t v___x_210_; uint8_t v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_210_ = 0;
v___x_211_ = 0;
v___x_212_ = lean_obj_once(&l_Lean_instInhabitedLocalDecl_default___closed__2, &l_Lean_instInhabitedLocalDecl_default___closed__2_once, _init_l_Lean_instInhabitedLocalDecl_default___closed__2);
v___x_213_ = lean_box(0);
v___x_214_ = lean_unsigned_to_nat(0u);
v___x_215_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_215_, 0, v___x_214_);
lean_ctor_set(v___x_215_, 1, v___x_213_);
lean_ctor_set(v___x_215_, 2, v___x_213_);
lean_ctor_set(v___x_215_, 3, v___x_212_);
lean_ctor_set_uint8(v___x_215_, sizeof(void*)*4, v___x_211_);
lean_ctor_set_uint8(v___x_215_, sizeof(void*)*4 + 1, v___x_210_);
return v___x_215_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl_default(void){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = lean_obj_once(&l_Lean_instInhabitedLocalDecl_default___closed__3, &l_Lean_instInhabitedLocalDecl_default___closed__3_once, _init_l_Lean_instInhabitedLocalDecl_default___closed__3);
return v___x_216_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl(void){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_instInhabitedLocalDecl_default;
return v___x_217_;
}
}
LEAN_EXPORT lean_object* lean_mk_local_decl(lean_object* v_index_218_, lean_object* v_fvarId_219_, lean_object* v_userName_220_, lean_object* v_type_221_, uint8_t v_bi_222_){
_start:
{
uint8_t v___x_223_; lean_object* v___x_224_; 
v___x_223_ = 0;
v___x_224_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_224_, 0, v_index_218_);
lean_ctor_set(v___x_224_, 1, v_fvarId_219_);
lean_ctor_set(v___x_224_, 2, v_userName_220_);
lean_ctor_set(v___x_224_, 3, v_type_221_);
lean_ctor_set_uint8(v___x_224_, sizeof(void*)*4, v_bi_222_);
lean_ctor_set_uint8(v___x_224_, sizeof(void*)*4 + 1, v___x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLocalDeclEx___boxed(lean_object* v_index_225_, lean_object* v_fvarId_226_, lean_object* v_userName_227_, lean_object* v_type_228_, lean_object* v_bi_229_){
_start:
{
uint8_t v_bi_boxed_230_; lean_object* v_res_231_; 
v_bi_boxed_230_ = lean_unbox(v_bi_229_);
v_res_231_ = lean_mk_local_decl(v_index_225_, v_fvarId_226_, v_userName_227_, v_type_228_, v_bi_boxed_230_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* lean_mk_let_decl(lean_object* v_index_232_, lean_object* v_fvarId_233_, lean_object* v_userName_234_, lean_object* v_type_235_, lean_object* v_val_236_){
_start:
{
uint8_t v___x_237_; uint8_t v___x_238_; lean_object* v___x_239_; 
v___x_237_ = 0;
v___x_238_ = 0;
v___x_239_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v___x_239_, 0, v_index_232_);
lean_ctor_set(v___x_239_, 1, v_fvarId_233_);
lean_ctor_set(v___x_239_, 2, v_userName_234_);
lean_ctor_set(v___x_239_, 3, v_type_235_);
lean_ctor_set(v___x_239_, 4, v_val_236_);
lean_ctor_set_uint8(v___x_239_, sizeof(void*)*5, v___x_237_);
lean_ctor_set_uint8(v___x_239_, sizeof(void*)*5 + 1, v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT uint8_t lean_local_decl_binder_info(lean_object* v_x_240_){
_start:
{
if (lean_obj_tag(v_x_240_) == 0)
{
uint8_t v_bi_241_; 
v_bi_241_ = lean_ctor_get_uint8(v_x_240_, sizeof(void*)*4);
lean_dec_ref_known(v_x_240_, 4);
return v_bi_241_;
}
else
{
uint8_t v___x_242_; 
lean_dec_ref(v_x_240_);
v___x_242_ = 0;
return v___x_242_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_binderInfoEx___boxed(lean_object* v_x_243_){
_start:
{
uint8_t v_res_244_; lean_object* v_r_245_; 
v_res_244_ = lean_local_decl_binder_info(v_x_243_);
v_r_245_ = lean_box(v_res_244_);
return v_r_245_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isLet(lean_object* v_x_246_, uint8_t v_x_247_){
_start:
{
if (lean_obj_tag(v_x_246_) == 0)
{
uint8_t v___x_248_; 
v___x_248_ = 0;
return v___x_248_;
}
else
{
uint8_t v_nondep_249_; 
v_nondep_249_ = lean_ctor_get_uint8(v_x_246_, sizeof(void*)*5);
if (v_nondep_249_ == 0)
{
uint8_t v___x_250_; 
v___x_250_ = 1;
return v___x_250_;
}
else
{
return v_x_247_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isLet___boxed(lean_object* v_x_251_, lean_object* v_x_252_){
_start:
{
uint8_t v_x_53__boxed_253_; uint8_t v_res_254_; lean_object* v_r_255_; 
v_x_53__boxed_253_ = lean_unbox(v_x_252_);
v_res_254_ = l_Lean_LocalDecl_isLet(v_x_251_, v_x_53__boxed_253_);
lean_dec_ref(v_x_251_);
v_r_255_ = lean_box(v_res_254_);
return v_r_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_index(lean_object* v_x_256_){
_start:
{
lean_object* v_index_257_; 
v_index_257_ = lean_ctor_get(v_x_256_, 0);
lean_inc(v_index_257_);
return v_index_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_index___boxed(lean_object* v_x_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_LocalDecl_index(v_x_258_);
lean_dec_ref(v_x_258_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setIndex(lean_object* v_x_260_, lean_object* v_x_261_){
_start:
{
if (lean_obj_tag(v_x_260_) == 0)
{
lean_object* v_fvarId_262_; lean_object* v_userName_263_; lean_object* v_type_264_; uint8_t v_bi_265_; uint8_t v_kind_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_273_; 
v_fvarId_262_ = lean_ctor_get(v_x_260_, 1);
v_userName_263_ = lean_ctor_get(v_x_260_, 2);
v_type_264_ = lean_ctor_get(v_x_260_, 3);
v_bi_265_ = lean_ctor_get_uint8(v_x_260_, sizeof(void*)*4);
v_kind_266_ = lean_ctor_get_uint8(v_x_260_, sizeof(void*)*4 + 1);
v_isSharedCheck_273_ = !lean_is_exclusive(v_x_260_);
if (v_isSharedCheck_273_ == 0)
{
lean_object* v_unused_274_; 
v_unused_274_ = lean_ctor_get(v_x_260_, 0);
lean_dec(v_unused_274_);
v___x_268_ = v_x_260_;
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_type_264_);
lean_inc(v_userName_263_);
lean_inc(v_fvarId_262_);
lean_dec(v_x_260_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_271_; 
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 0, v_x_261_);
v___x_271_ = v___x_268_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_x_261_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v_fvarId_262_);
lean_ctor_set(v_reuseFailAlloc_272_, 2, v_userName_263_);
lean_ctor_set(v_reuseFailAlloc_272_, 3, v_type_264_);
lean_ctor_set_uint8(v_reuseFailAlloc_272_, sizeof(void*)*4, v_bi_265_);
lean_ctor_set_uint8(v_reuseFailAlloc_272_, sizeof(void*)*4 + 1, v_kind_266_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
else
{
lean_object* v_fvarId_275_; lean_object* v_userName_276_; lean_object* v_type_277_; lean_object* v_value_278_; uint8_t v_nondep_279_; uint8_t v_kind_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_287_; 
v_fvarId_275_ = lean_ctor_get(v_x_260_, 1);
v_userName_276_ = lean_ctor_get(v_x_260_, 2);
v_type_277_ = lean_ctor_get(v_x_260_, 3);
v_value_278_ = lean_ctor_get(v_x_260_, 4);
v_nondep_279_ = lean_ctor_get_uint8(v_x_260_, sizeof(void*)*5);
v_kind_280_ = lean_ctor_get_uint8(v_x_260_, sizeof(void*)*5 + 1);
v_isSharedCheck_287_ = !lean_is_exclusive(v_x_260_);
if (v_isSharedCheck_287_ == 0)
{
lean_object* v_unused_288_; 
v_unused_288_ = lean_ctor_get(v_x_260_, 0);
lean_dec(v_unused_288_);
v___x_282_ = v_x_260_;
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_value_278_);
lean_inc(v_type_277_);
lean_inc(v_userName_276_);
lean_inc(v_fvarId_275_);
lean_dec(v_x_260_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_285_; 
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 0, v_x_261_);
v___x_285_ = v___x_282_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_x_261_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v_fvarId_275_);
lean_ctor_set(v_reuseFailAlloc_286_, 2, v_userName_276_);
lean_ctor_set(v_reuseFailAlloc_286_, 3, v_type_277_);
lean_ctor_set(v_reuseFailAlloc_286_, 4, v_value_278_);
lean_ctor_set_uint8(v_reuseFailAlloc_286_, sizeof(void*)*5, v_nondep_279_);
lean_ctor_set_uint8(v_reuseFailAlloc_286_, sizeof(void*)*5 + 1, v_kind_280_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_fvarId(lean_object* v_x_289_){
_start:
{
lean_object* v_fvarId_290_; 
v_fvarId_290_ = lean_ctor_get(v_x_289_, 1);
lean_inc(v_fvarId_290_);
return v_fvarId_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_fvarId___boxed(lean_object* v_x_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_LocalDecl_fvarId(v_x_291_);
lean_dec_ref(v_x_291_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_userName(lean_object* v_x_293_){
_start:
{
lean_object* v_userName_294_; 
v_userName_294_ = lean_ctor_get(v_x_293_, 2);
lean_inc(v_userName_294_);
return v_userName_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_userName___boxed(lean_object* v_x_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_LocalDecl_userName(v_x_295_);
lean_dec_ref(v_x_295_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_type(lean_object* v_x_297_){
_start:
{
lean_object* v_type_298_; 
v_type_298_ = lean_ctor_get(v_x_297_, 3);
lean_inc_ref(v_type_298_);
return v_type_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_type___boxed(lean_object* v_x_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_LocalDecl_type(v_x_299_);
lean_dec_ref(v_x_299_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setType(lean_object* v_x_301_, lean_object* v_x_302_){
_start:
{
if (lean_obj_tag(v_x_301_) == 0)
{
lean_object* v_index_303_; lean_object* v_fvarId_304_; lean_object* v_userName_305_; uint8_t v_bi_306_; uint8_t v_kind_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_314_; 
v_index_303_ = lean_ctor_get(v_x_301_, 0);
v_fvarId_304_ = lean_ctor_get(v_x_301_, 1);
v_userName_305_ = lean_ctor_get(v_x_301_, 2);
v_bi_306_ = lean_ctor_get_uint8(v_x_301_, sizeof(void*)*4);
v_kind_307_ = lean_ctor_get_uint8(v_x_301_, sizeof(void*)*4 + 1);
v_isSharedCheck_314_ = !lean_is_exclusive(v_x_301_);
if (v_isSharedCheck_314_ == 0)
{
lean_object* v_unused_315_; 
v_unused_315_ = lean_ctor_get(v_x_301_, 3);
lean_dec(v_unused_315_);
v___x_309_ = v_x_301_;
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_userName_305_);
lean_inc(v_fvarId_304_);
lean_inc(v_index_303_);
lean_dec(v_x_301_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_312_; 
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 3, v_x_302_);
v___x_312_ = v___x_309_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_index_303_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v_fvarId_304_);
lean_ctor_set(v_reuseFailAlloc_313_, 2, v_userName_305_);
lean_ctor_set(v_reuseFailAlloc_313_, 3, v_x_302_);
lean_ctor_set_uint8(v_reuseFailAlloc_313_, sizeof(void*)*4, v_bi_306_);
lean_ctor_set_uint8(v_reuseFailAlloc_313_, sizeof(void*)*4 + 1, v_kind_307_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
else
{
lean_object* v_index_316_; lean_object* v_fvarId_317_; lean_object* v_userName_318_; lean_object* v_value_319_; uint8_t v_nondep_320_; uint8_t v_kind_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_328_; 
v_index_316_ = lean_ctor_get(v_x_301_, 0);
v_fvarId_317_ = lean_ctor_get(v_x_301_, 1);
v_userName_318_ = lean_ctor_get(v_x_301_, 2);
v_value_319_ = lean_ctor_get(v_x_301_, 4);
v_nondep_320_ = lean_ctor_get_uint8(v_x_301_, sizeof(void*)*5);
v_kind_321_ = lean_ctor_get_uint8(v_x_301_, sizeof(void*)*5 + 1);
v_isSharedCheck_328_ = !lean_is_exclusive(v_x_301_);
if (v_isSharedCheck_328_ == 0)
{
lean_object* v_unused_329_; 
v_unused_329_ = lean_ctor_get(v_x_301_, 3);
lean_dec(v_unused_329_);
v___x_323_ = v_x_301_;
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_value_319_);
lean_inc(v_userName_318_);
lean_inc(v_fvarId_317_);
lean_inc(v_index_316_);
lean_dec(v_x_301_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 3, v_x_302_);
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_index_316_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_fvarId_317_);
lean_ctor_set(v_reuseFailAlloc_327_, 2, v_userName_318_);
lean_ctor_set(v_reuseFailAlloc_327_, 3, v_x_302_);
lean_ctor_set(v_reuseFailAlloc_327_, 4, v_value_319_);
lean_ctor_set_uint8(v_reuseFailAlloc_327_, sizeof(void*)*5, v_nondep_320_);
lean_ctor_set_uint8(v_reuseFailAlloc_327_, sizeof(void*)*5 + 1, v_kind_321_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_binderInfo(lean_object* v_x_330_){
_start:
{
if (lean_obj_tag(v_x_330_) == 0)
{
uint8_t v_bi_331_; 
v_bi_331_ = lean_ctor_get_uint8(v_x_330_, sizeof(void*)*4);
return v_bi_331_;
}
else
{
uint8_t v___x_332_; 
v___x_332_ = 0;
return v___x_332_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_binderInfo___boxed(lean_object* v_x_333_){
_start:
{
uint8_t v_res_334_; lean_object* v_r_335_; 
v_res_334_ = l_Lean_LocalDecl_binderInfo(v_x_333_);
lean_dec_ref(v_x_333_);
v_r_335_ = lean_box(v_res_334_);
return v_r_335_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_kind(lean_object* v_x_336_){
_start:
{
if (lean_obj_tag(v_x_336_) == 0)
{
uint8_t v_kind_337_; 
v_kind_337_ = lean_ctor_get_uint8(v_x_336_, sizeof(void*)*4 + 1);
return v_kind_337_;
}
else
{
uint8_t v_kind_338_; 
v_kind_338_ = lean_ctor_get_uint8(v_x_336_, sizeof(void*)*5 + 1);
return v_kind_338_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_kind___boxed(lean_object* v_x_339_){
_start:
{
uint8_t v_res_340_; lean_object* v_r_341_; 
v_res_340_ = l_Lean_LocalDecl_kind(v_x_339_);
lean_dec_ref(v_x_339_);
v_r_341_ = lean_box(v_res_340_);
return v_r_341_;
}
}
static lean_object* _init_l_Lean_LocalDecl_isAuxDecl___closed__0(void){
_start:
{
uint8_t v___x_342_; lean_object* v___x_343_; 
v___x_342_ = 2;
v___x_343_ = l_Lean_LocalDeclKind_ctorIdx(v___x_342_);
return v___x_343_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object* v_d_344_){
_start:
{
uint8_t v___y_346_; 
if (lean_obj_tag(v_d_344_) == 0)
{
uint8_t v_kind_350_; 
v_kind_350_ = lean_ctor_get_uint8(v_d_344_, sizeof(void*)*4 + 1);
v___y_346_ = v_kind_350_;
goto v___jp_345_;
}
else
{
uint8_t v_kind_351_; 
v_kind_351_ = lean_ctor_get_uint8(v_d_344_, sizeof(void*)*5 + 1);
v___y_346_ = v_kind_351_;
goto v___jp_345_;
}
v___jp_345_:
{
lean_object* v___x_347_; lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_347_ = l_Lean_LocalDeclKind_ctorIdx(v___y_346_);
v___x_348_ = lean_obj_once(&l_Lean_LocalDecl_isAuxDecl___closed__0, &l_Lean_LocalDecl_isAuxDecl___closed__0_once, _init_l_Lean_LocalDecl_isAuxDecl___closed__0);
v___x_349_ = lean_nat_dec_eq(v___x_347_, v___x_348_);
lean_dec(v___x_347_);
return v___x_349_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isAuxDecl___boxed(lean_object* v_d_352_){
_start:
{
uint8_t v_res_353_; lean_object* v_r_354_; 
v_res_353_ = l_Lean_LocalDecl_isAuxDecl(v_d_352_);
lean_dec_ref(v_d_352_);
v_r_354_ = lean_box(v_res_353_);
return v_r_354_;
}
}
static lean_object* _init_l_Lean_LocalDecl_isImplementationDetail___closed__0(void){
_start:
{
uint8_t v___x_355_; lean_object* v___x_356_; 
v___x_355_ = 0;
v___x_356_ = l_Lean_LocalDeclKind_ctorIdx(v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object* v_d_357_){
_start:
{
uint8_t v___y_359_; 
if (lean_obj_tag(v_d_357_) == 0)
{
uint8_t v_kind_365_; 
v_kind_365_ = lean_ctor_get_uint8(v_d_357_, sizeof(void*)*4 + 1);
v___y_359_ = v_kind_365_;
goto v___jp_358_;
}
else
{
uint8_t v_kind_366_; 
v_kind_366_ = lean_ctor_get_uint8(v_d_357_, sizeof(void*)*5 + 1);
v___y_359_ = v_kind_366_;
goto v___jp_358_;
}
v___jp_358_:
{
lean_object* v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v___x_360_ = l_Lean_LocalDeclKind_ctorIdx(v___y_359_);
v___x_361_ = lean_obj_once(&l_Lean_LocalDecl_isImplementationDetail___closed__0, &l_Lean_LocalDecl_isImplementationDetail___closed__0_once, _init_l_Lean_LocalDecl_isImplementationDetail___closed__0);
v___x_362_ = lean_nat_dec_eq(v___x_360_, v___x_361_);
lean_dec(v___x_360_);
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
uint8_t v_x_47__boxed_381_; lean_object* v_res_382_; 
v_x_47__boxed_381_ = lean_unbox(v_x_380_);
v_res_382_ = l_Lean_LocalDecl_value_x3f(v_x_379_, v_x_47__boxed_381_);
lean_dec_ref(v_x_379_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_LocalDecl_value_spec__0(lean_object* v_msg_383_){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = l_Lean_instInhabitedExpr;
v___x_385_ = lean_panic_fn_borrowed(v___x_384_, v_msg_383_);
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
uint8_t v_x_23__boxed_458_; lean_object* v_res_459_; 
v_x_23__boxed_458_ = lean_unbox(v_x_457_);
v_res_459_ = l_Lean_LocalDecl_setNondep(v_x_456_, v_x_23__boxed_458_);
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
v___x_497_ = lean_panic_fn_borrowed(v___x_496_, v_msg_495_);
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
lean_dec_ref_known(v_x_506_, 5);
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
v___x_570_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_573_ = lean_unsigned_to_nat(32u);
v___x_574_ = lean_mk_empty_array_with_capacity(v___x_573_);
v___x_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
return v___x_575_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__3(void){
_start:
{
size_t v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_576_ = ((size_t)5ULL);
v___x_577_ = lean_unsigned_to_nat(0u);
v___x_578_ = lean_unsigned_to_nat(32u);
v___x_579_ = lean_mk_empty_array_with_capacity(v___x_578_);
v___x_580_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__2, &l_Lean_instInhabitedLocalContext_default___closed__2_once, _init_l_Lean_instInhabitedLocalContext_default___closed__2);
v___x_581_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_581_, 0, v___x_580_);
lean_ctor_set(v___x_581_, 1, v___x_579_);
lean_ctor_set(v___x_581_, 2, v___x_577_);
lean_ctor_set(v___x_581_, 3, v___x_577_);
lean_ctor_set_usize(v___x_581_, 4, v___x_576_);
return v___x_581_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__4(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_582_ = lean_box(1);
v___x_583_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__3, &l_Lean_instInhabitedLocalContext_default___closed__3_once, _init_l_Lean_instInhabitedLocalContext_default___closed__3);
v___x_584_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__1, &l_Lean_instInhabitedLocalContext_default___closed__1_once, _init_l_Lean_instInhabitedLocalContext_default___closed__1);
v___x_585_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
lean_ctor_set(v___x_585_, 1, v___x_583_);
lean_ctor_set(v___x_585_, 2, v___x_582_);
return v___x_585_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default(void){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__4, &l_Lean_instInhabitedLocalContext_default___closed__4_once, _init_l_Lean_instInhabitedLocalContext_default___closed__4);
return v___x_586_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext(void){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_instInhabitedLocalContext_default;
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkEmpty___redArg(){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_589_ = lean_unsigned_to_nat(32u);
v___x_590_ = lean_mk_empty_array_with_capacity(v___x_589_);
lean_dec_ref(v___x_590_);
v___x_591_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__4, &l_Lean_instInhabitedLocalContext_default___closed__4_once, _init_l_Lean_instInhabitedLocalContext_default___closed__4);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkEmpty___redArg___boxed(lean_object* v___dummy_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Lean_LocalContext_mkEmpty___redArg();
return v_res_593_;
}
}
static lean_object* _init_l_Lean_LocalContext_mkEmpty___closed__0(void){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Lean_LocalContext_mkEmpty___redArg();
return v___x_594_;
}
}
LEAN_EXPORT lean_object* lean_mk_empty_local_ctx(lean_object* v_x_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = lean_obj_once(&l_Lean_LocalContext_mkEmpty___closed__0, &l_Lean_LocalContext_mkEmpty___closed__0_once, _init_l_Lean_LocalContext_mkEmpty___closed__0);
return v___x_596_;
}
}
static lean_object* _init_l_Lean_LocalContext_empty(void){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_597_ = lean_unsigned_to_nat(32u);
v___x_598_ = lean_mk_empty_array_with_capacity(v___x_597_);
lean_dec_ref(v___x_598_);
v___x_599_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__4, &l_Lean_instInhabitedLocalContext_default___closed__4_once, _init_l_Lean_instInhabitedLocalContext_default___closed__4);
return v___x_599_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg(lean_object* v_x_600_){
_start:
{
uint8_t v___x_601_; 
v___x_601_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg___boxed(lean_object* v_x_602_){
_start:
{
uint8_t v_res_603_; lean_object* v_r_604_; 
v_res_603_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg(v_x_602_);
lean_dec_ref(v_x_602_);
v_r_604_ = lean_box(v_res_603_);
return v_r_604_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0(lean_object* v_00_u03b2_605_, lean_object* v_x_606_){
_start:
{
uint8_t v___x_607_; 
v___x_607_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___boxed(lean_object* v_00_u03b2_608_, lean_object* v_x_609_){
_start:
{
uint8_t v_res_610_; lean_object* v_r_611_; 
v_res_610_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0(v_00_u03b2_608_, v_x_609_);
lean_dec_ref(v_x_609_);
v_r_611_ = lean_box(v_res_610_);
return v_r_611_;
}
}
LEAN_EXPORT uint8_t lean_local_ctx_is_empty(lean_object* v_lctx_612_){
_start:
{
lean_object* v_fvarIdToDecl_613_; uint8_t v___x_614_; 
v_fvarIdToDecl_613_ = lean_ctor_get(v_lctx_612_, 0);
lean_inc_ref(v_fvarIdToDecl_613_);
lean_dec_ref(v_lctx_612_);
v___x_614_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_fvarIdToDecl_613_);
lean_dec_ref(v_fvarIdToDecl_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_isEmpty___boxed(lean_object* v_lctx_615_){
_start:
{
uint8_t v_res_616_; lean_object* v_r_617_; 
v_res_616_ = lean_local_ctx_is_empty(v_lctx_615_);
v_r_617_ = lean_box(v_res_616_);
return v_r_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_618_, lean_object* v_x_619_, lean_object* v_x_620_, lean_object* v_x_621_){
_start:
{
lean_object* v_ks_622_; lean_object* v_vs_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_647_; 
v_ks_622_ = lean_ctor_get(v_x_618_, 0);
v_vs_623_ = lean_ctor_get(v_x_618_, 1);
v_isSharedCheck_647_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_647_ == 0)
{
v___x_625_ = v_x_618_;
v_isShared_626_ = v_isSharedCheck_647_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_vs_623_);
lean_inc(v_ks_622_);
lean_dec(v_x_618_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_647_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_627_; uint8_t v___x_628_; 
v___x_627_ = lean_array_get_size(v_ks_622_);
v___x_628_ = lean_nat_dec_lt(v_x_619_, v___x_627_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_632_; 
lean_dec(v_x_619_);
v___x_629_ = lean_array_push(v_ks_622_, v_x_620_);
v___x_630_ = lean_array_push(v_vs_623_, v_x_621_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 1, v___x_630_);
lean_ctor_set(v___x_625_, 0, v___x_629_);
v___x_632_ = v___x_625_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v___x_630_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
else
{
lean_object* v_k_x27_634_; uint8_t v___x_635_; 
v_k_x27_634_ = lean_array_fget_borrowed(v_ks_622_, v_x_619_);
v___x_635_ = l_Lean_instBEqFVarId_beq(v_x_620_, v_k_x27_634_);
if (v___x_635_ == 0)
{
lean_object* v___x_637_; 
if (v_isShared_626_ == 0)
{
v___x_637_ = v___x_625_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_ks_622_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v_vs_623_);
v___x_637_ = v_reuseFailAlloc_641_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = lean_unsigned_to_nat(1u);
v___x_639_ = lean_nat_add(v_x_619_, v___x_638_);
lean_dec(v_x_619_);
v_x_618_ = v___x_637_;
v_x_619_ = v___x_639_;
goto _start;
}
}
else
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_645_; 
v___x_642_ = lean_array_fset(v_ks_622_, v_x_619_, v_x_620_);
v___x_643_ = lean_array_fset(v_vs_623_, v_x_619_, v_x_621_);
lean_dec(v_x_619_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 1, v___x_643_);
lean_ctor_set(v___x_625_, 0, v___x_642_);
v___x_645_ = v___x_625_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_642_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v___x_643_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1___redArg(lean_object* v_n_648_, lean_object* v_k_649_, lean_object* v_v_650_){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = lean_unsigned_to_nat(0u);
v___x_652_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2___redArg(v_n_648_, v___x_651_, v_k_649_, v_v_650_);
return v___x_652_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(lean_object* v_x_654_, size_t v_x_655_, size_t v_x_656_, lean_object* v_x_657_, lean_object* v_x_658_){
_start:
{
if (lean_obj_tag(v_x_654_) == 0)
{
lean_object* v_es_659_; size_t v___x_660_; size_t v___x_661_; lean_object* v_j_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v_es_659_ = lean_ctor_get(v_x_654_, 0);
v___x_660_ = ((size_t)31ULL);
v___x_661_ = lean_usize_land(v_x_655_, v___x_660_);
v_j_662_ = lean_usize_to_nat(v___x_661_);
v___x_663_ = lean_array_get_size(v_es_659_);
v___x_664_ = lean_nat_dec_lt(v_j_662_, v___x_663_);
if (v___x_664_ == 0)
{
lean_dec(v_j_662_);
lean_dec(v_x_658_);
lean_dec(v_x_657_);
return v_x_654_;
}
else
{
lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_703_; 
lean_inc_ref(v_es_659_);
v_isSharedCheck_703_ = !lean_is_exclusive(v_x_654_);
if (v_isSharedCheck_703_ == 0)
{
lean_object* v_unused_704_; 
v_unused_704_ = lean_ctor_get(v_x_654_, 0);
lean_dec(v_unused_704_);
v___x_666_ = v_x_654_;
v_isShared_667_ = v_isSharedCheck_703_;
goto v_resetjp_665_;
}
else
{
lean_dec(v_x_654_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_703_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v_v_668_; lean_object* v___x_669_; lean_object* v_xs_x27_670_; lean_object* v___y_672_; 
v_v_668_ = lean_array_fget(v_es_659_, v_j_662_);
v___x_669_ = lean_box(0);
v_xs_x27_670_ = lean_array_fset(v_es_659_, v_j_662_, v___x_669_);
switch(lean_obj_tag(v_v_668_))
{
case 0:
{
lean_object* v_key_677_; lean_object* v_val_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_688_; 
v_key_677_ = lean_ctor_get(v_v_668_, 0);
v_val_678_ = lean_ctor_get(v_v_668_, 1);
v_isSharedCheck_688_ = !lean_is_exclusive(v_v_668_);
if (v_isSharedCheck_688_ == 0)
{
v___x_680_ = v_v_668_;
v_isShared_681_ = v_isSharedCheck_688_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_val_678_);
lean_inc(v_key_677_);
lean_dec(v_v_668_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_688_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
uint8_t v___x_682_; 
v___x_682_ = l_Lean_instBEqFVarId_beq(v_x_657_, v_key_677_);
if (v___x_682_ == 0)
{
lean_object* v___x_683_; lean_object* v___x_684_; 
lean_del_object(v___x_680_);
v___x_683_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_677_, v_val_678_, v_x_657_, v_x_658_);
v___x_684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
v___y_672_ = v___x_684_;
goto v___jp_671_;
}
else
{
lean_object* v___x_686_; 
lean_dec(v_val_678_);
lean_dec(v_key_677_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 1, v_x_658_);
lean_ctor_set(v___x_680_, 0, v_x_657_);
v___x_686_ = v___x_680_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_x_657_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v_x_658_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
v___y_672_ = v___x_686_;
goto v___jp_671_;
}
}
}
}
case 1:
{
lean_object* v_node_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_701_; 
v_node_689_ = lean_ctor_get(v_v_668_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v_v_668_);
if (v_isSharedCheck_701_ == 0)
{
v___x_691_ = v_v_668_;
v_isShared_692_ = v_isSharedCheck_701_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_node_689_);
lean_dec(v_v_668_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_701_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
size_t v___x_693_; size_t v___x_694_; size_t v___x_695_; size_t v___x_696_; lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_693_ = ((size_t)5ULL);
v___x_694_ = lean_usize_shift_right(v_x_655_, v___x_693_);
v___x_695_ = ((size_t)1ULL);
v___x_696_ = lean_usize_add(v_x_656_, v___x_695_);
v___x_697_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_node_689_, v___x_694_, v___x_696_, v_x_657_, v_x_658_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v___x_697_);
v___x_699_ = v___x_691_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_697_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
v___y_672_ = v___x_699_;
goto v___jp_671_;
}
}
}
default: 
{
lean_object* v___x_702_; 
v___x_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_702_, 0, v_x_657_);
lean_ctor_set(v___x_702_, 1, v_x_658_);
v___y_672_ = v___x_702_;
goto v___jp_671_;
}
}
v___jp_671_:
{
lean_object* v___x_673_; lean_object* v___x_675_; 
v___x_673_ = lean_array_fset(v_xs_x27_670_, v_j_662_, v___y_672_);
lean_dec(v_j_662_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_673_);
v___x_675_ = v___x_666_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_673_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
}
else
{
lean_object* v_ks_705_; lean_object* v_vs_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_724_; 
v_ks_705_ = lean_ctor_get(v_x_654_, 0);
v_vs_706_ = lean_ctor_get(v_x_654_, 1);
v_isSharedCheck_724_ = !lean_is_exclusive(v_x_654_);
if (v_isSharedCheck_724_ == 0)
{
v___x_708_ = v_x_654_;
v_isShared_709_ = v_isSharedCheck_724_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_vs_706_);
lean_inc(v_ks_705_);
lean_dec(v_x_654_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_724_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_ks_705_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_vs_706_);
v___x_711_ = v_reuseFailAlloc_723_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
lean_object* v_newNode_712_; size_t v___x_713_; uint8_t v___x_714_; 
v_newNode_712_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1___redArg(v___x_711_, v_x_657_, v_x_658_);
v___x_713_ = ((size_t)7ULL);
v___x_714_ = lean_usize_dec_le(v___x_713_, v_x_656_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_715_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_712_);
v___x_716_ = lean_unsigned_to_nat(4u);
v___x_717_ = lean_nat_dec_lt(v___x_715_, v___x_716_);
lean_dec(v___x_715_);
if (v___x_717_ == 0)
{
lean_object* v_ks_718_; lean_object* v_vs_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v_ks_718_ = lean_ctor_get(v_newNode_712_, 0);
lean_inc_ref(v_ks_718_);
v_vs_719_ = lean_ctor_get(v_newNode_712_, 1);
lean_inc_ref(v_vs_719_);
lean_dec_ref(v_newNode_712_);
v___x_720_ = lean_unsigned_to_nat(0u);
v___x_721_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0);
v___x_722_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(v_x_656_, v_ks_718_, v_vs_719_, v___x_720_, v___x_721_);
lean_dec_ref(v_vs_719_);
lean_dec_ref(v_ks_718_);
return v___x_722_;
}
else
{
return v_newNode_712_;
}
}
else
{
return v_newNode_712_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(size_t v_depth_725_, lean_object* v_keys_726_, lean_object* v_vals_727_, lean_object* v_i_728_, lean_object* v_entries_729_){
_start:
{
lean_object* v___x_730_; uint8_t v___x_731_; 
v___x_730_ = lean_array_get_size(v_keys_726_);
v___x_731_ = lean_nat_dec_lt(v_i_728_, v___x_730_);
if (v___x_731_ == 0)
{
lean_dec(v_i_728_);
return v_entries_729_;
}
else
{
lean_object* v_k_732_; lean_object* v_v_733_; uint64_t v___x_734_; size_t v_h_735_; size_t v___x_736_; lean_object* v___x_737_; size_t v___x_738_; size_t v___x_739_; size_t v___x_740_; size_t v_h_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v_k_732_ = lean_array_fget_borrowed(v_keys_726_, v_i_728_);
v_v_733_ = lean_array_fget_borrowed(v_vals_727_, v_i_728_);
v___x_734_ = l_Lean_instHashableFVarId_hash(v_k_732_);
v_h_735_ = lean_uint64_to_usize(v___x_734_);
v___x_736_ = ((size_t)5ULL);
v___x_737_ = lean_unsigned_to_nat(1u);
v___x_738_ = ((size_t)1ULL);
v___x_739_ = lean_usize_sub(v_depth_725_, v___x_738_);
v___x_740_ = lean_usize_mul(v___x_736_, v___x_739_);
v_h_741_ = lean_usize_shift_right(v_h_735_, v___x_740_);
v___x_742_ = lean_nat_add(v_i_728_, v___x_737_);
lean_dec(v_i_728_);
lean_inc(v_v_733_);
lean_inc(v_k_732_);
v___x_743_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_entries_729_, v_h_741_, v_depth_725_, v_k_732_, v_v_733_);
v_i_728_ = v___x_742_;
v_entries_729_ = v___x_743_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_745_, lean_object* v_keys_746_, lean_object* v_vals_747_, lean_object* v_i_748_, lean_object* v_entries_749_){
_start:
{
size_t v_depth_boxed_750_; lean_object* v_res_751_; 
v_depth_boxed_750_ = lean_unbox_usize(v_depth_745_);
lean_dec(v_depth_745_);
v_res_751_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(v_depth_boxed_750_, v_keys_746_, v_vals_747_, v_i_748_, v_entries_749_);
lean_dec_ref(v_vals_747_);
lean_dec_ref(v_keys_746_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___boxed(lean_object* v_x_752_, lean_object* v_x_753_, lean_object* v_x_754_, lean_object* v_x_755_, lean_object* v_x_756_){
_start:
{
size_t v_x_365__boxed_757_; size_t v_x_366__boxed_758_; lean_object* v_res_759_; 
v_x_365__boxed_757_ = lean_unbox_usize(v_x_753_);
lean_dec(v_x_753_);
v_x_366__boxed_758_ = lean_unbox_usize(v_x_754_);
lean_dec(v_x_754_);
v_res_759_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_x_752_, v_x_365__boxed_757_, v_x_366__boxed_758_, v_x_755_, v_x_756_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(lean_object* v_x_760_, lean_object* v_x_761_, lean_object* v_x_762_){
_start:
{
uint64_t v___x_763_; size_t v___x_764_; size_t v___x_765_; lean_object* v___x_766_; 
v___x_763_ = l_Lean_instHashableFVarId_hash(v_x_761_);
v___x_764_ = lean_uint64_to_usize(v___x_763_);
v___x_765_ = ((size_t)1ULL);
v___x_766_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_x_760_, v___x_764_, v___x_765_, v_x_761_, v_x_762_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object* v_lctx_767_, lean_object* v_fvarId_768_, lean_object* v_userName_769_, lean_object* v_type_770_, uint8_t v_bi_771_, uint8_t v_kind_772_){
_start:
{
lean_object* v_decls_773_; lean_object* v_fvarIdToDecl_774_; lean_object* v_auxDeclToFullName_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_787_; 
v_decls_773_ = lean_ctor_get(v_lctx_767_, 1);
v_fvarIdToDecl_774_ = lean_ctor_get(v_lctx_767_, 0);
v_auxDeclToFullName_775_ = lean_ctor_get(v_lctx_767_, 2);
v_isSharedCheck_787_ = !lean_is_exclusive(v_lctx_767_);
if (v_isSharedCheck_787_ == 0)
{
v___x_777_ = v_lctx_767_;
v_isShared_778_ = v_isSharedCheck_787_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_auxDeclToFullName_775_);
lean_inc(v_decls_773_);
lean_inc(v_fvarIdToDecl_774_);
lean_dec(v_lctx_767_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_787_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v_size_779_; lean_object* v_decl_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_785_; 
v_size_779_ = lean_ctor_get(v_decls_773_, 2);
lean_inc(v_fvarId_768_);
lean_inc(v_size_779_);
v_decl_780_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_decl_780_, 0, v_size_779_);
lean_ctor_set(v_decl_780_, 1, v_fvarId_768_);
lean_ctor_set(v_decl_780_, 2, v_userName_769_);
lean_ctor_set(v_decl_780_, 3, v_type_770_);
lean_ctor_set_uint8(v_decl_780_, sizeof(void*)*4, v_bi_771_);
lean_ctor_set_uint8(v_decl_780_, sizeof(void*)*4 + 1, v_kind_772_);
lean_inc_ref(v_decl_780_);
v___x_781_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_774_, v_fvarId_768_, v_decl_780_);
v___x_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_782_, 0, v_decl_780_);
v___x_783_ = l_Lean_PersistentArray_push___redArg(v_decls_773_, v___x_782_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 1, v___x_783_);
lean_ctor_set(v___x_777_, 0, v___x_781_);
v___x_785_ = v___x_777_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_781_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v___x_783_);
lean_ctor_set(v_reuseFailAlloc_786_, 2, v_auxDeclToFullName_775_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLocalDecl___boxed(lean_object* v_lctx_788_, lean_object* v_fvarId_789_, lean_object* v_userName_790_, lean_object* v_type_791_, lean_object* v_bi_792_, lean_object* v_kind_793_){
_start:
{
uint8_t v_bi_boxed_794_; uint8_t v_kind_boxed_795_; lean_object* v_res_796_; 
v_bi_boxed_794_ = lean_unbox(v_bi_792_);
v_kind_boxed_795_ = lean_unbox(v_kind_793_);
v_res_796_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_788_, v_fvarId_789_, v_userName_790_, v_type_791_, v_bi_boxed_794_, v_kind_boxed_795_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0(lean_object* v_00_u03b2_797_, lean_object* v_x_798_, lean_object* v_x_799_, lean_object* v_x_800_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_x_798_, v_x_799_, v_x_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0(lean_object* v_00_u03b2_802_, lean_object* v_x_803_, size_t v_x_804_, size_t v_x_805_, lean_object* v_x_806_, lean_object* v_x_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_x_803_, v_x_804_, v_x_805_, v_x_806_, v_x_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_809_, lean_object* v_x_810_, lean_object* v_x_811_, lean_object* v_x_812_, lean_object* v_x_813_, lean_object* v_x_814_){
_start:
{
size_t v_x_565__boxed_815_; size_t v_x_566__boxed_816_; lean_object* v_res_817_; 
v_x_565__boxed_815_ = lean_unbox_usize(v_x_811_);
lean_dec(v_x_811_);
v_x_566__boxed_816_ = lean_unbox_usize(v_x_812_);
lean_dec(v_x_812_);
v_res_817_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0(v_00_u03b2_809_, v_x_810_, v_x_565__boxed_815_, v_x_566__boxed_816_, v_x_813_, v_x_814_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_818_, lean_object* v_n_819_, lean_object* v_k_820_, lean_object* v_v_821_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1___redArg(v_n_819_, v_k_820_, v_v_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_823_, size_t v_depth_824_, lean_object* v_keys_825_, lean_object* v_vals_826_, lean_object* v_heq_827_, lean_object* v_i_828_, lean_object* v_entries_829_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(v_depth_824_, v_keys_825_, v_vals_826_, v_i_828_, v_entries_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_831_, lean_object* v_depth_832_, lean_object* v_keys_833_, lean_object* v_vals_834_, lean_object* v_heq_835_, lean_object* v_i_836_, lean_object* v_entries_837_){
_start:
{
size_t v_depth_boxed_838_; lean_object* v_res_839_; 
v_depth_boxed_838_ = lean_unbox_usize(v_depth_832_);
lean_dec(v_depth_832_);
v_res_839_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2(v_00_u03b2_831_, v_depth_boxed_838_, v_keys_833_, v_vals_834_, v_heq_835_, v_i_836_, v_entries_837_);
lean_dec_ref(v_vals_834_);
lean_dec_ref(v_keys_833_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_840_, lean_object* v_x_841_, lean_object* v_x_842_, lean_object* v_x_843_, lean_object* v_x_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2___redArg(v_x_841_, v_x_842_, v_x_843_, v_x_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_mk_local_decl(lean_object* v_lctx_846_, lean_object* v_fvarId_847_, lean_object* v_userName_848_, lean_object* v_type_849_, uint8_t v_bi_850_){
_start:
{
uint8_t v___x_851_; lean_object* v___x_852_; 
v___x_851_ = 0;
v___x_852_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_846_, v_fvarId_847_, v_userName_848_, v_type_849_, v_bi_850_, v___x_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_mkLocalDeclExported___boxed(lean_object* v_lctx_853_, lean_object* v_fvarId_854_, lean_object* v_userName_855_, lean_object* v_type_856_, lean_object* v_bi_857_){
_start:
{
uint8_t v_bi_boxed_858_; lean_object* v_res_859_; 
v_bi_boxed_858_ = lean_unbox(v_bi_857_);
v_res_859_ = lean_local_ctx_mk_local_decl(v_lctx_853_, v_fvarId_854_, v_userName_855_, v_type_856_, v_bi_boxed_858_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLetDecl(lean_object* v_lctx_860_, lean_object* v_fvarId_861_, lean_object* v_userName_862_, lean_object* v_type_863_, lean_object* v_value_864_, uint8_t v_nondep_865_, uint8_t v_kind_866_){
_start:
{
lean_object* v_decls_867_; lean_object* v_fvarIdToDecl_868_; lean_object* v_auxDeclToFullName_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_881_; 
v_decls_867_ = lean_ctor_get(v_lctx_860_, 1);
v_fvarIdToDecl_868_ = lean_ctor_get(v_lctx_860_, 0);
v_auxDeclToFullName_869_ = lean_ctor_get(v_lctx_860_, 2);
v_isSharedCheck_881_ = !lean_is_exclusive(v_lctx_860_);
if (v_isSharedCheck_881_ == 0)
{
v___x_871_ = v_lctx_860_;
v_isShared_872_ = v_isSharedCheck_881_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_auxDeclToFullName_869_);
lean_inc(v_decls_867_);
lean_inc(v_fvarIdToDecl_868_);
lean_dec(v_lctx_860_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_881_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v_size_873_; lean_object* v_decl_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_879_; 
v_size_873_ = lean_ctor_get(v_decls_867_, 2);
lean_inc(v_fvarId_861_);
lean_inc(v_size_873_);
v_decl_874_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_decl_874_, 0, v_size_873_);
lean_ctor_set(v_decl_874_, 1, v_fvarId_861_);
lean_ctor_set(v_decl_874_, 2, v_userName_862_);
lean_ctor_set(v_decl_874_, 3, v_type_863_);
lean_ctor_set(v_decl_874_, 4, v_value_864_);
lean_ctor_set_uint8(v_decl_874_, sizeof(void*)*5, v_nondep_865_);
lean_ctor_set_uint8(v_decl_874_, sizeof(void*)*5 + 1, v_kind_866_);
lean_inc_ref(v_decl_874_);
v___x_875_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_868_, v_fvarId_861_, v_decl_874_);
v___x_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_876_, 0, v_decl_874_);
v___x_877_ = l_Lean_PersistentArray_push___redArg(v_decls_867_, v___x_876_);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 1, v___x_877_);
lean_ctor_set(v___x_871_, 0, v___x_875_);
v___x_879_ = v___x_871_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_875_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v___x_877_);
lean_ctor_set(v_reuseFailAlloc_880_, 2, v_auxDeclToFullName_869_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLetDecl___boxed(lean_object* v_lctx_882_, lean_object* v_fvarId_883_, lean_object* v_userName_884_, lean_object* v_type_885_, lean_object* v_value_886_, lean_object* v_nondep_887_, lean_object* v_kind_888_){
_start:
{
uint8_t v_nondep_boxed_889_; uint8_t v_kind_boxed_890_; lean_object* v_res_891_; 
v_nondep_boxed_889_ = lean_unbox(v_nondep_887_);
v_kind_boxed_890_ = lean_unbox(v_kind_888_);
v_res_891_ = l_Lean_LocalContext_mkLetDecl(v_lctx_882_, v_fvarId_883_, v_userName_884_, v_type_885_, v_value_886_, v_nondep_boxed_889_, v_kind_boxed_890_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_mk_let_decl(lean_object* v_lctx_892_, lean_object* v_fvarId_893_, lean_object* v_userName_894_, lean_object* v_type_895_, lean_object* v_value_896_, uint8_t v_nondep_897_){
_start:
{
uint8_t v___x_898_; lean_object* v___x_899_; 
v___x_898_ = 0;
v___x_899_ = l_Lean_LocalContext_mkLetDecl(v_lctx_892_, v_fvarId_893_, v_userName_894_, v_type_895_, v_value_896_, v_nondep_897_, v___x_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_mkLetDeclExported___boxed(lean_object* v_lctx_900_, lean_object* v_fvarId_901_, lean_object* v_userName_902_, lean_object* v_type_903_, lean_object* v_value_904_, lean_object* v_nondep_905_){
_start:
{
uint8_t v_nondep_boxed_906_; lean_object* v_res_907_; 
v_nondep_boxed_906_ = lean_unbox(v_nondep_905_);
v_res_907_ = lean_local_ctx_mk_let_decl(v_lctx_900_, v_fvarId_901_, v_userName_902_, v_type_903_, v_value_904_, v_nondep_boxed_906_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkAuxDecl(lean_object* v_lctx_908_, lean_object* v_fvarId_909_, lean_object* v_userName_910_, lean_object* v_type_911_, lean_object* v_fullName_912_){
_start:
{
lean_object* v_decls_913_; lean_object* v_fvarIdToDecl_914_; lean_object* v_auxDeclToFullName_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_930_; 
v_decls_913_ = lean_ctor_get(v_lctx_908_, 1);
v_fvarIdToDecl_914_ = lean_ctor_get(v_lctx_908_, 0);
v_auxDeclToFullName_915_ = lean_ctor_get(v_lctx_908_, 2);
v_isSharedCheck_930_ = !lean_is_exclusive(v_lctx_908_);
if (v_isSharedCheck_930_ == 0)
{
v___x_917_ = v_lctx_908_;
v_isShared_918_ = v_isSharedCheck_930_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_auxDeclToFullName_915_);
lean_inc(v_decls_913_);
lean_inc(v_fvarIdToDecl_914_);
lean_dec(v_lctx_908_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_930_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v_size_919_; uint8_t v___x_920_; uint8_t v___x_921_; lean_object* v_decl_922_; lean_object* v_auxDeclToFullName_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_928_; 
v_size_919_ = lean_ctor_get(v_decls_913_, 2);
v___x_920_ = 0;
v___x_921_ = 2;
lean_inc_n(v_fvarId_909_, 2);
lean_inc(v_size_919_);
v_decl_922_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_decl_922_, 0, v_size_919_);
lean_ctor_set(v_decl_922_, 1, v_fvarId_909_);
lean_ctor_set(v_decl_922_, 2, v_userName_910_);
lean_ctor_set(v_decl_922_, 3, v_type_911_);
lean_ctor_set_uint8(v_decl_922_, sizeof(void*)*4, v___x_920_);
lean_ctor_set_uint8(v_decl_922_, sizeof(void*)*4 + 1, v___x_921_);
v_auxDeclToFullName_923_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_909_, v_fullName_912_, v_auxDeclToFullName_915_);
lean_inc_ref(v_decl_922_);
v___x_924_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_914_, v_fvarId_909_, v_decl_922_);
v___x_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_925_, 0, v_decl_922_);
v___x_926_ = l_Lean_PersistentArray_push___redArg(v_decls_913_, v___x_925_);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 2, v_auxDeclToFullName_923_);
lean_ctor_set(v___x_917_, 1, v___x_926_);
lean_ctor_set(v___x_917_, 0, v___x_924_);
v___x_928_ = v___x_917_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_924_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v___x_926_);
lean_ctor_set(v_reuseFailAlloc_929_, 2, v_auxDeclToFullName_923_);
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
LEAN_EXPORT lean_object* l_Lean_LocalContext_addDecl(lean_object* v_lctx_931_, lean_object* v_newDecl_932_){
_start:
{
lean_object* v_decls_933_; lean_object* v_fvarIdToDecl_934_; lean_object* v_auxDeclToFullName_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_950_; 
v_decls_933_ = lean_ctor_get(v_lctx_931_, 1);
v_fvarIdToDecl_934_ = lean_ctor_get(v_lctx_931_, 0);
v_auxDeclToFullName_935_ = lean_ctor_get(v_lctx_931_, 2);
v_isSharedCheck_950_ = !lean_is_exclusive(v_lctx_931_);
if (v_isSharedCheck_950_ == 0)
{
v___x_937_ = v_lctx_931_;
v_isShared_938_ = v_isSharedCheck_950_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_auxDeclToFullName_935_);
lean_inc(v_decls_933_);
lean_inc(v_fvarIdToDecl_934_);
lean_dec(v_lctx_931_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_950_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v_size_939_; lean_object* v_newDecl_940_; lean_object* v___y_942_; lean_object* v_fvarId_949_; 
v_size_939_ = lean_ctor_get(v_decls_933_, 2);
lean_inc(v_size_939_);
v_newDecl_940_ = l_Lean_LocalDecl_setIndex(v_newDecl_932_, v_size_939_);
v_fvarId_949_ = lean_ctor_get(v_newDecl_940_, 1);
lean_inc(v_fvarId_949_);
v___y_942_ = v_fvarId_949_;
goto v___jp_941_;
v___jp_941_:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_947_; 
lean_inc_ref(v_newDecl_940_);
v___x_943_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_934_, v___y_942_, v_newDecl_940_);
v___x_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_944_, 0, v_newDecl_940_);
v___x_945_ = l_Lean_PersistentArray_push___redArg(v_decls_933_, v___x_944_);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 1, v___x_945_);
lean_ctor_set(v___x_937_, 0, v___x_943_);
v___x_947_ = v___x_937_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_943_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v___x_945_);
lean_ctor_set(v_reuseFailAlloc_948_, 2, v_auxDeclToFullName_935_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_951_, lean_object* v_vals_952_, lean_object* v_i_953_, lean_object* v_k_954_){
_start:
{
lean_object* v___x_955_; uint8_t v___x_956_; 
v___x_955_ = lean_array_get_size(v_keys_951_);
v___x_956_ = lean_nat_dec_lt(v_i_953_, v___x_955_);
if (v___x_956_ == 0)
{
lean_object* v___x_957_; 
lean_dec(v_i_953_);
v___x_957_ = lean_box(0);
return v___x_957_;
}
else
{
lean_object* v_k_x27_958_; uint8_t v___x_959_; 
v_k_x27_958_ = lean_array_fget_borrowed(v_keys_951_, v_i_953_);
v___x_959_ = l_Lean_instBEqFVarId_beq(v_k_954_, v_k_x27_958_);
if (v___x_959_ == 0)
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = lean_unsigned_to_nat(1u);
v___x_961_ = lean_nat_add(v_i_953_, v___x_960_);
lean_dec(v_i_953_);
v_i_953_ = v___x_961_;
goto _start;
}
else
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = lean_array_fget_borrowed(v_vals_952_, v_i_953_);
lean_dec(v_i_953_);
lean_inc(v___x_963_);
v___x_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
return v___x_964_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_965_, lean_object* v_vals_966_, lean_object* v_i_967_, lean_object* v_k_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_965_, v_vals_966_, v_i_967_, v_k_968_);
lean_dec(v_k_968_);
lean_dec_ref(v_vals_966_);
lean_dec_ref(v_keys_965_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(lean_object* v_x_970_, size_t v_x_971_, lean_object* v_x_972_){
_start:
{
if (lean_obj_tag(v_x_970_) == 0)
{
lean_object* v_es_973_; lean_object* v___x_974_; size_t v___x_975_; size_t v___x_976_; lean_object* v_j_977_; lean_object* v___x_978_; 
v_es_973_ = lean_ctor_get(v_x_970_, 0);
v___x_974_ = lean_box(2);
v___x_975_ = ((size_t)31ULL);
v___x_976_ = lean_usize_land(v_x_971_, v___x_975_);
v_j_977_ = lean_usize_to_nat(v___x_976_);
v___x_978_ = lean_array_get_borrowed(v___x_974_, v_es_973_, v_j_977_);
lean_dec(v_j_977_);
switch(lean_obj_tag(v___x_978_))
{
case 0:
{
lean_object* v_key_979_; lean_object* v_val_980_; uint8_t v___x_981_; 
v_key_979_ = lean_ctor_get(v___x_978_, 0);
v_val_980_ = lean_ctor_get(v___x_978_, 1);
v___x_981_ = l_Lean_instBEqFVarId_beq(v_x_972_, v_key_979_);
if (v___x_981_ == 0)
{
lean_object* v___x_982_; 
v___x_982_ = lean_box(0);
return v___x_982_;
}
else
{
lean_object* v___x_983_; 
lean_inc(v_val_980_);
v___x_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_983_, 0, v_val_980_);
return v___x_983_;
}
}
case 1:
{
lean_object* v_node_984_; size_t v___x_985_; size_t v___x_986_; 
v_node_984_ = lean_ctor_get(v___x_978_, 0);
v___x_985_ = ((size_t)5ULL);
v___x_986_ = lean_usize_shift_right(v_x_971_, v___x_985_);
v_x_970_ = v_node_984_;
v_x_971_ = v___x_986_;
goto _start;
}
default: 
{
lean_object* v___x_988_; 
v___x_988_ = lean_box(0);
return v___x_988_;
}
}
}
else
{
lean_object* v_ks_989_; lean_object* v_vs_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v_ks_989_ = lean_ctor_get(v_x_970_, 0);
v_vs_990_ = lean_ctor_get(v_x_970_, 1);
v___x_991_ = lean_unsigned_to_nat(0u);
v___x_992_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(v_ks_989_, v_vs_990_, v___x_991_, v_x_972_);
return v___x_992_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_993_, lean_object* v_x_994_, lean_object* v_x_995_){
_start:
{
size_t v_x_135__boxed_996_; lean_object* v_res_997_; 
v_x_135__boxed_996_ = lean_unbox_usize(v_x_994_);
lean_dec(v_x_994_);
v_res_997_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(v_x_993_, v_x_135__boxed_996_, v_x_995_);
lean_dec(v_x_995_);
lean_dec_ref(v_x_993_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(lean_object* v_x_998_, lean_object* v_x_999_){
_start:
{
uint64_t v___x_1000_; size_t v___x_1001_; lean_object* v___x_1002_; 
v___x_1000_ = l_Lean_instHashableFVarId_hash(v_x_999_);
v___x_1001_ = lean_uint64_to_usize(v___x_1000_);
v___x_1002_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(v_x_998_, v___x_1001_, v_x_999_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg___boxed(lean_object* v_x_1003_, lean_object* v_x_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_x_1003_, v_x_1004_);
lean_dec(v_x_1004_);
lean_dec_ref(v_x_1003_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_find(lean_object* v_lctx_1006_, lean_object* v_fvarId_1007_){
_start:
{
lean_object* v_fvarIdToDecl_1008_; lean_object* v___x_1009_; 
v_fvarIdToDecl_1008_ = lean_ctor_get(v_lctx_1006_, 0);
lean_inc_ref(v_fvarIdToDecl_1008_);
lean_dec_ref(v_lctx_1006_);
v___x_1009_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_fvarIdToDecl_1008_, v_fvarId_1007_);
lean_dec(v_fvarId_1007_);
lean_dec_ref(v_fvarIdToDecl_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0(lean_object* v_00_u03b2_1010_, lean_object* v_x_1011_, lean_object* v_x_1012_){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_x_1011_, v_x_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___boxed(lean_object* v_00_u03b2_1014_, lean_object* v_x_1015_, lean_object* v_x_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0(v_00_u03b2_1014_, v_x_1015_, v_x_1016_);
lean_dec(v_x_1016_);
lean_dec_ref(v_x_1015_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1018_, lean_object* v_x_1019_, size_t v_x_1020_, lean_object* v_x_1021_){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(v_x_1019_, v_x_1020_, v_x_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1023_, lean_object* v_x_1024_, lean_object* v_x_1025_, lean_object* v_x_1026_){
_start:
{
size_t v_x_204__boxed_1027_; lean_object* v_res_1028_; 
v_x_204__boxed_1027_ = lean_unbox_usize(v_x_1025_);
lean_dec(v_x_1025_);
v_res_1028_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0(v_00_u03b2_1023_, v_x_1024_, v_x_204__boxed_1027_, v_x_1026_);
lean_dec(v_x_1026_);
lean_dec_ref(v_x_1024_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1029_, lean_object* v_keys_1030_, lean_object* v_vals_1031_, lean_object* v_heq_1032_, lean_object* v_i_1033_, lean_object* v_k_1034_){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1030_, v_vals_1031_, v_i_1033_, v_k_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1036_, lean_object* v_keys_1037_, lean_object* v_vals_1038_, lean_object* v_heq_1039_, lean_object* v_i_1040_, lean_object* v_k_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1036_, v_keys_1037_, v_vals_1038_, v_heq_1039_, v_i_1040_, v_k_1041_);
lean_dec(v_k_1041_);
lean_dec_ref(v_vals_1038_);
lean_dec_ref(v_keys_1037_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFVar_x3f(lean_object* v_lctx_1043_, lean_object* v_e_1044_){
_start:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = l_Lean_Expr_fvarId_x21(v_e_1044_);
v___x_1046_ = lean_local_ctx_find(v_lctx_1043_, v___x_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFVar_x3f___boxed(lean_object* v_lctx_1047_, lean_object* v_e_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_1047_, v_e_1048_);
lean_dec_ref(v_e_1048_);
return v_res_1049_;
}
}
static lean_object* _init_l_Lean_LocalContext_get_x21___closed__2(void){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1052_ = ((lean_object*)(l_Lean_LocalContext_get_x21___closed__1));
v___x_1053_ = lean_unsigned_to_nat(14u);
v___x_1054_ = lean_unsigned_to_nat(340u);
v___x_1055_ = ((lean_object*)(l_Lean_LocalContext_get_x21___closed__0));
v___x_1056_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_1057_ = l_mkPanicMessageWithDecl(v___x_1056_, v___x_1055_, v___x_1054_, v___x_1053_, v___x_1052_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_get_x21(lean_object* v_lctx_1058_, lean_object* v_fvarId_1059_){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = lean_local_ctx_find(v_lctx_1058_, v_fvarId_1059_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = lean_obj_once(&l_Lean_LocalContext_get_x21___closed__2, &l_Lean_LocalContext_get_x21___closed__2_once, _init_l_Lean_LocalContext_get_x21___closed__2);
v___x_1062_ = l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(v___x_1061_);
return v___x_1062_;
}
else
{
lean_object* v_val_1063_; 
v_val_1063_ = lean_ctor_get(v___x_1060_, 0);
lean_inc(v_val_1063_);
lean_dec_ref_known(v___x_1060_, 1);
return v_val_1063_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVar_x21(lean_object* v_lctx_1064_, lean_object* v_e_1065_){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = l_Lean_Expr_fvarId_x21(v_e_1065_);
v___x_1067_ = l_Lean_LocalContext_get_x21(v_lctx_1064_, v___x_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVar_x21___boxed(lean_object* v_lctx_1068_, lean_object* v_e_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l_Lean_LocalContext_getFVar_x21(v_lctx_1068_, v_e_1069_);
lean_dec_ref(v_e_1069_);
return v_res_1070_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1071_, lean_object* v_i_1072_, lean_object* v_k_1073_){
_start:
{
lean_object* v___x_1074_; uint8_t v___x_1075_; 
v___x_1074_ = lean_array_get_size(v_keys_1071_);
v___x_1075_ = lean_nat_dec_lt(v_i_1072_, v___x_1074_);
if (v___x_1075_ == 0)
{
lean_dec(v_i_1072_);
return v___x_1075_;
}
else
{
lean_object* v_k_x27_1076_; uint8_t v___x_1077_; 
v_k_x27_1076_ = lean_array_fget_borrowed(v_keys_1071_, v_i_1072_);
v___x_1077_ = l_Lean_instBEqFVarId_beq(v_k_1073_, v_k_x27_1076_);
if (v___x_1077_ == 0)
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = lean_unsigned_to_nat(1u);
v___x_1079_ = lean_nat_add(v_i_1072_, v___x_1078_);
lean_dec(v_i_1072_);
v_i_1072_ = v___x_1079_;
goto _start;
}
else
{
lean_dec(v_i_1072_);
return v___x_1075_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1081_, lean_object* v_i_1082_, lean_object* v_k_1083_){
_start:
{
uint8_t v_res_1084_; lean_object* v_r_1085_; 
v_res_1084_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(v_keys_1081_, v_i_1082_, v_k_1083_);
lean_dec(v_k_1083_);
lean_dec_ref(v_keys_1081_);
v_r_1085_ = lean_box(v_res_1084_);
return v_r_1085_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(lean_object* v_x_1086_, size_t v_x_1087_, lean_object* v_x_1088_){
_start:
{
if (lean_obj_tag(v_x_1086_) == 0)
{
lean_object* v_es_1089_; lean_object* v___x_1090_; size_t v___x_1091_; size_t v___x_1092_; lean_object* v_j_1093_; lean_object* v___x_1094_; 
v_es_1089_ = lean_ctor_get(v_x_1086_, 0);
v___x_1090_ = lean_box(2);
v___x_1091_ = ((size_t)31ULL);
v___x_1092_ = lean_usize_land(v_x_1087_, v___x_1091_);
v_j_1093_ = lean_usize_to_nat(v___x_1092_);
v___x_1094_ = lean_array_get_borrowed(v___x_1090_, v_es_1089_, v_j_1093_);
lean_dec(v_j_1093_);
switch(lean_obj_tag(v___x_1094_))
{
case 0:
{
lean_object* v_key_1095_; uint8_t v___x_1096_; 
v_key_1095_ = lean_ctor_get(v___x_1094_, 0);
v___x_1096_ = l_Lean_instBEqFVarId_beq(v_x_1088_, v_key_1095_);
return v___x_1096_;
}
case 1:
{
lean_object* v_node_1097_; size_t v___x_1098_; size_t v___x_1099_; 
v_node_1097_ = lean_ctor_get(v___x_1094_, 0);
v___x_1098_ = ((size_t)5ULL);
v___x_1099_ = lean_usize_shift_right(v_x_1087_, v___x_1098_);
v_x_1086_ = v_node_1097_;
v_x_1087_ = v___x_1099_;
goto _start;
}
default: 
{
uint8_t v___x_1101_; 
v___x_1101_ = 0;
return v___x_1101_;
}
}
}
else
{
lean_object* v_ks_1102_; lean_object* v___x_1103_; uint8_t v___x_1104_; 
v_ks_1102_ = lean_ctor_get(v_x_1086_, 0);
v___x_1103_ = lean_unsigned_to_nat(0u);
v___x_1104_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(v_ks_1102_, v___x_1103_, v_x_1088_);
return v___x_1104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg___boxed(lean_object* v_x_1105_, lean_object* v_x_1106_, lean_object* v_x_1107_){
_start:
{
size_t v_x_119__boxed_1108_; uint8_t v_res_1109_; lean_object* v_r_1110_; 
v_x_119__boxed_1108_ = lean_unbox_usize(v_x_1106_);
lean_dec(v_x_1106_);
v_res_1109_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(v_x_1105_, v_x_119__boxed_1108_, v_x_1107_);
lean_dec(v_x_1107_);
lean_dec_ref(v_x_1105_);
v_r_1110_ = lean_box(v_res_1109_);
return v_r_1110_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(lean_object* v_x_1111_, lean_object* v_x_1112_){
_start:
{
uint64_t v___x_1113_; size_t v___x_1114_; uint8_t v___x_1115_; 
v___x_1113_ = l_Lean_instHashableFVarId_hash(v_x_1112_);
v___x_1114_ = lean_uint64_to_usize(v___x_1113_);
v___x_1115_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(v_x_1111_, v___x_1114_, v_x_1112_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg___boxed(lean_object* v_x_1116_, lean_object* v_x_1117_){
_start:
{
uint8_t v_res_1118_; lean_object* v_r_1119_; 
v_res_1118_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(v_x_1116_, v_x_1117_);
lean_dec(v_x_1117_);
lean_dec_ref(v_x_1116_);
v_r_1119_ = lean_box(v_res_1118_);
return v_r_1119_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_contains(lean_object* v_lctx_1120_, lean_object* v_fvarId_1121_){
_start:
{
lean_object* v_fvarIdToDecl_1122_; uint8_t v___x_1123_; 
v_fvarIdToDecl_1122_ = lean_ctor_get(v_lctx_1120_, 0);
v___x_1123_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(v_fvarIdToDecl_1122_, v_fvarId_1121_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_contains___boxed(lean_object* v_lctx_1124_, lean_object* v_fvarId_1125_){
_start:
{
uint8_t v_res_1126_; lean_object* v_r_1127_; 
v_res_1126_ = l_Lean_LocalContext_contains(v_lctx_1124_, v_fvarId_1125_);
lean_dec(v_fvarId_1125_);
lean_dec_ref(v_lctx_1124_);
v_r_1127_ = lean_box(v_res_1126_);
return v_r_1127_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0(lean_object* v_00_u03b2_1128_, lean_object* v_x_1129_, lean_object* v_x_1130_){
_start:
{
uint8_t v___x_1131_; 
v___x_1131_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(v_x_1129_, v_x_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___boxed(lean_object* v_00_u03b2_1132_, lean_object* v_x_1133_, lean_object* v_x_1134_){
_start:
{
uint8_t v_res_1135_; lean_object* v_r_1136_; 
v_res_1135_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0(v_00_u03b2_1132_, v_x_1133_, v_x_1134_);
lean_dec(v_x_1134_);
lean_dec_ref(v_x_1133_);
v_r_1136_ = lean_box(v_res_1135_);
return v_r_1136_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0(lean_object* v_00_u03b2_1137_, lean_object* v_x_1138_, size_t v_x_1139_, lean_object* v_x_1140_){
_start:
{
uint8_t v___x_1141_; 
v___x_1141_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(v_x_1138_, v_x_1139_, v_x_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1142_, lean_object* v_x_1143_, lean_object* v_x_1144_, lean_object* v_x_1145_){
_start:
{
size_t v_x_182__boxed_1146_; uint8_t v_res_1147_; lean_object* v_r_1148_; 
v_x_182__boxed_1146_ = lean_unbox_usize(v_x_1144_);
lean_dec(v_x_1144_);
v_res_1147_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0(v_00_u03b2_1142_, v_x_1143_, v_x_182__boxed_1146_, v_x_1145_);
lean_dec(v_x_1145_);
lean_dec_ref(v_x_1143_);
v_r_1148_ = lean_box(v_res_1147_);
return v_r_1148_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1149_, lean_object* v_keys_1150_, lean_object* v_vals_1151_, lean_object* v_heq_1152_, lean_object* v_i_1153_, lean_object* v_k_1154_){
_start:
{
uint8_t v___x_1155_; 
v___x_1155_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(v_keys_1150_, v_i_1153_, v_k_1154_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1156_, lean_object* v_keys_1157_, lean_object* v_vals_1158_, lean_object* v_heq_1159_, lean_object* v_i_1160_, lean_object* v_k_1161_){
_start:
{
uint8_t v_res_1162_; lean_object* v_r_1163_; 
v_res_1162_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1(v_00_u03b2_1156_, v_keys_1157_, v_vals_1158_, v_heq_1159_, v_i_1160_, v_k_1161_);
lean_dec(v_k_1161_);
lean_dec_ref(v_vals_1158_);
lean_dec_ref(v_keys_1157_);
v_r_1163_ = lean_box(v_res_1162_);
return v_r_1163_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_containsFVar(lean_object* v_lctx_1164_, lean_object* v_e_1165_){
_start:
{
lean_object* v___x_1166_; uint8_t v___x_1167_; 
v___x_1166_ = l_Lean_Expr_fvarId_x21(v_e_1165_);
v___x_1167_ = l_Lean_LocalContext_contains(v_lctx_1164_, v___x_1166_);
lean_dec(v___x_1166_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_containsFVar___boxed(lean_object* v_lctx_1168_, lean_object* v_e_1169_){
_start:
{
uint8_t v_res_1170_; lean_object* v_r_1171_; 
v_res_1170_ = l_Lean_LocalContext_containsFVar(v_lctx_1168_, v_e_1169_);
lean_dec_ref(v_e_1169_);
lean_dec_ref(v_lctx_1168_);
v_r_1171_ = lean_box(v_res_1170_);
return v_r_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(lean_object* v_as_1172_, size_t v_i_1173_, size_t v_stop_1174_, lean_object* v_b_1175_){
_start:
{
lean_object* v___y_1177_; uint8_t v___x_1181_; 
v___x_1181_ = lean_usize_dec_eq(v_i_1173_, v_stop_1174_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; 
v___x_1182_ = lean_array_uget_borrowed(v_as_1172_, v_i_1173_);
if (lean_obj_tag(v___x_1182_) == 0)
{
v___y_1177_ = v_b_1175_;
goto v___jp_1176_;
}
else
{
lean_object* v_val_1183_; lean_object* v_fvarId_1184_; lean_object* v___x_1185_; 
v_val_1183_ = lean_ctor_get(v___x_1182_, 0);
v_fvarId_1184_ = lean_ctor_get(v_val_1183_, 1);
lean_inc(v_fvarId_1184_);
v___x_1185_ = lean_array_push(v_b_1175_, v_fvarId_1184_);
v___y_1177_ = v___x_1185_;
goto v___jp_1176_;
}
}
else
{
return v_b_1175_;
}
v___jp_1176_:
{
size_t v___x_1178_; size_t v___x_1179_; 
v___x_1178_ = ((size_t)1ULL);
v___x_1179_ = lean_usize_add(v_i_1173_, v___x_1178_);
v_i_1173_ = v___x_1179_;
v_b_1175_ = v___y_1177_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1___boxed(lean_object* v_as_1186_, lean_object* v_i_1187_, lean_object* v_stop_1188_, lean_object* v_b_1189_){
_start:
{
size_t v_i_boxed_1190_; size_t v_stop_boxed_1191_; lean_object* v_res_1192_; 
v_i_boxed_1190_ = lean_unbox_usize(v_i_1187_);
lean_dec(v_i_1187_);
v_stop_boxed_1191_ = lean_unbox_usize(v_stop_1188_);
lean_dec(v_stop_1188_);
v_res_1192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_as_1186_, v_i_boxed_1190_, v_stop_boxed_1191_, v_b_1189_);
lean_dec_ref(v_as_1186_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(lean_object* v_x_1193_, lean_object* v_x_1194_){
_start:
{
if (lean_obj_tag(v_x_1193_) == 0)
{
lean_object* v_cs_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; uint8_t v___x_1198_; 
v_cs_1195_ = lean_ctor_get(v_x_1193_, 0);
v___x_1196_ = lean_unsigned_to_nat(0u);
v___x_1197_ = lean_array_get_size(v_cs_1195_);
v___x_1198_ = lean_nat_dec_lt(v___x_1196_, v___x_1197_);
if (v___x_1198_ == 0)
{
return v_x_1194_;
}
else
{
size_t v___x_1199_; size_t v___x_1200_; lean_object* v___x_1201_; 
v___x_1199_ = ((size_t)0ULL);
v___x_1200_ = lean_usize_of_nat(v___x_1197_);
v___x_1201_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_cs_1195_, v___x_1199_, v___x_1200_, v_x_1194_);
return v___x_1201_;
}
}
else
{
lean_object* v_vs_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; uint8_t v___x_1205_; 
v_vs_1202_ = lean_ctor_get(v_x_1193_, 0);
v___x_1203_ = lean_unsigned_to_nat(0u);
v___x_1204_ = lean_array_get_size(v_vs_1202_);
v___x_1205_ = lean_nat_dec_lt(v___x_1203_, v___x_1204_);
if (v___x_1205_ == 0)
{
return v_x_1194_;
}
else
{
size_t v___x_1206_; size_t v___x_1207_; lean_object* v___x_1208_; 
v___x_1206_ = ((size_t)0ULL);
v___x_1207_ = lean_usize_of_nat(v___x_1204_);
v___x_1208_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_vs_1202_, v___x_1206_, v___x_1207_, v_x_1194_);
return v___x_1208_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(lean_object* v_as_1209_, size_t v_i_1210_, size_t v_stop_1211_, lean_object* v_b_1212_){
_start:
{
uint8_t v___x_1213_; 
v___x_1213_ = lean_usize_dec_eq(v_i_1210_, v_stop_1211_);
if (v___x_1213_ == 0)
{
lean_object* v___x_1214_; lean_object* v___x_1215_; size_t v___x_1216_; size_t v___x_1217_; 
v___x_1214_ = lean_array_uget_borrowed(v_as_1209_, v_i_1210_);
v___x_1215_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(v___x_1214_, v_b_1212_);
v___x_1216_ = ((size_t)1ULL);
v___x_1217_ = lean_usize_add(v_i_1210_, v___x_1216_);
v_i_1210_ = v___x_1217_;
v_b_1212_ = v___x_1215_;
goto _start;
}
else
{
return v_b_1212_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1___boxed(lean_object* v_as_1219_, lean_object* v_i_1220_, lean_object* v_stop_1221_, lean_object* v_b_1222_){
_start:
{
size_t v_i_boxed_1223_; size_t v_stop_boxed_1224_; lean_object* v_res_1225_; 
v_i_boxed_1223_ = lean_unbox_usize(v_i_1220_);
lean_dec(v_i_1220_);
v_stop_boxed_1224_ = lean_unbox_usize(v_stop_1221_);
lean_dec(v_stop_1221_);
v_res_1225_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_as_1219_, v_i_boxed_1223_, v_stop_boxed_1224_, v_b_1222_);
lean_dec_ref(v_as_1219_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2___boxed(lean_object* v_x_1226_, lean_object* v_x_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(v_x_1226_, v_x_1227_);
lean_dec_ref(v_x_1226_);
return v_res_1228_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(lean_object* v_x_1230_, size_t v_x_1231_, size_t v_x_1232_, lean_object* v_x_1233_){
_start:
{
if (lean_obj_tag(v_x_1230_) == 0)
{
lean_object* v_cs_1234_; lean_object* v___x_1235_; size_t v___x_1236_; lean_object* v_j_1237_; lean_object* v___x_1238_; size_t v___x_1239_; size_t v___x_1240_; size_t v___x_1241_; size_t v___x_1242_; size_t v___x_1243_; size_t v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; uint8_t v___x_1249_; 
v_cs_1234_ = lean_ctor_get(v_x_1230_, 0);
v___x_1235_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0);
v___x_1236_ = lean_usize_shift_right(v_x_1231_, v_x_1232_);
v_j_1237_ = lean_usize_to_nat(v___x_1236_);
v___x_1238_ = lean_array_get_borrowed(v___x_1235_, v_cs_1234_, v_j_1237_);
v___x_1239_ = ((size_t)1ULL);
v___x_1240_ = lean_usize_shift_left(v___x_1239_, v_x_1232_);
v___x_1241_ = lean_usize_sub(v___x_1240_, v___x_1239_);
v___x_1242_ = lean_usize_land(v_x_1231_, v___x_1241_);
v___x_1243_ = ((size_t)5ULL);
v___x_1244_ = lean_usize_sub(v_x_1232_, v___x_1243_);
v___x_1245_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(v___x_1238_, v___x_1242_, v___x_1244_, v_x_1233_);
v___x_1246_ = lean_unsigned_to_nat(1u);
v___x_1247_ = lean_nat_add(v_j_1237_, v___x_1246_);
lean_dec(v_j_1237_);
v___x_1248_ = lean_array_get_size(v_cs_1234_);
v___x_1249_ = lean_nat_dec_lt(v___x_1247_, v___x_1248_);
if (v___x_1249_ == 0)
{
lean_dec(v___x_1247_);
return v___x_1245_;
}
else
{
size_t v___x_1250_; size_t v___x_1251_; lean_object* v___x_1252_; 
v___x_1250_ = lean_usize_of_nat(v___x_1247_);
lean_dec(v___x_1247_);
v___x_1251_ = lean_usize_of_nat(v___x_1248_);
v___x_1252_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_cs_1234_, v___x_1250_, v___x_1251_, v___x_1245_);
return v___x_1252_;
}
}
else
{
lean_object* v_vs_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; uint8_t v___x_1256_; 
v_vs_1253_ = lean_ctor_get(v_x_1230_, 0);
v___x_1254_ = lean_usize_to_nat(v_x_1231_);
v___x_1255_ = lean_array_get_size(v_vs_1253_);
v___x_1256_ = lean_nat_dec_lt(v___x_1254_, v___x_1255_);
if (v___x_1256_ == 0)
{
lean_dec(v___x_1254_);
return v_x_1233_;
}
else
{
size_t v___x_1257_; size_t v___x_1258_; lean_object* v___x_1259_; 
v___x_1257_ = lean_usize_of_nat(v___x_1254_);
lean_dec(v___x_1254_);
v___x_1258_ = lean_usize_of_nat(v___x_1255_);
v___x_1259_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_vs_1253_, v___x_1257_, v___x_1258_, v_x_1233_);
return v___x_1259_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___boxed(lean_object* v_x_1260_, lean_object* v_x_1261_, lean_object* v_x_1262_, lean_object* v_x_1263_){
_start:
{
size_t v_x_1260__boxed_1264_; size_t v_x_1261__boxed_1265_; lean_object* v_res_1266_; 
v_x_1260__boxed_1264_ = lean_unbox_usize(v_x_1261_);
lean_dec(v_x_1261_);
v_x_1261__boxed_1265_ = lean_unbox_usize(v_x_1262_);
lean_dec(v_x_1262_);
v_res_1266_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(v_x_1260_, v_x_1260__boxed_1264_, v_x_1261__boxed_1265_, v_x_1263_);
lean_dec_ref(v_x_1260_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0(lean_object* v_t_1267_, lean_object* v_init_1268_, lean_object* v_start_1269_){
_start:
{
lean_object* v___x_1270_; uint8_t v___x_1271_; 
v___x_1270_ = lean_unsigned_to_nat(0u);
v___x_1271_ = lean_nat_dec_eq(v_start_1269_, v___x_1270_);
if (v___x_1271_ == 0)
{
lean_object* v_root_1272_; lean_object* v_tail_1273_; size_t v_shift_1274_; lean_object* v_tailOff_1275_; uint8_t v___x_1276_; 
v_root_1272_ = lean_ctor_get(v_t_1267_, 0);
v_tail_1273_ = lean_ctor_get(v_t_1267_, 1);
v_shift_1274_ = lean_ctor_get_usize(v_t_1267_, 4);
v_tailOff_1275_ = lean_ctor_get(v_t_1267_, 3);
v___x_1276_ = lean_nat_dec_le(v_tailOff_1275_, v_start_1269_);
if (v___x_1276_ == 0)
{
size_t v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; uint8_t v___x_1280_; 
v___x_1277_ = lean_usize_of_nat(v_start_1269_);
v___x_1278_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(v_root_1272_, v___x_1277_, v_shift_1274_, v_init_1268_);
v___x_1279_ = lean_array_get_size(v_tail_1273_);
v___x_1280_ = lean_nat_dec_lt(v___x_1270_, v___x_1279_);
if (v___x_1280_ == 0)
{
return v___x_1278_;
}
else
{
size_t v___x_1281_; size_t v___x_1282_; lean_object* v___x_1283_; 
v___x_1281_ = ((size_t)0ULL);
v___x_1282_ = lean_usize_of_nat(v___x_1279_);
v___x_1283_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1273_, v___x_1281_, v___x_1282_, v___x_1278_);
return v___x_1283_;
}
}
else
{
lean_object* v___x_1284_; lean_object* v___x_1285_; uint8_t v___x_1286_; 
v___x_1284_ = lean_nat_sub(v_start_1269_, v_tailOff_1275_);
v___x_1285_ = lean_array_get_size(v_tail_1273_);
v___x_1286_ = lean_nat_dec_lt(v___x_1284_, v___x_1285_);
if (v___x_1286_ == 0)
{
lean_dec(v___x_1284_);
return v_init_1268_;
}
else
{
size_t v___x_1287_; size_t v___x_1288_; lean_object* v___x_1289_; 
v___x_1287_ = lean_usize_of_nat(v___x_1284_);
lean_dec(v___x_1284_);
v___x_1288_ = lean_usize_of_nat(v___x_1285_);
v___x_1289_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1273_, v___x_1287_, v___x_1288_, v_init_1268_);
return v___x_1289_;
}
}
}
else
{
lean_object* v_root_1290_; lean_object* v_tail_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; uint8_t v___x_1294_; 
v_root_1290_ = lean_ctor_get(v_t_1267_, 0);
v_tail_1291_ = lean_ctor_get(v_t_1267_, 1);
v___x_1292_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(v_root_1290_, v_init_1268_);
v___x_1293_ = lean_array_get_size(v_tail_1291_);
v___x_1294_ = lean_nat_dec_lt(v___x_1270_, v___x_1293_);
if (v___x_1294_ == 0)
{
return v___x_1292_;
}
else
{
size_t v___x_1295_; size_t v___x_1296_; lean_object* v___x_1297_; 
v___x_1295_ = ((size_t)0ULL);
v___x_1296_ = lean_usize_of_nat(v___x_1293_);
v___x_1297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1291_, v___x_1295_, v___x_1296_, v___x_1292_);
return v___x_1297_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0___boxed(lean_object* v_t_1298_, lean_object* v_init_1299_, lean_object* v_start_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0(v_t_1298_, v_init_1299_, v_start_1300_);
lean_dec(v_start_1300_);
lean_dec_ref(v_t_1298_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVarIds(lean_object* v_lctx_1304_){
_start:
{
lean_object* v_decls_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v_decls_1305_ = lean_ctor_get(v_lctx_1304_, 1);
v___x_1306_ = lean_unsigned_to_nat(0u);
v___x_1307_ = ((lean_object*)(l_Lean_LocalContext_getFVarIds___closed__0));
v___x_1308_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0(v_decls_1305_, v___x_1307_, v___x_1306_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVarIds___boxed(lean_object* v_lctx_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Lean_LocalContext_getFVarIds(v_lctx_1309_);
lean_dec_ref(v_lctx_1309_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0(size_t v_sz_1311_, size_t v_i_1312_, lean_object* v_bs_1313_){
_start:
{
uint8_t v___x_1314_; 
v___x_1314_ = lean_usize_dec_lt(v_i_1312_, v_sz_1311_);
if (v___x_1314_ == 0)
{
return v_bs_1313_;
}
else
{
lean_object* v_v_1315_; lean_object* v___x_1316_; lean_object* v_bs_x27_1317_; lean_object* v___x_1318_; size_t v___x_1319_; size_t v___x_1320_; lean_object* v___x_1321_; 
v_v_1315_ = lean_array_uget(v_bs_1313_, v_i_1312_);
v___x_1316_ = lean_unsigned_to_nat(0u);
v_bs_x27_1317_ = lean_array_uset(v_bs_1313_, v_i_1312_, v___x_1316_);
v___x_1318_ = l_Lean_mkFVar(v_v_1315_);
v___x_1319_ = ((size_t)1ULL);
v___x_1320_ = lean_usize_add(v_i_1312_, v___x_1319_);
v___x_1321_ = lean_array_uset(v_bs_x27_1317_, v_i_1312_, v___x_1318_);
v_i_1312_ = v___x_1320_;
v_bs_1313_ = v___x_1321_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0___boxed(lean_object* v_sz_1323_, lean_object* v_i_1324_, lean_object* v_bs_1325_){
_start:
{
size_t v_sz_boxed_1326_; size_t v_i_boxed_1327_; lean_object* v_res_1328_; 
v_sz_boxed_1326_ = lean_unbox_usize(v_sz_1323_);
lean_dec(v_sz_1323_);
v_i_boxed_1327_ = lean_unbox_usize(v_i_1324_);
lean_dec(v_i_1324_);
v_res_1328_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0(v_sz_boxed_1326_, v_i_boxed_1327_, v_bs_1325_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVars(lean_object* v_lctx_1329_){
_start:
{
lean_object* v___x_1330_; size_t v_sz_1331_; size_t v___x_1332_; lean_object* v___x_1333_; 
v___x_1330_ = l_Lean_LocalContext_getFVarIds(v_lctx_1329_);
v_sz_1331_ = lean_array_size(v___x_1330_);
v___x_1332_ = ((size_t)0ULL);
v___x_1333_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0(v_sz_1331_, v___x_1332_, v___x_1330_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVars___boxed(lean_object* v_lctx_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_Lean_LocalContext_getFVars(v_lctx_1334_);
lean_dec_ref(v_lctx_1334_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(lean_object* v_a_1336_){
_start:
{
lean_object* v_size_1337_; lean_object* v___x_1338_; uint8_t v___x_1339_; 
v_size_1337_ = lean_ctor_get(v_a_1336_, 2);
v___x_1338_ = lean_unsigned_to_nat(0u);
v___x_1339_ = lean_nat_dec_eq(v_size_1337_, v___x_1338_);
if (v___x_1339_ == 0)
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1340_ = lean_box(0);
v___x_1341_ = lean_unsigned_to_nat(1u);
v___x_1342_ = lean_nat_sub(v_size_1337_, v___x_1341_);
v___x_1343_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1340_, v_a_1336_, v___x_1342_);
lean_dec(v___x_1342_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v___x_1344_; 
v___x_1344_ = l_Lean_PersistentArray_pop___redArg(v_a_1336_);
v_a_1336_ = v___x_1344_;
goto _start;
}
else
{
lean_dec_ref_known(v___x_1343_, 1);
return v_a_1336_;
}
}
else
{
return v_a_1336_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(lean_object* v_k_1346_, lean_object* v_t_1347_){
_start:
{
if (lean_obj_tag(v_t_1347_) == 0)
{
lean_object* v_k_1348_; lean_object* v_v_1349_; lean_object* v_l_1350_; lean_object* v_r_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_2005_; 
v_k_1348_ = lean_ctor_get(v_t_1347_, 1);
v_v_1349_ = lean_ctor_get(v_t_1347_, 2);
v_l_1350_ = lean_ctor_get(v_t_1347_, 3);
v_r_1351_ = lean_ctor_get(v_t_1347_, 4);
v_isSharedCheck_2005_ = !lean_is_exclusive(v_t_1347_);
if (v_isSharedCheck_2005_ == 0)
{
lean_object* v_unused_2006_; 
v_unused_2006_ = lean_ctor_get(v_t_1347_, 0);
lean_dec(v_unused_2006_);
v___x_1353_ = v_t_1347_;
v_isShared_1354_ = v_isSharedCheck_2005_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_r_1351_);
lean_inc(v_l_1350_);
lean_inc(v_v_1349_);
lean_inc(v_k_1348_);
lean_dec(v_t_1347_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_2005_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
uint8_t v___x_1355_; 
v___x_1355_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1346_, v_k_1348_);
switch(v___x_1355_)
{
case 0:
{
lean_object* v_impl_1356_; lean_object* v___x_1357_; 
v_impl_1356_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_1346_, v_l_1350_);
v___x_1357_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1356_) == 0)
{
if (lean_obj_tag(v_r_1351_) == 0)
{
lean_object* v_size_1358_; lean_object* v_size_1359_; lean_object* v_k_1360_; lean_object* v_v_1361_; lean_object* v_l_1362_; lean_object* v_r_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; uint8_t v___x_1366_; 
v_size_1358_ = lean_ctor_get(v_impl_1356_, 0);
lean_inc(v_size_1358_);
v_size_1359_ = lean_ctor_get(v_r_1351_, 0);
v_k_1360_ = lean_ctor_get(v_r_1351_, 1);
v_v_1361_ = lean_ctor_get(v_r_1351_, 2);
v_l_1362_ = lean_ctor_get(v_r_1351_, 3);
lean_inc(v_l_1362_);
v_r_1363_ = lean_ctor_get(v_r_1351_, 4);
v___x_1364_ = lean_unsigned_to_nat(3u);
v___x_1365_ = lean_nat_mul(v___x_1364_, v_size_1358_);
v___x_1366_ = lean_nat_dec_lt(v___x_1365_, v_size_1359_);
lean_dec(v___x_1365_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1370_; 
lean_dec(v_l_1362_);
v___x_1367_ = lean_nat_add(v___x_1357_, v_size_1358_);
lean_dec(v_size_1358_);
v___x_1368_ = lean_nat_add(v___x_1367_, v_size_1359_);
lean_dec(v___x_1367_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 3, v_impl_1356_);
lean_ctor_set(v___x_1353_, 0, v___x_1368_);
v___x_1370_ = v___x_1353_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1368_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v_k_1348_);
lean_ctor_set(v_reuseFailAlloc_1371_, 2, v_v_1349_);
lean_ctor_set(v_reuseFailAlloc_1371_, 3, v_impl_1356_);
lean_ctor_set(v_reuseFailAlloc_1371_, 4, v_r_1351_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
else
{
lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1435_; 
lean_inc(v_r_1363_);
lean_inc(v_v_1361_);
lean_inc(v_k_1360_);
lean_inc(v_size_1359_);
v_isSharedCheck_1435_ = !lean_is_exclusive(v_r_1351_);
if (v_isSharedCheck_1435_ == 0)
{
lean_object* v_unused_1436_; lean_object* v_unused_1437_; lean_object* v_unused_1438_; lean_object* v_unused_1439_; lean_object* v_unused_1440_; 
v_unused_1436_ = lean_ctor_get(v_r_1351_, 4);
lean_dec(v_unused_1436_);
v_unused_1437_ = lean_ctor_get(v_r_1351_, 3);
lean_dec(v_unused_1437_);
v_unused_1438_ = lean_ctor_get(v_r_1351_, 2);
lean_dec(v_unused_1438_);
v_unused_1439_ = lean_ctor_get(v_r_1351_, 1);
lean_dec(v_unused_1439_);
v_unused_1440_ = lean_ctor_get(v_r_1351_, 0);
lean_dec(v_unused_1440_);
v___x_1373_ = v_r_1351_;
v_isShared_1374_ = v_isSharedCheck_1435_;
goto v_resetjp_1372_;
}
else
{
lean_dec(v_r_1351_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1435_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v_size_1375_; lean_object* v_k_1376_; lean_object* v_v_1377_; lean_object* v_l_1378_; lean_object* v_r_1379_; lean_object* v_size_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; uint8_t v___x_1383_; 
v_size_1375_ = lean_ctor_get(v_l_1362_, 0);
v_k_1376_ = lean_ctor_get(v_l_1362_, 1);
v_v_1377_ = lean_ctor_get(v_l_1362_, 2);
v_l_1378_ = lean_ctor_get(v_l_1362_, 3);
v_r_1379_ = lean_ctor_get(v_l_1362_, 4);
v_size_1380_ = lean_ctor_get(v_r_1363_, 0);
v___x_1381_ = lean_unsigned_to_nat(2u);
v___x_1382_ = lean_nat_mul(v___x_1381_, v_size_1380_);
v___x_1383_ = lean_nat_dec_lt(v_size_1375_, v___x_1382_);
lean_dec(v___x_1382_);
if (v___x_1383_ == 0)
{
lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1411_; 
lean_inc(v_r_1379_);
lean_inc(v_l_1378_);
lean_inc(v_v_1377_);
lean_inc(v_k_1376_);
v_isSharedCheck_1411_ = !lean_is_exclusive(v_l_1362_);
if (v_isSharedCheck_1411_ == 0)
{
lean_object* v_unused_1412_; lean_object* v_unused_1413_; lean_object* v_unused_1414_; lean_object* v_unused_1415_; lean_object* v_unused_1416_; 
v_unused_1412_ = lean_ctor_get(v_l_1362_, 4);
lean_dec(v_unused_1412_);
v_unused_1413_ = lean_ctor_get(v_l_1362_, 3);
lean_dec(v_unused_1413_);
v_unused_1414_ = lean_ctor_get(v_l_1362_, 2);
lean_dec(v_unused_1414_);
v_unused_1415_ = lean_ctor_get(v_l_1362_, 1);
lean_dec(v_unused_1415_);
v_unused_1416_ = lean_ctor_get(v_l_1362_, 0);
lean_dec(v_unused_1416_);
v___x_1385_ = v_l_1362_;
v_isShared_1386_ = v_isSharedCheck_1411_;
goto v_resetjp_1384_;
}
else
{
lean_dec(v_l_1362_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1411_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1401_; 
v___x_1387_ = lean_nat_add(v___x_1357_, v_size_1358_);
lean_dec(v_size_1358_);
v___x_1388_ = lean_nat_add(v___x_1387_, v_size_1359_);
lean_dec(v_size_1359_);
if (lean_obj_tag(v_l_1378_) == 0)
{
lean_object* v_size_1409_; 
v_size_1409_ = lean_ctor_get(v_l_1378_, 0);
lean_inc(v_size_1409_);
v___y_1401_ = v_size_1409_;
goto v___jp_1400_;
}
else
{
lean_object* v___x_1410_; 
v___x_1410_ = lean_unsigned_to_nat(0u);
v___y_1401_ = v___x_1410_;
goto v___jp_1400_;
}
v___jp_1389_:
{
lean_object* v___x_1393_; lean_object* v___x_1395_; 
v___x_1393_ = lean_nat_add(v___y_1391_, v___y_1392_);
lean_dec(v___y_1392_);
lean_dec(v___y_1391_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 4, v_r_1363_);
lean_ctor_set(v___x_1385_, 3, v_r_1379_);
lean_ctor_set(v___x_1385_, 2, v_v_1361_);
lean_ctor_set(v___x_1385_, 1, v_k_1360_);
lean_ctor_set(v___x_1385_, 0, v___x_1393_);
v___x_1395_ = v___x_1385_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1393_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v_k_1360_);
lean_ctor_set(v_reuseFailAlloc_1399_, 2, v_v_1361_);
lean_ctor_set(v_reuseFailAlloc_1399_, 3, v_r_1379_);
lean_ctor_set(v_reuseFailAlloc_1399_, 4, v_r_1363_);
v___x_1395_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
lean_object* v___x_1397_; 
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 4, v___x_1395_);
lean_ctor_set(v___x_1373_, 3, v___y_1390_);
lean_ctor_set(v___x_1373_, 2, v_v_1377_);
lean_ctor_set(v___x_1373_, 1, v_k_1376_);
lean_ctor_set(v___x_1373_, 0, v___x_1388_);
v___x_1397_ = v___x_1373_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1388_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v_k_1376_);
lean_ctor_set(v_reuseFailAlloc_1398_, 2, v_v_1377_);
lean_ctor_set(v_reuseFailAlloc_1398_, 3, v___y_1390_);
lean_ctor_set(v_reuseFailAlloc_1398_, 4, v___x_1395_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
v___jp_1400_:
{
lean_object* v___x_1402_; lean_object* v___x_1404_; 
v___x_1402_ = lean_nat_add(v___x_1387_, v___y_1401_);
lean_dec(v___y_1401_);
lean_dec(v___x_1387_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 4, v_l_1378_);
lean_ctor_set(v___x_1353_, 3, v_impl_1356_);
lean_ctor_set(v___x_1353_, 0, v___x_1402_);
v___x_1404_ = v___x_1353_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___x_1402_);
lean_ctor_set(v_reuseFailAlloc_1408_, 1, v_k_1348_);
lean_ctor_set(v_reuseFailAlloc_1408_, 2, v_v_1349_);
lean_ctor_set(v_reuseFailAlloc_1408_, 3, v_impl_1356_);
lean_ctor_set(v_reuseFailAlloc_1408_, 4, v_l_1378_);
v___x_1404_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
lean_object* v___x_1405_; 
v___x_1405_ = lean_nat_add(v___x_1357_, v_size_1380_);
if (lean_obj_tag(v_r_1379_) == 0)
{
lean_object* v_size_1406_; 
v_size_1406_ = lean_ctor_get(v_r_1379_, 0);
lean_inc(v_size_1406_);
v___y_1390_ = v___x_1404_;
v___y_1391_ = v___x_1405_;
v___y_1392_ = v_size_1406_;
goto v___jp_1389_;
}
else
{
lean_object* v___x_1407_; 
v___x_1407_ = lean_unsigned_to_nat(0u);
v___y_1390_ = v___x_1404_;
v___y_1391_ = v___x_1405_;
v___y_1392_ = v___x_1407_;
goto v___jp_1389_;
}
}
}
}
}
else
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1421_; 
lean_del_object(v___x_1353_);
v___x_1417_ = lean_nat_add(v___x_1357_, v_size_1358_);
lean_dec(v_size_1358_);
v___x_1418_ = lean_nat_add(v___x_1417_, v_size_1359_);
lean_dec(v_size_1359_);
v___x_1419_ = lean_nat_add(v___x_1417_, v_size_1375_);
lean_dec(v___x_1417_);
lean_inc_ref(v_impl_1356_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 4, v_l_1362_);
lean_ctor_set(v___x_1373_, 3, v_impl_1356_);
lean_ctor_set(v___x_1373_, 2, v_v_1349_);
lean_ctor_set(v___x_1373_, 1, v_k_1348_);
lean_ctor_set(v___x_1373_, 0, v___x_1419_);
v___x_1421_ = v___x_1373_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1419_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v_k_1348_);
lean_ctor_set(v_reuseFailAlloc_1434_, 2, v_v_1349_);
lean_ctor_set(v_reuseFailAlloc_1434_, 3, v_impl_1356_);
lean_ctor_set(v_reuseFailAlloc_1434_, 4, v_l_1362_);
v___x_1421_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1428_; 
v_isSharedCheck_1428_ = !lean_is_exclusive(v_impl_1356_);
if (v_isSharedCheck_1428_ == 0)
{
lean_object* v_unused_1429_; lean_object* v_unused_1430_; lean_object* v_unused_1431_; lean_object* v_unused_1432_; lean_object* v_unused_1433_; 
v_unused_1429_ = lean_ctor_get(v_impl_1356_, 4);
lean_dec(v_unused_1429_);
v_unused_1430_ = lean_ctor_get(v_impl_1356_, 3);
lean_dec(v_unused_1430_);
v_unused_1431_ = lean_ctor_get(v_impl_1356_, 2);
lean_dec(v_unused_1431_);
v_unused_1432_ = lean_ctor_get(v_impl_1356_, 1);
lean_dec(v_unused_1432_);
v_unused_1433_ = lean_ctor_get(v_impl_1356_, 0);
lean_dec(v_unused_1433_);
v___x_1423_ = v_impl_1356_;
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
else
{
lean_dec(v_impl_1356_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1426_; 
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 4, v_r_1363_);
lean_ctor_set(v___x_1423_, 3, v___x_1421_);
lean_ctor_set(v___x_1423_, 2, v_v_1361_);
lean_ctor_set(v___x_1423_, 1, v_k_1360_);
lean_ctor_set(v___x_1423_, 0, v___x_1418_);
v___x_1426_ = v___x_1423_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1418_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v_k_1360_);
lean_ctor_set(v_reuseFailAlloc_1427_, 2, v_v_1361_);
lean_ctor_set(v_reuseFailAlloc_1427_, 3, v___x_1421_);
lean_ctor_set(v_reuseFailAlloc_1427_, 4, v_r_1363_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1441_; lean_object* v___x_1442_; lean_object* v___x_1444_; 
v_size_1441_ = lean_ctor_get(v_impl_1356_, 0);
lean_inc(v_size_1441_);
v___x_1442_ = lean_nat_add(v___x_1357_, v_size_1441_);
lean_dec(v_size_1441_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 3, v_impl_1356_);
lean_ctor_set(v___x_1353_, 0, v___x_1442_);
v___x_1444_ = v___x_1353_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1442_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_k_1348_);
lean_ctor_set(v_reuseFailAlloc_1445_, 2, v_v_1349_);
lean_ctor_set(v_reuseFailAlloc_1445_, 3, v_impl_1356_);
lean_ctor_set(v_reuseFailAlloc_1445_, 4, v_r_1351_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
else
{
if (lean_obj_tag(v_r_1351_) == 0)
{
lean_object* v_l_1446_; 
v_l_1446_ = lean_ctor_get(v_r_1351_, 3);
lean_inc(v_l_1446_);
if (lean_obj_tag(v_l_1446_) == 0)
{
lean_object* v_r_1447_; 
v_r_1447_ = lean_ctor_get(v_r_1351_, 4);
lean_inc(v_r_1447_);
if (lean_obj_tag(v_r_1447_) == 0)
{
lean_object* v_size_1448_; lean_object* v_k_1449_; lean_object* v_v_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1463_; 
v_size_1448_ = lean_ctor_get(v_r_1351_, 0);
v_k_1449_ = lean_ctor_get(v_r_1351_, 1);
v_v_1450_ = lean_ctor_get(v_r_1351_, 2);
v_isSharedCheck_1463_ = !lean_is_exclusive(v_r_1351_);
if (v_isSharedCheck_1463_ == 0)
{
lean_object* v_unused_1464_; lean_object* v_unused_1465_; 
v_unused_1464_ = lean_ctor_get(v_r_1351_, 4);
lean_dec(v_unused_1464_);
v_unused_1465_ = lean_ctor_get(v_r_1351_, 3);
lean_dec(v_unused_1465_);
v___x_1452_ = v_r_1351_;
v_isShared_1453_ = v_isSharedCheck_1463_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_v_1450_);
lean_inc(v_k_1449_);
lean_inc(v_size_1448_);
lean_dec(v_r_1351_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1463_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v_size_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1458_; 
v_size_1454_ = lean_ctor_get(v_l_1446_, 0);
v___x_1455_ = lean_nat_add(v___x_1357_, v_size_1448_);
lean_dec(v_size_1448_);
v___x_1456_ = lean_nat_add(v___x_1357_, v_size_1454_);
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 4, v_l_1446_);
lean_ctor_set(v___x_1452_, 3, v_impl_1356_);
lean_ctor_set(v___x_1452_, 2, v_v_1349_);
lean_ctor_set(v___x_1452_, 1, v_k_1348_);
lean_ctor_set(v___x_1452_, 0, v___x_1456_);
v___x_1458_ = v___x_1452_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v___x_1456_);
lean_ctor_set(v_reuseFailAlloc_1462_, 1, v_k_1348_);
lean_ctor_set(v_reuseFailAlloc_1462_, 2, v_v_1349_);
lean_ctor_set(v_reuseFailAlloc_1462_, 3, v_impl_1356_);
lean_ctor_set(v_reuseFailAlloc_1462_, 4, v_l_1446_);
v___x_1458_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
lean_object* v___x_1460_; 
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 4, v_r_1447_);
lean_ctor_set(v___x_1353_, 3, v___x_1458_);
lean_ctor_set(v___x_1353_, 2, v_v_1450_);
lean_ctor_set(v___x_1353_, 1, v_k_1449_);
lean_ctor_set(v___x_1353_, 0, v___x_1455_);
v___x_1460_ = v___x_1353_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1455_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v_k_1449_);
lean_ctor_set(v_reuseFailAlloc_1461_, 2, v_v_1450_);
lean_ctor_set(v_reuseFailAlloc_1461_, 3, v___x_1458_);
lean_ctor_set(v_reuseFailAlloc_1461_, 4, v_r_1447_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
else
{
lean_object* v_k_1466_; lean_object* v_v_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1490_; 
v_k_1466_ = lean_ctor_get(v_r_1351_, 1);
v_v_1467_ = lean_ctor_get(v_r_1351_, 2);
v_isSharedCheck_1490_ = !lean_is_exclusive(v_r_1351_);
if (v_isSharedCheck_1490_ == 0)
{
lean_object* v_unused_1491_; lean_object* v_unused_1492_; lean_object* v_unused_1493_; 
v_unused_1491_ = lean_ctor_get(v_r_1351_, 4);
lean_dec(v_unused_1491_);
v_unused_1492_ = lean_ctor_get(v_r_1351_, 3);
lean_dec(v_unused_1492_);
v_unused_1493_ = lean_ctor_get(v_r_1351_, 0);
lean_dec(v_unused_1493_);
v___x_1469_ = v_r_1351_;
v_isShared_1470_ = v_isSharedCheck_1490_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_v_1467_);
lean_inc(v_k_1466_);
lean_dec(v_r_1351_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1490_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v_k_1471_; lean_object* v_v_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1486_; 
v_k_1471_ = lean_ctor_get(v_l_1446_, 1);
v_v_1472_ = lean_ctor_get(v_l_1446_, 2);
v_isSharedCheck_1486_ = !lean_is_exclusive(v_l_1446_);
if (v_isSharedCheck_1486_ == 0)
{
lean_object* v_unused_1487_; lean_object* v_unused_1488_; lean_object* v_unused_1489_; 
v_unused_1487_ = lean_ctor_get(v_l_1446_, 4);
lean_dec(v_unused_1487_);
v_unused_1488_ = lean_ctor_get(v_l_1446_, 3);
lean_dec(v_unused_1488_);
v_unused_1489_ = lean_ctor_get(v_l_1446_, 0);
lean_dec(v_unused_1489_);
v___x_1474_ = v_l_1446_;
v_isShared_1475_ = v_isSharedCheck_1486_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_v_1472_);
lean_inc(v_k_1471_);
lean_dec(v_l_1446_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1486_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1476_; lean_object* v___x_1478_; 
v___x_1476_ = lean_unsigned_to_nat(3u);
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 4, v_r_1447_);
lean_ctor_set(v___x_1474_, 3, v_r_1447_);
lean_ctor_set(v___x_1474_, 2, v_v_1349_);
lean_ctor_set(v___x_1474_, 1, v_k_1348_);
lean_ctor_set(v___x_1474_, 0, v___x_1357_);
v___x_1478_ = v___x_1474_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1357_);
lean_ctor_set(v_reuseFailAlloc_1485_, 1, v_k_1348_);
lean_ctor_set(v_reuseFailAlloc_1485_, 2, v_v_1349_);
lean_ctor_set(v_reuseFailAlloc_1485_, 3, v_r_1447_);
lean_ctor_set(v_reuseFailAlloc_1485_, 4, v_r_1447_);
v___x_1478_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
lean_object* v___x_1480_; 
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 3, v_r_1447_);
lean_ctor_set(v___x_1469_, 0, v___x_1357_);
v___x_1480_ = v___x_1469_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v___x_1357_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v_k_1466_);
lean_ctor_set(v_reuseFailAlloc_1484_, 2, v_v_1467_);
lean_ctor_set(v_reuseFailAlloc_1484_, 3, v_r_1447_);
lean_ctor_set(v_reuseFailAlloc_1484_, 4, v_r_1447_);
v___x_1480_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
lean_object* v___x_1482_; 
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 4, v___x_1480_);
lean_ctor_set(v___x_1353_, 3, v___x_1478_);
lean_ctor_set(v___x_1353_, 2, v_v_1472_);
lean_ctor_set(v___x_1353_, 1, v_k_1471_);
lean_ctor_set(v___x_1353_, 0, v___x_1476_);
v___x_1482_ = v___x_1353_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1476_);
lean_ctor_set(v_reuseFailAlloc_1483_, 1, v_k_1471_);
lean_ctor_set(v_reuseFailAlloc_1483_, 2, v_v_1472_);
lean_ctor_set(v_reuseFailAlloc_1483_, 3, v___x_1478_);
lean_ctor_set(v_reuseFailAlloc_1483_, 4, v___x_1480_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1494_; 
v_r_1494_ = lean_ctor_get(v_r_1351_, 4);
lean_inc(v_r_1494_);
if (lean_obj_tag(v_r_1494_) == 0)
{
lean_object* v_k_1495_; lean_object* v_v_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1507_; 
v_k_1495_ = lean_ctor_get(v_r_1351_, 1);
v_v_1496_ = lean_ctor_get(v_r_1351_, 2);
v_isSharedCheck_1507_ = !lean_is_exclusive(v_r_1351_);
if (v_isSharedCheck_1507_ == 0)
{
lean_object* v_unused_1508_; lean_object* v_unused_1509_; lean_object* v_unused_1510_; 
v_unused_1508_ = lean_ctor_get(v_r_1351_, 4);
lean_dec(v_unused_1508_);
v_unused_1509_ = lean_ctor_get(v_r_1351_, 3);
lean_dec(v_unused_1509_);
v_unused_1510_ = lean_ctor_get(v_r_1351_, 0);
lean_dec(v_unused_1510_);
v___x_1498_ = v_r_1351_;
v_isShared_1499_ = v_isSharedCheck_1507_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_v_1496_);
lean_inc(v_k_1495_);
lean_dec(v_r_1351_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1507_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1500_; lean_object* v___x_1502_; 
v___x_1500_ = lean_unsigned_to_nat(3u);
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 4, v_l_1446_);
lean_ctor_set(v___x_1498_, 2, v_v_1349_);
lean_ctor_set(v___x_1498_, 1, v_k_1348_);
lean_ctor_set(v___x_1498_, 0, v___x_1357_);
v___x_1502_ = v___x_1498_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1357_);
lean_ctor_set(v_reuseFailAlloc_1506_, 1, v_k_1348_);
lean_ctor_set(v_reuseFailAlloc_1506_, 2, v_v_1349_);
lean_ctor_set(v_reuseFailAlloc_1506_, 3, v_l_1446_);
lean_ctor_set(v_reuseFailAlloc_1506_, 4, v_l_1446_);
v___x_1502_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
lean_object* v___x_1504_; 
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 4, v_r_1494_);
lean_ctor_set(v___x_1353_, 3, v___x_1502_);
lean_ctor_set(v___x_1353_, 2, v_v_1496_);
lean_ctor_set(v___x_1353_, 1, v_k_1495_);
lean_ctor_set(v___x_1353_, 0, v___x_1500_);
v___x_1504_ = v___x_1353_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___x_1500_);
lean_ctor_set(v_reuseFailAlloc_1505_, 1, v_k_1495_);
lean_ctor_set(v_reuseFailAlloc_1505_, 2, v_v_1496_);
lean_ctor_set(v_reuseFailAlloc_1505_, 3, v___x_1502_);
lean_ctor_set(v_reuseFailAlloc_1505_, 4, v_r_1494_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
}
else
{
lean_object* v_size_1511_; lean_object* v_k_1512_; lean_object* v_v_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1524_; 
v_size_1511_ = lean_ctor_get(v_r_1351_, 0);
v_k_1512_ = lean_ctor_get(v_r_1351_, 1);
v_v_1513_ = lean_ctor_get(v_r_1351_, 2);
v_isSharedCheck_1524_ = !lean_is_exclusive(v_r_1351_);
if (v_isSharedCheck_1524_ == 0)
{
lean_object* v_unused_1525_; lean_object* v_unused_1526_; 
v_unused_1525_ = lean_ctor_get(v_r_1351_, 4);
lean_dec(v_unused_1525_);
v_unused_1526_ = lean_ctor_get(v_r_1351_, 3);
lean_dec(v_unused_1526_);
v___x_1515_ = v_r_1351_;
v_isShared_1516_ = v_isSharedCheck_1524_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_v_1513_);
lean_inc(v_k_1512_);
lean_inc(v_size_1511_);
lean_dec(v_r_1351_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1524_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 3, v_r_1494_);
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_size_1511_);
lean_ctor_set(v_reuseFailAlloc_1523_, 1, v_k_1512_);
lean_ctor_set(v_reuseFailAlloc_1523_, 2, v_v_1513_);
lean_ctor_set(v_reuseFailAlloc_1523_, 3, v_r_1494_);
lean_ctor_set(v_reuseFailAlloc_1523_, 4, v_r_1494_);
v___x_1518_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
lean_object* v___x_1519_; lean_object* v___x_1521_; 
v___x_1519_ = lean_unsigned_to_nat(2u);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 4, v___x_1518_);
lean_ctor_set(v___x_1353_, 3, v_r_1494_);
lean_ctor_set(v___x_1353_, 0, v___x_1519_);
v___x_1521_ = v___x_1353_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1519_);
lean_ctor_set(v_reuseFailAlloc_1522_, 1, v_k_1348_);
lean_ctor_set(v_reuseFailAlloc_1522_, 2, v_v_1349_);
lean_ctor_set(v_reuseFailAlloc_1522_, 3, v_r_1494_);
lean_ctor_set(v_reuseFailAlloc_1522_, 4, v___x_1518_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
}
}
}
else
{
lean_object* v___x_1528_; 
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 3, v_r_1351_);
lean_ctor_set(v___x_1353_, 0, v___x_1357_);
v___x_1528_ = v___x_1353_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___x_1357_);
lean_ctor_set(v_reuseFailAlloc_1529_, 1, v_k_1348_);
lean_ctor_set(v_reuseFailAlloc_1529_, 2, v_v_1349_);
lean_ctor_set(v_reuseFailAlloc_1529_, 3, v_r_1351_);
lean_ctor_set(v_reuseFailAlloc_1529_, 4, v_r_1351_);
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
case 1:
{
lean_del_object(v___x_1353_);
lean_dec(v_v_1349_);
lean_dec(v_k_1348_);
if (lean_obj_tag(v_l_1350_) == 0)
{
if (lean_obj_tag(v_r_1351_) == 0)
{
lean_object* v_size_1530_; lean_object* v_k_1531_; lean_object* v_v_1532_; lean_object* v_l_1533_; lean_object* v_r_1534_; lean_object* v_size_1535_; lean_object* v_k_1536_; lean_object* v_v_1537_; lean_object* v_l_1538_; lean_object* v_r_1539_; lean_object* v___x_1540_; uint8_t v___x_1541_; 
v_size_1530_ = lean_ctor_get(v_l_1350_, 0);
v_k_1531_ = lean_ctor_get(v_l_1350_, 1);
v_v_1532_ = lean_ctor_get(v_l_1350_, 2);
v_l_1533_ = lean_ctor_get(v_l_1350_, 3);
v_r_1534_ = lean_ctor_get(v_l_1350_, 4);
lean_inc(v_r_1534_);
v_size_1535_ = lean_ctor_get(v_r_1351_, 0);
v_k_1536_ = lean_ctor_get(v_r_1351_, 1);
v_v_1537_ = lean_ctor_get(v_r_1351_, 2);
v_l_1538_ = lean_ctor_get(v_r_1351_, 3);
lean_inc(v_l_1538_);
v_r_1539_ = lean_ctor_get(v_r_1351_, 4);
v___x_1540_ = lean_unsigned_to_nat(1u);
v___x_1541_ = lean_nat_dec_lt(v_size_1530_, v_size_1535_);
if (v___x_1541_ == 0)
{
lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1677_; 
lean_inc(v_l_1533_);
lean_inc(v_v_1532_);
lean_inc(v_k_1531_);
v_isSharedCheck_1677_ = !lean_is_exclusive(v_l_1350_);
if (v_isSharedCheck_1677_ == 0)
{
lean_object* v_unused_1678_; lean_object* v_unused_1679_; lean_object* v_unused_1680_; lean_object* v_unused_1681_; lean_object* v_unused_1682_; 
v_unused_1678_ = lean_ctor_get(v_l_1350_, 4);
lean_dec(v_unused_1678_);
v_unused_1679_ = lean_ctor_get(v_l_1350_, 3);
lean_dec(v_unused_1679_);
v_unused_1680_ = lean_ctor_get(v_l_1350_, 2);
lean_dec(v_unused_1680_);
v_unused_1681_ = lean_ctor_get(v_l_1350_, 1);
lean_dec(v_unused_1681_);
v_unused_1682_ = lean_ctor_get(v_l_1350_, 0);
lean_dec(v_unused_1682_);
v___x_1543_ = v_l_1350_;
v_isShared_1544_ = v_isSharedCheck_1677_;
goto v_resetjp_1542_;
}
else
{
lean_dec(v_l_1350_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1677_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1545_; lean_object* v_tree_1546_; 
v___x_1545_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_1531_, v_v_1532_, v_l_1533_, v_r_1534_);
v_tree_1546_ = lean_ctor_get(v___x_1545_, 2);
lean_inc(v_tree_1546_);
if (lean_obj_tag(v_tree_1546_) == 0)
{
lean_object* v_k_1547_; lean_object* v_v_1548_; lean_object* v_size_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; uint8_t v___x_1552_; 
v_k_1547_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_k_1547_);
v_v_1548_ = lean_ctor_get(v___x_1545_, 1);
lean_inc(v_v_1548_);
lean_dec_ref(v___x_1545_);
v_size_1549_ = lean_ctor_get(v_tree_1546_, 0);
v___x_1550_ = lean_unsigned_to_nat(3u);
v___x_1551_ = lean_nat_mul(v___x_1550_, v_size_1549_);
v___x_1552_ = lean_nat_dec_lt(v___x_1551_, v_size_1535_);
lean_dec(v___x_1551_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1556_; 
lean_dec(v_l_1538_);
v___x_1553_ = lean_nat_add(v___x_1540_, v_size_1549_);
v___x_1554_ = lean_nat_add(v___x_1553_, v_size_1535_);
lean_dec(v___x_1553_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 4, v_r_1351_);
lean_ctor_set(v___x_1543_, 3, v_tree_1546_);
lean_ctor_set(v___x_1543_, 2, v_v_1548_);
lean_ctor_set(v___x_1543_, 1, v_k_1547_);
lean_ctor_set(v___x_1543_, 0, v___x_1554_);
v___x_1556_ = v___x_1543_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1554_);
lean_ctor_set(v_reuseFailAlloc_1557_, 1, v_k_1547_);
lean_ctor_set(v_reuseFailAlloc_1557_, 2, v_v_1548_);
lean_ctor_set(v_reuseFailAlloc_1557_, 3, v_tree_1546_);
lean_ctor_set(v_reuseFailAlloc_1557_, 4, v_r_1351_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
else
{
lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1612_; 
lean_inc(v_r_1539_);
lean_inc(v_v_1537_);
lean_inc(v_k_1536_);
lean_inc(v_size_1535_);
v_isSharedCheck_1612_ = !lean_is_exclusive(v_r_1351_);
if (v_isSharedCheck_1612_ == 0)
{
lean_object* v_unused_1613_; lean_object* v_unused_1614_; lean_object* v_unused_1615_; lean_object* v_unused_1616_; lean_object* v_unused_1617_; 
v_unused_1613_ = lean_ctor_get(v_r_1351_, 4);
lean_dec(v_unused_1613_);
v_unused_1614_ = lean_ctor_get(v_r_1351_, 3);
lean_dec(v_unused_1614_);
v_unused_1615_ = lean_ctor_get(v_r_1351_, 2);
lean_dec(v_unused_1615_);
v_unused_1616_ = lean_ctor_get(v_r_1351_, 1);
lean_dec(v_unused_1616_);
v_unused_1617_ = lean_ctor_get(v_r_1351_, 0);
lean_dec(v_unused_1617_);
v___x_1559_ = v_r_1351_;
v_isShared_1560_ = v_isSharedCheck_1612_;
goto v_resetjp_1558_;
}
else
{
lean_dec(v_r_1351_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1612_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v_size_1561_; lean_object* v_k_1562_; lean_object* v_v_1563_; lean_object* v_l_1564_; lean_object* v_r_1565_; lean_object* v_size_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; uint8_t v___x_1569_; 
v_size_1561_ = lean_ctor_get(v_l_1538_, 0);
v_k_1562_ = lean_ctor_get(v_l_1538_, 1);
v_v_1563_ = lean_ctor_get(v_l_1538_, 2);
v_l_1564_ = lean_ctor_get(v_l_1538_, 3);
v_r_1565_ = lean_ctor_get(v_l_1538_, 4);
v_size_1566_ = lean_ctor_get(v_r_1539_, 0);
v___x_1567_ = lean_unsigned_to_nat(2u);
v___x_1568_ = lean_nat_mul(v___x_1567_, v_size_1566_);
v___x_1569_ = lean_nat_dec_lt(v_size_1561_, v___x_1568_);
lean_dec(v___x_1568_);
if (v___x_1569_ == 0)
{
lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1597_; 
lean_inc(v_r_1565_);
lean_inc(v_l_1564_);
lean_inc(v_v_1563_);
lean_inc(v_k_1562_);
v_isSharedCheck_1597_ = !lean_is_exclusive(v_l_1538_);
if (v_isSharedCheck_1597_ == 0)
{
lean_object* v_unused_1598_; lean_object* v_unused_1599_; lean_object* v_unused_1600_; lean_object* v_unused_1601_; lean_object* v_unused_1602_; 
v_unused_1598_ = lean_ctor_get(v_l_1538_, 4);
lean_dec(v_unused_1598_);
v_unused_1599_ = lean_ctor_get(v_l_1538_, 3);
lean_dec(v_unused_1599_);
v_unused_1600_ = lean_ctor_get(v_l_1538_, 2);
lean_dec(v_unused_1600_);
v_unused_1601_ = lean_ctor_get(v_l_1538_, 1);
lean_dec(v_unused_1601_);
v_unused_1602_ = lean_ctor_get(v_l_1538_, 0);
lean_dec(v_unused_1602_);
v___x_1571_ = v_l_1538_;
v_isShared_1572_ = v_isSharedCheck_1597_;
goto v_resetjp_1570_;
}
else
{
lean_dec(v_l_1538_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1597_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1587_; 
v___x_1573_ = lean_nat_add(v___x_1540_, v_size_1549_);
v___x_1574_ = lean_nat_add(v___x_1573_, v_size_1535_);
lean_dec(v_size_1535_);
if (lean_obj_tag(v_l_1564_) == 0)
{
lean_object* v_size_1595_; 
v_size_1595_ = lean_ctor_get(v_l_1564_, 0);
lean_inc(v_size_1595_);
v___y_1587_ = v_size_1595_;
goto v___jp_1586_;
}
else
{
lean_object* v___x_1596_; 
v___x_1596_ = lean_unsigned_to_nat(0u);
v___y_1587_ = v___x_1596_;
goto v___jp_1586_;
}
v___jp_1575_:
{
lean_object* v___x_1579_; lean_object* v___x_1581_; 
v___x_1579_ = lean_nat_add(v___y_1576_, v___y_1578_);
lean_dec(v___y_1578_);
lean_dec(v___y_1576_);
if (v_isShared_1572_ == 0)
{
lean_ctor_set(v___x_1571_, 4, v_r_1539_);
lean_ctor_set(v___x_1571_, 3, v_r_1565_);
lean_ctor_set(v___x_1571_, 2, v_v_1537_);
lean_ctor_set(v___x_1571_, 1, v_k_1536_);
lean_ctor_set(v___x_1571_, 0, v___x_1579_);
v___x_1581_ = v___x_1571_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1579_);
lean_ctor_set(v_reuseFailAlloc_1585_, 1, v_k_1536_);
lean_ctor_set(v_reuseFailAlloc_1585_, 2, v_v_1537_);
lean_ctor_set(v_reuseFailAlloc_1585_, 3, v_r_1565_);
lean_ctor_set(v_reuseFailAlloc_1585_, 4, v_r_1539_);
v___x_1581_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
lean_object* v___x_1583_; 
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 4, v___x_1581_);
lean_ctor_set(v___x_1559_, 3, v___y_1577_);
lean_ctor_set(v___x_1559_, 2, v_v_1563_);
lean_ctor_set(v___x_1559_, 1, v_k_1562_);
lean_ctor_set(v___x_1559_, 0, v___x_1574_);
v___x_1583_ = v___x_1559_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1574_);
lean_ctor_set(v_reuseFailAlloc_1584_, 1, v_k_1562_);
lean_ctor_set(v_reuseFailAlloc_1584_, 2, v_v_1563_);
lean_ctor_set(v_reuseFailAlloc_1584_, 3, v___y_1577_);
lean_ctor_set(v_reuseFailAlloc_1584_, 4, v___x_1581_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
v___jp_1586_:
{
lean_object* v___x_1588_; lean_object* v___x_1590_; 
v___x_1588_ = lean_nat_add(v___x_1573_, v___y_1587_);
lean_dec(v___y_1587_);
lean_dec(v___x_1573_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 4, v_l_1564_);
lean_ctor_set(v___x_1543_, 3, v_tree_1546_);
lean_ctor_set(v___x_1543_, 2, v_v_1548_);
lean_ctor_set(v___x_1543_, 1, v_k_1547_);
lean_ctor_set(v___x_1543_, 0, v___x_1588_);
v___x_1590_ = v___x_1543_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1588_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v_k_1547_);
lean_ctor_set(v_reuseFailAlloc_1594_, 2, v_v_1548_);
lean_ctor_set(v_reuseFailAlloc_1594_, 3, v_tree_1546_);
lean_ctor_set(v_reuseFailAlloc_1594_, 4, v_l_1564_);
v___x_1590_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
lean_object* v___x_1591_; 
v___x_1591_ = lean_nat_add(v___x_1540_, v_size_1566_);
if (lean_obj_tag(v_r_1565_) == 0)
{
lean_object* v_size_1592_; 
v_size_1592_ = lean_ctor_get(v_r_1565_, 0);
lean_inc(v_size_1592_);
v___y_1576_ = v___x_1591_;
v___y_1577_ = v___x_1590_;
v___y_1578_ = v_size_1592_;
goto v___jp_1575_;
}
else
{
lean_object* v___x_1593_; 
v___x_1593_ = lean_unsigned_to_nat(0u);
v___y_1576_ = v___x_1591_;
v___y_1577_ = v___x_1590_;
v___y_1578_ = v___x_1593_;
goto v___jp_1575_;
}
}
}
}
}
else
{
lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1607_; 
v___x_1603_ = lean_nat_add(v___x_1540_, v_size_1549_);
v___x_1604_ = lean_nat_add(v___x_1603_, v_size_1535_);
lean_dec(v_size_1535_);
v___x_1605_ = lean_nat_add(v___x_1603_, v_size_1561_);
lean_dec(v___x_1603_);
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 4, v_l_1538_);
lean_ctor_set(v___x_1559_, 3, v_tree_1546_);
lean_ctor_set(v___x_1559_, 2, v_v_1548_);
lean_ctor_set(v___x_1559_, 1, v_k_1547_);
lean_ctor_set(v___x_1559_, 0, v___x_1605_);
v___x_1607_ = v___x_1559_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1605_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v_k_1547_);
lean_ctor_set(v_reuseFailAlloc_1611_, 2, v_v_1548_);
lean_ctor_set(v_reuseFailAlloc_1611_, 3, v_tree_1546_);
lean_ctor_set(v_reuseFailAlloc_1611_, 4, v_l_1538_);
v___x_1607_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
lean_object* v___x_1609_; 
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 4, v_r_1539_);
lean_ctor_set(v___x_1543_, 3, v___x_1607_);
lean_ctor_set(v___x_1543_, 2, v_v_1537_);
lean_ctor_set(v___x_1543_, 1, v_k_1536_);
lean_ctor_set(v___x_1543_, 0, v___x_1604_);
v___x_1609_ = v___x_1543_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1604_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v_k_1536_);
lean_ctor_set(v_reuseFailAlloc_1610_, 2, v_v_1537_);
lean_ctor_set(v_reuseFailAlloc_1610_, 3, v___x_1607_);
lean_ctor_set(v_reuseFailAlloc_1610_, 4, v_r_1539_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
}
}
else
{
lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1671_; 
lean_inc(v_r_1539_);
lean_inc(v_v_1537_);
lean_inc(v_k_1536_);
lean_inc(v_size_1535_);
v_isSharedCheck_1671_ = !lean_is_exclusive(v_r_1351_);
if (v_isSharedCheck_1671_ == 0)
{
lean_object* v_unused_1672_; lean_object* v_unused_1673_; lean_object* v_unused_1674_; lean_object* v_unused_1675_; lean_object* v_unused_1676_; 
v_unused_1672_ = lean_ctor_get(v_r_1351_, 4);
lean_dec(v_unused_1672_);
v_unused_1673_ = lean_ctor_get(v_r_1351_, 3);
lean_dec(v_unused_1673_);
v_unused_1674_ = lean_ctor_get(v_r_1351_, 2);
lean_dec(v_unused_1674_);
v_unused_1675_ = lean_ctor_get(v_r_1351_, 1);
lean_dec(v_unused_1675_);
v_unused_1676_ = lean_ctor_get(v_r_1351_, 0);
lean_dec(v_unused_1676_);
v___x_1619_ = v_r_1351_;
v_isShared_1620_ = v_isSharedCheck_1671_;
goto v_resetjp_1618_;
}
else
{
lean_dec(v_r_1351_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1671_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
if (lean_obj_tag(v_l_1538_) == 0)
{
if (lean_obj_tag(v_r_1539_) == 0)
{
lean_object* v_k_1621_; lean_object* v_v_1622_; lean_object* v_size_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1627_; 
v_k_1621_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_k_1621_);
v_v_1622_ = lean_ctor_get(v___x_1545_, 1);
lean_inc(v_v_1622_);
lean_dec_ref(v___x_1545_);
v_size_1623_ = lean_ctor_get(v_l_1538_, 0);
v___x_1624_ = lean_nat_add(v___x_1540_, v_size_1535_);
lean_dec(v_size_1535_);
v___x_1625_ = lean_nat_add(v___x_1540_, v_size_1623_);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 4, v_l_1538_);
lean_ctor_set(v___x_1619_, 3, v_tree_1546_);
lean_ctor_set(v___x_1619_, 2, v_v_1622_);
lean_ctor_set(v___x_1619_, 1, v_k_1621_);
lean_ctor_set(v___x_1619_, 0, v___x_1625_);
v___x_1627_ = v___x_1619_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v___x_1625_);
lean_ctor_set(v_reuseFailAlloc_1631_, 1, v_k_1621_);
lean_ctor_set(v_reuseFailAlloc_1631_, 2, v_v_1622_);
lean_ctor_set(v_reuseFailAlloc_1631_, 3, v_tree_1546_);
lean_ctor_set(v_reuseFailAlloc_1631_, 4, v_l_1538_);
v___x_1627_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
lean_object* v___x_1629_; 
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 4, v_r_1539_);
lean_ctor_set(v___x_1543_, 3, v___x_1627_);
lean_ctor_set(v___x_1543_, 2, v_v_1537_);
lean_ctor_set(v___x_1543_, 1, v_k_1536_);
lean_ctor_set(v___x_1543_, 0, v___x_1624_);
v___x_1629_ = v___x_1543_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___x_1624_);
lean_ctor_set(v_reuseFailAlloc_1630_, 1, v_k_1536_);
lean_ctor_set(v_reuseFailAlloc_1630_, 2, v_v_1537_);
lean_ctor_set(v_reuseFailAlloc_1630_, 3, v___x_1627_);
lean_ctor_set(v_reuseFailAlloc_1630_, 4, v_r_1539_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
else
{
lean_object* v_k_1632_; lean_object* v_v_1633_; lean_object* v_k_1634_; lean_object* v_v_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1649_; 
lean_dec(v_size_1535_);
v_k_1632_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_k_1632_);
v_v_1633_ = lean_ctor_get(v___x_1545_, 1);
lean_inc(v_v_1633_);
lean_dec_ref(v___x_1545_);
v_k_1634_ = lean_ctor_get(v_l_1538_, 1);
v_v_1635_ = lean_ctor_get(v_l_1538_, 2);
v_isSharedCheck_1649_ = !lean_is_exclusive(v_l_1538_);
if (v_isSharedCheck_1649_ == 0)
{
lean_object* v_unused_1650_; lean_object* v_unused_1651_; lean_object* v_unused_1652_; 
v_unused_1650_ = lean_ctor_get(v_l_1538_, 4);
lean_dec(v_unused_1650_);
v_unused_1651_ = lean_ctor_get(v_l_1538_, 3);
lean_dec(v_unused_1651_);
v_unused_1652_ = lean_ctor_get(v_l_1538_, 0);
lean_dec(v_unused_1652_);
v___x_1637_ = v_l_1538_;
v_isShared_1638_ = v_isSharedCheck_1649_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_v_1635_);
lean_inc(v_k_1634_);
lean_dec(v_l_1538_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1649_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1639_; lean_object* v___x_1641_; 
v___x_1639_ = lean_unsigned_to_nat(3u);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 4, v_r_1539_);
lean_ctor_set(v___x_1637_, 3, v_r_1539_);
lean_ctor_set(v___x_1637_, 2, v_v_1633_);
lean_ctor_set(v___x_1637_, 1, v_k_1632_);
lean_ctor_set(v___x_1637_, 0, v___x_1540_);
v___x_1641_ = v___x_1637_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v___x_1540_);
lean_ctor_set(v_reuseFailAlloc_1648_, 1, v_k_1632_);
lean_ctor_set(v_reuseFailAlloc_1648_, 2, v_v_1633_);
lean_ctor_set(v_reuseFailAlloc_1648_, 3, v_r_1539_);
lean_ctor_set(v_reuseFailAlloc_1648_, 4, v_r_1539_);
v___x_1641_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
lean_object* v___x_1643_; 
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 3, v_r_1539_);
lean_ctor_set(v___x_1619_, 0, v___x_1540_);
v___x_1643_ = v___x_1619_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v___x_1540_);
lean_ctor_set(v_reuseFailAlloc_1647_, 1, v_k_1536_);
lean_ctor_set(v_reuseFailAlloc_1647_, 2, v_v_1537_);
lean_ctor_set(v_reuseFailAlloc_1647_, 3, v_r_1539_);
lean_ctor_set(v_reuseFailAlloc_1647_, 4, v_r_1539_);
v___x_1643_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
lean_object* v___x_1645_; 
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 4, v___x_1643_);
lean_ctor_set(v___x_1543_, 3, v___x_1641_);
lean_ctor_set(v___x_1543_, 2, v_v_1635_);
lean_ctor_set(v___x_1543_, 1, v_k_1634_);
lean_ctor_set(v___x_1543_, 0, v___x_1639_);
v___x_1645_ = v___x_1543_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1639_);
lean_ctor_set(v_reuseFailAlloc_1646_, 1, v_k_1634_);
lean_ctor_set(v_reuseFailAlloc_1646_, 2, v_v_1635_);
lean_ctor_set(v_reuseFailAlloc_1646_, 3, v___x_1641_);
lean_ctor_set(v_reuseFailAlloc_1646_, 4, v___x_1643_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1539_) == 0)
{
lean_object* v_k_1653_; lean_object* v_v_1654_; lean_object* v___x_1655_; lean_object* v___x_1657_; 
lean_dec(v_size_1535_);
v_k_1653_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_k_1653_);
v_v_1654_ = lean_ctor_get(v___x_1545_, 1);
lean_inc(v_v_1654_);
lean_dec_ref(v___x_1545_);
v___x_1655_ = lean_unsigned_to_nat(3u);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 4, v_l_1538_);
lean_ctor_set(v___x_1619_, 2, v_v_1654_);
lean_ctor_set(v___x_1619_, 1, v_k_1653_);
lean_ctor_set(v___x_1619_, 0, v___x_1540_);
v___x_1657_ = v___x_1619_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1540_);
lean_ctor_set(v_reuseFailAlloc_1661_, 1, v_k_1653_);
lean_ctor_set(v_reuseFailAlloc_1661_, 2, v_v_1654_);
lean_ctor_set(v_reuseFailAlloc_1661_, 3, v_l_1538_);
lean_ctor_set(v_reuseFailAlloc_1661_, 4, v_l_1538_);
v___x_1657_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
lean_object* v___x_1659_; 
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 4, v_r_1539_);
lean_ctor_set(v___x_1543_, 3, v___x_1657_);
lean_ctor_set(v___x_1543_, 2, v_v_1537_);
lean_ctor_set(v___x_1543_, 1, v_k_1536_);
lean_ctor_set(v___x_1543_, 0, v___x_1655_);
v___x_1659_ = v___x_1543_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1655_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v_k_1536_);
lean_ctor_set(v_reuseFailAlloc_1660_, 2, v_v_1537_);
lean_ctor_set(v_reuseFailAlloc_1660_, 3, v___x_1657_);
lean_ctor_set(v_reuseFailAlloc_1660_, 4, v_r_1539_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
else
{
lean_object* v_k_1662_; lean_object* v_v_1663_; lean_object* v___x_1665_; 
v_k_1662_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_k_1662_);
v_v_1663_ = lean_ctor_get(v___x_1545_, 1);
lean_inc(v_v_1663_);
lean_dec_ref(v___x_1545_);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 3, v_r_1539_);
v___x_1665_ = v___x_1619_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_size_1535_);
lean_ctor_set(v_reuseFailAlloc_1670_, 1, v_k_1536_);
lean_ctor_set(v_reuseFailAlloc_1670_, 2, v_v_1537_);
lean_ctor_set(v_reuseFailAlloc_1670_, 3, v_r_1539_);
lean_ctor_set(v_reuseFailAlloc_1670_, 4, v_r_1539_);
v___x_1665_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
lean_object* v___x_1666_; lean_object* v___x_1668_; 
v___x_1666_ = lean_unsigned_to_nat(2u);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 4, v___x_1665_);
lean_ctor_set(v___x_1543_, 3, v_r_1539_);
lean_ctor_set(v___x_1543_, 2, v_v_1663_);
lean_ctor_set(v___x_1543_, 1, v_k_1662_);
lean_ctor_set(v___x_1543_, 0, v___x_1666_);
v___x_1668_ = v___x_1543_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v___x_1666_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v_k_1662_);
lean_ctor_set(v_reuseFailAlloc_1669_, 2, v_v_1663_);
lean_ctor_set(v_reuseFailAlloc_1669_, 3, v_r_1539_);
lean_ctor_set(v_reuseFailAlloc_1669_, 4, v___x_1665_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
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
lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1835_; 
lean_inc(v_r_1539_);
lean_inc(v_v_1537_);
lean_inc(v_k_1536_);
v_isSharedCheck_1835_ = !lean_is_exclusive(v_r_1351_);
if (v_isSharedCheck_1835_ == 0)
{
lean_object* v_unused_1836_; lean_object* v_unused_1837_; lean_object* v_unused_1838_; lean_object* v_unused_1839_; lean_object* v_unused_1840_; 
v_unused_1836_ = lean_ctor_get(v_r_1351_, 4);
lean_dec(v_unused_1836_);
v_unused_1837_ = lean_ctor_get(v_r_1351_, 3);
lean_dec(v_unused_1837_);
v_unused_1838_ = lean_ctor_get(v_r_1351_, 2);
lean_dec(v_unused_1838_);
v_unused_1839_ = lean_ctor_get(v_r_1351_, 1);
lean_dec(v_unused_1839_);
v_unused_1840_ = lean_ctor_get(v_r_1351_, 0);
lean_dec(v_unused_1840_);
v___x_1684_ = v_r_1351_;
v_isShared_1685_ = v_isSharedCheck_1835_;
goto v_resetjp_1683_;
}
else
{
lean_dec(v_r_1351_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1835_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1686_; lean_object* v_tree_1687_; 
v___x_1686_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_1536_, v_v_1537_, v_l_1538_, v_r_1539_);
v_tree_1687_ = lean_ctor_get(v___x_1686_, 2);
lean_inc(v_tree_1687_);
if (lean_obj_tag(v_tree_1687_) == 0)
{
lean_object* v_k_1688_; lean_object* v_v_1689_; lean_object* v_size_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; uint8_t v___x_1693_; 
v_k_1688_ = lean_ctor_get(v___x_1686_, 0);
lean_inc(v_k_1688_);
v_v_1689_ = lean_ctor_get(v___x_1686_, 1);
lean_inc(v_v_1689_);
lean_dec_ref(v___x_1686_);
v_size_1690_ = lean_ctor_get(v_tree_1687_, 0);
v___x_1691_ = lean_unsigned_to_nat(3u);
v___x_1692_ = lean_nat_mul(v___x_1691_, v_size_1690_);
v___x_1693_ = lean_nat_dec_lt(v___x_1692_, v_size_1530_);
lean_dec(v___x_1692_);
if (v___x_1693_ == 0)
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1697_; 
lean_dec(v_r_1534_);
v___x_1694_ = lean_nat_add(v___x_1540_, v_size_1530_);
v___x_1695_ = lean_nat_add(v___x_1694_, v_size_1690_);
lean_dec(v___x_1694_);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 4, v_tree_1687_);
lean_ctor_set(v___x_1684_, 3, v_l_1350_);
lean_ctor_set(v___x_1684_, 2, v_v_1689_);
lean_ctor_set(v___x_1684_, 1, v_k_1688_);
lean_ctor_set(v___x_1684_, 0, v___x_1695_);
v___x_1697_ = v___x_1684_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v___x_1695_);
lean_ctor_set(v_reuseFailAlloc_1698_, 1, v_k_1688_);
lean_ctor_set(v_reuseFailAlloc_1698_, 2, v_v_1689_);
lean_ctor_set(v_reuseFailAlloc_1698_, 3, v_l_1350_);
lean_ctor_set(v_reuseFailAlloc_1698_, 4, v_tree_1687_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
else
{
lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1764_; 
lean_inc(v_l_1533_);
lean_inc(v_v_1532_);
lean_inc(v_k_1531_);
lean_inc(v_size_1530_);
v_isSharedCheck_1764_ = !lean_is_exclusive(v_l_1350_);
if (v_isSharedCheck_1764_ == 0)
{
lean_object* v_unused_1765_; lean_object* v_unused_1766_; lean_object* v_unused_1767_; lean_object* v_unused_1768_; lean_object* v_unused_1769_; 
v_unused_1765_ = lean_ctor_get(v_l_1350_, 4);
lean_dec(v_unused_1765_);
v_unused_1766_ = lean_ctor_get(v_l_1350_, 3);
lean_dec(v_unused_1766_);
v_unused_1767_ = lean_ctor_get(v_l_1350_, 2);
lean_dec(v_unused_1767_);
v_unused_1768_ = lean_ctor_get(v_l_1350_, 1);
lean_dec(v_unused_1768_);
v_unused_1769_ = lean_ctor_get(v_l_1350_, 0);
lean_dec(v_unused_1769_);
v___x_1700_ = v_l_1350_;
v_isShared_1701_ = v_isSharedCheck_1764_;
goto v_resetjp_1699_;
}
else
{
lean_dec(v_l_1350_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1764_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v_size_1702_; lean_object* v_size_1703_; lean_object* v_k_1704_; lean_object* v_v_1705_; lean_object* v_l_1706_; lean_object* v_r_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; uint8_t v___x_1710_; 
v_size_1702_ = lean_ctor_get(v_l_1533_, 0);
v_size_1703_ = lean_ctor_get(v_r_1534_, 0);
v_k_1704_ = lean_ctor_get(v_r_1534_, 1);
v_v_1705_ = lean_ctor_get(v_r_1534_, 2);
v_l_1706_ = lean_ctor_get(v_r_1534_, 3);
v_r_1707_ = lean_ctor_get(v_r_1534_, 4);
v___x_1708_ = lean_unsigned_to_nat(2u);
v___x_1709_ = lean_nat_mul(v___x_1708_, v_size_1702_);
v___x_1710_ = lean_nat_dec_lt(v_size_1703_, v___x_1709_);
lean_dec(v___x_1709_);
if (v___x_1710_ == 0)
{
lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1748_; 
lean_inc(v_r_1707_);
lean_inc(v_l_1706_);
lean_inc(v_v_1705_);
lean_inc(v_k_1704_);
lean_del_object(v___x_1700_);
v_isSharedCheck_1748_ = !lean_is_exclusive(v_r_1534_);
if (v_isSharedCheck_1748_ == 0)
{
lean_object* v_unused_1749_; lean_object* v_unused_1750_; lean_object* v_unused_1751_; lean_object* v_unused_1752_; lean_object* v_unused_1753_; 
v_unused_1749_ = lean_ctor_get(v_r_1534_, 4);
lean_dec(v_unused_1749_);
v_unused_1750_ = lean_ctor_get(v_r_1534_, 3);
lean_dec(v_unused_1750_);
v_unused_1751_ = lean_ctor_get(v_r_1534_, 2);
lean_dec(v_unused_1751_);
v_unused_1752_ = lean_ctor_get(v_r_1534_, 1);
lean_dec(v_unused_1752_);
v_unused_1753_ = lean_ctor_get(v_r_1534_, 0);
lean_dec(v_unused_1753_);
v___x_1712_ = v_r_1534_;
v_isShared_1713_ = v_isSharedCheck_1748_;
goto v_resetjp_1711_;
}
else
{
lean_dec(v_r_1534_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1748_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___x_1736_; lean_object* v___y_1738_; 
v___x_1714_ = lean_nat_add(v___x_1540_, v_size_1530_);
lean_dec(v_size_1530_);
v___x_1715_ = lean_nat_add(v___x_1714_, v_size_1690_);
lean_dec(v___x_1714_);
v___x_1736_ = lean_nat_add(v___x_1540_, v_size_1702_);
if (lean_obj_tag(v_l_1706_) == 0)
{
lean_object* v_size_1746_; 
v_size_1746_ = lean_ctor_get(v_l_1706_, 0);
lean_inc(v_size_1746_);
v___y_1738_ = v_size_1746_;
goto v___jp_1737_;
}
else
{
lean_object* v___x_1747_; 
v___x_1747_ = lean_unsigned_to_nat(0u);
v___y_1738_ = v___x_1747_;
goto v___jp_1737_;
}
v___jp_1716_:
{
lean_object* v___x_1720_; lean_object* v___x_1722_; 
v___x_1720_ = lean_nat_add(v___y_1718_, v___y_1719_);
lean_dec(v___y_1719_);
lean_dec(v___y_1718_);
lean_inc_ref(v_tree_1687_);
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 4, v_tree_1687_);
lean_ctor_set(v___x_1712_, 3, v_r_1707_);
lean_ctor_set(v___x_1712_, 2, v_v_1689_);
lean_ctor_set(v___x_1712_, 1, v_k_1688_);
lean_ctor_set(v___x_1712_, 0, v___x_1720_);
v___x_1722_ = v___x_1712_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v___x_1720_);
lean_ctor_set(v_reuseFailAlloc_1735_, 1, v_k_1688_);
lean_ctor_set(v_reuseFailAlloc_1735_, 2, v_v_1689_);
lean_ctor_set(v_reuseFailAlloc_1735_, 3, v_r_1707_);
lean_ctor_set(v_reuseFailAlloc_1735_, 4, v_tree_1687_);
v___x_1722_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1729_; 
v_isSharedCheck_1729_ = !lean_is_exclusive(v_tree_1687_);
if (v_isSharedCheck_1729_ == 0)
{
lean_object* v_unused_1730_; lean_object* v_unused_1731_; lean_object* v_unused_1732_; lean_object* v_unused_1733_; lean_object* v_unused_1734_; 
v_unused_1730_ = lean_ctor_get(v_tree_1687_, 4);
lean_dec(v_unused_1730_);
v_unused_1731_ = lean_ctor_get(v_tree_1687_, 3);
lean_dec(v_unused_1731_);
v_unused_1732_ = lean_ctor_get(v_tree_1687_, 2);
lean_dec(v_unused_1732_);
v_unused_1733_ = lean_ctor_get(v_tree_1687_, 1);
lean_dec(v_unused_1733_);
v_unused_1734_ = lean_ctor_get(v_tree_1687_, 0);
lean_dec(v_unused_1734_);
v___x_1724_ = v_tree_1687_;
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
else
{
lean_dec(v_tree_1687_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 4, v___x_1722_);
lean_ctor_set(v___x_1724_, 3, v___y_1717_);
lean_ctor_set(v___x_1724_, 2, v_v_1705_);
lean_ctor_set(v___x_1724_, 1, v_k_1704_);
lean_ctor_set(v___x_1724_, 0, v___x_1715_);
v___x_1727_ = v___x_1724_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1715_);
lean_ctor_set(v_reuseFailAlloc_1728_, 1, v_k_1704_);
lean_ctor_set(v_reuseFailAlloc_1728_, 2, v_v_1705_);
lean_ctor_set(v_reuseFailAlloc_1728_, 3, v___y_1717_);
lean_ctor_set(v_reuseFailAlloc_1728_, 4, v___x_1722_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
}
v___jp_1737_:
{
lean_object* v___x_1739_; lean_object* v___x_1741_; 
v___x_1739_ = lean_nat_add(v___x_1736_, v___y_1738_);
lean_dec(v___y_1738_);
lean_dec(v___x_1736_);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 4, v_l_1706_);
lean_ctor_set(v___x_1684_, 3, v_l_1533_);
lean_ctor_set(v___x_1684_, 2, v_v_1532_);
lean_ctor_set(v___x_1684_, 1, v_k_1531_);
lean_ctor_set(v___x_1684_, 0, v___x_1739_);
v___x_1741_ = v___x_1684_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1739_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v_k_1531_);
lean_ctor_set(v_reuseFailAlloc_1745_, 2, v_v_1532_);
lean_ctor_set(v_reuseFailAlloc_1745_, 3, v_l_1533_);
lean_ctor_set(v_reuseFailAlloc_1745_, 4, v_l_1706_);
v___x_1741_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
lean_object* v___x_1742_; 
v___x_1742_ = lean_nat_add(v___x_1540_, v_size_1690_);
if (lean_obj_tag(v_r_1707_) == 0)
{
lean_object* v_size_1743_; 
v_size_1743_ = lean_ctor_get(v_r_1707_, 0);
lean_inc(v_size_1743_);
v___y_1717_ = v___x_1741_;
v___y_1718_ = v___x_1742_;
v___y_1719_ = v_size_1743_;
goto v___jp_1716_;
}
else
{
lean_object* v___x_1744_; 
v___x_1744_ = lean_unsigned_to_nat(0u);
v___y_1717_ = v___x_1741_;
v___y_1718_ = v___x_1742_;
v___y_1719_ = v___x_1744_;
goto v___jp_1716_;
}
}
}
}
}
else
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1759_; 
v___x_1754_ = lean_nat_add(v___x_1540_, v_size_1530_);
lean_dec(v_size_1530_);
v___x_1755_ = lean_nat_add(v___x_1754_, v_size_1690_);
lean_dec(v___x_1754_);
v___x_1756_ = lean_nat_add(v___x_1540_, v_size_1690_);
v___x_1757_ = lean_nat_add(v___x_1756_, v_size_1703_);
lean_dec(v___x_1756_);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 4, v_tree_1687_);
lean_ctor_set(v___x_1684_, 3, v_r_1534_);
lean_ctor_set(v___x_1684_, 2, v_v_1689_);
lean_ctor_set(v___x_1684_, 1, v_k_1688_);
lean_ctor_set(v___x_1684_, 0, v___x_1757_);
v___x_1759_ = v___x_1684_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1757_);
lean_ctor_set(v_reuseFailAlloc_1763_, 1, v_k_1688_);
lean_ctor_set(v_reuseFailAlloc_1763_, 2, v_v_1689_);
lean_ctor_set(v_reuseFailAlloc_1763_, 3, v_r_1534_);
lean_ctor_set(v_reuseFailAlloc_1763_, 4, v_tree_1687_);
v___x_1759_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
lean_object* v___x_1761_; 
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 4, v___x_1759_);
lean_ctor_set(v___x_1700_, 0, v___x_1755_);
v___x_1761_ = v___x_1700_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1755_);
lean_ctor_set(v_reuseFailAlloc_1762_, 1, v_k_1531_);
lean_ctor_set(v_reuseFailAlloc_1762_, 2, v_v_1532_);
lean_ctor_set(v_reuseFailAlloc_1762_, 3, v_l_1533_);
lean_ctor_set(v_reuseFailAlloc_1762_, 4, v___x_1759_);
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
}
}
else
{
if (lean_obj_tag(v_l_1533_) == 0)
{
lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1793_; 
lean_inc_ref(v_l_1533_);
lean_inc(v_v_1532_);
lean_inc(v_k_1531_);
lean_inc(v_size_1530_);
v_isSharedCheck_1793_ = !lean_is_exclusive(v_l_1350_);
if (v_isSharedCheck_1793_ == 0)
{
lean_object* v_unused_1794_; lean_object* v_unused_1795_; lean_object* v_unused_1796_; lean_object* v_unused_1797_; lean_object* v_unused_1798_; 
v_unused_1794_ = lean_ctor_get(v_l_1350_, 4);
lean_dec(v_unused_1794_);
v_unused_1795_ = lean_ctor_get(v_l_1350_, 3);
lean_dec(v_unused_1795_);
v_unused_1796_ = lean_ctor_get(v_l_1350_, 2);
lean_dec(v_unused_1796_);
v_unused_1797_ = lean_ctor_get(v_l_1350_, 1);
lean_dec(v_unused_1797_);
v_unused_1798_ = lean_ctor_get(v_l_1350_, 0);
lean_dec(v_unused_1798_);
v___x_1771_ = v_l_1350_;
v_isShared_1772_ = v_isSharedCheck_1793_;
goto v_resetjp_1770_;
}
else
{
lean_dec(v_l_1350_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1793_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
if (lean_obj_tag(v_r_1534_) == 0)
{
lean_object* v_k_1773_; lean_object* v_v_1774_; lean_object* v_size_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1779_; 
v_k_1773_ = lean_ctor_get(v___x_1686_, 0);
lean_inc(v_k_1773_);
v_v_1774_ = lean_ctor_get(v___x_1686_, 1);
lean_inc(v_v_1774_);
lean_dec_ref(v___x_1686_);
v_size_1775_ = lean_ctor_get(v_r_1534_, 0);
v___x_1776_ = lean_nat_add(v___x_1540_, v_size_1530_);
lean_dec(v_size_1530_);
v___x_1777_ = lean_nat_add(v___x_1540_, v_size_1775_);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 4, v_tree_1687_);
lean_ctor_set(v___x_1684_, 3, v_r_1534_);
lean_ctor_set(v___x_1684_, 2, v_v_1774_);
lean_ctor_set(v___x_1684_, 1, v_k_1773_);
lean_ctor_set(v___x_1684_, 0, v___x_1777_);
v___x_1779_ = v___x_1684_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v___x_1777_);
lean_ctor_set(v_reuseFailAlloc_1783_, 1, v_k_1773_);
lean_ctor_set(v_reuseFailAlloc_1783_, 2, v_v_1774_);
lean_ctor_set(v_reuseFailAlloc_1783_, 3, v_r_1534_);
lean_ctor_set(v_reuseFailAlloc_1783_, 4, v_tree_1687_);
v___x_1779_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
lean_object* v___x_1781_; 
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 4, v___x_1779_);
lean_ctor_set(v___x_1771_, 0, v___x_1776_);
v___x_1781_ = v___x_1771_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1776_);
lean_ctor_set(v_reuseFailAlloc_1782_, 1, v_k_1531_);
lean_ctor_set(v_reuseFailAlloc_1782_, 2, v_v_1532_);
lean_ctor_set(v_reuseFailAlloc_1782_, 3, v_l_1533_);
lean_ctor_set(v_reuseFailAlloc_1782_, 4, v___x_1779_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
else
{
lean_object* v_k_1784_; lean_object* v_v_1785_; lean_object* v___x_1786_; lean_object* v___x_1788_; 
lean_dec(v_size_1530_);
v_k_1784_ = lean_ctor_get(v___x_1686_, 0);
lean_inc(v_k_1784_);
v_v_1785_ = lean_ctor_get(v___x_1686_, 1);
lean_inc(v_v_1785_);
lean_dec_ref(v___x_1686_);
v___x_1786_ = lean_unsigned_to_nat(3u);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 4, v_r_1534_);
lean_ctor_set(v___x_1684_, 3, v_r_1534_);
lean_ctor_set(v___x_1684_, 2, v_v_1785_);
lean_ctor_set(v___x_1684_, 1, v_k_1784_);
lean_ctor_set(v___x_1684_, 0, v___x_1540_);
v___x_1788_ = v___x_1684_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v___x_1540_);
lean_ctor_set(v_reuseFailAlloc_1792_, 1, v_k_1784_);
lean_ctor_set(v_reuseFailAlloc_1792_, 2, v_v_1785_);
lean_ctor_set(v_reuseFailAlloc_1792_, 3, v_r_1534_);
lean_ctor_set(v_reuseFailAlloc_1792_, 4, v_r_1534_);
v___x_1788_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
lean_object* v___x_1790_; 
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 4, v___x_1788_);
lean_ctor_set(v___x_1771_, 0, v___x_1786_);
v___x_1790_ = v___x_1771_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1786_);
lean_ctor_set(v_reuseFailAlloc_1791_, 1, v_k_1531_);
lean_ctor_set(v_reuseFailAlloc_1791_, 2, v_v_1532_);
lean_ctor_set(v_reuseFailAlloc_1791_, 3, v_l_1533_);
lean_ctor_set(v_reuseFailAlloc_1791_, 4, v___x_1788_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1534_) == 0)
{
lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1823_; 
lean_inc(v_l_1533_);
lean_inc(v_v_1532_);
lean_inc(v_k_1531_);
v_isSharedCheck_1823_ = !lean_is_exclusive(v_l_1350_);
if (v_isSharedCheck_1823_ == 0)
{
lean_object* v_unused_1824_; lean_object* v_unused_1825_; lean_object* v_unused_1826_; lean_object* v_unused_1827_; lean_object* v_unused_1828_; 
v_unused_1824_ = lean_ctor_get(v_l_1350_, 4);
lean_dec(v_unused_1824_);
v_unused_1825_ = lean_ctor_get(v_l_1350_, 3);
lean_dec(v_unused_1825_);
v_unused_1826_ = lean_ctor_get(v_l_1350_, 2);
lean_dec(v_unused_1826_);
v_unused_1827_ = lean_ctor_get(v_l_1350_, 1);
lean_dec(v_unused_1827_);
v_unused_1828_ = lean_ctor_get(v_l_1350_, 0);
lean_dec(v_unused_1828_);
v___x_1800_ = v_l_1350_;
v_isShared_1801_ = v_isSharedCheck_1823_;
goto v_resetjp_1799_;
}
else
{
lean_dec(v_l_1350_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1823_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v_k_1802_; lean_object* v_v_1803_; lean_object* v_k_1804_; lean_object* v_v_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1819_; 
v_k_1802_ = lean_ctor_get(v___x_1686_, 0);
lean_inc(v_k_1802_);
v_v_1803_ = lean_ctor_get(v___x_1686_, 1);
lean_inc(v_v_1803_);
lean_dec_ref(v___x_1686_);
v_k_1804_ = lean_ctor_get(v_r_1534_, 1);
v_v_1805_ = lean_ctor_get(v_r_1534_, 2);
v_isSharedCheck_1819_ = !lean_is_exclusive(v_r_1534_);
if (v_isSharedCheck_1819_ == 0)
{
lean_object* v_unused_1820_; lean_object* v_unused_1821_; lean_object* v_unused_1822_; 
v_unused_1820_ = lean_ctor_get(v_r_1534_, 4);
lean_dec(v_unused_1820_);
v_unused_1821_ = lean_ctor_get(v_r_1534_, 3);
lean_dec(v_unused_1821_);
v_unused_1822_ = lean_ctor_get(v_r_1534_, 0);
lean_dec(v_unused_1822_);
v___x_1807_ = v_r_1534_;
v_isShared_1808_ = v_isSharedCheck_1819_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_v_1805_);
lean_inc(v_k_1804_);
lean_dec(v_r_1534_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1819_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1809_; lean_object* v___x_1811_; 
v___x_1809_ = lean_unsigned_to_nat(3u);
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 4, v_l_1533_);
lean_ctor_set(v___x_1807_, 3, v_l_1533_);
lean_ctor_set(v___x_1807_, 2, v_v_1532_);
lean_ctor_set(v___x_1807_, 1, v_k_1531_);
lean_ctor_set(v___x_1807_, 0, v___x_1540_);
v___x_1811_ = v___x_1807_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1540_);
lean_ctor_set(v_reuseFailAlloc_1818_, 1, v_k_1531_);
lean_ctor_set(v_reuseFailAlloc_1818_, 2, v_v_1532_);
lean_ctor_set(v_reuseFailAlloc_1818_, 3, v_l_1533_);
lean_ctor_set(v_reuseFailAlloc_1818_, 4, v_l_1533_);
v___x_1811_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
lean_object* v___x_1813_; 
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 4, v_l_1533_);
lean_ctor_set(v___x_1684_, 3, v_l_1533_);
lean_ctor_set(v___x_1684_, 2, v_v_1803_);
lean_ctor_set(v___x_1684_, 1, v_k_1802_);
lean_ctor_set(v___x_1684_, 0, v___x_1540_);
v___x_1813_ = v___x_1684_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v___x_1540_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v_k_1802_);
lean_ctor_set(v_reuseFailAlloc_1817_, 2, v_v_1803_);
lean_ctor_set(v_reuseFailAlloc_1817_, 3, v_l_1533_);
lean_ctor_set(v_reuseFailAlloc_1817_, 4, v_l_1533_);
v___x_1813_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
lean_object* v___x_1815_; 
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 4, v___x_1813_);
lean_ctor_set(v___x_1800_, 3, v___x_1811_);
lean_ctor_set(v___x_1800_, 2, v_v_1805_);
lean_ctor_set(v___x_1800_, 1, v_k_1804_);
lean_ctor_set(v___x_1800_, 0, v___x_1809_);
v___x_1815_ = v___x_1800_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1809_);
lean_ctor_set(v_reuseFailAlloc_1816_, 1, v_k_1804_);
lean_ctor_set(v_reuseFailAlloc_1816_, 2, v_v_1805_);
lean_ctor_set(v_reuseFailAlloc_1816_, 3, v___x_1811_);
lean_ctor_set(v_reuseFailAlloc_1816_, 4, v___x_1813_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
}
}
}
else
{
lean_object* v_k_1829_; lean_object* v_v_1830_; lean_object* v___x_1831_; lean_object* v___x_1833_; 
v_k_1829_ = lean_ctor_get(v___x_1686_, 0);
lean_inc(v_k_1829_);
v_v_1830_ = lean_ctor_get(v___x_1686_, 1);
lean_inc(v_v_1830_);
lean_dec_ref(v___x_1686_);
v___x_1831_ = lean_unsigned_to_nat(2u);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 4, v_r_1534_);
lean_ctor_set(v___x_1684_, 3, v_l_1350_);
lean_ctor_set(v___x_1684_, 2, v_v_1830_);
lean_ctor_set(v___x_1684_, 1, v_k_1829_);
lean_ctor_set(v___x_1684_, 0, v___x_1831_);
v___x_1833_ = v___x_1684_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1831_);
lean_ctor_set(v_reuseFailAlloc_1834_, 1, v_k_1829_);
lean_ctor_set(v_reuseFailAlloc_1834_, 2, v_v_1830_);
lean_ctor_set(v_reuseFailAlloc_1834_, 3, v_l_1350_);
lean_ctor_set(v_reuseFailAlloc_1834_, 4, v_r_1534_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
}
}
}
}
}
else
{
return v_l_1350_;
}
}
else
{
return v_r_1351_;
}
}
default: 
{
lean_object* v_impl_1841_; lean_object* v___x_1842_; 
v_impl_1841_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_1346_, v_r_1351_);
v___x_1842_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1841_) == 0)
{
if (lean_obj_tag(v_l_1350_) == 0)
{
lean_object* v_size_1843_; lean_object* v_size_1844_; lean_object* v_k_1845_; lean_object* v_v_1846_; lean_object* v_l_1847_; lean_object* v_r_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; uint8_t v___x_1851_; 
v_size_1843_ = lean_ctor_get(v_impl_1841_, 0);
lean_inc(v_size_1843_);
v_size_1844_ = lean_ctor_get(v_l_1350_, 0);
v_k_1845_ = lean_ctor_get(v_l_1350_, 1);
v_v_1846_ = lean_ctor_get(v_l_1350_, 2);
v_l_1847_ = lean_ctor_get(v_l_1350_, 3);
v_r_1848_ = lean_ctor_get(v_l_1350_, 4);
lean_inc(v_r_1848_);
v___x_1849_ = lean_unsigned_to_nat(3u);
v___x_1850_ = lean_nat_mul(v___x_1849_, v_size_1843_);
v___x_1851_ = lean_nat_dec_lt(v___x_1850_, v_size_1844_);
lean_dec(v___x_1850_);
if (v___x_1851_ == 0)
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1855_; 
lean_dec(v_r_1848_);
v___x_1852_ = lean_nat_add(v___x_1842_, v_size_1844_);
v___x_1853_ = lean_nat_add(v___x_1852_, v_size_1843_);
lean_dec(v_size_1843_);
lean_dec(v___x_1852_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 4, v_impl_1841_);
lean_ctor_set(v___x_1353_, 0, v___x_1853_);
v___x_1855_ = v___x_1353_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1853_);
lean_ctor_set(v_reuseFailAlloc_1856_, 1, v_k_1348_);
lean_ctor_set(v_reuseFailAlloc_1856_, 2, v_v_1349_);
lean_ctor_set(v_reuseFailAlloc_1856_, 3, v_l_1350_);
lean_ctor_set(v_reuseFailAlloc_1856_, 4, v_impl_1841_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
else
{
lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1922_; 
lean_inc(v_l_1847_);
lean_inc(v_v_1846_);
lean_inc(v_k_1845_);
lean_inc(v_size_1844_);
v_isSharedCheck_1922_ = !lean_is_exclusive(v_l_1350_);
if (v_isSharedCheck_1922_ == 0)
{
lean_object* v_unused_1923_; lean_object* v_unused_1924_; lean_object* v_unused_1925_; lean_object* v_unused_1926_; lean_object* v_unused_1927_; 
v_unused_1923_ = lean_ctor_get(v_l_1350_, 4);
lean_dec(v_unused_1923_);
v_unused_1924_ = lean_ctor_get(v_l_1350_, 3);
lean_dec(v_unused_1924_);
v_unused_1925_ = lean_ctor_get(v_l_1350_, 2);
lean_dec(v_unused_1925_);
v_unused_1926_ = lean_ctor_get(v_l_1350_, 1);
lean_dec(v_unused_1926_);
v_unused_1927_ = lean_ctor_get(v_l_1350_, 0);
lean_dec(v_unused_1927_);
v___x_1858_ = v_l_1350_;
v_isShared_1859_ = v_isSharedCheck_1922_;
goto v_resetjp_1857_;
}
else
{
lean_dec(v_l_1350_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1922_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v_size_1860_; lean_object* v_size_1861_; lean_object* v_k_1862_; lean_object* v_v_1863_; lean_object* v_l_1864_; lean_object* v_r_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; uint8_t v___x_1868_; 
v_size_1860_ = lean_ctor_get(v_l_1847_, 0);
v_size_1861_ = lean_ctor_get(v_r_1848_, 0);
v_k_1862_ = lean_ctor_get(v_r_1848_, 1);
v_v_1863_ = lean_ctor_get(v_r_1848_, 2);
v_l_1864_ = lean_ctor_get(v_r_1848_, 3);
v_r_1865_ = lean_ctor_get(v_r_1848_, 4);
v___x_1866_ = lean_unsigned_to_nat(2u);
v___x_1867_ = lean_nat_mul(v___x_1866_, v_size_1860_);
v___x_1868_ = lean_nat_dec_lt(v_size_1861_, v___x_1867_);
lean_dec(v___x_1867_);
if (v___x_1868_ == 0)
{
lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1897_; 
lean_inc(v_r_1865_);
lean_inc(v_l_1864_);
lean_inc(v_v_1863_);
lean_inc(v_k_1862_);
v_isSharedCheck_1897_ = !lean_is_exclusive(v_r_1848_);
if (v_isSharedCheck_1897_ == 0)
{
lean_object* v_unused_1898_; lean_object* v_unused_1899_; lean_object* v_unused_1900_; lean_object* v_unused_1901_; lean_object* v_unused_1902_; 
v_unused_1898_ = lean_ctor_get(v_r_1848_, 4);
lean_dec(v_unused_1898_);
v_unused_1899_ = lean_ctor_get(v_r_1848_, 3);
lean_dec(v_unused_1899_);
v_unused_1900_ = lean_ctor_get(v_r_1848_, 2);
lean_dec(v_unused_1900_);
v_unused_1901_ = lean_ctor_get(v_r_1848_, 1);
lean_dec(v_unused_1901_);
v_unused_1902_ = lean_ctor_get(v_r_1848_, 0);
lean_dec(v_unused_1902_);
v___x_1870_ = v_r_1848_;
v_isShared_1871_ = v_isSharedCheck_1897_;
goto v_resetjp_1869_;
}
else
{
lean_dec(v_r_1848_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1897_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v___x_1885_; lean_object* v___y_1887_; 
v___x_1872_ = lean_nat_add(v___x_1842_, v_size_1844_);
lean_dec(v_size_1844_);
v___x_1873_ = lean_nat_add(v___x_1872_, v_size_1843_);
lean_dec(v___x_1872_);
v___x_1885_ = lean_nat_add(v___x_1842_, v_size_1860_);
if (lean_obj_tag(v_l_1864_) == 0)
{
lean_object* v_size_1895_; 
v_size_1895_ = lean_ctor_get(v_l_1864_, 0);
lean_inc(v_size_1895_);
v___y_1887_ = v_size_1895_;
goto v___jp_1886_;
}
else
{
lean_object* v___x_1896_; 
v___x_1896_ = lean_unsigned_to_nat(0u);
v___y_1887_ = v___x_1896_;
goto v___jp_1886_;
}
v___jp_1874_:
{
lean_object* v___x_1878_; lean_object* v___x_1880_; 
v___x_1878_ = lean_nat_add(v___y_1875_, v___y_1877_);
lean_dec(v___y_1877_);
lean_dec(v___y_1875_);
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 4, v_impl_1841_);
lean_ctor_set(v___x_1870_, 3, v_r_1865_);
lean_ctor_set(v___x_1870_, 2, v_v_1349_);
lean_ctor_set(v___x_1870_, 1, v_k_1348_);
lean_ctor_set(v___x_1870_, 0, v___x_1878_);
v___x_1880_ = v___x_1870_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v___x_1878_);
lean_ctor_set(v_reuseFailAlloc_1884_, 1, v_k_1348_);
lean_ctor_set(v_reuseFailAlloc_1884_, 2, v_v_1349_);
lean_ctor_set(v_reuseFailAlloc_1884_, 3, v_r_1865_);
lean_ctor_set(v_reuseFailAlloc_1884_, 4, v_impl_1841_);
v___x_1880_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
lean_object* v___x_1882_; 
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 4, v___x_1880_);
lean_ctor_set(v___x_1858_, 3, v___y_1876_);
lean_ctor_set(v___x_1858_, 2, v_v_1863_);
lean_ctor_set(v___x_1858_, 1, v_k_1862_);
lean_ctor_set(v___x_1858_, 0, v___x_1873_);
v___x_1882_ = v___x_1858_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v___x_1873_);
lean_ctor_set(v_reuseFailAlloc_1883_, 1, v_k_1862_);
lean_ctor_set(v_reuseFailAlloc_1883_, 2, v_v_1863_);
lean_ctor_set(v_reuseFailAlloc_1883_, 3, v___y_1876_);
lean_ctor_set(v_reuseFailAlloc_1883_, 4, v___x_1880_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
v___jp_1886_:
{
lean_object* v___x_1888_; lean_object* v___x_1890_; 
v___x_1888_ = lean_nat_add(v___x_1885_, v___y_1887_);
lean_dec(v___y_1887_);
lean_dec(v___x_1885_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 4, v_l_1864_);
lean_ctor_set(v___x_1353_, 3, v_l_1847_);
lean_ctor_set(v___x_1353_, 2, v_v_1846_);
lean_ctor_set(v___x_1353_, 1, v_k_1845_);
lean_ctor_set(v___x_1353_, 0, v___x_1888_);
v___x_1890_ = v___x_1353_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1888_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v_k_1845_);
lean_ctor_set(v_reuseFailAlloc_1894_, 2, v_v_1846_);
lean_ctor_set(v_reuseFailAlloc_1894_, 3, v_l_1847_);
lean_ctor_set(v_reuseFailAlloc_1894_, 4, v_l_1864_);
v___x_1890_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1891_; 
v___x_1891_ = lean_nat_add(v___x_1842_, v_size_1843_);
lean_dec(v_size_1843_);
if (lean_obj_tag(v_r_1865_) == 0)
{
lean_object* v_size_1892_; 
v_size_1892_ = lean_ctor_get(v_r_1865_, 0);
lean_inc(v_size_1892_);
v___y_1875_ = v___x_1891_;
v___y_1876_ = v___x_1890_;
v___y_1877_ = v_size_1892_;
goto v___jp_1874_;
}
else
{
lean_object* v___x_1893_; 
v___x_1893_ = lean_unsigned_to_nat(0u);
v___y_1875_ = v___x_1891_;
v___y_1876_ = v___x_1890_;
v___y_1877_ = v___x_1893_;
goto v___jp_1874_;
}
}
}
}
}
else
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1908_; 
lean_del_object(v___x_1353_);
v___x_1903_ = lean_nat_add(v___x_1842_, v_size_1844_);
lean_dec(v_size_1844_);
v___x_1904_ = lean_nat_add(v___x_1903_, v_size_1843_);
lean_dec(v___x_1903_);
v___x_1905_ = lean_nat_add(v___x_1842_, v_size_1843_);
lean_dec(v_size_1843_);
v___x_1906_ = lean_nat_add(v___x_1905_, v_size_1861_);
lean_dec(v___x_1905_);
lean_inc_ref(v_impl_1841_);
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 4, v_impl_1841_);
lean_ctor_set(v___x_1858_, 3, v_r_1848_);
lean_ctor_set(v___x_1858_, 2, v_v_1349_);
lean_ctor_set(v___x_1858_, 1, v_k_1348_);
lean_ctor_set(v___x_1858_, 0, v___x_1906_);
v___x_1908_ = v___x_1858_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1906_);
lean_ctor_set(v_reuseFailAlloc_1921_, 1, v_k_1348_);
lean_ctor_set(v_reuseFailAlloc_1921_, 2, v_v_1349_);
lean_ctor_set(v_reuseFailAlloc_1921_, 3, v_r_1848_);
lean_ctor_set(v_reuseFailAlloc_1921_, 4, v_impl_1841_);
v___x_1908_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1915_; 
v_isSharedCheck_1915_ = !lean_is_exclusive(v_impl_1841_);
if (v_isSharedCheck_1915_ == 0)
{
lean_object* v_unused_1916_; lean_object* v_unused_1917_; lean_object* v_unused_1918_; lean_object* v_unused_1919_; lean_object* v_unused_1920_; 
v_unused_1916_ = lean_ctor_get(v_impl_1841_, 4);
lean_dec(v_unused_1916_);
v_unused_1917_ = lean_ctor_get(v_impl_1841_, 3);
lean_dec(v_unused_1917_);
v_unused_1918_ = lean_ctor_get(v_impl_1841_, 2);
lean_dec(v_unused_1918_);
v_unused_1919_ = lean_ctor_get(v_impl_1841_, 1);
lean_dec(v_unused_1919_);
v_unused_1920_ = lean_ctor_get(v_impl_1841_, 0);
lean_dec(v_unused_1920_);
v___x_1910_ = v_impl_1841_;
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
else
{
lean_dec(v_impl_1841_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 4, v___x_1908_);
lean_ctor_set(v___x_1910_, 3, v_l_1847_);
lean_ctor_set(v___x_1910_, 2, v_v_1846_);
lean_ctor_set(v___x_1910_, 1, v_k_1845_);
lean_ctor_set(v___x_1910_, 0, v___x_1904_);
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1904_);
lean_ctor_set(v_reuseFailAlloc_1914_, 1, v_k_1845_);
lean_ctor_set(v_reuseFailAlloc_1914_, 2, v_v_1846_);
lean_ctor_set(v_reuseFailAlloc_1914_, 3, v_l_1847_);
lean_ctor_set(v_reuseFailAlloc_1914_, 4, v___x_1908_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1928_; lean_object* v___x_1929_; lean_object* v___x_1931_; 
v_size_1928_ = lean_ctor_get(v_impl_1841_, 0);
lean_inc(v_size_1928_);
v___x_1929_ = lean_nat_add(v___x_1842_, v_size_1928_);
lean_dec(v_size_1928_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 4, v_impl_1841_);
lean_ctor_set(v___x_1353_, 0, v___x_1929_);
v___x_1931_ = v___x_1353_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v___x_1929_);
lean_ctor_set(v_reuseFailAlloc_1932_, 1, v_k_1348_);
lean_ctor_set(v_reuseFailAlloc_1932_, 2, v_v_1349_);
lean_ctor_set(v_reuseFailAlloc_1932_, 3, v_l_1350_);
lean_ctor_set(v_reuseFailAlloc_1932_, 4, v_impl_1841_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
else
{
if (lean_obj_tag(v_l_1350_) == 0)
{
lean_object* v_l_1933_; 
v_l_1933_ = lean_ctor_get(v_l_1350_, 3);
if (lean_obj_tag(v_l_1933_) == 0)
{
lean_object* v_r_1934_; 
lean_inc_ref(v_l_1933_);
v_r_1934_ = lean_ctor_get(v_l_1350_, 4);
lean_inc(v_r_1934_);
if (lean_obj_tag(v_r_1934_) == 0)
{
lean_object* v_size_1935_; lean_object* v_k_1936_; lean_object* v_v_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1950_; 
v_size_1935_ = lean_ctor_get(v_l_1350_, 0);
v_k_1936_ = lean_ctor_get(v_l_1350_, 1);
v_v_1937_ = lean_ctor_get(v_l_1350_, 2);
v_isSharedCheck_1950_ = !lean_is_exclusive(v_l_1350_);
if (v_isSharedCheck_1950_ == 0)
{
lean_object* v_unused_1951_; lean_object* v_unused_1952_; 
v_unused_1951_ = lean_ctor_get(v_l_1350_, 4);
lean_dec(v_unused_1951_);
v_unused_1952_ = lean_ctor_get(v_l_1350_, 3);
lean_dec(v_unused_1952_);
v___x_1939_ = v_l_1350_;
v_isShared_1940_ = v_isSharedCheck_1950_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_v_1937_);
lean_inc(v_k_1936_);
lean_inc(v_size_1935_);
lean_dec(v_l_1350_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1950_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v_size_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1945_; 
v_size_1941_ = lean_ctor_get(v_r_1934_, 0);
v___x_1942_ = lean_nat_add(v___x_1842_, v_size_1935_);
lean_dec(v_size_1935_);
v___x_1943_ = lean_nat_add(v___x_1842_, v_size_1941_);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 4, v_impl_1841_);
lean_ctor_set(v___x_1939_, 3, v_r_1934_);
lean_ctor_set(v___x_1939_, 2, v_v_1349_);
lean_ctor_set(v___x_1939_, 1, v_k_1348_);
lean_ctor_set(v___x_1939_, 0, v___x_1943_);
v___x_1945_ = v___x_1939_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v___x_1943_);
lean_ctor_set(v_reuseFailAlloc_1949_, 1, v_k_1348_);
lean_ctor_set(v_reuseFailAlloc_1949_, 2, v_v_1349_);
lean_ctor_set(v_reuseFailAlloc_1949_, 3, v_r_1934_);
lean_ctor_set(v_reuseFailAlloc_1949_, 4, v_impl_1841_);
v___x_1945_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
lean_object* v___x_1947_; 
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 4, v___x_1945_);
lean_ctor_set(v___x_1353_, 3, v_l_1933_);
lean_ctor_set(v___x_1353_, 2, v_v_1937_);
lean_ctor_set(v___x_1353_, 1, v_k_1936_);
lean_ctor_set(v___x_1353_, 0, v___x_1942_);
v___x_1947_ = v___x_1353_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1942_);
lean_ctor_set(v_reuseFailAlloc_1948_, 1, v_k_1936_);
lean_ctor_set(v_reuseFailAlloc_1948_, 2, v_v_1937_);
lean_ctor_set(v_reuseFailAlloc_1948_, 3, v_l_1933_);
lean_ctor_set(v_reuseFailAlloc_1948_, 4, v___x_1945_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
else
{
lean_object* v_k_1953_; lean_object* v_v_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1965_; 
v_k_1953_ = lean_ctor_get(v_l_1350_, 1);
v_v_1954_ = lean_ctor_get(v_l_1350_, 2);
v_isSharedCheck_1965_ = !lean_is_exclusive(v_l_1350_);
if (v_isSharedCheck_1965_ == 0)
{
lean_object* v_unused_1966_; lean_object* v_unused_1967_; lean_object* v_unused_1968_; 
v_unused_1966_ = lean_ctor_get(v_l_1350_, 4);
lean_dec(v_unused_1966_);
v_unused_1967_ = lean_ctor_get(v_l_1350_, 3);
lean_dec(v_unused_1967_);
v_unused_1968_ = lean_ctor_get(v_l_1350_, 0);
lean_dec(v_unused_1968_);
v___x_1956_ = v_l_1350_;
v_isShared_1957_ = v_isSharedCheck_1965_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_v_1954_);
lean_inc(v_k_1953_);
lean_dec(v_l_1350_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1965_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1958_; lean_object* v___x_1960_; 
v___x_1958_ = lean_unsigned_to_nat(3u);
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 3, v_r_1934_);
lean_ctor_set(v___x_1956_, 2, v_v_1349_);
lean_ctor_set(v___x_1956_, 1, v_k_1348_);
lean_ctor_set(v___x_1956_, 0, v___x_1842_);
v___x_1960_ = v___x_1956_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___x_1842_);
lean_ctor_set(v_reuseFailAlloc_1964_, 1, v_k_1348_);
lean_ctor_set(v_reuseFailAlloc_1964_, 2, v_v_1349_);
lean_ctor_set(v_reuseFailAlloc_1964_, 3, v_r_1934_);
lean_ctor_set(v_reuseFailAlloc_1964_, 4, v_r_1934_);
v___x_1960_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
lean_object* v___x_1962_; 
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 4, v___x_1960_);
lean_ctor_set(v___x_1353_, 3, v_l_1933_);
lean_ctor_set(v___x_1353_, 2, v_v_1954_);
lean_ctor_set(v___x_1353_, 1, v_k_1953_);
lean_ctor_set(v___x_1353_, 0, v___x_1958_);
v___x_1962_ = v___x_1353_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v___x_1958_);
lean_ctor_set(v_reuseFailAlloc_1963_, 1, v_k_1953_);
lean_ctor_set(v_reuseFailAlloc_1963_, 2, v_v_1954_);
lean_ctor_set(v_reuseFailAlloc_1963_, 3, v_l_1933_);
lean_ctor_set(v_reuseFailAlloc_1963_, 4, v___x_1960_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
}
else
{
lean_object* v_r_1969_; 
v_r_1969_ = lean_ctor_get(v_l_1350_, 4);
lean_inc(v_r_1969_);
if (lean_obj_tag(v_r_1969_) == 0)
{
lean_object* v_k_1970_; lean_object* v_v_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1994_; 
lean_inc(v_l_1933_);
v_k_1970_ = lean_ctor_get(v_l_1350_, 1);
v_v_1971_ = lean_ctor_get(v_l_1350_, 2);
v_isSharedCheck_1994_ = !lean_is_exclusive(v_l_1350_);
if (v_isSharedCheck_1994_ == 0)
{
lean_object* v_unused_1995_; lean_object* v_unused_1996_; lean_object* v_unused_1997_; 
v_unused_1995_ = lean_ctor_get(v_l_1350_, 4);
lean_dec(v_unused_1995_);
v_unused_1996_ = lean_ctor_get(v_l_1350_, 3);
lean_dec(v_unused_1996_);
v_unused_1997_ = lean_ctor_get(v_l_1350_, 0);
lean_dec(v_unused_1997_);
v___x_1973_ = v_l_1350_;
v_isShared_1974_ = v_isSharedCheck_1994_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_v_1971_);
lean_inc(v_k_1970_);
lean_dec(v_l_1350_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1994_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v_k_1975_; lean_object* v_v_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1990_; 
v_k_1975_ = lean_ctor_get(v_r_1969_, 1);
v_v_1976_ = lean_ctor_get(v_r_1969_, 2);
v_isSharedCheck_1990_ = !lean_is_exclusive(v_r_1969_);
if (v_isSharedCheck_1990_ == 0)
{
lean_object* v_unused_1991_; lean_object* v_unused_1992_; lean_object* v_unused_1993_; 
v_unused_1991_ = lean_ctor_get(v_r_1969_, 4);
lean_dec(v_unused_1991_);
v_unused_1992_ = lean_ctor_get(v_r_1969_, 3);
lean_dec(v_unused_1992_);
v_unused_1993_ = lean_ctor_get(v_r_1969_, 0);
lean_dec(v_unused_1993_);
v___x_1978_ = v_r_1969_;
v_isShared_1979_ = v_isSharedCheck_1990_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_v_1976_);
lean_inc(v_k_1975_);
lean_dec(v_r_1969_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1990_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1980_; lean_object* v___x_1982_; 
v___x_1980_ = lean_unsigned_to_nat(3u);
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 4, v_l_1933_);
lean_ctor_set(v___x_1978_, 3, v_l_1933_);
lean_ctor_set(v___x_1978_, 2, v_v_1971_);
lean_ctor_set(v___x_1978_, 1, v_k_1970_);
lean_ctor_set(v___x_1978_, 0, v___x_1842_);
v___x_1982_ = v___x_1978_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v___x_1842_);
lean_ctor_set(v_reuseFailAlloc_1989_, 1, v_k_1970_);
lean_ctor_set(v_reuseFailAlloc_1989_, 2, v_v_1971_);
lean_ctor_set(v_reuseFailAlloc_1989_, 3, v_l_1933_);
lean_ctor_set(v_reuseFailAlloc_1989_, 4, v_l_1933_);
v___x_1982_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
lean_object* v___x_1984_; 
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 4, v_l_1933_);
lean_ctor_set(v___x_1973_, 2, v_v_1349_);
lean_ctor_set(v___x_1973_, 1, v_k_1348_);
lean_ctor_set(v___x_1973_, 0, v___x_1842_);
v___x_1984_ = v___x_1973_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1842_);
lean_ctor_set(v_reuseFailAlloc_1988_, 1, v_k_1348_);
lean_ctor_set(v_reuseFailAlloc_1988_, 2, v_v_1349_);
lean_ctor_set(v_reuseFailAlloc_1988_, 3, v_l_1933_);
lean_ctor_set(v_reuseFailAlloc_1988_, 4, v_l_1933_);
v___x_1984_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
lean_object* v___x_1986_; 
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 4, v___x_1984_);
lean_ctor_set(v___x_1353_, 3, v___x_1982_);
lean_ctor_set(v___x_1353_, 2, v_v_1976_);
lean_ctor_set(v___x_1353_, 1, v_k_1975_);
lean_ctor_set(v___x_1353_, 0, v___x_1980_);
v___x_1986_ = v___x_1353_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___x_1980_);
lean_ctor_set(v_reuseFailAlloc_1987_, 1, v_k_1975_);
lean_ctor_set(v_reuseFailAlloc_1987_, 2, v_v_1976_);
lean_ctor_set(v_reuseFailAlloc_1987_, 3, v___x_1982_);
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
}
else
{
lean_object* v___x_1998_; lean_object* v___x_2000_; 
v___x_1998_ = lean_unsigned_to_nat(2u);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 4, v_r_1969_);
lean_ctor_set(v___x_1353_, 0, v___x_1998_);
v___x_2000_ = v___x_1353_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1998_);
lean_ctor_set(v_reuseFailAlloc_2001_, 1, v_k_1348_);
lean_ctor_set(v_reuseFailAlloc_2001_, 2, v_v_1349_);
lean_ctor_set(v_reuseFailAlloc_2001_, 3, v_l_1350_);
lean_ctor_set(v_reuseFailAlloc_2001_, 4, v_r_1969_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
else
{
lean_object* v___x_2003_; 
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 4, v_l_1350_);
lean_ctor_set(v___x_1353_, 0, v___x_1842_);
v___x_2003_ = v___x_1353_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v___x_1842_);
lean_ctor_set(v_reuseFailAlloc_2004_, 1, v_k_1348_);
lean_ctor_set(v_reuseFailAlloc_2004_, 2, v_v_1349_);
lean_ctor_set(v_reuseFailAlloc_2004_, 3, v_l_1350_);
lean_ctor_set(v_reuseFailAlloc_2004_, 4, v_l_1350_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
}
}
}
}
else
{
return v_t_1347_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg___boxed(lean_object* v_k_2007_, lean_object* v_t_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_2007_, v_t_2008_);
lean_dec(v_k_2007_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3(lean_object* v_xs_2010_, lean_object* v_v_2011_, lean_object* v_i_2012_){
_start:
{
lean_object* v___x_2013_; uint8_t v___x_2014_; 
v___x_2013_ = lean_array_get_size(v_xs_2010_);
v___x_2014_ = lean_nat_dec_lt(v_i_2012_, v___x_2013_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; 
lean_dec(v_i_2012_);
v___x_2015_ = lean_box(0);
return v___x_2015_;
}
else
{
lean_object* v___x_2016_; uint8_t v___x_2017_; 
v___x_2016_ = lean_array_fget_borrowed(v_xs_2010_, v_i_2012_);
v___x_2017_ = l_Lean_instBEqFVarId_beq(v___x_2016_, v_v_2011_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2018_ = lean_unsigned_to_nat(1u);
v___x_2019_ = lean_nat_add(v_i_2012_, v___x_2018_);
lean_dec(v_i_2012_);
v_i_2012_ = v___x_2019_;
goto _start;
}
else
{
lean_object* v___x_2021_; 
v___x_2021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2021_, 0, v_i_2012_);
return v___x_2021_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_xs_2022_, lean_object* v_v_2023_, lean_object* v_i_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3(v_xs_2022_, v_v_2023_, v_i_2024_);
lean_dec(v_v_2023_);
lean_dec_ref(v_xs_2022_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1(lean_object* v_xs_2026_, lean_object* v_v_2027_){
_start:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2028_ = lean_unsigned_to_nat(0u);
v___x_2029_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3(v_xs_2026_, v_v_2027_, v___x_2028_);
return v___x_2029_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_2030_, lean_object* v_v_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1(v_xs_2030_, v_v_2031_);
lean_dec(v_v_2031_);
lean_dec_ref(v_xs_2030_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(lean_object* v_x_2033_, size_t v_x_2034_, lean_object* v_x_2035_){
_start:
{
if (lean_obj_tag(v_x_2033_) == 0)
{
lean_object* v_es_2036_; lean_object* v___x_2037_; size_t v___x_2038_; size_t v___x_2039_; lean_object* v_j_2040_; lean_object* v_entry_2041_; 
v_es_2036_ = lean_ctor_get(v_x_2033_, 0);
v___x_2037_ = lean_box(2);
v___x_2038_ = ((size_t)31ULL);
v___x_2039_ = lean_usize_land(v_x_2034_, v___x_2038_);
v_j_2040_ = lean_usize_to_nat(v___x_2039_);
v_entry_2041_ = lean_array_get(v___x_2037_, v_es_2036_, v_j_2040_);
switch(lean_obj_tag(v_entry_2041_))
{
case 0:
{
lean_object* v_key_2042_; uint8_t v___x_2043_; 
v_key_2042_ = lean_ctor_get(v_entry_2041_, 0);
lean_inc(v_key_2042_);
lean_dec_ref_known(v_entry_2041_, 2);
v___x_2043_ = l_Lean_instBEqFVarId_beq(v_x_2035_, v_key_2042_);
lean_dec(v_key_2042_);
if (v___x_2043_ == 0)
{
lean_dec(v_j_2040_);
return v_x_2033_;
}
else
{
lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2051_; 
lean_inc_ref(v_es_2036_);
v_isSharedCheck_2051_ = !lean_is_exclusive(v_x_2033_);
if (v_isSharedCheck_2051_ == 0)
{
lean_object* v_unused_2052_; 
v_unused_2052_ = lean_ctor_get(v_x_2033_, 0);
lean_dec(v_unused_2052_);
v___x_2045_ = v_x_2033_;
v_isShared_2046_ = v_isSharedCheck_2051_;
goto v_resetjp_2044_;
}
else
{
lean_dec(v_x_2033_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2051_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2047_; lean_object* v___x_2049_; 
v___x_2047_ = lean_array_set(v_es_2036_, v_j_2040_, v___x_2037_);
lean_dec(v_j_2040_);
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 0, v___x_2047_);
v___x_2049_ = v___x_2045_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2047_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
}
case 1:
{
lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2087_; 
lean_inc_ref(v_es_2036_);
v_isSharedCheck_2087_ = !lean_is_exclusive(v_x_2033_);
if (v_isSharedCheck_2087_ == 0)
{
lean_object* v_unused_2088_; 
v_unused_2088_ = lean_ctor_get(v_x_2033_, 0);
lean_dec(v_unused_2088_);
v___x_2054_ = v_x_2033_;
v_isShared_2055_ = v_isSharedCheck_2087_;
goto v_resetjp_2053_;
}
else
{
lean_dec(v_x_2033_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2087_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v_node_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2086_; 
v_node_2056_ = lean_ctor_get(v_entry_2041_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v_entry_2041_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2058_ = v_entry_2041_;
v_isShared_2059_ = v_isSharedCheck_2086_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_node_2056_);
lean_dec(v_entry_2041_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2086_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
size_t v___x_2060_; lean_object* v_entries_2061_; size_t v___x_2062_; lean_object* v_newNode_2063_; lean_object* v___x_2064_; 
v___x_2060_ = ((size_t)5ULL);
v_entries_2061_ = lean_array_set(v_es_2036_, v_j_2040_, v___x_2037_);
v___x_2062_ = lean_usize_shift_right(v_x_2034_, v___x_2060_);
v_newNode_2063_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_node_2056_, v___x_2062_, v_x_2035_);
lean_inc_ref(v_newNode_2063_);
v___x_2064_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_2063_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v___x_2066_; 
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 0, v_newNode_2063_);
v___x_2066_ = v___x_2058_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_newNode_2063_);
v___x_2066_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
lean_object* v___x_2067_; lean_object* v___x_2069_; 
v___x_2067_ = lean_array_set(v_entries_2061_, v_j_2040_, v___x_2066_);
lean_dec(v_j_2040_);
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 0, v___x_2067_);
v___x_2069_ = v___x_2054_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v___x_2067_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
else
{
lean_object* v_val_2072_; lean_object* v_fst_2073_; lean_object* v_snd_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2085_; 
lean_dec_ref(v_newNode_2063_);
lean_del_object(v___x_2058_);
v_val_2072_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_val_2072_);
lean_dec_ref_known(v___x_2064_, 1);
v_fst_2073_ = lean_ctor_get(v_val_2072_, 0);
v_snd_2074_ = lean_ctor_get(v_val_2072_, 1);
v_isSharedCheck_2085_ = !lean_is_exclusive(v_val_2072_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2076_ = v_val_2072_;
v_isShared_2077_ = v_isSharedCheck_2085_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_snd_2074_);
lean_inc(v_fst_2073_);
lean_dec(v_val_2072_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2085_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_fst_2073_);
lean_ctor_set(v_reuseFailAlloc_2084_, 1, v_snd_2074_);
v___x_2079_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
lean_object* v___x_2080_; lean_object* v___x_2082_; 
v___x_2080_ = lean_array_set(v_entries_2061_, v_j_2040_, v___x_2079_);
lean_dec(v_j_2040_);
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 0, v___x_2080_);
v___x_2082_ = v___x_2054_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2080_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_2040_);
return v_x_2033_;
}
}
}
else
{
lean_object* v_ks_2089_; lean_object* v_vs_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2104_; 
v_ks_2089_ = lean_ctor_get(v_x_2033_, 0);
v_vs_2090_ = lean_ctor_get(v_x_2033_, 1);
v_isSharedCheck_2104_ = !lean_is_exclusive(v_x_2033_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2092_ = v_x_2033_;
v_isShared_2093_ = v_isSharedCheck_2104_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_vs_2090_);
lean_inc(v_ks_2089_);
lean_dec(v_x_2033_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2104_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2094_; 
v___x_2094_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1(v_ks_2089_, v_x_2035_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v___x_2096_; 
if (v_isShared_2093_ == 0)
{
v___x_2096_ = v___x_2092_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_ks_2089_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v_vs_2090_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
else
{
lean_object* v_val_2098_; lean_object* v_keys_x27_2099_; lean_object* v_vals_x27_2100_; lean_object* v___x_2102_; 
v_val_2098_ = lean_ctor_get(v___x_2094_, 0);
lean_inc_n(v_val_2098_, 2);
lean_dec_ref_known(v___x_2094_, 1);
v_keys_x27_2099_ = l_Array_eraseIdx___redArg(v_ks_2089_, v_val_2098_);
v_vals_x27_2100_ = l_Array_eraseIdx___redArg(v_vs_2090_, v_val_2098_);
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 1, v_vals_x27_2100_);
lean_ctor_set(v___x_2092_, 0, v_keys_x27_2099_);
v___x_2102_ = v___x_2092_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_keys_x27_2099_);
lean_ctor_set(v_reuseFailAlloc_2103_, 1, v_vals_x27_2100_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg___boxed(lean_object* v_x_2105_, lean_object* v_x_2106_, lean_object* v_x_2107_){
_start:
{
size_t v_x_2640__boxed_2108_; lean_object* v_res_2109_; 
v_x_2640__boxed_2108_ = lean_unbox_usize(v_x_2106_);
lean_dec(v_x_2106_);
v_res_2109_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_x_2105_, v_x_2640__boxed_2108_, v_x_2107_);
lean_dec(v_x_2107_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(lean_object* v_x_2110_, lean_object* v_x_2111_){
_start:
{
uint64_t v___x_2112_; size_t v_h_2113_; lean_object* v___x_2114_; 
v___x_2112_ = l_Lean_instHashableFVarId_hash(v_x_2111_);
v_h_2113_ = lean_uint64_to_usize(v___x_2112_);
v___x_2114_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_x_2110_, v_h_2113_, v_x_2111_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg___boxed(lean_object* v_x_2115_, lean_object* v_x_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_x_2115_, v_x_2116_);
lean_dec(v_x_2116_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_erase(lean_object* v_lctx_2118_, lean_object* v_fvarId_2119_){
_start:
{
lean_object* v_fvarIdToDecl_2120_; lean_object* v_decls_2121_; lean_object* v_auxDeclToFullName_2122_; lean_object* v___x_2123_; 
v_fvarIdToDecl_2120_ = lean_ctor_get(v_lctx_2118_, 0);
v_decls_2121_ = lean_ctor_get(v_lctx_2118_, 1);
v_auxDeclToFullName_2122_ = lean_ctor_get(v_lctx_2118_, 2);
v___x_2123_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_fvarIdToDecl_2120_, v_fvarId_2119_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_dec(v_fvarId_2119_);
return v_lctx_2118_;
}
else
{
lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2143_; 
lean_inc(v_auxDeclToFullName_2122_);
lean_inc_ref(v_decls_2121_);
lean_inc_ref(v_fvarIdToDecl_2120_);
v_isSharedCheck_2143_ = !lean_is_exclusive(v_lctx_2118_);
if (v_isSharedCheck_2143_ == 0)
{
lean_object* v_unused_2144_; lean_object* v_unused_2145_; lean_object* v_unused_2146_; 
v_unused_2144_ = lean_ctor_get(v_lctx_2118_, 2);
lean_dec(v_unused_2144_);
v_unused_2145_ = lean_ctor_get(v_lctx_2118_, 1);
lean_dec(v_unused_2145_);
v_unused_2146_ = lean_ctor_get(v_lctx_2118_, 0);
lean_dec(v_unused_2146_);
v___x_2125_ = v_lctx_2118_;
v_isShared_2126_ = v_isSharedCheck_2143_;
goto v_resetjp_2124_;
}
else
{
lean_dec(v_lctx_2118_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2143_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v_val_2127_; lean_object* v___x_2128_; lean_object* v___y_2130_; lean_object* v_index_2142_; 
v_val_2127_ = lean_ctor_get(v___x_2123_, 0);
lean_inc(v_val_2127_);
lean_dec_ref_known(v___x_2123_, 1);
v___x_2128_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_fvarIdToDecl_2120_, v_fvarId_2119_);
v_index_2142_ = lean_ctor_get(v_val_2127_, 0);
lean_inc(v_index_2142_);
v___y_2130_ = v_index_2142_;
goto v___jp_2129_;
v___jp_2129_:
{
lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; uint8_t v___x_2134_; 
v___x_2131_ = lean_box(0);
v___x_2132_ = l_Lean_PersistentArray_set___redArg(v_decls_2121_, v___y_2130_, v___x_2131_);
lean_dec(v___y_2130_);
v___x_2133_ = l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(v___x_2132_);
v___x_2134_ = l_Lean_LocalDecl_isAuxDecl(v_val_2127_);
lean_dec(v_val_2127_);
if (v___x_2134_ == 0)
{
lean_object* v___x_2136_; 
lean_dec(v_fvarId_2119_);
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 1, v___x_2133_);
lean_ctor_set(v___x_2125_, 0, v___x_2128_);
v___x_2136_ = v___x_2125_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2128_);
lean_ctor_set(v_reuseFailAlloc_2137_, 1, v___x_2133_);
lean_ctor_set(v_reuseFailAlloc_2137_, 2, v_auxDeclToFullName_2122_);
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
lean_object* v___x_2138_; lean_object* v___x_2140_; 
v___x_2138_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_fvarId_2119_, v_auxDeclToFullName_2122_);
lean_dec(v_fvarId_2119_);
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 2, v___x_2138_);
lean_ctor_set(v___x_2125_, 1, v___x_2133_);
lean_ctor_set(v___x_2125_, 0, v___x_2128_);
v___x_2140_ = v___x_2125_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2128_);
lean_ctor_set(v_reuseFailAlloc_2141_, 1, v___x_2133_);
lean_ctor_set(v_reuseFailAlloc_2141_, 2, v___x_2138_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0(lean_object* v_00_u03b2_2147_, lean_object* v_x_2148_, lean_object* v_x_2149_){
_start:
{
lean_object* v___x_2150_; 
v___x_2150_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_x_2148_, v_x_2149_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___boxed(lean_object* v_00_u03b2_2151_, lean_object* v_x_2152_, lean_object* v_x_2153_){
_start:
{
lean_object* v_res_2154_; 
v_res_2154_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0(v_00_u03b2_2151_, v_x_2152_, v_x_2153_);
lean_dec(v_x_2153_);
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1(lean_object* v_00_u03b2_2155_, lean_object* v_k_2156_, lean_object* v_t_2157_, lean_object* v_h_2158_){
_start:
{
lean_object* v___x_2159_; 
v___x_2159_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_2156_, v_t_2157_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___boxed(lean_object* v_00_u03b2_2160_, lean_object* v_k_2161_, lean_object* v_t_2162_, lean_object* v_h_2163_){
_start:
{
lean_object* v_res_2164_; 
v_res_2164_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1(v_00_u03b2_2160_, v_k_2161_, v_t_2162_, v_h_2163_);
lean_dec(v_k_2161_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0(lean_object* v_00_u03b2_2165_, lean_object* v_x_2166_, size_t v_x_2167_, lean_object* v_x_2168_){
_start:
{
lean_object* v___x_2169_; 
v___x_2169_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_x_2166_, v_x_2167_, v_x_2168_);
return v___x_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2170_, lean_object* v_x_2171_, lean_object* v_x_2172_, lean_object* v_x_2173_){
_start:
{
size_t v_x_2862__boxed_2174_; lean_object* v_res_2175_; 
v_x_2862__boxed_2174_ = lean_unbox_usize(v_x_2172_);
lean_dec(v_x_2172_);
v_res_2175_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0(v_00_u03b2_2170_, v_x_2171_, v_x_2862__boxed_2174_, v_x_2173_);
lean_dec(v_x_2173_);
return v_res_2175_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_pop(lean_object* v_lctx_2176_){
_start:
{
lean_object* v_decls_2177_; lean_object* v_fvarIdToDecl_2178_; lean_object* v_auxDeclToFullName_2179_; lean_object* v_size_2180_; lean_object* v___x_2181_; uint8_t v___x_2182_; 
v_decls_2177_ = lean_ctor_get(v_lctx_2176_, 1);
v_fvarIdToDecl_2178_ = lean_ctor_get(v_lctx_2176_, 0);
v_auxDeclToFullName_2179_ = lean_ctor_get(v_lctx_2176_, 2);
v_size_2180_ = lean_ctor_get(v_decls_2177_, 2);
v___x_2181_ = lean_unsigned_to_nat(0u);
v___x_2182_ = lean_nat_dec_eq(v_size_2180_, v___x_2181_);
if (v___x_2182_ == 0)
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2183_ = lean_box(0);
v___x_2184_ = lean_unsigned_to_nat(1u);
v___x_2185_ = lean_nat_sub(v_size_2180_, v___x_2184_);
v___x_2186_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2183_, v_decls_2177_, v___x_2185_);
lean_dec(v___x_2185_);
if (lean_obj_tag(v___x_2186_) == 0)
{
return v_lctx_2176_;
}
else
{
lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2205_; 
lean_inc(v_auxDeclToFullName_2179_);
lean_inc_ref(v_fvarIdToDecl_2178_);
lean_inc_ref(v_decls_2177_);
v_isSharedCheck_2205_ = !lean_is_exclusive(v_lctx_2176_);
if (v_isSharedCheck_2205_ == 0)
{
lean_object* v_unused_2206_; lean_object* v_unused_2207_; lean_object* v_unused_2208_; 
v_unused_2206_ = lean_ctor_get(v_lctx_2176_, 2);
lean_dec(v_unused_2206_);
v_unused_2207_ = lean_ctor_get(v_lctx_2176_, 1);
lean_dec(v_unused_2207_);
v_unused_2208_ = lean_ctor_get(v_lctx_2176_, 0);
lean_dec(v_unused_2208_);
v___x_2188_ = v_lctx_2176_;
v_isShared_2189_ = v_isSharedCheck_2205_;
goto v_resetjp_2187_;
}
else
{
lean_dec(v_lctx_2176_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2205_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v_val_2190_; lean_object* v___y_2192_; lean_object* v_fvarId_2204_; 
v_val_2190_ = lean_ctor_get(v___x_2186_, 0);
lean_inc(v_val_2190_);
lean_dec_ref_known(v___x_2186_, 1);
v_fvarId_2204_ = lean_ctor_get(v_val_2190_, 1);
lean_inc(v_fvarId_2204_);
v___y_2192_ = v_fvarId_2204_;
goto v___jp_2191_;
v___jp_2191_:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; uint8_t v___x_2196_; 
v___x_2193_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_fvarIdToDecl_2178_, v___y_2192_);
v___x_2194_ = l_Lean_PersistentArray_pop___redArg(v_decls_2177_);
v___x_2195_ = l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(v___x_2194_);
v___x_2196_ = l_Lean_LocalDecl_isAuxDecl(v_val_2190_);
lean_dec(v_val_2190_);
if (v___x_2196_ == 0)
{
lean_object* v___x_2198_; 
lean_dec(v___y_2192_);
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 1, v___x_2195_);
lean_ctor_set(v___x_2188_, 0, v___x_2193_);
v___x_2198_ = v___x_2188_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v___x_2193_);
lean_ctor_set(v_reuseFailAlloc_2199_, 1, v___x_2195_);
lean_ctor_set(v_reuseFailAlloc_2199_, 2, v_auxDeclToFullName_2179_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
else
{
lean_object* v___x_2200_; lean_object* v___x_2202_; 
v___x_2200_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v___y_2192_, v_auxDeclToFullName_2179_);
lean_dec(v___y_2192_);
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 2, v___x_2200_);
lean_ctor_set(v___x_2188_, 1, v___x_2195_);
lean_ctor_set(v___x_2188_, 0, v___x_2193_);
v___x_2202_ = v___x_2188_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v___x_2193_);
lean_ctor_set(v_reuseFailAlloc_2203_, 1, v___x_2195_);
lean_ctor_set(v_reuseFailAlloc_2203_, 2, v___x_2200_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
}
}
}
else
{
return v_lctx_2176_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(lean_object* v_userName_2209_, lean_object* v_as_2210_, lean_object* v_i_2211_){
_start:
{
lean_object* v_zero_2212_; uint8_t v_isZero_2213_; 
v_zero_2212_ = lean_unsigned_to_nat(0u);
v_isZero_2213_ = lean_nat_dec_eq(v_i_2211_, v_zero_2212_);
if (v_isZero_2213_ == 1)
{
lean_object* v___x_2214_; 
lean_dec(v_i_2211_);
v___x_2214_ = lean_box(0);
return v___x_2214_;
}
else
{
lean_object* v_one_2215_; lean_object* v_n_2216_; lean_object* v___y_2218_; lean_object* v___x_2220_; lean_object* v___y_2222_; 
v_one_2215_ = lean_unsigned_to_nat(1u);
v_n_2216_ = lean_nat_sub(v_i_2211_, v_one_2215_);
lean_dec(v_i_2211_);
v___x_2220_ = lean_array_fget_borrowed(v_as_2210_, v_n_2216_);
if (lean_obj_tag(v___x_2220_) == 0)
{
v___y_2218_ = v___x_2220_;
goto v___jp_2217_;
}
else
{
lean_object* v_val_2225_; lean_object* v_userName_2226_; 
v_val_2225_ = lean_ctor_get(v___x_2220_, 0);
v_userName_2226_ = lean_ctor_get(v_val_2225_, 2);
v___y_2222_ = v_userName_2226_;
goto v___jp_2221_;
}
v___jp_2217_:
{
if (lean_obj_tag(v___y_2218_) == 0)
{
v_i_2211_ = v_n_2216_;
goto _start;
}
else
{
lean_dec(v_n_2216_);
lean_inc_ref(v___y_2218_);
return v___y_2218_;
}
}
v___jp_2221_:
{
uint8_t v___x_2223_; 
v___x_2223_ = lean_name_eq(v___y_2222_, v_userName_2209_);
if (v___x_2223_ == 0)
{
v_i_2211_ = v_n_2216_;
goto _start;
}
else
{
v___y_2218_ = v___x_2220_;
goto v___jp_2217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_userName_2227_, lean_object* v_as_2228_, lean_object* v_i_2229_){
_start:
{
lean_object* v_res_2230_; 
v_res_2230_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2227_, v_as_2228_, v_i_2229_);
lean_dec_ref(v_as_2228_);
lean_dec(v_userName_2227_);
return v_res_2230_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(lean_object* v_userName_2231_, lean_object* v_as_2232_, lean_object* v_i_2233_){
_start:
{
lean_object* v_zero_2234_; uint8_t v_isZero_2235_; 
v_zero_2234_ = lean_unsigned_to_nat(0u);
v_isZero_2235_ = lean_nat_dec_eq(v_i_2233_, v_zero_2234_);
if (v_isZero_2235_ == 1)
{
lean_object* v___x_2236_; 
lean_dec(v_i_2233_);
v___x_2236_ = lean_box(0);
return v___x_2236_;
}
else
{
lean_object* v_one_2237_; lean_object* v_n_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v_one_2237_ = lean_unsigned_to_nat(1u);
v_n_2238_ = lean_nat_sub(v_i_2233_, v_one_2237_);
lean_dec(v_i_2233_);
v___x_2239_ = lean_array_fget_borrowed(v_as_2232_, v_n_2238_);
v___x_2240_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(v_userName_2231_, v___x_2239_);
if (lean_obj_tag(v___x_2240_) == 0)
{
v_i_2233_ = v_n_2238_;
goto _start;
}
else
{
lean_dec(v_n_2238_);
return v___x_2240_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(lean_object* v_userName_2242_, lean_object* v_x_2243_){
_start:
{
if (lean_obj_tag(v_x_2243_) == 0)
{
lean_object* v_cs_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v_cs_2244_ = lean_ctor_get(v_x_2243_, 0);
v___x_2245_ = lean_array_get_size(v_cs_2244_);
v___x_2246_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(v_userName_2242_, v_cs_2244_, v___x_2245_);
return v___x_2246_;
}
else
{
lean_object* v_vs_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v_vs_2247_ = lean_ctor_get(v_x_2243_, 0);
v___x_2248_ = lean_array_get_size(v_vs_2247_);
v___x_2249_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2242_, v_vs_2247_, v___x_2248_);
return v___x_2249_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1___boxed(lean_object* v_userName_2250_, lean_object* v_x_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(v_userName_2250_, v_x_2251_);
lean_dec_ref(v_x_2251_);
lean_dec(v_userName_2250_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_userName_2253_, lean_object* v_as_2254_, lean_object* v_i_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(v_userName_2253_, v_as_2254_, v_i_2255_);
lean_dec_ref(v_as_2254_);
lean_dec(v_userName_2253_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0(lean_object* v_userName_2257_, lean_object* v_t_2258_){
_start:
{
lean_object* v_root_2259_; lean_object* v_tail_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
v_root_2259_ = lean_ctor_get(v_t_2258_, 0);
v_tail_2260_ = lean_ctor_get(v_t_2258_, 1);
v___x_2261_ = lean_array_get_size(v_tail_2260_);
v___x_2262_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2257_, v_tail_2260_, v___x_2261_);
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_object* v___x_2263_; 
v___x_2263_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(v_userName_2257_, v_root_2259_);
return v___x_2263_;
}
else
{
return v___x_2262_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0___boxed(lean_object* v_userName_2264_, lean_object* v_t_2265_){
_start:
{
lean_object* v_res_2266_; 
v_res_2266_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0(v_userName_2264_, v_t_2265_);
lean_dec_ref(v_t_2265_);
lean_dec(v_userName_2264_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object* v_lctx_2267_, lean_object* v_userName_2268_){
_start:
{
lean_object* v_decls_2269_; lean_object* v___x_2270_; 
v_decls_2269_ = lean_ctor_get(v_lctx_2267_, 1);
v___x_2270_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0(v_userName_2268_, v_decls_2269_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserName_x3f___boxed(lean_object* v_lctx_2271_, lean_object* v_userName_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2271_, v_userName_2272_);
lean_dec(v_userName_2272_);
lean_dec_ref(v_lctx_2271_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0(lean_object* v_userName_2274_, lean_object* v_as_2275_, lean_object* v_i_2276_, lean_object* v_a_2277_){
_start:
{
lean_object* v___x_2278_; 
v___x_2278_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2274_, v_as_2275_, v_i_2276_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___boxed(lean_object* v_userName_2279_, lean_object* v_as_2280_, lean_object* v_i_2281_, lean_object* v_a_2282_){
_start:
{
lean_object* v_res_2283_; 
v_res_2283_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0(v_userName_2279_, v_as_2280_, v_i_2281_, v_a_2282_);
lean_dec_ref(v_as_2280_);
lean_dec(v_userName_2279_);
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2(lean_object* v_userName_2284_, lean_object* v_as_2285_, lean_object* v_i_2286_, lean_object* v_a_2287_){
_start:
{
lean_object* v___x_2288_; 
v___x_2288_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(v_userName_2284_, v_as_2285_, v_i_2286_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___boxed(lean_object* v_userName_2289_, lean_object* v_as_2290_, lean_object* v_i_2291_, lean_object* v_a_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2(v_userName_2289_, v_as_2290_, v_i_2291_, v_a_2292_);
lean_dec_ref(v_as_2290_);
lean_dec(v_userName_2289_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFromUserName_x21(lean_object* v_lctx_2297_, lean_object* v_userName_2298_){
_start:
{
lean_object* v___x_2299_; 
v___x_2299_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2297_, v_userName_2298_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; uint8_t v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2300_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_2301_ = ((lean_object*)(l_Lean_LocalContext_getFromUserName_x21___closed__0));
v___x_2302_ = lean_unsigned_to_nat(403u);
v___x_2303_ = lean_unsigned_to_nat(17u);
v___x_2304_ = ((lean_object*)(l_Lean_LocalContext_getFromUserName_x21___closed__1));
v___x_2305_ = 1;
v___x_2306_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_userName_2298_, v___x_2305_);
v___x_2307_ = lean_string_append(v___x_2304_, v___x_2306_);
lean_dec_ref(v___x_2306_);
v___x_2308_ = ((lean_object*)(l_Lean_LocalContext_getFromUserName_x21___closed__2));
v___x_2309_ = lean_string_append(v___x_2307_, v___x_2308_);
v___x_2310_ = l_mkPanicMessageWithDecl(v___x_2300_, v___x_2301_, v___x_2302_, v___x_2303_, v___x_2309_);
lean_dec_ref(v___x_2309_);
v___x_2311_ = l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(v___x_2310_);
return v___x_2311_;
}
else
{
lean_object* v_val_2312_; 
lean_dec(v_userName_2298_);
v_val_2312_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_val_2312_);
lean_dec_ref_known(v___x_2299_, 1);
return v_val_2312_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFromUserName_x21___boxed(lean_object* v_lctx_2313_, lean_object* v_userName_2314_){
_start:
{
lean_object* v_res_2315_; 
v_res_2315_ = l_Lean_LocalContext_getFromUserName_x21(v_lctx_2313_, v_userName_2314_);
lean_dec_ref(v_lctx_2313_);
return v_res_2315_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_usesUserName(lean_object* v_lctx_2316_, lean_object* v_userName_2317_){
_start:
{
lean_object* v___x_2318_; 
v___x_2318_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2316_, v_userName_2317_);
if (lean_obj_tag(v___x_2318_) == 0)
{
uint8_t v___x_2319_; 
v___x_2319_ = 0;
return v___x_2319_;
}
else
{
uint8_t v___x_2320_; 
lean_dec_ref_known(v___x_2318_, 1);
v___x_2320_ = 1;
return v___x_2320_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_usesUserName___boxed(lean_object* v_lctx_2321_, lean_object* v_userName_2322_){
_start:
{
uint8_t v_res_2323_; lean_object* v_r_2324_; 
v_res_2323_ = l_Lean_LocalContext_usesUserName(v_lctx_2321_, v_userName_2322_);
lean_dec(v_userName_2322_);
lean_dec_ref(v_lctx_2321_);
v_r_2324_ = lean_box(v_res_2323_);
return v_r_2324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(lean_object* v_lctx_2325_, lean_object* v_suggestion_2326_, lean_object* v_i_2327_){
_start:
{
lean_object* v_curr_2328_; uint8_t v___x_2329_; 
lean_inc(v_i_2327_);
lean_inc(v_suggestion_2326_);
v_curr_2328_ = lean_name_append_index_after(v_suggestion_2326_, v_i_2327_);
v___x_2329_ = l_Lean_LocalContext_usesUserName(v_lctx_2325_, v_curr_2328_);
if (v___x_2329_ == 0)
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
lean_dec(v_suggestion_2326_);
v___x_2330_ = lean_unsigned_to_nat(1u);
v___x_2331_ = lean_nat_add(v_i_2327_, v___x_2330_);
lean_dec(v_i_2327_);
v___x_2332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2332_, 0, v_curr_2328_);
lean_ctor_set(v___x_2332_, 1, v___x_2331_);
return v___x_2332_;
}
else
{
lean_object* v___x_2333_; lean_object* v___x_2334_; 
lean_dec(v_curr_2328_);
v___x_2333_ = lean_unsigned_to_nat(1u);
v___x_2334_ = lean_nat_add(v_i_2327_, v___x_2333_);
lean_dec(v_i_2327_);
v_i_2327_ = v___x_2334_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux___boxed(lean_object* v_lctx_2336_, lean_object* v_suggestion_2337_, lean_object* v_i_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(v_lctx_2336_, v_suggestion_2337_, v_i_2338_);
lean_dec_ref(v_lctx_2336_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getUnusedName(lean_object* v_lctx_2340_, lean_object* v_suggestion_2341_){
_start:
{
lean_object* v_suggestion_2342_; uint8_t v___x_2343_; 
v_suggestion_2342_ = l_Lean_Name_eraseMacroScopes(v_suggestion_2341_);
v___x_2343_ = l_Lean_LocalContext_usesUserName(v_lctx_2340_, v_suggestion_2342_);
if (v___x_2343_ == 0)
{
return v_suggestion_2342_;
}
else
{
lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v_fst_2346_; 
v___x_2344_ = lean_unsigned_to_nat(1u);
v___x_2345_ = l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(v_lctx_2340_, v_suggestion_2342_, v___x_2344_);
v_fst_2346_ = lean_ctor_get(v___x_2345_, 0);
lean_inc(v_fst_2346_);
lean_dec_ref(v___x_2345_);
return v_fst_2346_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getUnusedName___boxed(lean_object* v_lctx_2347_, lean_object* v_suggestion_2348_){
_start:
{
lean_object* v_res_2349_; 
v_res_2349_ = l_Lean_LocalContext_getUnusedName(v_lctx_2347_, v_suggestion_2348_);
lean_dec(v_suggestion_2348_);
lean_dec_ref(v_lctx_2347_);
return v_res_2349_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_lastDecl(lean_object* v_lctx_2350_){
_start:
{
lean_object* v_decls_2351_; lean_object* v_size_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; uint8_t v___x_2356_; 
v_decls_2351_ = lean_ctor_get(v_lctx_2350_, 1);
v_size_2352_ = lean_ctor_get(v_decls_2351_, 2);
v___x_2353_ = lean_box(0);
v___x_2354_ = lean_unsigned_to_nat(1u);
v___x_2355_ = lean_nat_sub(v_size_2352_, v___x_2354_);
v___x_2356_ = lean_nat_dec_lt(v___x_2355_, v_size_2352_);
if (v___x_2356_ == 0)
{
lean_object* v___x_2357_; 
lean_dec(v___x_2355_);
v___x_2357_ = l_outOfBounds___redArg(v___x_2353_);
return v___x_2357_;
}
else
{
lean_object* v___x_2358_; 
v___x_2358_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2353_, v_decls_2351_, v___x_2355_);
lean_dec(v___x_2355_);
return v___x_2358_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_lastDecl___boxed(lean_object* v_lctx_2359_){
_start:
{
lean_object* v_res_2360_; 
v_res_2360_ = l_Lean_LocalContext_lastDecl(v_lctx_2359_);
lean_dec_ref(v_lctx_2359_);
return v_res_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setUserName(lean_object* v_lctx_2361_, lean_object* v_fvarId_2362_, lean_object* v_userName_2363_){
_start:
{
lean_object* v_fvarIdToDecl_2364_; lean_object* v_decls_2365_; lean_object* v_auxDeclToFullName_2366_; lean_object* v_decl_2367_; lean_object* v_decl_2368_; lean_object* v___y_2370_; lean_object* v___y_2371_; lean_object* v___y_2376_; lean_object* v_fvarId_2379_; 
v_fvarIdToDecl_2364_ = lean_ctor_get(v_lctx_2361_, 0);
lean_inc_ref(v_fvarIdToDecl_2364_);
v_decls_2365_ = lean_ctor_get(v_lctx_2361_, 1);
lean_inc_ref(v_decls_2365_);
v_auxDeclToFullName_2366_ = lean_ctor_get(v_lctx_2361_, 2);
lean_inc(v_auxDeclToFullName_2366_);
v_decl_2367_ = l_Lean_LocalContext_get_x21(v_lctx_2361_, v_fvarId_2362_);
v_decl_2368_ = l_Lean_LocalDecl_setUserName(v_decl_2367_, v_userName_2363_);
v_fvarId_2379_ = lean_ctor_get(v_decl_2368_, 1);
lean_inc(v_fvarId_2379_);
v___y_2376_ = v_fvarId_2379_;
goto v___jp_2375_;
v___jp_2369_:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2372_, 0, v_decl_2368_);
v___x_2373_ = l_Lean_PersistentArray_set___redArg(v_decls_2365_, v___y_2371_, v___x_2372_);
lean_dec(v___y_2371_);
v___x_2374_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2374_, 0, v___y_2370_);
lean_ctor_set(v___x_2374_, 1, v___x_2373_);
lean_ctor_set(v___x_2374_, 2, v_auxDeclToFullName_2366_);
return v___x_2374_;
}
v___jp_2375_:
{
lean_object* v___x_2377_; lean_object* v_index_2378_; 
lean_inc_ref(v_decl_2368_);
v___x_2377_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2364_, v___y_2376_, v_decl_2368_);
v_index_2378_ = lean_ctor_get(v_decl_2368_, 0);
lean_inc(v_index_2378_);
v___y_2370_ = v___x_2377_;
v___y_2371_ = v_index_2378_;
goto v___jp_2369_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_renameUserName(lean_object* v_lctx_2380_, lean_object* v_fromName_2381_, lean_object* v_toName_2382_){
_start:
{
lean_object* v_fvarIdToDecl_2383_; lean_object* v_decls_2384_; lean_object* v_auxDeclToFullName_2385_; lean_object* v___x_2386_; 
v_fvarIdToDecl_2383_ = lean_ctor_get(v_lctx_2380_, 0);
v_decls_2384_ = lean_ctor_get(v_lctx_2380_, 1);
v_auxDeclToFullName_2385_ = lean_ctor_get(v_lctx_2380_, 2);
v___x_2386_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2380_, v_fromName_2381_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_dec(v_toName_2382_);
return v_lctx_2380_;
}
else
{
lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2411_; 
lean_inc(v_auxDeclToFullName_2385_);
lean_inc_ref(v_decls_2384_);
lean_inc_ref(v_fvarIdToDecl_2383_);
v_isSharedCheck_2411_ = !lean_is_exclusive(v_lctx_2380_);
if (v_isSharedCheck_2411_ == 0)
{
lean_object* v_unused_2412_; lean_object* v_unused_2413_; lean_object* v_unused_2414_; 
v_unused_2412_ = lean_ctor_get(v_lctx_2380_, 2);
lean_dec(v_unused_2412_);
v_unused_2413_ = lean_ctor_get(v_lctx_2380_, 1);
lean_dec(v_unused_2413_);
v_unused_2414_ = lean_ctor_get(v_lctx_2380_, 0);
lean_dec(v_unused_2414_);
v___x_2388_ = v_lctx_2380_;
v_isShared_2389_ = v_isSharedCheck_2411_;
goto v_resetjp_2387_;
}
else
{
lean_dec(v_lctx_2380_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2411_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v_val_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2410_; 
v_val_2390_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2410_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2410_ == 0)
{
v___x_2392_ = v___x_2386_;
v_isShared_2393_ = v_isSharedCheck_2410_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_val_2390_);
lean_dec(v___x_2386_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2410_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v_decl_2394_; lean_object* v___y_2396_; lean_object* v___y_2397_; lean_object* v___y_2406_; lean_object* v_fvarId_2409_; 
v_decl_2394_ = l_Lean_LocalDecl_setUserName(v_val_2390_, v_toName_2382_);
v_fvarId_2409_ = lean_ctor_get(v_decl_2394_, 1);
lean_inc(v_fvarId_2409_);
v___y_2406_ = v_fvarId_2409_;
goto v___jp_2405_;
v___jp_2395_:
{
lean_object* v___x_2399_; 
if (v_isShared_2393_ == 0)
{
lean_ctor_set(v___x_2392_, 0, v_decl_2394_);
v___x_2399_ = v___x_2392_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_decl_2394_);
v___x_2399_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
lean_object* v___x_2400_; lean_object* v___x_2402_; 
v___x_2400_ = l_Lean_PersistentArray_set___redArg(v_decls_2384_, v___y_2397_, v___x_2399_);
lean_dec(v___y_2397_);
if (v_isShared_2389_ == 0)
{
lean_ctor_set(v___x_2388_, 1, v___x_2400_);
lean_ctor_set(v___x_2388_, 0, v___y_2396_);
v___x_2402_ = v___x_2388_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v___y_2396_);
lean_ctor_set(v_reuseFailAlloc_2403_, 1, v___x_2400_);
lean_ctor_set(v_reuseFailAlloc_2403_, 2, v_auxDeclToFullName_2385_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
v___jp_2405_:
{
lean_object* v___x_2407_; lean_object* v_index_2408_; 
lean_inc_ref(v_decl_2394_);
v___x_2407_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2383_, v___y_2406_, v_decl_2394_);
v_index_2408_ = lean_ctor_get(v_decl_2394_, 0);
lean_inc(v_index_2408_);
v___y_2396_ = v___x_2407_;
v___y_2397_ = v_index_2408_;
goto v___jp_2395_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_renameUserName___boxed(lean_object* v_lctx_2415_, lean_object* v_fromName_2416_, lean_object* v_toName_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l_Lean_LocalContext_renameUserName(v_lctx_2415_, v_fromName_2416_, v_toName_2417_);
lean_dec(v_fromName_2416_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_modifyLocalDecl(lean_object* v_lctx_2421_, lean_object* v_fvarId_2422_, lean_object* v_f_2423_){
_start:
{
lean_object* v_fvarIdToDecl_2424_; lean_object* v_decls_2425_; lean_object* v_auxDeclToFullName_2426_; lean_object* v___x_2427_; 
v_fvarIdToDecl_2424_ = lean_ctor_get(v_lctx_2421_, 0);
v_decls_2425_ = lean_ctor_get(v_lctx_2421_, 1);
v_auxDeclToFullName_2426_ = lean_ctor_get(v_lctx_2421_, 2);
lean_inc_ref(v_lctx_2421_);
v___x_2427_ = lean_local_ctx_find(v_lctx_2421_, v_fvarId_2422_);
if (lean_obj_tag(v___x_2427_) == 0)
{
lean_dec_ref(v_f_2423_);
return v_lctx_2421_;
}
else
{
lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2454_; 
lean_inc(v_auxDeclToFullName_2426_);
lean_inc_ref(v_decls_2425_);
lean_inc_ref(v_fvarIdToDecl_2424_);
v_isSharedCheck_2454_ = !lean_is_exclusive(v_lctx_2421_);
if (v_isSharedCheck_2454_ == 0)
{
lean_object* v_unused_2455_; lean_object* v_unused_2456_; lean_object* v_unused_2457_; 
v_unused_2455_ = lean_ctor_get(v_lctx_2421_, 2);
lean_dec(v_unused_2455_);
v_unused_2456_ = lean_ctor_get(v_lctx_2421_, 1);
lean_dec(v_unused_2456_);
v_unused_2457_ = lean_ctor_get(v_lctx_2421_, 0);
lean_dec(v_unused_2457_);
v___x_2429_ = v_lctx_2421_;
v_isShared_2430_ = v_isSharedCheck_2454_;
goto v_resetjp_2428_;
}
else
{
lean_dec(v_lctx_2421_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2454_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v_val_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2453_; 
v_val_2431_ = lean_ctor_get(v___x_2427_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2433_ = v___x_2427_;
v_isShared_2434_ = v_isSharedCheck_2453_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_val_2431_);
lean_dec(v___x_2427_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2453_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v_decl_2437_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2449_; lean_object* v_fvarId_2452_; 
v___x_2435_ = ((lean_object*)(l_Lean_LocalContext_modifyLocalDecl___closed__0));
v___x_2436_ = ((lean_object*)(l_Lean_LocalContext_modifyLocalDecl___closed__1));
v_decl_2437_ = lean_apply_1(v_f_2423_, v_val_2431_);
v_fvarId_2452_ = lean_ctor_get(v_decl_2437_, 1);
lean_inc(v_fvarId_2452_);
v___y_2449_ = v_fvarId_2452_;
goto v___jp_2448_;
v___jp_2438_:
{
lean_object* v___x_2442_; 
if (v_isShared_2434_ == 0)
{
lean_ctor_set(v___x_2433_, 0, v_decl_2437_);
v___x_2442_ = v___x_2433_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_decl_2437_);
v___x_2442_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
lean_object* v___x_2443_; lean_object* v___x_2445_; 
v___x_2443_ = l_Lean_PersistentArray_set___redArg(v_decls_2425_, v___y_2440_, v___x_2442_);
lean_dec(v___y_2440_);
if (v_isShared_2430_ == 0)
{
lean_ctor_set(v___x_2429_, 1, v___x_2443_);
lean_ctor_set(v___x_2429_, 0, v___y_2439_);
v___x_2445_ = v___x_2429_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v___y_2439_);
lean_ctor_set(v_reuseFailAlloc_2446_, 1, v___x_2443_);
lean_ctor_set(v_reuseFailAlloc_2446_, 2, v_auxDeclToFullName_2426_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
v___jp_2448_:
{
lean_object* v___x_2450_; lean_object* v_index_2451_; 
lean_inc_ref(v_decl_2437_);
v___x_2450_ = l_Lean_PersistentHashMap_insert___redArg(v___x_2435_, v___x_2436_, v_fvarIdToDecl_2424_, v___y_2449_, v_decl_2437_);
v_index_2451_ = lean_ctor_get(v_decl_2437_, 0);
lean_inc(v_index_2451_);
v___y_2439_ = v___x_2450_;
v___y_2440_ = v_index_2451_;
goto v___jp_2438_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(lean_object* v_f_2458_, lean_object* v_as_2459_, size_t v_i_2460_, size_t v_stop_2461_, lean_object* v_b_2462_){
_start:
{
lean_object* v___y_2464_; uint8_t v___x_2468_; 
v___x_2468_ = lean_usize_dec_eq(v_i_2460_, v_stop_2461_);
if (v___x_2468_ == 0)
{
lean_object* v___x_2469_; 
v___x_2469_ = lean_array_uget(v_as_2459_, v_i_2460_);
if (lean_obj_tag(v___x_2469_) == 0)
{
v___y_2464_ = v_b_2462_;
goto v___jp_2463_;
}
else
{
lean_object* v_val_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2497_; 
v_val_2470_ = lean_ctor_get(v___x_2469_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2472_ = v___x_2469_;
v_isShared_2473_ = v_isSharedCheck_2497_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_val_2470_);
lean_dec(v___x_2469_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2497_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v_fvarIdToDecl_2474_; lean_object* v_decls_2475_; lean_object* v_auxDeclToFullName_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2496_; 
v_fvarIdToDecl_2474_ = lean_ctor_get(v_b_2462_, 0);
v_decls_2475_ = lean_ctor_get(v_b_2462_, 1);
v_auxDeclToFullName_2476_ = lean_ctor_get(v_b_2462_, 2);
v_isSharedCheck_2496_ = !lean_is_exclusive(v_b_2462_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2478_ = v_b_2462_;
v_isShared_2479_ = v_isSharedCheck_2496_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_auxDeclToFullName_2476_);
lean_inc(v_decls_2475_);
lean_inc(v_fvarIdToDecl_2474_);
lean_dec(v_b_2462_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2496_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v_decl_2480_; lean_object* v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2492_; lean_object* v_fvarId_2495_; 
lean_inc_ref(v_f_2458_);
v_decl_2480_ = lean_apply_1(v_f_2458_, v_val_2470_);
v_fvarId_2495_ = lean_ctor_get(v_decl_2480_, 1);
lean_inc(v_fvarId_2495_);
v___y_2492_ = v_fvarId_2495_;
goto v___jp_2491_;
v___jp_2481_:
{
lean_object* v___x_2485_; 
if (v_isShared_2473_ == 0)
{
lean_ctor_set(v___x_2472_, 0, v_decl_2480_);
v___x_2485_ = v___x_2472_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_decl_2480_);
v___x_2485_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
lean_object* v___x_2486_; lean_object* v___x_2488_; 
v___x_2486_ = l_Lean_PersistentArray_set___redArg(v_decls_2475_, v___y_2483_, v___x_2485_);
lean_dec(v___y_2483_);
if (v_isShared_2479_ == 0)
{
lean_ctor_set(v___x_2478_, 1, v___x_2486_);
lean_ctor_set(v___x_2478_, 0, v___y_2482_);
v___x_2488_ = v___x_2478_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v___y_2482_);
lean_ctor_set(v_reuseFailAlloc_2489_, 1, v___x_2486_);
lean_ctor_set(v_reuseFailAlloc_2489_, 2, v_auxDeclToFullName_2476_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
v___y_2464_ = v___x_2488_;
goto v___jp_2463_;
}
}
}
v___jp_2491_:
{
lean_object* v___x_2493_; lean_object* v_index_2494_; 
lean_inc_ref(v_decl_2480_);
v___x_2493_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2474_, v___y_2492_, v_decl_2480_);
v_index_2494_ = lean_ctor_get(v_decl_2480_, 0);
lean_inc(v_index_2494_);
v___y_2482_ = v___x_2493_;
v___y_2483_ = v_index_2494_;
goto v___jp_2481_;
}
}
}
}
}
else
{
lean_dec_ref(v_f_2458_);
return v_b_2462_;
}
v___jp_2463_:
{
size_t v___x_2465_; size_t v___x_2466_; 
v___x_2465_ = ((size_t)1ULL);
v___x_2466_ = lean_usize_add(v_i_2460_, v___x_2465_);
v_i_2460_ = v___x_2466_;
v_b_2462_ = v___y_2464_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1___boxed(lean_object* v_f_2498_, lean_object* v_as_2499_, lean_object* v_i_2500_, lean_object* v_stop_2501_, lean_object* v_b_2502_){
_start:
{
size_t v_i_boxed_2503_; size_t v_stop_boxed_2504_; lean_object* v_res_2505_; 
v_i_boxed_2503_ = lean_unbox_usize(v_i_2500_);
lean_dec(v_i_2500_);
v_stop_boxed_2504_ = lean_unbox_usize(v_stop_2501_);
lean_dec(v_stop_2501_);
v_res_2505_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2498_, v_as_2499_, v_i_boxed_2503_, v_stop_boxed_2504_, v_b_2502_);
lean_dec_ref(v_as_2499_);
return v_res_2505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(lean_object* v_f_2506_, lean_object* v_x_2507_, lean_object* v_x_2508_){
_start:
{
if (lean_obj_tag(v_x_2507_) == 0)
{
lean_object* v_cs_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; uint8_t v___x_2512_; 
v_cs_2509_ = lean_ctor_get(v_x_2507_, 0);
v___x_2510_ = lean_unsigned_to_nat(0u);
v___x_2511_ = lean_array_get_size(v_cs_2509_);
v___x_2512_ = lean_nat_dec_lt(v___x_2510_, v___x_2511_);
if (v___x_2512_ == 0)
{
lean_dec_ref(v_f_2506_);
return v_x_2508_;
}
else
{
size_t v___x_2513_; size_t v___x_2514_; lean_object* v___x_2515_; 
v___x_2513_ = ((size_t)0ULL);
v___x_2514_ = lean_usize_of_nat(v___x_2511_);
v___x_2515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2506_, v_cs_2509_, v___x_2513_, v___x_2514_, v_x_2508_);
return v___x_2515_;
}
}
else
{
lean_object* v_vs_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; uint8_t v___x_2519_; 
v_vs_2516_ = lean_ctor_get(v_x_2507_, 0);
v___x_2517_ = lean_unsigned_to_nat(0u);
v___x_2518_ = lean_array_get_size(v_vs_2516_);
v___x_2519_ = lean_nat_dec_lt(v___x_2517_, v___x_2518_);
if (v___x_2519_ == 0)
{
lean_dec_ref(v_f_2506_);
return v_x_2508_;
}
else
{
size_t v___x_2520_; size_t v___x_2521_; lean_object* v___x_2522_; 
v___x_2520_ = ((size_t)0ULL);
v___x_2521_ = lean_usize_of_nat(v___x_2518_);
v___x_2522_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2506_, v_vs_2516_, v___x_2520_, v___x_2521_, v_x_2508_);
return v___x_2522_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(lean_object* v_f_2523_, lean_object* v_as_2524_, size_t v_i_2525_, size_t v_stop_2526_, lean_object* v_b_2527_){
_start:
{
uint8_t v___x_2528_; 
v___x_2528_ = lean_usize_dec_eq(v_i_2525_, v_stop_2526_);
if (v___x_2528_ == 0)
{
lean_object* v___x_2529_; lean_object* v___x_2530_; size_t v___x_2531_; size_t v___x_2532_; 
v___x_2529_ = lean_array_uget_borrowed(v_as_2524_, v_i_2525_);
lean_inc_ref(v_f_2523_);
v___x_2530_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(v_f_2523_, v___x_2529_, v_b_2527_);
v___x_2531_ = ((size_t)1ULL);
v___x_2532_ = lean_usize_add(v_i_2525_, v___x_2531_);
v_i_2525_ = v___x_2532_;
v_b_2527_ = v___x_2530_;
goto _start;
}
else
{
lean_dec_ref(v_f_2523_);
return v_b_2527_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1___boxed(lean_object* v_f_2534_, lean_object* v_as_2535_, lean_object* v_i_2536_, lean_object* v_stop_2537_, lean_object* v_b_2538_){
_start:
{
size_t v_i_boxed_2539_; size_t v_stop_boxed_2540_; lean_object* v_res_2541_; 
v_i_boxed_2539_ = lean_unbox_usize(v_i_2536_);
lean_dec(v_i_2536_);
v_stop_boxed_2540_ = lean_unbox_usize(v_stop_2537_);
lean_dec(v_stop_2537_);
v_res_2541_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2534_, v_as_2535_, v_i_boxed_2539_, v_stop_boxed_2540_, v_b_2538_);
lean_dec_ref(v_as_2535_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2___boxed(lean_object* v_f_2542_, lean_object* v_x_2543_, lean_object* v_x_2544_){
_start:
{
lean_object* v_res_2545_; 
v_res_2545_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(v_f_2542_, v_x_2543_, v_x_2544_);
lean_dec_ref(v_x_2543_);
return v_res_2545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(lean_object* v_f_2546_, lean_object* v_x_2547_, size_t v_x_2548_, size_t v_x_2549_, lean_object* v_x_2550_){
_start:
{
if (lean_obj_tag(v_x_2547_) == 0)
{
lean_object* v_cs_2551_; lean_object* v___x_2552_; size_t v___x_2553_; lean_object* v_j_2554_; lean_object* v___x_2555_; size_t v___x_2556_; size_t v___x_2557_; size_t v___x_2558_; size_t v___x_2559_; size_t v___x_2560_; size_t v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; uint8_t v___x_2566_; 
v_cs_2551_ = lean_ctor_get(v_x_2547_, 0);
v___x_2552_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0);
v___x_2553_ = lean_usize_shift_right(v_x_2548_, v_x_2549_);
v_j_2554_ = lean_usize_to_nat(v___x_2553_);
v___x_2555_ = lean_array_get_borrowed(v___x_2552_, v_cs_2551_, v_j_2554_);
v___x_2556_ = ((size_t)1ULL);
v___x_2557_ = lean_usize_shift_left(v___x_2556_, v_x_2549_);
v___x_2558_ = lean_usize_sub(v___x_2557_, v___x_2556_);
v___x_2559_ = lean_usize_land(v_x_2548_, v___x_2558_);
v___x_2560_ = ((size_t)5ULL);
v___x_2561_ = lean_usize_sub(v_x_2549_, v___x_2560_);
lean_inc_ref(v_f_2546_);
v___x_2562_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(v_f_2546_, v___x_2555_, v___x_2559_, v___x_2561_, v_x_2550_);
v___x_2563_ = lean_unsigned_to_nat(1u);
v___x_2564_ = lean_nat_add(v_j_2554_, v___x_2563_);
lean_dec(v_j_2554_);
v___x_2565_ = lean_array_get_size(v_cs_2551_);
v___x_2566_ = lean_nat_dec_lt(v___x_2564_, v___x_2565_);
if (v___x_2566_ == 0)
{
lean_dec(v___x_2564_);
lean_dec_ref(v_f_2546_);
return v___x_2562_;
}
else
{
size_t v___x_2567_; size_t v___x_2568_; lean_object* v___x_2569_; 
v___x_2567_ = lean_usize_of_nat(v___x_2564_);
lean_dec(v___x_2564_);
v___x_2568_ = lean_usize_of_nat(v___x_2565_);
v___x_2569_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2546_, v_cs_2551_, v___x_2567_, v___x_2568_, v___x_2562_);
return v___x_2569_;
}
}
else
{
lean_object* v_vs_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; uint8_t v___x_2573_; 
v_vs_2570_ = lean_ctor_get(v_x_2547_, 0);
v___x_2571_ = lean_usize_to_nat(v_x_2548_);
v___x_2572_ = lean_array_get_size(v_vs_2570_);
v___x_2573_ = lean_nat_dec_lt(v___x_2571_, v___x_2572_);
if (v___x_2573_ == 0)
{
lean_dec(v___x_2571_);
lean_dec_ref(v_f_2546_);
return v_x_2550_;
}
else
{
size_t v___x_2574_; size_t v___x_2575_; lean_object* v___x_2576_; 
v___x_2574_ = lean_usize_of_nat(v___x_2571_);
lean_dec(v___x_2571_);
v___x_2575_ = lean_usize_of_nat(v___x_2572_);
v___x_2576_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2546_, v_vs_2570_, v___x_2574_, v___x_2575_, v_x_2550_);
return v___x_2576_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0___boxed(lean_object* v_f_2577_, lean_object* v_x_2578_, lean_object* v_x_2579_, lean_object* v_x_2580_, lean_object* v_x_2581_){
_start:
{
size_t v_x_1489__boxed_2582_; size_t v_x_1490__boxed_2583_; lean_object* v_res_2584_; 
v_x_1489__boxed_2582_ = lean_unbox_usize(v_x_2579_);
lean_dec(v_x_2579_);
v_x_1490__boxed_2583_ = lean_unbox_usize(v_x_2580_);
lean_dec(v_x_2580_);
v_res_2584_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(v_f_2577_, v_x_2578_, v_x_1489__boxed_2582_, v_x_1490__boxed_2583_, v_x_2581_);
lean_dec_ref(v_x_2578_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0(lean_object* v_f_2585_, lean_object* v_t_2586_, lean_object* v_init_2587_, lean_object* v_start_2588_){
_start:
{
lean_object* v___x_2589_; uint8_t v___x_2590_; 
v___x_2589_ = lean_unsigned_to_nat(0u);
v___x_2590_ = lean_nat_dec_eq(v_start_2588_, v___x_2589_);
if (v___x_2590_ == 0)
{
lean_object* v_root_2591_; lean_object* v_tail_2592_; size_t v_shift_2593_; lean_object* v_tailOff_2594_; uint8_t v___x_2595_; 
v_root_2591_ = lean_ctor_get(v_t_2586_, 0);
v_tail_2592_ = lean_ctor_get(v_t_2586_, 1);
v_shift_2593_ = lean_ctor_get_usize(v_t_2586_, 4);
v_tailOff_2594_ = lean_ctor_get(v_t_2586_, 3);
v___x_2595_ = lean_nat_dec_le(v_tailOff_2594_, v_start_2588_);
if (v___x_2595_ == 0)
{
size_t v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; uint8_t v___x_2599_; 
v___x_2596_ = lean_usize_of_nat(v_start_2588_);
lean_inc_ref(v_f_2585_);
v___x_2597_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(v_f_2585_, v_root_2591_, v___x_2596_, v_shift_2593_, v_init_2587_);
v___x_2598_ = lean_array_get_size(v_tail_2592_);
v___x_2599_ = lean_nat_dec_lt(v___x_2589_, v___x_2598_);
if (v___x_2599_ == 0)
{
lean_dec_ref(v_f_2585_);
return v___x_2597_;
}
else
{
size_t v___x_2600_; size_t v___x_2601_; lean_object* v___x_2602_; 
v___x_2600_ = ((size_t)0ULL);
v___x_2601_ = lean_usize_of_nat(v___x_2598_);
v___x_2602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2585_, v_tail_2592_, v___x_2600_, v___x_2601_, v___x_2597_);
return v___x_2602_;
}
}
else
{
lean_object* v___x_2603_; lean_object* v___x_2604_; uint8_t v___x_2605_; 
v___x_2603_ = lean_nat_sub(v_start_2588_, v_tailOff_2594_);
v___x_2604_ = lean_array_get_size(v_tail_2592_);
v___x_2605_ = lean_nat_dec_lt(v___x_2603_, v___x_2604_);
if (v___x_2605_ == 0)
{
lean_dec(v___x_2603_);
lean_dec_ref(v_f_2585_);
return v_init_2587_;
}
else
{
size_t v___x_2606_; size_t v___x_2607_; lean_object* v___x_2608_; 
v___x_2606_ = lean_usize_of_nat(v___x_2603_);
lean_dec(v___x_2603_);
v___x_2607_ = lean_usize_of_nat(v___x_2604_);
v___x_2608_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2585_, v_tail_2592_, v___x_2606_, v___x_2607_, v_init_2587_);
return v___x_2608_;
}
}
}
else
{
lean_object* v_root_2609_; lean_object* v_tail_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; uint8_t v___x_2613_; 
v_root_2609_ = lean_ctor_get(v_t_2586_, 0);
v_tail_2610_ = lean_ctor_get(v_t_2586_, 1);
lean_inc_ref(v_f_2585_);
v___x_2611_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(v_f_2585_, v_root_2609_, v_init_2587_);
v___x_2612_ = lean_array_get_size(v_tail_2610_);
v___x_2613_ = lean_nat_dec_lt(v___x_2589_, v___x_2612_);
if (v___x_2613_ == 0)
{
lean_dec_ref(v_f_2585_);
return v___x_2611_;
}
else
{
size_t v___x_2614_; size_t v___x_2615_; lean_object* v___x_2616_; 
v___x_2614_ = ((size_t)0ULL);
v___x_2615_ = lean_usize_of_nat(v___x_2612_);
v___x_2616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2585_, v_tail_2610_, v___x_2614_, v___x_2615_, v___x_2611_);
return v___x_2616_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0___boxed(lean_object* v_f_2617_, lean_object* v_t_2618_, lean_object* v_init_2619_, lean_object* v_start_2620_){
_start:
{
lean_object* v_res_2621_; 
v_res_2621_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0(v_f_2617_, v_t_2618_, v_init_2619_, v_start_2620_);
lean_dec(v_start_2620_);
lean_dec_ref(v_t_2618_);
return v_res_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_modifyLocalDecls(lean_object* v_lctx_2622_, lean_object* v_f_2623_){
_start:
{
lean_object* v_decls_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
v_decls_2624_ = lean_ctor_get(v_lctx_2622_, 1);
lean_inc_ref(v_decls_2624_);
v___x_2625_ = lean_unsigned_to_nat(0u);
v___x_2626_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0(v_f_2623_, v_decls_2624_, v_lctx_2622_, v___x_2625_);
lean_dec_ref(v_decls_2624_);
return v___x_2626_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setKind(lean_object* v_lctx_2627_, lean_object* v_fvarId_2628_, uint8_t v_kind_2629_){
_start:
{
lean_object* v_fvarIdToDecl_2630_; lean_object* v_decls_2631_; lean_object* v_auxDeclToFullName_2632_; lean_object* v___x_2633_; 
v_fvarIdToDecl_2630_ = lean_ctor_get(v_lctx_2627_, 0);
v_decls_2631_ = lean_ctor_get(v_lctx_2627_, 1);
v_auxDeclToFullName_2632_ = lean_ctor_get(v_lctx_2627_, 2);
lean_inc_ref(v_lctx_2627_);
v___x_2633_ = lean_local_ctx_find(v_lctx_2627_, v_fvarId_2628_);
if (lean_obj_tag(v___x_2633_) == 0)
{
return v_lctx_2627_;
}
else
{
lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2658_; 
lean_inc(v_auxDeclToFullName_2632_);
lean_inc_ref(v_decls_2631_);
lean_inc_ref(v_fvarIdToDecl_2630_);
v_isSharedCheck_2658_ = !lean_is_exclusive(v_lctx_2627_);
if (v_isSharedCheck_2658_ == 0)
{
lean_object* v_unused_2659_; lean_object* v_unused_2660_; lean_object* v_unused_2661_; 
v_unused_2659_ = lean_ctor_get(v_lctx_2627_, 2);
lean_dec(v_unused_2659_);
v_unused_2660_ = lean_ctor_get(v_lctx_2627_, 1);
lean_dec(v_unused_2660_);
v_unused_2661_ = lean_ctor_get(v_lctx_2627_, 0);
lean_dec(v_unused_2661_);
v___x_2635_ = v_lctx_2627_;
v_isShared_2636_ = v_isSharedCheck_2658_;
goto v_resetjp_2634_;
}
else
{
lean_dec(v_lctx_2627_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2658_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v_val_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2657_; 
v_val_2637_ = lean_ctor_get(v___x_2633_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2639_ = v___x_2633_;
v_isShared_2640_ = v_isSharedCheck_2657_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_val_2637_);
lean_dec(v___x_2633_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2657_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v_decl_2641_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2653_; lean_object* v_fvarId_2656_; 
v_decl_2641_ = l_Lean_LocalDecl_setKind(v_val_2637_, v_kind_2629_);
v_fvarId_2656_ = lean_ctor_get(v_decl_2641_, 1);
lean_inc(v_fvarId_2656_);
v___y_2653_ = v_fvarId_2656_;
goto v___jp_2652_;
v___jp_2642_:
{
lean_object* v___x_2646_; 
if (v_isShared_2640_ == 0)
{
lean_ctor_set(v___x_2639_, 0, v_decl_2641_);
v___x_2646_ = v___x_2639_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_decl_2641_);
v___x_2646_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
lean_object* v___x_2647_; lean_object* v___x_2649_; 
v___x_2647_ = l_Lean_PersistentArray_set___redArg(v_decls_2631_, v___y_2644_, v___x_2646_);
lean_dec(v___y_2644_);
if (v_isShared_2636_ == 0)
{
lean_ctor_set(v___x_2635_, 1, v___x_2647_);
lean_ctor_set(v___x_2635_, 0, v___y_2643_);
v___x_2649_ = v___x_2635_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v___y_2643_);
lean_ctor_set(v_reuseFailAlloc_2650_, 1, v___x_2647_);
lean_ctor_set(v_reuseFailAlloc_2650_, 2, v_auxDeclToFullName_2632_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
v___jp_2652_:
{
lean_object* v___x_2654_; lean_object* v_index_2655_; 
lean_inc_ref(v_decl_2641_);
v___x_2654_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2630_, v___y_2653_, v_decl_2641_);
v_index_2655_ = lean_ctor_get(v_decl_2641_, 0);
lean_inc(v_index_2655_);
v___y_2643_ = v___x_2654_;
v___y_2644_ = v_index_2655_;
goto v___jp_2642_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setKind___boxed(lean_object* v_lctx_2662_, lean_object* v_fvarId_2663_, lean_object* v_kind_2664_){
_start:
{
uint8_t v_kind_boxed_2665_; lean_object* v_res_2666_; 
v_kind_boxed_2665_ = lean_unbox(v_kind_2664_);
v_res_2666_ = l_Lean_LocalContext_setKind(v_lctx_2662_, v_fvarId_2663_, v_kind_boxed_2665_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setBinderInfo(lean_object* v_lctx_2667_, lean_object* v_fvarId_2668_, uint8_t v_bi_2669_){
_start:
{
lean_object* v_fvarIdToDecl_2670_; lean_object* v_decls_2671_; lean_object* v_auxDeclToFullName_2672_; lean_object* v___x_2673_; 
v_fvarIdToDecl_2670_ = lean_ctor_get(v_lctx_2667_, 0);
v_decls_2671_ = lean_ctor_get(v_lctx_2667_, 1);
v_auxDeclToFullName_2672_ = lean_ctor_get(v_lctx_2667_, 2);
lean_inc_ref(v_lctx_2667_);
v___x_2673_ = lean_local_ctx_find(v_lctx_2667_, v_fvarId_2668_);
if (lean_obj_tag(v___x_2673_) == 0)
{
return v_lctx_2667_;
}
else
{
lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2698_; 
lean_inc(v_auxDeclToFullName_2672_);
lean_inc_ref(v_decls_2671_);
lean_inc_ref(v_fvarIdToDecl_2670_);
v_isSharedCheck_2698_ = !lean_is_exclusive(v_lctx_2667_);
if (v_isSharedCheck_2698_ == 0)
{
lean_object* v_unused_2699_; lean_object* v_unused_2700_; lean_object* v_unused_2701_; 
v_unused_2699_ = lean_ctor_get(v_lctx_2667_, 2);
lean_dec(v_unused_2699_);
v_unused_2700_ = lean_ctor_get(v_lctx_2667_, 1);
lean_dec(v_unused_2700_);
v_unused_2701_ = lean_ctor_get(v_lctx_2667_, 0);
lean_dec(v_unused_2701_);
v___x_2675_ = v_lctx_2667_;
v_isShared_2676_ = v_isSharedCheck_2698_;
goto v_resetjp_2674_;
}
else
{
lean_dec(v_lctx_2667_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2698_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v_val_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2697_; 
v_val_2677_ = lean_ctor_get(v___x_2673_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2673_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2679_ = v___x_2673_;
v_isShared_2680_ = v_isSharedCheck_2697_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_val_2677_);
lean_dec(v___x_2673_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2697_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v_decl_2681_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2693_; lean_object* v_fvarId_2696_; 
v_decl_2681_ = l_Lean_LocalDecl_setBinderInfo(v_val_2677_, v_bi_2669_);
v_fvarId_2696_ = lean_ctor_get(v_decl_2681_, 1);
lean_inc(v_fvarId_2696_);
v___y_2693_ = v_fvarId_2696_;
goto v___jp_2692_;
v___jp_2682_:
{
lean_object* v___x_2686_; 
if (v_isShared_2680_ == 0)
{
lean_ctor_set(v___x_2679_, 0, v_decl_2681_);
v___x_2686_ = v___x_2679_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_decl_2681_);
v___x_2686_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
lean_object* v___x_2687_; lean_object* v___x_2689_; 
v___x_2687_ = l_Lean_PersistentArray_set___redArg(v_decls_2671_, v___y_2684_, v___x_2686_);
lean_dec(v___y_2684_);
if (v_isShared_2676_ == 0)
{
lean_ctor_set(v___x_2675_, 1, v___x_2687_);
lean_ctor_set(v___x_2675_, 0, v___y_2683_);
v___x_2689_ = v___x_2675_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v___y_2683_);
lean_ctor_set(v_reuseFailAlloc_2690_, 1, v___x_2687_);
lean_ctor_set(v_reuseFailAlloc_2690_, 2, v_auxDeclToFullName_2672_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
v___jp_2692_:
{
lean_object* v___x_2694_; lean_object* v_index_2695_; 
lean_inc_ref(v_decl_2681_);
v___x_2694_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2670_, v___y_2693_, v_decl_2681_);
v_index_2695_ = lean_ctor_get(v_decl_2681_, 0);
lean_inc(v_index_2695_);
v___y_2683_ = v___x_2694_;
v___y_2684_ = v_index_2695_;
goto v___jp_2682_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setBinderInfo___boxed(lean_object* v_lctx_2702_, lean_object* v_fvarId_2703_, lean_object* v_bi_2704_){
_start:
{
uint8_t v_bi_boxed_2705_; lean_object* v_res_2706_; 
v_bi_boxed_2705_ = lean_unbox(v_bi_2704_);
v_res_2706_ = l_Lean_LocalContext_setBinderInfo(v_lctx_2702_, v_fvarId_2703_, v_bi_boxed_2705_);
return v_res_2706_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setType(lean_object* v_lctx_2707_, lean_object* v_fvarId_2708_, lean_object* v_type_2709_){
_start:
{
lean_object* v_fvarIdToDecl_2710_; lean_object* v_decls_2711_; lean_object* v_auxDeclToFullName_2712_; lean_object* v___x_2713_; 
v_fvarIdToDecl_2710_ = lean_ctor_get(v_lctx_2707_, 0);
v_decls_2711_ = lean_ctor_get(v_lctx_2707_, 1);
v_auxDeclToFullName_2712_ = lean_ctor_get(v_lctx_2707_, 2);
lean_inc_ref(v_lctx_2707_);
v___x_2713_ = lean_local_ctx_find(v_lctx_2707_, v_fvarId_2708_);
if (lean_obj_tag(v___x_2713_) == 0)
{
lean_dec_ref(v_type_2709_);
return v_lctx_2707_;
}
else
{
lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2738_; 
lean_inc(v_auxDeclToFullName_2712_);
lean_inc_ref(v_decls_2711_);
lean_inc_ref(v_fvarIdToDecl_2710_);
v_isSharedCheck_2738_ = !lean_is_exclusive(v_lctx_2707_);
if (v_isSharedCheck_2738_ == 0)
{
lean_object* v_unused_2739_; lean_object* v_unused_2740_; lean_object* v_unused_2741_; 
v_unused_2739_ = lean_ctor_get(v_lctx_2707_, 2);
lean_dec(v_unused_2739_);
v_unused_2740_ = lean_ctor_get(v_lctx_2707_, 1);
lean_dec(v_unused_2740_);
v_unused_2741_ = lean_ctor_get(v_lctx_2707_, 0);
lean_dec(v_unused_2741_);
v___x_2715_ = v_lctx_2707_;
v_isShared_2716_ = v_isSharedCheck_2738_;
goto v_resetjp_2714_;
}
else
{
lean_dec(v_lctx_2707_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2738_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v_val_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2737_; 
v_val_2717_ = lean_ctor_get(v___x_2713_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2719_ = v___x_2713_;
v_isShared_2720_ = v_isSharedCheck_2737_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_val_2717_);
lean_dec(v___x_2713_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2737_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v_decl_2721_; lean_object* v___y_2723_; lean_object* v___y_2724_; lean_object* v___y_2733_; lean_object* v_fvarId_2736_; 
v_decl_2721_ = l_Lean_LocalDecl_setType(v_val_2717_, v_type_2709_);
v_fvarId_2736_ = lean_ctor_get(v_decl_2721_, 1);
lean_inc(v_fvarId_2736_);
v___y_2733_ = v_fvarId_2736_;
goto v___jp_2732_;
v___jp_2722_:
{
lean_object* v___x_2726_; 
if (v_isShared_2720_ == 0)
{
lean_ctor_set(v___x_2719_, 0, v_decl_2721_);
v___x_2726_ = v___x_2719_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_decl_2721_);
v___x_2726_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
lean_object* v___x_2727_; lean_object* v___x_2729_; 
v___x_2727_ = l_Lean_PersistentArray_set___redArg(v_decls_2711_, v___y_2724_, v___x_2726_);
lean_dec(v___y_2724_);
if (v_isShared_2716_ == 0)
{
lean_ctor_set(v___x_2715_, 1, v___x_2727_);
lean_ctor_set(v___x_2715_, 0, v___y_2723_);
v___x_2729_ = v___x_2715_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v___y_2723_);
lean_ctor_set(v_reuseFailAlloc_2730_, 1, v___x_2727_);
lean_ctor_set(v_reuseFailAlloc_2730_, 2, v_auxDeclToFullName_2712_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
}
v___jp_2732_:
{
lean_object* v___x_2734_; lean_object* v_index_2735_; 
lean_inc_ref(v_decl_2721_);
v___x_2734_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2710_, v___y_2733_, v_decl_2721_);
v_index_2735_ = lean_ctor_get(v_decl_2721_, 0);
lean_inc(v_index_2735_);
v___y_2723_ = v___x_2734_;
v___y_2724_ = v_index_2735_;
goto v___jp_2722_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lean_local_ctx_num_indices(lean_object* v_lctx_2742_){
_start:
{
lean_object* v_decls_2743_; lean_object* v_size_2744_; 
v_decls_2743_ = lean_ctor_get(v_lctx_2742_, 1);
lean_inc_ref(v_decls_2743_);
lean_dec_ref(v_lctx_2742_);
v_size_2744_ = lean_ctor_get(v_decls_2743_, 2);
lean_inc(v_size_2744_);
lean_dec_ref(v_decls_2743_);
return v_size_2744_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getAt_x3f(lean_object* v_lctx_2745_, lean_object* v_i_2746_){
_start:
{
lean_object* v_decls_2747_; lean_object* v_size_2748_; lean_object* v___x_2749_; uint8_t v___x_2750_; 
v_decls_2747_ = lean_ctor_get(v_lctx_2745_, 1);
v_size_2748_ = lean_ctor_get(v_decls_2747_, 2);
v___x_2749_ = lean_box(0);
v___x_2750_ = lean_nat_dec_lt(v_i_2746_, v_size_2748_);
if (v___x_2750_ == 0)
{
lean_object* v___x_2751_; 
v___x_2751_ = l_outOfBounds___redArg(v___x_2749_);
return v___x_2751_;
}
else
{
lean_object* v___x_2752_; 
v___x_2752_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2749_, v_decls_2747_, v_i_2746_);
return v___x_2752_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getAt_x3f___boxed(lean_object* v_lctx_2753_, lean_object* v_i_2754_){
_start:
{
lean_object* v_res_2755_; 
v_res_2755_ = l_Lean_LocalContext_getAt_x3f(v_lctx_2753_, v_i_2754_);
lean_dec(v_i_2754_);
lean_dec_ref(v_lctx_2753_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg___lam__0(lean_object* v_toPure_2756_, lean_object* v_f_2757_, lean_object* v_b_2758_, lean_object* v_decl_2759_){
_start:
{
if (lean_obj_tag(v_decl_2759_) == 0)
{
lean_object* v___x_2760_; 
lean_dec(v_f_2757_);
v___x_2760_ = lean_apply_2(v_toPure_2756_, lean_box(0), v_b_2758_);
return v___x_2760_;
}
else
{
lean_object* v_val_2761_; lean_object* v___x_2762_; 
lean_dec(v_toPure_2756_);
v_val_2761_ = lean_ctor_get(v_decl_2759_, 0);
lean_inc(v_val_2761_);
lean_dec_ref_known(v_decl_2759_, 1);
v___x_2762_ = lean_apply_2(v_f_2757_, v_b_2758_, v_val_2761_);
return v___x_2762_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg(lean_object* v_inst_2763_, lean_object* v_lctx_2764_, lean_object* v_f_2765_, lean_object* v_init_2766_, lean_object* v_start_2767_){
_start:
{
lean_object* v_toApplicative_2768_; lean_object* v_decls_2769_; lean_object* v_toPure_2770_; lean_object* v___f_2771_; lean_object* v___x_2772_; 
v_toApplicative_2768_ = lean_ctor_get(v_inst_2763_, 0);
v_decls_2769_ = lean_ctor_get(v_lctx_2764_, 1);
lean_inc_ref(v_decls_2769_);
lean_dec_ref(v_lctx_2764_);
v_toPure_2770_ = lean_ctor_get(v_toApplicative_2768_, 1);
lean_inc(v_toPure_2770_);
v___f_2771_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldlM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2771_, 0, v_toPure_2770_);
lean_closure_set(v___f_2771_, 1, v_f_2765_);
v___x_2772_ = l_Lean_PersistentArray_foldlM___redArg(v_inst_2763_, v_decls_2769_, v___f_2771_, v_init_2766_, v_start_2767_);
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg___boxed(lean_object* v_inst_2773_, lean_object* v_lctx_2774_, lean_object* v_f_2775_, lean_object* v_init_2776_, lean_object* v_start_2777_){
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = l_Lean_LocalContext_foldlM___redArg(v_inst_2773_, v_lctx_2774_, v_f_2775_, v_init_2776_, v_start_2777_);
lean_dec(v_start_2777_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM(lean_object* v_m_2779_, lean_object* v_00_u03b2_2780_, lean_object* v_inst_2781_, lean_object* v_lctx_2782_, lean_object* v_f_2783_, lean_object* v_init_2784_, lean_object* v_start_2785_){
_start:
{
lean_object* v___x_2786_; 
v___x_2786_ = l_Lean_LocalContext_foldlM___redArg(v_inst_2781_, v_lctx_2782_, v_f_2783_, v_init_2784_, v_start_2785_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___boxed(lean_object* v_m_2787_, lean_object* v_00_u03b2_2788_, lean_object* v_inst_2789_, lean_object* v_lctx_2790_, lean_object* v_f_2791_, lean_object* v_init_2792_, lean_object* v_start_2793_){
_start:
{
lean_object* v_res_2794_; 
v_res_2794_ = l_Lean_LocalContext_foldlM(v_m_2787_, v_00_u03b2_2788_, v_inst_2789_, v_lctx_2790_, v_f_2791_, v_init_2792_, v_start_2793_);
lean_dec(v_start_2793_);
return v_res_2794_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___redArg___lam__0(lean_object* v_toPure_2795_, lean_object* v_f_2796_, lean_object* v_decl_2797_, lean_object* v_b_2798_){
_start:
{
if (lean_obj_tag(v_decl_2797_) == 0)
{
lean_object* v___x_2799_; 
lean_dec(v_f_2796_);
v___x_2799_ = lean_apply_2(v_toPure_2795_, lean_box(0), v_b_2798_);
return v___x_2799_;
}
else
{
lean_object* v_val_2800_; lean_object* v___x_2801_; 
lean_dec(v_toPure_2795_);
v_val_2800_ = lean_ctor_get(v_decl_2797_, 0);
lean_inc(v_val_2800_);
lean_dec_ref_known(v_decl_2797_, 1);
v___x_2801_ = lean_apply_2(v_f_2796_, v_val_2800_, v_b_2798_);
return v___x_2801_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___redArg(lean_object* v_inst_2802_, lean_object* v_lctx_2803_, lean_object* v_f_2804_, lean_object* v_init_2805_){
_start:
{
lean_object* v_toApplicative_2806_; lean_object* v_decls_2807_; lean_object* v_toPure_2808_; lean_object* v___f_2809_; lean_object* v___x_2810_; 
v_toApplicative_2806_ = lean_ctor_get(v_inst_2802_, 0);
v_decls_2807_ = lean_ctor_get(v_lctx_2803_, 1);
lean_inc_ref(v_decls_2807_);
lean_dec_ref(v_lctx_2803_);
v_toPure_2808_ = lean_ctor_get(v_toApplicative_2806_, 1);
lean_inc(v_toPure_2808_);
v___f_2809_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldrM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2809_, 0, v_toPure_2808_);
lean_closure_set(v___f_2809_, 1, v_f_2804_);
v___x_2810_ = l_Lean_PersistentArray_foldrM___redArg(v_inst_2802_, v_decls_2807_, v___f_2809_, v_init_2805_);
return v___x_2810_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM(lean_object* v_m_2811_, lean_object* v_00_u03b2_2812_, lean_object* v_inst_2813_, lean_object* v_lctx_2814_, lean_object* v_f_2815_, lean_object* v_init_2816_){
_start:
{
lean_object* v___x_2817_; 
v___x_2817_ = l_Lean_LocalContext_foldrM___redArg(v_inst_2813_, v_lctx_2814_, v_f_2815_, v_init_2816_);
return v___x_2817_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg___lam__0(lean_object* v_toPure_2818_, lean_object* v_f_2819_, lean_object* v_decl_2820_){
_start:
{
if (lean_obj_tag(v_decl_2820_) == 0)
{
lean_object* v___x_2821_; lean_object* v___x_2822_; 
lean_dec(v_f_2819_);
v___x_2821_ = lean_box(0);
v___x_2822_ = lean_apply_2(v_toPure_2818_, lean_box(0), v___x_2821_);
return v___x_2822_;
}
else
{
lean_object* v_val_2823_; lean_object* v___x_2824_; 
lean_dec(v_toPure_2818_);
v_val_2823_ = lean_ctor_get(v_decl_2820_, 0);
lean_inc(v_val_2823_);
lean_dec_ref_known(v_decl_2820_, 1);
v___x_2824_ = lean_apply_1(v_f_2819_, v_val_2823_);
return v___x_2824_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg(lean_object* v_inst_2825_, lean_object* v_lctx_2826_, lean_object* v_f_2827_, lean_object* v_start_2828_){
_start:
{
lean_object* v_toApplicative_2829_; lean_object* v_decls_2830_; lean_object* v_toPure_2831_; lean_object* v___f_2832_; lean_object* v___x_2833_; 
v_toApplicative_2829_ = lean_ctor_get(v_inst_2825_, 0);
v_decls_2830_ = lean_ctor_get(v_lctx_2826_, 1);
lean_inc_ref(v_decls_2830_);
lean_dec_ref(v_lctx_2826_);
v_toPure_2831_ = lean_ctor_get(v_toApplicative_2829_, 1);
lean_inc(v_toPure_2831_);
v___f_2832_ = lean_alloc_closure((void*)(l_Lean_LocalContext_forM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2832_, 0, v_toPure_2831_);
lean_closure_set(v___f_2832_, 1, v_f_2827_);
v___x_2833_ = l_Lean_PersistentArray_forM___redArg(v_inst_2825_, v_decls_2830_, v___f_2832_, v_start_2828_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg___boxed(lean_object* v_inst_2834_, lean_object* v_lctx_2835_, lean_object* v_f_2836_, lean_object* v_start_2837_){
_start:
{
lean_object* v_res_2838_; 
v_res_2838_ = l_Lean_LocalContext_forM___redArg(v_inst_2834_, v_lctx_2835_, v_f_2836_, v_start_2837_);
lean_dec(v_start_2837_);
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM(lean_object* v_m_2839_, lean_object* v_inst_2840_, lean_object* v_lctx_2841_, lean_object* v_f_2842_, lean_object* v_start_2843_){
_start:
{
lean_object* v___x_2844_; 
v___x_2844_ = l_Lean_LocalContext_forM___redArg(v_inst_2840_, v_lctx_2841_, v_f_2842_, v_start_2843_);
return v___x_2844_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___boxed(lean_object* v_m_2845_, lean_object* v_inst_2846_, lean_object* v_lctx_2847_, lean_object* v_f_2848_, lean_object* v_start_2849_){
_start:
{
lean_object* v_res_2850_; 
v_res_2850_ = l_Lean_LocalContext_forM(v_m_2845_, v_inst_2846_, v_lctx_2847_, v_f_2848_, v_start_2849_);
lean_dec(v_start_2849_);
return v_res_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0(lean_object* v_toPure_2851_, lean_object* v_f_2852_, lean_object* v_decl_2853_){
_start:
{
if (lean_obj_tag(v_decl_2853_) == 0)
{
lean_object* v___x_2854_; lean_object* v___x_2855_; 
lean_dec(v_f_2852_);
v___x_2854_ = lean_box(0);
v___x_2855_ = lean_apply_2(v_toPure_2851_, lean_box(0), v___x_2854_);
return v___x_2855_;
}
else
{
lean_object* v_val_2856_; lean_object* v___x_2857_; 
lean_dec(v_toPure_2851_);
v_val_2856_ = lean_ctor_get(v_decl_2853_, 0);
lean_inc(v_val_2856_);
lean_dec_ref_known(v_decl_2853_, 1);
v___x_2857_ = lean_apply_1(v_f_2852_, v_val_2856_);
return v___x_2857_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___redArg(lean_object* v_inst_2858_, lean_object* v_lctx_2859_, lean_object* v_f_2860_){
_start:
{
lean_object* v_toApplicative_2861_; lean_object* v_decls_2862_; lean_object* v_toPure_2863_; lean_object* v___f_2864_; lean_object* v___x_2865_; 
v_toApplicative_2861_ = lean_ctor_get(v_inst_2858_, 0);
v_decls_2862_ = lean_ctor_get(v_lctx_2859_, 1);
lean_inc_ref(v_decls_2862_);
lean_dec_ref(v_lctx_2859_);
v_toPure_2863_ = lean_ctor_get(v_toApplicative_2861_, 1);
lean_inc(v_toPure_2863_);
v___f_2864_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2864_, 0, v_toPure_2863_);
lean_closure_set(v___f_2864_, 1, v_f_2860_);
v___x_2865_ = l_Lean_PersistentArray_findSomeM_x3f___redArg(v_inst_2858_, v_decls_2862_, v___f_2864_);
return v___x_2865_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f(lean_object* v_m_2866_, lean_object* v_00_u03b2_2867_, lean_object* v_inst_2868_, lean_object* v_lctx_2869_, lean_object* v_f_2870_){
_start:
{
lean_object* v___x_2871_; 
v___x_2871_ = l_Lean_LocalContext_findDeclM_x3f___redArg(v_inst_2868_, v_lctx_2869_, v_f_2870_);
return v___x_2871_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___redArg(lean_object* v_inst_2872_, lean_object* v_lctx_2873_, lean_object* v_f_2874_){
_start:
{
lean_object* v_toApplicative_2875_; lean_object* v_decls_2876_; lean_object* v_toPure_2877_; lean_object* v___f_2878_; lean_object* v___x_2879_; 
v_toApplicative_2875_ = lean_ctor_get(v_inst_2872_, 0);
v_decls_2876_ = lean_ctor_get(v_lctx_2873_, 1);
lean_inc_ref(v_decls_2876_);
lean_dec_ref(v_lctx_2873_);
v_toPure_2877_ = lean_ctor_get(v_toApplicative_2875_, 1);
lean_inc(v_toPure_2877_);
v___f_2878_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2878_, 0, v_toPure_2877_);
lean_closure_set(v___f_2878_, 1, v_f_2874_);
v___x_2879_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v_inst_2872_, v_decls_2876_, v___f_2878_);
return v___x_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f(lean_object* v_m_2880_, lean_object* v_00_u03b2_2881_, lean_object* v_inst_2882_, lean_object* v_lctx_2883_, lean_object* v_f_2884_){
_start:
{
lean_object* v___x_2885_; 
v___x_2885_ = l_Lean_LocalContext_findDeclRevM_x3f___redArg(v_inst_2882_, v_lctx_2883_, v_f_2884_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__0(lean_object* v_toPure_2886_, lean_object* v_f_2887_, lean_object* v_d_x3f_2888_, lean_object* v_b_2889_){
_start:
{
if (lean_obj_tag(v_d_x3f_2888_) == 0)
{
lean_object* v___x_2890_; lean_object* v___x_2891_; 
lean_dec(v_f_2887_);
v___x_2890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2890_, 0, v_b_2889_);
v___x_2891_ = lean_apply_2(v_toPure_2886_, lean_box(0), v___x_2890_);
return v___x_2891_;
}
else
{
lean_object* v_val_2892_; lean_object* v___x_2893_; 
lean_dec(v_toPure_2886_);
v_val_2892_ = lean_ctor_get(v_d_x3f_2888_, 0);
lean_inc(v_val_2892_);
lean_dec_ref_known(v_d_x3f_2888_, 1);
v___x_2893_ = lean_apply_2(v_f_2887_, v_val_2892_, v_b_2889_);
return v___x_2893_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1(lean_object* v_toPure_2894_, lean_object* v_inst_2895_, lean_object* v_00_u03b2_2896_, lean_object* v_lctx_2897_, lean_object* v_init_2898_, lean_object* v_f_2899_){
_start:
{
lean_object* v_decls_2900_; lean_object* v___f_2901_; lean_object* v___x_2902_; 
v_decls_2900_ = lean_ctor_get(v_lctx_2897_, 1);
v___f_2901_ = lean_alloc_closure((void*)(l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2901_, 0, v_toPure_2894_);
lean_closure_set(v___f_2901_, 1, v_f_2899_);
v___x_2902_ = l_Lean_PersistentArray_forIn___redArg(v_inst_2895_, v_decls_2900_, v_init_2898_, v___f_2901_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1___boxed(lean_object* v_toPure_2903_, lean_object* v_inst_2904_, lean_object* v_00_u03b2_2905_, lean_object* v_lctx_2906_, lean_object* v_init_2907_, lean_object* v_f_2908_){
_start:
{
lean_object* v_res_2909_; 
v_res_2909_ = l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1(v_toPure_2903_, v_inst_2904_, v_00_u03b2_2905_, v_lctx_2906_, v_init_2907_, v_f_2908_);
lean_dec_ref(v_lctx_2906_);
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg(lean_object* v_inst_2910_){
_start:
{
lean_object* v_toApplicative_2911_; lean_object* v_toPure_2912_; lean_object* v___f_2913_; 
v_toApplicative_2911_ = lean_ctor_get(v_inst_2910_, 0);
v_toPure_2912_ = lean_ctor_get(v_toApplicative_2911_, 1);
lean_inc(v_toPure_2912_);
v___f_2913_ = lean_alloc_closure((void*)(l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1___boxed), 6, 2);
lean_closure_set(v___f_2913_, 0, v_toPure_2912_);
lean_closure_set(v___f_2913_, 1, v_inst_2910_);
return v___f_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad(lean_object* v_m_2914_, lean_object* v_inst_2915_){
_start:
{
lean_object* v___x_2916_; 
v___x_2916_ = l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg(v_inst_2915_);
return v___x_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg___lam__0(lean_object* v_f_2917_, lean_object* v_x1_2918_, lean_object* v_x2_2919_){
_start:
{
lean_object* v___x_2920_; 
v___x_2920_ = lean_apply_2(v_f_2917_, v_x1_2918_, v_x2_2919_);
return v___x_2920_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg(lean_object* v_lctx_2940_, lean_object* v_f_2941_, lean_object* v_init_2942_, lean_object* v_start_2943_){
_start:
{
lean_object* v___f_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___f_2944_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2944_, 0, v_f_2941_);
v___x_2945_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_2946_ = l_Lean_LocalContext_foldlM___redArg(v___x_2945_, v_lctx_2940_, v___f_2944_, v_init_2942_, v_start_2943_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg___boxed(lean_object* v_lctx_2947_, lean_object* v_f_2948_, lean_object* v_init_2949_, lean_object* v_start_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l_Lean_LocalContext_foldl___redArg(v_lctx_2947_, v_f_2948_, v_init_2949_, v_start_2950_);
lean_dec(v_start_2950_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl(lean_object* v_00_u03b2_2952_, lean_object* v_lctx_2953_, lean_object* v_f_2954_, lean_object* v_init_2955_, lean_object* v_start_2956_){
_start:
{
lean_object* v___f_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; 
v___f_2957_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2957_, 0, v_f_2954_);
v___x_2958_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_2959_ = l_Lean_LocalContext_foldlM___redArg(v___x_2958_, v_lctx_2953_, v___f_2957_, v_init_2955_, v_start_2956_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___boxed(lean_object* v_00_u03b2_2960_, lean_object* v_lctx_2961_, lean_object* v_f_2962_, lean_object* v_init_2963_, lean_object* v_start_2964_){
_start:
{
lean_object* v_res_2965_; 
v_res_2965_ = l_Lean_LocalContext_foldl(v_00_u03b2_2960_, v_lctx_2961_, v_f_2962_, v_init_2963_, v_start_2964_);
lean_dec(v_start_2964_);
return v_res_2965_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr___redArg___lam__0(lean_object* v_f_2966_, lean_object* v_x1_2967_, lean_object* v_x2_2968_){
_start:
{
lean_object* v___x_2969_; 
v___x_2969_ = lean_apply_2(v_f_2966_, v_x1_2967_, v_x2_2968_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr___redArg(lean_object* v_lctx_2970_, lean_object* v_f_2971_, lean_object* v_init_2972_){
_start:
{
lean_object* v___f_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v___f_2973_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2973_, 0, v_f_2971_);
v___x_2974_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_2975_ = l_Lean_LocalContext_foldrM___redArg(v___x_2974_, v_lctx_2970_, v___f_2973_, v_init_2972_);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr(lean_object* v_00_u03b2_2976_, lean_object* v_lctx_2977_, lean_object* v_f_2978_, lean_object* v_init_2979_){
_start:
{
lean_object* v___f_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
v___f_2980_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2980_, 0, v_f_2978_);
v___x_2981_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_2982_ = l_Lean_LocalContext_foldrM___redArg(v___x_2981_, v_lctx_2977_, v___f_2980_, v_init_2979_);
return v___x_2982_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(lean_object* v_as_2983_, size_t v_i_2984_, size_t v_stop_2985_, lean_object* v_b_2986_){
_start:
{
lean_object* v___y_2988_; uint8_t v___x_2992_; 
v___x_2992_ = lean_usize_dec_eq(v_i_2984_, v_stop_2985_);
if (v___x_2992_ == 0)
{
lean_object* v___x_2993_; 
v___x_2993_ = lean_array_uget_borrowed(v_as_2983_, v_i_2984_);
if (lean_obj_tag(v___x_2993_) == 0)
{
v___y_2988_ = v_b_2986_;
goto v___jp_2987_;
}
else
{
lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2994_ = lean_unsigned_to_nat(1u);
v___x_2995_ = lean_nat_add(v_b_2986_, v___x_2994_);
lean_dec(v_b_2986_);
v___y_2988_ = v___x_2995_;
goto v___jp_2987_;
}
}
else
{
return v_b_2986_;
}
v___jp_2987_:
{
size_t v___x_2989_; size_t v___x_2990_; 
v___x_2989_ = ((size_t)1ULL);
v___x_2990_ = lean_usize_add(v_i_2984_, v___x_2989_);
v_i_2984_ = v___x_2990_;
v_b_2986_ = v___y_2988_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2___boxed(lean_object* v_as_2996_, lean_object* v_i_2997_, lean_object* v_stop_2998_, lean_object* v_b_2999_){
_start:
{
size_t v_i_boxed_3000_; size_t v_stop_boxed_3001_; lean_object* v_res_3002_; 
v_i_boxed_3000_ = lean_unbox_usize(v_i_2997_);
lean_dec(v_i_2997_);
v_stop_boxed_3001_ = lean_unbox_usize(v_stop_2998_);
lean_dec(v_stop_2998_);
v_res_3002_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_as_2996_, v_i_boxed_3000_, v_stop_boxed_3001_, v_b_2999_);
lean_dec_ref(v_as_2996_);
return v_res_3002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(lean_object* v_x_3003_, lean_object* v_x_3004_){
_start:
{
if (lean_obj_tag(v_x_3003_) == 0)
{
lean_object* v_cs_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; uint8_t v___x_3008_; 
v_cs_3005_ = lean_ctor_get(v_x_3003_, 0);
v___x_3006_ = lean_unsigned_to_nat(0u);
v___x_3007_ = lean_array_get_size(v_cs_3005_);
v___x_3008_ = lean_nat_dec_lt(v___x_3006_, v___x_3007_);
if (v___x_3008_ == 0)
{
return v_x_3004_;
}
else
{
size_t v___x_3009_; size_t v___x_3010_; lean_object* v___x_3011_; 
v___x_3009_ = ((size_t)0ULL);
v___x_3010_ = lean_usize_of_nat(v___x_3007_);
v___x_3011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_cs_3005_, v___x_3009_, v___x_3010_, v_x_3004_);
return v___x_3011_;
}
}
else
{
lean_object* v_vs_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; uint8_t v___x_3015_; 
v_vs_3012_ = lean_ctor_get(v_x_3003_, 0);
v___x_3013_ = lean_unsigned_to_nat(0u);
v___x_3014_ = lean_array_get_size(v_vs_3012_);
v___x_3015_ = lean_nat_dec_lt(v___x_3013_, v___x_3014_);
if (v___x_3015_ == 0)
{
return v_x_3004_;
}
else
{
size_t v___x_3016_; size_t v___x_3017_; lean_object* v___x_3018_; 
v___x_3016_ = ((size_t)0ULL);
v___x_3017_ = lean_usize_of_nat(v___x_3014_);
v___x_3018_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_vs_3012_, v___x_3016_, v___x_3017_, v_x_3004_);
return v___x_3018_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(lean_object* v_as_3019_, size_t v_i_3020_, size_t v_stop_3021_, lean_object* v_b_3022_){
_start:
{
uint8_t v___x_3023_; 
v___x_3023_ = lean_usize_dec_eq(v_i_3020_, v_stop_3021_);
if (v___x_3023_ == 0)
{
lean_object* v___x_3024_; lean_object* v___x_3025_; size_t v___x_3026_; size_t v___x_3027_; 
v___x_3024_ = lean_array_uget_borrowed(v_as_3019_, v_i_3020_);
v___x_3025_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(v___x_3024_, v_b_3022_);
v___x_3026_ = ((size_t)1ULL);
v___x_3027_ = lean_usize_add(v_i_3020_, v___x_3026_);
v_i_3020_ = v___x_3027_;
v_b_3022_ = v___x_3025_;
goto _start;
}
else
{
return v_b_3022_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_as_3029_, lean_object* v_i_3030_, lean_object* v_stop_3031_, lean_object* v_b_3032_){
_start:
{
size_t v_i_boxed_3033_; size_t v_stop_boxed_3034_; lean_object* v_res_3035_; 
v_i_boxed_3033_ = lean_unbox_usize(v_i_3030_);
lean_dec(v_i_3030_);
v_stop_boxed_3034_ = lean_unbox_usize(v_stop_3031_);
lean_dec(v_stop_3031_);
v_res_3035_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_as_3029_, v_i_boxed_3033_, v_stop_boxed_3034_, v_b_3032_);
lean_dec_ref(v_as_3029_);
return v_res_3035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3___boxed(lean_object* v_x_3036_, lean_object* v_x_3037_){
_start:
{
lean_object* v_res_3038_; 
v_res_3038_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(v_x_3036_, v_x_3037_);
lean_dec_ref(v_x_3036_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(lean_object* v_x_3039_, size_t v_x_3040_, size_t v_x_3041_, lean_object* v_x_3042_){
_start:
{
if (lean_obj_tag(v_x_3039_) == 0)
{
lean_object* v_cs_3043_; lean_object* v___x_3044_; size_t v___x_3045_; lean_object* v_j_3046_; lean_object* v___x_3047_; size_t v___x_3048_; size_t v___x_3049_; size_t v___x_3050_; size_t v___x_3051_; size_t v___x_3052_; size_t v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; uint8_t v___x_3058_; 
v_cs_3043_ = lean_ctor_get(v_x_3039_, 0);
v___x_3044_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0);
v___x_3045_ = lean_usize_shift_right(v_x_3040_, v_x_3041_);
v_j_3046_ = lean_usize_to_nat(v___x_3045_);
v___x_3047_ = lean_array_get_borrowed(v___x_3044_, v_cs_3043_, v_j_3046_);
v___x_3048_ = ((size_t)1ULL);
v___x_3049_ = lean_usize_shift_left(v___x_3048_, v_x_3041_);
v___x_3050_ = lean_usize_sub(v___x_3049_, v___x_3048_);
v___x_3051_ = lean_usize_land(v_x_3040_, v___x_3050_);
v___x_3052_ = ((size_t)5ULL);
v___x_3053_ = lean_usize_sub(v_x_3041_, v___x_3052_);
v___x_3054_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(v___x_3047_, v___x_3051_, v___x_3053_, v_x_3042_);
v___x_3055_ = lean_unsigned_to_nat(1u);
v___x_3056_ = lean_nat_add(v_j_3046_, v___x_3055_);
lean_dec(v_j_3046_);
v___x_3057_ = lean_array_get_size(v_cs_3043_);
v___x_3058_ = lean_nat_dec_lt(v___x_3056_, v___x_3057_);
if (v___x_3058_ == 0)
{
lean_dec(v___x_3056_);
return v___x_3054_;
}
else
{
size_t v___x_3059_; size_t v___x_3060_; lean_object* v___x_3061_; 
v___x_3059_ = lean_usize_of_nat(v___x_3056_);
lean_dec(v___x_3056_);
v___x_3060_ = lean_usize_of_nat(v___x_3057_);
v___x_3061_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_cs_3043_, v___x_3059_, v___x_3060_, v___x_3054_);
return v___x_3061_;
}
}
else
{
lean_object* v_vs_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; uint8_t v___x_3065_; 
v_vs_3062_ = lean_ctor_get(v_x_3039_, 0);
v___x_3063_ = lean_usize_to_nat(v_x_3040_);
v___x_3064_ = lean_array_get_size(v_vs_3062_);
v___x_3065_ = lean_nat_dec_lt(v___x_3063_, v___x_3064_);
if (v___x_3065_ == 0)
{
lean_dec(v___x_3063_);
return v_x_3042_;
}
else
{
size_t v___x_3066_; size_t v___x_3067_; lean_object* v___x_3068_; 
v___x_3066_ = lean_usize_of_nat(v___x_3063_);
lean_dec(v___x_3063_);
v___x_3067_ = lean_usize_of_nat(v___x_3064_);
v___x_3068_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_vs_3062_, v___x_3066_, v___x_3067_, v_x_3042_);
return v___x_3068_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3069_, lean_object* v_x_3070_, lean_object* v_x_3071_, lean_object* v_x_3072_){
_start:
{
size_t v_x_1185__boxed_3073_; size_t v_x_1186__boxed_3074_; lean_object* v_res_3075_; 
v_x_1185__boxed_3073_ = lean_unbox_usize(v_x_3070_);
lean_dec(v_x_3070_);
v_x_1186__boxed_3074_ = lean_unbox_usize(v_x_3071_);
lean_dec(v_x_3071_);
v_res_3075_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(v_x_3069_, v_x_1185__boxed_3073_, v_x_1186__boxed_3074_, v_x_3072_);
lean_dec_ref(v_x_3069_);
return v_res_3075_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(lean_object* v_t_3076_, lean_object* v_init_3077_, lean_object* v_start_3078_){
_start:
{
lean_object* v___x_3079_; uint8_t v___x_3080_; 
v___x_3079_ = lean_unsigned_to_nat(0u);
v___x_3080_ = lean_nat_dec_eq(v_start_3078_, v___x_3079_);
if (v___x_3080_ == 0)
{
lean_object* v_root_3081_; lean_object* v_tail_3082_; size_t v_shift_3083_; lean_object* v_tailOff_3084_; uint8_t v___x_3085_; 
v_root_3081_ = lean_ctor_get(v_t_3076_, 0);
v_tail_3082_ = lean_ctor_get(v_t_3076_, 1);
v_shift_3083_ = lean_ctor_get_usize(v_t_3076_, 4);
v_tailOff_3084_ = lean_ctor_get(v_t_3076_, 3);
v___x_3085_ = lean_nat_dec_le(v_tailOff_3084_, v_start_3078_);
if (v___x_3085_ == 0)
{
size_t v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; uint8_t v___x_3089_; 
v___x_3086_ = lean_usize_of_nat(v_start_3078_);
v___x_3087_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(v_root_3081_, v___x_3086_, v_shift_3083_, v_init_3077_);
v___x_3088_ = lean_array_get_size(v_tail_3082_);
v___x_3089_ = lean_nat_dec_lt(v___x_3079_, v___x_3088_);
if (v___x_3089_ == 0)
{
return v___x_3087_;
}
else
{
size_t v___x_3090_; size_t v___x_3091_; lean_object* v___x_3092_; 
v___x_3090_ = ((size_t)0ULL);
v___x_3091_ = lean_usize_of_nat(v___x_3088_);
v___x_3092_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3082_, v___x_3090_, v___x_3091_, v___x_3087_);
return v___x_3092_;
}
}
else
{
lean_object* v___x_3093_; lean_object* v___x_3094_; uint8_t v___x_3095_; 
v___x_3093_ = lean_nat_sub(v_start_3078_, v_tailOff_3084_);
v___x_3094_ = lean_array_get_size(v_tail_3082_);
v___x_3095_ = lean_nat_dec_lt(v___x_3093_, v___x_3094_);
if (v___x_3095_ == 0)
{
lean_dec(v___x_3093_);
return v_init_3077_;
}
else
{
size_t v___x_3096_; size_t v___x_3097_; lean_object* v___x_3098_; 
v___x_3096_ = lean_usize_of_nat(v___x_3093_);
lean_dec(v___x_3093_);
v___x_3097_ = lean_usize_of_nat(v___x_3094_);
v___x_3098_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3082_, v___x_3096_, v___x_3097_, v_init_3077_);
return v___x_3098_;
}
}
}
else
{
lean_object* v_root_3099_; lean_object* v_tail_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; uint8_t v___x_3103_; 
v_root_3099_ = lean_ctor_get(v_t_3076_, 0);
v_tail_3100_ = lean_ctor_get(v_t_3076_, 1);
v___x_3101_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(v_root_3099_, v_init_3077_);
v___x_3102_ = lean_array_get_size(v_tail_3100_);
v___x_3103_ = lean_nat_dec_lt(v___x_3079_, v___x_3102_);
if (v___x_3103_ == 0)
{
return v___x_3101_;
}
else
{
size_t v___x_3104_; size_t v___x_3105_; lean_object* v___x_3106_; 
v___x_3104_ = ((size_t)0ULL);
v___x_3105_ = lean_usize_of_nat(v___x_3102_);
v___x_3106_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3100_, v___x_3104_, v___x_3105_, v___x_3101_);
return v___x_3106_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0___boxed(lean_object* v_t_3107_, lean_object* v_init_3108_, lean_object* v_start_3109_){
_start:
{
lean_object* v_res_3110_; 
v_res_3110_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(v_t_3107_, v_init_3108_, v_start_3109_);
lean_dec(v_start_3109_);
lean_dec_ref(v_t_3107_);
return v_res_3110_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(lean_object* v_lctx_3111_, lean_object* v_init_3112_, lean_object* v_start_3113_){
_start:
{
lean_object* v_decls_3114_; lean_object* v___x_3115_; 
v_decls_3114_ = lean_ctor_get(v_lctx_3111_, 1);
v___x_3115_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(v_decls_3114_, v_init_3112_, v_start_3113_);
return v___x_3115_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0___boxed(lean_object* v_lctx_3116_, lean_object* v_init_3117_, lean_object* v_start_3118_){
_start:
{
lean_object* v_res_3119_; 
v_res_3119_ = l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(v_lctx_3116_, v_init_3117_, v_start_3118_);
lean_dec(v_start_3118_);
lean_dec_ref(v_lctx_3116_);
return v_res_3119_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_size(lean_object* v_lctx_3120_){
_start:
{
lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3121_ = lean_unsigned_to_nat(0u);
v___x_3122_ = l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(v_lctx_3120_, v___x_3121_, v___x_3121_);
return v___x_3122_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_size___boxed(lean_object* v_lctx_3123_){
_start:
{
lean_object* v_res_3124_; 
v_res_3124_ = l_Lean_LocalContext_size(v_lctx_3123_);
lean_dec_ref(v_lctx_3123_);
return v_res_3124_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f___redArg___lam__0(lean_object* v_f_3125_, lean_object* v_x_3126_){
_start:
{
lean_object* v___x_3127_; 
v___x_3127_ = lean_apply_1(v_f_3125_, v_x_3126_);
return v___x_3127_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f___redArg(lean_object* v_lctx_3128_, lean_object* v_f_3129_){
_start:
{
lean_object* v___f_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___f_3130_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3130_, 0, v_f_3129_);
v___x_3131_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3132_ = l_Lean_LocalContext_findDeclM_x3f___redArg(v___x_3131_, v_lctx_3128_, v___f_3130_);
return v___x_3132_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f(lean_object* v_00_u03b2_3133_, lean_object* v_lctx_3134_, lean_object* v_f_3135_){
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
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRev_x3f___redArg(lean_object* v_lctx_3139_, lean_object* v_f_3140_){
_start:
{
lean_object* v___f_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; 
v___f_3141_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3141_, 0, v_f_3140_);
v___x_3142_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3143_ = l_Lean_LocalContext_findDeclRevM_x3f___redArg(v___x_3142_, v_lctx_3139_, v___f_3141_);
return v___x_3143_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRev_x3f(lean_object* v_00_u03b2_3144_, lean_object* v_lctx_3145_, lean_object* v_f_3146_){
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(lean_object* v_val_3150_, lean_object* v_as_3151_, size_t v_i_3152_, size_t v_stop_3153_){
_start:
{
uint8_t v___x_3154_; 
v___x_3154_ = lean_usize_dec_eq(v_i_3152_, v_stop_3153_);
if (v___x_3154_ == 0)
{
uint8_t v___x_3155_; uint8_t v___y_3157_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v_fvarId_3163_; uint8_t v___x_3164_; 
v___x_3155_ = 1;
v___x_3161_ = lean_array_uget_borrowed(v_as_3151_, v_i_3152_);
v___x_3162_ = l_Lean_Expr_fvarId_x21(v___x_3161_);
v_fvarId_3163_ = lean_ctor_get(v_val_3150_, 1);
v___x_3164_ = l_Lean_instBEqFVarId_beq(v___x_3162_, v_fvarId_3163_);
lean_dec(v___x_3162_);
v___y_3157_ = v___x_3164_;
goto v___jp_3156_;
v___jp_3156_:
{
if (v___y_3157_ == 0)
{
size_t v___x_3158_; size_t v___x_3159_; 
v___x_3158_ = ((size_t)1ULL);
v___x_3159_ = lean_usize_add(v_i_3152_, v___x_3158_);
v_i_3152_ = v___x_3159_;
goto _start;
}
else
{
return v___x_3155_;
}
}
}
else
{
uint8_t v___x_3165_; 
v___x_3165_ = 0;
return v___x_3165_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0___boxed(lean_object* v_val_3166_, lean_object* v_as_3167_, lean_object* v_i_3168_, lean_object* v_stop_3169_){
_start:
{
size_t v_i_boxed_3170_; size_t v_stop_boxed_3171_; uint8_t v_res_3172_; lean_object* v_r_3173_; 
v_i_boxed_3170_ = lean_unbox_usize(v_i_3168_);
lean_dec(v_i_3168_);
v_stop_boxed_3171_ = lean_unbox_usize(v_stop_3169_);
lean_dec(v_stop_3169_);
v_res_3172_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(v_val_3166_, v_as_3167_, v_i_boxed_3170_, v_stop_boxed_3171_);
lean_dec_ref(v_as_3167_);
lean_dec_ref(v_val_3166_);
v_r_3173_ = lean_box(v_res_3172_);
return v_r_3173_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_isSubPrefixOfAux(lean_object* v_a_u2081_3174_, lean_object* v_a_u2082_3175_, lean_object* v_exceptFVars_3176_, lean_object* v_i_3177_, lean_object* v_j_3178_){
_start:
{
lean_object* v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v_size_3194_; uint8_t v___x_3195_; 
v_size_3194_ = lean_ctor_get(v_a_u2081_3174_, 2);
v___x_3195_ = lean_nat_dec_lt(v_i_3177_, v_size_3194_);
if (v___x_3195_ == 0)
{
uint8_t v___x_3196_; 
lean_dec(v_j_3178_);
lean_dec(v_i_3177_);
v___x_3196_ = 1;
return v___x_3196_;
}
else
{
lean_object* v___x_3197_; lean_object* v___x_3198_; 
v___x_3197_ = lean_box(0);
v___x_3198_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3197_, v_a_u2081_3174_, v_i_3177_);
if (lean_obj_tag(v___x_3198_) == 0)
{
lean_object* v___x_3199_; lean_object* v___x_3200_; 
v___x_3199_ = lean_unsigned_to_nat(1u);
v___x_3200_ = lean_nat_add(v_i_3177_, v___x_3199_);
lean_dec(v_i_3177_);
v_i_3177_ = v___x_3200_;
goto _start;
}
else
{
lean_object* v_val_3202_; lean_object* v___x_3212_; lean_object* v___x_3213_; uint8_t v___x_3214_; 
v_val_3202_ = lean_ctor_get(v___x_3198_, 0);
lean_inc(v_val_3202_);
lean_dec_ref_known(v___x_3198_, 1);
v___x_3212_ = lean_unsigned_to_nat(0u);
v___x_3213_ = lean_array_get_size(v_exceptFVars_3176_);
v___x_3214_ = lean_nat_dec_lt(v___x_3212_, v___x_3213_);
if (v___x_3214_ == 0)
{
goto v___jp_3203_;
}
else
{
if (v___x_3214_ == 0)
{
goto v___jp_3203_;
}
else
{
size_t v___x_3215_; size_t v___x_3216_; uint8_t v___x_3217_; 
v___x_3215_ = ((size_t)0ULL);
v___x_3216_ = lean_usize_of_nat(v___x_3213_);
v___x_3217_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(v_val_3202_, v_exceptFVars_3176_, v___x_3215_, v___x_3216_);
if (v___x_3217_ == 0)
{
goto v___jp_3203_;
}
else
{
lean_object* v___x_3218_; lean_object* v___x_3219_; 
lean_dec(v_val_3202_);
v___x_3218_ = lean_unsigned_to_nat(1u);
v___x_3219_ = lean_nat_add(v_i_3177_, v___x_3218_);
lean_dec(v_i_3177_);
v_i_3177_ = v___x_3219_;
goto _start;
}
}
}
v___jp_3203_:
{
lean_object* v_size_3204_; uint8_t v___x_3205_; 
v_size_3204_ = lean_ctor_get(v_a_u2082_3175_, 2);
v___x_3205_ = lean_nat_dec_lt(v_j_3178_, v_size_3204_);
if (v___x_3205_ == 0)
{
lean_dec(v_val_3202_);
lean_dec(v_j_3178_);
lean_dec(v_i_3177_);
return v___x_3205_;
}
else
{
lean_object* v___x_3206_; 
v___x_3206_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3197_, v_a_u2082_3175_, v_j_3178_);
if (lean_obj_tag(v___x_3206_) == 0)
{
lean_object* v___x_3207_; lean_object* v___x_3208_; 
lean_dec(v_val_3202_);
v___x_3207_ = lean_unsigned_to_nat(1u);
v___x_3208_ = lean_nat_add(v_j_3178_, v___x_3207_);
lean_dec(v_j_3178_);
v_j_3178_ = v___x_3208_;
goto _start;
}
else
{
lean_object* v_val_3210_; lean_object* v_fvarId_3211_; 
v_val_3210_ = lean_ctor_get(v___x_3206_, 0);
lean_inc(v_val_3210_);
lean_dec_ref_known(v___x_3206_, 1);
v_fvarId_3211_ = lean_ctor_get(v_val_3202_, 1);
lean_inc(v_fvarId_3211_);
lean_dec(v_val_3202_);
v___y_3191_ = v_val_3210_;
v___y_3192_ = v_fvarId_3211_;
goto v___jp_3190_;
}
}
}
}
}
v___jp_3179_:
{
uint8_t v___x_3182_; 
v___x_3182_ = l_Lean_instBEqFVarId_beq(v___y_3180_, v___y_3181_);
lean_dec(v___y_3181_);
lean_dec(v___y_3180_);
if (v___x_3182_ == 0)
{
lean_object* v___x_3183_; lean_object* v___x_3184_; 
v___x_3183_ = lean_unsigned_to_nat(1u);
v___x_3184_ = lean_nat_add(v_j_3178_, v___x_3183_);
lean_dec(v_j_3178_);
v_j_3178_ = v___x_3184_;
goto _start;
}
else
{
lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3186_ = lean_unsigned_to_nat(1u);
v___x_3187_ = lean_nat_add(v_i_3177_, v___x_3186_);
lean_dec(v_i_3177_);
v___x_3188_ = lean_nat_add(v_j_3178_, v___x_3186_);
lean_dec(v_j_3178_);
v_i_3177_ = v___x_3187_;
v_j_3178_ = v___x_3188_;
goto _start;
}
}
v___jp_3190_:
{
lean_object* v_fvarId_3193_; 
v_fvarId_3193_ = lean_ctor_get(v___y_3191_, 1);
lean_inc(v_fvarId_3193_);
lean_dec_ref(v___y_3191_);
v___y_3180_ = v___y_3192_;
v___y_3181_ = v_fvarId_3193_;
goto v___jp_3179_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_isSubPrefixOfAux___boxed(lean_object* v_a_u2081_3221_, lean_object* v_a_u2082_3222_, lean_object* v_exceptFVars_3223_, lean_object* v_i_3224_, lean_object* v_j_3225_){
_start:
{
uint8_t v_res_3226_; lean_object* v_r_3227_; 
v_res_3226_ = l_Lean_LocalContext_isSubPrefixOfAux(v_a_u2081_3221_, v_a_u2082_3222_, v_exceptFVars_3223_, v_i_3224_, v_j_3225_);
lean_dec_ref(v_exceptFVars_3223_);
lean_dec_ref(v_a_u2082_3222_);
lean_dec_ref(v_a_u2081_3221_);
v_r_3227_ = lean_box(v_res_3226_);
return v_r_3227_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_isSubPrefixOf(lean_object* v_lctx_u2081_3228_, lean_object* v_lctx_u2082_3229_, lean_object* v_exceptFVars_3230_){
_start:
{
lean_object* v_decls_3231_; lean_object* v_decls_3232_; lean_object* v___x_3233_; uint8_t v___x_3234_; 
v_decls_3231_ = lean_ctor_get(v_lctx_u2081_3228_, 1);
v_decls_3232_ = lean_ctor_get(v_lctx_u2082_3229_, 1);
v___x_3233_ = lean_unsigned_to_nat(0u);
v___x_3234_ = l_Lean_LocalContext_isSubPrefixOfAux(v_decls_3231_, v_decls_3232_, v_exceptFVars_3230_, v___x_3233_, v___x_3233_);
return v___x_3234_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_isSubPrefixOf___boxed(lean_object* v_lctx_u2081_3235_, lean_object* v_lctx_u2082_3236_, lean_object* v_exceptFVars_3237_){
_start:
{
uint8_t v_res_3238_; lean_object* v_r_3239_; 
v_res_3238_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_u2081_3235_, v_lctx_u2082_3236_, v_exceptFVars_3237_);
lean_dec_ref(v_exceptFVars_3237_);
lean_dec_ref(v_lctx_u2082_3236_);
lean_dec_ref(v_lctx_u2081_3235_);
v_r_3239_ = lean_box(v_res_3238_);
return v_r_3239_;
}
}
static lean_object* _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; 
v___x_3241_ = ((lean_object*)(l_Lean_LocalContext_get_x21___closed__1));
v___x_3242_ = lean_unsigned_to_nat(14u);
v___x_3243_ = lean_unsigned_to_nat(576u);
v___x_3244_ = ((lean_object*)(l_Lean_LocalContext_mkBinding___lam__0___closed__0));
v___x_3245_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_3246_ = l_mkPanicMessageWithDecl(v___x_3245_, v___x_3244_, v___x_3243_, v___x_3242_, v___x_3241_);
return v___x_3246_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___lam__0(lean_object* v_xs_3247_, lean_object* v_lctx_3248_, lean_object* v___x_3249_, uint8_t v_isLambda_3250_, uint8_t v_usedLetOnly_3251_, uint8_t v_generalizeNondepLet_3252_, lean_object* v_i_3253_, lean_object* v_x_3254_, lean_object* v_b_3255_){
_start:
{
lean_object* v_n_3257_; lean_object* v_ty_3258_; uint8_t v_bi_3259_; lean_object* v_x_3263_; lean_object* v___x_3264_; 
v_x_3263_ = lean_array_fget_borrowed(v_xs_3247_, v_i_3253_);
v___x_3264_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3248_, v_x_3263_);
if (lean_obj_tag(v___x_3264_) == 0)
{
lean_object* v___x_3265_; lean_object* v___x_3266_; 
lean_dec_ref(v_b_3255_);
v___x_3265_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3266_ = l_panic___redArg(v___x_3249_, v___x_3265_);
return v___x_3266_;
}
else
{
lean_object* v_val_3267_; 
v_val_3267_ = lean_ctor_get(v___x_3264_, 0);
lean_inc(v_val_3267_);
lean_dec_ref_known(v___x_3264_, 1);
if (lean_obj_tag(v_val_3267_) == 0)
{
lean_object* v_userName_3268_; lean_object* v_type_3269_; uint8_t v_bi_3270_; 
v_userName_3268_ = lean_ctor_get(v_val_3267_, 2);
lean_inc(v_userName_3268_);
v_type_3269_ = lean_ctor_get(v_val_3267_, 3);
lean_inc_ref(v_type_3269_);
v_bi_3270_ = lean_ctor_get_uint8(v_val_3267_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3267_, 4);
v_n_3257_ = v_userName_3268_;
v_ty_3258_ = v_type_3269_;
v_bi_3259_ = v_bi_3270_;
goto v___jp_3256_;
}
else
{
lean_object* v_userName_3271_; lean_object* v_type_3272_; lean_object* v_value_3273_; uint8_t v_nondep_3274_; uint8_t v___y_3280_; 
v_userName_3271_ = lean_ctor_get(v_val_3267_, 2);
lean_inc(v_userName_3271_);
v_type_3272_ = lean_ctor_get(v_val_3267_, 3);
lean_inc_ref(v_type_3272_);
v_value_3273_ = lean_ctor_get(v_val_3267_, 4);
lean_inc_ref(v_value_3273_);
v_nondep_3274_ = lean_ctor_get_uint8(v_val_3267_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3267_, 5);
if (v_nondep_3274_ == 0)
{
v___y_3280_ = v_nondep_3274_;
goto v___jp_3279_;
}
else
{
if (v_generalizeNondepLet_3252_ == 0)
{
v___y_3280_ = v_generalizeNondepLet_3252_;
goto v___jp_3279_;
}
else
{
uint8_t v___x_3285_; 
lean_dec_ref(v_value_3273_);
v___x_3285_ = 0;
v_n_3257_ = v_userName_3271_;
v_ty_3258_ = v_type_3272_;
v_bi_3259_ = v___x_3285_;
goto v___jp_3256_;
}
}
v___jp_3275_:
{
lean_object* v_ty_3276_; lean_object* v_val_3277_; lean_object* v___x_3278_; 
v_ty_3276_ = lean_expr_abstract_range(v_type_3272_, v_i_3253_, v_xs_3247_);
lean_dec_ref(v_type_3272_);
v_val_3277_ = lean_expr_abstract_range(v_value_3273_, v_i_3253_, v_xs_3247_);
lean_dec_ref(v_value_3273_);
v___x_3278_ = l_Lean_Expr_letE___override(v_userName_3271_, v_ty_3276_, v_val_3277_, v_b_3255_, v_nondep_3274_);
return v___x_3278_;
}
v___jp_3279_:
{
if (v_usedLetOnly_3251_ == 0)
{
goto v___jp_3275_;
}
else
{
if (v___y_3280_ == 0)
{
lean_object* v___x_3281_; uint8_t v___x_3282_; 
v___x_3281_ = lean_unsigned_to_nat(0u);
v___x_3282_ = lean_expr_has_loose_bvar(v_b_3255_, v___x_3281_);
if (v___x_3282_ == 0)
{
lean_object* v___x_3283_; lean_object* v___x_3284_; 
lean_dec_ref(v_value_3273_);
lean_dec_ref(v_type_3272_);
lean_dec(v_userName_3271_);
v___x_3283_ = lean_unsigned_to_nat(1u);
v___x_3284_ = lean_expr_lower_loose_bvars(v_b_3255_, v___x_3283_, v___x_3283_);
lean_dec_ref(v_b_3255_);
return v___x_3284_;
}
else
{
goto v___jp_3275_;
}
}
else
{
goto v___jp_3275_;
}
}
}
}
}
v___jp_3256_:
{
lean_object* v_ty_3260_; 
v_ty_3260_ = lean_expr_abstract_range(v_ty_3258_, v_i_3253_, v_xs_3247_);
lean_dec_ref(v_ty_3258_);
if (v_isLambda_3250_ == 0)
{
lean_object* v___x_3261_; 
v___x_3261_ = l_Lean_mkForall(v_n_3257_, v_bi_3259_, v_ty_3260_, v_b_3255_);
return v___x_3261_;
}
else
{
lean_object* v___x_3262_; 
v___x_3262_ = l_Lean_mkLambda(v_n_3257_, v_bi_3259_, v_ty_3260_, v_b_3255_);
return v___x_3262_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___lam__0___boxed(lean_object* v_xs_3286_, lean_object* v_lctx_3287_, lean_object* v___x_3288_, lean_object* v_isLambda_3289_, lean_object* v_usedLetOnly_3290_, lean_object* v_generalizeNondepLet_3291_, lean_object* v_i_3292_, lean_object* v_x_3293_, lean_object* v_b_3294_){
_start:
{
uint8_t v_isLambda_boxed_3295_; uint8_t v_usedLetOnly_boxed_3296_; uint8_t v_generalizeNondepLet_boxed_3297_; lean_object* v_res_3298_; 
v_isLambda_boxed_3295_ = lean_unbox(v_isLambda_3289_);
v_usedLetOnly_boxed_3296_ = lean_unbox(v_usedLetOnly_3290_);
v_generalizeNondepLet_boxed_3297_ = lean_unbox(v_generalizeNondepLet_3291_);
v_res_3298_ = l_Lean_LocalContext_mkBinding___lam__0(v_xs_3286_, v_lctx_3287_, v___x_3288_, v_isLambda_boxed_3295_, v_usedLetOnly_boxed_3296_, v_generalizeNondepLet_boxed_3297_, v_i_3292_, v_x_3293_, v_b_3294_);
lean_dec(v_i_3292_);
lean_dec_ref(v___x_3288_);
lean_dec_ref(v_xs_3286_);
return v_res_3298_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding(uint8_t v_isLambda_3299_, lean_object* v_lctx_3300_, lean_object* v_xs_3301_, lean_object* v_b_3302_, uint8_t v_usedLetOnly_3303_, uint8_t v_generalizeNondepLet_3304_){
_start:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___f_3309_; lean_object* v_b_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
v___x_3305_ = l_Lean_instInhabitedExpr;
v___x_3306_ = lean_box(v_isLambda_3299_);
v___x_3307_ = lean_box(v_usedLetOnly_3303_);
v___x_3308_ = lean_box(v_generalizeNondepLet_3304_);
lean_inc_ref(v_xs_3301_);
v___f_3309_ = lean_alloc_closure((void*)(l_Lean_LocalContext_mkBinding___lam__0___boxed), 9, 6);
lean_closure_set(v___f_3309_, 0, v_xs_3301_);
lean_closure_set(v___f_3309_, 1, v_lctx_3300_);
lean_closure_set(v___f_3309_, 2, v___x_3305_);
lean_closure_set(v___f_3309_, 3, v___x_3306_);
lean_closure_set(v___f_3309_, 4, v___x_3307_);
lean_closure_set(v___f_3309_, 5, v___x_3308_);
v_b_3310_ = lean_expr_abstract(v_b_3302_, v_xs_3301_);
v___x_3311_ = lean_array_get_size(v_xs_3301_);
lean_dec_ref(v_xs_3301_);
v___x_3312_ = l_Nat_foldRev___redArg(v___x_3311_, v___f_3309_, v_b_3310_);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___boxed(lean_object* v_isLambda_3313_, lean_object* v_lctx_3314_, lean_object* v_xs_3315_, lean_object* v_b_3316_, lean_object* v_usedLetOnly_3317_, lean_object* v_generalizeNondepLet_3318_){
_start:
{
uint8_t v_isLambda_boxed_3319_; uint8_t v_usedLetOnly_boxed_3320_; uint8_t v_generalizeNondepLet_boxed_3321_; lean_object* v_res_3322_; 
v_isLambda_boxed_3319_ = lean_unbox(v_isLambda_3313_);
v_usedLetOnly_boxed_3320_ = lean_unbox(v_usedLetOnly_3317_);
v_generalizeNondepLet_boxed_3321_ = lean_unbox(v_generalizeNondepLet_3318_);
v_res_3322_ = l_Lean_LocalContext_mkBinding(v_isLambda_boxed_3319_, v_lctx_3314_, v_xs_3315_, v_b_3316_, v_usedLetOnly_boxed_3320_, v_generalizeNondepLet_boxed_3321_);
lean_dec_ref(v_b_3316_);
return v_res_3322_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(lean_object* v_xs_3323_, lean_object* v_lctx_3324_, uint8_t v_usedLetOnly_3325_, uint8_t v_generalizeNondepLet_3326_, lean_object* v_x_3327_, lean_object* v_x_3328_){
_start:
{
lean_object* v_zero_3329_; uint8_t v_isZero_3330_; 
v_zero_3329_ = lean_unsigned_to_nat(0u);
v_isZero_3330_ = lean_nat_dec_eq(v_x_3327_, v_zero_3329_);
if (v_isZero_3330_ == 1)
{
lean_dec(v_x_3327_);
lean_dec_ref(v_lctx_3324_);
return v_x_3328_;
}
else
{
lean_object* v_one_3331_; lean_object* v_n_3332_; lean_object* v_n_3334_; lean_object* v_ty_3335_; uint8_t v_bi_3336_; lean_object* v_x_3340_; lean_object* v___x_3341_; 
v_one_3331_ = lean_unsigned_to_nat(1u);
v_n_3332_ = lean_nat_sub(v_x_3327_, v_one_3331_);
lean_dec(v_x_3327_);
v_x_3340_ = lean_array_fget_borrowed(v_xs_3323_, v_n_3332_);
lean_inc_ref(v_lctx_3324_);
v___x_3341_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3324_, v_x_3340_);
if (lean_obj_tag(v___x_3341_) == 0)
{
lean_object* v___x_3342_; lean_object* v___x_3343_; 
lean_dec_ref(v_x_3328_);
v___x_3342_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3343_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3342_);
v_x_3327_ = v_n_3332_;
v_x_3328_ = v___x_3343_;
goto _start;
}
else
{
lean_object* v_val_3345_; 
v_val_3345_ = lean_ctor_get(v___x_3341_, 0);
lean_inc(v_val_3345_);
lean_dec_ref_known(v___x_3341_, 1);
if (lean_obj_tag(v_val_3345_) == 0)
{
lean_object* v_userName_3346_; lean_object* v_type_3347_; uint8_t v_bi_3348_; 
v_userName_3346_ = lean_ctor_get(v_val_3345_, 2);
lean_inc(v_userName_3346_);
v_type_3347_ = lean_ctor_get(v_val_3345_, 3);
lean_inc_ref(v_type_3347_);
v_bi_3348_ = lean_ctor_get_uint8(v_val_3345_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3345_, 4);
v_n_3334_ = v_userName_3346_;
v_ty_3335_ = v_type_3347_;
v_bi_3336_ = v_bi_3348_;
goto v___jp_3333_;
}
else
{
lean_object* v_userName_3349_; lean_object* v_type_3350_; lean_object* v_value_3351_; uint8_t v_nondep_3352_; uint8_t v___y_3359_; 
v_userName_3349_ = lean_ctor_get(v_val_3345_, 2);
lean_inc(v_userName_3349_);
v_type_3350_ = lean_ctor_get(v_val_3345_, 3);
lean_inc_ref(v_type_3350_);
v_value_3351_ = lean_ctor_get(v_val_3345_, 4);
lean_inc_ref(v_value_3351_);
v_nondep_3352_ = lean_ctor_get_uint8(v_val_3345_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3345_, 5);
if (v_nondep_3352_ == 0)
{
v___y_3359_ = v_nondep_3352_;
goto v___jp_3358_;
}
else
{
if (v_generalizeNondepLet_3326_ == 0)
{
v___y_3359_ = v_generalizeNondepLet_3326_;
goto v___jp_3358_;
}
else
{
uint8_t v___x_3363_; 
lean_dec_ref(v_value_3351_);
v___x_3363_ = 0;
v_n_3334_ = v_userName_3349_;
v_ty_3335_ = v_type_3350_;
v_bi_3336_ = v___x_3363_;
goto v___jp_3333_;
}
}
v___jp_3353_:
{
lean_object* v_ty_3354_; lean_object* v_val_3355_; lean_object* v___x_3356_; 
v_ty_3354_ = lean_expr_abstract_range(v_type_3350_, v_n_3332_, v_xs_3323_);
lean_dec_ref(v_type_3350_);
v_val_3355_ = lean_expr_abstract_range(v_value_3351_, v_n_3332_, v_xs_3323_);
lean_dec_ref(v_value_3351_);
v___x_3356_ = l_Lean_Expr_letE___override(v_userName_3349_, v_ty_3354_, v_val_3355_, v_x_3328_, v_nondep_3352_);
v_x_3327_ = v_n_3332_;
v_x_3328_ = v___x_3356_;
goto _start;
}
v___jp_3358_:
{
if (v_usedLetOnly_3325_ == 0)
{
goto v___jp_3353_;
}
else
{
if (v___y_3359_ == 0)
{
uint8_t v___x_3360_; 
v___x_3360_ = lean_expr_has_loose_bvar(v_x_3328_, v_zero_3329_);
if (v___x_3360_ == 0)
{
lean_object* v___x_3361_; 
lean_dec_ref(v_value_3351_);
lean_dec_ref(v_type_3350_);
lean_dec(v_userName_3349_);
v___x_3361_ = lean_expr_lower_loose_bvars(v_x_3328_, v_one_3331_, v_one_3331_);
lean_dec_ref(v_x_3328_);
v_x_3327_ = v_n_3332_;
v_x_3328_ = v___x_3361_;
goto _start;
}
else
{
goto v___jp_3353_;
}
}
else
{
goto v___jp_3353_;
}
}
}
}
}
v___jp_3333_:
{
lean_object* v_ty_3337_; lean_object* v___x_3338_; 
v_ty_3337_ = lean_expr_abstract_range(v_ty_3335_, v_n_3332_, v_xs_3323_);
lean_dec_ref(v_ty_3335_);
v___x_3338_ = l_Lean_mkLambda(v_n_3334_, v_bi_3336_, v_ty_3337_, v_x_3328_);
v_x_3327_ = v_n_3332_;
v_x_3328_ = v___x_3338_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0___boxed(lean_object* v_xs_3364_, lean_object* v_lctx_3365_, lean_object* v_usedLetOnly_3366_, lean_object* v_generalizeNondepLet_3367_, lean_object* v_x_3368_, lean_object* v_x_3369_){
_start:
{
uint8_t v_usedLetOnly_boxed_3370_; uint8_t v_generalizeNondepLet_boxed_3371_; lean_object* v_res_3372_; 
v_usedLetOnly_boxed_3370_ = lean_unbox(v_usedLetOnly_3366_);
v_generalizeNondepLet_boxed_3371_ = lean_unbox(v_generalizeNondepLet_3367_);
v_res_3372_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3364_, v_lctx_3365_, v_usedLetOnly_boxed_3370_, v_generalizeNondepLet_boxed_3371_, v_x_3368_, v_x_3369_);
lean_dec_ref(v_xs_3364_);
return v_res_3372_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(lean_object* v_xs_3373_, lean_object* v_lctx_3374_, uint8_t v_usedLetOnly_3375_, uint8_t v_generalizeNondepLet_3376_, lean_object* v_x_3377_, lean_object* v_x_3378_){
_start:
{
lean_object* v_zero_3379_; uint8_t v_isZero_3380_; 
v_zero_3379_ = lean_unsigned_to_nat(0u);
v_isZero_3380_ = lean_nat_dec_eq(v_x_3377_, v_zero_3379_);
if (v_isZero_3380_ == 1)
{
lean_dec_ref(v_lctx_3374_);
return v_x_3378_;
}
else
{
lean_object* v_one_3381_; lean_object* v_n_3382_; lean_object* v_n_3384_; lean_object* v_ty_3385_; uint8_t v_bi_3386_; lean_object* v_x_3390_; lean_object* v___x_3391_; 
v_one_3381_ = lean_unsigned_to_nat(1u);
v_n_3382_ = lean_nat_sub(v_x_3377_, v_one_3381_);
v_x_3390_ = lean_array_fget_borrowed(v_xs_3373_, v_n_3382_);
lean_inc_ref(v_lctx_3374_);
v___x_3391_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3374_, v_x_3390_);
if (lean_obj_tag(v___x_3391_) == 0)
{
lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; 
lean_dec_ref(v_x_3378_);
v___x_3392_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3393_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3392_);
v___x_3394_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3373_, v_lctx_3374_, v_usedLetOnly_3375_, v_generalizeNondepLet_3376_, v_n_3382_, v___x_3393_);
return v___x_3394_;
}
else
{
lean_object* v_val_3395_; 
v_val_3395_ = lean_ctor_get(v___x_3391_, 0);
lean_inc(v_val_3395_);
lean_dec_ref_known(v___x_3391_, 1);
if (lean_obj_tag(v_val_3395_) == 0)
{
lean_object* v_userName_3396_; lean_object* v_type_3397_; uint8_t v_bi_3398_; 
v_userName_3396_ = lean_ctor_get(v_val_3395_, 2);
lean_inc(v_userName_3396_);
v_type_3397_ = lean_ctor_get(v_val_3395_, 3);
lean_inc_ref(v_type_3397_);
v_bi_3398_ = lean_ctor_get_uint8(v_val_3395_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3395_, 4);
v_n_3384_ = v_userName_3396_;
v_ty_3385_ = v_type_3397_;
v_bi_3386_ = v_bi_3398_;
goto v___jp_3383_;
}
else
{
lean_object* v_userName_3399_; lean_object* v_type_3400_; lean_object* v_value_3401_; uint8_t v_nondep_3402_; uint8_t v___y_3409_; 
v_userName_3399_ = lean_ctor_get(v_val_3395_, 2);
lean_inc(v_userName_3399_);
v_type_3400_ = lean_ctor_get(v_val_3395_, 3);
lean_inc_ref(v_type_3400_);
v_value_3401_ = lean_ctor_get(v_val_3395_, 4);
lean_inc_ref(v_value_3401_);
v_nondep_3402_ = lean_ctor_get_uint8(v_val_3395_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3395_, 5);
if (v_nondep_3402_ == 0)
{
v___y_3409_ = v_nondep_3402_;
goto v___jp_3408_;
}
else
{
if (v_generalizeNondepLet_3376_ == 0)
{
v___y_3409_ = v_generalizeNondepLet_3376_;
goto v___jp_3408_;
}
else
{
uint8_t v___x_3413_; 
lean_dec_ref(v_value_3401_);
v___x_3413_ = 0;
v_n_3384_ = v_userName_3399_;
v_ty_3385_ = v_type_3400_;
v_bi_3386_ = v___x_3413_;
goto v___jp_3383_;
}
}
v___jp_3403_:
{
lean_object* v_ty_3404_; lean_object* v_val_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; 
v_ty_3404_ = lean_expr_abstract_range(v_type_3400_, v_n_3382_, v_xs_3373_);
lean_dec_ref(v_type_3400_);
v_val_3405_ = lean_expr_abstract_range(v_value_3401_, v_n_3382_, v_xs_3373_);
lean_dec_ref(v_value_3401_);
v___x_3406_ = l_Lean_Expr_letE___override(v_userName_3399_, v_ty_3404_, v_val_3405_, v_x_3378_, v_nondep_3402_);
v___x_3407_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3373_, v_lctx_3374_, v_usedLetOnly_3375_, v_generalizeNondepLet_3376_, v_n_3382_, v___x_3406_);
return v___x_3407_;
}
v___jp_3408_:
{
if (v_usedLetOnly_3375_ == 0)
{
goto v___jp_3403_;
}
else
{
if (v___y_3409_ == 0)
{
uint8_t v___x_3410_; 
v___x_3410_ = lean_expr_has_loose_bvar(v_x_3378_, v_zero_3379_);
if (v___x_3410_ == 0)
{
lean_object* v___x_3411_; lean_object* v___x_3412_; 
lean_dec_ref(v_value_3401_);
lean_dec_ref(v_type_3400_);
lean_dec(v_userName_3399_);
v___x_3411_ = lean_expr_lower_loose_bvars(v_x_3378_, v_one_3381_, v_one_3381_);
lean_dec_ref(v_x_3378_);
v___x_3412_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3373_, v_lctx_3374_, v_usedLetOnly_3375_, v_generalizeNondepLet_3376_, v_n_3382_, v___x_3411_);
return v___x_3412_;
}
else
{
goto v___jp_3403_;
}
}
else
{
goto v___jp_3403_;
}
}
}
}
}
v___jp_3383_:
{
lean_object* v_ty_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
v_ty_3387_ = lean_expr_abstract_range(v_ty_3385_, v_n_3382_, v_xs_3373_);
lean_dec_ref(v_ty_3385_);
v___x_3388_ = l_Lean_mkLambda(v_n_3384_, v_bi_3386_, v_ty_3387_, v_x_3378_);
v___x_3389_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3373_, v_lctx_3374_, v_usedLetOnly_3375_, v_generalizeNondepLet_3376_, v_n_3382_, v___x_3388_);
return v___x_3389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0___boxed(lean_object* v_xs_3414_, lean_object* v_lctx_3415_, lean_object* v_usedLetOnly_3416_, lean_object* v_generalizeNondepLet_3417_, lean_object* v_x_3418_, lean_object* v_x_3419_){
_start:
{
uint8_t v_usedLetOnly_boxed_3420_; uint8_t v_generalizeNondepLet_boxed_3421_; lean_object* v_res_3422_; 
v_usedLetOnly_boxed_3420_ = lean_unbox(v_usedLetOnly_3416_);
v_generalizeNondepLet_boxed_3421_ = lean_unbox(v_generalizeNondepLet_3417_);
v_res_3422_ = l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(v_xs_3414_, v_lctx_3415_, v_usedLetOnly_boxed_3420_, v_generalizeNondepLet_boxed_3421_, v_x_3418_, v_x_3419_);
lean_dec(v_x_3418_);
lean_dec_ref(v_xs_3414_);
return v_res_3422_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLambda(lean_object* v_lctx_3423_, lean_object* v_xs_3424_, lean_object* v_b_3425_, uint8_t v_usedLetOnly_3426_, uint8_t v_generalizeNondepLet_3427_){
_start:
{
lean_object* v_b_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; 
v_b_3428_ = lean_expr_abstract(v_b_3425_, v_xs_3424_);
v___x_3429_ = lean_array_get_size(v_xs_3424_);
v___x_3430_ = l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(v_xs_3424_, v_lctx_3423_, v_usedLetOnly_3426_, v_generalizeNondepLet_3427_, v___x_3429_, v_b_3428_);
return v___x_3430_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLambda___boxed(lean_object* v_lctx_3431_, lean_object* v_xs_3432_, lean_object* v_b_3433_, lean_object* v_usedLetOnly_3434_, lean_object* v_generalizeNondepLet_3435_){
_start:
{
uint8_t v_usedLetOnly_boxed_3436_; uint8_t v_generalizeNondepLet_boxed_3437_; lean_object* v_res_3438_; 
v_usedLetOnly_boxed_3436_ = lean_unbox(v_usedLetOnly_3434_);
v_generalizeNondepLet_boxed_3437_ = lean_unbox(v_generalizeNondepLet_3435_);
v_res_3438_ = l_Lean_LocalContext_mkLambda(v_lctx_3431_, v_xs_3432_, v_b_3433_, v_usedLetOnly_boxed_3436_, v_generalizeNondepLet_boxed_3437_);
lean_dec_ref(v_b_3433_);
lean_dec_ref(v_xs_3432_);
return v_res_3438_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(lean_object* v_xs_3439_, lean_object* v_lctx_3440_, uint8_t v_usedLetOnly_3441_, uint8_t v_generalizeNondepLet_3442_, lean_object* v_x_3443_, lean_object* v_x_3444_){
_start:
{
lean_object* v_zero_3445_; uint8_t v_isZero_3446_; 
v_zero_3445_ = lean_unsigned_to_nat(0u);
v_isZero_3446_ = lean_nat_dec_eq(v_x_3443_, v_zero_3445_);
if (v_isZero_3446_ == 1)
{
lean_dec(v_x_3443_);
lean_dec_ref(v_lctx_3440_);
return v_x_3444_;
}
else
{
lean_object* v_one_3447_; lean_object* v_n_3448_; lean_object* v_n_3450_; lean_object* v_ty_3451_; uint8_t v_bi_3452_; lean_object* v_x_3456_; lean_object* v___x_3457_; 
v_one_3447_ = lean_unsigned_to_nat(1u);
v_n_3448_ = lean_nat_sub(v_x_3443_, v_one_3447_);
lean_dec(v_x_3443_);
v_x_3456_ = lean_array_fget_borrowed(v_xs_3439_, v_n_3448_);
lean_inc_ref(v_lctx_3440_);
v___x_3457_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3440_, v_x_3456_);
if (lean_obj_tag(v___x_3457_) == 0)
{
lean_object* v___x_3458_; lean_object* v___x_3459_; 
lean_dec_ref(v_x_3444_);
v___x_3458_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3459_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3458_);
v_x_3443_ = v_n_3448_;
v_x_3444_ = v___x_3459_;
goto _start;
}
else
{
lean_object* v_val_3461_; 
v_val_3461_ = lean_ctor_get(v___x_3457_, 0);
lean_inc(v_val_3461_);
lean_dec_ref_known(v___x_3457_, 1);
if (lean_obj_tag(v_val_3461_) == 0)
{
lean_object* v_userName_3462_; lean_object* v_type_3463_; uint8_t v_bi_3464_; 
v_userName_3462_ = lean_ctor_get(v_val_3461_, 2);
lean_inc(v_userName_3462_);
v_type_3463_ = lean_ctor_get(v_val_3461_, 3);
lean_inc_ref(v_type_3463_);
v_bi_3464_ = lean_ctor_get_uint8(v_val_3461_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3461_, 4);
v_n_3450_ = v_userName_3462_;
v_ty_3451_ = v_type_3463_;
v_bi_3452_ = v_bi_3464_;
goto v___jp_3449_;
}
else
{
lean_object* v_userName_3465_; lean_object* v_type_3466_; lean_object* v_value_3467_; uint8_t v_nondep_3468_; uint8_t v___y_3475_; 
v_userName_3465_ = lean_ctor_get(v_val_3461_, 2);
lean_inc(v_userName_3465_);
v_type_3466_ = lean_ctor_get(v_val_3461_, 3);
lean_inc_ref(v_type_3466_);
v_value_3467_ = lean_ctor_get(v_val_3461_, 4);
lean_inc_ref(v_value_3467_);
v_nondep_3468_ = lean_ctor_get_uint8(v_val_3461_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3461_, 5);
if (v_nondep_3468_ == 0)
{
v___y_3475_ = v_nondep_3468_;
goto v___jp_3474_;
}
else
{
if (v_generalizeNondepLet_3442_ == 0)
{
v___y_3475_ = v_generalizeNondepLet_3442_;
goto v___jp_3474_;
}
else
{
uint8_t v___x_3479_; 
lean_dec_ref(v_value_3467_);
v___x_3479_ = 0;
v_n_3450_ = v_userName_3465_;
v_ty_3451_ = v_type_3466_;
v_bi_3452_ = v___x_3479_;
goto v___jp_3449_;
}
}
v___jp_3469_:
{
lean_object* v_ty_3470_; lean_object* v_val_3471_; lean_object* v___x_3472_; 
v_ty_3470_ = lean_expr_abstract_range(v_type_3466_, v_n_3448_, v_xs_3439_);
lean_dec_ref(v_type_3466_);
v_val_3471_ = lean_expr_abstract_range(v_value_3467_, v_n_3448_, v_xs_3439_);
lean_dec_ref(v_value_3467_);
v___x_3472_ = l_Lean_Expr_letE___override(v_userName_3465_, v_ty_3470_, v_val_3471_, v_x_3444_, v_nondep_3468_);
v_x_3443_ = v_n_3448_;
v_x_3444_ = v___x_3472_;
goto _start;
}
v___jp_3474_:
{
if (v_usedLetOnly_3441_ == 0)
{
goto v___jp_3469_;
}
else
{
if (v___y_3475_ == 0)
{
uint8_t v___x_3476_; 
v___x_3476_ = lean_expr_has_loose_bvar(v_x_3444_, v_zero_3445_);
if (v___x_3476_ == 0)
{
lean_object* v___x_3477_; 
lean_dec_ref(v_value_3467_);
lean_dec_ref(v_type_3466_);
lean_dec(v_userName_3465_);
v___x_3477_ = lean_expr_lower_loose_bvars(v_x_3444_, v_one_3447_, v_one_3447_);
lean_dec_ref(v_x_3444_);
v_x_3443_ = v_n_3448_;
v_x_3444_ = v___x_3477_;
goto _start;
}
else
{
goto v___jp_3469_;
}
}
else
{
goto v___jp_3469_;
}
}
}
}
}
v___jp_3449_:
{
lean_object* v_ty_3453_; lean_object* v___x_3454_; 
v_ty_3453_ = lean_expr_abstract_range(v_ty_3451_, v_n_3448_, v_xs_3439_);
lean_dec_ref(v_ty_3451_);
v___x_3454_ = l_Lean_mkForall(v_n_3450_, v_bi_3452_, v_ty_3453_, v_x_3444_);
v_x_3443_ = v_n_3448_;
v_x_3444_ = v___x_3454_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0___boxed(lean_object* v_xs_3480_, lean_object* v_lctx_3481_, lean_object* v_usedLetOnly_3482_, lean_object* v_generalizeNondepLet_3483_, lean_object* v_x_3484_, lean_object* v_x_3485_){
_start:
{
uint8_t v_usedLetOnly_boxed_3486_; uint8_t v_generalizeNondepLet_boxed_3487_; lean_object* v_res_3488_; 
v_usedLetOnly_boxed_3486_ = lean_unbox(v_usedLetOnly_3482_);
v_generalizeNondepLet_boxed_3487_ = lean_unbox(v_generalizeNondepLet_3483_);
v_res_3488_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3480_, v_lctx_3481_, v_usedLetOnly_boxed_3486_, v_generalizeNondepLet_boxed_3487_, v_x_3484_, v_x_3485_);
lean_dec_ref(v_xs_3480_);
return v_res_3488_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(lean_object* v_xs_3489_, lean_object* v_lctx_3490_, uint8_t v_usedLetOnly_3491_, uint8_t v_generalizeNondepLet_3492_, lean_object* v_x_3493_, lean_object* v_x_3494_){
_start:
{
lean_object* v_zero_3495_; uint8_t v_isZero_3496_; 
v_zero_3495_ = lean_unsigned_to_nat(0u);
v_isZero_3496_ = lean_nat_dec_eq(v_x_3493_, v_zero_3495_);
if (v_isZero_3496_ == 1)
{
lean_dec_ref(v_lctx_3490_);
return v_x_3494_;
}
else
{
lean_object* v_one_3497_; lean_object* v_n_3498_; lean_object* v_n_3500_; lean_object* v_ty_3501_; uint8_t v_bi_3502_; lean_object* v_x_3506_; lean_object* v___x_3507_; 
v_one_3497_ = lean_unsigned_to_nat(1u);
v_n_3498_ = lean_nat_sub(v_x_3493_, v_one_3497_);
v_x_3506_ = lean_array_fget_borrowed(v_xs_3489_, v_n_3498_);
lean_inc_ref(v_lctx_3490_);
v___x_3507_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3490_, v_x_3506_);
if (lean_obj_tag(v___x_3507_) == 0)
{
lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; 
lean_dec_ref(v_x_3494_);
v___x_3508_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3509_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3508_);
v___x_3510_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3489_, v_lctx_3490_, v_usedLetOnly_3491_, v_generalizeNondepLet_3492_, v_n_3498_, v___x_3509_);
return v___x_3510_;
}
else
{
lean_object* v_val_3511_; 
v_val_3511_ = lean_ctor_get(v___x_3507_, 0);
lean_inc(v_val_3511_);
lean_dec_ref_known(v___x_3507_, 1);
if (lean_obj_tag(v_val_3511_) == 0)
{
lean_object* v_userName_3512_; lean_object* v_type_3513_; uint8_t v_bi_3514_; 
v_userName_3512_ = lean_ctor_get(v_val_3511_, 2);
lean_inc(v_userName_3512_);
v_type_3513_ = lean_ctor_get(v_val_3511_, 3);
lean_inc_ref(v_type_3513_);
v_bi_3514_ = lean_ctor_get_uint8(v_val_3511_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3511_, 4);
v_n_3500_ = v_userName_3512_;
v_ty_3501_ = v_type_3513_;
v_bi_3502_ = v_bi_3514_;
goto v___jp_3499_;
}
else
{
lean_object* v_userName_3515_; lean_object* v_type_3516_; lean_object* v_value_3517_; uint8_t v_nondep_3518_; uint8_t v___y_3525_; 
v_userName_3515_ = lean_ctor_get(v_val_3511_, 2);
lean_inc(v_userName_3515_);
v_type_3516_ = lean_ctor_get(v_val_3511_, 3);
lean_inc_ref(v_type_3516_);
v_value_3517_ = lean_ctor_get(v_val_3511_, 4);
lean_inc_ref(v_value_3517_);
v_nondep_3518_ = lean_ctor_get_uint8(v_val_3511_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3511_, 5);
if (v_nondep_3518_ == 0)
{
v___y_3525_ = v_nondep_3518_;
goto v___jp_3524_;
}
else
{
if (v_generalizeNondepLet_3492_ == 0)
{
v___y_3525_ = v_generalizeNondepLet_3492_;
goto v___jp_3524_;
}
else
{
uint8_t v___x_3529_; 
lean_dec_ref(v_value_3517_);
v___x_3529_ = 0;
v_n_3500_ = v_userName_3515_;
v_ty_3501_ = v_type_3516_;
v_bi_3502_ = v___x_3529_;
goto v___jp_3499_;
}
}
v___jp_3519_:
{
lean_object* v_ty_3520_; lean_object* v_val_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; 
v_ty_3520_ = lean_expr_abstract_range(v_type_3516_, v_n_3498_, v_xs_3489_);
lean_dec_ref(v_type_3516_);
v_val_3521_ = lean_expr_abstract_range(v_value_3517_, v_n_3498_, v_xs_3489_);
lean_dec_ref(v_value_3517_);
v___x_3522_ = l_Lean_Expr_letE___override(v_userName_3515_, v_ty_3520_, v_val_3521_, v_x_3494_, v_nondep_3518_);
v___x_3523_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3489_, v_lctx_3490_, v_usedLetOnly_3491_, v_generalizeNondepLet_3492_, v_n_3498_, v___x_3522_);
return v___x_3523_;
}
v___jp_3524_:
{
if (v_usedLetOnly_3491_ == 0)
{
goto v___jp_3519_;
}
else
{
if (v___y_3525_ == 0)
{
uint8_t v___x_3526_; 
v___x_3526_ = lean_expr_has_loose_bvar(v_x_3494_, v_zero_3495_);
if (v___x_3526_ == 0)
{
lean_object* v___x_3527_; lean_object* v___x_3528_; 
lean_dec_ref(v_value_3517_);
lean_dec_ref(v_type_3516_);
lean_dec(v_userName_3515_);
v___x_3527_ = lean_expr_lower_loose_bvars(v_x_3494_, v_one_3497_, v_one_3497_);
lean_dec_ref(v_x_3494_);
v___x_3528_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3489_, v_lctx_3490_, v_usedLetOnly_3491_, v_generalizeNondepLet_3492_, v_n_3498_, v___x_3527_);
return v___x_3528_;
}
else
{
goto v___jp_3519_;
}
}
else
{
goto v___jp_3519_;
}
}
}
}
}
v___jp_3499_:
{
lean_object* v_ty_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; 
v_ty_3503_ = lean_expr_abstract_range(v_ty_3501_, v_n_3498_, v_xs_3489_);
lean_dec_ref(v_ty_3501_);
v___x_3504_ = l_Lean_mkForall(v_n_3500_, v_bi_3502_, v_ty_3503_, v_x_3494_);
v___x_3505_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3489_, v_lctx_3490_, v_usedLetOnly_3491_, v_generalizeNondepLet_3492_, v_n_3498_, v___x_3504_);
return v___x_3505_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0___boxed(lean_object* v_xs_3530_, lean_object* v_lctx_3531_, lean_object* v_usedLetOnly_3532_, lean_object* v_generalizeNondepLet_3533_, lean_object* v_x_3534_, lean_object* v_x_3535_){
_start:
{
uint8_t v_usedLetOnly_boxed_3536_; uint8_t v_generalizeNondepLet_boxed_3537_; lean_object* v_res_3538_; 
v_usedLetOnly_boxed_3536_ = lean_unbox(v_usedLetOnly_3532_);
v_generalizeNondepLet_boxed_3537_ = lean_unbox(v_generalizeNondepLet_3533_);
v_res_3538_ = l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(v_xs_3530_, v_lctx_3531_, v_usedLetOnly_boxed_3536_, v_generalizeNondepLet_boxed_3537_, v_x_3534_, v_x_3535_);
lean_dec(v_x_3534_);
lean_dec_ref(v_xs_3530_);
return v_res_3538_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkForall(lean_object* v_lctx_3539_, lean_object* v_xs_3540_, lean_object* v_b_3541_, uint8_t v_usedLetOnly_3542_, uint8_t v_generalizeNondepLet_3543_){
_start:
{
lean_object* v_b_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; 
v_b_3544_ = lean_expr_abstract(v_b_3541_, v_xs_3540_);
v___x_3545_ = lean_array_get_size(v_xs_3540_);
v___x_3546_ = l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(v_xs_3540_, v_lctx_3539_, v_usedLetOnly_3542_, v_generalizeNondepLet_3543_, v___x_3545_, v_b_3544_);
return v___x_3546_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkForall___boxed(lean_object* v_lctx_3547_, lean_object* v_xs_3548_, lean_object* v_b_3549_, lean_object* v_usedLetOnly_3550_, lean_object* v_generalizeNondepLet_3551_){
_start:
{
uint8_t v_usedLetOnly_boxed_3552_; uint8_t v_generalizeNondepLet_boxed_3553_; lean_object* v_res_3554_; 
v_usedLetOnly_boxed_3552_ = lean_unbox(v_usedLetOnly_3550_);
v_generalizeNondepLet_boxed_3553_ = lean_unbox(v_generalizeNondepLet_3551_);
v_res_3554_ = l_Lean_LocalContext_mkForall(v_lctx_3547_, v_xs_3548_, v_b_3549_, v_usedLetOnly_boxed_3552_, v_generalizeNondepLet_boxed_3553_);
lean_dec_ref(v_b_3549_);
lean_dec_ref(v_xs_3548_);
return v_res_3554_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM___redArg___lam__0(lean_object* v_toPure_3555_, lean_object* v_p_3556_, lean_object* v_d_3557_){
_start:
{
if (lean_obj_tag(v_d_3557_) == 0)
{
uint8_t v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; 
lean_dec(v_p_3556_);
v___x_3558_ = 0;
v___x_3559_ = lean_box(v___x_3558_);
v___x_3560_ = lean_apply_2(v_toPure_3555_, lean_box(0), v___x_3559_);
return v___x_3560_;
}
else
{
lean_object* v_val_3561_; lean_object* v___x_3562_; 
lean_dec(v_toPure_3555_);
v_val_3561_ = lean_ctor_get(v_d_3557_, 0);
lean_inc(v_val_3561_);
lean_dec_ref_known(v_d_3557_, 1);
v___x_3562_ = lean_apply_1(v_p_3556_, v_val_3561_);
return v___x_3562_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM___redArg(lean_object* v_inst_3563_, lean_object* v_lctx_3564_, lean_object* v_p_3565_){
_start:
{
lean_object* v_toApplicative_3566_; lean_object* v_decls_3567_; lean_object* v_toPure_3568_; lean_object* v___f_3569_; lean_object* v___x_3570_; 
v_toApplicative_3566_ = lean_ctor_get(v_inst_3563_, 0);
v_decls_3567_ = lean_ctor_get(v_lctx_3564_, 1);
lean_inc_ref(v_decls_3567_);
lean_dec_ref(v_lctx_3564_);
v_toPure_3568_ = lean_ctor_get(v_toApplicative_3566_, 1);
lean_inc(v_toPure_3568_);
v___f_3569_ = lean_alloc_closure((void*)(l_Lean_LocalContext_anyM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3569_, 0, v_toPure_3568_);
lean_closure_set(v___f_3569_, 1, v_p_3565_);
v___x_3570_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3563_, v_decls_3567_, v___f_3569_);
return v___x_3570_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM(lean_object* v_m_3571_, lean_object* v_inst_3572_, lean_object* v_lctx_3573_, lean_object* v_p_3574_){
_start:
{
lean_object* v_toApplicative_3575_; lean_object* v_decls_3576_; lean_object* v_toPure_3577_; lean_object* v___f_3578_; lean_object* v___x_3579_; 
v_toApplicative_3575_ = lean_ctor_get(v_inst_3572_, 0);
v_decls_3576_ = lean_ctor_get(v_lctx_3573_, 1);
lean_inc_ref(v_decls_3576_);
lean_dec_ref(v_lctx_3573_);
v_toPure_3577_ = lean_ctor_get(v_toApplicative_3575_, 1);
lean_inc(v_toPure_3577_);
v___f_3578_ = lean_alloc_closure((void*)(l_Lean_LocalContext_anyM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3578_, 0, v_toPure_3577_);
lean_closure_set(v___f_3578_, 1, v_p_3574_);
v___x_3579_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3572_, v_decls_3576_, v___f_3578_);
return v___x_3579_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__0(lean_object* v_toPure_3580_, uint8_t v_b_3581_){
_start:
{
if (v_b_3581_ == 0)
{
uint8_t v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; 
v___x_3582_ = 1;
v___x_3583_ = lean_box(v___x_3582_);
v___x_3584_ = lean_apply_2(v_toPure_3580_, lean_box(0), v___x_3583_);
return v___x_3584_;
}
else
{
uint8_t v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; 
v___x_3585_ = 0;
v___x_3586_ = lean_box(v___x_3585_);
v___x_3587_ = lean_apply_2(v_toPure_3580_, lean_box(0), v___x_3586_);
return v___x_3587_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__0___boxed(lean_object* v_toPure_3588_, lean_object* v_b_3589_){
_start:
{
uint8_t v_b_boxed_3590_; lean_object* v_res_3591_; 
v_b_boxed_3590_ = lean_unbox(v_b_3589_);
v_res_3591_ = l_Lean_LocalContext_allM___redArg___lam__0(v_toPure_3588_, v_b_boxed_3590_);
return v_res_3591_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__2(lean_object* v_toPure_3592_, lean_object* v_toBind_3593_, lean_object* v___f_3594_, lean_object* v_p_3595_, lean_object* v_v_3596_){
_start:
{
if (lean_obj_tag(v_v_3596_) == 0)
{
uint8_t v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; 
lean_dec(v_p_3595_);
v___x_3597_ = 1;
v___x_3598_ = lean_box(v___x_3597_);
v___x_3599_ = lean_apply_2(v_toPure_3592_, lean_box(0), v___x_3598_);
v___x_3600_ = lean_apply_4(v_toBind_3593_, lean_box(0), lean_box(0), v___x_3599_, v___f_3594_);
return v___x_3600_;
}
else
{
lean_object* v_val_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; 
lean_dec(v_toPure_3592_);
v_val_3601_ = lean_ctor_get(v_v_3596_, 0);
lean_inc(v_val_3601_);
lean_dec_ref_known(v_v_3596_, 1);
v___x_3602_ = lean_apply_1(v_p_3595_, v_val_3601_);
v___x_3603_ = lean_apply_4(v_toBind_3593_, lean_box(0), lean_box(0), v___x_3602_, v___f_3594_);
return v___x_3603_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg(lean_object* v_inst_3604_, lean_object* v_lctx_3605_, lean_object* v_p_3606_){
_start:
{
lean_object* v_toApplicative_3607_; lean_object* v_decls_3608_; lean_object* v_toBind_3609_; lean_object* v_toPure_3610_; lean_object* v___f_3611_; lean_object* v___f_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; 
v_toApplicative_3607_ = lean_ctor_get(v_inst_3604_, 0);
v_decls_3608_ = lean_ctor_get(v_lctx_3605_, 1);
lean_inc_ref(v_decls_3608_);
lean_dec_ref(v_lctx_3605_);
v_toBind_3609_ = lean_ctor_get(v_inst_3604_, 1);
lean_inc_n(v_toBind_3609_, 2);
v_toPure_3610_ = lean_ctor_get(v_toApplicative_3607_, 1);
lean_inc_n(v_toPure_3610_, 2);
v___f_3611_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3611_, 0, v_toPure_3610_);
lean_inc_ref(v___f_3611_);
v___f_3612_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3612_, 0, v_toPure_3610_);
lean_closure_set(v___f_3612_, 1, v_toBind_3609_);
lean_closure_set(v___f_3612_, 2, v___f_3611_);
lean_closure_set(v___f_3612_, 3, v_p_3606_);
v___x_3613_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3604_, v_decls_3608_, v___f_3612_);
v___x_3614_ = lean_apply_4(v_toBind_3609_, lean_box(0), lean_box(0), v___x_3613_, v___f_3611_);
return v___x_3614_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM(lean_object* v_m_3615_, lean_object* v_inst_3616_, lean_object* v_lctx_3617_, lean_object* v_p_3618_){
_start:
{
lean_object* v_toApplicative_3619_; lean_object* v_decls_3620_; lean_object* v_toBind_3621_; lean_object* v_toPure_3622_; lean_object* v___f_3623_; lean_object* v___f_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; 
v_toApplicative_3619_ = lean_ctor_get(v_inst_3616_, 0);
v_decls_3620_ = lean_ctor_get(v_lctx_3617_, 1);
lean_inc_ref(v_decls_3620_);
lean_dec_ref(v_lctx_3617_);
v_toBind_3621_ = lean_ctor_get(v_inst_3616_, 1);
lean_inc_n(v_toBind_3621_, 2);
v_toPure_3622_ = lean_ctor_get(v_toApplicative_3619_, 1);
lean_inc_n(v_toPure_3622_, 2);
v___f_3623_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3623_, 0, v_toPure_3622_);
lean_inc_ref(v___f_3623_);
v___f_3624_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3624_, 0, v_toPure_3622_);
lean_closure_set(v___f_3624_, 1, v_toBind_3621_);
lean_closure_set(v___f_3624_, 2, v___f_3623_);
lean_closure_set(v___f_3624_, 3, v_p_3618_);
v___x_3625_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3616_, v_decls_3620_, v___f_3624_);
v___x_3626_ = lean_apply_4(v_toBind_3621_, lean_box(0), lean_box(0), v___x_3625_, v___f_3623_);
return v___x_3626_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_any___lam__0(lean_object* v_p_3627_, lean_object* v_d_3628_){
_start:
{
if (lean_obj_tag(v_d_3628_) == 0)
{
uint8_t v___x_3629_; 
lean_dec_ref(v_p_3627_);
v___x_3629_ = 0;
return v___x_3629_;
}
else
{
lean_object* v_val_3630_; lean_object* v___x_3631_; uint8_t v___x_3632_; 
v_val_3630_ = lean_ctor_get(v_d_3628_, 0);
lean_inc(v_val_3630_);
lean_dec_ref_known(v_d_3628_, 1);
v___x_3631_ = lean_apply_1(v_p_3627_, v_val_3630_);
v___x_3632_ = lean_unbox(v___x_3631_);
return v___x_3632_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_any___lam__0___boxed(lean_object* v_p_3633_, lean_object* v_d_3634_){
_start:
{
uint8_t v_res_3635_; lean_object* v_r_3636_; 
v_res_3635_ = l_Lean_LocalContext_any___lam__0(v_p_3633_, v_d_3634_);
v_r_3636_ = lean_box(v_res_3635_);
return v_r_3636_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_any(lean_object* v_lctx_3637_, lean_object* v_p_3638_){
_start:
{
lean_object* v___x_3639_; lean_object* v_decls_3640_; lean_object* v___f_3641_; lean_object* v___x_3642_; uint8_t v___x_3643_; 
v___x_3639_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v_decls_3640_ = lean_ctor_get(v_lctx_3637_, 1);
lean_inc_ref(v_decls_3640_);
lean_dec_ref(v_lctx_3637_);
v___f_3641_ = lean_alloc_closure((void*)(l_Lean_LocalContext_any___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3641_, 0, v_p_3638_);
v___x_3642_ = l_Lean_PersistentArray_anyM___redArg(v___x_3639_, v_decls_3640_, v___f_3641_);
v___x_3643_ = lean_unbox(v___x_3642_);
lean_dec(v___x_3642_);
return v___x_3643_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_any___boxed(lean_object* v_lctx_3644_, lean_object* v_p_3645_){
_start:
{
uint8_t v_res_3646_; lean_object* v_r_3647_; 
v_res_3646_ = l_Lean_LocalContext_any(v_lctx_3644_, v_p_3645_);
v_r_3647_ = lean_box(v_res_3646_);
return v_r_3647_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_all___lam__0(lean_object* v_p_3648_, lean_object* v_v_3649_){
_start:
{
if (lean_obj_tag(v_v_3649_) == 0)
{
uint8_t v___x_3650_; 
lean_dec_ref(v_p_3648_);
v___x_3650_ = 0;
return v___x_3650_;
}
else
{
lean_object* v_val_3651_; lean_object* v___x_3652_; uint8_t v___x_3653_; 
v_val_3651_ = lean_ctor_get(v_v_3649_, 0);
lean_inc(v_val_3651_);
lean_dec_ref_known(v_v_3649_, 1);
v___x_3652_ = lean_apply_1(v_p_3648_, v_val_3651_);
v___x_3653_ = lean_unbox(v___x_3652_);
if (v___x_3653_ == 0)
{
uint8_t v___x_3654_; 
v___x_3654_ = 1;
return v___x_3654_;
}
else
{
uint8_t v___x_3655_; 
v___x_3655_ = 0;
return v___x_3655_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_all___lam__0___boxed(lean_object* v_p_3656_, lean_object* v_v_3657_){
_start:
{
uint8_t v_res_3658_; lean_object* v_r_3659_; 
v_res_3658_ = l_Lean_LocalContext_all___lam__0(v_p_3656_, v_v_3657_);
v_r_3659_ = lean_box(v_res_3658_);
return v_r_3659_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_all(lean_object* v_lctx_3660_, lean_object* v_p_3661_){
_start:
{
lean_object* v___x_3662_; lean_object* v_decls_3663_; lean_object* v___f_3664_; lean_object* v___x_3665_; uint8_t v___x_3666_; 
v___x_3662_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v_decls_3663_ = lean_ctor_get(v_lctx_3660_, 1);
lean_inc_ref(v_decls_3663_);
lean_dec_ref(v_lctx_3660_);
v___f_3664_ = lean_alloc_closure((void*)(l_Lean_LocalContext_all___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3664_, 0, v_p_3661_);
v___x_3665_ = l_Lean_PersistentArray_anyM___redArg(v___x_3662_, v_decls_3663_, v___f_3664_);
v___x_3666_ = lean_unbox(v___x_3665_);
lean_dec(v___x_3665_);
if (v___x_3666_ == 0)
{
uint8_t v___x_3667_; 
v___x_3667_ = 1;
return v___x_3667_;
}
else
{
uint8_t v___x_3668_; 
v___x_3668_ = 0;
return v___x_3668_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_all___boxed(lean_object* v_lctx_3669_, lean_object* v_p_3670_){
_start:
{
uint8_t v_res_3671_; lean_object* v_r_3672_; 
v_res_3671_ = l_Lean_LocalContext_all(v_lctx_3669_, v_p_3670_);
v_r_3672_ = lean_box(v_res_3671_);
return v_r_3672_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(lean_object* v_i_3673_, lean_object* v_a_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_){
_start:
{
lean_object* v_zero_3677_; uint8_t v_isZero_3678_; 
v_zero_3677_ = lean_unsigned_to_nat(0u);
v_isZero_3678_ = lean_nat_dec_eq(v_i_3673_, v_zero_3677_);
if (v_isZero_3678_ == 1)
{
lean_object* v___x_3679_; lean_object* v___x_3680_; 
lean_dec(v_i_3673_);
v___x_3679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3679_, 0, v_a_3674_);
lean_ctor_set(v___x_3679_, 1, v___y_3675_);
v___x_3680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3680_, 0, v___x_3679_);
lean_ctor_set(v___x_3680_, 1, v___y_3676_);
return v___x_3680_;
}
else
{
lean_object* v_decls_3681_; lean_object* v_size_3682_; lean_object* v___x_3683_; lean_object* v_one_3684_; lean_object* v_n_3685_; lean_object* v___y_3687_; lean_object* v___y_3688_; lean_object* v___y_3689_; lean_object* v___y_3690_; lean_object* v___y_3694_; lean_object* v___y_3695_; lean_object* v___y_3702_; lean_object* v___y_3703_; uint8_t v___y_3704_; lean_object* v___y_3708_; lean_object* v___y_3709_; lean_object* v___y_3714_; uint8_t v___x_3718_; 
v_decls_3681_ = lean_ctor_get(v_a_3674_, 1);
v_size_3682_ = lean_ctor_get(v_decls_3681_, 2);
v___x_3683_ = lean_box(0);
v_one_3684_ = lean_unsigned_to_nat(1u);
v_n_3685_ = lean_nat_sub(v_i_3673_, v_one_3684_);
lean_dec(v_i_3673_);
v___x_3718_ = lean_nat_dec_lt(v_n_3685_, v_size_3682_);
if (v___x_3718_ == 0)
{
lean_object* v___x_3719_; 
v___x_3719_ = l_outOfBounds___redArg(v___x_3683_);
v___y_3714_ = v___x_3719_;
goto v___jp_3713_;
}
else
{
lean_object* v___x_3720_; 
v___x_3720_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3683_, v_decls_3681_, v_n_3685_);
v___y_3714_ = v___x_3720_;
goto v___jp_3713_;
}
v___jp_3686_:
{
lean_object* v___x_3691_; 
v___x_3691_ = l_Lean_LocalContext_setUserName(v_a_3674_, v___y_3690_, v___y_3688_);
v_i_3673_ = v_n_3685_;
v_a_3674_ = v___x_3691_;
v___y_3675_ = v___y_3687_;
v___y_3676_ = v___y_3689_;
goto _start;
}
v___jp_3693_:
{
lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v_fst_3698_; lean_object* v_snd_3699_; lean_object* v_fvarId_3700_; 
lean_inc(v___y_3695_);
v___x_3696_ = l_Lean_NameSet_insert(v___y_3675_, v___y_3695_);
v___x_3697_ = l_Lean_sanitizeName(v___y_3695_, v___y_3676_);
v_fst_3698_ = lean_ctor_get(v___x_3697_, 0);
lean_inc(v_fst_3698_);
v_snd_3699_ = lean_ctor_get(v___x_3697_, 1);
lean_inc(v_snd_3699_);
lean_dec_ref(v___x_3697_);
v_fvarId_3700_ = lean_ctor_get(v___y_3694_, 1);
lean_inc(v_fvarId_3700_);
lean_dec_ref(v___y_3694_);
v___y_3687_ = v___x_3696_;
v___y_3688_ = v_fst_3698_;
v___y_3689_ = v_snd_3699_;
v___y_3690_ = v_fvarId_3700_;
goto v___jp_3686_;
}
v___jp_3701_:
{
if (v___y_3704_ == 0)
{
lean_object* v___x_3705_; 
lean_dec_ref(v___y_3702_);
v___x_3705_ = l_Lean_NameSet_insert(v___y_3675_, v___y_3703_);
v_i_3673_ = v_n_3685_;
v___y_3675_ = v___x_3705_;
goto _start;
}
else
{
v___y_3694_ = v___y_3702_;
v___y_3695_ = v___y_3703_;
goto v___jp_3693_;
}
}
v___jp_3707_:
{
uint8_t v___x_3710_; 
v___x_3710_ = l_Lean_Name_hasMacroScopes(v___y_3709_);
if (v___x_3710_ == 0)
{
lean_object* v_userName_3711_; uint8_t v___x_3712_; 
v_userName_3711_ = lean_ctor_get(v___y_3708_, 2);
v___x_3712_ = l_Lean_NameSet_contains(v___y_3675_, v_userName_3711_);
v___y_3702_ = v___y_3708_;
v___y_3703_ = v___y_3709_;
v___y_3704_ = v___x_3712_;
goto v___jp_3701_;
}
else
{
v___y_3694_ = v___y_3708_;
v___y_3695_ = v___y_3709_;
goto v___jp_3693_;
}
}
v___jp_3713_:
{
if (lean_obj_tag(v___y_3714_) == 0)
{
v_i_3673_ = v_n_3685_;
goto _start;
}
else
{
lean_object* v_val_3716_; lean_object* v_userName_3717_; 
v_val_3716_ = lean_ctor_get(v___y_3714_, 0);
lean_inc(v_val_3716_);
lean_dec_ref_known(v___y_3714_, 1);
v_userName_3717_ = lean_ctor_get(v_val_3716_, 2);
lean_inc(v_userName_3717_);
v___y_3708_ = v_val_3716_;
v___y_3709_ = v_userName_3717_;
goto v___jp_3707_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_sanitizeNames(lean_object* v_lctx_3721_, lean_object* v_a_3722_){
_start:
{
lean_object* v_options_3723_; uint8_t v___x_3724_; 
v_options_3723_ = lean_ctor_get(v_a_3722_, 0);
v___x_3724_ = l_Lean_getSanitizeNames(v_options_3723_);
if (v___x_3724_ == 0)
{
lean_object* v___x_3725_; 
v___x_3725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3725_, 0, v_lctx_3721_);
lean_ctor_set(v___x_3725_, 1, v_a_3722_);
return v___x_3725_;
}
else
{
lean_object* v_decls_3726_; lean_object* v_size_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v_fst_3730_; lean_object* v_snd_3731_; lean_object* v_fst_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3739_; 
v_decls_3726_ = lean_ctor_get(v_lctx_3721_, 1);
v_size_3727_ = lean_ctor_get(v_decls_3726_, 2);
lean_inc(v_size_3727_);
v___x_3728_ = l_Lean_NameSet_empty;
v___x_3729_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(v_size_3727_, v_lctx_3721_, v___x_3728_, v_a_3722_);
v_fst_3730_ = lean_ctor_get(v___x_3729_, 0);
lean_inc(v_fst_3730_);
v_snd_3731_ = lean_ctor_get(v___x_3729_, 1);
lean_inc(v_snd_3731_);
lean_dec_ref(v___x_3729_);
v_fst_3732_ = lean_ctor_get(v_fst_3730_, 0);
v_isSharedCheck_3739_ = !lean_is_exclusive(v_fst_3730_);
if (v_isSharedCheck_3739_ == 0)
{
lean_object* v_unused_3740_; 
v_unused_3740_ = lean_ctor_get(v_fst_3730_, 1);
lean_dec(v_unused_3740_);
v___x_3734_ = v_fst_3730_;
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_fst_3732_);
lean_dec(v_fst_3730_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v___x_3737_; 
if (v_isShared_3735_ == 0)
{
lean_ctor_set(v___x_3734_, 1, v_snd_3731_);
v___x_3737_ = v___x_3734_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_fst_3732_);
lean_ctor_set(v_reuseFailAlloc_3738_, 1, v_snd_3731_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0(lean_object* v_n_3741_, lean_object* v_i_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_){
_start:
{
lean_object* v___x_3747_; 
v___x_3747_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(v_i_3742_, v_a_3744_, v___y_3745_, v___y_3746_);
return v___x_3747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___boxed(lean_object* v_n_3748_, lean_object* v_i_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_){
_start:
{
lean_object* v_res_3754_; 
v_res_3754_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0(v_n_3748_, v_i_3749_, v_a_3750_, v_a_3751_, v___y_3752_, v___y_3753_);
lean_dec(v_n_3748_);
return v_res_3754_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getRoundtrippingUserName_x3f(lean_object* v_lctx_3755_, lean_object* v_fvarId_3756_){
_start:
{
lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v___y_3760_; lean_object* v___y_3765_; lean_object* v___y_3766_; lean_object* v___y_3767_; lean_object* v___x_3769_; 
lean_inc_ref(v_lctx_3755_);
v___x_3769_ = lean_local_ctx_find(v_lctx_3755_, v_fvarId_3756_);
if (lean_obj_tag(v___x_3769_) == 0)
{
lean_object* v___x_3770_; 
lean_dec_ref(v_lctx_3755_);
v___x_3770_ = lean_box(0);
return v___x_3770_;
}
else
{
lean_object* v_val_3771_; lean_object* v___y_3773_; lean_object* v_userName_3778_; 
v_val_3771_ = lean_ctor_get(v___x_3769_, 0);
lean_inc(v_val_3771_);
lean_dec_ref_known(v___x_3769_, 1);
v_userName_3778_ = lean_ctor_get(v_val_3771_, 2);
lean_inc(v_userName_3778_);
v___y_3773_ = v_userName_3778_;
goto v___jp_3772_;
v___jp_3772_:
{
lean_object* v___x_3774_; 
v___x_3774_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_3755_, v___y_3773_);
lean_dec_ref(v_lctx_3755_);
if (lean_obj_tag(v___x_3774_) == 0)
{
lean_object* v___x_3775_; 
lean_dec(v___y_3773_);
lean_dec(v_val_3771_);
v___x_3775_ = lean_box(0);
return v___x_3775_;
}
else
{
lean_object* v_val_3776_; lean_object* v_fvarId_3777_; 
v_val_3776_ = lean_ctor_get(v___x_3774_, 0);
lean_inc(v_val_3776_);
lean_dec_ref_known(v___x_3774_, 1);
v_fvarId_3777_ = lean_ctor_get(v_val_3771_, 1);
lean_inc(v_fvarId_3777_);
lean_dec(v_val_3771_);
v___y_3765_ = v___y_3773_;
v___y_3766_ = v_val_3776_;
v___y_3767_ = v_fvarId_3777_;
goto v___jp_3764_;
}
}
}
v___jp_3757_:
{
uint8_t v___x_3761_; 
v___x_3761_ = l_Lean_instBEqFVarId_beq(v___y_3759_, v___y_3760_);
lean_dec(v___y_3760_);
lean_dec(v___y_3759_);
if (v___x_3761_ == 0)
{
lean_object* v___x_3762_; 
lean_dec(v___y_3758_);
v___x_3762_ = lean_box(0);
return v___x_3762_;
}
else
{
lean_object* v___x_3763_; 
v___x_3763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3763_, 0, v___y_3758_);
return v___x_3763_;
}
}
v___jp_3764_:
{
lean_object* v_fvarId_3768_; 
v_fvarId_3768_ = lean_ctor_get(v___y_3766_, 1);
lean_inc(v_fvarId_3768_);
lean_dec_ref(v___y_3766_);
v___y_3758_ = v___y_3765_;
v___y_3759_ = v___y_3767_;
v___y_3760_ = v_fvarId_3768_;
goto v___jp_3757_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(size_t v_sz_3779_, size_t v_i_3780_, lean_object* v_bs_3781_){
_start:
{
uint8_t v___x_3782_; 
v___x_3782_ = lean_usize_dec_lt(v_i_3780_, v_sz_3779_);
if (v___x_3782_ == 0)
{
return v_bs_3781_;
}
else
{
lean_object* v_v_3783_; lean_object* v_snd_3784_; lean_object* v___x_3785_; lean_object* v_bs_x27_3786_; size_t v___x_3787_; size_t v___x_3788_; lean_object* v___x_3789_; 
v_v_3783_ = lean_array_uget_borrowed(v_bs_3781_, v_i_3780_);
v_snd_3784_ = lean_ctor_get(v_v_3783_, 1);
lean_inc(v_snd_3784_);
v___x_3785_ = lean_unsigned_to_nat(0u);
v_bs_x27_3786_ = lean_array_uset(v_bs_3781_, v_i_3780_, v___x_3785_);
v___x_3787_ = ((size_t)1ULL);
v___x_3788_ = lean_usize_add(v_i_3780_, v___x_3787_);
v___x_3789_ = lean_array_uset(v_bs_x27_3786_, v_i_3780_, v_snd_3784_);
v_i_3780_ = v___x_3788_;
v_bs_3781_ = v___x_3789_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0___boxed(lean_object* v_sz_3791_, lean_object* v_i_3792_, lean_object* v_bs_3793_){
_start:
{
size_t v_sz_boxed_3794_; size_t v_i_boxed_3795_; lean_object* v_res_3796_; 
v_sz_boxed_3794_ = lean_unbox_usize(v_sz_3791_);
lean_dec(v_sz_3791_);
v_i_boxed_3795_ = lean_unbox_usize(v_i_3792_);
lean_dec(v_i_3792_);
v_res_3796_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(v_sz_boxed_3794_, v_i_boxed_3795_, v_bs_3793_);
return v_res_3796_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(lean_object* v_lctx_3797_, size_t v_sz_3798_, size_t v_i_3799_, lean_object* v_bs_3800_){
_start:
{
uint8_t v___x_3801_; 
v___x_3801_ = lean_usize_dec_lt(v_i_3799_, v_sz_3798_);
if (v___x_3801_ == 0)
{
return v_bs_3800_;
}
else
{
lean_object* v_fvarIdToDecl_3802_; lean_object* v_v_3803_; lean_object* v___x_3804_; lean_object* v_bs_x27_3805_; lean_object* v___y_3807_; lean_object* v___x_3812_; 
v_fvarIdToDecl_3802_ = lean_ctor_get(v_lctx_3797_, 0);
v_v_3803_ = lean_array_uget(v_bs_3800_, v_i_3799_);
v___x_3804_ = lean_unsigned_to_nat(0u);
v_bs_x27_3805_ = lean_array_uset(v_bs_3800_, v_i_3799_, v___x_3804_);
v___x_3812_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_fvarIdToDecl_3802_, v_v_3803_);
if (lean_obj_tag(v___x_3812_) == 0)
{
lean_object* v___x_3813_; 
v___x_3813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3813_, 0, v___x_3804_);
lean_ctor_set(v___x_3813_, 1, v_v_3803_);
v___y_3807_ = v___x_3813_;
goto v___jp_3806_;
}
else
{
lean_object* v_val_3814_; lean_object* v_index_3815_; lean_object* v___x_3816_; 
v_val_3814_ = lean_ctor_get(v___x_3812_, 0);
lean_inc(v_val_3814_);
lean_dec_ref_known(v___x_3812_, 1);
v_index_3815_ = lean_ctor_get(v_val_3814_, 0);
lean_inc(v_index_3815_);
lean_dec(v_val_3814_);
v___x_3816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3816_, 0, v_index_3815_);
lean_ctor_set(v___x_3816_, 1, v_v_3803_);
v___y_3807_ = v___x_3816_;
goto v___jp_3806_;
}
v___jp_3806_:
{
size_t v___x_3808_; size_t v___x_3809_; lean_object* v___x_3810_; 
v___x_3808_ = ((size_t)1ULL);
v___x_3809_ = lean_usize_add(v_i_3799_, v___x_3808_);
v___x_3810_ = lean_array_uset(v_bs_x27_3805_, v_i_3799_, v___y_3807_);
v_i_3799_ = v___x_3809_;
v_bs_3800_ = v___x_3810_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1___boxed(lean_object* v_lctx_3817_, lean_object* v_sz_3818_, lean_object* v_i_3819_, lean_object* v_bs_3820_){
_start:
{
size_t v_sz_boxed_3821_; size_t v_i_boxed_3822_; lean_object* v_res_3823_; 
v_sz_boxed_3821_ = lean_unbox_usize(v_sz_3818_);
lean_dec(v_sz_3818_);
v_i_boxed_3822_ = lean_unbox_usize(v_i_3819_);
lean_dec(v_i_3819_);
v_res_3823_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(v_lctx_3817_, v_sz_boxed_3821_, v_i_boxed_3822_, v_bs_3820_);
lean_dec_ref(v_lctx_3817_);
return v_res_3823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(lean_object* v_hi_3824_, lean_object* v_pivot_3825_, lean_object* v_as_3826_, lean_object* v_i_3827_, lean_object* v_k_3828_){
_start:
{
uint8_t v___x_3829_; 
v___x_3829_ = lean_nat_dec_lt(v_k_3828_, v_hi_3824_);
if (v___x_3829_ == 0)
{
lean_object* v___x_3830_; lean_object* v___x_3831_; 
lean_dec(v_k_3828_);
v___x_3830_ = lean_array_fswap(v_as_3826_, v_i_3827_, v_hi_3824_);
v___x_3831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3831_, 0, v_i_3827_);
lean_ctor_set(v___x_3831_, 1, v___x_3830_);
return v___x_3831_;
}
else
{
lean_object* v___x_3832_; lean_object* v_fst_3833_; lean_object* v_fst_3834_; uint8_t v___x_3835_; 
v___x_3832_ = lean_array_fget_borrowed(v_as_3826_, v_k_3828_);
v_fst_3833_ = lean_ctor_get(v___x_3832_, 0);
v_fst_3834_ = lean_ctor_get(v_pivot_3825_, 0);
v___x_3835_ = lean_nat_dec_lt(v_fst_3833_, v_fst_3834_);
if (v___x_3835_ == 0)
{
lean_object* v___x_3836_; lean_object* v___x_3837_; 
v___x_3836_ = lean_unsigned_to_nat(1u);
v___x_3837_ = lean_nat_add(v_k_3828_, v___x_3836_);
lean_dec(v_k_3828_);
v_k_3828_ = v___x_3837_;
goto _start;
}
else
{
lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; 
v___x_3839_ = lean_array_fswap(v_as_3826_, v_i_3827_, v_k_3828_);
v___x_3840_ = lean_unsigned_to_nat(1u);
v___x_3841_ = lean_nat_add(v_i_3827_, v___x_3840_);
lean_dec(v_i_3827_);
v___x_3842_ = lean_nat_add(v_k_3828_, v___x_3840_);
lean_dec(v_k_3828_);
v_as_3826_ = v___x_3839_;
v_i_3827_ = v___x_3841_;
v_k_3828_ = v___x_3842_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg___boxed(lean_object* v_hi_3844_, lean_object* v_pivot_3845_, lean_object* v_as_3846_, lean_object* v_i_3847_, lean_object* v_k_3848_){
_start:
{
lean_object* v_res_3849_; 
v_res_3849_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(v_hi_3844_, v_pivot_3845_, v_as_3846_, v_i_3847_, v_k_3848_);
lean_dec_ref(v_pivot_3845_);
lean_dec(v_hi_3844_);
return v_res_3849_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(lean_object* v_h_3850_, lean_object* v_i_3851_){
_start:
{
lean_object* v_fst_3852_; lean_object* v_fst_3853_; uint8_t v___x_3854_; 
v_fst_3852_ = lean_ctor_get(v_h_3850_, 0);
v_fst_3853_ = lean_ctor_get(v_i_3851_, 0);
v___x_3854_ = lean_nat_dec_lt(v_fst_3852_, v_fst_3853_);
return v___x_3854_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0___boxed(lean_object* v_h_3855_, lean_object* v_i_3856_){
_start:
{
uint8_t v_res_3857_; lean_object* v_r_3858_; 
v_res_3857_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v_h_3855_, v_i_3856_);
lean_dec_ref(v_i_3856_);
lean_dec_ref(v_h_3855_);
v_r_3858_ = lean_box(v_res_3857_);
return v_r_3858_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(lean_object* v_n_3859_, lean_object* v_as_3860_, lean_object* v_lo_3861_, lean_object* v_hi_3862_){
_start:
{
lean_object* v___y_3864_; uint8_t v___x_3874_; 
v___x_3874_ = lean_nat_dec_lt(v_lo_3861_, v_hi_3862_);
if (v___x_3874_ == 0)
{
lean_dec(v_lo_3861_);
return v_as_3860_;
}
else
{
lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v_mid_3877_; lean_object* v___y_3879_; lean_object* v___y_3885_; lean_object* v___x_3890_; lean_object* v___x_3891_; uint8_t v___x_3892_; 
v___x_3875_ = lean_nat_add(v_lo_3861_, v_hi_3862_);
v___x_3876_ = lean_unsigned_to_nat(1u);
v_mid_3877_ = lean_nat_shiftr(v___x_3875_, v___x_3876_);
lean_dec(v___x_3875_);
v___x_3890_ = lean_array_fget_borrowed(v_as_3860_, v_mid_3877_);
v___x_3891_ = lean_array_fget_borrowed(v_as_3860_, v_lo_3861_);
v___x_3892_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v___x_3890_, v___x_3891_);
if (v___x_3892_ == 0)
{
v___y_3885_ = v_as_3860_;
goto v___jp_3884_;
}
else
{
lean_object* v___x_3893_; 
v___x_3893_ = lean_array_fswap(v_as_3860_, v_lo_3861_, v_mid_3877_);
v___y_3885_ = v___x_3893_;
goto v___jp_3884_;
}
v___jp_3878_:
{
lean_object* v___x_3880_; lean_object* v___x_3881_; uint8_t v___x_3882_; 
v___x_3880_ = lean_array_fget_borrowed(v___y_3879_, v_mid_3877_);
v___x_3881_ = lean_array_fget_borrowed(v___y_3879_, v_hi_3862_);
v___x_3882_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v___x_3880_, v___x_3881_);
if (v___x_3882_ == 0)
{
lean_dec(v_mid_3877_);
v___y_3864_ = v___y_3879_;
goto v___jp_3863_;
}
else
{
lean_object* v___x_3883_; 
v___x_3883_ = lean_array_fswap(v___y_3879_, v_mid_3877_, v_hi_3862_);
lean_dec(v_mid_3877_);
v___y_3864_ = v___x_3883_;
goto v___jp_3863_;
}
}
v___jp_3884_:
{
lean_object* v___x_3886_; lean_object* v___x_3887_; uint8_t v___x_3888_; 
v___x_3886_ = lean_array_fget_borrowed(v___y_3885_, v_hi_3862_);
v___x_3887_ = lean_array_fget_borrowed(v___y_3885_, v_lo_3861_);
v___x_3888_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v___x_3886_, v___x_3887_);
if (v___x_3888_ == 0)
{
v___y_3879_ = v___y_3885_;
goto v___jp_3878_;
}
else
{
lean_object* v___x_3889_; 
v___x_3889_ = lean_array_fswap(v___y_3885_, v_lo_3861_, v_hi_3862_);
v___y_3879_ = v___x_3889_;
goto v___jp_3878_;
}
}
}
v___jp_3863_:
{
lean_object* v_pivot_3865_; lean_object* v___x_3866_; lean_object* v_fst_3867_; lean_object* v_snd_3868_; uint8_t v___x_3869_; 
v_pivot_3865_ = lean_array_fget(v___y_3864_, v_hi_3862_);
lean_inc_n(v_lo_3861_, 2);
v___x_3866_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(v_hi_3862_, v_pivot_3865_, v___y_3864_, v_lo_3861_, v_lo_3861_);
lean_dec(v_pivot_3865_);
v_fst_3867_ = lean_ctor_get(v___x_3866_, 0);
lean_inc(v_fst_3867_);
v_snd_3868_ = lean_ctor_get(v___x_3866_, 1);
lean_inc(v_snd_3868_);
lean_dec_ref(v___x_3866_);
v___x_3869_ = lean_nat_dec_le(v_hi_3862_, v_fst_3867_);
if (v___x_3869_ == 0)
{
lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; 
v___x_3870_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v_n_3859_, v_snd_3868_, v_lo_3861_, v_fst_3867_);
v___x_3871_ = lean_unsigned_to_nat(1u);
v___x_3872_ = lean_nat_add(v_fst_3867_, v___x_3871_);
lean_dec(v_fst_3867_);
v_as_3860_ = v___x_3870_;
v_lo_3861_ = v___x_3872_;
goto _start;
}
else
{
lean_dec(v_fst_3867_);
lean_dec(v_lo_3861_);
return v_snd_3868_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___boxed(lean_object* v_n_3894_, lean_object* v_as_3895_, lean_object* v_lo_3896_, lean_object* v_hi_3897_){
_start:
{
lean_object* v_res_3898_; 
v_res_3898_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v_n_3894_, v_as_3895_, v_lo_3896_, v_hi_3897_);
lean_dec(v_hi_3897_);
lean_dec(v_n_3894_);
return v_res_3898_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_sortFVarsByContextOrder(lean_object* v_lctx_3899_, lean_object* v_hyps_3900_){
_start:
{
lean_object* v___y_3902_; size_t v_sz_3906_; size_t v___x_3907_; lean_object* v_hyps_3908_; lean_object* v___x_3909_; lean_object* v___y_3911_; lean_object* v___y_3912_; lean_object* v___x_3914_; uint8_t v___x_3915_; 
v_sz_3906_ = lean_array_size(v_hyps_3900_);
v___x_3907_ = ((size_t)0ULL);
v_hyps_3908_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(v_lctx_3899_, v_sz_3906_, v___x_3907_, v_hyps_3900_);
v___x_3909_ = lean_array_get_size(v_hyps_3908_);
v___x_3914_ = lean_unsigned_to_nat(0u);
v___x_3915_ = lean_nat_dec_eq(v___x_3909_, v___x_3914_);
if (v___x_3915_ == 0)
{
lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___y_3919_; uint8_t v___x_3921_; 
v___x_3916_ = lean_unsigned_to_nat(1u);
v___x_3917_ = lean_nat_sub(v___x_3909_, v___x_3916_);
v___x_3921_ = lean_nat_dec_le(v___x_3914_, v___x_3917_);
if (v___x_3921_ == 0)
{
lean_inc(v___x_3917_);
v___y_3919_ = v___x_3917_;
goto v___jp_3918_;
}
else
{
v___y_3919_ = v___x_3914_;
goto v___jp_3918_;
}
v___jp_3918_:
{
uint8_t v___x_3920_; 
v___x_3920_ = lean_nat_dec_le(v___y_3919_, v___x_3917_);
if (v___x_3920_ == 0)
{
lean_dec(v___x_3917_);
lean_inc(v___y_3919_);
v___y_3911_ = v___y_3919_;
v___y_3912_ = v___y_3919_;
goto v___jp_3910_;
}
else
{
v___y_3911_ = v___y_3919_;
v___y_3912_ = v___x_3917_;
goto v___jp_3910_;
}
}
}
else
{
v___y_3902_ = v_hyps_3908_;
goto v___jp_3901_;
}
v___jp_3901_:
{
size_t v_sz_3903_; size_t v___x_3904_; lean_object* v___x_3905_; 
v_sz_3903_ = lean_array_size(v___y_3902_);
v___x_3904_ = ((size_t)0ULL);
v___x_3905_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(v_sz_3903_, v___x_3904_, v___y_3902_);
return v___x_3905_;
}
v___jp_3910_:
{
lean_object* v___x_3913_; 
v___x_3913_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v___x_3909_, v_hyps_3908_, v___y_3911_, v___y_3912_);
lean_dec(v___y_3912_);
v___y_3902_ = v___x_3913_;
goto v___jp_3901_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_sortFVarsByContextOrder___boxed(lean_object* v_lctx_3922_, lean_object* v_hyps_3923_){
_start:
{
lean_object* v_res_3924_; 
v_res_3924_ = l_Lean_LocalContext_sortFVarsByContextOrder(v_lctx_3922_, v_hyps_3923_);
lean_dec_ref(v_lctx_3922_);
return v_res_3924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2(lean_object* v_n_3925_, lean_object* v_as_3926_, lean_object* v_lo_3927_, lean_object* v_hi_3928_, lean_object* v_w_3929_, lean_object* v_hlo_3930_, lean_object* v_hhi_3931_){
_start:
{
lean_object* v___x_3932_; 
v___x_3932_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v_n_3925_, v_as_3926_, v_lo_3927_, v_hi_3928_);
return v___x_3932_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___boxed(lean_object* v_n_3933_, lean_object* v_as_3934_, lean_object* v_lo_3935_, lean_object* v_hi_3936_, lean_object* v_w_3937_, lean_object* v_hlo_3938_, lean_object* v_hhi_3939_){
_start:
{
lean_object* v_res_3940_; 
v_res_3940_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2(v_n_3933_, v_as_3934_, v_lo_3935_, v_hi_3936_, v_w_3937_, v_hlo_3938_, v_hhi_3939_);
lean_dec(v_hi_3936_);
lean_dec(v_n_3933_);
return v_res_3940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2(lean_object* v_n_3941_, lean_object* v_lo_3942_, lean_object* v_hi_3943_, lean_object* v_hhi_3944_, lean_object* v_pivot_3945_, lean_object* v_as_3946_, lean_object* v_i_3947_, lean_object* v_k_3948_, lean_object* v_ilo_3949_, lean_object* v_ik_3950_, lean_object* v_w_3951_){
_start:
{
lean_object* v___x_3952_; 
v___x_3952_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(v_hi_3943_, v_pivot_3945_, v_as_3946_, v_i_3947_, v_k_3948_);
return v___x_3952_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___boxed(lean_object* v_n_3953_, lean_object* v_lo_3954_, lean_object* v_hi_3955_, lean_object* v_hhi_3956_, lean_object* v_pivot_3957_, lean_object* v_as_3958_, lean_object* v_i_3959_, lean_object* v_k_3960_, lean_object* v_ilo_3961_, lean_object* v_ik_3962_, lean_object* v_w_3963_){
_start:
{
lean_object* v_res_3964_; 
v_res_3964_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2(v_n_3953_, v_lo_3954_, v_hi_3955_, v_hhi_3956_, v_pivot_3957_, v_as_3958_, v_i_3959_, v_k_3960_, v_ilo_3961_, v_ik_3962_, v_w_3963_);
lean_dec_ref(v_pivot_3957_);
lean_dec(v_hi_3955_);
lean_dec(v_lo_3954_);
lean_dec(v_n_3953_);
return v_res_3964_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(lean_object* v_a_3965_, lean_object* v_x_3966_){
_start:
{
if (lean_obj_tag(v_x_3966_) == 0)
{
uint8_t v___x_3967_; 
v___x_3967_ = 0;
return v___x_3967_;
}
else
{
lean_object* v_key_3968_; lean_object* v_tail_3969_; uint8_t v___x_3970_; 
v_key_3968_ = lean_ctor_get(v_x_3966_, 0);
v_tail_3969_ = lean_ctor_get(v_x_3966_, 2);
v___x_3970_ = lean_name_eq(v_key_3968_, v_a_3965_);
if (v___x_3970_ == 0)
{
v_x_3966_ = v_tail_3969_;
goto _start;
}
else
{
return v___x_3970_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg___boxed(lean_object* v_a_3972_, lean_object* v_x_3973_){
_start:
{
uint8_t v_res_3974_; lean_object* v_r_3975_; 
v_res_3974_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_3972_, v_x_3973_);
lean_dec(v_x_3973_);
lean_dec(v_a_3972_);
v_r_3975_ = lean_box(v_res_3974_);
return v_r_3975_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(lean_object* v_a_3976_, lean_object* v_x_3977_){
_start:
{
if (lean_obj_tag(v_x_3977_) == 0)
{
return v_x_3977_;
}
else
{
lean_object* v_key_3978_; lean_object* v_value_3979_; lean_object* v_tail_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_3989_; 
v_key_3978_ = lean_ctor_get(v_x_3977_, 0);
v_value_3979_ = lean_ctor_get(v_x_3977_, 1);
v_tail_3980_ = lean_ctor_get(v_x_3977_, 2);
v_isSharedCheck_3989_ = !lean_is_exclusive(v_x_3977_);
if (v_isSharedCheck_3989_ == 0)
{
v___x_3982_ = v_x_3977_;
v_isShared_3983_ = v_isSharedCheck_3989_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_tail_3980_);
lean_inc(v_value_3979_);
lean_inc(v_key_3978_);
lean_dec(v_x_3977_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_3989_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
uint8_t v___x_3984_; 
v___x_3984_ = lean_name_eq(v_key_3978_, v_a_3976_);
if (v___x_3984_ == 0)
{
lean_object* v___x_3985_; lean_object* v___x_3987_; 
v___x_3985_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_3976_, v_tail_3980_);
if (v_isShared_3983_ == 0)
{
lean_ctor_set(v___x_3982_, 2, v___x_3985_);
v___x_3987_ = v___x_3982_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v_key_3978_);
lean_ctor_set(v_reuseFailAlloc_3988_, 1, v_value_3979_);
lean_ctor_set(v_reuseFailAlloc_3988_, 2, v___x_3985_);
v___x_3987_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
return v___x_3987_;
}
}
else
{
lean_del_object(v___x_3982_);
lean_dec(v_value_3979_);
lean_dec(v_key_3978_);
return v_tail_3980_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg___boxed(lean_object* v_a_3990_, lean_object* v_x_3991_){
_start:
{
lean_object* v_res_3992_; 
v_res_3992_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_3990_, v_x_3991_);
lean_dec(v_a_3990_);
return v_res_3992_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(lean_object* v_m_3993_, lean_object* v_a_3994_){
_start:
{
lean_object* v_size_3995_; lean_object* v_buckets_3996_; lean_object* v___x_3997_; uint64_t v___y_3999_; 
v_size_3995_ = lean_ctor_get(v_m_3993_, 0);
v_buckets_3996_ = lean_ctor_get(v_m_3993_, 1);
v___x_3997_ = lean_array_get_size(v_buckets_3996_);
if (lean_obj_tag(v_a_3994_) == 0)
{
uint64_t v___x_4028_; 
v___x_4028_ = 1723ULL;
v___y_3999_ = v___x_4028_;
goto v___jp_3998_;
}
else
{
uint64_t v_hash_4029_; 
v_hash_4029_ = lean_ctor_get_uint64(v_a_3994_, sizeof(void*)*2);
v___y_3999_ = v_hash_4029_;
goto v___jp_3998_;
}
v___jp_3998_:
{
uint64_t v___x_4000_; uint64_t v___x_4001_; uint64_t v_fold_4002_; uint64_t v___x_4003_; uint64_t v___x_4004_; uint64_t v___x_4005_; size_t v___x_4006_; size_t v___x_4007_; size_t v___x_4008_; size_t v___x_4009_; size_t v___x_4010_; lean_object* v_bkt_4011_; uint8_t v___x_4012_; 
v___x_4000_ = 32ULL;
v___x_4001_ = lean_uint64_shift_right(v___y_3999_, v___x_4000_);
v_fold_4002_ = lean_uint64_xor(v___y_3999_, v___x_4001_);
v___x_4003_ = 16ULL;
v___x_4004_ = lean_uint64_shift_right(v_fold_4002_, v___x_4003_);
v___x_4005_ = lean_uint64_xor(v_fold_4002_, v___x_4004_);
v___x_4006_ = lean_uint64_to_usize(v___x_4005_);
v___x_4007_ = lean_usize_of_nat(v___x_3997_);
v___x_4008_ = ((size_t)1ULL);
v___x_4009_ = lean_usize_sub(v___x_4007_, v___x_4008_);
v___x_4010_ = lean_usize_land(v___x_4006_, v___x_4009_);
v_bkt_4011_ = lean_array_uget_borrowed(v_buckets_3996_, v___x_4010_);
v___x_4012_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_3994_, v_bkt_4011_);
if (v___x_4012_ == 0)
{
return v_m_3993_;
}
else
{
lean_object* v___x_4014_; uint8_t v_isShared_4015_; uint8_t v_isSharedCheck_4025_; 
lean_inc(v_bkt_4011_);
lean_inc_ref(v_buckets_3996_);
lean_inc(v_size_3995_);
v_isSharedCheck_4025_ = !lean_is_exclusive(v_m_3993_);
if (v_isSharedCheck_4025_ == 0)
{
lean_object* v_unused_4026_; lean_object* v_unused_4027_; 
v_unused_4026_ = lean_ctor_get(v_m_3993_, 1);
lean_dec(v_unused_4026_);
v_unused_4027_ = lean_ctor_get(v_m_3993_, 0);
lean_dec(v_unused_4027_);
v___x_4014_ = v_m_3993_;
v_isShared_4015_ = v_isSharedCheck_4025_;
goto v_resetjp_4013_;
}
else
{
lean_dec(v_m_3993_);
v___x_4014_ = lean_box(0);
v_isShared_4015_ = v_isSharedCheck_4025_;
goto v_resetjp_4013_;
}
v_resetjp_4013_:
{
lean_object* v___x_4016_; lean_object* v_buckets_x27_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4023_; 
v___x_4016_ = lean_box(0);
v_buckets_x27_4017_ = lean_array_uset(v_buckets_3996_, v___x_4010_, v___x_4016_);
v___x_4018_ = lean_unsigned_to_nat(1u);
v___x_4019_ = lean_nat_sub(v_size_3995_, v___x_4018_);
lean_dec(v_size_3995_);
v___x_4020_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_3994_, v_bkt_4011_);
v___x_4021_ = lean_array_uset(v_buckets_x27_4017_, v___x_4010_, v___x_4020_);
if (v_isShared_4015_ == 0)
{
lean_ctor_set(v___x_4014_, 1, v___x_4021_);
lean_ctor_set(v___x_4014_, 0, v___x_4019_);
v___x_4023_ = v___x_4014_;
goto v_reusejp_4022_;
}
else
{
lean_object* v_reuseFailAlloc_4024_; 
v_reuseFailAlloc_4024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4024_, 0, v___x_4019_);
lean_ctor_set(v_reuseFailAlloc_4024_, 1, v___x_4021_);
v___x_4023_ = v_reuseFailAlloc_4024_;
goto v_reusejp_4022_;
}
v_reusejp_4022_:
{
return v___x_4023_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___boxed(lean_object* v_m_4030_, lean_object* v_a_4031_){
_start:
{
lean_object* v_res_4032_; 
v_res_4032_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_m_4030_, v_a_4031_);
lean_dec(v_a_4031_);
return v_res_4032_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(lean_object* v_m_4033_, lean_object* v_a_4034_){
_start:
{
lean_object* v_buckets_4035_; lean_object* v___x_4036_; uint64_t v___y_4038_; 
v_buckets_4035_ = lean_ctor_get(v_m_4033_, 1);
v___x_4036_ = lean_array_get_size(v_buckets_4035_);
if (lean_obj_tag(v_a_4034_) == 0)
{
uint64_t v___x_4052_; 
v___x_4052_ = 1723ULL;
v___y_4038_ = v___x_4052_;
goto v___jp_4037_;
}
else
{
uint64_t v_hash_4053_; 
v_hash_4053_ = lean_ctor_get_uint64(v_a_4034_, sizeof(void*)*2);
v___y_4038_ = v_hash_4053_;
goto v___jp_4037_;
}
v___jp_4037_:
{
uint64_t v___x_4039_; uint64_t v___x_4040_; uint64_t v_fold_4041_; uint64_t v___x_4042_; uint64_t v___x_4043_; uint64_t v___x_4044_; size_t v___x_4045_; size_t v___x_4046_; size_t v___x_4047_; size_t v___x_4048_; size_t v___x_4049_; lean_object* v___x_4050_; uint8_t v___x_4051_; 
v___x_4039_ = 32ULL;
v___x_4040_ = lean_uint64_shift_right(v___y_4038_, v___x_4039_);
v_fold_4041_ = lean_uint64_xor(v___y_4038_, v___x_4040_);
v___x_4042_ = 16ULL;
v___x_4043_ = lean_uint64_shift_right(v_fold_4041_, v___x_4042_);
v___x_4044_ = lean_uint64_xor(v_fold_4041_, v___x_4043_);
v___x_4045_ = lean_uint64_to_usize(v___x_4044_);
v___x_4046_ = lean_usize_of_nat(v___x_4036_);
v___x_4047_ = ((size_t)1ULL);
v___x_4048_ = lean_usize_sub(v___x_4046_, v___x_4047_);
v___x_4049_ = lean_usize_land(v___x_4045_, v___x_4048_);
v___x_4050_ = lean_array_uget_borrowed(v_buckets_4035_, v___x_4049_);
v___x_4051_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_4034_, v___x_4050_);
return v___x_4051_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg___boxed(lean_object* v_m_4054_, lean_object* v_a_4055_){
_start:
{
uint8_t v_res_4056_; lean_object* v_r_4057_; 
v_res_4056_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(v_m_4054_, v_a_4055_);
lean_dec(v_a_4055_);
lean_dec_ref(v_m_4054_);
v_r_4057_ = lean_box(v_res_4056_);
return v_r_4057_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(lean_object* v_start_4058_, lean_object* v_as_4059_, size_t v_i_4060_, size_t v_stop_4061_, lean_object* v_b_4062_){
_start:
{
uint8_t v___x_4063_; 
v___x_4063_ = lean_usize_dec_eq(v_i_4060_, v_stop_4061_);
if (v___x_4063_ == 0)
{
size_t v___x_4064_; size_t v___x_4065_; lean_object* v___x_4066_; 
v___x_4064_ = ((size_t)1ULL);
v___x_4065_ = lean_usize_sub(v_i_4060_, v___x_4064_);
v___x_4066_ = lean_array_uget(v_as_4059_, v___x_4065_);
if (lean_obj_tag(v___x_4066_) == 0)
{
v_i_4060_ = v___x_4065_;
goto _start;
}
else
{
lean_object* v_val_4068_; lean_object* v___x_4070_; uint8_t v_isShared_4071_; uint8_t v_isSharedCheck_4102_; 
v_val_4068_ = lean_ctor_get(v___x_4066_, 0);
v_isSharedCheck_4102_ = !lean_is_exclusive(v___x_4066_);
if (v_isSharedCheck_4102_ == 0)
{
v___x_4070_ = v___x_4066_;
v_isShared_4071_ = v_isSharedCheck_4102_;
goto v_resetjp_4069_;
}
else
{
lean_inc(v_val_4068_);
lean_dec(v___x_4066_);
v___x_4070_ = lean_box(0);
v_isShared_4071_ = v_isSharedCheck_4102_;
goto v_resetjp_4069_;
}
v_resetjp_4069_:
{
lean_object* v_fst_4072_; lean_object* v_snd_4073_; lean_object* v___y_4075_; lean_object* v___y_4091_; lean_object* v_size_4097_; lean_object* v___x_4098_; uint8_t v___x_4099_; 
v_fst_4072_ = lean_ctor_get(v_b_4062_, 0);
v_snd_4073_ = lean_ctor_get(v_b_4062_, 1);
v_size_4097_ = lean_ctor_get(v_fst_4072_, 0);
v___x_4098_ = lean_unsigned_to_nat(0u);
v___x_4099_ = lean_nat_dec_eq(v_size_4097_, v___x_4098_);
if (v___x_4099_ == 0)
{
lean_object* v_index_4100_; 
v_index_4100_ = lean_ctor_get(v_val_4068_, 0);
lean_inc(v_index_4100_);
v___y_4091_ = v_index_4100_;
goto v___jp_4090_;
}
else
{
lean_object* v___x_4101_; 
lean_inc(v_snd_4073_);
lean_del_object(v___x_4070_);
lean_dec(v_val_4068_);
lean_dec_ref(v_b_4062_);
v___x_4101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4101_, 0, v_snd_4073_);
return v___x_4101_;
}
v___jp_4074_:
{
uint8_t v___x_4076_; 
v___x_4076_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(v_fst_4072_, v___y_4075_);
if (v___x_4076_ == 0)
{
lean_dec(v___y_4075_);
lean_dec(v_val_4068_);
v_i_4060_ = v___x_4065_;
goto _start;
}
else
{
lean_object* v___x_4079_; uint8_t v_isShared_4080_; uint8_t v_isSharedCheck_4087_; 
lean_inc(v_snd_4073_);
lean_inc(v_fst_4072_);
v_isSharedCheck_4087_ = !lean_is_exclusive(v_b_4062_);
if (v_isSharedCheck_4087_ == 0)
{
lean_object* v_unused_4088_; lean_object* v_unused_4089_; 
v_unused_4088_ = lean_ctor_get(v_b_4062_, 1);
lean_dec(v_unused_4088_);
v_unused_4089_ = lean_ctor_get(v_b_4062_, 0);
lean_dec(v_unused_4089_);
v___x_4079_ = v_b_4062_;
v_isShared_4080_ = v_isSharedCheck_4087_;
goto v_resetjp_4078_;
}
else
{
lean_dec(v_b_4062_);
v___x_4079_ = lean_box(0);
v_isShared_4080_ = v_isSharedCheck_4087_;
goto v_resetjp_4078_;
}
v_resetjp_4078_:
{
lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4084_; 
v___x_4081_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_fst_4072_, v___y_4075_);
lean_dec(v___y_4075_);
v___x_4082_ = lean_array_push(v_snd_4073_, v_val_4068_);
if (v_isShared_4080_ == 0)
{
lean_ctor_set(v___x_4079_, 1, v___x_4082_);
lean_ctor_set(v___x_4079_, 0, v___x_4081_);
v___x_4084_ = v___x_4079_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4086_; 
v_reuseFailAlloc_4086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4086_, 0, v___x_4081_);
lean_ctor_set(v_reuseFailAlloc_4086_, 1, v___x_4082_);
v___x_4084_ = v_reuseFailAlloc_4086_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
v_i_4060_ = v___x_4065_;
v_b_4062_ = v___x_4084_;
goto _start;
}
}
}
}
v___jp_4090_:
{
uint8_t v___x_4092_; 
v___x_4092_ = lean_nat_dec_lt(v___y_4091_, v_start_4058_);
lean_dec(v___y_4091_);
if (v___x_4092_ == 0)
{
lean_object* v_userName_4093_; 
lean_del_object(v___x_4070_);
v_userName_4093_ = lean_ctor_get(v_val_4068_, 2);
lean_inc(v_userName_4093_);
v___y_4075_ = v_userName_4093_;
goto v___jp_4074_;
}
else
{
lean_object* v___x_4095_; 
lean_inc(v_snd_4073_);
lean_dec(v_val_4068_);
lean_dec_ref(v_b_4062_);
if (v_isShared_4071_ == 0)
{
lean_ctor_set_tag(v___x_4070_, 0);
lean_ctor_set(v___x_4070_, 0, v_snd_4073_);
v___x_4095_ = v___x_4070_;
goto v_reusejp_4094_;
}
else
{
lean_object* v_reuseFailAlloc_4096_; 
v_reuseFailAlloc_4096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4096_, 0, v_snd_4073_);
v___x_4095_ = v_reuseFailAlloc_4096_;
goto v_reusejp_4094_;
}
v_reusejp_4094_:
{
return v___x_4095_;
}
}
}
}
}
}
else
{
lean_object* v___x_4103_; 
v___x_4103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4103_, 0, v_b_4062_);
return v___x_4103_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_start_4104_, lean_object* v_as_4105_, lean_object* v_i_4106_, lean_object* v_stop_4107_, lean_object* v_b_4108_){
_start:
{
size_t v_i_boxed_4109_; size_t v_stop_boxed_4110_; lean_object* v_res_4111_; 
v_i_boxed_4109_ = lean_unbox_usize(v_i_4106_);
lean_dec(v_i_4106_);
v_stop_boxed_4110_ = lean_unbox_usize(v_stop_4107_);
lean_dec(v_stop_4107_);
v_res_4111_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4104_, v_as_4105_, v_i_boxed_4109_, v_stop_boxed_4110_, v_b_4108_);
lean_dec_ref(v_as_4105_);
lean_dec(v_start_4104_);
return v_res_4111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(lean_object* v_start_4112_, lean_object* v_x_4113_, lean_object* v_x_4114_){
_start:
{
if (lean_obj_tag(v_x_4113_) == 0)
{
lean_object* v_cs_4115_; lean_object* v___x_4117_; uint8_t v_isShared_4118_; uint8_t v_isSharedCheck_4128_; 
v_cs_4115_ = lean_ctor_get(v_x_4113_, 0);
v_isSharedCheck_4128_ = !lean_is_exclusive(v_x_4113_);
if (v_isSharedCheck_4128_ == 0)
{
v___x_4117_ = v_x_4113_;
v_isShared_4118_ = v_isSharedCheck_4128_;
goto v_resetjp_4116_;
}
else
{
lean_inc(v_cs_4115_);
lean_dec(v_x_4113_);
v___x_4117_ = lean_box(0);
v_isShared_4118_ = v_isSharedCheck_4128_;
goto v_resetjp_4116_;
}
v_resetjp_4116_:
{
lean_object* v___x_4119_; lean_object* v___x_4120_; uint8_t v___x_4121_; 
v___x_4119_ = lean_array_get_size(v_cs_4115_);
v___x_4120_ = lean_unsigned_to_nat(0u);
v___x_4121_ = lean_nat_dec_lt(v___x_4120_, v___x_4119_);
if (v___x_4121_ == 0)
{
lean_object* v___x_4123_; 
lean_dec_ref(v_cs_4115_);
if (v_isShared_4118_ == 0)
{
lean_ctor_set_tag(v___x_4117_, 1);
lean_ctor_set(v___x_4117_, 0, v_x_4114_);
v___x_4123_ = v___x_4117_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4124_; 
v_reuseFailAlloc_4124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4124_, 0, v_x_4114_);
v___x_4123_ = v_reuseFailAlloc_4124_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
return v___x_4123_;
}
}
else
{
size_t v___x_4125_; size_t v___x_4126_; lean_object* v___x_4127_; 
lean_del_object(v___x_4117_);
v___x_4125_ = lean_usize_of_nat(v___x_4119_);
v___x_4126_ = ((size_t)0ULL);
v___x_4127_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(v_start_4112_, v_cs_4115_, v___x_4125_, v___x_4126_, v_x_4114_);
lean_dec_ref(v_cs_4115_);
return v___x_4127_;
}
}
}
else
{
lean_object* v_vs_4129_; lean_object* v___x_4131_; uint8_t v_isShared_4132_; uint8_t v_isSharedCheck_4142_; 
v_vs_4129_ = lean_ctor_get(v_x_4113_, 0);
v_isSharedCheck_4142_ = !lean_is_exclusive(v_x_4113_);
if (v_isSharedCheck_4142_ == 0)
{
v___x_4131_ = v_x_4113_;
v_isShared_4132_ = v_isSharedCheck_4142_;
goto v_resetjp_4130_;
}
else
{
lean_inc(v_vs_4129_);
lean_dec(v_x_4113_);
v___x_4131_ = lean_box(0);
v_isShared_4132_ = v_isSharedCheck_4142_;
goto v_resetjp_4130_;
}
v_resetjp_4130_:
{
lean_object* v___x_4133_; lean_object* v___x_4134_; uint8_t v___x_4135_; 
v___x_4133_ = lean_array_get_size(v_vs_4129_);
v___x_4134_ = lean_unsigned_to_nat(0u);
v___x_4135_ = lean_nat_dec_lt(v___x_4134_, v___x_4133_);
if (v___x_4135_ == 0)
{
lean_object* v___x_4137_; 
lean_dec_ref(v_vs_4129_);
if (v_isShared_4132_ == 0)
{
lean_ctor_set(v___x_4131_, 0, v_x_4114_);
v___x_4137_ = v___x_4131_;
goto v_reusejp_4136_;
}
else
{
lean_object* v_reuseFailAlloc_4138_; 
v_reuseFailAlloc_4138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4138_, 0, v_x_4114_);
v___x_4137_ = v_reuseFailAlloc_4138_;
goto v_reusejp_4136_;
}
v_reusejp_4136_:
{
return v___x_4137_;
}
}
else
{
size_t v___x_4139_; size_t v___x_4140_; lean_object* v___x_4141_; 
lean_del_object(v___x_4131_);
v___x_4139_ = lean_usize_of_nat(v___x_4133_);
v___x_4140_ = ((size_t)0ULL);
v___x_4141_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4112_, v_vs_4129_, v___x_4139_, v___x_4140_, v_x_4114_);
lean_dec_ref(v_vs_4129_);
return v___x_4141_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_start_4143_, lean_object* v_as_4144_, size_t v_i_4145_, size_t v_stop_4146_, lean_object* v_b_4147_){
_start:
{
uint8_t v___x_4148_; 
v___x_4148_ = lean_usize_dec_eq(v_i_4145_, v_stop_4146_);
if (v___x_4148_ == 0)
{
size_t v___x_4149_; size_t v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; 
v___x_4149_ = ((size_t)1ULL);
v___x_4150_ = lean_usize_sub(v_i_4145_, v___x_4149_);
v___x_4151_ = lean_array_uget_borrowed(v_as_4144_, v___x_4150_);
lean_inc(v___x_4151_);
v___x_4152_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4143_, v___x_4151_, v_b_4147_);
if (lean_obj_tag(v___x_4152_) == 0)
{
return v___x_4152_;
}
else
{
lean_object* v_a_4153_; 
v_a_4153_ = lean_ctor_get(v___x_4152_, 0);
lean_inc(v_a_4153_);
lean_dec_ref_known(v___x_4152_, 1);
v_i_4145_ = v___x_4150_;
v_b_4147_ = v_a_4153_;
goto _start;
}
}
else
{
lean_object* v___x_4155_; 
v___x_4155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4155_, 0, v_b_4147_);
return v___x_4155_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_start_4156_, lean_object* v_as_4157_, lean_object* v_i_4158_, lean_object* v_stop_4159_, lean_object* v_b_4160_){
_start:
{
size_t v_i_boxed_4161_; size_t v_stop_boxed_4162_; lean_object* v_res_4163_; 
v_i_boxed_4161_ = lean_unbox_usize(v_i_4158_);
lean_dec(v_i_4158_);
v_stop_boxed_4162_ = lean_unbox_usize(v_stop_4159_);
lean_dec(v_stop_4159_);
v_res_4163_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(v_start_4156_, v_as_4157_, v_i_boxed_4161_, v_stop_boxed_4162_, v_b_4160_);
lean_dec_ref(v_as_4157_);
lean_dec(v_start_4156_);
return v_res_4163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_start_4164_, lean_object* v_x_4165_, lean_object* v_x_4166_){
_start:
{
lean_object* v_res_4167_; 
v_res_4167_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4164_, v_x_4165_, v_x_4166_);
lean_dec(v_start_4164_);
return v_res_4167_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(lean_object* v_start_4168_, lean_object* v_t_4169_, lean_object* v_init_4170_){
_start:
{
lean_object* v_root_4171_; lean_object* v_tail_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; uint8_t v___x_4175_; 
v_root_4171_ = lean_ctor_get(v_t_4169_, 0);
lean_inc_ref(v_root_4171_);
v_tail_4172_ = lean_ctor_get(v_t_4169_, 1);
lean_inc_ref(v_tail_4172_);
lean_dec_ref(v_t_4169_);
v___x_4173_ = lean_array_get_size(v_tail_4172_);
v___x_4174_ = lean_unsigned_to_nat(0u);
v___x_4175_ = lean_nat_dec_lt(v___x_4174_, v___x_4173_);
if (v___x_4175_ == 0)
{
lean_object* v___x_4176_; 
lean_dec_ref(v_tail_4172_);
v___x_4176_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4168_, v_root_4171_, v_init_4170_);
return v___x_4176_;
}
else
{
size_t v___x_4177_; size_t v___x_4178_; lean_object* v___x_4179_; 
v___x_4177_ = lean_usize_of_nat(v___x_4173_);
v___x_4178_ = ((size_t)0ULL);
v___x_4179_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4168_, v_tail_4172_, v___x_4177_, v___x_4178_, v_init_4170_);
lean_dec_ref(v_tail_4172_);
if (lean_obj_tag(v___x_4179_) == 0)
{
lean_dec_ref(v_root_4171_);
return v___x_4179_;
}
else
{
lean_object* v_a_4180_; lean_object* v___x_4181_; 
v_a_4180_ = lean_ctor_get(v___x_4179_, 0);
lean_inc(v_a_4180_);
lean_dec_ref_known(v___x_4179_, 1);
v___x_4181_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4168_, v_root_4171_, v_a_4180_);
return v___x_4181_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg___boxed(lean_object* v_start_4182_, lean_object* v_t_4183_, lean_object* v_init_4184_){
_start:
{
lean_object* v_res_4185_; 
v_res_4185_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(v_start_4182_, v_t_4183_, v_init_4184_);
lean_dec(v_start_4182_);
return v_res_4185_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(lean_object* v_start_4186_, lean_object* v_lctx_4187_, lean_object* v_init_4188_){
_start:
{
lean_object* v_decls_4189_; lean_object* v___x_4190_; 
v_decls_4189_ = lean_ctor_get(v_lctx_4187_, 1);
lean_inc_ref(v_decls_4189_);
lean_dec_ref(v_lctx_4187_);
v___x_4190_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(v_start_4186_, v_decls_4189_, v_init_4188_);
return v___x_4190_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg___boxed(lean_object* v_start_4191_, lean_object* v_lctx_4192_, lean_object* v_init_4193_){
_start:
{
lean_object* v_res_4194_; 
v_res_4194_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(v_start_4191_, v_lctx_4192_, v_init_4193_);
lean_dec(v_start_4191_);
return v_res_4194_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___redArg(lean_object* v_lctx_4197_, lean_object* v_userNames_4198_, lean_object* v_start_4199_){
_start:
{
lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; 
v___x_4200_ = ((lean_object*)(l_Lean_LocalContext_findFromUserNames___redArg___closed__0));
v___x_4201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4201_, 0, v_userNames_4198_);
lean_ctor_set(v___x_4201_, 1, v___x_4200_);
v___x_4202_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(v_start_4199_, v_lctx_4197_, v___x_4201_);
if (lean_obj_tag(v___x_4202_) == 0)
{
lean_object* v_a_4203_; lean_object* v___x_4204_; 
v_a_4203_ = lean_ctor_get(v___x_4202_, 0);
lean_inc(v_a_4203_);
lean_dec_ref_known(v___x_4202_, 1);
v___x_4204_ = l_Array_reverse___redArg(v_a_4203_);
return v___x_4204_;
}
else
{
lean_object* v_a_4205_; lean_object* v_snd_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; 
v_a_4205_ = lean_ctor_get(v___x_4202_, 0);
lean_inc(v_a_4205_);
lean_dec_ref_known(v___x_4202_, 1);
v_snd_4206_ = lean_ctor_get(v_a_4205_, 1);
lean_inc(v_snd_4206_);
lean_dec(v_a_4205_);
v___x_4207_ = l_Array_reverse___redArg(v_snd_4206_);
v___x_4208_ = l_Array_reverse___redArg(v___x_4207_);
return v___x_4208_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___redArg___boxed(lean_object* v_lctx_4209_, lean_object* v_userNames_4210_, lean_object* v_start_4211_){
_start:
{
lean_object* v_res_4212_; 
v_res_4212_ = l_Lean_LocalContext_findFromUserNames___redArg(v_lctx_4209_, v_userNames_4210_, v_start_4211_);
lean_dec(v_start_4211_);
return v_res_4212_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames(lean_object* v_00_u03b1_4213_, lean_object* v_lctx_4214_, lean_object* v_userNames_4215_, lean_object* v_start_4216_){
_start:
{
lean_object* v___x_4217_; 
v___x_4217_ = l_Lean_LocalContext_findFromUserNames___redArg(v_lctx_4214_, v_userNames_4215_, v_start_4216_);
return v___x_4217_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___boxed(lean_object* v_00_u03b1_4218_, lean_object* v_lctx_4219_, lean_object* v_userNames_4220_, lean_object* v_start_4221_){
_start:
{
lean_object* v_res_4222_; 
v_res_4222_ = l_Lean_LocalContext_findFromUserNames(v_00_u03b1_4218_, v_lctx_4219_, v_userNames_4220_, v_start_4221_);
lean_dec(v_start_4221_);
return v_res_4222_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0(lean_object* v_00_u03b2_4223_, lean_object* v_m_4224_, lean_object* v_a_4225_){
_start:
{
uint8_t v___x_4226_; 
v___x_4226_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(v_m_4224_, v_a_4225_);
return v___x_4226_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___boxed(lean_object* v_00_u03b2_4227_, lean_object* v_m_4228_, lean_object* v_a_4229_){
_start:
{
uint8_t v_res_4230_; lean_object* v_r_4231_; 
v_res_4230_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0(v_00_u03b2_4227_, v_m_4228_, v_a_4229_);
lean_dec(v_a_4229_);
lean_dec_ref(v_m_4228_);
v_r_4231_ = lean_box(v_res_4230_);
return v_r_4231_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1(lean_object* v_00_u03b2_4232_, lean_object* v_m_4233_, lean_object* v_a_4234_){
_start:
{
lean_object* v___x_4235_; 
v___x_4235_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_m_4233_, v_a_4234_);
return v___x_4235_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___boxed(lean_object* v_00_u03b2_4236_, lean_object* v_m_4237_, lean_object* v_a_4238_){
_start:
{
lean_object* v_res_4239_; 
v_res_4239_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1(v_00_u03b2_4236_, v_m_4237_, v_a_4238_);
lean_dec(v_a_4238_);
return v_res_4239_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2(lean_object* v_00_u03b1_4240_, lean_object* v_start_4241_, lean_object* v_lctx_4242_, lean_object* v_init_4243_){
_start:
{
lean_object* v___x_4244_; 
v___x_4244_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(v_start_4241_, v_lctx_4242_, v_init_4243_);
return v___x_4244_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___boxed(lean_object* v_00_u03b1_4245_, lean_object* v_start_4246_, lean_object* v_lctx_4247_, lean_object* v_init_4248_){
_start:
{
lean_object* v_res_4249_; 
v_res_4249_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2(v_00_u03b1_4245_, v_start_4246_, v_lctx_4247_, v_init_4248_);
lean_dec(v_start_4246_);
return v_res_4249_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0(lean_object* v_00_u03b2_4250_, lean_object* v_a_4251_, lean_object* v_x_4252_){
_start:
{
uint8_t v___x_4253_; 
v___x_4253_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_4251_, v_x_4252_);
return v___x_4253_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4254_, lean_object* v_a_4255_, lean_object* v_x_4256_){
_start:
{
uint8_t v_res_4257_; lean_object* v_r_4258_; 
v_res_4257_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0(v_00_u03b2_4254_, v_a_4255_, v_x_4256_);
lean_dec(v_x_4256_);
lean_dec(v_a_4255_);
v_r_4258_ = lean_box(v_res_4257_);
return v_r_4258_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2(lean_object* v_00_u03b2_4259_, lean_object* v_a_4260_, lean_object* v_x_4261_){
_start:
{
lean_object* v___x_4262_; 
v___x_4262_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_4260_, v_x_4261_);
return v___x_4262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4263_, lean_object* v_a_4264_, lean_object* v_x_4265_){
_start:
{
lean_object* v_res_4266_; 
v_res_4266_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2(v_00_u03b2_4263_, v_a_4264_, v_x_4265_);
lean_dec(v_a_4264_);
return v_res_4266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4(lean_object* v_00_u03b1_4267_, lean_object* v_start_4268_, lean_object* v_t_4269_, lean_object* v_init_4270_){
_start:
{
lean_object* v___x_4271_; 
v___x_4271_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(v_start_4268_, v_t_4269_, v_init_4270_);
return v___x_4271_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___boxed(lean_object* v_00_u03b1_4272_, lean_object* v_start_4273_, lean_object* v_t_4274_, lean_object* v_init_4275_){
_start:
{
lean_object* v_res_4276_; 
v_res_4276_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4(v_00_u03b1_4272_, v_start_4273_, v_t_4274_, v_init_4275_);
lean_dec(v_start_4273_);
return v_res_4276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5(lean_object* v_00_u03b1_4277_, lean_object* v_start_4278_, lean_object* v_x_4279_, lean_object* v_x_4280_){
_start:
{
lean_object* v___x_4281_; 
v___x_4281_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4278_, v_x_4279_, v_x_4280_);
return v___x_4281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b1_4282_, lean_object* v_start_4283_, lean_object* v_x_4284_, lean_object* v_x_4285_){
_start:
{
lean_object* v_res_4286_; 
v_res_4286_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5(v_00_u03b1_4282_, v_start_4283_, v_x_4284_, v_x_4285_);
lean_dec(v_start_4283_);
return v_res_4286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_4287_, lean_object* v_start_4288_, lean_object* v_as_4289_, size_t v_i_4290_, size_t v_stop_4291_, lean_object* v_b_4292_){
_start:
{
lean_object* v___x_4293_; 
v___x_4293_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4288_, v_as_4289_, v_i_4290_, v_stop_4291_, v_b_4292_);
return v___x_4293_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_4294_, lean_object* v_start_4295_, lean_object* v_as_4296_, lean_object* v_i_4297_, lean_object* v_stop_4298_, lean_object* v_b_4299_){
_start:
{
size_t v_i_boxed_4300_; size_t v_stop_boxed_4301_; lean_object* v_res_4302_; 
v_i_boxed_4300_ = lean_unbox_usize(v_i_4297_);
lean_dec(v_i_4297_);
v_stop_boxed_4301_ = lean_unbox_usize(v_stop_4298_);
lean_dec(v_stop_4298_);
v_res_4302_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6(v_00_u03b1_4294_, v_start_4295_, v_as_4296_, v_i_boxed_4300_, v_stop_boxed_4301_, v_b_4299_);
lean_dec_ref(v_as_4296_);
lean_dec(v_start_4295_);
return v_res_4302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b1_4303_, lean_object* v_start_4304_, lean_object* v_as_4305_, size_t v_i_4306_, size_t v_stop_4307_, lean_object* v_b_4308_){
_start:
{
lean_object* v___x_4309_; 
v___x_4309_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(v_start_4304_, v_as_4305_, v_i_4306_, v_stop_4307_, v_b_4308_);
return v___x_4309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___boxed(lean_object* v_00_u03b1_4310_, lean_object* v_start_4311_, lean_object* v_as_4312_, lean_object* v_i_4313_, lean_object* v_stop_4314_, lean_object* v_b_4315_){
_start:
{
size_t v_i_boxed_4316_; size_t v_stop_boxed_4317_; lean_object* v_res_4318_; 
v_i_boxed_4316_ = lean_unbox_usize(v_i_4313_);
lean_dec(v_i_4313_);
v_stop_boxed_4317_ = lean_unbox_usize(v_stop_4314_);
lean_dec(v_stop_4314_);
v_res_4318_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6(v_00_u03b1_4310_, v_start_4311_, v_as_4312_, v_i_boxed_4316_, v_stop_boxed_4317_, v_b_4315_);
lean_dec_ref(v_as_4312_);
lean_dec(v_start_4311_);
return v_res_4318_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLCtxOfMonadLift___redArg(lean_object* v_inst_4319_, lean_object* v_inst_4320_){
_start:
{
lean_object* v___x_4321_; 
v___x_4321_ = lean_apply_2(v_inst_4319_, lean_box(0), v_inst_4320_);
return v___x_4321_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLCtxOfMonadLift(lean_object* v_m_4322_, lean_object* v_n_4323_, lean_object* v_inst_4324_, lean_object* v_inst_4325_){
_start:
{
lean_object* v___x_4326_; 
v___x_4326_ = lean_apply_2(v_inst_4324_, lean_box(0), v_inst_4325_);
return v___x_4326_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__0(lean_object* v_toPure_4327_, lean_object* v_d_x3f_4328_, lean_object* v_b_4329_){
_start:
{
if (lean_obj_tag(v_d_x3f_4328_) == 0)
{
lean_object* v___x_4330_; lean_object* v___x_4331_; 
v___x_4330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4330_, 0, v_b_4329_);
v___x_4331_ = lean_apply_2(v_toPure_4327_, lean_box(0), v___x_4330_);
return v___x_4331_;
}
else
{
lean_object* v_val_4332_; lean_object* v___x_4334_; uint8_t v_isShared_4335_; uint8_t v_isSharedCheck_4347_; 
v_val_4332_ = lean_ctor_get(v_d_x3f_4328_, 0);
v_isSharedCheck_4347_ = !lean_is_exclusive(v_d_x3f_4328_);
if (v_isSharedCheck_4347_ == 0)
{
v___x_4334_ = v_d_x3f_4328_;
v_isShared_4335_ = v_isSharedCheck_4347_;
goto v_resetjp_4333_;
}
else
{
lean_inc(v_val_4332_);
lean_dec(v_d_x3f_4328_);
v___x_4334_ = lean_box(0);
v_isShared_4335_ = v_isSharedCheck_4347_;
goto v_resetjp_4333_;
}
v_resetjp_4333_:
{
uint8_t v___x_4336_; 
v___x_4336_ = l_Lean_LocalDecl_isImplementationDetail(v_val_4332_);
if (v___x_4336_ == 0)
{
lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4340_; 
v___x_4337_ = l_Lean_LocalDecl_toExpr(v_val_4332_);
v___x_4338_ = lean_array_push(v_b_4329_, v___x_4337_);
if (v_isShared_4335_ == 0)
{
lean_ctor_set(v___x_4334_, 0, v___x_4338_);
v___x_4340_ = v___x_4334_;
goto v_reusejp_4339_;
}
else
{
lean_object* v_reuseFailAlloc_4342_; 
v_reuseFailAlloc_4342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4342_, 0, v___x_4338_);
v___x_4340_ = v_reuseFailAlloc_4342_;
goto v_reusejp_4339_;
}
v_reusejp_4339_:
{
lean_object* v___x_4341_; 
v___x_4341_ = lean_apply_2(v_toPure_4327_, lean_box(0), v___x_4340_);
return v___x_4341_;
}
}
else
{
lean_object* v___x_4344_; 
lean_dec(v_val_4332_);
if (v_isShared_4335_ == 0)
{
lean_ctor_set(v___x_4334_, 0, v_b_4329_);
v___x_4344_ = v___x_4334_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4346_; 
v_reuseFailAlloc_4346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4346_, 0, v_b_4329_);
v___x_4344_ = v_reuseFailAlloc_4346_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
lean_object* v___x_4345_; 
v___x_4345_ = lean_apply_2(v_toPure_4327_, lean_box(0), v___x_4344_);
return v___x_4345_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__1(lean_object* v_toPure_4348_, lean_object* v_____s_4349_){
_start:
{
lean_object* v___x_4350_; 
v___x_4350_ = lean_apply_2(v_toPure_4348_, lean_box(0), v_____s_4349_);
return v___x_4350_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__2(lean_object* v_inst_4351_, lean_object* v_hs_4352_, lean_object* v___f_4353_, lean_object* v_toBind_4354_, lean_object* v___f_4355_, lean_object* v_____do__lift_4356_){
_start:
{
lean_object* v_decls_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; 
v_decls_4357_ = lean_ctor_get(v_____do__lift_4356_, 1);
v___x_4358_ = l_Lean_PersistentArray_forIn___redArg(v_inst_4351_, v_decls_4357_, v_hs_4352_, v___f_4353_);
v___x_4359_ = lean_apply_4(v_toBind_4354_, lean_box(0), lean_box(0), v___x_4358_, v___f_4355_);
return v___x_4359_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__2___boxed(lean_object* v_inst_4360_, lean_object* v_hs_4361_, lean_object* v___f_4362_, lean_object* v_toBind_4363_, lean_object* v___f_4364_, lean_object* v_____do__lift_4365_){
_start:
{
lean_object* v_res_4366_; 
v_res_4366_ = l_Lean_getLocalHyps___redArg___lam__2(v_inst_4360_, v_hs_4361_, v___f_4362_, v_toBind_4363_, v___f_4364_, v_____do__lift_4365_);
lean_dec_ref(v_____do__lift_4365_);
return v_res_4366_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg(lean_object* v_inst_4369_, lean_object* v_inst_4370_){
_start:
{
lean_object* v_toApplicative_4371_; lean_object* v_toBind_4372_; lean_object* v_toPure_4373_; lean_object* v_hs_4374_; lean_object* v___f_4375_; lean_object* v___f_4376_; lean_object* v___f_4377_; lean_object* v___x_4378_; 
v_toApplicative_4371_ = lean_ctor_get(v_inst_4369_, 0);
v_toBind_4372_ = lean_ctor_get(v_inst_4369_, 1);
lean_inc_n(v_toBind_4372_, 2);
v_toPure_4373_ = lean_ctor_get(v_toApplicative_4371_, 1);
v_hs_4374_ = ((lean_object*)(l_Lean_getLocalHyps___redArg___closed__0));
lean_inc_n(v_toPure_4373_, 2);
v___f_4375_ = lean_alloc_closure((void*)(l_Lean_getLocalHyps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4375_, 0, v_toPure_4373_);
v___f_4376_ = lean_alloc_closure((void*)(l_Lean_getLocalHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_4376_, 0, v_toPure_4373_);
v___f_4377_ = lean_alloc_closure((void*)(l_Lean_getLocalHyps___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_4377_, 0, v_inst_4369_);
lean_closure_set(v___f_4377_, 1, v_hs_4374_);
lean_closure_set(v___f_4377_, 2, v___f_4375_);
lean_closure_set(v___f_4377_, 3, v_toBind_4372_);
lean_closure_set(v___f_4377_, 4, v___f_4376_);
v___x_4378_ = lean_apply_4(v_toBind_4372_, lean_box(0), lean_box(0), v_inst_4370_, v___f_4377_);
return v___x_4378_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps(lean_object* v_m_4379_, lean_object* v_inst_4380_, lean_object* v_inst_4381_){
_start:
{
lean_object* v___x_4382_; 
v___x_4382_ = l_Lean_getLocalHyps___redArg(v_inst_4380_, v_inst_4381_);
return v___x_4382_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_replaceFVarId(lean_object* v_fvarId_4383_, lean_object* v_e_4384_, lean_object* v_d_4385_){
_start:
{
lean_object* v___y_4387_; lean_object* v_fvarId_4419_; 
v_fvarId_4419_ = lean_ctor_get(v_d_4385_, 1);
lean_inc(v_fvarId_4419_);
v___y_4387_ = v_fvarId_4419_;
goto v___jp_4386_;
v___jp_4386_:
{
uint8_t v___x_4388_; 
v___x_4388_ = l_Lean_instBEqFVarId_beq(v___y_4387_, v_fvarId_4383_);
lean_dec(v___y_4387_);
if (v___x_4388_ == 0)
{
if (lean_obj_tag(v_d_4385_) == 0)
{
lean_object* v_index_4389_; lean_object* v_fvarId_4390_; lean_object* v_userName_4391_; lean_object* v_type_4392_; uint8_t v_bi_4393_; uint8_t v_kind_4394_; lean_object* v___x_4396_; uint8_t v_isShared_4397_; uint8_t v_isSharedCheck_4402_; 
v_index_4389_ = lean_ctor_get(v_d_4385_, 0);
v_fvarId_4390_ = lean_ctor_get(v_d_4385_, 1);
v_userName_4391_ = lean_ctor_get(v_d_4385_, 2);
v_type_4392_ = lean_ctor_get(v_d_4385_, 3);
v_bi_4393_ = lean_ctor_get_uint8(v_d_4385_, sizeof(void*)*4);
v_kind_4394_ = lean_ctor_get_uint8(v_d_4385_, sizeof(void*)*4 + 1);
v_isSharedCheck_4402_ = !lean_is_exclusive(v_d_4385_);
if (v_isSharedCheck_4402_ == 0)
{
v___x_4396_ = v_d_4385_;
v_isShared_4397_ = v_isSharedCheck_4402_;
goto v_resetjp_4395_;
}
else
{
lean_inc(v_type_4392_);
lean_inc(v_userName_4391_);
lean_inc(v_fvarId_4390_);
lean_inc(v_index_4389_);
lean_dec(v_d_4385_);
v___x_4396_ = lean_box(0);
v_isShared_4397_ = v_isSharedCheck_4402_;
goto v_resetjp_4395_;
}
v_resetjp_4395_:
{
lean_object* v___x_4398_; lean_object* v___x_4400_; 
v___x_4398_ = l_Lean_Expr_replaceFVarId(v_type_4392_, v_fvarId_4383_, v_e_4384_);
lean_dec_ref(v_type_4392_);
if (v_isShared_4397_ == 0)
{
lean_ctor_set(v___x_4396_, 3, v___x_4398_);
v___x_4400_ = v___x_4396_;
goto v_reusejp_4399_;
}
else
{
lean_object* v_reuseFailAlloc_4401_; 
v_reuseFailAlloc_4401_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4401_, 0, v_index_4389_);
lean_ctor_set(v_reuseFailAlloc_4401_, 1, v_fvarId_4390_);
lean_ctor_set(v_reuseFailAlloc_4401_, 2, v_userName_4391_);
lean_ctor_set(v_reuseFailAlloc_4401_, 3, v___x_4398_);
lean_ctor_set_uint8(v_reuseFailAlloc_4401_, sizeof(void*)*4, v_bi_4393_);
lean_ctor_set_uint8(v_reuseFailAlloc_4401_, sizeof(void*)*4 + 1, v_kind_4394_);
v___x_4400_ = v_reuseFailAlloc_4401_;
goto v_reusejp_4399_;
}
v_reusejp_4399_:
{
return v___x_4400_;
}
}
}
else
{
lean_object* v_index_4403_; lean_object* v_fvarId_4404_; lean_object* v_userName_4405_; lean_object* v_type_4406_; lean_object* v_value_4407_; uint8_t v_nondep_4408_; uint8_t v_kind_4409_; lean_object* v___x_4411_; uint8_t v_isShared_4412_; uint8_t v_isSharedCheck_4418_; 
v_index_4403_ = lean_ctor_get(v_d_4385_, 0);
v_fvarId_4404_ = lean_ctor_get(v_d_4385_, 1);
v_userName_4405_ = lean_ctor_get(v_d_4385_, 2);
v_type_4406_ = lean_ctor_get(v_d_4385_, 3);
v_value_4407_ = lean_ctor_get(v_d_4385_, 4);
v_nondep_4408_ = lean_ctor_get_uint8(v_d_4385_, sizeof(void*)*5);
v_kind_4409_ = lean_ctor_get_uint8(v_d_4385_, sizeof(void*)*5 + 1);
v_isSharedCheck_4418_ = !lean_is_exclusive(v_d_4385_);
if (v_isSharedCheck_4418_ == 0)
{
v___x_4411_ = v_d_4385_;
v_isShared_4412_ = v_isSharedCheck_4418_;
goto v_resetjp_4410_;
}
else
{
lean_inc(v_value_4407_);
lean_inc(v_type_4406_);
lean_inc(v_userName_4405_);
lean_inc(v_fvarId_4404_);
lean_inc(v_index_4403_);
lean_dec(v_d_4385_);
v___x_4411_ = lean_box(0);
v_isShared_4412_ = v_isSharedCheck_4418_;
goto v_resetjp_4410_;
}
v_resetjp_4410_:
{
lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4416_; 
lean_inc(v_fvarId_4383_);
v___x_4413_ = l_Lean_Expr_replaceFVarId(v_type_4406_, v_fvarId_4383_, v_e_4384_);
lean_dec_ref(v_type_4406_);
v___x_4414_ = l_Lean_Expr_replaceFVarId(v_value_4407_, v_fvarId_4383_, v_e_4384_);
lean_dec_ref(v_value_4407_);
if (v_isShared_4412_ == 0)
{
lean_ctor_set(v___x_4411_, 4, v___x_4414_);
lean_ctor_set(v___x_4411_, 3, v___x_4413_);
v___x_4416_ = v___x_4411_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4417_; 
v_reuseFailAlloc_4417_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_4417_, 0, v_index_4403_);
lean_ctor_set(v_reuseFailAlloc_4417_, 1, v_fvarId_4404_);
lean_ctor_set(v_reuseFailAlloc_4417_, 2, v_userName_4405_);
lean_ctor_set(v_reuseFailAlloc_4417_, 3, v___x_4413_);
lean_ctor_set(v_reuseFailAlloc_4417_, 4, v___x_4414_);
lean_ctor_set_uint8(v_reuseFailAlloc_4417_, sizeof(void*)*5, v_nondep_4408_);
lean_ctor_set_uint8(v_reuseFailAlloc_4417_, sizeof(void*)*5 + 1, v_kind_4409_);
v___x_4416_ = v_reuseFailAlloc_4417_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
return v___x_4416_;
}
}
}
}
else
{
lean_dec(v_fvarId_4383_);
return v_d_4385_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_replaceFVarId___boxed(lean_object* v_fvarId_4420_, lean_object* v_e_4421_, lean_object* v_d_4422_){
_start:
{
lean_object* v_res_4423_; 
v_res_4423_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_4420_, v_e_4421_, v_d_4422_);
lean_dec_ref(v_e_4421_);
return v_res_4423_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId___lam__0(lean_object* v_fvarId_4424_, lean_object* v_e_4425_, lean_object* v_x_4426_){
_start:
{
lean_object* v___x_4427_; 
v___x_4427_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_4424_, v_e_4425_, v_x_4426_);
return v___x_4427_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId___lam__0___boxed(lean_object* v_fvarId_4428_, lean_object* v_e_4429_, lean_object* v_x_4430_){
_start:
{
lean_object* v_res_4431_; 
v_res_4431_ = l_Lean_LocalContext_replaceFVarId___lam__0(v_fvarId_4428_, v_e_4429_, v_x_4430_);
lean_dec_ref(v_e_4429_);
return v_res_4431_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(lean_object* v_fvarId_4432_, lean_object* v_e_4433_, size_t v_sz_4434_, size_t v_i_4435_, lean_object* v_bs_4436_){
_start:
{
uint8_t v___x_4437_; 
v___x_4437_ = lean_usize_dec_lt(v_i_4435_, v_sz_4434_);
if (v___x_4437_ == 0)
{
lean_dec(v_fvarId_4432_);
return v_bs_4436_;
}
else
{
lean_object* v_v_4438_; lean_object* v___x_4439_; lean_object* v_bs_x27_4440_; lean_object* v___y_4442_; 
v_v_4438_ = lean_array_uget(v_bs_4436_, v_i_4435_);
v___x_4439_ = lean_unsigned_to_nat(0u);
v_bs_x27_4440_ = lean_array_uset(v_bs_4436_, v_i_4435_, v___x_4439_);
if (lean_obj_tag(v_v_4438_) == 0)
{
v___y_4442_ = v_v_4438_;
goto v___jp_4441_;
}
else
{
lean_object* v_val_4447_; lean_object* v___x_4449_; uint8_t v_isShared_4450_; uint8_t v_isSharedCheck_4455_; 
v_val_4447_ = lean_ctor_get(v_v_4438_, 0);
v_isSharedCheck_4455_ = !lean_is_exclusive(v_v_4438_);
if (v_isSharedCheck_4455_ == 0)
{
v___x_4449_ = v_v_4438_;
v_isShared_4450_ = v_isSharedCheck_4455_;
goto v_resetjp_4448_;
}
else
{
lean_inc(v_val_4447_);
lean_dec(v_v_4438_);
v___x_4449_ = lean_box(0);
v_isShared_4450_ = v_isSharedCheck_4455_;
goto v_resetjp_4448_;
}
v_resetjp_4448_:
{
lean_object* v___x_4451_; lean_object* v___x_4453_; 
lean_inc(v_fvarId_4432_);
v___x_4451_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_4432_, v_e_4433_, v_val_4447_);
if (v_isShared_4450_ == 0)
{
lean_ctor_set(v___x_4449_, 0, v___x_4451_);
v___x_4453_ = v___x_4449_;
goto v_reusejp_4452_;
}
else
{
lean_object* v_reuseFailAlloc_4454_; 
v_reuseFailAlloc_4454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4454_, 0, v___x_4451_);
v___x_4453_ = v_reuseFailAlloc_4454_;
goto v_reusejp_4452_;
}
v_reusejp_4452_:
{
v___y_4442_ = v___x_4453_;
goto v___jp_4441_;
}
}
}
v___jp_4441_:
{
size_t v___x_4443_; size_t v___x_4444_; lean_object* v___x_4445_; 
v___x_4443_ = ((size_t)1ULL);
v___x_4444_ = lean_usize_add(v_i_4435_, v___x_4443_);
v___x_4445_ = lean_array_uset(v_bs_x27_4440_, v_i_4435_, v___y_4442_);
v_i_4435_ = v___x_4444_;
v_bs_4436_ = v___x_4445_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3___boxed(lean_object* v_fvarId_4456_, lean_object* v_e_4457_, lean_object* v_sz_4458_, lean_object* v_i_4459_, lean_object* v_bs_4460_){
_start:
{
size_t v_sz_boxed_4461_; size_t v_i_boxed_4462_; lean_object* v_res_4463_; 
v_sz_boxed_4461_ = lean_unbox_usize(v_sz_4458_);
lean_dec(v_sz_4458_);
v_i_boxed_4462_ = lean_unbox_usize(v_i_4459_);
lean_dec(v_i_4459_);
v_res_4463_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(v_fvarId_4456_, v_e_4457_, v_sz_boxed_4461_, v_i_boxed_4462_, v_bs_4460_);
lean_dec_ref(v_e_4457_);
return v_res_4463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(lean_object* v_fvarId_4464_, lean_object* v_e_4465_, size_t v_sz_4466_, size_t v_i_4467_, lean_object* v_bs_4468_){
_start:
{
uint8_t v___x_4469_; 
v___x_4469_ = lean_usize_dec_lt(v_i_4467_, v_sz_4466_);
if (v___x_4469_ == 0)
{
lean_dec(v_fvarId_4464_);
return v_bs_4468_;
}
else
{
lean_object* v_v_4470_; lean_object* v___x_4471_; lean_object* v_bs_x27_4472_; lean_object* v___x_4473_; size_t v___x_4474_; size_t v___x_4475_; lean_object* v___x_4476_; 
v_v_4470_ = lean_array_uget(v_bs_4468_, v_i_4467_);
v___x_4471_ = lean_unsigned_to_nat(0u);
v_bs_x27_4472_ = lean_array_uset(v_bs_4468_, v_i_4467_, v___x_4471_);
lean_inc(v_fvarId_4464_);
v___x_4473_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(v_fvarId_4464_, v_e_4465_, v_v_4470_);
v___x_4474_ = ((size_t)1ULL);
v___x_4475_ = lean_usize_add(v_i_4467_, v___x_4474_);
v___x_4476_ = lean_array_uset(v_bs_x27_4472_, v_i_4467_, v___x_4473_);
v_i_4467_ = v___x_4475_;
v_bs_4468_ = v___x_4476_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(lean_object* v_fvarId_4478_, lean_object* v_e_4479_, lean_object* v_x_4480_){
_start:
{
if (lean_obj_tag(v_x_4480_) == 0)
{
lean_object* v_cs_4481_; lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4491_; 
v_cs_4481_ = lean_ctor_get(v_x_4480_, 0);
v_isSharedCheck_4491_ = !lean_is_exclusive(v_x_4480_);
if (v_isSharedCheck_4491_ == 0)
{
v___x_4483_ = v_x_4480_;
v_isShared_4484_ = v_isSharedCheck_4491_;
goto v_resetjp_4482_;
}
else
{
lean_inc(v_cs_4481_);
lean_dec(v_x_4480_);
v___x_4483_ = lean_box(0);
v_isShared_4484_ = v_isSharedCheck_4491_;
goto v_resetjp_4482_;
}
v_resetjp_4482_:
{
size_t v_sz_4485_; size_t v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4489_; 
v_sz_4485_ = lean_array_size(v_cs_4481_);
v___x_4486_ = ((size_t)0ULL);
v___x_4487_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(v_fvarId_4478_, v_e_4479_, v_sz_4485_, v___x_4486_, v_cs_4481_);
if (v_isShared_4484_ == 0)
{
lean_ctor_set(v___x_4483_, 0, v___x_4487_);
v___x_4489_ = v___x_4483_;
goto v_reusejp_4488_;
}
else
{
lean_object* v_reuseFailAlloc_4490_; 
v_reuseFailAlloc_4490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4490_, 0, v___x_4487_);
v___x_4489_ = v_reuseFailAlloc_4490_;
goto v_reusejp_4488_;
}
v_reusejp_4488_:
{
return v___x_4489_;
}
}
}
else
{
lean_object* v_vs_4492_; lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_4502_; 
v_vs_4492_ = lean_ctor_get(v_x_4480_, 0);
v_isSharedCheck_4502_ = !lean_is_exclusive(v_x_4480_);
if (v_isSharedCheck_4502_ == 0)
{
v___x_4494_ = v_x_4480_;
v_isShared_4495_ = v_isSharedCheck_4502_;
goto v_resetjp_4493_;
}
else
{
lean_inc(v_vs_4492_);
lean_dec(v_x_4480_);
v___x_4494_ = lean_box(0);
v_isShared_4495_ = v_isSharedCheck_4502_;
goto v_resetjp_4493_;
}
v_resetjp_4493_:
{
size_t v_sz_4496_; size_t v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4500_; 
v_sz_4496_ = lean_array_size(v_vs_4492_);
v___x_4497_ = ((size_t)0ULL);
v___x_4498_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(v_fvarId_4478_, v_e_4479_, v_sz_4496_, v___x_4497_, v_vs_4492_);
if (v_isShared_4495_ == 0)
{
lean_ctor_set(v___x_4494_, 0, v___x_4498_);
v___x_4500_ = v___x_4494_;
goto v_reusejp_4499_;
}
else
{
lean_object* v_reuseFailAlloc_4501_; 
v_reuseFailAlloc_4501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4501_, 0, v___x_4498_);
v___x_4500_ = v_reuseFailAlloc_4501_;
goto v_reusejp_4499_;
}
v_reusejp_4499_:
{
return v___x_4500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2___boxed(lean_object* v_fvarId_4503_, lean_object* v_e_4504_, lean_object* v_x_4505_){
_start:
{
lean_object* v_res_4506_; 
v_res_4506_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(v_fvarId_4503_, v_e_4504_, v_x_4505_);
lean_dec_ref(v_e_4504_);
return v_res_4506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4___boxed(lean_object* v_fvarId_4507_, lean_object* v_e_4508_, lean_object* v_sz_4509_, lean_object* v_i_4510_, lean_object* v_bs_4511_){
_start:
{
size_t v_sz_boxed_4512_; size_t v_i_boxed_4513_; lean_object* v_res_4514_; 
v_sz_boxed_4512_ = lean_unbox_usize(v_sz_4509_);
lean_dec(v_sz_4509_);
v_i_boxed_4513_ = lean_unbox_usize(v_i_4510_);
lean_dec(v_i_4510_);
v_res_4514_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(v_fvarId_4507_, v_e_4508_, v_sz_boxed_4512_, v_i_boxed_4513_, v_bs_4511_);
lean_dec_ref(v_e_4508_);
return v_res_4514_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(lean_object* v_fvarId_4515_, lean_object* v_e_4516_, lean_object* v_t_4517_){
_start:
{
lean_object* v_root_4518_; lean_object* v_tail_4519_; lean_object* v_size_4520_; size_t v_shift_4521_; lean_object* v_tailOff_4522_; lean_object* v___x_4524_; uint8_t v_isShared_4525_; uint8_t v_isSharedCheck_4533_; 
v_root_4518_ = lean_ctor_get(v_t_4517_, 0);
v_tail_4519_ = lean_ctor_get(v_t_4517_, 1);
v_size_4520_ = lean_ctor_get(v_t_4517_, 2);
v_shift_4521_ = lean_ctor_get_usize(v_t_4517_, 4);
v_tailOff_4522_ = lean_ctor_get(v_t_4517_, 3);
v_isSharedCheck_4533_ = !lean_is_exclusive(v_t_4517_);
if (v_isSharedCheck_4533_ == 0)
{
v___x_4524_ = v_t_4517_;
v_isShared_4525_ = v_isSharedCheck_4533_;
goto v_resetjp_4523_;
}
else
{
lean_inc(v_tailOff_4522_);
lean_inc(v_size_4520_);
lean_inc(v_tail_4519_);
lean_inc(v_root_4518_);
lean_dec(v_t_4517_);
v___x_4524_ = lean_box(0);
v_isShared_4525_ = v_isSharedCheck_4533_;
goto v_resetjp_4523_;
}
v_resetjp_4523_:
{
lean_object* v___x_4526_; size_t v_sz_4527_; size_t v___x_4528_; lean_object* v___x_4529_; lean_object* v___x_4531_; 
lean_inc(v_fvarId_4515_);
v___x_4526_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(v_fvarId_4515_, v_e_4516_, v_root_4518_);
v_sz_4527_ = lean_array_size(v_tail_4519_);
v___x_4528_ = ((size_t)0ULL);
v___x_4529_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(v_fvarId_4515_, v_e_4516_, v_sz_4527_, v___x_4528_, v_tail_4519_);
if (v_isShared_4525_ == 0)
{
lean_ctor_set(v___x_4524_, 1, v___x_4529_);
lean_ctor_set(v___x_4524_, 0, v___x_4526_);
v___x_4531_ = v___x_4524_;
goto v_reusejp_4530_;
}
else
{
lean_object* v_reuseFailAlloc_4532_; 
v_reuseFailAlloc_4532_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_4532_, 0, v___x_4526_);
lean_ctor_set(v_reuseFailAlloc_4532_, 1, v___x_4529_);
lean_ctor_set(v_reuseFailAlloc_4532_, 2, v_size_4520_);
lean_ctor_set(v_reuseFailAlloc_4532_, 3, v_tailOff_4522_);
lean_ctor_set_usize(v_reuseFailAlloc_4532_, 4, v_shift_4521_);
v___x_4531_ = v_reuseFailAlloc_4532_;
goto v_reusejp_4530_;
}
v_reusejp_4530_:
{
return v___x_4531_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1___boxed(lean_object* v_fvarId_4534_, lean_object* v_e_4535_, lean_object* v_t_4536_){
_start:
{
lean_object* v_res_4537_; 
v_res_4537_ = l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(v_fvarId_4534_, v_e_4535_, v_t_4536_);
lean_dec_ref(v_e_4535_);
return v_res_4537_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg___lam__0(lean_object* v_f_4538_, lean_object* v_x_4539_){
_start:
{
lean_object* v___x_4540_; 
v___x_4540_ = lean_apply_1(v_f_4538_, v_x_4539_);
return v___x_4540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(lean_object* v_f_4541_, lean_object* v_as_4542_, lean_object* v_i_4543_, lean_object* v_acc_4544_){
_start:
{
lean_object* v___x_4545_; uint8_t v___x_4546_; 
v___x_4545_ = lean_array_get_size(v_as_4542_);
v___x_4546_ = lean_nat_dec_eq(v_i_4543_, v___x_4545_);
if (v___x_4546_ == 0)
{
lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; 
v___x_4547_ = lean_array_fget_borrowed(v_as_4542_, v_i_4543_);
lean_inc(v_f_4541_);
lean_inc(v___x_4547_);
v___x_4548_ = lean_apply_1(v_f_4541_, v___x_4547_);
v___x_4549_ = lean_unsigned_to_nat(1u);
v___x_4550_ = lean_nat_add(v_i_4543_, v___x_4549_);
lean_dec(v_i_4543_);
v___x_4551_ = lean_array_push(v_acc_4544_, v___x_4548_);
v_i_4543_ = v___x_4550_;
v_acc_4544_ = v___x_4551_;
goto _start;
}
else
{
lean_dec(v_i_4543_);
lean_dec(v_f_4541_);
return v_acc_4544_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg___boxed(lean_object* v_f_4553_, lean_object* v_as_4554_, lean_object* v_i_4555_, lean_object* v_acc_4556_){
_start:
{
lean_object* v_res_4557_; 
v_res_4557_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_f_4553_, v_as_4554_, v_i_4555_, v_acc_4556_);
lean_dec_ref(v_as_4554_);
return v_res_4557_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_f_4558_, lean_object* v_as_4559_){
_start:
{
lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; 
v___x_4560_ = lean_unsigned_to_nat(0u);
v___x_4561_ = lean_array_get_size(v_as_4559_);
v___x_4562_ = lean_mk_empty_array_with_capacity(v___x_4561_);
v___x_4563_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_f_4558_, v_as_4559_, v___x_4560_, v___x_4562_);
return v___x_4563_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_f_4564_, lean_object* v_as_4565_){
_start:
{
lean_object* v_res_4566_; 
v_res_4566_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(v_f_4564_, v_as_4565_);
lean_dec_ref(v_as_4565_);
return v_res_4566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_4567_, size_t v_sz_4568_, size_t v_i_4569_, lean_object* v_bs_4570_){
_start:
{
uint8_t v___x_4571_; 
v___x_4571_ = lean_usize_dec_lt(v_i_4569_, v_sz_4568_);
if (v___x_4571_ == 0)
{
lean_dec(v_f_4567_);
return v_bs_4570_;
}
else
{
lean_object* v_v_4572_; lean_object* v___x_4573_; lean_object* v_bs_x27_4574_; lean_object* v___y_4576_; 
v_v_4572_ = lean_array_uget(v_bs_4570_, v_i_4569_);
v___x_4573_ = lean_unsigned_to_nat(0u);
v_bs_x27_4574_ = lean_array_uset(v_bs_4570_, v_i_4569_, v___x_4573_);
switch(lean_obj_tag(v_v_4572_))
{
case 0:
{
lean_object* v_key_4581_; lean_object* v_val_4582_; lean_object* v___x_4584_; uint8_t v_isShared_4585_; uint8_t v_isSharedCheck_4590_; 
v_key_4581_ = lean_ctor_get(v_v_4572_, 0);
v_val_4582_ = lean_ctor_get(v_v_4572_, 1);
v_isSharedCheck_4590_ = !lean_is_exclusive(v_v_4572_);
if (v_isSharedCheck_4590_ == 0)
{
v___x_4584_ = v_v_4572_;
v_isShared_4585_ = v_isSharedCheck_4590_;
goto v_resetjp_4583_;
}
else
{
lean_inc(v_val_4582_);
lean_inc(v_key_4581_);
lean_dec(v_v_4572_);
v___x_4584_ = lean_box(0);
v_isShared_4585_ = v_isSharedCheck_4590_;
goto v_resetjp_4583_;
}
v_resetjp_4583_:
{
lean_object* v___x_4586_; lean_object* v___x_4588_; 
lean_inc(v_f_4567_);
v___x_4586_ = lean_apply_1(v_f_4567_, v_val_4582_);
if (v_isShared_4585_ == 0)
{
lean_ctor_set(v___x_4584_, 1, v___x_4586_);
v___x_4588_ = v___x_4584_;
goto v_reusejp_4587_;
}
else
{
lean_object* v_reuseFailAlloc_4589_; 
v_reuseFailAlloc_4589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4589_, 0, v_key_4581_);
lean_ctor_set(v_reuseFailAlloc_4589_, 1, v___x_4586_);
v___x_4588_ = v_reuseFailAlloc_4589_;
goto v_reusejp_4587_;
}
v_reusejp_4587_:
{
v___y_4576_ = v___x_4588_;
goto v___jp_4575_;
}
}
}
case 1:
{
lean_object* v_node_4591_; lean_object* v___x_4593_; uint8_t v_isShared_4594_; uint8_t v_isSharedCheck_4599_; 
v_node_4591_ = lean_ctor_get(v_v_4572_, 0);
v_isSharedCheck_4599_ = !lean_is_exclusive(v_v_4572_);
if (v_isSharedCheck_4599_ == 0)
{
v___x_4593_ = v_v_4572_;
v_isShared_4594_ = v_isSharedCheck_4599_;
goto v_resetjp_4592_;
}
else
{
lean_inc(v_node_4591_);
lean_dec(v_v_4572_);
v___x_4593_ = lean_box(0);
v_isShared_4594_ = v_isSharedCheck_4599_;
goto v_resetjp_4592_;
}
v_resetjp_4592_:
{
lean_object* v___x_4595_; lean_object* v___x_4597_; 
lean_inc(v_f_4567_);
v___x_4595_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4567_, v_node_4591_);
if (v_isShared_4594_ == 0)
{
lean_ctor_set(v___x_4593_, 0, v___x_4595_);
v___x_4597_ = v___x_4593_;
goto v_reusejp_4596_;
}
else
{
lean_object* v_reuseFailAlloc_4598_; 
v_reuseFailAlloc_4598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4598_, 0, v___x_4595_);
v___x_4597_ = v_reuseFailAlloc_4598_;
goto v_reusejp_4596_;
}
v_reusejp_4596_:
{
v___y_4576_ = v___x_4597_;
goto v___jp_4575_;
}
}
}
default: 
{
lean_object* v___x_4600_; 
v___x_4600_ = lean_box(2);
v___y_4576_ = v___x_4600_;
goto v___jp_4575_;
}
}
v___jp_4575_:
{
size_t v___x_4577_; size_t v___x_4578_; lean_object* v___x_4579_; 
v___x_4577_ = ((size_t)1ULL);
v___x_4578_ = lean_usize_add(v_i_4569_, v___x_4577_);
v___x_4579_ = lean_array_uset(v_bs_x27_4574_, v_i_4569_, v___y_4576_);
v_i_4569_ = v___x_4578_;
v_bs_4570_ = v___x_4579_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(lean_object* v_f_4601_, lean_object* v_n_4602_){
_start:
{
if (lean_obj_tag(v_n_4602_) == 0)
{
lean_object* v_es_4603_; lean_object* v___x_4605_; uint8_t v_isShared_4606_; uint8_t v_isSharedCheck_4613_; 
v_es_4603_ = lean_ctor_get(v_n_4602_, 0);
v_isSharedCheck_4613_ = !lean_is_exclusive(v_n_4602_);
if (v_isSharedCheck_4613_ == 0)
{
v___x_4605_ = v_n_4602_;
v_isShared_4606_ = v_isSharedCheck_4613_;
goto v_resetjp_4604_;
}
else
{
lean_inc(v_es_4603_);
lean_dec(v_n_4602_);
v___x_4605_ = lean_box(0);
v_isShared_4606_ = v_isSharedCheck_4613_;
goto v_resetjp_4604_;
}
v_resetjp_4604_:
{
size_t v_sz_4607_; size_t v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4611_; 
v_sz_4607_ = lean_array_size(v_es_4603_);
v___x_4608_ = ((size_t)0ULL);
v___x_4609_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(v_f_4601_, v_sz_4607_, v___x_4608_, v_es_4603_);
if (v_isShared_4606_ == 0)
{
lean_ctor_set(v___x_4605_, 0, v___x_4609_);
v___x_4611_ = v___x_4605_;
goto v_reusejp_4610_;
}
else
{
lean_object* v_reuseFailAlloc_4612_; 
v_reuseFailAlloc_4612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4612_, 0, v___x_4609_);
v___x_4611_ = v_reuseFailAlloc_4612_;
goto v_reusejp_4610_;
}
v_reusejp_4610_:
{
return v___x_4611_;
}
}
}
else
{
lean_object* v_ks_4614_; lean_object* v_vs_4615_; lean_object* v___x_4617_; uint8_t v_isShared_4618_; uint8_t v_isSharedCheck_4623_; 
v_ks_4614_ = lean_ctor_get(v_n_4602_, 0);
v_vs_4615_ = lean_ctor_get(v_n_4602_, 1);
v_isSharedCheck_4623_ = !lean_is_exclusive(v_n_4602_);
if (v_isSharedCheck_4623_ == 0)
{
v___x_4617_ = v_n_4602_;
v_isShared_4618_ = v_isSharedCheck_4623_;
goto v_resetjp_4616_;
}
else
{
lean_inc(v_vs_4615_);
lean_inc(v_ks_4614_);
lean_dec(v_n_4602_);
v___x_4617_ = lean_box(0);
v_isShared_4618_ = v_isSharedCheck_4623_;
goto v_resetjp_4616_;
}
v_resetjp_4616_:
{
lean_object* v_val_4619_; lean_object* v___x_4621_; 
v_val_4619_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(v_f_4601_, v_vs_4615_);
lean_dec_ref(v_vs_4615_);
if (v_isShared_4618_ == 0)
{
lean_ctor_set(v___x_4617_, 1, v_val_4619_);
v___x_4621_ = v___x_4617_;
goto v_reusejp_4620_;
}
else
{
lean_object* v_reuseFailAlloc_4622_; 
v_reuseFailAlloc_4622_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4622_, 0, v_ks_4614_);
lean_ctor_set(v_reuseFailAlloc_4622_, 1, v_val_4619_);
v___x_4621_ = v_reuseFailAlloc_4622_;
goto v_reusejp_4620_;
}
v_reusejp_4620_:
{
return v___x_4621_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_4624_, lean_object* v_sz_4625_, lean_object* v_i_4626_, lean_object* v_bs_4627_){
_start:
{
size_t v_sz_boxed_4628_; size_t v_i_boxed_4629_; lean_object* v_res_4630_; 
v_sz_boxed_4628_ = lean_unbox_usize(v_sz_4625_);
lean_dec(v_sz_4625_);
v_i_boxed_4629_ = lean_unbox_usize(v_i_4626_);
lean_dec(v_i_4626_);
v_res_4630_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(v_f_4624_, v_sz_boxed_4628_, v_i_boxed_4629_, v_bs_4627_);
return v_res_4630_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(lean_object* v_pm_4631_, lean_object* v_f_4632_){
_start:
{
lean_object* v___f_4633_; lean_object* v___x_4634_; 
v___f_4633_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4633_, 0, v_f_4632_);
v___x_4634_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v___f_4633_, v_pm_4631_);
return v___x_4634_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId(lean_object* v_fvarId_4635_, lean_object* v_e_4636_, lean_object* v_lctx_4637_){
_start:
{
lean_object* v_lctx_4638_; lean_object* v_fvarIdToDecl_4639_; lean_object* v_decls_4640_; lean_object* v_auxDeclToFullName_4641_; lean_object* v___x_4643_; uint8_t v_isShared_4644_; uint8_t v_isSharedCheck_4651_; 
lean_inc(v_fvarId_4635_);
v_lctx_4638_ = lean_local_ctx_erase(v_lctx_4637_, v_fvarId_4635_);
v_fvarIdToDecl_4639_ = lean_ctor_get(v_lctx_4638_, 0);
v_decls_4640_ = lean_ctor_get(v_lctx_4638_, 1);
v_auxDeclToFullName_4641_ = lean_ctor_get(v_lctx_4638_, 2);
v_isSharedCheck_4651_ = !lean_is_exclusive(v_lctx_4638_);
if (v_isSharedCheck_4651_ == 0)
{
v___x_4643_ = v_lctx_4638_;
v_isShared_4644_ = v_isSharedCheck_4651_;
goto v_resetjp_4642_;
}
else
{
lean_inc(v_auxDeclToFullName_4641_);
lean_inc(v_decls_4640_);
lean_inc(v_fvarIdToDecl_4639_);
lean_dec(v_lctx_4638_);
v___x_4643_ = lean_box(0);
v_isShared_4644_ = v_isSharedCheck_4651_;
goto v_resetjp_4642_;
}
v_resetjp_4642_:
{
lean_object* v___f_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4649_; 
lean_inc_ref(v_e_4636_);
lean_inc(v_fvarId_4635_);
v___f_4645_ = lean_alloc_closure((void*)(l_Lean_LocalContext_replaceFVarId___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4645_, 0, v_fvarId_4635_);
lean_closure_set(v___f_4645_, 1, v_e_4636_);
v___x_4646_ = l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(v_fvarIdToDecl_4639_, v___f_4645_);
v___x_4647_ = l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(v_fvarId_4635_, v_e_4636_, v_decls_4640_);
lean_dec_ref(v_e_4636_);
if (v_isShared_4644_ == 0)
{
lean_ctor_set(v___x_4643_, 1, v___x_4647_);
lean_ctor_set(v___x_4643_, 0, v___x_4646_);
v___x_4649_ = v___x_4643_;
goto v_reusejp_4648_;
}
else
{
lean_object* v_reuseFailAlloc_4650_; 
v_reuseFailAlloc_4650_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4650_, 0, v___x_4646_);
lean_ctor_set(v_reuseFailAlloc_4650_, 1, v___x_4647_);
lean_ctor_set(v_reuseFailAlloc_4650_, 2, v_auxDeclToFullName_4641_);
v___x_4649_ = v_reuseFailAlloc_4650_;
goto v_reusejp_4648_;
}
v_reusejp_4648_:
{
return v___x_4649_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0(lean_object* v_00_u03b2_4652_, lean_object* v_00_u03c3_4653_, lean_object* v_pm_4654_, lean_object* v_f_4655_){
_start:
{
lean_object* v___x_4656_; 
v___x_4656_ = l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(v_pm_4654_, v_f_4655_);
return v___x_4656_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0___redArg(lean_object* v_pm_4657_, lean_object* v_f_4658_){
_start:
{
lean_object* v___x_4659_; 
v___x_4659_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4658_, v_pm_4657_);
return v___x_4659_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0(lean_object* v_00_u03b2_4660_, lean_object* v_00_u03c3_4661_, lean_object* v_pm_4662_, lean_object* v_f_4663_){
_start:
{
lean_object* v___x_4664_; 
v___x_4664_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4663_, v_pm_4662_);
return v___x_4664_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_4665_, lean_object* v_00_u03b2_4666_, lean_object* v_00_u03c3_4667_, lean_object* v_f_4668_, lean_object* v_n_4669_){
_start:
{
lean_object* v___x_4670_; 
v___x_4670_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4668_, v_n_4669_);
return v___x_4670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_4671_, lean_object* v_00_u03b2_4672_, lean_object* v_00_u03c3_4673_, lean_object* v_f_4674_, size_t v_sz_4675_, size_t v_i_4676_, lean_object* v_bs_4677_){
_start:
{
lean_object* v___x_4678_; 
v___x_4678_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(v_f_4674_, v_sz_4675_, v_i_4676_, v_bs_4677_);
return v___x_4678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_4679_, lean_object* v_00_u03b2_4680_, lean_object* v_00_u03c3_4681_, lean_object* v_f_4682_, lean_object* v_sz_4683_, lean_object* v_i_4684_, lean_object* v_bs_4685_){
_start:
{
size_t v_sz_boxed_4686_; size_t v_i_boxed_4687_; lean_object* v_res_4688_; 
v_sz_boxed_4686_ = lean_unbox_usize(v_sz_4683_);
lean_dec(v_sz_4683_);
v_i_boxed_4687_ = lean_unbox_usize(v_i_4684_);
lean_dec(v_i_4684_);
v_res_4688_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_4679_, v_00_u03b2_4680_, v_00_u03c3_4681_, v_f_4682_, v_sz_boxed_4686_, v_i_boxed_4687_, v_bs_4685_);
return v_res_4688_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_4689_, lean_object* v_00_u03b2_4690_, lean_object* v_f_4691_, lean_object* v_as_4692_){
_start:
{
lean_object* v___x_4693_; 
v___x_4693_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(v_f_4691_, v_as_4692_);
return v___x_4693_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_4694_, lean_object* v_00_u03b2_4695_, lean_object* v_f_4696_, lean_object* v_as_4697_){
_start:
{
lean_object* v_res_4698_; 
v_res_4698_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_4694_, v_00_u03b2_4695_, v_f_4696_, v_as_4697_);
lean_dec_ref(v_as_4697_);
return v_res_4698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7(lean_object* v_00_u03b1_4699_, lean_object* v_00_u03b2_4700_, lean_object* v_f_4701_, lean_object* v_as_4702_, lean_object* v_i_4703_, lean_object* v_acc_4704_, lean_object* v_hle_4705_){
_start:
{
lean_object* v___x_4706_; 
v___x_4706_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_f_4701_, v_as_4702_, v_i_4703_, v_acc_4704_);
return v___x_4706_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___boxed(lean_object* v_00_u03b1_4707_, lean_object* v_00_u03b2_4708_, lean_object* v_f_4709_, lean_object* v_as_4710_, lean_object* v_i_4711_, lean_object* v_acc_4712_, lean_object* v_hle_4713_){
_start:
{
lean_object* v_res_4714_; 
v_res_4714_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7(v_00_u03b1_4707_, v_00_u03b2_4708_, v_f_4709_, v_as_4710_, v_i_4711_, v_acc_4712_, v_hle_4713_);
lean_dec_ref(v_as_4710_);
return v_res_4714_;
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
