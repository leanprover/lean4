// Lean compiler output
// Module: Lean.Meta.Match.CaseArraySizes
// Imports: public import Lean.Meta.Basic public import Lean.Meta.Tactic.FVarSubst import Lean.Meta.Match.CaseValues import Lean.Meta.Tactic.Subst
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
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_Meta_mkLt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecideProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Meta_mkArrayLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_get(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assertExt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValues(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default___closed__0 = (const lean_object*)&l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default___closed__0_value),((lean_object*)&l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default___closed__1 = (const lean_object*)&l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default = (const lean_object*)&l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instInhabitedCaseArraySizesSubgoal = (const lean_object*)&l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_getArrayArgType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Array"};
static const lean_object* l_Lean_Meta_getArrayArgType___closed__0 = (const lean_object*)&l_Lean_Meta_getArrayArgType___closed__0_value;
static const lean_ctor_object l_Lean_Meta_getArrayArgType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getArrayArgType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_object* l_Lean_Meta_getArrayArgType___closed__1 = (const lean_object*)&l_Lean_Meta_getArrayArgType___closed__1_value;
static const lean_string_object l_Lean_Meta_getArrayArgType___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "array expected"};
static const lean_object* l_Lean_Meta_getArrayArgType___closed__2 = (const lean_object*)&l_Lean_Meta_getArrayArgType___closed__2_value;
static lean_once_cell_t l_Lean_Meta_getArrayArgType___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_getArrayArgType___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayArgType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayArgType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "getLit"};
static const lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__0 = (const lean_object*)&l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getArrayArgType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(203, 31, 150, 206, 23, 239, 28, 61)}};
static const lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__1 = (const lean_object*)&l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "toArrayLit_eq"};
static const lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__0 = (const lean_object*)&l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getArrayArgType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 54, 254, 215, 42, 180, 33, 232)}};
static const lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__1 = (const lean_object*)&l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "hEqALit"};
static const lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__2 = (const lean_object*)&l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__2_value),LEAN_SCALAR_PTR_LITERAL(144, 218, 54, 212, 216, 192, 54, 198)}};
static const lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__3 = (const lean_object*)&l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit___closed__0 = (const lean_object*)&l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_caseArraySizes___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "aSize"};
static const lean_object* l_Lean_Meta_caseArraySizes___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_caseArraySizes___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_caseArraySizes___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_caseArraySizes___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 102, 98, 152, 210, 104, 173, 219)}};
static const lean_object* l_Lean_Meta_caseArraySizes___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_caseArraySizes___lam__0___closed__1_value;
static const lean_string_object l_Lean_Meta_caseArraySizes___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Meta_caseArraySizes___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_caseArraySizes___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Meta_caseArraySizes___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_caseArraySizes___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Meta_caseArraySizes___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_caseArraySizes___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_Meta_caseArraySizes___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_caseArraySizes___lam__0___closed__4;
static const lean_string_object l_Lean_Meta_caseArraySizes___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l_Lean_Meta_caseArraySizes___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_caseArraySizes___lam__0___closed__5_value;
static const lean_ctor_object l_Lean_Meta_caseArraySizes___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_caseArraySizes___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l_Lean_Meta_caseArraySizes___lam__0___closed__6 = (const lean_object*)&l_Lean_Meta_caseArraySizes___lam__0___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Meta_caseArraySizes___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_caseArraySizes___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_caseArraySizes___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "size"};
static const lean_object* l_Lean_Meta_caseArraySizes___closed__0 = (const lean_object*)&l_Lean_Meta_caseArraySizes___closed__0_value;
static const lean_ctor_object l_Lean_Meta_caseArraySizes___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getArrayArgType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Lean_Meta_caseArraySizes___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_caseArraySizes___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_caseArraySizes___closed__0_value),LEAN_SCALAR_PTR_LITERAL(44, 164, 37, 176, 250, 127, 194, 229)}};
static const lean_object* l_Lean_Meta_caseArraySizes___closed__1 = (const lean_object*)&l_Lean_Meta_caseArraySizes___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_caseArraySizes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_caseArraySizes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_caseArraySizes_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_caseArraySizes_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0_spec__0(lean_object* v_msgData_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_){
_start:
{
lean_object* v___x_15_; lean_object* v_env_16_; lean_object* v___x_17_; lean_object* v_mctx_18_; lean_object* v_lctx_19_; lean_object* v_options_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_15_ = lean_st_ref_get(v___y_13_);
v_env_16_ = lean_ctor_get(v___x_15_, 0);
lean_inc_ref(v_env_16_);
lean_dec(v___x_15_);
v___x_17_ = lean_st_ref_get(v___y_11_);
v_mctx_18_ = lean_ctor_get(v___x_17_, 0);
lean_inc_ref(v_mctx_18_);
lean_dec(v___x_17_);
v_lctx_19_ = lean_ctor_get(v___y_10_, 2);
v_options_20_ = lean_ctor_get(v___y_12_, 2);
lean_inc_ref(v_options_20_);
lean_inc_ref(v_lctx_19_);
v___x_21_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_21_, 0, v_env_16_);
lean_ctor_set(v___x_21_, 1, v_mctx_18_);
lean_ctor_set(v___x_21_, 2, v_lctx_19_);
lean_ctor_set(v___x_21_, 3, v_options_20_);
v___x_22_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_22_, 0, v___x_21_);
lean_ctor_set(v___x_22_, 1, v_msgData_9_);
v___x_23_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_23_, 0, v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0_spec__0___boxed(lean_object* v_msgData_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0_spec__0(v_msgData_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
lean_dec(v___y_26_);
lean_dec_ref(v___y_25_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0___redArg(lean_object* v_msg_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v_ref_37_; lean_object* v___x_38_; lean_object* v_a_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_47_; 
v_ref_37_ = lean_ctor_get(v___y_34_, 5);
v___x_38_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0_spec__0(v_msg_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_);
v_a_39_ = lean_ctor_get(v___x_38_, 0);
v_isSharedCheck_47_ = !lean_is_exclusive(v___x_38_);
if (v_isSharedCheck_47_ == 0)
{
v___x_41_ = v___x_38_;
v_isShared_42_ = v_isSharedCheck_47_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_a_39_);
lean_dec(v___x_38_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_47_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v___x_43_; lean_object* v___x_45_; 
lean_inc(v_ref_37_);
v___x_43_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_43_, 0, v_ref_37_);
lean_ctor_set(v___x_43_, 1, v_a_39_);
if (v_isShared_42_ == 0)
{
lean_ctor_set_tag(v___x_41_, 1);
lean_ctor_set(v___x_41_, 0, v___x_43_);
v___x_45_ = v___x_41_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v___x_43_);
v___x_45_ = v_reuseFailAlloc_46_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
return v___x_45_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0___redArg___boxed(lean_object* v_msg_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0___redArg(v_msg_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
return v_res_54_;
}
}
static lean_object* _init_l_Lean_Meta_getArrayArgType___closed__3(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = ((lean_object*)(l_Lean_Meta_getArrayArgType___closed__2));
v___x_60_ = l_Lean_stringToMessageData(v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayArgType(lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_){
_start:
{
lean_object* v___x_67_; 
lean_inc(v_a_65_);
lean_inc_ref(v_a_64_);
lean_inc(v_a_63_);
lean_inc_ref(v_a_62_);
lean_inc_ref(v_a_61_);
v___x_67_ = lean_infer_type(v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_);
if (lean_obj_tag(v___x_67_) == 0)
{
lean_object* v_a_68_; lean_object* v___x_69_; 
v_a_68_ = lean_ctor_get(v___x_67_, 0);
lean_inc(v_a_68_);
lean_dec_ref(v___x_67_);
v___x_69_ = l_Lean_Meta_whnfD(v_a_68_, v_a_62_, v_a_63_, v_a_64_, v_a_65_);
if (lean_obj_tag(v___x_69_) == 0)
{
lean_object* v_a_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_94_; 
v_a_70_ = lean_ctor_get(v___x_69_, 0);
v_isSharedCheck_94_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_94_ == 0)
{
v___x_72_ = v___x_69_;
v_isShared_73_ = v_isSharedCheck_94_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_a_70_);
lean_dec(v___x_69_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_94_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v___x_79_; lean_object* v___x_80_; uint8_t v___x_81_; 
v___x_79_ = ((lean_object*)(l_Lean_Meta_getArrayArgType___closed__1));
v___x_80_ = lean_unsigned_to_nat(1u);
v___x_81_ = l_Lean_Expr_isAppOfArity(v_a_70_, v___x_79_, v___x_80_);
if (v___x_81_ == 0)
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v_a_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_93_; 
lean_del_object(v___x_72_);
lean_dec(v_a_70_);
v___x_82_ = lean_obj_once(&l_Lean_Meta_getArrayArgType___closed__3, &l_Lean_Meta_getArrayArgType___closed__3_once, _init_l_Lean_Meta_getArrayArgType___closed__3);
v___x_83_ = l_Lean_indentExpr(v_a_61_);
v___x_84_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_84_, 0, v___x_82_);
lean_ctor_set(v___x_84_, 1, v___x_83_);
v___x_85_ = l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0___redArg(v___x_84_, v_a_62_, v_a_63_, v_a_64_, v_a_65_);
v_a_86_ = lean_ctor_get(v___x_85_, 0);
v_isSharedCheck_93_ = !lean_is_exclusive(v___x_85_);
if (v_isSharedCheck_93_ == 0)
{
v___x_88_ = v___x_85_;
v_isShared_89_ = v_isSharedCheck_93_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_a_86_);
lean_dec(v___x_85_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_93_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_91_; 
if (v_isShared_89_ == 0)
{
v___x_91_ = v___x_88_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v_a_86_);
v___x_91_ = v_reuseFailAlloc_92_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
return v___x_91_;
}
}
}
else
{
lean_dec_ref(v_a_61_);
goto v___jp_74_;
}
v___jp_74_:
{
lean_object* v___x_75_; lean_object* v___x_77_; 
v___x_75_ = l_Lean_Expr_appArg_x21(v_a_70_);
lean_dec(v_a_70_);
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 0, v___x_75_);
v___x_77_ = v___x_72_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v___x_75_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
return v___x_77_;
}
}
}
}
else
{
lean_dec_ref(v_a_61_);
return v___x_69_;
}
}
else
{
lean_dec_ref(v_a_61_);
return v___x_67_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayArgType___boxed(lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lean_Meta_getArrayArgType(v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_);
lean_dec(v_a_99_);
lean_dec_ref(v_a_98_);
lean_dec(v_a_97_);
lean_dec_ref(v_a_96_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0(lean_object* v_00_u03b1_102_, lean_object* v_msg_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0___redArg(v_msg_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0___boxed(lean_object* v_00_u03b1_110_, lean_object* v_msg_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0(v_00_u03b1_110_, v_msg_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit(lean_object* v_a_122_, lean_object* v_i_123_, lean_object* v_n_124_, lean_object* v_h_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_131_ = l_Lean_mkRawNatLit(v_i_123_);
v___x_132_ = l_Lean_mkRawNatLit(v_n_124_);
lean_inc_ref(v___x_131_);
v___x_133_ = l_Lean_Meta_mkLt(v___x_131_, v___x_132_, v_a_126_, v_a_127_, v_a_128_, v_a_129_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v_a_134_; lean_object* v___x_135_; 
v_a_134_ = lean_ctor_get(v___x_133_, 0);
lean_inc(v_a_134_);
lean_dec_ref(v___x_133_);
v___x_135_ = l_Lean_Meta_mkDecideProof(v_a_134_, v_a_126_, v_a_127_, v_a_128_, v_a_129_);
if (lean_obj_tag(v___x_135_) == 0)
{
lean_object* v_a_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v_a_136_ = lean_ctor_get(v___x_135_, 0);
lean_inc(v_a_136_);
lean_dec_ref(v___x_135_);
v___x_137_ = ((lean_object*)(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__1));
v___x_138_ = lean_unsigned_to_nat(4u);
v___x_139_ = lean_mk_empty_array_with_capacity(v___x_138_);
v___x_140_ = lean_array_push(v___x_139_, v_a_122_);
v___x_141_ = lean_array_push(v___x_140_, v___x_131_);
v___x_142_ = lean_array_push(v___x_141_, v_h_125_);
v___x_143_ = lean_array_push(v___x_142_, v_a_136_);
v___x_144_ = l_Lean_Meta_mkAppM(v___x_137_, v___x_143_, v_a_126_, v_a_127_, v_a_128_, v_a_129_);
return v___x_144_;
}
else
{
lean_dec_ref(v___x_131_);
lean_dec_ref(v_h_125_);
lean_dec_ref(v_a_122_);
return v___x_135_;
}
}
else
{
lean_dec_ref(v___x_131_);
lean_dec_ref(v_h_125_);
lean_dec_ref(v_a_122_);
return v___x_133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___boxed(lean_object* v_a_145_, lean_object* v_i_146_, lean_object* v_n_147_, lean_object* v_h_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit(v_a_145_, v_i_146_, v_n_147_, v_h_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_);
lean_dec(v_a_152_);
lean_dec_ref(v_a_151_);
lean_dec(v_a_150_);
lean_dec_ref(v_a_149_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__0(lean_object* v_mvarId_155_, lean_object* v_xs_156_, uint8_t v___x_157_, lean_object* v_args_158_, lean_object* v_a_159_, lean_object* v_heq_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = l_Lean_MVarId_getType(v_mvarId_155_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
if (lean_obj_tag(v___x_166_) == 0)
{
lean_object* v_a_167_; lean_object* v___x_168_; uint8_t v___x_169_; uint8_t v___x_170_; lean_object* v___x_171_; 
v_a_167_ = lean_ctor_get(v___x_166_, 0);
lean_inc(v_a_167_);
lean_dec_ref(v___x_166_);
v___x_168_ = lean_array_push(v_xs_156_, v_heq_160_);
v___x_169_ = 1;
v___x_170_ = 1;
v___x_171_ = l_Lean_Meta_mkForallFVars(v___x_168_, v_a_167_, v___x_157_, v___x_169_, v___x_169_, v___x_170_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
lean_dec_ref(v___x_168_);
if (lean_obj_tag(v___x_171_) == 0)
{
lean_object* v_a_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_181_; 
v_a_172_ = lean_ctor_get(v___x_171_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_181_ == 0)
{
v___x_174_ = v___x_171_;
v_isShared_175_ = v_isSharedCheck_181_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_a_172_);
lean_dec(v___x_171_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_181_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_179_; 
v___x_176_ = lean_array_push(v_args_158_, v_a_159_);
v___x_177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_177_, 0, v_a_172_);
lean_ctor_set(v___x_177_, 1, v___x_176_);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 0, v___x_177_);
v___x_179_ = v___x_174_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_177_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
else
{
lean_object* v_a_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_189_; 
lean_dec_ref(v_a_159_);
lean_dec_ref(v_args_158_);
v_a_182_ = lean_ctor_get(v___x_171_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_189_ == 0)
{
v___x_184_ = v___x_171_;
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_a_182_);
lean_dec(v___x_171_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_187_; 
if (v_isShared_185_ == 0)
{
v___x_187_ = v___x_184_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_a_182_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
}
else
{
lean_object* v_a_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_197_; 
lean_dec_ref(v_heq_160_);
lean_dec_ref(v_a_159_);
lean_dec_ref(v_args_158_);
lean_dec_ref(v_xs_156_);
v_a_190_ = lean_ctor_get(v___x_166_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_197_ == 0)
{
v___x_192_ = v___x_166_;
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_a_190_);
lean_dec(v___x_166_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_195_; 
if (v_isShared_193_ == 0)
{
v___x_195_ = v___x_192_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_a_190_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__0___boxed(lean_object* v_mvarId_198_, lean_object* v_xs_199_, lean_object* v___x_200_, lean_object* v_args_201_, lean_object* v_a_202_, lean_object* v_heq_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
uint8_t v___x_1223__boxed_209_; lean_object* v_res_210_; 
v___x_1223__boxed_209_ = lean_unbox(v___x_200_);
v_res_210_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__0(v_mvarId_198_, v_xs_199_, v___x_1223__boxed_209_, v_args_201_, v_a_202_, v_heq_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_);
lean_dec(v___y_207_);
lean_dec_ref(v___y_206_);
lean_dec(v___y_205_);
lean_dec_ref(v___y_204_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg___lam__0(lean_object* v_k_211_, lean_object* v_b_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v___x_218_; 
lean_inc(v___y_216_);
lean_inc_ref(v___y_215_);
lean_inc(v___y_214_);
lean_inc_ref(v___y_213_);
v___x_218_ = lean_apply_6(v_k_211_, v_b_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, lean_box(0));
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_219_, lean_object* v_b_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg___lam__0(v_k_219_, v_b_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg(lean_object* v_name_227_, uint8_t v_bi_228_, lean_object* v_type_229_, lean_object* v_k_230_, uint8_t v_kind_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v___f_237_; lean_object* v___x_238_; 
v___f_237_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_237_, 0, v_k_230_);
v___x_238_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_227_, v_bi_228_, v_type_229_, v___f_237_, v_kind_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_246_; 
v_a_239_ = lean_ctor_get(v___x_238_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_246_ == 0)
{
v___x_241_ = v___x_238_;
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_a_239_);
lean_dec(v___x_238_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_244_; 
if (v_isShared_242_ == 0)
{
v___x_244_ = v___x_241_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_a_239_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
else
{
lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_254_; 
v_a_247_ = lean_ctor_get(v___x_238_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_254_ == 0)
{
v___x_249_ = v___x_238_;
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v___x_238_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_252_; 
if (v_isShared_250_ == 0)
{
v___x_252_ = v___x_249_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_a_247_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg___boxed(lean_object* v_name_255_, lean_object* v_bi_256_, lean_object* v_type_257_, lean_object* v_k_258_, lean_object* v_kind_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
uint8_t v_bi_boxed_265_; uint8_t v_kind_boxed_266_; lean_object* v_res_267_; 
v_bi_boxed_265_ = lean_unbox(v_bi_256_);
v_kind_boxed_266_ = lean_unbox(v_kind_259_);
v_res_267_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg(v_name_255_, v_bi_boxed_265_, v_type_257_, v_k_258_, v_kind_boxed_266_, v___y_260_, v___y_261_, v___y_262_, v___y_263_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
lean_dec(v___y_261_);
lean_dec_ref(v___y_260_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___redArg(lean_object* v_name_268_, lean_object* v_type_269_, lean_object* v_k_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
uint8_t v___x_276_; uint8_t v___x_277_; lean_object* v___x_278_; 
v___x_276_ = 0;
v___x_277_ = 0;
v___x_278_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg(v_name_268_, v___x_276_, v_type_269_, v_k_270_, v___x_277_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___redArg___boxed(lean_object* v_name_279_, lean_object* v_type_280_, lean_object* v_k_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___redArg(v_name_279_, v_type_280_, v_k_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__1___boxed(lean_object* v_a_295_, lean_object* v_i_296_, lean_object* v_n_297_, lean_object* v_aSizeEqN_298_, lean_object* v_xs_299_, lean_object* v_args_300_, lean_object* v_mvarId_301_, lean_object* v_xNamePrefix_302_, lean_object* v_00_u03b1_303_, lean_object* v___x_304_, lean_object* v_xi_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__1(v_a_295_, v_i_296_, v_n_297_, v_aSizeEqN_298_, v_xs_299_, v_args_300_, v_mvarId_301_, v_xNamePrefix_302_, v_00_u03b1_303_, v___x_304_, v_xi_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop(lean_object* v_mvarId_312_, lean_object* v_a_313_, lean_object* v_n_314_, lean_object* v_xNamePrefix_315_, lean_object* v_aSizeEqN_316_, lean_object* v_00_u03b1_317_, lean_object* v_i_318_, lean_object* v_xs_319_, lean_object* v_args_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
uint8_t v___x_326_; 
v___x_326_ = lean_nat_dec_lt(v_i_318_, v_n_314_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; lean_object* v___x_328_; 
lean_dec(v_i_318_);
lean_dec(v_xNamePrefix_315_);
lean_inc_ref(v_xs_319_);
v___x_327_ = lean_array_to_list(v_xs_319_);
v___x_328_ = l_Lean_Meta_mkArrayLit(v_00_u03b1_317_, v___x_327_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v_a_329_; lean_object* v___x_330_; 
v_a_329_ = lean_ctor_get(v___x_328_, 0);
lean_inc(v_a_329_);
lean_dec_ref(v___x_328_);
lean_inc_ref(v_a_313_);
v___x_330_ = l_Lean_Meta_mkEq(v_a_313_, v_a_329_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v_a_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_a_331_);
lean_dec_ref(v___x_330_);
v___x_332_ = ((lean_object*)(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__1));
v___x_333_ = l_Lean_mkRawNatLit(v_n_314_);
v___x_334_ = lean_unsigned_to_nat(3u);
v___x_335_ = lean_mk_empty_array_with_capacity(v___x_334_);
v___x_336_ = lean_array_push(v___x_335_, v_a_313_);
v___x_337_ = lean_array_push(v___x_336_, v___x_333_);
v___x_338_ = lean_array_push(v___x_337_, v_aSizeEqN_316_);
v___x_339_ = l_Lean_Meta_mkAppM(v___x_332_, v___x_338_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v_a_340_; lean_object* v___x_341_; lean_object* v___f_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v_a_340_ = lean_ctor_get(v___x_339_, 0);
lean_inc(v_a_340_);
lean_dec_ref(v___x_339_);
v___x_341_ = lean_box(v___x_326_);
v___f_342_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__0___boxed), 11, 5);
lean_closure_set(v___f_342_, 0, v_mvarId_312_);
lean_closure_set(v___f_342_, 1, v_xs_319_);
lean_closure_set(v___f_342_, 2, v___x_341_);
lean_closure_set(v___f_342_, 3, v_args_320_);
lean_closure_set(v___f_342_, 4, v_a_340_);
v___x_343_ = ((lean_object*)(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__3));
v___x_344_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___redArg(v___x_343_, v_a_331_, v___f_342_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
return v___x_344_;
}
else
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_352_; 
lean_dec(v_a_331_);
lean_dec_ref(v_args_320_);
lean_dec_ref(v_xs_319_);
lean_dec(v_mvarId_312_);
v_a_345_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_352_ == 0)
{
v___x_347_ = v___x_339_;
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_339_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_348_ == 0)
{
v___x_350_ = v___x_347_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_a_345_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
else
{
lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_360_; 
lean_dec_ref(v_args_320_);
lean_dec_ref(v_xs_319_);
lean_dec_ref(v_aSizeEqN_316_);
lean_dec(v_n_314_);
lean_dec_ref(v_a_313_);
lean_dec(v_mvarId_312_);
v_a_353_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_360_ == 0)
{
v___x_355_ = v___x_330_;
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_dec(v___x_330_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_358_; 
if (v_isShared_356_ == 0)
{
v___x_358_ = v___x_355_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_a_353_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
}
else
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_368_; 
lean_dec_ref(v_args_320_);
lean_dec_ref(v_xs_319_);
lean_dec_ref(v_aSizeEqN_316_);
lean_dec(v_n_314_);
lean_dec_ref(v_a_313_);
lean_dec(v_mvarId_312_);
v_a_361_ = lean_ctor_get(v___x_328_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_368_ == 0)
{
v___x_363_ = v___x_328_;
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___x_328_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_366_; 
if (v_isShared_364_ == 0)
{
v___x_366_ = v___x_363_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_a_361_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
else
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___f_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_369_ = lean_unsigned_to_nat(1u);
v___x_370_ = lean_nat_add(v_i_318_, v___x_369_);
lean_inc(v___x_370_);
lean_inc_ref(v_00_u03b1_317_);
lean_inc(v_xNamePrefix_315_);
v___f_371_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__1___boxed), 16, 10);
lean_closure_set(v___f_371_, 0, v_a_313_);
lean_closure_set(v___f_371_, 1, v_i_318_);
lean_closure_set(v___f_371_, 2, v_n_314_);
lean_closure_set(v___f_371_, 3, v_aSizeEqN_316_);
lean_closure_set(v___f_371_, 4, v_xs_319_);
lean_closure_set(v___f_371_, 5, v_args_320_);
lean_closure_set(v___f_371_, 6, v_mvarId_312_);
lean_closure_set(v___f_371_, 7, v_xNamePrefix_315_);
lean_closure_set(v___f_371_, 8, v_00_u03b1_317_);
lean_closure_set(v___f_371_, 9, v___x_370_);
v___x_372_ = lean_name_append_index_after(v_xNamePrefix_315_, v___x_370_);
v___x_373_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___redArg(v___x_372_, v_00_u03b1_317_, v___f_371_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
return v___x_373_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__1(lean_object* v_a_374_, lean_object* v_i_375_, lean_object* v_n_376_, lean_object* v_aSizeEqN_377_, lean_object* v_xs_378_, lean_object* v_args_379_, lean_object* v_mvarId_380_, lean_object* v_xNamePrefix_381_, lean_object* v_00_u03b1_382_, lean_object* v___x_383_, lean_object* v_xi_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v___x_390_; 
lean_inc_ref(v_aSizeEqN_377_);
lean_inc(v_n_376_);
lean_inc_ref(v_a_374_);
v___x_390_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit(v_a_374_, v_i_375_, v_n_376_, v_aSizeEqN_377_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_a_391_; lean_object* v_xs_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v_a_391_ = lean_ctor_get(v___x_390_, 0);
lean_inc(v_a_391_);
lean_dec_ref(v___x_390_);
v_xs_392_ = lean_array_push(v_xs_378_, v_xi_384_);
v___x_393_ = lean_array_push(v_args_379_, v_a_391_);
v___x_394_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop(v_mvarId_380_, v_a_374_, v_n_376_, v_xNamePrefix_381_, v_aSizeEqN_377_, v_00_u03b1_382_, v___x_383_, v_xs_392_, v___x_393_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
return v___x_394_;
}
else
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_402_; 
lean_dec_ref(v_xi_384_);
lean_dec(v___x_383_);
lean_dec_ref(v_00_u03b1_382_);
lean_dec(v_xNamePrefix_381_);
lean_dec(v_mvarId_380_);
lean_dec_ref(v_args_379_);
lean_dec_ref(v_xs_378_);
lean_dec_ref(v_aSizeEqN_377_);
lean_dec(v_n_376_);
lean_dec_ref(v_a_374_);
v_a_395_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_402_ == 0)
{
v___x_397_ = v___x_390_;
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_390_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_400_; 
if (v_isShared_398_ == 0)
{
v___x_400_ = v___x_397_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_a_395_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___boxed(lean_object* v_mvarId_403_, lean_object* v_a_404_, lean_object* v_n_405_, lean_object* v_xNamePrefix_406_, lean_object* v_aSizeEqN_407_, lean_object* v_00_u03b1_408_, lean_object* v_i_409_, lean_object* v_xs_410_, lean_object* v_args_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop(v_mvarId_403_, v_a_404_, v_n_405_, v_xNamePrefix_406_, v_aSizeEqN_407_, v_00_u03b1_408_, v_i_409_, v_xs_410_, v_args_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
lean_dec(v_a_415_);
lean_dec_ref(v_a_414_);
lean_dec(v_a_413_);
lean_dec_ref(v_a_412_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0(lean_object* v_00_u03b1_418_, lean_object* v_name_419_, uint8_t v_bi_420_, lean_object* v_type_421_, lean_object* v_k_422_, uint8_t v_kind_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg(v_name_419_, v_bi_420_, v_type_421_, v_k_422_, v_kind_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___boxed(lean_object* v_00_u03b1_430_, lean_object* v_name_431_, lean_object* v_bi_432_, lean_object* v_type_433_, lean_object* v_k_434_, lean_object* v_kind_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
uint8_t v_bi_boxed_441_; uint8_t v_kind_boxed_442_; lean_object* v_res_443_; 
v_bi_boxed_441_ = lean_unbox(v_bi_432_);
v_kind_boxed_442_ = lean_unbox(v_kind_435_);
v_res_443_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0(v_00_u03b1_430_, v_name_431_, v_bi_boxed_441_, v_type_433_, v_k_434_, v_kind_boxed_442_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0(lean_object* v_00_u03b1_444_, lean_object* v_name_445_, lean_object* v_type_446_, lean_object* v_k_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___redArg(v_name_445_, v_type_446_, v_k_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___boxed(lean_object* v_00_u03b1_454_, lean_object* v_name_455_, lean_object* v_type_456_, lean_object* v_k_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0(v_00_u03b1_454_, v_name_455_, v_type_456_, v_k_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_464_, lean_object* v_x_465_, lean_object* v_x_466_, lean_object* v_x_467_){
_start:
{
lean_object* v_ks_468_; lean_object* v_vs_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_493_; 
v_ks_468_ = lean_ctor_get(v_x_464_, 0);
v_vs_469_ = lean_ctor_get(v_x_464_, 1);
v_isSharedCheck_493_ = !lean_is_exclusive(v_x_464_);
if (v_isSharedCheck_493_ == 0)
{
v___x_471_ = v_x_464_;
v_isShared_472_ = v_isSharedCheck_493_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_vs_469_);
lean_inc(v_ks_468_);
lean_dec(v_x_464_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_493_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_473_; uint8_t v___x_474_; 
v___x_473_ = lean_array_get_size(v_ks_468_);
v___x_474_ = lean_nat_dec_lt(v_x_465_, v___x_473_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_478_; 
lean_dec(v_x_465_);
v___x_475_ = lean_array_push(v_ks_468_, v_x_466_);
v___x_476_ = lean_array_push(v_vs_469_, v_x_467_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 1, v___x_476_);
lean_ctor_set(v___x_471_, 0, v___x_475_);
v___x_478_ = v___x_471_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_475_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v___x_476_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
else
{
lean_object* v_k_x27_480_; uint8_t v___x_481_; 
v_k_x27_480_ = lean_array_fget_borrowed(v_ks_468_, v_x_465_);
v___x_481_ = l_Lean_instBEqMVarId_beq(v_x_466_, v_k_x27_480_);
if (v___x_481_ == 0)
{
lean_object* v___x_483_; 
if (v_isShared_472_ == 0)
{
v___x_483_ = v___x_471_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_ks_468_);
lean_ctor_set(v_reuseFailAlloc_487_, 1, v_vs_469_);
v___x_483_ = v_reuseFailAlloc_487_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = lean_unsigned_to_nat(1u);
v___x_485_ = lean_nat_add(v_x_465_, v___x_484_);
lean_dec(v_x_465_);
v_x_464_ = v___x_483_;
v_x_465_ = v___x_485_;
goto _start;
}
}
else
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_491_; 
v___x_488_ = lean_array_fset(v_ks_468_, v_x_465_, v_x_466_);
v___x_489_ = lean_array_fset(v_vs_469_, v_x_465_, v_x_467_);
lean_dec(v_x_465_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 1, v___x_489_);
lean_ctor_set(v___x_471_, 0, v___x_488_);
v___x_491_ = v___x_471_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_488_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v___x_489_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_494_, lean_object* v_k_495_, lean_object* v_v_496_){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = lean_unsigned_to_nat(0u);
v___x_498_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_494_, v___x_497_, v_k_495_, v_v_496_);
return v___x_498_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_499_; size_t v___x_500_; size_t v___x_501_; 
v___x_499_ = ((size_t)5ULL);
v___x_500_ = ((size_t)1ULL);
v___x_501_ = lean_usize_shift_left(v___x_500_, v___x_499_);
return v___x_501_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_502_; size_t v___x_503_; size_t v___x_504_; 
v___x_502_ = ((size_t)1ULL);
v___x_503_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_504_ = lean_usize_sub(v___x_503_, v___x_502_);
return v___x_504_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg(lean_object* v_x_506_, size_t v_x_507_, size_t v_x_508_, lean_object* v_x_509_, lean_object* v_x_510_){
_start:
{
if (lean_obj_tag(v_x_506_) == 0)
{
lean_object* v_es_511_; size_t v___x_512_; size_t v___x_513_; size_t v___x_514_; size_t v___x_515_; lean_object* v_j_516_; lean_object* v___x_517_; uint8_t v___x_518_; 
v_es_511_ = lean_ctor_get(v_x_506_, 0);
v___x_512_ = ((size_t)5ULL);
v___x_513_ = ((size_t)1ULL);
v___x_514_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_515_ = lean_usize_land(v_x_507_, v___x_514_);
v_j_516_ = lean_usize_to_nat(v___x_515_);
v___x_517_ = lean_array_get_size(v_es_511_);
v___x_518_ = lean_nat_dec_lt(v_j_516_, v___x_517_);
if (v___x_518_ == 0)
{
lean_dec(v_j_516_);
lean_dec(v_x_510_);
lean_dec(v_x_509_);
return v_x_506_;
}
else
{
lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_555_; 
lean_inc_ref(v_es_511_);
v_isSharedCheck_555_ = !lean_is_exclusive(v_x_506_);
if (v_isSharedCheck_555_ == 0)
{
lean_object* v_unused_556_; 
v_unused_556_ = lean_ctor_get(v_x_506_, 0);
lean_dec(v_unused_556_);
v___x_520_ = v_x_506_;
v_isShared_521_ = v_isSharedCheck_555_;
goto v_resetjp_519_;
}
else
{
lean_dec(v_x_506_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_555_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v_v_522_; lean_object* v___x_523_; lean_object* v_xs_x27_524_; lean_object* v___y_526_; 
v_v_522_ = lean_array_fget(v_es_511_, v_j_516_);
v___x_523_ = lean_box(0);
v_xs_x27_524_ = lean_array_fset(v_es_511_, v_j_516_, v___x_523_);
switch(lean_obj_tag(v_v_522_))
{
case 0:
{
lean_object* v_key_531_; lean_object* v_val_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_542_; 
v_key_531_ = lean_ctor_get(v_v_522_, 0);
v_val_532_ = lean_ctor_get(v_v_522_, 1);
v_isSharedCheck_542_ = !lean_is_exclusive(v_v_522_);
if (v_isSharedCheck_542_ == 0)
{
v___x_534_ = v_v_522_;
v_isShared_535_ = v_isSharedCheck_542_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_val_532_);
lean_inc(v_key_531_);
lean_dec(v_v_522_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_542_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
uint8_t v___x_536_; 
v___x_536_ = l_Lean_instBEqMVarId_beq(v_x_509_, v_key_531_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; lean_object* v___x_538_; 
lean_del_object(v___x_534_);
v___x_537_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_531_, v_val_532_, v_x_509_, v_x_510_);
v___x_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
v___y_526_ = v___x_538_;
goto v___jp_525_;
}
else
{
lean_object* v___x_540_; 
lean_dec(v_val_532_);
lean_dec(v_key_531_);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 1, v_x_510_);
lean_ctor_set(v___x_534_, 0, v_x_509_);
v___x_540_ = v___x_534_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_x_509_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v_x_510_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
v___y_526_ = v___x_540_;
goto v___jp_525_;
}
}
}
}
case 1:
{
lean_object* v_node_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_553_; 
v_node_543_ = lean_ctor_get(v_v_522_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v_v_522_);
if (v_isSharedCheck_553_ == 0)
{
v___x_545_ = v_v_522_;
v_isShared_546_ = v_isSharedCheck_553_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_node_543_);
lean_dec(v_v_522_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_553_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
size_t v___x_547_; size_t v___x_548_; lean_object* v___x_549_; lean_object* v___x_551_; 
v___x_547_ = lean_usize_shift_right(v_x_507_, v___x_512_);
v___x_548_ = lean_usize_add(v_x_508_, v___x_513_);
v___x_549_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg(v_node_543_, v___x_547_, v___x_548_, v_x_509_, v_x_510_);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 0, v___x_549_);
v___x_551_ = v___x_545_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_549_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
v___y_526_ = v___x_551_;
goto v___jp_525_;
}
}
}
default: 
{
lean_object* v___x_554_; 
v___x_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_554_, 0, v_x_509_);
lean_ctor_set(v___x_554_, 1, v_x_510_);
v___y_526_ = v___x_554_;
goto v___jp_525_;
}
}
v___jp_525_:
{
lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_527_ = lean_array_fset(v_xs_x27_524_, v_j_516_, v___y_526_);
lean_dec(v_j_516_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___x_527_);
v___x_529_ = v___x_520_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_527_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
}
else
{
lean_object* v_ks_557_; lean_object* v_vs_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_578_; 
v_ks_557_ = lean_ctor_get(v_x_506_, 0);
v_vs_558_ = lean_ctor_get(v_x_506_, 1);
v_isSharedCheck_578_ = !lean_is_exclusive(v_x_506_);
if (v_isSharedCheck_578_ == 0)
{
v___x_560_ = v_x_506_;
v_isShared_561_ = v_isSharedCheck_578_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_vs_558_);
lean_inc(v_ks_557_);
lean_dec(v_x_506_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_578_;
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
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_ks_557_);
lean_ctor_set(v_reuseFailAlloc_577_, 1, v_vs_558_);
v___x_563_ = v_reuseFailAlloc_577_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
lean_object* v_newNode_564_; uint8_t v___y_566_; size_t v___x_572_; uint8_t v___x_573_; 
v_newNode_564_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2___redArg(v___x_563_, v_x_509_, v_x_510_);
v___x_572_ = ((size_t)7ULL);
v___x_573_ = lean_usize_dec_le(v___x_572_, v_x_508_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_574_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_564_);
v___x_575_ = lean_unsigned_to_nat(4u);
v___x_576_ = lean_nat_dec_lt(v___x_574_, v___x_575_);
lean_dec(v___x_574_);
v___y_566_ = v___x_576_;
goto v___jp_565_;
}
else
{
v___y_566_ = v___x_573_;
goto v___jp_565_;
}
v___jp_565_:
{
if (v___y_566_ == 0)
{
lean_object* v_ks_567_; lean_object* v_vs_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v_ks_567_ = lean_ctor_get(v_newNode_564_, 0);
lean_inc_ref(v_ks_567_);
v_vs_568_ = lean_ctor_get(v_newNode_564_, 1);
lean_inc_ref(v_vs_568_);
lean_dec_ref(v_newNode_564_);
v___x_569_ = lean_unsigned_to_nat(0u);
v___x_570_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_571_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3___redArg(v_x_508_, v_ks_567_, v_vs_568_, v___x_569_, v___x_570_);
lean_dec_ref(v_vs_568_);
lean_dec_ref(v_ks_567_);
return v___x_571_;
}
else
{
return v_newNode_564_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_579_, lean_object* v_keys_580_, lean_object* v_vals_581_, lean_object* v_i_582_, lean_object* v_entries_583_){
_start:
{
lean_object* v___x_584_; uint8_t v___x_585_; 
v___x_584_ = lean_array_get_size(v_keys_580_);
v___x_585_ = lean_nat_dec_lt(v_i_582_, v___x_584_);
if (v___x_585_ == 0)
{
lean_dec(v_i_582_);
return v_entries_583_;
}
else
{
lean_object* v_k_586_; lean_object* v_v_587_; uint64_t v___x_588_; size_t v_h_589_; size_t v___x_590_; lean_object* v___x_591_; size_t v___x_592_; size_t v___x_593_; size_t v___x_594_; size_t v_h_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v_k_586_ = lean_array_fget_borrowed(v_keys_580_, v_i_582_);
v_v_587_ = lean_array_fget_borrowed(v_vals_581_, v_i_582_);
v___x_588_ = l_Lean_instHashableMVarId_hash(v_k_586_);
v_h_589_ = lean_uint64_to_usize(v___x_588_);
v___x_590_ = ((size_t)5ULL);
v___x_591_ = lean_unsigned_to_nat(1u);
v___x_592_ = ((size_t)1ULL);
v___x_593_ = lean_usize_sub(v_depth_579_, v___x_592_);
v___x_594_ = lean_usize_mul(v___x_590_, v___x_593_);
v_h_595_ = lean_usize_shift_right(v_h_589_, v___x_594_);
v___x_596_ = lean_nat_add(v_i_582_, v___x_591_);
lean_dec(v_i_582_);
lean_inc(v_v_587_);
lean_inc(v_k_586_);
v___x_597_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg(v_entries_583_, v_h_595_, v_depth_579_, v_k_586_, v_v_587_);
v_i_582_ = v___x_596_;
v_entries_583_ = v___x_597_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_599_, lean_object* v_keys_600_, lean_object* v_vals_601_, lean_object* v_i_602_, lean_object* v_entries_603_){
_start:
{
size_t v_depth_boxed_604_; lean_object* v_res_605_; 
v_depth_boxed_604_ = lean_unbox_usize(v_depth_599_);
lean_dec(v_depth_599_);
v_res_605_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_604_, v_keys_600_, v_vals_601_, v_i_602_, v_entries_603_);
lean_dec_ref(v_vals_601_);
lean_dec_ref(v_keys_600_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_606_, lean_object* v_x_607_, lean_object* v_x_608_, lean_object* v_x_609_, lean_object* v_x_610_){
_start:
{
size_t v_x_998__boxed_611_; size_t v_x_999__boxed_612_; lean_object* v_res_613_; 
v_x_998__boxed_611_ = lean_unbox_usize(v_x_607_);
lean_dec(v_x_607_);
v_x_999__boxed_612_ = lean_unbox_usize(v_x_608_);
lean_dec(v_x_608_);
v_res_613_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg(v_x_606_, v_x_998__boxed_611_, v_x_999__boxed_612_, v_x_609_, v_x_610_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0___redArg(lean_object* v_x_614_, lean_object* v_x_615_, lean_object* v_x_616_){
_start:
{
uint64_t v___x_617_; size_t v___x_618_; size_t v___x_619_; lean_object* v___x_620_; 
v___x_617_ = l_Lean_instHashableMVarId_hash(v_x_615_);
v___x_618_ = lean_uint64_to_usize(v___x_617_);
v___x_619_ = ((size_t)1ULL);
v___x_620_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg(v_x_614_, v___x_618_, v___x_619_, v_x_615_, v_x_616_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0___redArg(lean_object* v_mvarId_621_, lean_object* v_val_622_, lean_object* v___y_623_){
_start:
{
lean_object* v___x_625_; lean_object* v_mctx_626_; lean_object* v_cache_627_; lean_object* v_zetaDeltaFVarIds_628_; lean_object* v_postponed_629_; lean_object* v_diag_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_658_; 
v___x_625_ = lean_st_ref_take(v___y_623_);
v_mctx_626_ = lean_ctor_get(v___x_625_, 0);
v_cache_627_ = lean_ctor_get(v___x_625_, 1);
v_zetaDeltaFVarIds_628_ = lean_ctor_get(v___x_625_, 2);
v_postponed_629_ = lean_ctor_get(v___x_625_, 3);
v_diag_630_ = lean_ctor_get(v___x_625_, 4);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_658_ == 0)
{
v___x_632_ = v___x_625_;
v_isShared_633_ = v_isSharedCheck_658_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_diag_630_);
lean_inc(v_postponed_629_);
lean_inc(v_zetaDeltaFVarIds_628_);
lean_inc(v_cache_627_);
lean_inc(v_mctx_626_);
lean_dec(v___x_625_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_658_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v_depth_634_; lean_object* v_levelAssignDepth_635_; lean_object* v_lmvarCounter_636_; lean_object* v_mvarCounter_637_; lean_object* v_lDecls_638_; lean_object* v_decls_639_; lean_object* v_userNames_640_; lean_object* v_lAssignment_641_; lean_object* v_eAssignment_642_; lean_object* v_dAssignment_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_657_; 
v_depth_634_ = lean_ctor_get(v_mctx_626_, 0);
v_levelAssignDepth_635_ = lean_ctor_get(v_mctx_626_, 1);
v_lmvarCounter_636_ = lean_ctor_get(v_mctx_626_, 2);
v_mvarCounter_637_ = lean_ctor_get(v_mctx_626_, 3);
v_lDecls_638_ = lean_ctor_get(v_mctx_626_, 4);
v_decls_639_ = lean_ctor_get(v_mctx_626_, 5);
v_userNames_640_ = lean_ctor_get(v_mctx_626_, 6);
v_lAssignment_641_ = lean_ctor_get(v_mctx_626_, 7);
v_eAssignment_642_ = lean_ctor_get(v_mctx_626_, 8);
v_dAssignment_643_ = lean_ctor_get(v_mctx_626_, 9);
v_isSharedCheck_657_ = !lean_is_exclusive(v_mctx_626_);
if (v_isSharedCheck_657_ == 0)
{
v___x_645_ = v_mctx_626_;
v_isShared_646_ = v_isSharedCheck_657_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_dAssignment_643_);
lean_inc(v_eAssignment_642_);
lean_inc(v_lAssignment_641_);
lean_inc(v_userNames_640_);
lean_inc(v_decls_639_);
lean_inc(v_lDecls_638_);
lean_inc(v_mvarCounter_637_);
lean_inc(v_lmvarCounter_636_);
lean_inc(v_levelAssignDepth_635_);
lean_inc(v_depth_634_);
lean_dec(v_mctx_626_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_657_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_647_; lean_object* v___x_649_; 
v___x_647_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0___redArg(v_eAssignment_642_, v_mvarId_621_, v_val_622_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 8, v___x_647_);
v___x_649_ = v___x_645_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_depth_634_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v_levelAssignDepth_635_);
lean_ctor_set(v_reuseFailAlloc_656_, 2, v_lmvarCounter_636_);
lean_ctor_set(v_reuseFailAlloc_656_, 3, v_mvarCounter_637_);
lean_ctor_set(v_reuseFailAlloc_656_, 4, v_lDecls_638_);
lean_ctor_set(v_reuseFailAlloc_656_, 5, v_decls_639_);
lean_ctor_set(v_reuseFailAlloc_656_, 6, v_userNames_640_);
lean_ctor_set(v_reuseFailAlloc_656_, 7, v_lAssignment_641_);
lean_ctor_set(v_reuseFailAlloc_656_, 8, v___x_647_);
lean_ctor_set(v_reuseFailAlloc_656_, 9, v_dAssignment_643_);
v___x_649_ = v_reuseFailAlloc_656_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_object* v___x_651_; 
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 0, v___x_649_);
v___x_651_ = v___x_632_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v___x_649_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v_cache_627_);
lean_ctor_set(v_reuseFailAlloc_655_, 2, v_zetaDeltaFVarIds_628_);
lean_ctor_set(v_reuseFailAlloc_655_, 3, v_postponed_629_);
lean_ctor_set(v_reuseFailAlloc_655_, 4, v_diag_630_);
v___x_651_ = v_reuseFailAlloc_655_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_652_ = lean_st_ref_set(v___y_623_, v___x_651_);
v___x_653_ = lean_box(0);
v___x_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
return v___x_654_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0___redArg___boxed(lean_object* v_mvarId_659_, lean_object* v_val_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0___redArg(v_mvarId_659_, v_val_660_, v___y_661_);
lean_dec(v___y_661_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit(lean_object* v_mvarId_666_, lean_object* v_a_667_, lean_object* v_n_668_, lean_object* v_xNamePrefix_669_, lean_object* v_aSizeEqN_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
lean_object* v___x_676_; 
lean_inc_ref(v_a_667_);
v___x_676_ = l_Lean_Meta_getArrayArgType(v_a_667_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v_a_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v_a_677_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_a_677_);
lean_dec_ref(v___x_676_);
v___x_678_ = lean_unsigned_to_nat(0u);
v___x_679_ = ((lean_object*)(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit___closed__0));
lean_inc(v_mvarId_666_);
v___x_680_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop(v_mvarId_666_, v_a_667_, v_n_668_, v_xNamePrefix_669_, v_aSizeEqN_670_, v_a_677_, v___x_678_, v___x_679_, v___x_679_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v_a_681_; lean_object* v_fst_682_; lean_object* v_snd_683_; lean_object* v___x_684_; 
v_a_681_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_a_681_);
lean_dec_ref(v___x_680_);
v_fst_682_ = lean_ctor_get(v_a_681_, 0);
lean_inc(v_fst_682_);
v_snd_683_ = lean_ctor_get(v_a_681_, 1);
lean_inc(v_snd_683_);
lean_dec(v_a_681_);
lean_inc(v_mvarId_666_);
v___x_684_ = l_Lean_MVarId_getTag(v_mvarId_666_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; lean_object* v___x_686_; 
v_a_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc(v_a_685_);
lean_dec_ref(v___x_684_);
v___x_686_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_fst_682_, v_a_685_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_697_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc_n(v_a_687_, 2);
lean_dec_ref(v___x_686_);
v___x_688_ = l_Lean_mkAppN(v_a_687_, v_snd_683_);
lean_dec(v_snd_683_);
v___x_689_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0___redArg(v_mvarId_666_, v___x_688_, v_a_672_);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_697_ == 0)
{
lean_object* v_unused_698_; 
v_unused_698_ = lean_ctor_get(v___x_689_, 0);
lean_dec(v_unused_698_);
v___x_691_ = v___x_689_;
v_isShared_692_ = v_isSharedCheck_697_;
goto v_resetjp_690_;
}
else
{
lean_dec(v___x_689_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_697_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_693_; lean_object* v___x_695_; 
v___x_693_ = l_Lean_Expr_mvarId_x21(v_a_687_);
lean_dec(v_a_687_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v___x_693_);
v___x_695_ = v___x_691_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v___x_693_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
else
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
lean_dec(v_snd_683_);
lean_dec(v_mvarId_666_);
v_a_699_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___x_686_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_686_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_a_699_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
else
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
lean_dec(v_snd_683_);
lean_dec(v_fst_682_);
lean_dec(v_mvarId_666_);
v_a_707_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_684_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_684_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
else
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_722_; 
lean_dec(v_mvarId_666_);
v_a_715_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_722_ == 0)
{
v___x_717_ = v___x_680_;
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_680_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_720_; 
if (v_isShared_718_ == 0)
{
v___x_720_ = v___x_717_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_a_715_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
else
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
lean_dec_ref(v_aSizeEqN_670_);
lean_dec(v_xNamePrefix_669_);
lean_dec(v_n_668_);
lean_dec_ref(v_a_667_);
lean_dec(v_mvarId_666_);
v_a_723_ = lean_ctor_get(v___x_676_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_730_ == 0)
{
v___x_725_ = v___x_676_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_676_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_723_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit___boxed(lean_object* v_mvarId_731_, lean_object* v_a_732_, lean_object* v_n_733_, lean_object* v_xNamePrefix_734_, lean_object* v_aSizeEqN_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit(v_mvarId_731_, v_a_732_, v_n_733_, v_xNamePrefix_734_, v_aSizeEqN_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_);
lean_dec(v_a_739_);
lean_dec_ref(v_a_738_);
lean_dec(v_a_737_);
lean_dec_ref(v_a_736_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0(lean_object* v_mvarId_742_, lean_object* v_val_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0___redArg(v_mvarId_742_, v_val_743_, v___y_745_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0___boxed(lean_object* v_mvarId_750_, lean_object* v_val_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0(v_mvarId_750_, v_val_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0(lean_object* v_00_u03b2_758_, lean_object* v_x_759_, lean_object* v_x_760_, lean_object* v_x_761_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0___redArg(v_x_759_, v_x_760_, v_x_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_763_, lean_object* v_x_764_, size_t v_x_765_, size_t v_x_766_, lean_object* v_x_767_, lean_object* v_x_768_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg(v_x_764_, v_x_765_, v_x_766_, v_x_767_, v_x_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_770_, lean_object* v_x_771_, lean_object* v_x_772_, lean_object* v_x_773_, lean_object* v_x_774_, lean_object* v_x_775_){
_start:
{
size_t v_x_1364__boxed_776_; size_t v_x_1365__boxed_777_; lean_object* v_res_778_; 
v_x_1364__boxed_776_ = lean_unbox_usize(v_x_772_);
lean_dec(v_x_772_);
v_x_1365__boxed_777_ = lean_unbox_usize(v_x_773_);
lean_dec(v_x_773_);
v_res_778_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1(v_00_u03b2_770_, v_x_771_, v_x_1364__boxed_776_, v_x_1365__boxed_777_, v_x_774_, v_x_775_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_779_, lean_object* v_n_780_, lean_object* v_k_781_, lean_object* v_v_782_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2___redArg(v_n_780_, v_k_781_, v_v_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_784_, size_t v_depth_785_, lean_object* v_keys_786_, lean_object* v_vals_787_, lean_object* v_heq_788_, lean_object* v_i_789_, lean_object* v_entries_790_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_785_, v_keys_786_, v_vals_787_, v_i_789_, v_entries_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_792_, lean_object* v_depth_793_, lean_object* v_keys_794_, lean_object* v_vals_795_, lean_object* v_heq_796_, lean_object* v_i_797_, lean_object* v_entries_798_){
_start:
{
size_t v_depth_boxed_799_; lean_object* v_res_800_; 
v_depth_boxed_799_ = lean_unbox_usize(v_depth_793_);
lean_dec(v_depth_793_);
v_res_800_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_792_, v_depth_boxed_799_, v_keys_794_, v_vals_795_, v_heq_796_, v_i_797_, v_entries_798_);
lean_dec_ref(v_vals_795_);
lean_dec_ref(v_keys_794_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_801_, lean_object* v_x_802_, lean_object* v_x_803_, lean_object* v_x_804_, lean_object* v_x_805_){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_802_, v_x_803_, v_x_804_, v_x_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___redArg(lean_object* v_mvarId_807_, lean_object* v_x_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_807_, v_x_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_822_; 
v_a_815_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_822_ == 0)
{
v___x_817_ = v___x_814_;
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_814_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_820_; 
if (v_isShared_818_ == 0)
{
v___x_820_ = v___x_817_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_815_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
else
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_830_; 
v_a_823_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_830_ == 0)
{
v___x_825_ = v___x_814_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_814_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_823_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___redArg___boxed(lean_object* v_mvarId_831_, lean_object* v_x_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___redArg(v_mvarId_831_, v_x_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2(lean_object* v_00_u03b1_839_, lean_object* v_mvarId_840_, lean_object* v_x_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___redArg(v_mvarId_840_, v_x_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___boxed(lean_object* v_00_u03b1_848_, lean_object* v_mvarId_849_, lean_object* v_x_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2(v_00_u03b1_848_, v_mvarId_849_, v_x_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__0(size_t v_sz_857_, size_t v_i_858_, lean_object* v_bs_859_){
_start:
{
uint8_t v___x_860_; 
v___x_860_ = lean_usize_dec_lt(v_i_858_, v_sz_857_);
if (v___x_860_ == 0)
{
return v_bs_859_;
}
else
{
lean_object* v_v_861_; lean_object* v___x_862_; lean_object* v_bs_x27_863_; lean_object* v___x_864_; size_t v___x_865_; size_t v___x_866_; lean_object* v___x_867_; 
v_v_861_ = lean_array_uget(v_bs_859_, v_i_858_);
v___x_862_ = lean_unsigned_to_nat(0u);
v_bs_x27_863_ = lean_array_uset(v_bs_859_, v_i_858_, v___x_862_);
v___x_864_ = l_Lean_mkRawNatLit(v_v_861_);
v___x_865_ = ((size_t)1ULL);
v___x_866_ = lean_usize_add(v_i_858_, v___x_865_);
v___x_867_ = lean_array_uset(v_bs_x27_863_, v_i_858_, v___x_864_);
v_i_858_ = v___x_866_;
v_bs_859_ = v___x_867_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__0___boxed(lean_object* v_sz_869_, lean_object* v_i_870_, lean_object* v_bs_871_){
_start:
{
size_t v_sz_boxed_872_; size_t v_i_boxed_873_; lean_object* v_res_874_; 
v_sz_boxed_872_ = lean_unbox_usize(v_sz_869_);
lean_dec(v_sz_869_);
v_i_boxed_873_ = lean_unbox_usize(v_i_870_);
lean_dec(v_i_870_);
v_res_874_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__0(v_sz_boxed_872_, v_i_boxed_873_, v_bs_871_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg___lam__0(lean_object* v___x_875_, lean_object* v_mvarId_876_, lean_object* v_a_877_, lean_object* v___x_878_, lean_object* v_xNamePrefix_879_, uint8_t v_isZero_880_, lean_object* v___x_881_, lean_object* v_subst_882_, uint8_t v___x_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l_Lean_Meta_mkEqSymm(v___x_875_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v_a_890_; lean_object* v___x_891_; 
v_a_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_a_890_);
lean_dec_ref(v___x_889_);
lean_inc(v___x_878_);
v___x_891_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit(v_mvarId_876_, v_a_877_, v___x_878_, v_xNamePrefix_879_, v_a_890_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v_a_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v_a_892_ = lean_ctor_get(v___x_891_, 0);
lean_inc(v_a_892_);
lean_dec_ref(v___x_891_);
v___x_893_ = lean_box(0);
v___x_894_ = l_Lean_Meta_introNCore(v_a_892_, v___x_878_, v___x_893_, v_isZero_880_, v_isZero_880_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v_fst_896_; lean_object* v_snd_897_; lean_object* v___x_898_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_a_895_);
lean_dec_ref(v___x_894_);
v_fst_896_ = lean_ctor_get(v_a_895_, 0);
lean_inc(v_fst_896_);
v_snd_897_ = lean_ctor_get(v_a_895_, 1);
lean_inc(v_snd_897_);
lean_dec(v_a_895_);
v___x_898_ = l_Lean_Meta_intro1Core(v_snd_897_, v_isZero_880_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_object* v_a_899_; lean_object* v_fst_900_; lean_object* v_snd_901_; lean_object* v___x_902_; 
v_a_899_ = lean_ctor_get(v___x_898_, 0);
lean_inc(v_a_899_);
lean_dec_ref(v___x_898_);
v_fst_900_ = lean_ctor_get(v_a_899_, 0);
lean_inc(v_fst_900_);
v_snd_901_ = lean_ctor_get(v_a_899_, 1);
lean_inc(v_snd_901_);
lean_dec(v_a_899_);
v___x_902_ = l_Lean_MVarId_clear(v_snd_901_, v___x_881_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; lean_object* v___x_904_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_a_903_);
lean_dec_ref(v___x_902_);
v___x_904_ = l_Lean_Meta_substCore(v_a_903_, v_fst_900_, v_isZero_880_, v_subst_882_, v___x_883_, v_isZero_880_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_916_; 
v_a_905_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_916_ == 0)
{
v___x_907_ = v___x_904_;
v_isShared_908_ = v_isSharedCheck_916_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_904_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_916_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v_fst_909_; lean_object* v_snd_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_914_; 
v_fst_909_ = lean_ctor_get(v_a_905_, 0);
lean_inc(v_fst_909_);
v_snd_910_ = lean_ctor_get(v_a_905_, 1);
lean_inc(v_snd_910_);
lean_dec(v_a_905_);
v___x_911_ = ((lean_object*)(l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default___closed__0));
v___x_912_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_912_, 0, v_snd_910_);
lean_ctor_set(v___x_912_, 1, v_fst_896_);
lean_ctor_set(v___x_912_, 2, v___x_911_);
lean_ctor_set(v___x_912_, 3, v_fst_909_);
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 0, v___x_912_);
v___x_914_ = v___x_907_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_912_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
lean_dec(v_fst_896_);
v_a_917_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_904_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_904_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_917_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
else
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
lean_dec(v_fst_900_);
lean_dec(v_fst_896_);
lean_dec(v_subst_882_);
v_a_925_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_902_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_902_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
else
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_940_; 
lean_dec(v_fst_896_);
lean_dec(v_subst_882_);
lean_dec(v___x_881_);
v_a_933_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_940_ == 0)
{
v___x_935_ = v___x_898_;
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_898_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_938_; 
if (v_isShared_936_ == 0)
{
v___x_938_ = v___x_935_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_a_933_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
else
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_948_; 
lean_dec(v_subst_882_);
lean_dec(v___x_881_);
v_a_941_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_948_ == 0)
{
v___x_943_ = v___x_894_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_894_);
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
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_a_941_);
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
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
lean_dec(v_subst_882_);
lean_dec(v___x_881_);
lean_dec(v___x_878_);
v_a_949_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___x_891_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_891_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_949_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
else
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
lean_dec(v_subst_882_);
lean_dec(v___x_881_);
lean_dec(v_xNamePrefix_879_);
lean_dec(v___x_878_);
lean_dec_ref(v_a_877_);
lean_dec(v_mvarId_876_);
v_a_957_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_964_ == 0)
{
v___x_959_ = v___x_889_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_889_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_957_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg___lam__0___boxed(lean_object* v___x_965_, lean_object* v_mvarId_966_, lean_object* v_a_967_, lean_object* v___x_968_, lean_object* v_xNamePrefix_969_, lean_object* v_isZero_970_, lean_object* v___x_971_, lean_object* v_subst_972_, lean_object* v___x_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
uint8_t v_isZero_boxed_979_; uint8_t v___x_3732__boxed_980_; lean_object* v_res_981_; 
v_isZero_boxed_979_ = lean_unbox(v_isZero_970_);
v___x_3732__boxed_980_ = lean_unbox(v___x_973_);
v_res_981_ = l_Array_mapFinIdxM_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg___lam__0(v___x_965_, v_mvarId_966_, v_a_967_, v___x_968_, v_xNamePrefix_969_, v_isZero_boxed_979_, v___x_971_, v_subst_972_, v___x_3732__boxed_980_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__1(lean_object* v_fst_982_, size_t v_sz_983_, size_t v_i_984_, lean_object* v_bs_985_){
_start:
{
uint8_t v___x_986_; 
v___x_986_ = lean_usize_dec_lt(v_i_984_, v_sz_983_);
if (v___x_986_ == 0)
{
return v_bs_985_;
}
else
{
lean_object* v_v_987_; lean_object* v___x_988_; lean_object* v_bs_x27_989_; lean_object* v___x_990_; lean_object* v___x_991_; size_t v___x_992_; size_t v___x_993_; lean_object* v___x_994_; 
v_v_987_ = lean_array_uget(v_bs_985_, v_i_984_);
v___x_988_ = lean_unsigned_to_nat(0u);
v_bs_x27_989_ = lean_array_uset(v_bs_985_, v_i_984_, v___x_988_);
v___x_990_ = l_Lean_Meta_FVarSubst_get(v_fst_982_, v_v_987_);
v___x_991_ = l_Lean_Expr_fvarId_x21(v___x_990_);
lean_dec_ref(v___x_990_);
v___x_992_ = ((size_t)1ULL);
v___x_993_ = lean_usize_add(v_i_984_, v___x_992_);
v___x_994_ = lean_array_uset(v_bs_x27_989_, v_i_984_, v___x_991_);
v_i_984_ = v___x_993_;
v_bs_985_ = v___x_994_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__1___boxed(lean_object* v_fst_996_, lean_object* v_sz_997_, lean_object* v_i_998_, lean_object* v_bs_999_){
_start:
{
size_t v_sz_boxed_1000_; size_t v_i_boxed_1001_; lean_object* v_res_1002_; 
v_sz_boxed_1000_ = lean_unbox_usize(v_sz_997_);
lean_dec(v_sz_997_);
v_i_boxed_1001_ = lean_unbox_usize(v_i_998_);
lean_dec(v_i_998_);
v_res_1002_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__1(v_fst_996_, v_sz_boxed_1000_, v_i_boxed_1001_, v_bs_999_);
lean_dec(v_fst_996_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg(lean_object* v_sizes_1003_, lean_object* v_fst_1004_, lean_object* v_a_1005_, lean_object* v_xNamePrefix_1006_, lean_object* v_as_1007_, lean_object* v_i_1008_, lean_object* v_j_1009_, lean_object* v_bs_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v_zero_1016_; uint8_t v_isZero_1017_; 
v_zero_1016_ = lean_unsigned_to_nat(0u);
v_isZero_1017_ = lean_nat_dec_eq(v_i_1008_, v_zero_1016_);
if (v_isZero_1017_ == 1)
{
lean_object* v___x_1018_; 
lean_dec(v_j_1009_);
lean_dec(v_i_1008_);
lean_dec(v_xNamePrefix_1006_);
lean_dec_ref(v_a_1005_);
lean_dec(v_fst_1004_);
v___x_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1018_, 0, v_bs_1010_);
return v___x_1018_;
}
else
{
lean_object* v___x_1019_; lean_object* v_mvarId_1020_; lean_object* v_newHs_1021_; lean_object* v_subst_1022_; uint8_t v___x_1023_; lean_object* v_one_1024_; lean_object* v_n_1025_; lean_object* v_a_1027_; lean_object* v___x_1031_; uint8_t v___x_1032_; 
v___x_1019_ = lean_array_fget_borrowed(v_as_1007_, v_j_1009_);
v_mvarId_1020_ = lean_ctor_get(v___x_1019_, 0);
v_newHs_1021_ = lean_ctor_get(v___x_1019_, 1);
v_subst_1022_ = lean_ctor_get(v___x_1019_, 2);
v___x_1023_ = 1;
v_one_1024_ = lean_unsigned_to_nat(1u);
v_n_1025_ = lean_nat_sub(v_i_1008_, v_one_1024_);
lean_dec(v_i_1008_);
v___x_1031_ = lean_array_get_size(v_sizes_1003_);
v___x_1032_ = lean_nat_dec_lt(v_j_1009_, v___x_1031_);
if (v___x_1032_ == 0)
{
lean_object* v___x_1033_; 
lean_inc(v_subst_1022_);
lean_inc(v_fst_1004_);
lean_inc(v_mvarId_1020_);
v___x_1033_ = l_Lean_Meta_substCore(v_mvarId_1020_, v_fst_1004_, v___x_1032_, v_subst_1022_, v___x_1023_, v___x_1032_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v_a_1034_; lean_object* v_fst_1035_; lean_object* v_snd_1036_; size_t v_sz_1037_; size_t v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
lean_inc(v_a_1034_);
lean_dec_ref(v___x_1033_);
v_fst_1035_ = lean_ctor_get(v_a_1034_, 0);
lean_inc(v_fst_1035_);
v_snd_1036_ = lean_ctor_get(v_a_1034_, 1);
lean_inc(v_snd_1036_);
lean_dec(v_a_1034_);
v_sz_1037_ = lean_array_size(v_newHs_1021_);
v___x_1038_ = ((size_t)0ULL);
lean_inc_ref(v_newHs_1021_);
v___x_1039_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__1(v_fst_1035_, v_sz_1037_, v___x_1038_, v_newHs_1021_);
v___x_1040_ = ((lean_object*)(l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default___closed__0));
v___x_1041_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1041_, 0, v_snd_1036_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
lean_ctor_set(v___x_1041_, 2, v___x_1039_);
lean_ctor_set(v___x_1041_, 3, v_fst_1035_);
v_a_1027_ = v___x_1041_;
goto v___jp_1026_;
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
lean_dec(v_n_1025_);
lean_dec_ref(v_bs_1010_);
lean_dec(v_j_1009_);
lean_dec(v_xNamePrefix_1006_);
lean_dec_ref(v_a_1005_);
lean_dec(v_fst_1004_);
v_a_1042_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_1033_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1033_);
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
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1042_);
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
else
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___f_1056_; lean_object* v___x_1057_; 
lean_inc(v_fst_1004_);
v___x_1050_ = l_Lean_Meta_FVarSubst_get(v_subst_1022_, v_fst_1004_);
v___x_1051_ = l_Lean_Expr_fvarId_x21(v___x_1050_);
lean_dec_ref(v___x_1050_);
v___x_1052_ = lean_array_fget_borrowed(v_sizes_1003_, v_j_1009_);
lean_inc(v___x_1051_);
v___x_1053_ = l_Lean_mkFVar(v___x_1051_);
v___x_1054_ = lean_box(v_isZero_1017_);
v___x_1055_ = lean_box(v___x_1023_);
lean_inc(v_subst_1022_);
lean_inc(v_xNamePrefix_1006_);
lean_inc(v___x_1052_);
lean_inc_ref(v_a_1005_);
lean_inc_n(v_mvarId_1020_, 2);
v___f_1056_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1056_, 0, v___x_1053_);
lean_closure_set(v___f_1056_, 1, v_mvarId_1020_);
lean_closure_set(v___f_1056_, 2, v_a_1005_);
lean_closure_set(v___f_1056_, 3, v___x_1052_);
lean_closure_set(v___f_1056_, 4, v_xNamePrefix_1006_);
lean_closure_set(v___f_1056_, 5, v___x_1054_);
lean_closure_set(v___f_1056_, 6, v___x_1051_);
lean_closure_set(v___f_1056_, 7, v_subst_1022_);
lean_closure_set(v___f_1056_, 8, v___x_1055_);
v___x_1057_ = l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___redArg(v_mvarId_1020_, v___f_1056_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_object* v_a_1058_; 
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc(v_a_1058_);
lean_dec_ref(v___x_1057_);
v_a_1027_ = v_a_1058_;
goto v___jp_1026_;
}
else
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1066_; 
lean_dec(v_n_1025_);
lean_dec_ref(v_bs_1010_);
lean_dec(v_j_1009_);
lean_dec(v_xNamePrefix_1006_);
lean_dec_ref(v_a_1005_);
lean_dec(v_fst_1004_);
v_a_1059_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1061_ = v___x_1057_;
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1057_);
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
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_a_1059_);
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
v___jp_1026_:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = lean_nat_add(v_j_1009_, v_one_1024_);
lean_dec(v_j_1009_);
v___x_1029_ = lean_array_push(v_bs_1010_, v_a_1027_);
v_i_1008_ = v_n_1025_;
v_j_1009_ = v___x_1028_;
v_bs_1010_ = v___x_1029_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg___boxed(lean_object* v_sizes_1067_, lean_object* v_fst_1068_, lean_object* v_a_1069_, lean_object* v_xNamePrefix_1070_, lean_object* v_as_1071_, lean_object* v_i_1072_, lean_object* v_j_1073_, lean_object* v_bs_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Array_mapFinIdxM_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg(v_sizes_1067_, v_fst_1068_, v_a_1069_, v_xNamePrefix_1070_, v_as_1071_, v_i_1072_, v_j_1073_, v_bs_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec_ref(v_as_1071_);
lean_dec_ref(v_sizes_1067_);
return v_res_1080_;
}
}
static lean_object* _init_l_Lean_Meta_caseArraySizes___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1087_ = lean_box(0);
v___x_1088_ = ((lean_object*)(l_Lean_Meta_caseArraySizes___lam__0___closed__3));
v___x_1089_ = l_Lean_mkConst(v___x_1088_, v___x_1087_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_caseArraySizes___lam__0(lean_object* v___x_1093_, lean_object* v___x_1094_, lean_object* v_mvarId_1095_, lean_object* v_sizes_1096_, lean_object* v_hNamePrefix_1097_, lean_object* v_a_1098_, lean_object* v_xNamePrefix_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v___x_1105_; 
v___x_1105_ = l_Lean_Meta_mkAppM(v___x_1093_, v___x_1094_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v_a_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_a_1106_);
lean_dec_ref(v___x_1105_);
v___x_1107_ = ((lean_object*)(l_Lean_Meta_caseArraySizes___lam__0___closed__1));
v___x_1108_ = lean_obj_once(&l_Lean_Meta_caseArraySizes___lam__0___closed__4, &l_Lean_Meta_caseArraySizes___lam__0___closed__4_once, _init_l_Lean_Meta_caseArraySizes___lam__0___closed__4);
v___x_1109_ = ((lean_object*)(l_Lean_Meta_caseArraySizes___lam__0___closed__6));
v___x_1110_ = l_Lean_MVarId_assertExt(v_mvarId_1095_, v___x_1107_, v___x_1108_, v_a_1106_, v___x_1109_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_a_1111_; uint8_t v___x_1112_; lean_object* v___x_1113_; 
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
lean_inc(v_a_1111_);
lean_dec_ref(v___x_1110_);
v___x_1112_ = 0;
v___x_1113_ = l_Lean_Meta_intro1Core(v_a_1111_, v___x_1112_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_object* v_a_1114_; lean_object* v_fst_1115_; lean_object* v_snd_1116_; lean_object* v___x_1117_; 
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
lean_inc(v_a_1114_);
lean_dec_ref(v___x_1113_);
v_fst_1115_ = lean_ctor_get(v_a_1114_, 0);
lean_inc(v_fst_1115_);
v_snd_1116_ = lean_ctor_get(v_a_1114_, 1);
lean_inc(v_snd_1116_);
lean_dec(v_a_1114_);
v___x_1117_ = l_Lean_Meta_intro1Core(v_snd_1116_, v___x_1112_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v_fst_1119_; lean_object* v_snd_1120_; size_t v_sz_1121_; size_t v___x_1122_; lean_object* v___x_1123_; uint8_t v___x_1124_; lean_object* v___x_1125_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1118_);
lean_dec_ref(v___x_1117_);
v_fst_1119_ = lean_ctor_get(v_a_1118_, 0);
lean_inc(v_fst_1119_);
v_snd_1120_ = lean_ctor_get(v_a_1118_, 1);
lean_inc(v_snd_1120_);
lean_dec(v_a_1118_);
v_sz_1121_ = lean_array_size(v_sizes_1096_);
v___x_1122_ = ((size_t)0ULL);
lean_inc_ref(v_sizes_1096_);
v___x_1123_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__0(v_sz_1121_, v___x_1122_, v_sizes_1096_);
v___x_1124_ = 1;
v___x_1125_ = l_Lean_Meta_caseValues(v_snd_1120_, v_fst_1115_, v___x_1123_, v_hNamePrefix_1097_, v___x_1124_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v_a_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v_a_1126_ = lean_ctor_get(v___x_1125_, 0);
lean_inc(v_a_1126_);
lean_dec_ref(v___x_1125_);
v___x_1127_ = lean_array_get_size(v_a_1126_);
v___x_1128_ = lean_unsigned_to_nat(0u);
v___x_1129_ = lean_mk_empty_array_with_capacity(v___x_1127_);
v___x_1130_ = l_Array_mapFinIdxM_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg(v_sizes_1096_, v_fst_1119_, v_a_1098_, v_xNamePrefix_1099_, v_a_1126_, v___x_1127_, v___x_1128_, v___x_1129_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
lean_dec(v_a_1126_);
lean_dec_ref(v_sizes_1096_);
return v___x_1130_;
}
else
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
lean_dec(v_fst_1119_);
lean_dec(v_xNamePrefix_1099_);
lean_dec_ref(v_a_1098_);
lean_dec_ref(v_sizes_1096_);
v_a_1131_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v___x_1125_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1125_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1131_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
else
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1146_; 
lean_dec(v_fst_1115_);
lean_dec(v_xNamePrefix_1099_);
lean_dec_ref(v_a_1098_);
lean_dec(v_hNamePrefix_1097_);
lean_dec_ref(v_sizes_1096_);
v_a_1139_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1141_ = v___x_1117_;
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1117_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1144_; 
if (v_isShared_1142_ == 0)
{
v___x_1144_ = v___x_1141_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_a_1139_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
else
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
lean_dec(v_xNamePrefix_1099_);
lean_dec_ref(v_a_1098_);
lean_dec(v_hNamePrefix_1097_);
lean_dec_ref(v_sizes_1096_);
v_a_1147_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1149_ = v___x_1113_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1113_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
if (v_isShared_1150_ == 0)
{
v___x_1152_ = v___x_1149_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1147_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
else
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1162_; 
lean_dec(v_xNamePrefix_1099_);
lean_dec_ref(v_a_1098_);
lean_dec(v_hNamePrefix_1097_);
lean_dec_ref(v_sizes_1096_);
v_a_1155_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1157_ = v___x_1110_;
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1110_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
if (v_isShared_1158_ == 0)
{
v___x_1160_ = v___x_1157_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_a_1155_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
else
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1170_; 
lean_dec(v_xNamePrefix_1099_);
lean_dec_ref(v_a_1098_);
lean_dec(v_hNamePrefix_1097_);
lean_dec_ref(v_sizes_1096_);
lean_dec(v_mvarId_1095_);
v_a_1163_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1165_ = v___x_1105_;
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1105_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1168_; 
if (v_isShared_1166_ == 0)
{
v___x_1168_ = v___x_1165_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_a_1163_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_caseArraySizes___lam__0___boxed(lean_object* v___x_1171_, lean_object* v___x_1172_, lean_object* v_mvarId_1173_, lean_object* v_sizes_1174_, lean_object* v_hNamePrefix_1175_, lean_object* v_a_1176_, lean_object* v_xNamePrefix_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_Lean_Meta_caseArraySizes___lam__0(v___x_1171_, v___x_1172_, v_mvarId_1173_, v_sizes_1174_, v_hNamePrefix_1175_, v_a_1176_, v_xNamePrefix_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_caseArraySizes(lean_object* v_mvarId_1188_, lean_object* v_fvarId_1189_, lean_object* v_sizes_1190_, lean_object* v_xNamePrefix_1191_, lean_object* v_hNamePrefix_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_){
_start:
{
lean_object* v_a_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___f_1203_; lean_object* v___x_1204_; 
v_a_1198_ = l_Lean_mkFVar(v_fvarId_1189_);
v___x_1199_ = ((lean_object*)(l_Lean_Meta_caseArraySizes___closed__1));
v___x_1200_ = lean_unsigned_to_nat(1u);
v___x_1201_ = lean_mk_empty_array_with_capacity(v___x_1200_);
lean_inc_ref(v_a_1198_);
v___x_1202_ = lean_array_push(v___x_1201_, v_a_1198_);
lean_inc(v_mvarId_1188_);
v___f_1203_ = lean_alloc_closure((void*)(l_Lean_Meta_caseArraySizes___lam__0___boxed), 12, 7);
lean_closure_set(v___f_1203_, 0, v___x_1199_);
lean_closure_set(v___f_1203_, 1, v___x_1202_);
lean_closure_set(v___f_1203_, 2, v_mvarId_1188_);
lean_closure_set(v___f_1203_, 3, v_sizes_1190_);
lean_closure_set(v___f_1203_, 4, v_hNamePrefix_1192_);
lean_closure_set(v___f_1203_, 5, v_a_1198_);
lean_closure_set(v___f_1203_, 6, v_xNamePrefix_1191_);
v___x_1204_ = l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___redArg(v_mvarId_1188_, v___f_1203_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_caseArraySizes___boxed(lean_object* v_mvarId_1205_, lean_object* v_fvarId_1206_, lean_object* v_sizes_1207_, lean_object* v_xNamePrefix_1208_, lean_object* v_hNamePrefix_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l_Lean_Meta_caseArraySizes(v_mvarId_1205_, v_fvarId_1206_, v_sizes_1207_, v_xNamePrefix_1208_, v_hNamePrefix_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
lean_dec(v_a_1213_);
lean_dec_ref(v_a_1212_);
lean_dec(v_a_1211_);
lean_dec_ref(v_a_1210_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_caseArraySizes_spec__3(lean_object* v_sizes_1216_, lean_object* v_fst_1217_, lean_object* v_a_1218_, lean_object* v_xNamePrefix_1219_, lean_object* v_as_1220_, lean_object* v_i_1221_, lean_object* v_j_1222_, lean_object* v_inv_1223_, lean_object* v_bs_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
lean_object* v___x_1230_; 
v___x_1230_ = l_Array_mapFinIdxM_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg(v_sizes_1216_, v_fst_1217_, v_a_1218_, v_xNamePrefix_1219_, v_as_1220_, v_i_1221_, v_j_1222_, v_bs_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_caseArraySizes_spec__3___boxed(lean_object* v_sizes_1231_, lean_object* v_fst_1232_, lean_object* v_a_1233_, lean_object* v_xNamePrefix_1234_, lean_object* v_as_1235_, lean_object* v_i_1236_, lean_object* v_j_1237_, lean_object* v_inv_1238_, lean_object* v_bs_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Array_mapFinIdxM_map___at___00Lean_Meta_caseArraySizes_spec__3(v_sizes_1231_, v_fst_1232_, v_a_1233_, v_xNamePrefix_1234_, v_as_1235_, v_i_1236_, v_j_1237_, v_inv_1238_, v_bs_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec_ref(v_as_1235_);
lean_dec_ref(v_sizes_1231_);
return v_res_1245_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_FVarSubst(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Match_CaseValues(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Subst(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Match_CaseArraySizes(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_FVarSubst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_CaseValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Subst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Match_CaseArraySizes(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_FVarSubst(uint8_t builtin);
lean_object* initialize_Lean_Meta_Match_CaseValues(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Subst(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Match_CaseArraySizes(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_FVarSubst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_CaseValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Subst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_CaseArraySizes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Match_CaseArraySizes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Match_CaseArraySizes(builtin);
}
#ifdef __cplusplus
}
#endif
