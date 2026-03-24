// Lean compiler output
// Module: Lean.Meta.Sym.SymM
// Imports: public import Lean.Meta.Sym.AlphaShareCommon public import Lean.Meta.CongrTheorems
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
extern lean_object* l_Lean_Int_mkType;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isDefEqI(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sym"};
static const lean_object* l_Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l_Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(230, 3, 132, 38, 134, 149, 222, 229)}};
static const lean_ctor_object l_Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(249, 1, 190, 45, 30, 82, 81, 176)}};
static const lean_object* l_Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_Sym_initFn___closed__3_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "check invariants"};
static const lean_object* l_Lean_Meta_Sym_initFn___closed__3_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Sym_initFn___closed__3_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_Sym_initFn___closed__4_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_initFn___closed__3_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Meta_Sym_initFn___closed__4_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Sym_initFn___closed__4_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sym"};
static const lean_object* l_Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(243, 157, 148, 19, 62, 70, 252, 55)}};
static const lean_ctor_object l_Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(254, 148, 146, 121, 82, 137, 202, 245)}};
static const lean_ctor_object l_Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_3),((lean_object*)&l_Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(81, 198, 26, 180, 162, 99, 75, 86)}};
static const lean_object* l_Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_sym_debug;
static const lean_ctor_object l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_instInhabitedProofInstArgInfo = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default___closed__0_value;
static const lean_array_object l_Lean_Meta_Sym_instInhabitedProofInstInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Sym_instInhabitedProofInstInfo_default___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedProofInstInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_instInhabitedProofInstInfo_default = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedProofInstInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_instInhabitedProofInstInfo = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedProofInstInfo_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_none_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_none_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_fixedPrefix_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_fixedPrefix_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_interlaced_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_interlaced_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_congrTheorem_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_congrTheorem_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__3_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__7 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__6_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__7_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__8 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__10 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__6_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__10_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__11 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12;
static lean_once_cell_t l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Ordering"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__14 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "eq"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__15 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__14_value),LEAN_SCALAR_PTR_LITERAL(226, 44, 125, 228, 251, 150, 72, 72)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__15_value),LEAN_SCALAR_PTR_LITERAL(103, 150, 86, 2, 28, 163, 164, 77)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__16 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__16_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__1___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_SymM_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_SymM_run___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Sym_SymM_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_SymM_run___redArg___closed__1;
static lean_once_cell_t l_Lean_Meta_Sym_SymM_run___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_SymM_run___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0___redArg(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_shareCommon___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_shareCommon___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Sym_shareCommon___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_shareCommon___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_share___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_share___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_share(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_share___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_33_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_isSharedCheck_33_ = !lean_is_exclusive(v_decl_2_);
if (v_isSharedCheck_33_ == 0)
{
v___x_8_ = v_decl_2_;
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_descr_6_);
lean_inc(v_defValue_5_);
lean_dec(v_decl_2_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; uint8_t v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_10_ = lean_alloc_ctor(1, 0, 1);
v___x_11_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_10_, 0, v___x_11_);
lean_inc(v_name_1_);
v___x_12_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_12_, 0, v_name_1_);
lean_ctor_set(v___x_12_, 1, v_ref_3_);
lean_ctor_set(v___x_12_, 2, v___x_10_);
lean_ctor_set(v___x_12_, 3, v_descr_6_);
lean_inc(v_name_1_);
v___x_13_ = lean_register_option(v_name_1_, v___x_12_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_23_; 
v_isSharedCheck_23_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_23_ == 0)
{
lean_object* v_unused_24_; 
v_unused_24_ = lean_ctor_get(v___x_13_, 0);
lean_dec(v_unused_24_);
v___x_15_ = v___x_13_;
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
else
{
lean_dec(v___x_13_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___x_18_; 
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v_defValue_5_);
lean_ctor_set(v___x_8_, 0, v_name_1_);
v___x_18_ = v___x_8_;
goto v_reusejp_17_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_name_1_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v_defValue_5_);
v___x_18_ = v_reuseFailAlloc_22_;
goto v_reusejp_17_;
}
v_reusejp_17_:
{
lean_object* v___x_20_; 
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 0, v___x_18_);
v___x_20_ = v___x_15_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v___x_18_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
}
else
{
lean_object* v_a_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_32_; 
lean_del_object(v___x_8_);
lean_dec(v_defValue_5_);
lean_dec(v_name_1_);
v_a_25_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_32_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_32_ == 0)
{
v___x_27_ = v___x_13_;
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_a_25_);
lean_dec(v___x_13_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___x_30_; 
if (v_isShared_28_ == 0)
{
v___x_30_ = v___x_27_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_a_25_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_34_, lean_object* v_decl_35_, lean_object* v_ref_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Option_register___at___00Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__spec__0(v_name_34_, v_decl_35_, v_ref_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_59_ = ((lean_object*)(l_Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_));
v___x_60_ = ((lean_object*)(l_Lean_Meta_Sym_initFn___closed__4_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_));
v___x_61_ = ((lean_object*)(l_Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_));
v___x_62_ = l_Lean_Option_register___at___00Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__spec__0(v___x_59_, v___x_60_, v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4____boxed(lean_object* v_a_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_();
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorIdx(lean_object* v_x_73_){
_start:
{
switch(lean_obj_tag(v_x_73_))
{
case 0:
{
lean_object* v___x_74_; 
v___x_74_ = lean_unsigned_to_nat(0u);
return v___x_74_;
}
case 1:
{
lean_object* v___x_75_; 
v___x_75_ = lean_unsigned_to_nat(1u);
return v___x_75_;
}
case 2:
{
lean_object* v___x_76_; 
v___x_76_ = lean_unsigned_to_nat(2u);
return v___x_76_;
}
default: 
{
lean_object* v___x_77_; 
v___x_77_ = lean_unsigned_to_nat(3u);
return v___x_77_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorIdx___boxed(lean_object* v_x_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Lean_Meta_Sym_CongrInfo_ctorIdx(v_x_78_);
lean_dec(v_x_78_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(lean_object* v_t_80_, lean_object* v_k_81_){
_start:
{
switch(lean_obj_tag(v_t_80_))
{
case 0:
{
return v_k_81_;
}
case 1:
{
lean_object* v_prefixSize_82_; lean_object* v_suffixSize_83_; lean_object* v___x_84_; 
v_prefixSize_82_ = lean_ctor_get(v_t_80_, 0);
lean_inc(v_prefixSize_82_);
v_suffixSize_83_ = lean_ctor_get(v_t_80_, 1);
lean_inc(v_suffixSize_83_);
lean_dec_ref(v_t_80_);
v___x_84_ = lean_apply_2(v_k_81_, v_prefixSize_82_, v_suffixSize_83_);
return v___x_84_;
}
default: 
{
lean_object* v_rewritable_85_; lean_object* v___x_86_; 
v_rewritable_85_ = lean_ctor_get(v_t_80_, 0);
lean_inc_ref(v_rewritable_85_);
lean_dec(v_t_80_);
v___x_86_ = lean_apply_1(v_k_81_, v_rewritable_85_);
return v___x_86_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorElim(lean_object* v_motive_87_, lean_object* v_ctorIdx_88_, lean_object* v_t_89_, lean_object* v_h_90_, lean_object* v_k_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_89_, v_k_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorElim___boxed(lean_object* v_motive_93_, lean_object* v_ctorIdx_94_, lean_object* v_t_95_, lean_object* v_h_96_, lean_object* v_k_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_Meta_Sym_CongrInfo_ctorElim(v_motive_93_, v_ctorIdx_94_, v_t_95_, v_h_96_, v_k_97_);
lean_dec(v_ctorIdx_94_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_none_elim___redArg(lean_object* v_t_99_, lean_object* v_none_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_99_, v_none_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_none_elim(lean_object* v_motive_102_, lean_object* v_t_103_, lean_object* v_h_104_, lean_object* v_none_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_103_, v_none_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_fixedPrefix_elim___redArg(lean_object* v_t_107_, lean_object* v_fixedPrefix_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_107_, v_fixedPrefix_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_fixedPrefix_elim(lean_object* v_motive_110_, lean_object* v_t_111_, lean_object* v_h_112_, lean_object* v_fixedPrefix_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_111_, v_fixedPrefix_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_interlaced_elim___redArg(lean_object* v_t_115_, lean_object* v_interlaced_116_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_115_, v_interlaced_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_interlaced_elim(lean_object* v_motive_118_, lean_object* v_t_119_, lean_object* v_h_120_, lean_object* v_interlaced_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_119_, v_interlaced_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_congrTheorem_elim___redArg(lean_object* v_t_123_, lean_object* v_congrTheorem_124_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_123_, v_congrTheorem_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_congrTheorem_elim(lean_object* v_motive_126_, lean_object* v_t_127_, lean_object* v_h_128_, lean_object* v_congrTheorem_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_127_, v_congrTheorem_129_);
return v___x_130_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2(void){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_134_ = lean_box(0);
v___x_135_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__1));
v___x_136_ = l_Lean_mkConst(v___x_135_, v___x_134_);
return v___x_136_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_140_ = lean_box(0);
v___x_141_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__4));
v___x_142_ = l_Lean_mkConst(v___x_141_, v___x_140_);
return v___x_142_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_148_ = lean_box(0);
v___x_149_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__8));
v___x_150_ = l_Lean_mkConst(v___x_149_, v___x_148_);
return v___x_150_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = lean_box(0);
v___x_156_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__11));
v___x_157_ = l_Lean_mkConst(v___x_156_, v___x_155_);
return v___x_157_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_158_ = lean_unsigned_to_nat(0u);
v___x_159_ = l_Lean_mkNatLit(v___x_158_);
return v___x_159_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_165_ = lean_box(0);
v___x_166_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__16));
v___x_167_ = l_Lean_mkConst(v___x_166_, v___x_165_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs(lean_object* v_a_168_){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v_fst_171_; lean_object* v_snd_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v_fst_175_; lean_object* v_snd_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v_fst_179_; lean_object* v_snd_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v_fst_183_; lean_object* v_snd_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v_fst_187_; lean_object* v_snd_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v_fst_191_; lean_object* v_snd_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v_fst_195_; lean_object* v_snd_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_204_; 
v___x_169_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2);
v___x_170_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_169_, v_a_168_);
v_fst_171_ = lean_ctor_get(v___x_170_, 0);
lean_inc(v_fst_171_);
v_snd_172_ = lean_ctor_get(v___x_170_, 1);
lean_inc(v_snd_172_);
lean_dec_ref(v___x_170_);
v___x_173_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5);
v___x_174_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_173_, v_snd_172_);
v_fst_175_ = lean_ctor_get(v___x_174_, 0);
lean_inc(v_fst_175_);
v_snd_176_ = lean_ctor_get(v___x_174_, 1);
lean_inc(v_snd_176_);
lean_dec_ref(v___x_174_);
v___x_177_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9);
v___x_178_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_177_, v_snd_176_);
v_fst_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_fst_179_);
v_snd_180_ = lean_ctor_get(v___x_178_, 1);
lean_inc(v_snd_180_);
lean_dec_ref(v___x_178_);
v___x_181_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12);
v___x_182_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_181_, v_snd_180_);
v_fst_183_ = lean_ctor_get(v___x_182_, 0);
lean_inc(v_fst_183_);
v_snd_184_ = lean_ctor_get(v___x_182_, 1);
lean_inc(v_snd_184_);
lean_dec_ref(v___x_182_);
v___x_185_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13);
v___x_186_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_185_, v_snd_184_);
v_fst_187_ = lean_ctor_get(v___x_186_, 0);
lean_inc(v_fst_187_);
v_snd_188_ = lean_ctor_get(v___x_186_, 1);
lean_inc(v_snd_188_);
lean_dec_ref(v___x_186_);
v___x_189_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17);
v___x_190_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_189_, v_snd_188_);
v_fst_191_ = lean_ctor_get(v___x_190_, 0);
lean_inc(v_fst_191_);
v_snd_192_ = lean_ctor_get(v___x_190_, 1);
lean_inc(v_snd_192_);
lean_dec_ref(v___x_190_);
v___x_193_ = l_Lean_Int_mkType;
v___x_194_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_193_, v_snd_192_);
v_fst_195_ = lean_ctor_get(v___x_194_, 0);
v_snd_196_ = lean_ctor_get(v___x_194_, 1);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_204_ == 0)
{
v___x_198_ = v___x_194_;
v_isShared_199_ = v_isSharedCheck_204_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_snd_196_);
lean_inc(v_fst_195_);
lean_dec(v___x_194_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_204_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_200_; lean_object* v___x_202_; 
v___x_200_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_200_, 0, v_fst_175_);
lean_ctor_set(v___x_200_, 1, v_fst_171_);
lean_ctor_set(v___x_200_, 2, v_fst_187_);
lean_ctor_set(v___x_200_, 3, v_fst_183_);
lean_ctor_set(v___x_200_, 4, v_fst_179_);
lean_ctor_set(v___x_200_, 5, v_fst_191_);
lean_ctor_set(v___x_200_, 6, v_fst_195_);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 0, v___x_200_);
v___x_202_ = v___x_198_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_200_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v_snd_196_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__0(void){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_205_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__1(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__0);
v___x_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0(lean_object* v_00_u03b2_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__1);
return v___x_209_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__1(lean_object* v_opts_210_, lean_object* v_opt_211_){
_start:
{
lean_object* v_name_212_; lean_object* v_defValue_213_; lean_object* v_map_214_; lean_object* v___x_215_; 
v_name_212_ = lean_ctor_get(v_opt_211_, 0);
v_defValue_213_ = lean_ctor_get(v_opt_211_, 1);
v_map_214_ = lean_ctor_get(v_opts_210_, 0);
v___x_215_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_214_, v_name_212_);
if (lean_obj_tag(v___x_215_) == 0)
{
uint8_t v___x_216_; 
v___x_216_ = lean_unbox(v_defValue_213_);
return v___x_216_;
}
else
{
lean_object* v_val_217_; 
v_val_217_ = lean_ctor_get(v___x_215_, 0);
lean_inc(v_val_217_);
lean_dec_ref(v___x_215_);
if (lean_obj_tag(v_val_217_) == 1)
{
uint8_t v_v_218_; 
v_v_218_ = lean_ctor_get_uint8(v_val_217_, 0);
lean_dec_ref(v_val_217_);
return v_v_218_;
}
else
{
uint8_t v___x_219_; 
lean_dec(v_val_217_);
v___x_219_ = lean_unbox(v_defValue_213_);
return v___x_219_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__1___boxed(lean_object* v_opts_220_, lean_object* v_opt_221_){
_start:
{
uint8_t v_res_222_; lean_object* v_r_223_; 
v_res_222_ = l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__1(v_opts_220_, v_opt_221_);
lean_dec_ref(v_opt_221_);
lean_dec_ref(v_opts_220_);
v_r_223_ = lean_box(v_res_222_);
return v_r_223_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0(lean_box(0));
return v___x_224_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_225_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__1, &l_Lean_Meta_Sym_SymM_run___redArg___closed__1_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__1);
v___x_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___redArg(lean_object* v_x_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v_fst_236_; lean_object* v_snd_237_; lean_object* v_options_238_; lean_object* v___x_239_; uint8_t v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_234_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__0, &l_Lean_Meta_Sym_SymM_run___redArg___closed__0_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__0);
v___x_235_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs(v___x_234_);
v_fst_236_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_fst_236_);
v_snd_237_ = lean_ctor_get(v___x_235_, 1);
lean_inc(v_snd_237_);
lean_dec_ref(v___x_235_);
v_options_238_ = lean_ctor_get(v_a_231_, 2);
v___x_239_ = l_Lean_Meta_Sym_sym_debug;
v___x_240_ = l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__1(v_options_238_, v___x_239_);
v___x_241_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__2, &l_Lean_Meta_Sym_SymM_run___redArg___closed__2_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__2);
v___x_242_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_242_, 0, v_snd_237_);
lean_ctor_set(v___x_242_, 1, v___x_241_);
lean_ctor_set(v___x_242_, 2, v___x_241_);
lean_ctor_set(v___x_242_, 3, v___x_241_);
lean_ctor_set(v___x_242_, 4, v___x_241_);
lean_ctor_set(v___x_242_, 5, v___x_241_);
lean_ctor_set(v___x_242_, 6, v___x_241_);
lean_ctor_set_uint8(v___x_242_, sizeof(void*)*7, v___x_240_);
v___x_243_ = lean_st_mk_ref(v___x_242_);
lean_inc(v_a_232_);
lean_inc_ref(v_a_231_);
lean_inc(v_a_230_);
lean_inc_ref(v_a_229_);
lean_inc(v___x_243_);
v___x_244_ = lean_apply_7(v_x_228_, v_fst_236_, v___x_243_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, lean_box(0));
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_253_; 
v_a_245_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_253_ == 0)
{
v___x_247_ = v___x_244_;
v_isShared_248_ = v_isSharedCheck_253_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_244_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_253_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_249_; lean_object* v___x_251_; 
v___x_249_ = lean_st_ref_get(v___x_243_);
lean_dec(v___x_243_);
lean_dec(v___x_249_);
if (v_isShared_248_ == 0)
{
v___x_251_ = v___x_247_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_a_245_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
else
{
lean_dec(v___x_243_);
return v___x_244_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___redArg___boxed(lean_object* v_x_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_Meta_Sym_SymM_run___redArg(v_x_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec(v_a_256_);
lean_dec_ref(v_a_255_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run(lean_object* v_00_u03b1_261_, lean_object* v_x_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Lean_Meta_Sym_SymM_run___redArg(v_x_262_, v_a_263_, v_a_264_, v_a_265_, v_a_266_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___boxed(lean_object* v_00_u03b1_269_, lean_object* v_x_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_Meta_Sym_SymM_run(v_00_u03b1_269_, v_x_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_);
lean_dec(v_a_274_);
lean_dec_ref(v_a_273_);
lean_dec(v_a_272_);
lean_dec_ref(v_a_271_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___redArg(lean_object* v_a_277_){
_start:
{
lean_object* v___x_279_; 
lean_inc_ref(v_a_277_);
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v_a_277_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___redArg___boxed(lean_object* v_a_280_, lean_object* v_a_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_280_);
lean_dec_ref(v_a_280_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs(lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_){
_start:
{
lean_object* v___x_290_; 
lean_inc_ref(v_a_283_);
v___x_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_290_, 0, v_a_283_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___boxed(lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lean_Meta_Sym_getSharedExprs(v_a_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_);
lean_dec(v_a_296_);
lean_dec_ref(v_a_295_);
lean_dec(v_a_294_);
lean_dec_ref(v_a_293_);
lean_dec(v_a_292_);
lean_dec_ref(v_a_291_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg(lean_object* v_a_299_){
_start:
{
lean_object* v_trueExpr_301_; lean_object* v___x_302_; 
v_trueExpr_301_ = lean_ctor_get(v_a_299_, 0);
lean_inc_ref(v_trueExpr_301_);
v___x_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_302_, 0, v_trueExpr_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg___boxed(lean_object* v_a_303_, lean_object* v_a_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_303_);
lean_dec_ref(v_a_303_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr(lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_306_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___boxed(lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_Meta_Sym_getTrueExpr(v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
lean_dec(v_a_319_);
lean_dec_ref(v_a_318_);
lean_dec(v_a_317_);
lean_dec_ref(v_a_316_);
lean_dec(v_a_315_);
lean_dec_ref(v_a_314_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___redArg(lean_object* v_e_322_, lean_object* v_a_323_){
_start:
{
lean_object* v___x_325_; lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_335_; 
v___x_325_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_323_);
v_a_326_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_335_ == 0)
{
v___x_328_ = v___x_325_;
v_isShared_329_ = v_isSharedCheck_335_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_325_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_335_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
uint8_t v___x_330_; lean_object* v___x_331_; lean_object* v___x_333_; 
v___x_330_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_322_, v_a_326_);
lean_dec(v_a_326_);
v___x_331_ = lean_box(v___x_330_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 0, v___x_331_);
v___x_333_ = v___x_328_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_331_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___redArg___boxed(lean_object* v_e_336_, lean_object* v_a_337_, lean_object* v_a_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_336_, v_a_337_);
lean_dec_ref(v_a_337_);
lean_dec_ref(v_e_336_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr(lean_object* v_e_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_340_, v_a_341_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___boxed(lean_object* v_e_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lean_Meta_Sym_isTrueExpr(v_e_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
lean_dec(v_a_355_);
lean_dec_ref(v_a_354_);
lean_dec(v_a_353_);
lean_dec_ref(v_a_352_);
lean_dec(v_a_351_);
lean_dec_ref(v_a_350_);
lean_dec_ref(v_e_349_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg(lean_object* v_a_358_){
_start:
{
lean_object* v_falseExpr_360_; lean_object* v___x_361_; 
v_falseExpr_360_ = lean_ctor_get(v_a_358_, 1);
lean_inc_ref(v_falseExpr_360_);
v___x_361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_361_, 0, v_falseExpr_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg___boxed(lean_object* v_a_362_, lean_object* v_a_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_362_);
lean_dec_ref(v_a_362_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr(lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_365_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___boxed(lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_Meta_Sym_getFalseExpr(v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_);
lean_dec(v_a_378_);
lean_dec_ref(v_a_377_);
lean_dec(v_a_376_);
lean_dec_ref(v_a_375_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg(lean_object* v_e_381_, lean_object* v_a_382_){
_start:
{
lean_object* v___x_384_; lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_394_; 
v___x_384_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_382_);
v_a_385_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_394_ == 0)
{
v___x_387_ = v___x_384_;
v_isShared_388_ = v_isSharedCheck_394_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_384_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_394_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
uint8_t v___x_389_; lean_object* v___x_390_; lean_object* v___x_392_; 
v___x_389_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_381_, v_a_385_);
lean_dec(v_a_385_);
v___x_390_ = lean_box(v___x_389_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 0, v___x_390_);
v___x_392_ = v___x_387_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v___x_390_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg___boxed(lean_object* v_e_395_, lean_object* v_a_396_, lean_object* v_a_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_395_, v_a_396_);
lean_dec_ref(v_a_396_);
lean_dec_ref(v_e_395_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr(lean_object* v_e_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_399_, v_a_400_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___boxed(lean_object* v_e_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_Meta_Sym_isFalseExpr(v_e_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
lean_dec(v_a_414_);
lean_dec_ref(v_a_413_);
lean_dec(v_a_412_);
lean_dec_ref(v_a_411_);
lean_dec(v_a_410_);
lean_dec_ref(v_a_409_);
lean_dec_ref(v_e_408_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg(lean_object* v_a_417_){
_start:
{
lean_object* v_btrueExpr_419_; lean_object* v___x_420_; 
v_btrueExpr_419_ = lean_ctor_get(v_a_417_, 3);
lean_inc_ref(v_btrueExpr_419_);
v___x_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_420_, 0, v_btrueExpr_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg___boxed(lean_object* v_a_421_, lean_object* v_a_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_421_);
lean_dec_ref(v_a_421_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr(lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_424_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___boxed(lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lean_Meta_Sym_getBoolTrueExpr(v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec(v_a_433_);
lean_dec_ref(v_a_432_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___redArg(lean_object* v_e_440_, lean_object* v_a_441_){
_start:
{
lean_object* v___x_443_; lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_453_; 
v___x_443_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_441_);
v_a_444_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_453_ == 0)
{
v___x_446_ = v___x_443_;
v_isShared_447_ = v_isSharedCheck_453_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_443_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_453_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
uint8_t v___x_448_; lean_object* v___x_449_; lean_object* v___x_451_; 
v___x_448_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_440_, v_a_444_);
lean_dec(v_a_444_);
v___x_449_ = lean_box(v___x_448_);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 0, v___x_449_);
v___x_451_ = v___x_446_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_449_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___redArg___boxed(lean_object* v_e_454_, lean_object* v_a_455_, lean_object* v_a_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_454_, v_a_455_);
lean_dec_ref(v_a_455_);
lean_dec_ref(v_e_454_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr(lean_object* v_e_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_458_, v_a_459_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___boxed(lean_object* v_e_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Lean_Meta_Sym_isBoolTrueExpr(v_e_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_);
lean_dec(v_a_473_);
lean_dec_ref(v_a_472_);
lean_dec(v_a_471_);
lean_dec_ref(v_a_470_);
lean_dec(v_a_469_);
lean_dec_ref(v_a_468_);
lean_dec_ref(v_e_467_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg(lean_object* v_a_476_){
_start:
{
lean_object* v_bfalseExpr_478_; lean_object* v___x_479_; 
v_bfalseExpr_478_ = lean_ctor_get(v_a_476_, 4);
lean_inc_ref(v_bfalseExpr_478_);
v___x_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_479_, 0, v_bfalseExpr_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg___boxed(lean_object* v_a_480_, lean_object* v_a_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_480_);
lean_dec_ref(v_a_480_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr(lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_483_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___boxed(lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lean_Meta_Sym_getBoolFalseExpr(v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_);
lean_dec(v_a_496_);
lean_dec_ref(v_a_495_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___redArg(lean_object* v_e_499_, lean_object* v_a_500_){
_start:
{
lean_object* v___x_502_; lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_512_; 
v___x_502_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_500_);
v_a_503_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_512_ == 0)
{
v___x_505_ = v___x_502_;
v_isShared_506_ = v_isSharedCheck_512_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_502_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_512_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
uint8_t v___x_507_; lean_object* v___x_508_; lean_object* v___x_510_; 
v___x_507_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_499_, v_a_503_);
lean_dec(v_a_503_);
v___x_508_ = lean_box(v___x_507_);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v___x_508_);
v___x_510_ = v___x_505_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_508_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___redArg___boxed(lean_object* v_e_513_, lean_object* v_a_514_, lean_object* v_a_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_513_, v_a_514_);
lean_dec_ref(v_a_514_);
lean_dec_ref(v_e_513_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr(lean_object* v_e_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_517_, v_a_518_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___boxed(lean_object* v_e_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lean_Meta_Sym_isBoolFalseExpr(v_e_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
lean_dec(v_a_530_);
lean_dec_ref(v_a_529_);
lean_dec(v_a_528_);
lean_dec_ref(v_a_527_);
lean_dec_ref(v_e_526_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___redArg(lean_object* v_a_535_){
_start:
{
lean_object* v_natZExpr_537_; lean_object* v___x_538_; 
v_natZExpr_537_ = lean_ctor_get(v_a_535_, 2);
lean_inc_ref(v_natZExpr_537_);
v___x_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_538_, 0, v_natZExpr_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___redArg___boxed(lean_object* v_a_539_, lean_object* v_a_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Lean_Meta_Sym_getNatZeroExpr___redArg(v_a_539_);
lean_dec_ref(v_a_539_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr(lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l_Lean_Meta_Sym_getNatZeroExpr___redArg(v_a_542_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___boxed(lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Lean_Meta_Sym_getNatZeroExpr(v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_);
lean_dec(v_a_555_);
lean_dec_ref(v_a_554_);
lean_dec(v_a_553_);
lean_dec_ref(v_a_552_);
lean_dec(v_a_551_);
lean_dec_ref(v_a_550_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___redArg(lean_object* v_a_558_){
_start:
{
lean_object* v_ordEqExpr_560_; lean_object* v___x_561_; 
v_ordEqExpr_560_ = lean_ctor_get(v_a_558_, 5);
lean_inc_ref(v_ordEqExpr_560_);
v___x_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_561_, 0, v_ordEqExpr_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___redArg___boxed(lean_object* v_a_562_, lean_object* v_a_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_Meta_Sym_getOrderingEqExpr___redArg(v_a_562_);
lean_dec_ref(v_a_562_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr(lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l_Lean_Meta_Sym_getOrderingEqExpr___redArg(v_a_565_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___boxed(lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lean_Meta_Sym_getOrderingEqExpr(v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_);
lean_dec(v_a_578_);
lean_dec_ref(v_a_577_);
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___redArg(lean_object* v_a_581_){
_start:
{
lean_object* v_intExpr_583_; lean_object* v___x_584_; 
v_intExpr_583_ = lean_ctor_get(v_a_581_, 6);
lean_inc_ref(v_intExpr_583_);
v___x_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_584_, 0, v_intExpr_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___redArg___boxed(lean_object* v_a_585_, lean_object* v_a_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lean_Meta_Sym_getIntExpr___redArg(v_a_585_);
lean_dec_ref(v_a_585_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr(lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Lean_Meta_Sym_getIntExpr___redArg(v_a_588_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___boxed(lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Lean_Meta_Sym_getIntExpr(v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_);
lean_dec(v_a_601_);
lean_dec_ref(v_a_600_);
lean_dec(v_a_599_);
lean_dec_ref(v_a_598_);
lean_dec(v_a_597_);
lean_dec_ref(v_a_596_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_604_, lean_object* v_vals_605_, lean_object* v_i_606_, lean_object* v_k_607_){
_start:
{
lean_object* v___x_608_; uint8_t v___x_609_; 
v___x_608_ = lean_array_get_size(v_keys_604_);
v___x_609_ = lean_nat_dec_lt(v_i_606_, v___x_608_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; 
lean_dec_ref(v_k_607_);
lean_dec(v_i_606_);
v___x_610_ = lean_box(0);
return v___x_610_;
}
else
{
lean_object* v_k_x27_611_; uint8_t v___x_612_; 
v_k_x27_611_ = lean_array_fget_borrowed(v_keys_604_, v_i_606_);
lean_inc(v_k_x27_611_);
lean_inc_ref(v_k_607_);
v___x_612_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_607_, v_k_x27_611_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = lean_unsigned_to_nat(1u);
v___x_614_ = lean_nat_add(v_i_606_, v___x_613_);
lean_dec(v_i_606_);
v_i_606_ = v___x_614_;
goto _start;
}
else
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
lean_dec_ref(v_k_607_);
v___x_616_ = lean_array_fget_borrowed(v_vals_605_, v_i_606_);
lean_dec(v_i_606_);
lean_inc(v___x_616_);
lean_inc(v_k_x27_611_);
v___x_617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_617_, 0, v_k_x27_611_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
v___x_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_618_, 0, v___x_617_);
return v___x_618_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_619_, lean_object* v_vals_620_, lean_object* v_i_621_, lean_object* v_k_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1___redArg(v_keys_619_, v_vals_620_, v_i_621_, v_k_622_);
lean_dec_ref(v_vals_620_);
lean_dec_ref(v_keys_619_);
return v_res_623_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_624_; size_t v___x_625_; size_t v___x_626_; 
v___x_624_ = ((size_t)5ULL);
v___x_625_ = ((size_t)1ULL);
v___x_626_ = lean_usize_shift_left(v___x_625_, v___x_624_);
return v___x_626_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_627_; size_t v___x_628_; size_t v___x_629_; 
v___x_627_ = ((size_t)1ULL);
v___x_628_ = lean_usize_once(&l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__0);
v___x_629_ = lean_usize_sub(v___x_628_, v___x_627_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg(lean_object* v_x_630_, size_t v_x_631_, lean_object* v_x_632_){
_start:
{
if (lean_obj_tag(v_x_630_) == 0)
{
lean_object* v_es_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_661_; 
v_es_633_ = lean_ctor_get(v_x_630_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v_x_630_);
if (v_isSharedCheck_661_ == 0)
{
v___x_635_ = v_x_630_;
v_isShared_636_ = v_isSharedCheck_661_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_es_633_);
lean_dec(v_x_630_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_661_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_637_; size_t v___x_638_; size_t v___x_639_; size_t v___x_640_; lean_object* v_j_641_; lean_object* v___x_642_; 
v___x_637_ = lean_box(2);
v___x_638_ = ((size_t)5ULL);
v___x_639_ = lean_usize_once(&l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1);
v___x_640_ = lean_usize_land(v_x_631_, v___x_639_);
v_j_641_ = lean_usize_to_nat(v___x_640_);
v___x_642_ = lean_array_get(v___x_637_, v_es_633_, v_j_641_);
lean_dec(v_j_641_);
lean_dec_ref(v_es_633_);
switch(lean_obj_tag(v___x_642_))
{
case 0:
{
lean_object* v_key_643_; lean_object* v_val_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_656_; 
v_key_643_ = lean_ctor_get(v___x_642_, 0);
v_val_644_ = lean_ctor_get(v___x_642_, 1);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_656_ == 0)
{
v___x_646_ = v___x_642_;
v_isShared_647_ = v_isSharedCheck_656_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_val_644_);
lean_inc(v_key_643_);
lean_dec(v___x_642_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_656_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
uint8_t v___x_648_; 
lean_inc(v_key_643_);
v___x_648_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_632_, v_key_643_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; 
lean_del_object(v___x_646_);
lean_dec(v_val_644_);
lean_dec(v_key_643_);
lean_del_object(v___x_635_);
v___x_649_ = lean_box(0);
return v___x_649_;
}
else
{
lean_object* v___x_651_; 
if (v_isShared_647_ == 0)
{
v___x_651_ = v___x_646_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_key_643_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v_val_644_);
v___x_651_ = v_reuseFailAlloc_655_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
lean_object* v___x_653_; 
if (v_isShared_636_ == 0)
{
lean_ctor_set_tag(v___x_635_, 1);
lean_ctor_set(v___x_635_, 0, v___x_651_);
v___x_653_ = v___x_635_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_651_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
}
case 1:
{
lean_object* v_node_657_; size_t v___x_658_; 
lean_del_object(v___x_635_);
v_node_657_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_node_657_);
lean_dec_ref(v___x_642_);
v___x_658_ = lean_usize_shift_right(v_x_631_, v___x_638_);
v_x_630_ = v_node_657_;
v_x_631_ = v___x_658_;
goto _start;
}
default: 
{
lean_object* v___x_660_; 
lean_del_object(v___x_635_);
lean_dec_ref(v_x_632_);
v___x_660_ = lean_box(0);
return v___x_660_;
}
}
}
}
else
{
lean_object* v_ks_662_; lean_object* v_vs_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v_ks_662_ = lean_ctor_get(v_x_630_, 0);
lean_inc_ref(v_ks_662_);
v_vs_663_ = lean_ctor_get(v_x_630_, 1);
lean_inc_ref(v_vs_663_);
lean_dec_ref(v_x_630_);
v___x_664_ = lean_unsigned_to_nat(0u);
v___x_665_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1___redArg(v_ks_662_, v_vs_663_, v___x_664_, v_x_632_);
lean_dec_ref(v_vs_663_);
lean_dec_ref(v_ks_662_);
return v___x_665_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___boxed(lean_object* v_x_666_, lean_object* v_x_667_, lean_object* v_x_668_){
_start:
{
size_t v_x_2045__boxed_669_; lean_object* v_res_670_; 
v_x_2045__boxed_669_ = lean_unbox_usize(v_x_667_);
lean_dec(v_x_667_);
v_res_670_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg(v_x_666_, v_x_2045__boxed_669_, v_x_668_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0___redArg(lean_object* v_x_671_, lean_object* v_x_672_){
_start:
{
uint64_t v___x_673_; size_t v___x_674_; lean_object* v___x_675_; 
v___x_673_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_672_);
v___x_674_ = lean_uint64_to_usize(v___x_673_);
v___x_675_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg(v_x_671_, v___x_674_, v_x_672_);
return v___x_675_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_shareCommon___redArg___closed__0(void){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_676_ = lean_box(0);
v___x_677_ = lean_unsigned_to_nat(16u);
v___x_678_ = lean_mk_array(v___x_677_, v___x_676_);
return v___x_678_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_shareCommon___redArg___closed__1(void){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_679_ = lean_obj_once(&l_Lean_Meta_Sym_shareCommon___redArg___closed__0, &l_Lean_Meta_Sym_shareCommon___redArg___closed__0_once, _init_l_Lean_Meta_Sym_shareCommon___redArg___closed__0);
v___x_680_ = lean_unsigned_to_nat(0u);
v___x_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
lean_ctor_set(v___x_681_, 1, v___x_679_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object* v_e_682_, lean_object* v_a_683_){
_start:
{
lean_object* v___x_685_; lean_object* v_share_686_; lean_object* v_maxFVar_687_; lean_object* v_proofInstInfo_688_; lean_object* v_inferType_689_; lean_object* v_getLevel_690_; lean_object* v_congrInfo_691_; lean_object* v_defEqI_692_; uint8_t v_debug_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_732_; 
v___x_685_ = lean_st_ref_take(v_a_683_);
v_share_686_ = lean_ctor_get(v___x_685_, 0);
v_maxFVar_687_ = lean_ctor_get(v___x_685_, 1);
v_proofInstInfo_688_ = lean_ctor_get(v___x_685_, 2);
v_inferType_689_ = lean_ctor_get(v___x_685_, 3);
v_getLevel_690_ = lean_ctor_get(v___x_685_, 4);
v_congrInfo_691_ = lean_ctor_get(v___x_685_, 5);
v_defEqI_692_ = lean_ctor_get(v___x_685_, 6);
v_debug_693_ = lean_ctor_get_uint8(v___x_685_, sizeof(void*)*7);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_732_ == 0)
{
v___x_695_ = v___x_685_;
v_isShared_696_ = v_isSharedCheck_732_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_defEqI_692_);
lean_inc(v_congrInfo_691_);
lean_inc(v_getLevel_690_);
lean_inc(v_inferType_689_);
lean_inc(v_proofInstInfo_688_);
lean_inc(v_maxFVar_687_);
lean_inc(v_share_686_);
lean_dec(v___x_685_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_732_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_697_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__0, &l_Lean_Meta_Sym_SymM_run___redArg___closed__0_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__0);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v___x_697_);
v___x_699_ = v___x_695_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_697_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v_maxFVar_687_);
lean_ctor_set(v_reuseFailAlloc_731_, 2, v_proofInstInfo_688_);
lean_ctor_set(v_reuseFailAlloc_731_, 3, v_inferType_689_);
lean_ctor_set(v_reuseFailAlloc_731_, 4, v_getLevel_690_);
lean_ctor_set(v_reuseFailAlloc_731_, 5, v_congrInfo_691_);
lean_ctor_set(v_reuseFailAlloc_731_, 6, v_defEqI_692_);
lean_ctor_set_uint8(v_reuseFailAlloc_731_, sizeof(void*)*7, v_debug_693_);
v___x_699_ = v_reuseFailAlloc_731_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v___x_700_; lean_object* v_fst_702_; lean_object* v_snd_703_; lean_object* v___x_722_; 
v___x_700_ = lean_st_ref_set(v_a_683_, v___x_699_);
lean_inc_ref(v_e_682_);
lean_inc_ref(v_share_686_);
v___x_722_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0___redArg(v_share_686_, v_e_682_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v_snd_726_; lean_object* v_fst_727_; lean_object* v_set_728_; 
v___x_723_ = lean_obj_once(&l_Lean_Meta_Sym_shareCommon___redArg___closed__1, &l_Lean_Meta_Sym_shareCommon___redArg___closed__1_once, _init_l_Lean_Meta_Sym_shareCommon___redArg___closed__1);
v___x_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
lean_ctor_set(v___x_724_, 1, v_share_686_);
v___x_725_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_682_, v___x_724_);
v_snd_726_ = lean_ctor_get(v___x_725_, 1);
lean_inc(v_snd_726_);
v_fst_727_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_fst_727_);
lean_dec_ref(v___x_725_);
v_set_728_ = lean_ctor_get(v_snd_726_, 1);
lean_inc_ref(v_set_728_);
lean_dec(v_snd_726_);
v_fst_702_ = v_fst_727_;
v_snd_703_ = v_set_728_;
goto v___jp_701_;
}
else
{
lean_object* v_val_729_; lean_object* v_fst_730_; 
lean_dec_ref(v_e_682_);
v_val_729_ = lean_ctor_get(v___x_722_, 0);
lean_inc(v_val_729_);
lean_dec_ref(v___x_722_);
v_fst_730_ = lean_ctor_get(v_val_729_, 0);
lean_inc(v_fst_730_);
lean_dec(v_val_729_);
v_fst_702_ = v_fst_730_;
v_snd_703_ = v_share_686_;
goto v___jp_701_;
}
v___jp_701_:
{
lean_object* v___x_704_; lean_object* v_maxFVar_705_; lean_object* v_proofInstInfo_706_; lean_object* v_inferType_707_; lean_object* v_getLevel_708_; lean_object* v_congrInfo_709_; lean_object* v_defEqI_710_; uint8_t v_debug_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_720_; 
v___x_704_ = lean_st_ref_take(v_a_683_);
v_maxFVar_705_ = lean_ctor_get(v___x_704_, 1);
v_proofInstInfo_706_ = lean_ctor_get(v___x_704_, 2);
v_inferType_707_ = lean_ctor_get(v___x_704_, 3);
v_getLevel_708_ = lean_ctor_get(v___x_704_, 4);
v_congrInfo_709_ = lean_ctor_get(v___x_704_, 5);
v_defEqI_710_ = lean_ctor_get(v___x_704_, 6);
v_debug_711_ = lean_ctor_get_uint8(v___x_704_, sizeof(void*)*7);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_720_ == 0)
{
lean_object* v_unused_721_; 
v_unused_721_ = lean_ctor_get(v___x_704_, 0);
lean_dec(v_unused_721_);
v___x_713_ = v___x_704_;
v_isShared_714_ = v_isSharedCheck_720_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_defEqI_710_);
lean_inc(v_congrInfo_709_);
lean_inc(v_getLevel_708_);
lean_inc(v_inferType_707_);
lean_inc(v_proofInstInfo_706_);
lean_inc(v_maxFVar_705_);
lean_dec(v___x_704_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_720_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 0, v_snd_703_);
v___x_716_ = v___x_713_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_snd_703_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v_maxFVar_705_);
lean_ctor_set(v_reuseFailAlloc_719_, 2, v_proofInstInfo_706_);
lean_ctor_set(v_reuseFailAlloc_719_, 3, v_inferType_707_);
lean_ctor_set(v_reuseFailAlloc_719_, 4, v_getLevel_708_);
lean_ctor_set(v_reuseFailAlloc_719_, 5, v_congrInfo_709_);
lean_ctor_set(v_reuseFailAlloc_719_, 6, v_defEqI_710_);
lean_ctor_set_uint8(v_reuseFailAlloc_719_, sizeof(void*)*7, v_debug_711_);
v___x_716_ = v_reuseFailAlloc_719_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_717_ = lean_st_ref_set(v_a_683_, v___x_716_);
v___x_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_718_, 0, v_fst_702_);
return v___x_718_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___redArg___boxed(lean_object* v_e_733_, lean_object* v_a_734_, lean_object* v_a_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Lean_Meta_Sym_shareCommon___redArg(v_e_733_, v_a_734_);
lean_dec(v_a_734_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon(lean_object* v_e_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = l_Lean_Meta_Sym_shareCommon___redArg(v_e_737_, v_a_739_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___boxed(lean_object* v_e_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Lean_Meta_Sym_shareCommon(v_e_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_);
lean_dec(v_a_752_);
lean_dec_ref(v_a_751_);
lean_dec(v_a_750_);
lean_dec_ref(v_a_749_);
lean_dec(v_a_748_);
lean_dec_ref(v_a_747_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0(lean_object* v_00_u03b2_755_, lean_object* v_x_756_, lean_object* v_x_757_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0___redArg(v_x_756_, v_x_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0(lean_object* v_00_u03b2_759_, lean_object* v_x_760_, size_t v_x_761_, lean_object* v_x_762_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg(v_x_760_, v_x_761_, v_x_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___boxed(lean_object* v_00_u03b2_764_, lean_object* v_x_765_, lean_object* v_x_766_, lean_object* v_x_767_){
_start:
{
size_t v_x_2235__boxed_768_; lean_object* v_res_769_; 
v_x_2235__boxed_768_ = lean_unbox_usize(v_x_766_);
lean_dec(v_x_766_);
v_res_769_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0(v_00_u03b2_764_, v_x_765_, v_x_2235__boxed_768_, v_x_767_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_770_, lean_object* v_keys_771_, lean_object* v_vals_772_, lean_object* v_heq_773_, lean_object* v_i_774_, lean_object* v_k_775_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1___redArg(v_keys_771_, v_vals_772_, v_i_774_, v_k_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_777_, lean_object* v_keys_778_, lean_object* v_vals_779_, lean_object* v_heq_780_, lean_object* v_i_781_, lean_object* v_k_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1(v_00_u03b2_777_, v_keys_778_, v_vals_779_, v_heq_780_, v_i_781_, v_k_782_);
lean_dec_ref(v_vals_779_);
lean_dec_ref(v_keys_778_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___redArg(lean_object* v_e_784_, lean_object* v_a_785_){
_start:
{
lean_object* v___x_787_; lean_object* v_share_788_; lean_object* v_maxFVar_789_; lean_object* v_proofInstInfo_790_; lean_object* v_inferType_791_; lean_object* v_getLevel_792_; lean_object* v_congrInfo_793_; lean_object* v_defEqI_794_; uint8_t v_debug_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_825_; 
v___x_787_ = lean_st_ref_take(v_a_785_);
v_share_788_ = lean_ctor_get(v___x_787_, 0);
v_maxFVar_789_ = lean_ctor_get(v___x_787_, 1);
v_proofInstInfo_790_ = lean_ctor_get(v___x_787_, 2);
v_inferType_791_ = lean_ctor_get(v___x_787_, 3);
v_getLevel_792_ = lean_ctor_get(v___x_787_, 4);
v_congrInfo_793_ = lean_ctor_get(v___x_787_, 5);
v_defEqI_794_ = lean_ctor_get(v___x_787_, 6);
v_debug_795_ = lean_ctor_get_uint8(v___x_787_, sizeof(void*)*7);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_825_ == 0)
{
v___x_797_ = v___x_787_;
v_isShared_798_ = v_isSharedCheck_825_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_defEqI_794_);
lean_inc(v_congrInfo_793_);
lean_inc(v_getLevel_792_);
lean_inc(v_inferType_791_);
lean_inc(v_proofInstInfo_790_);
lean_inc(v_maxFVar_789_);
lean_inc(v_share_788_);
lean_dec(v___x_787_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_825_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_799_; lean_object* v___x_801_; 
v___x_799_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__0, &l_Lean_Meta_Sym_SymM_run___redArg___closed__0_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__0);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 0, v___x_799_);
v___x_801_ = v___x_797_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_799_);
lean_ctor_set(v_reuseFailAlloc_824_, 1, v_maxFVar_789_);
lean_ctor_set(v_reuseFailAlloc_824_, 2, v_proofInstInfo_790_);
lean_ctor_set(v_reuseFailAlloc_824_, 3, v_inferType_791_);
lean_ctor_set(v_reuseFailAlloc_824_, 4, v_getLevel_792_);
lean_ctor_set(v_reuseFailAlloc_824_, 5, v_congrInfo_793_);
lean_ctor_set(v_reuseFailAlloc_824_, 6, v_defEqI_794_);
lean_ctor_set_uint8(v_reuseFailAlloc_824_, sizeof(void*)*7, v_debug_795_);
v___x_801_ = v_reuseFailAlloc_824_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v_fst_804_; lean_object* v_snd_805_; lean_object* v___x_806_; lean_object* v_maxFVar_807_; lean_object* v_proofInstInfo_808_; lean_object* v_inferType_809_; lean_object* v_getLevel_810_; lean_object* v_congrInfo_811_; lean_object* v_defEqI_812_; uint8_t v_debug_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_822_; 
v___x_802_ = lean_st_ref_set(v_a_785_, v___x_801_);
v___x_803_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_e_784_, v_share_788_);
v_fst_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_fst_804_);
v_snd_805_ = lean_ctor_get(v___x_803_, 1);
lean_inc(v_snd_805_);
lean_dec_ref(v___x_803_);
v___x_806_ = lean_st_ref_take(v_a_785_);
v_maxFVar_807_ = lean_ctor_get(v___x_806_, 1);
v_proofInstInfo_808_ = lean_ctor_get(v___x_806_, 2);
v_inferType_809_ = lean_ctor_get(v___x_806_, 3);
v_getLevel_810_ = lean_ctor_get(v___x_806_, 4);
v_congrInfo_811_ = lean_ctor_get(v___x_806_, 5);
v_defEqI_812_ = lean_ctor_get(v___x_806_, 6);
v_debug_813_ = lean_ctor_get_uint8(v___x_806_, sizeof(void*)*7);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_822_ == 0)
{
lean_object* v_unused_823_; 
v_unused_823_ = lean_ctor_get(v___x_806_, 0);
lean_dec(v_unused_823_);
v___x_815_ = v___x_806_;
v_isShared_816_ = v_isSharedCheck_822_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_defEqI_812_);
lean_inc(v_congrInfo_811_);
lean_inc(v_getLevel_810_);
lean_inc(v_inferType_809_);
lean_inc(v_proofInstInfo_808_);
lean_inc(v_maxFVar_807_);
lean_dec(v___x_806_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_822_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v_snd_805_);
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_snd_805_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_maxFVar_807_);
lean_ctor_set(v_reuseFailAlloc_821_, 2, v_proofInstInfo_808_);
lean_ctor_set(v_reuseFailAlloc_821_, 3, v_inferType_809_);
lean_ctor_set(v_reuseFailAlloc_821_, 4, v_getLevel_810_);
lean_ctor_set(v_reuseFailAlloc_821_, 5, v_congrInfo_811_);
lean_ctor_set(v_reuseFailAlloc_821_, 6, v_defEqI_812_);
lean_ctor_set_uint8(v_reuseFailAlloc_821_, sizeof(void*)*7, v_debug_813_);
v___x_818_ = v_reuseFailAlloc_821_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_819_ = lean_st_ref_set(v_a_785_, v___x_818_);
v___x_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_820_, 0, v_fst_804_);
return v___x_820_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___redArg___boxed(lean_object* v_e_826_, lean_object* v_a_827_, lean_object* v_a_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_e_826_, v_a_827_);
lean_dec(v_a_827_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object* v_e_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_e_830_, v_a_832_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___boxed(lean_object* v_e_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Lean_Meta_Sym_shareCommonInc(v_e_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_);
lean_dec(v_a_845_);
lean_dec_ref(v_a_844_);
lean_dec(v_a_843_);
lean_dec_ref(v_a_842_);
lean_dec(v_a_841_);
lean_dec_ref(v_a_840_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_share___redArg(lean_object* v_e_848_, lean_object* v_a_849_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_e_848_, v_a_849_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_share___redArg___boxed(lean_object* v_e_852_, lean_object* v_a_853_, lean_object* v_a_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Lean_Meta_Sym_share___redArg(v_e_852_, v_a_853_);
lean_dec(v_a_853_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_share(lean_object* v_e_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_e_856_, v_a_858_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_share___boxed(lean_object* v_e_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Lean_Meta_Sym_share(v_e_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_);
lean_dec(v_a_871_);
lean_dec_ref(v_a_870_);
lean_dec(v_a_869_);
lean_dec_ref(v_a_868_);
lean_dec(v_a_867_);
lean_dec_ref(v_a_866_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___redArg(lean_object* v_a_874_){
_start:
{
lean_object* v___x_876_; uint8_t v_debug_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_876_ = lean_st_ref_get(v_a_874_);
v_debug_877_ = lean_ctor_get_uint8(v___x_876_, sizeof(void*)*7);
lean_dec(v___x_876_);
v___x_878_ = lean_box(v_debug_877_);
v___x_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___redArg___boxed(lean_object* v_a_880_, lean_object* v_a_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Lean_Meta_Sym_isDebugEnabled___redArg(v_a_880_);
lean_dec(v_a_880_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled(lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_){
_start:
{
lean_object* v___x_890_; uint8_t v_debug_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_890_ = lean_st_ref_get(v_a_884_);
v_debug_891_ = lean_ctor_get_uint8(v___x_890_, sizeof(void*)*7);
lean_dec(v___x_890_);
v___x_892_ = lean_box(v_debug_891_);
v___x_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___boxed(lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lean_Meta_Sym_isDebugEnabled(v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_);
lean_dec(v_a_899_);
lean_dec_ref(v_a_898_);
lean_dec(v_a_897_);
lean_dec_ref(v_a_896_);
lean_dec(v_a_895_);
lean_dec_ref(v_a_894_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_902_, lean_object* v_vals_903_, lean_object* v_i_904_, lean_object* v_k_905_){
_start:
{
uint8_t v___y_907_; lean_object* v___x_913_; uint8_t v___x_914_; 
v___x_913_ = lean_array_get_size(v_keys_902_);
v___x_914_ = lean_nat_dec_lt(v_i_904_, v___x_913_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; 
lean_dec(v_i_904_);
v___x_915_ = lean_box(0);
return v___x_915_;
}
else
{
lean_object* v_fst_916_; lean_object* v_snd_917_; lean_object* v_k_x27_918_; lean_object* v_fst_919_; lean_object* v_snd_920_; uint8_t v___x_921_; 
v_fst_916_ = lean_ctor_get(v_k_905_, 0);
v_snd_917_ = lean_ctor_get(v_k_905_, 1);
v_k_x27_918_ = lean_array_fget_borrowed(v_keys_902_, v_i_904_);
v_fst_919_ = lean_ctor_get(v_k_x27_918_, 0);
v_snd_920_ = lean_ctor_get(v_k_x27_918_, 1);
v___x_921_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_916_, v_fst_919_);
if (v___x_921_ == 0)
{
v___y_907_ = v___x_921_;
goto v___jp_906_;
}
else
{
uint8_t v___x_922_; 
v___x_922_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_snd_917_, v_snd_920_);
v___y_907_ = v___x_922_;
goto v___jp_906_;
}
}
v___jp_906_:
{
if (v___y_907_ == 0)
{
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = lean_unsigned_to_nat(1u);
v___x_909_ = lean_nat_add(v_i_904_, v___x_908_);
lean_dec(v_i_904_);
v_i_904_ = v___x_909_;
goto _start;
}
else
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = lean_array_fget_borrowed(v_vals_903_, v_i_904_);
lean_dec(v_i_904_);
lean_inc(v___x_911_);
v___x_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
return v___x_912_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_923_, lean_object* v_vals_924_, lean_object* v_i_925_, lean_object* v_k_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_keys_923_, v_vals_924_, v_i_925_, v_k_926_);
lean_dec_ref(v_k_926_);
lean_dec_ref(v_vals_924_);
lean_dec_ref(v_keys_923_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(lean_object* v_x_928_, size_t v_x_929_, lean_object* v_x_930_){
_start:
{
if (lean_obj_tag(v_x_928_) == 0)
{
lean_object* v_es_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_959_; 
v_es_931_ = lean_ctor_get(v_x_928_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v_x_928_);
if (v_isSharedCheck_959_ == 0)
{
v___x_933_ = v_x_928_;
v_isShared_934_ = v_isSharedCheck_959_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_es_931_);
lean_dec(v_x_928_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_959_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_935_; size_t v___x_936_; size_t v___x_937_; size_t v___x_938_; lean_object* v_j_939_; lean_object* v___x_940_; 
v___x_935_ = lean_box(2);
v___x_936_ = ((size_t)5ULL);
v___x_937_ = lean_usize_once(&l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1);
v___x_938_ = lean_usize_land(v_x_929_, v___x_937_);
v_j_939_ = lean_usize_to_nat(v___x_938_);
v___x_940_ = lean_array_get(v___x_935_, v_es_931_, v_j_939_);
lean_dec(v_j_939_);
lean_dec_ref(v_es_931_);
switch(lean_obj_tag(v___x_940_))
{
case 0:
{
lean_object* v_key_941_; lean_object* v_val_942_; uint8_t v___y_944_; lean_object* v_fst_949_; lean_object* v_snd_950_; lean_object* v_fst_951_; lean_object* v_snd_952_; uint8_t v___x_953_; 
v_key_941_ = lean_ctor_get(v___x_940_, 0);
lean_inc(v_key_941_);
v_val_942_ = lean_ctor_get(v___x_940_, 1);
lean_inc(v_val_942_);
lean_dec_ref(v___x_940_);
v_fst_949_ = lean_ctor_get(v_x_930_, 0);
v_snd_950_ = lean_ctor_get(v_x_930_, 1);
v_fst_951_ = lean_ctor_get(v_key_941_, 0);
lean_inc(v_fst_951_);
v_snd_952_ = lean_ctor_get(v_key_941_, 1);
lean_inc(v_snd_952_);
lean_dec(v_key_941_);
v___x_953_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_949_, v_fst_951_);
lean_dec(v_fst_951_);
if (v___x_953_ == 0)
{
lean_dec(v_snd_952_);
v___y_944_ = v___x_953_;
goto v___jp_943_;
}
else
{
uint8_t v___x_954_; 
v___x_954_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_snd_950_, v_snd_952_);
lean_dec(v_snd_952_);
v___y_944_ = v___x_954_;
goto v___jp_943_;
}
v___jp_943_:
{
if (v___y_944_ == 0)
{
lean_object* v___x_945_; 
lean_dec(v_val_942_);
lean_del_object(v___x_933_);
v___x_945_ = lean_box(0);
return v___x_945_;
}
else
{
lean_object* v___x_947_; 
if (v_isShared_934_ == 0)
{
lean_ctor_set_tag(v___x_933_, 1);
lean_ctor_set(v___x_933_, 0, v_val_942_);
v___x_947_ = v___x_933_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_val_942_);
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
case 1:
{
lean_object* v_node_955_; size_t v___x_956_; 
lean_del_object(v___x_933_);
v_node_955_ = lean_ctor_get(v___x_940_, 0);
lean_inc(v_node_955_);
lean_dec_ref(v___x_940_);
v___x_956_ = lean_usize_shift_right(v_x_929_, v___x_936_);
v_x_928_ = v_node_955_;
v_x_929_ = v___x_956_;
goto _start;
}
default: 
{
lean_object* v___x_958_; 
lean_del_object(v___x_933_);
v___x_958_ = lean_box(0);
return v___x_958_;
}
}
}
}
else
{
lean_object* v_ks_960_; lean_object* v_vs_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v_ks_960_ = lean_ctor_get(v_x_928_, 0);
lean_inc_ref(v_ks_960_);
v_vs_961_ = lean_ctor_get(v_x_928_, 1);
lean_inc_ref(v_vs_961_);
lean_dec_ref(v_x_928_);
v___x_962_ = lean_unsigned_to_nat(0u);
v___x_963_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_ks_960_, v_vs_961_, v___x_962_, v_x_930_);
lean_dec_ref(v_vs_961_);
lean_dec_ref(v_ks_960_);
return v___x_963_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg___boxed(lean_object* v_x_964_, lean_object* v_x_965_, lean_object* v_x_966_){
_start:
{
size_t v_x_2706__boxed_967_; lean_object* v_res_968_; 
v_x_2706__boxed_967_ = lean_unbox_usize(v_x_965_);
lean_dec(v_x_965_);
v_res_968_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_964_, v_x_2706__boxed_967_, v_x_966_);
lean_dec_ref(v_x_966_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(lean_object* v_x_969_, lean_object* v_x_970_){
_start:
{
lean_object* v_fst_971_; lean_object* v_snd_972_; uint64_t v___x_973_; uint64_t v___x_974_; uint64_t v___x_975_; size_t v___x_976_; lean_object* v___x_977_; 
v_fst_971_ = lean_ctor_get(v_x_970_, 0);
v_snd_972_ = lean_ctor_get(v_x_970_, 1);
v___x_973_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_971_);
v___x_974_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_snd_972_);
v___x_975_ = lean_uint64_mix_hash(v___x_973_, v___x_974_);
v___x_976_ = lean_uint64_to_usize(v___x_975_);
v___x_977_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_969_, v___x_976_, v_x_970_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg___boxed(lean_object* v_x_978_, lean_object* v_x_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(v_x_978_, v_x_979_);
lean_dec_ref(v_x_979_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_981_, lean_object* v_x_982_, lean_object* v_x_983_, lean_object* v_x_984_){
_start:
{
lean_object* v_ks_985_; lean_object* v_vs_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_1015_; 
v_ks_985_ = lean_ctor_get(v_x_981_, 0);
v_vs_986_ = lean_ctor_get(v_x_981_, 1);
v_isSharedCheck_1015_ = !lean_is_exclusive(v_x_981_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_988_ = v_x_981_;
v_isShared_989_ = v_isSharedCheck_1015_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_vs_986_);
lean_inc(v_ks_985_);
lean_dec(v_x_981_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_1015_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
uint8_t v___y_991_; lean_object* v___x_1003_; uint8_t v___x_1004_; 
v___x_1003_ = lean_array_get_size(v_ks_985_);
v___x_1004_ = lean_nat_dec_lt(v_x_982_, v___x_1003_);
if (v___x_1004_ == 0)
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
lean_del_object(v___x_988_);
lean_dec(v_x_982_);
v___x_1005_ = lean_array_push(v_ks_985_, v_x_983_);
v___x_1006_ = lean_array_push(v_vs_986_, v_x_984_);
v___x_1007_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1005_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
return v___x_1007_;
}
else
{
lean_object* v_fst_1008_; lean_object* v_snd_1009_; lean_object* v_k_x27_1010_; lean_object* v_fst_1011_; lean_object* v_snd_1012_; uint8_t v___x_1013_; 
v_fst_1008_ = lean_ctor_get(v_x_983_, 0);
v_snd_1009_ = lean_ctor_get(v_x_983_, 1);
v_k_x27_1010_ = lean_array_fget_borrowed(v_ks_985_, v_x_982_);
v_fst_1011_ = lean_ctor_get(v_k_x27_1010_, 0);
v_snd_1012_ = lean_ctor_get(v_k_x27_1010_, 1);
v___x_1013_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_1008_, v_fst_1011_);
if (v___x_1013_ == 0)
{
v___y_991_ = v___x_1013_;
goto v___jp_990_;
}
else
{
uint8_t v___x_1014_; 
v___x_1014_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_snd_1009_, v_snd_1012_);
v___y_991_ = v___x_1014_;
goto v___jp_990_;
}
}
v___jp_990_:
{
if (v___y_991_ == 0)
{
lean_object* v___x_993_; 
if (v_isShared_989_ == 0)
{
v___x_993_ = v___x_988_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_ks_985_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_vs_986_);
v___x_993_ = v_reuseFailAlloc_997_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = lean_unsigned_to_nat(1u);
v___x_995_ = lean_nat_add(v_x_982_, v___x_994_);
lean_dec(v_x_982_);
v_x_981_ = v___x_993_;
v_x_982_ = v___x_995_;
goto _start;
}
}
else
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1001_; 
v___x_998_ = lean_array_fset(v_ks_985_, v_x_982_, v_x_983_);
v___x_999_ = lean_array_fset(v_vs_986_, v_x_982_, v_x_984_);
lean_dec(v_x_982_);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 1, v___x_999_);
lean_ctor_set(v___x_988_, 0, v___x_998_);
v___x_1001_ = v___x_988_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_998_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v___x_999_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(lean_object* v_n_1016_, lean_object* v_k_1017_, lean_object* v_v_1018_){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = lean_unsigned_to_nat(0u);
v___x_1020_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(v_n_1016_, v___x_1019_, v_k_1017_, v_v_1018_);
return v___x_1020_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1021_; 
v___x_1021_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(lean_object* v_x_1022_, size_t v_x_1023_, size_t v_x_1024_, lean_object* v_x_1025_, lean_object* v_x_1026_){
_start:
{
if (lean_obj_tag(v_x_1022_) == 0)
{
lean_object* v_es_1027_; size_t v___x_1028_; size_t v___x_1029_; size_t v___x_1030_; size_t v___x_1031_; lean_object* v_j_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; 
v_es_1027_ = lean_ctor_get(v_x_1022_, 0);
v___x_1028_ = ((size_t)5ULL);
v___x_1029_ = ((size_t)1ULL);
v___x_1030_ = lean_usize_once(&l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1);
v___x_1031_ = lean_usize_land(v_x_1023_, v___x_1030_);
v_j_1032_ = lean_usize_to_nat(v___x_1031_);
v___x_1033_ = lean_array_get_size(v_es_1027_);
v___x_1034_ = lean_nat_dec_lt(v_j_1032_, v___x_1033_);
if (v___x_1034_ == 0)
{
lean_dec(v_j_1032_);
lean_dec(v_x_1026_);
lean_dec_ref(v_x_1025_);
return v_x_1022_;
}
else
{
lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1078_; 
lean_inc_ref(v_es_1027_);
v_isSharedCheck_1078_ = !lean_is_exclusive(v_x_1022_);
if (v_isSharedCheck_1078_ == 0)
{
lean_object* v_unused_1079_; 
v_unused_1079_ = lean_ctor_get(v_x_1022_, 0);
lean_dec(v_unused_1079_);
v___x_1036_ = v_x_1022_;
v_isShared_1037_ = v_isSharedCheck_1078_;
goto v_resetjp_1035_;
}
else
{
lean_dec(v_x_1022_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1078_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v_v_1038_; lean_object* v___x_1039_; lean_object* v_xs_x27_1040_; lean_object* v___y_1042_; 
v_v_1038_ = lean_array_fget(v_es_1027_, v_j_1032_);
v___x_1039_ = lean_box(0);
v_xs_x27_1040_ = lean_array_fset(v_es_1027_, v_j_1032_, v___x_1039_);
switch(lean_obj_tag(v_v_1038_))
{
case 0:
{
lean_object* v_key_1047_; lean_object* v_val_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1065_; 
v_key_1047_ = lean_ctor_get(v_v_1038_, 0);
v_val_1048_ = lean_ctor_get(v_v_1038_, 1);
v_isSharedCheck_1065_ = !lean_is_exclusive(v_v_1038_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1050_ = v_v_1038_;
v_isShared_1051_ = v_isSharedCheck_1065_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_val_1048_);
lean_inc(v_key_1047_);
lean_dec(v_v_1038_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1065_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
uint8_t v___y_1053_; lean_object* v_fst_1059_; lean_object* v_snd_1060_; lean_object* v_fst_1061_; lean_object* v_snd_1062_; uint8_t v___x_1063_; 
v_fst_1059_ = lean_ctor_get(v_x_1025_, 0);
v_snd_1060_ = lean_ctor_get(v_x_1025_, 1);
v_fst_1061_ = lean_ctor_get(v_key_1047_, 0);
v_snd_1062_ = lean_ctor_get(v_key_1047_, 1);
v___x_1063_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_1059_, v_fst_1061_);
if (v___x_1063_ == 0)
{
v___y_1053_ = v___x_1063_;
goto v___jp_1052_;
}
else
{
uint8_t v___x_1064_; 
v___x_1064_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_snd_1060_, v_snd_1062_);
v___y_1053_ = v___x_1064_;
goto v___jp_1052_;
}
v___jp_1052_:
{
if (v___y_1053_ == 0)
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
lean_del_object(v___x_1050_);
v___x_1054_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1047_, v_val_1048_, v_x_1025_, v_x_1026_);
v___x_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
v___y_1042_ = v___x_1055_;
goto v___jp_1041_;
}
else
{
lean_object* v___x_1057_; 
lean_dec(v_val_1048_);
lean_dec(v_key_1047_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 1, v_x_1026_);
lean_ctor_set(v___x_1050_, 0, v_x_1025_);
v___x_1057_ = v___x_1050_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_x_1025_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v_x_1026_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
v___y_1042_ = v___x_1057_;
goto v___jp_1041_;
}
}
}
}
}
case 1:
{
lean_object* v_node_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1076_; 
v_node_1066_ = lean_ctor_get(v_v_1038_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v_v_1038_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1068_ = v_v_1038_;
v_isShared_1069_ = v_isSharedCheck_1076_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_node_1066_);
lean_dec(v_v_1038_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1076_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
size_t v___x_1070_; size_t v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1074_; 
v___x_1070_ = lean_usize_shift_right(v_x_1023_, v___x_1028_);
v___x_1071_ = lean_usize_add(v_x_1024_, v___x_1029_);
v___x_1072_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_node_1066_, v___x_1070_, v___x_1071_, v_x_1025_, v_x_1026_);
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 0, v___x_1072_);
v___x_1074_ = v___x_1068_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1072_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
v___y_1042_ = v___x_1074_;
goto v___jp_1041_;
}
}
}
default: 
{
lean_object* v___x_1077_; 
v___x_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1077_, 0, v_x_1025_);
lean_ctor_set(v___x_1077_, 1, v_x_1026_);
v___y_1042_ = v___x_1077_;
goto v___jp_1041_;
}
}
v___jp_1041_:
{
lean_object* v___x_1043_; lean_object* v___x_1045_; 
v___x_1043_ = lean_array_fset(v_xs_x27_1040_, v_j_1032_, v___y_1042_);
lean_dec(v_j_1032_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 0, v___x_1043_);
v___x_1045_ = v___x_1036_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v___x_1043_);
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
else
{
lean_object* v_ks_1080_; lean_object* v_vs_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1101_; 
v_ks_1080_ = lean_ctor_get(v_x_1022_, 0);
v_vs_1081_ = lean_ctor_get(v_x_1022_, 1);
v_isSharedCheck_1101_ = !lean_is_exclusive(v_x_1022_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1083_ = v_x_1022_;
v_isShared_1084_ = v_isSharedCheck_1101_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_vs_1081_);
lean_inc(v_ks_1080_);
lean_dec(v_x_1022_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1101_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1084_ == 0)
{
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_ks_1080_);
lean_ctor_set(v_reuseFailAlloc_1100_, 1, v_vs_1081_);
v___x_1086_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
lean_object* v_newNode_1087_; uint8_t v___y_1089_; size_t v___x_1095_; uint8_t v___x_1096_; 
v_newNode_1087_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(v___x_1086_, v_x_1025_, v_x_1026_);
v___x_1095_ = ((size_t)7ULL);
v___x_1096_ = lean_usize_dec_le(v___x_1095_, v_x_1024_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; lean_object* v___x_1098_; uint8_t v___x_1099_; 
v___x_1097_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1087_);
v___x_1098_ = lean_unsigned_to_nat(4u);
v___x_1099_ = lean_nat_dec_lt(v___x_1097_, v___x_1098_);
lean_dec(v___x_1097_);
v___y_1089_ = v___x_1099_;
goto v___jp_1088_;
}
else
{
v___y_1089_ = v___x_1096_;
goto v___jp_1088_;
}
v___jp_1088_:
{
if (v___y_1089_ == 0)
{
lean_object* v_ks_1090_; lean_object* v_vs_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v_ks_1090_ = lean_ctor_get(v_newNode_1087_, 0);
lean_inc_ref(v_ks_1090_);
v_vs_1091_ = lean_ctor_get(v_newNode_1087_, 1);
lean_inc_ref(v_vs_1091_);
lean_dec_ref(v_newNode_1087_);
v___x_1092_ = lean_unsigned_to_nat(0u);
v___x_1093_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0);
v___x_1094_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_x_1024_, v_ks_1090_, v_vs_1091_, v___x_1092_, v___x_1093_);
lean_dec_ref(v_vs_1091_);
lean_dec_ref(v_ks_1090_);
return v___x_1094_;
}
else
{
return v_newNode_1087_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(size_t v_depth_1102_, lean_object* v_keys_1103_, lean_object* v_vals_1104_, lean_object* v_i_1105_, lean_object* v_entries_1106_){
_start:
{
lean_object* v___x_1107_; uint8_t v___x_1108_; 
v___x_1107_ = lean_array_get_size(v_keys_1103_);
v___x_1108_ = lean_nat_dec_lt(v_i_1105_, v___x_1107_);
if (v___x_1108_ == 0)
{
lean_dec(v_i_1105_);
return v_entries_1106_;
}
else
{
lean_object* v_k_1109_; lean_object* v_fst_1110_; lean_object* v_snd_1111_; lean_object* v_v_1112_; uint64_t v___x_1113_; uint64_t v___x_1114_; uint64_t v___x_1115_; size_t v_h_1116_; size_t v___x_1117_; lean_object* v___x_1118_; size_t v___x_1119_; size_t v___x_1120_; size_t v___x_1121_; size_t v_h_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v_k_1109_ = lean_array_fget_borrowed(v_keys_1103_, v_i_1105_);
v_fst_1110_ = lean_ctor_get(v_k_1109_, 0);
v_snd_1111_ = lean_ctor_get(v_k_1109_, 1);
v_v_1112_ = lean_array_fget_borrowed(v_vals_1104_, v_i_1105_);
v___x_1113_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_1110_);
v___x_1114_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_snd_1111_);
v___x_1115_ = lean_uint64_mix_hash(v___x_1113_, v___x_1114_);
v_h_1116_ = lean_uint64_to_usize(v___x_1115_);
v___x_1117_ = ((size_t)5ULL);
v___x_1118_ = lean_unsigned_to_nat(1u);
v___x_1119_ = ((size_t)1ULL);
v___x_1120_ = lean_usize_sub(v_depth_1102_, v___x_1119_);
v___x_1121_ = lean_usize_mul(v___x_1117_, v___x_1120_);
v_h_1122_ = lean_usize_shift_right(v_h_1116_, v___x_1121_);
v___x_1123_ = lean_nat_add(v_i_1105_, v___x_1118_);
lean_dec(v_i_1105_);
lean_inc(v_v_1112_);
lean_inc(v_k_1109_);
v___x_1124_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_entries_1106_, v_h_1122_, v_depth_1102_, v_k_1109_, v_v_1112_);
v_i_1105_ = v___x_1123_;
v_entries_1106_ = v___x_1124_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_1126_, lean_object* v_keys_1127_, lean_object* v_vals_1128_, lean_object* v_i_1129_, lean_object* v_entries_1130_){
_start:
{
size_t v_depth_boxed_1131_; lean_object* v_res_1132_; 
v_depth_boxed_1131_ = lean_unbox_usize(v_depth_1126_);
lean_dec(v_depth_1126_);
v_res_1132_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_depth_boxed_1131_, v_keys_1127_, v_vals_1128_, v_i_1129_, v_entries_1130_);
lean_dec_ref(v_vals_1128_);
lean_dec_ref(v_keys_1127_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___boxed(lean_object* v_x_1133_, lean_object* v_x_1134_, lean_object* v_x_1135_, lean_object* v_x_1136_, lean_object* v_x_1137_){
_start:
{
size_t v_x_2897__boxed_1138_; size_t v_x_2898__boxed_1139_; lean_object* v_res_1140_; 
v_x_2897__boxed_1138_ = lean_unbox_usize(v_x_1134_);
lean_dec(v_x_1134_);
v_x_2898__boxed_1139_ = lean_unbox_usize(v_x_1135_);
lean_dec(v_x_1135_);
v_res_1140_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_1133_, v_x_2897__boxed_1138_, v_x_2898__boxed_1139_, v_x_1136_, v_x_1137_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(lean_object* v_x_1141_, lean_object* v_x_1142_, lean_object* v_x_1143_){
_start:
{
lean_object* v_fst_1144_; lean_object* v_snd_1145_; uint64_t v___x_1146_; uint64_t v___x_1147_; uint64_t v___x_1148_; size_t v___x_1149_; size_t v___x_1150_; lean_object* v___x_1151_; 
v_fst_1144_ = lean_ctor_get(v_x_1142_, 0);
v_snd_1145_ = lean_ctor_get(v_x_1142_, 1);
v___x_1146_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_1144_);
v___x_1147_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_snd_1145_);
v___x_1148_ = lean_uint64_mix_hash(v___x_1146_, v___x_1147_);
v___x_1149_ = lean_uint64_to_usize(v___x_1148_);
v___x_1150_ = ((size_t)1ULL);
v___x_1151_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_1141_, v___x_1149_, v___x_1150_, v_x_1142_, v_x_1143_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___redArg(lean_object* v_s_1152_, lean_object* v_t_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_){
_start:
{
lean_object* v___x_1160_; lean_object* v_defEqI_1161_; lean_object* v_key_1162_; lean_object* v___x_1163_; 
v___x_1160_ = lean_st_ref_get(v_a_1154_);
v_defEqI_1161_ = lean_ctor_get(v___x_1160_, 6);
lean_inc_ref(v_defEqI_1161_);
lean_dec(v___x_1160_);
lean_inc_ref(v_t_1153_);
lean_inc_ref(v_s_1152_);
v_key_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1162_, 0, v_s_1152_);
lean_ctor_set(v_key_1162_, 1, v_t_1153_);
v___x_1163_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(v_defEqI_1161_, v_key_1162_);
if (lean_obj_tag(v___x_1163_) == 1)
{
lean_object* v_val_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1171_; 
lean_dec_ref(v_key_1162_);
lean_dec_ref(v_t_1153_);
lean_dec_ref(v_s_1152_);
v_val_1164_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1166_ = v___x_1163_;
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_val_1164_);
lean_dec(v___x_1163_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1169_; 
if (v_isShared_1167_ == 0)
{
lean_ctor_set_tag(v___x_1166_, 0);
v___x_1169_ = v___x_1166_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_val_1164_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
else
{
lean_object* v___x_1172_; 
lean_dec(v___x_1163_);
v___x_1172_ = l_Lean_Meta_isDefEqI(v_s_1152_, v_t_1153_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1198_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1175_ = v___x_1172_;
v_isShared_1176_ = v_isSharedCheck_1198_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1172_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1198_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1177_; lean_object* v_share_1178_; lean_object* v_maxFVar_1179_; lean_object* v_proofInstInfo_1180_; lean_object* v_inferType_1181_; lean_object* v_getLevel_1182_; lean_object* v_congrInfo_1183_; lean_object* v_defEqI_1184_; uint8_t v_debug_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1197_; 
v___x_1177_ = lean_st_ref_take(v_a_1154_);
v_share_1178_ = lean_ctor_get(v___x_1177_, 0);
v_maxFVar_1179_ = lean_ctor_get(v___x_1177_, 1);
v_proofInstInfo_1180_ = lean_ctor_get(v___x_1177_, 2);
v_inferType_1181_ = lean_ctor_get(v___x_1177_, 3);
v_getLevel_1182_ = lean_ctor_get(v___x_1177_, 4);
v_congrInfo_1183_ = lean_ctor_get(v___x_1177_, 5);
v_defEqI_1184_ = lean_ctor_get(v___x_1177_, 6);
v_debug_1185_ = lean_ctor_get_uint8(v___x_1177_, sizeof(void*)*7);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1187_ = v___x_1177_;
v_isShared_1188_ = v_isSharedCheck_1197_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_defEqI_1184_);
lean_inc(v_congrInfo_1183_);
lean_inc(v_getLevel_1182_);
lean_inc(v_inferType_1181_);
lean_inc(v_proofInstInfo_1180_);
lean_inc(v_maxFVar_1179_);
lean_inc(v_share_1178_);
lean_dec(v___x_1177_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1197_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1189_; lean_object* v___x_1191_; 
lean_inc(v_a_1173_);
v___x_1189_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(v_defEqI_1184_, v_key_1162_, v_a_1173_);
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 6, v___x_1189_);
v___x_1191_ = v___x_1187_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_share_1178_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v_maxFVar_1179_);
lean_ctor_set(v_reuseFailAlloc_1196_, 2, v_proofInstInfo_1180_);
lean_ctor_set(v_reuseFailAlloc_1196_, 3, v_inferType_1181_);
lean_ctor_set(v_reuseFailAlloc_1196_, 4, v_getLevel_1182_);
lean_ctor_set(v_reuseFailAlloc_1196_, 5, v_congrInfo_1183_);
lean_ctor_set(v_reuseFailAlloc_1196_, 6, v___x_1189_);
lean_ctor_set_uint8(v_reuseFailAlloc_1196_, sizeof(void*)*7, v_debug_1185_);
v___x_1191_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
lean_object* v___x_1192_; lean_object* v___x_1194_; 
v___x_1192_ = lean_st_ref_set(v_a_1154_, v___x_1191_);
if (v_isShared_1176_ == 0)
{
v___x_1194_ = v___x_1175_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_a_1173_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
}
else
{
lean_dec_ref(v_key_1162_);
return v___x_1172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___redArg___boxed(lean_object* v_s_1199_, lean_object* v_t_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_s_1199_, v_t_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_);
lean_dec(v_a_1205_);
lean_dec_ref(v_a_1204_);
lean_dec(v_a_1203_);
lean_dec_ref(v_a_1202_);
lean_dec(v_a_1201_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI(lean_object* v_s_1208_, lean_object* v_t_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_){
_start:
{
lean_object* v___x_1217_; 
v___x_1217_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_s_1208_, v_t_1209_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___boxed(lean_object* v_s_1218_, lean_object* v_t_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l_Lean_Meta_Sym_isDefEqI(v_s_1218_, v_t_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_);
lean_dec(v_a_1225_);
lean_dec_ref(v_a_1224_);
lean_dec(v_a_1223_);
lean_dec_ref(v_a_1222_);
lean_dec(v_a_1221_);
lean_dec_ref(v_a_1220_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0(lean_object* v_00_u03b2_1228_, lean_object* v_x_1229_, lean_object* v_x_1230_){
_start:
{
lean_object* v___x_1231_; 
v___x_1231_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(v_x_1229_, v_x_1230_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___boxed(lean_object* v_00_u03b2_1232_, lean_object* v_x_1233_, lean_object* v_x_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0(v_00_u03b2_1232_, v_x_1233_, v_x_1234_);
lean_dec_ref(v_x_1234_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1(lean_object* v_00_u03b2_1236_, lean_object* v_x_1237_, lean_object* v_x_1238_, lean_object* v_x_1239_){
_start:
{
lean_object* v___x_1240_; 
v___x_1240_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(v_x_1237_, v_x_1238_, v_x_1239_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0(lean_object* v_00_u03b2_1241_, lean_object* v_x_1242_, size_t v_x_1243_, lean_object* v_x_1244_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_1242_, v_x_1243_, v_x_1244_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1246_, lean_object* v_x_1247_, lean_object* v_x_1248_, lean_object* v_x_1249_){
_start:
{
size_t v_x_3176__boxed_1250_; lean_object* v_res_1251_; 
v_x_3176__boxed_1250_ = lean_unbox_usize(v_x_1248_);
lean_dec(v_x_1248_);
v_res_1251_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0(v_00_u03b2_1246_, v_x_1247_, v_x_3176__boxed_1250_, v_x_1249_);
lean_dec_ref(v_x_1249_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2(lean_object* v_00_u03b2_1252_, lean_object* v_x_1253_, size_t v_x_1254_, size_t v_x_1255_, lean_object* v_x_1256_, lean_object* v_x_1257_){
_start:
{
lean_object* v___x_1258_; 
v___x_1258_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_1253_, v_x_1254_, v_x_1255_, v_x_1256_, v_x_1257_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1259_, lean_object* v_x_1260_, lean_object* v_x_1261_, lean_object* v_x_1262_, lean_object* v_x_1263_, lean_object* v_x_1264_){
_start:
{
size_t v_x_3187__boxed_1265_; size_t v_x_3188__boxed_1266_; lean_object* v_res_1267_; 
v_x_3187__boxed_1265_ = lean_unbox_usize(v_x_1261_);
lean_dec(v_x_1261_);
v_x_3188__boxed_1266_ = lean_unbox_usize(v_x_1262_);
lean_dec(v_x_1262_);
v_res_1267_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2(v_00_u03b2_1259_, v_x_1260_, v_x_3187__boxed_1265_, v_x_3188__boxed_1266_, v_x_1263_, v_x_1264_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1268_, lean_object* v_keys_1269_, lean_object* v_vals_1270_, lean_object* v_heq_1271_, lean_object* v_i_1272_, lean_object* v_k_1273_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_keys_1269_, v_vals_1270_, v_i_1272_, v_k_1273_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1275_, lean_object* v_keys_1276_, lean_object* v_vals_1277_, lean_object* v_heq_1278_, lean_object* v_i_1279_, lean_object* v_k_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1(v_00_u03b2_1275_, v_keys_1276_, v_vals_1277_, v_heq_1278_, v_i_1279_, v_k_1280_);
lean_dec_ref(v_k_1280_);
lean_dec_ref(v_vals_1277_);
lean_dec_ref(v_keys_1276_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1282_, lean_object* v_n_1283_, lean_object* v_k_1284_, lean_object* v_v_1285_){
_start:
{
lean_object* v___x_1286_; 
v___x_1286_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(v_n_1283_, v_k_1284_, v_v_1285_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1287_, size_t v_depth_1288_, lean_object* v_keys_1289_, lean_object* v_vals_1290_, lean_object* v_heq_1291_, lean_object* v_i_1292_, lean_object* v_entries_1293_){
_start:
{
lean_object* v___x_1294_; 
v___x_1294_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_depth_1288_, v_keys_1289_, v_vals_1290_, v_i_1292_, v_entries_1293_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1295_, lean_object* v_depth_1296_, lean_object* v_keys_1297_, lean_object* v_vals_1298_, lean_object* v_heq_1299_, lean_object* v_i_1300_, lean_object* v_entries_1301_){
_start:
{
size_t v_depth_boxed_1302_; lean_object* v_res_1303_; 
v_depth_boxed_1302_ = lean_unbox_usize(v_depth_1296_);
lean_dec(v_depth_1296_);
v_res_1303_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5(v_00_u03b2_1295_, v_depth_boxed_1302_, v_keys_1297_, v_vals_1298_, v_heq_1299_, v_i_1300_, v_entries_1301_);
lean_dec_ref(v_vals_1298_);
lean_dec_ref(v_keys_1297_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_1304_, lean_object* v_x_1305_, lean_object* v_x_1306_, lean_object* v_x_1307_, lean_object* v_x_1308_){
_start:
{
lean_object* v___x_1309_; 
v___x_1309_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(v_x_1305_, v_x_1306_, v_x_1307_, v_x_1308_);
return v___x_1309_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareCommon(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CongrTheorems(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_AlphaShareCommon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CongrTheorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Sym_sym_debug = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Sym_sym_debug);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_SymM(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_AlphaShareCommon(uint8_t builtin);
lean_object* initialize_Lean_Meta_CongrTheorems(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_AlphaShareCommon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CongrTheorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_SymM(builtin);
}
#ifdef __cplusplus
}
#endif
