// Lean compiler output
// Module: Lean.Meta.Sym.Arith.Classify
// Imports: public import Lean.Meta.Sym.Arith.Insts import Lean.Meta.Sym.SynthInstance import Lean.Meta.Sym.Canon import Lean.Meta.DecLevel import Init.Grind.Ring
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
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Meta_getDecLevel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_getArithState___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Sym_Arith_arithExt;
lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_getIsCharInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_registerInstance___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
extern lean_object* l_Lean_Nat_mkType;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Sym_Arith_instInhabitedCommRing_default;
extern lean_object* l_Lean_Meta_Sym_Arith_instInhabitedRing_default;
extern lean_object* l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring_default;
extern lean_object* l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default;
lean_object* l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_mkIsPartialOrderInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_mkIsLinearPreorderInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "CommRing"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "OfCommSemiring"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "ofCommSemiring"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(219, 56, 247, 159, 186, 83, 86, 251)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(36, 61, 219, 203, 190, 113, 236, 200)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "toRing"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(247, 129, 99, 43, 16, 237, 154, 169)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__7 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Ring"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__8 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "toSemiring"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__9 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__10_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(155, 231, 134, 53, 190, 181, 242, 194)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__10 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "toCommSemiring"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__11 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__12_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__12_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__11_value),LEAN_SCALAR_PTR_LITERAL(134, 95, 181, 253, 18, 104, 213, 131)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__12 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__13_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__13 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__14_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__14 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Semiring"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__15 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__16_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__16 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "CommSemiring"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__17 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__17_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__18_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__18_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__17_value),LEAN_SCALAR_PTR_LITERAL(69, 110, 106, 77, 169, 45, 119, 219)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__18 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "NatModule"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__19 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__19_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__20_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__19_value),LEAN_SCALAR_PTR_LITERAL(134, 252, 171, 186, 15, 174, 251, 179)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__20 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__20_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "toNatModule"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__21 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__21_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__22_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__22_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__22_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__21_value),LEAN_SCALAR_PTR_LITERAL(156, 107, 255, 119, 73, 35, 26, 237)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__22 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__22_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__23 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__23_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__23_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__24 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__24_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHAdd"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__25 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__25_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__25_value),LEAN_SCALAR_PTR_LITERAL(229, 81, 239, 34, 203, 244, 36, 133)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__26 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__26_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toAdd"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__27 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__27_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__28_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__28_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__28_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__27_value),LEAN_SCALAR_PTR_LITERAL(7, 205, 186, 60, 7, 38, 135, 75)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__28 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__28_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__29 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__29_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__29_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__30 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__30_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHMul"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__31 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__31_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__31_value),LEAN_SCALAR_PTR_LITERAL(177, 107, 107, 59, 202, 230, 169, 251)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__32 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__32_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toMul"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__33 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__33_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__34_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__34_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__34_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__34_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__33_value),LEAN_SCALAR_PTR_LITERAL(232, 23, 103, 115, 5, 120, 143, 98)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__34 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__34_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__35 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__35_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__35_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__36 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__36_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHSub"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__37 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__37_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__37_value),LEAN_SCALAR_PTR_LITERAL(32, 225, 92, 14, 170, 61, 170, 140)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__38 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__38_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toSub"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__39 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__39_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__40_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__40_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__40_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__40_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__40_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__39_value),LEAN_SCALAR_PTR_LITERAL(8, 241, 181, 204, 215, 46, 40, 252)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__40 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__40_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__41 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__41_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__41_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__42 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__42_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toNeg"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__43 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__43_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__44_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__44_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__44_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__44_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__44_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__43_value),LEAN_SCALAR_PTR_LITERAL(100, 233, 103, 154, 53, 22, 86, 139)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__44 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__44_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__45 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__45_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__45_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__46 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__46_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__47;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "npow"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__48 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__48_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__49_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__49_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__49_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__49_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__48_value),LEAN_SCALAR_PTR_LITERAL(227, 91, 39, 101, 227, 157, 49, 255)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__49 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__49_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NatCast"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__50 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__50_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__50_value),LEAN_SCALAR_PTR_LITERAL(65, 128, 63, 191, 243, 154, 52, 80)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__51 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__51_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "natCast"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__52 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__52_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__53_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__53_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__53_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__53_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__53_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__53_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__52_value),LEAN_SCALAR_PTR_LITERAL(84, 97, 73, 37, 143, 22, 233, 204)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__53 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__53_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "IntCast"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__54 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__54_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__54_value),LEAN_SCALAR_PTR_LITERAL(63, 186, 193, 83, 149, 255, 18, 69)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__55 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__55_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "intCast"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__56 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__56_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__57_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__57_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__57_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__57_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__57_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__56_value),LEAN_SCALAR_PTR_LITERAL(1, 189, 244, 99, 68, 50, 19, 202)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__57 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__57_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__58 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__58_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ring"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__59 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__59_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__58_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__60_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__59_value),LEAN_SCALAR_PTR_LITERAL(17, 56, 209, 254, 185, 203, 153, 57)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__60 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__60_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "PowIdentity available: false"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__62 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__62_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__63_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__63;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "NoNatZeroDivisors available: "};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__64 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__64_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__65_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__65;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__66 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__66_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__67 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__67_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "OfSemiring"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__68 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__68_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "instNoNatZeroDivisorsQOfAddRightCancel"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__69 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__69_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__70_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__70_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__70_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__70_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__70_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__70_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__70_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__68_value),LEAN_SCALAR_PTR_LITERAL(214, 53, 64, 113, 205, 30, 141, 114)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__70_value_aux_3),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__69_value),LEAN_SCALAR_PTR_LITERAL(221, 130, 167, 21, 145, 237, 132, 218)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__70 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__70_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Add"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__71 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__71_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__71_value),LEAN_SCALAR_PTR_LITERAL(123, 91, 0, 102, 155, 93, 69, 240)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__72 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__72_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "AddRightCancel"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__73 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__73_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__74_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__74_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__74_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__74_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__73_value),LEAN_SCALAR_PTR_LITERAL(33, 101, 175, 31, 110, 234, 168, 33)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__74 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__74_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "instIsCharPQOfAddRightCancel"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__75 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__75_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__76_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__76_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__76_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__76_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__76_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__76_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__76_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__68_value),LEAN_SCALAR_PTR_LITERAL(214, 53, 64, 113, 205, 30, 141, 114)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__76_value_aux_3),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__75_value),LEAN_SCALAR_PTR_LITERAL(194, 21, 126, 159, 192, 171, 59, 180)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__76 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__76_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "new ring: "};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__77 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__77_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Field"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "PowIdentity available: "};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "Q"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__68_value),LEAN_SCALAR_PTR_LITERAL(214, 53, 64, 113, 205, 30, 141, 114)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(184, 238, 182, 216, 107, 45, 243, 168)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__17_value),LEAN_SCALAR_PTR_LITERAL(69, 110, 106, 77, 169, 45, 119, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(134, 3, 13, 60, 96, 160, 201, 59)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__1(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "unexpected failure initializing ring"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_classify_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_classify_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classify_x3f___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classify_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classify_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_canonFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_canonFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "OrderedRing"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 123, 155, 51, 122, 17, 247, 247)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___lam__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__7 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classifyOrder_x3f___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classifyOrder_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classifyOrder_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__0(lean_object* v___x_1_, lean_object* v_s_2_){
_start:
{
lean_object* v_exp_3_; lean_object* v_rings_4_; lean_object* v_semirings_5_; lean_object* v_ncRings_6_; lean_object* v_ncSemirings_7_; lean_object* v_typeClassify_8_; lean_object* v_orders_9_; lean_object* v_typeOrderClassify_10_; lean_object* v___x_12_; uint8_t v_isShared_13_; uint8_t v_isSharedCheck_18_; 
v_exp_3_ = lean_ctor_get(v_s_2_, 0);
v_rings_4_ = lean_ctor_get(v_s_2_, 1);
v_semirings_5_ = lean_ctor_get(v_s_2_, 2);
v_ncRings_6_ = lean_ctor_get(v_s_2_, 3);
v_ncSemirings_7_ = lean_ctor_get(v_s_2_, 4);
v_typeClassify_8_ = lean_ctor_get(v_s_2_, 5);
v_orders_9_ = lean_ctor_get(v_s_2_, 6);
v_typeOrderClassify_10_ = lean_ctor_get(v_s_2_, 7);
v_isSharedCheck_18_ = !lean_is_exclusive(v_s_2_);
if (v_isSharedCheck_18_ == 0)
{
v___x_12_ = v_s_2_;
v_isShared_13_ = v_isSharedCheck_18_;
goto v_resetjp_11_;
}
else
{
lean_inc(v_typeOrderClassify_10_);
lean_inc(v_orders_9_);
lean_inc(v_typeClassify_8_);
lean_inc(v_ncSemirings_7_);
lean_inc(v_ncRings_6_);
lean_inc(v_semirings_5_);
lean_inc(v_rings_4_);
lean_inc(v_exp_3_);
lean_dec(v_s_2_);
v___x_12_ = lean_box(0);
v_isShared_13_ = v_isSharedCheck_18_;
goto v_resetjp_11_;
}
v_resetjp_11_:
{
lean_object* v___x_14_; lean_object* v___x_16_; 
v___x_14_ = lean_array_push(v_rings_4_, v___x_1_);
if (v_isShared_13_ == 0)
{
lean_ctor_set(v___x_12_, 1, v___x_14_);
v___x_16_ = v___x_12_;
goto v_reusejp_15_;
}
else
{
lean_object* v_reuseFailAlloc_17_; 
v_reuseFailAlloc_17_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_17_, 0, v_exp_3_);
lean_ctor_set(v_reuseFailAlloc_17_, 1, v___x_14_);
lean_ctor_set(v_reuseFailAlloc_17_, 2, v_semirings_5_);
lean_ctor_set(v_reuseFailAlloc_17_, 3, v_ncRings_6_);
lean_ctor_set(v_reuseFailAlloc_17_, 4, v_ncSemirings_7_);
lean_ctor_set(v_reuseFailAlloc_17_, 5, v_typeClassify_8_);
lean_ctor_set(v_reuseFailAlloc_17_, 6, v_orders_9_);
lean_ctor_set(v_reuseFailAlloc_17_, 7, v_typeOrderClassify_10_);
v___x_16_ = v_reuseFailAlloc_17_;
goto v_reusejp_15_;
}
v_reusejp_15_:
{
return v___x_16_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1(lean_object* v___x_22_, lean_object* v_____do__lift_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_toCold_31_; lean_object* v_options_32_; uint8_t v_hasTrace_33_; 
v_toCold_31_ = lean_ctor_get(v___y_28_, 0);
v_options_32_ = lean_ctor_get(v_toCold_31_, 2);
v_hasTrace_33_ = lean_ctor_get_uint8(v_options_32_, sizeof(void*)*1);
if (v_hasTrace_33_ == 0)
{
lean_object* v___x_34_; lean_object* v___x_35_; 
lean_dec(v___x_22_);
v___x_34_ = lean_box(v_hasTrace_33_);
v___x_35_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
return v___x_35_;
}
else
{
lean_object* v___x_36_; lean_object* v___x_37_; uint8_t v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_36_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1___closed__1));
v___x_37_ = l_Lean_Name_append(v___x_36_, v___x_22_);
v___x_38_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_23_, v_options_32_, v___x_37_);
lean_dec(v___x_37_);
v___x_39_ = lean_box(v___x_38_);
v___x_40_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_40_, 0, v___x_39_);
return v___x_40_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1___boxed(lean_object* v___x_41_, lean_object* v_____do__lift_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1(v___x_41_, v_____do__lift_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
lean_dec(v___y_46_);
lean_dec_ref(v___y_45_);
lean_dec(v___y_44_);
lean_dec_ref(v___y_43_);
lean_dec_ref(v_____do__lift_42_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0_spec__0(lean_object* v_msgData_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v___x_57_; lean_object* v_env_58_; uint8_t v___x_59_; lean_object* v_env_60_; lean_object* v___x_61_; lean_object* v_toCold_62_; lean_object* v_mctx_63_; lean_object* v_lctx_64_; lean_object* v_options_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_57_ = lean_st_ref_get(v___y_55_);
v_env_58_ = lean_ctor_get(v___x_57_, 0);
lean_inc_ref(v_env_58_);
lean_dec(v___x_57_);
v___x_59_ = 0;
v_env_60_ = l_Lean_Environment_setRecordingDeps(v_env_58_, v___x_59_);
v___x_61_ = lean_st_ref_get(v___y_53_);
v_toCold_62_ = lean_ctor_get(v___y_54_, 0);
v_mctx_63_ = lean_ctor_get(v___x_61_, 0);
lean_inc_ref(v_mctx_63_);
lean_dec(v___x_61_);
v_lctx_64_ = lean_ctor_get(v___y_52_, 2);
v_options_65_ = lean_ctor_get(v_toCold_62_, 2);
lean_inc_ref(v_options_65_);
lean_inc_ref(v_lctx_64_);
v___x_66_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_66_, 0, v_env_60_);
lean_ctor_set(v___x_66_, 1, v_mctx_63_);
lean_ctor_set(v___x_66_, 2, v_lctx_64_);
lean_ctor_set(v___x_66_, 3, v_options_65_);
v___x_67_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
lean_ctor_set(v___x_67_, 1, v_msgData_51_);
v___x_68_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0_spec__0___boxed(lean_object* v_msgData_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0_spec__0(v_msgData_69_, v___y_70_, v___y_71_, v___y_72_, v___y_73_);
lean_dec(v___y_73_);
lean_dec_ref(v___y_72_);
lean_dec(v___y_71_);
lean_dec_ref(v___y_70_);
return v_res_75_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_76_; double v___x_77_; 
v___x_76_ = lean_unsigned_to_nat(0u);
v___x_77_ = lean_float_of_nat(v___x_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(lean_object* v_cls_81_, lean_object* v_msg_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
lean_object* v_ref_88_; lean_object* v___x_89_; lean_object* v_a_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_135_; 
v_ref_88_ = lean_ctor_get(v___y_85_, 2);
v___x_89_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0_spec__0(v_msg_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_);
v_a_90_ = lean_ctor_get(v___x_89_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v___x_89_);
if (v_isSharedCheck_135_ == 0)
{
v___x_92_ = v___x_89_;
v_isShared_93_ = v_isSharedCheck_135_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_a_90_);
lean_dec(v___x_89_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_135_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v___x_94_; lean_object* v_traceState_95_; lean_object* v_env_96_; lean_object* v_nextMacroScope_97_; lean_object* v_ngen_98_; lean_object* v_auxDeclNGen_99_; lean_object* v_cache_100_; lean_object* v_recordedDeps_101_; lean_object* v_messages_102_; lean_object* v_infoState_103_; lean_object* v_snapshotTasks_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_134_; 
v___x_94_ = lean_st_ref_take(v___y_86_);
v_traceState_95_ = lean_ctor_get(v___x_94_, 4);
v_env_96_ = lean_ctor_get(v___x_94_, 0);
v_nextMacroScope_97_ = lean_ctor_get(v___x_94_, 1);
v_ngen_98_ = lean_ctor_get(v___x_94_, 2);
v_auxDeclNGen_99_ = lean_ctor_get(v___x_94_, 3);
v_cache_100_ = lean_ctor_get(v___x_94_, 5);
v_recordedDeps_101_ = lean_ctor_get(v___x_94_, 6);
v_messages_102_ = lean_ctor_get(v___x_94_, 7);
v_infoState_103_ = lean_ctor_get(v___x_94_, 8);
v_snapshotTasks_104_ = lean_ctor_get(v___x_94_, 9);
v_isSharedCheck_134_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_134_ == 0)
{
v___x_106_ = v___x_94_;
v_isShared_107_ = v_isSharedCheck_134_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_snapshotTasks_104_);
lean_inc(v_infoState_103_);
lean_inc(v_messages_102_);
lean_inc(v_recordedDeps_101_);
lean_inc(v_cache_100_);
lean_inc(v_traceState_95_);
lean_inc(v_auxDeclNGen_99_);
lean_inc(v_ngen_98_);
lean_inc(v_nextMacroScope_97_);
lean_inc(v_env_96_);
lean_dec(v___x_94_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_134_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
uint64_t v_tid_108_; lean_object* v_traces_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_133_; 
v_tid_108_ = lean_ctor_get_uint64(v_traceState_95_, sizeof(void*)*1);
v_traces_109_ = lean_ctor_get(v_traceState_95_, 0);
v_isSharedCheck_133_ = !lean_is_exclusive(v_traceState_95_);
if (v_isSharedCheck_133_ == 0)
{
v___x_111_ = v_traceState_95_;
v_isShared_112_ = v_isSharedCheck_133_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_traces_109_);
lean_dec(v_traceState_95_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_133_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_113_; lean_object* v___x_114_; double v___x_115_; uint8_t v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_124_; 
v___x_113_ = lean_box(0);
v___x_114_ = lean_box(0);
v___x_115_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__0);
v___x_116_ = 0;
v___x_117_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__1));
v___x_118_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_118_, 0, v_cls_81_);
lean_ctor_set(v___x_118_, 1, v___x_114_);
lean_ctor_set(v___x_118_, 2, v___x_117_);
lean_ctor_set_float(v___x_118_, sizeof(void*)*3, v___x_115_);
lean_ctor_set_float(v___x_118_, sizeof(void*)*3 + 8, v___x_115_);
lean_ctor_set_uint8(v___x_118_, sizeof(void*)*3 + 16, v___x_116_);
v___x_119_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__2));
v___x_120_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_120_, 0, v___x_118_);
lean_ctor_set(v___x_120_, 1, v_a_90_);
lean_ctor_set(v___x_120_, 2, v___x_119_);
lean_inc(v_ref_88_);
v___x_121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_121_, 0, v_ref_88_);
lean_ctor_set(v___x_121_, 1, v___x_120_);
v___x_122_ = l_Lean_PersistentArray_push___redArg(v_traces_109_, v___x_121_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v___x_122_);
v___x_124_ = v___x_111_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v___x_122_);
lean_ctor_set_uint64(v_reuseFailAlloc_132_, sizeof(void*)*1, v_tid_108_);
v___x_124_ = v_reuseFailAlloc_132_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
lean_object* v___x_126_; 
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 4, v___x_124_);
v___x_126_ = v___x_106_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_env_96_);
lean_ctor_set(v_reuseFailAlloc_131_, 1, v_nextMacroScope_97_);
lean_ctor_set(v_reuseFailAlloc_131_, 2, v_ngen_98_);
lean_ctor_set(v_reuseFailAlloc_131_, 3, v_auxDeclNGen_99_);
lean_ctor_set(v_reuseFailAlloc_131_, 4, v___x_124_);
lean_ctor_set(v_reuseFailAlloc_131_, 5, v_cache_100_);
lean_ctor_set(v_reuseFailAlloc_131_, 6, v_recordedDeps_101_);
lean_ctor_set(v_reuseFailAlloc_131_, 7, v_messages_102_);
lean_ctor_set(v_reuseFailAlloc_131_, 8, v_infoState_103_);
lean_ctor_set(v_reuseFailAlloc_131_, 9, v_snapshotTasks_104_);
v___x_126_ = v_reuseFailAlloc_131_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
lean_object* v___x_127_; lean_object* v___x_129_; 
v___x_127_ = lean_st_ref_put(v___y_86_, v___x_126_);
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 0, v___x_113_);
v___x_129_ = v___x_92_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v___x_113_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___boxed(lean_object* v_cls_136_, lean_object* v_msg_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(v_cls_136_, v_msg_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
return v_res_143_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__47(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = lean_unsigned_to_nat(0u);
v___x_252_ = l_Lean_Level_ofNat(v___x_251_);
return v___x_252_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_282_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__60));
v___x_283_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1___closed__1));
v___x_284_ = l_Lean_Name_append(v___x_283_, v___x_282_);
return v___x_284_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__63(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_286_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__62));
v___x_287_ = l_Lean_stringToMessageData(v___x_286_);
return v___x_287_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__65(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__64));
v___x_290_ = l_Lean_stringToMessageData(v___x_289_);
return v___x_290_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__77));
v___x_318_ = l_Lean_stringToMessageData(v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f(lean_object* v_type_319_, lean_object* v_base_320_, lean_object* v_semiringInst_321_, lean_object* v_commSemiringInst_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v___x_330_; 
lean_inc_ref(v_base_320_);
v___x_330_ = l_Lean_Meta_getDecLevel_x3f(v_base_320_, v_a_325_, v_a_326_, v_a_327_, v_a_328_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_775_; 
v_a_331_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_775_ == 0)
{
v___x_333_ = v___x_330_;
v_isShared_334_ = v_isSharedCheck_775_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_330_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_775_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
if (lean_obj_tag(v_a_331_) == 1)
{
lean_object* v_val_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_770_; 
lean_del_object(v___x_333_);
v_val_335_ = lean_ctor_get(v_a_331_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v_a_331_);
if (v_isSharedCheck_770_ == 0)
{
v___x_337_ = v_a_331_;
v_isShared_338_ = v_isSharedCheck_770_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_val_335_);
lean_dec(v_a_331_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_770_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___y_354_; lean_object* v___y_355_; lean_object* v___y_356_; lean_object* v___y_357_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_339_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__5));
v___x_340_ = lean_box(0);
lean_inc(v_val_335_);
v___x_341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_341_, 0, v_val_335_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
lean_inc_ref_n(v___x_341_, 5);
v___x_342_ = l_Lean_mkConst(v___x_339_, v___x_341_);
lean_inc_ref(v_base_320_);
v___x_343_ = l_Lean_mkAppB(v___x_342_, v_base_320_, v_commSemiringInst_322_);
v___x_344_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__7));
v___x_345_ = l_Lean_mkConst(v___x_344_, v___x_341_);
lean_inc_ref_n(v___x_343_, 2);
lean_inc_ref_n(v_type_319_, 4);
v___x_346_ = l_Lean_mkAppB(v___x_345_, v_type_319_, v___x_343_);
v___x_347_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__10));
v___x_348_ = l_Lean_mkConst(v___x_347_, v___x_341_);
lean_inc_ref(v___x_346_);
v___x_349_ = l_Lean_mkAppB(v___x_348_, v_type_319_, v___x_346_);
v___x_350_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__12));
v___x_351_ = l_Lean_mkConst(v___x_350_, v___x_341_);
lean_inc_ref(v___x_349_);
v___x_352_ = l_Lean_mkAppB(v___x_351_, v_type_319_, v___x_349_);
v___x_395_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__13));
v___x_396_ = l_Lean_mkConst(v___x_395_, v___x_341_);
v___x_397_ = l_Lean_Expr_app___override(v___x_396_, v_type_319_);
v___x_398_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_397_, v___x_343_, v_a_324_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
lean_dec_ref_known(v___x_398_, 1);
v___x_399_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__14));
lean_inc_ref(v___x_341_);
v___x_400_ = l_Lean_mkConst(v___x_399_, v___x_341_);
lean_inc_ref(v_type_319_);
v___x_401_ = l_Lean_Expr_app___override(v___x_400_, v_type_319_);
lean_inc_ref(v___x_346_);
v___x_402_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_401_, v___x_346_, v_a_324_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
lean_dec_ref_known(v___x_402_, 1);
v___x_403_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__16));
lean_inc_ref(v___x_341_);
v___x_404_ = l_Lean_mkConst(v___x_403_, v___x_341_);
lean_inc_ref(v_type_319_);
v___x_405_ = l_Lean_Expr_app___override(v___x_404_, v_type_319_);
lean_inc_ref(v___x_349_);
v___x_406_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_405_, v___x_349_, v_a_324_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
lean_dec_ref_known(v___x_406_, 1);
v___x_407_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__18));
lean_inc_ref(v___x_341_);
v___x_408_ = l_Lean_mkConst(v___x_407_, v___x_341_);
lean_inc_ref(v_type_319_);
v___x_409_ = l_Lean_Expr_app___override(v___x_408_, v_type_319_);
lean_inc_ref(v___x_352_);
v___x_410_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_409_, v___x_352_, v_a_324_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
lean_dec_ref_known(v___x_410_, 1);
v___x_411_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__20));
lean_inc_ref_n(v___x_341_, 2);
v___x_412_ = l_Lean_mkConst(v___x_411_, v___x_341_);
lean_inc_ref_n(v_type_319_, 2);
v___x_413_ = l_Lean_Expr_app___override(v___x_412_, v_type_319_);
v___x_414_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__22));
v___x_415_ = l_Lean_mkConst(v___x_414_, v___x_341_);
lean_inc_ref(v___x_349_);
v___x_416_ = l_Lean_mkAppB(v___x_415_, v_type_319_, v___x_349_);
v___x_417_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_413_, v___x_416_, v_a_324_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
lean_dec_ref_known(v___x_417_, 1);
v___x_418_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__24));
lean_inc_ref_n(v___x_341_, 3);
lean_inc_n(v_val_335_, 2);
v___x_419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_419_, 0, v_val_335_);
lean_ctor_set(v___x_419_, 1, v___x_341_);
v___x_420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_420_, 0, v_val_335_);
lean_ctor_set(v___x_420_, 1, v___x_419_);
lean_inc_ref(v___x_420_);
v___x_421_ = l_Lean_mkConst(v___x_418_, v___x_420_);
lean_inc_ref_n(v_type_319_, 5);
v___x_422_ = l_Lean_mkApp3(v___x_421_, v_type_319_, v_type_319_, v_type_319_);
v___x_423_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__26));
v___x_424_ = l_Lean_mkConst(v___x_423_, v___x_341_);
v___x_425_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__28));
v___x_426_ = l_Lean_mkConst(v___x_425_, v___x_341_);
lean_inc_ref(v___x_349_);
v___x_427_ = l_Lean_mkAppB(v___x_426_, v_type_319_, v___x_349_);
v___x_428_ = l_Lean_mkAppB(v___x_424_, v_type_319_, v___x_427_);
v___x_429_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_422_, v___x_428_, v_a_324_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
lean_dec_ref_known(v___x_429_, 1);
v___x_430_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__30));
lean_inc_ref(v___x_420_);
v___x_431_ = l_Lean_mkConst(v___x_430_, v___x_420_);
lean_inc_ref_n(v_type_319_, 5);
v___x_432_ = l_Lean_mkApp3(v___x_431_, v_type_319_, v_type_319_, v_type_319_);
v___x_433_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__32));
lean_inc_ref_n(v___x_341_, 2);
v___x_434_ = l_Lean_mkConst(v___x_433_, v___x_341_);
v___x_435_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__34));
v___x_436_ = l_Lean_mkConst(v___x_435_, v___x_341_);
lean_inc_ref(v___x_349_);
v___x_437_ = l_Lean_mkAppB(v___x_436_, v_type_319_, v___x_349_);
v___x_438_ = l_Lean_mkAppB(v___x_434_, v_type_319_, v___x_437_);
v___x_439_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_432_, v___x_438_, v_a_324_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
lean_dec_ref_known(v___x_439_, 1);
v___x_440_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__36));
v___x_441_ = l_Lean_mkConst(v___x_440_, v___x_420_);
lean_inc_ref_n(v_type_319_, 5);
v___x_442_ = l_Lean_mkApp3(v___x_441_, v_type_319_, v_type_319_, v_type_319_);
v___x_443_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__38));
lean_inc_ref_n(v___x_341_, 2);
v___x_444_ = l_Lean_mkConst(v___x_443_, v___x_341_);
v___x_445_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__40));
v___x_446_ = l_Lean_mkConst(v___x_445_, v___x_341_);
lean_inc_ref(v___x_346_);
v___x_447_ = l_Lean_mkAppB(v___x_446_, v_type_319_, v___x_346_);
v___x_448_ = l_Lean_mkAppB(v___x_444_, v_type_319_, v___x_447_);
v___x_449_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_442_, v___x_448_, v_a_324_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
lean_dec_ref_known(v___x_449_, 1);
v___x_450_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__42));
lean_inc_ref_n(v___x_341_, 2);
v___x_451_ = l_Lean_mkConst(v___x_450_, v___x_341_);
lean_inc_ref_n(v_type_319_, 2);
v___x_452_ = l_Lean_Expr_app___override(v___x_451_, v_type_319_);
v___x_453_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__44));
v___x_454_ = l_Lean_mkConst(v___x_453_, v___x_341_);
lean_inc_ref(v___x_346_);
v___x_455_ = l_Lean_mkAppB(v___x_454_, v_type_319_, v___x_346_);
v___x_456_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_452_, v___x_455_, v_a_324_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
lean_dec_ref_known(v___x_456_, 1);
v___x_457_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__46));
v___x_458_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__47, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__47_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__47);
lean_inc_ref_n(v___x_341_, 2);
v___x_459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
lean_ctor_set(v___x_459_, 1, v___x_341_);
lean_inc(v_val_335_);
v___x_460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_460_, 0, v_val_335_);
lean_ctor_set(v___x_460_, 1, v___x_459_);
v___x_461_ = l_Lean_mkConst(v___x_457_, v___x_460_);
v___x_462_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_319_, 3);
v___x_463_ = l_Lean_mkApp3(v___x_461_, v_type_319_, v___x_462_, v_type_319_);
v___x_464_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__49));
v___x_465_ = l_Lean_mkConst(v___x_464_, v___x_341_);
lean_inc_ref(v___x_349_);
v___x_466_ = l_Lean_mkAppB(v___x_465_, v_type_319_, v___x_349_);
v___x_467_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_463_, v___x_466_, v_a_324_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
lean_dec_ref_known(v___x_467_, 1);
v___x_468_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__51));
lean_inc_ref_n(v___x_341_, 2);
v___x_469_ = l_Lean_mkConst(v___x_468_, v___x_341_);
lean_inc_ref_n(v_type_319_, 2);
v___x_470_ = l_Lean_Expr_app___override(v___x_469_, v_type_319_);
v___x_471_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__53));
v___x_472_ = l_Lean_mkConst(v___x_471_, v___x_341_);
lean_inc_ref(v___x_349_);
v___x_473_ = l_Lean_mkAppB(v___x_472_, v_type_319_, v___x_349_);
v___x_474_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_470_, v___x_473_, v_a_324_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
lean_dec_ref_known(v___x_474_, 1);
v___x_475_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__55));
lean_inc_ref_n(v___x_341_, 2);
v___x_476_ = l_Lean_mkConst(v___x_475_, v___x_341_);
lean_inc_ref_n(v_type_319_, 2);
v___x_477_ = l_Lean_Expr_app___override(v___x_476_, v_type_319_);
v___x_478_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__57));
v___x_479_ = l_Lean_mkConst(v___x_478_, v___x_341_);
lean_inc_ref(v___x_346_);
v___x_480_ = l_Lean_mkAppB(v___x_479_, v_type_319_, v___x_346_);
v___x_481_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_477_, v___x_480_, v_a_324_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_toCold_482_; lean_object* v_inheritedTraceOptions_483_; lean_object* v___x_484_; lean_object* v___y_486_; lean_object* v___y_487_; lean_object* v___y_488_; lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v_options_492_; lean_object* v_inheritedTraceOptions_493_; lean_object* v___y_494_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_534_; lean_object* v_noZeroDivInst_x3f_535_; lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___y_538_; lean_object* v___y_539_; lean_object* v___y_540_; lean_object* v___y_541_; lean_object* v_val_552_; lean_object* v_charInst_x3f_553_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___y_583_; lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v___y_586_; lean_object* v___y_587_; lean_object* v___y_588_; lean_object* v___y_591_; lean_object* v___y_592_; lean_object* v___y_593_; lean_object* v___y_594_; lean_object* v___y_595_; lean_object* v___y_596_; lean_object* v___x_659_; lean_object* v_a_660_; uint8_t v___x_661_; 
lean_dec_ref_known(v___x_481_, 1);
v_toCold_482_ = lean_ctor_get(v_a_327_, 0);
v_inheritedTraceOptions_483_ = lean_ctor_get(v_toCold_482_, 11);
v___x_484_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__60));
v___x_659_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1(v___x_484_, v_inheritedTraceOptions_483_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_);
v_a_660_ = lean_ctor_get(v___x_659_, 0);
lean_inc(v_a_660_);
lean_dec_ref(v___x_659_);
v___x_661_ = lean_unbox(v_a_660_);
lean_dec(v_a_660_);
if (v___x_661_ == 0)
{
v___y_591_ = v_a_323_;
v___y_592_ = v_a_324_;
v___y_593_ = v_a_325_;
v___y_594_ = v_a_326_;
v___y_595_ = v_a_327_;
v___y_596_ = v_a_328_;
goto v___jp_590_;
}
else
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_662_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78);
lean_inc_ref(v_type_319_);
v___x_663_ = l_Lean_MessageData_ofExpr(v_type_319_);
v___x_664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_664_, 0, v___x_662_);
lean_ctor_set(v___x_664_, 1, v___x_663_);
v___x_665_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(v___x_484_, v___x_664_, v_a_325_, v_a_326_, v_a_327_, v_a_328_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_dec_ref_known(v___x_665_, 1);
v___y_591_ = v_a_323_;
v___y_592_ = v_a_324_;
v___y_593_ = v_a_325_;
v___y_594_ = v_a_326_;
v___y_595_ = v_a_327_;
v___y_596_ = v_a_328_;
goto v___jp_590_;
}
else
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_673_; 
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_666_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_673_ == 0)
{
v___x_668_ = v___x_665_;
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_665_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_666_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
v___jp_485_:
{
uint8_t v_hasTrace_495_; 
v_hasTrace_495_ = lean_ctor_get_uint8(v_options_492_, sizeof(void*)*1);
if (v_hasTrace_495_ == 0)
{
v___y_354_ = v___y_486_;
v___y_355_ = v___y_487_;
v___y_356_ = v___y_488_;
v___y_357_ = v___y_491_;
goto v___jp_353_;
}
else
{
lean_object* v___x_496_; uint8_t v___x_497_; 
v___x_496_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61);
v___x_497_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_493_, v_options_492_, v___x_496_);
if (v___x_497_ == 0)
{
v___y_354_ = v___y_486_;
v___y_355_ = v___y_487_;
v___y_356_ = v___y_488_;
v___y_357_ = v___y_491_;
goto v___jp_353_;
}
else
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__63, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__63_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__63);
v___x_499_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(v___x_484_, v___x_498_, v___y_489_, v___y_490_, v___y_491_, v___y_494_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_dec_ref_known(v___x_499_, 1);
v___y_354_ = v___y_486_;
v___y_355_ = v___y_487_;
v___y_356_ = v___y_488_;
v___y_357_ = v___y_491_;
goto v___jp_353_;
}
else
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_507_; 
lean_dec(v___y_487_);
lean_dec(v___y_486_);
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_type_319_);
v_a_500_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_507_ == 0)
{
v___x_502_ = v___x_499_;
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_499_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_505_; 
if (v_isShared_503_ == 0)
{
v___x_505_ = v___x_502_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_a_500_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
}
}
}
v___jp_508_:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
lean_inc_ref(v___y_517_);
v___x_518_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_518_, 0, v___y_517_);
v___x_519_ = l_Lean_MessageData_ofFormat(v___x_518_);
lean_inc_ref(v___y_516_);
v___x_520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_520_, 0, v___y_516_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(v___x_484_, v___x_520_, v___y_511_, v___y_514_, v___y_515_, v___y_509_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_toCold_522_; lean_object* v_options_523_; lean_object* v_inheritedTraceOptions_524_; 
lean_dec_ref_known(v___x_521_, 1);
v_toCold_522_ = lean_ctor_get(v___y_515_, 0);
v_options_523_ = lean_ctor_get(v_toCold_522_, 2);
v_inheritedTraceOptions_524_ = lean_ctor_get(v_toCold_522_, 11);
v___y_486_ = v___y_510_;
v___y_487_ = v___y_512_;
v___y_488_ = v___y_513_;
v___y_489_ = v___y_511_;
v___y_490_ = v___y_514_;
v___y_491_ = v___y_515_;
v_options_492_ = v_options_523_;
v_inheritedTraceOptions_493_ = v_inheritedTraceOptions_524_;
v___y_494_ = v___y_509_;
goto v___jp_485_;
}
else
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_532_; 
lean_dec(v___y_512_);
lean_dec(v___y_510_);
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_type_319_);
v_a_525_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_532_ == 0)
{
v___x_527_ = v___x_521_;
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_521_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_530_; 
if (v_isShared_528_ == 0)
{
v___x_530_ = v___x_527_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_a_525_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
v___jp_533_:
{
lean_object* v_toCold_542_; lean_object* v_options_543_; lean_object* v_inheritedTraceOptions_544_; lean_object* v___x_545_; lean_object* v_a_546_; uint8_t v___x_547_; 
v_toCold_542_ = lean_ctor_get(v___y_540_, 0);
v_options_543_ = lean_ctor_get(v_toCold_542_, 2);
v_inheritedTraceOptions_544_ = lean_ctor_get(v_toCold_542_, 11);
v___x_545_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1(v___x_484_, v_inheritedTraceOptions_544_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
v_a_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_a_546_);
lean_dec_ref(v___x_545_);
v___x_547_ = lean_unbox(v_a_546_);
lean_dec(v_a_546_);
if (v___x_547_ == 0)
{
v___y_486_ = v___y_534_;
v___y_487_ = v_noZeroDivInst_x3f_535_;
v___y_488_ = v___y_537_;
v___y_489_ = v___y_538_;
v___y_490_ = v___y_539_;
v___y_491_ = v___y_540_;
v_options_492_ = v_options_543_;
v_inheritedTraceOptions_493_ = v_inheritedTraceOptions_544_;
v___y_494_ = v___y_541_;
goto v___jp_485_;
}
else
{
lean_object* v___x_548_; 
v___x_548_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__65, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__65_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__65);
if (lean_obj_tag(v_noZeroDivInst_x3f_535_) == 0)
{
lean_object* v___x_549_; 
v___x_549_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__66));
v___y_509_ = v___y_541_;
v___y_510_ = v___y_534_;
v___y_511_ = v___y_538_;
v___y_512_ = v_noZeroDivInst_x3f_535_;
v___y_513_ = v___y_537_;
v___y_514_ = v___y_539_;
v___y_515_ = v___y_540_;
v___y_516_ = v___x_548_;
v___y_517_ = v___x_549_;
goto v___jp_508_;
}
else
{
lean_object* v___x_550_; 
v___x_550_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__67));
v___y_509_ = v___y_541_;
v___y_510_ = v___y_534_;
v___y_511_ = v___y_538_;
v___y_512_ = v_noZeroDivInst_x3f_535_;
v___y_513_ = v___y_537_;
v___y_514_ = v___y_539_;
v___y_515_ = v___y_540_;
v___y_516_ = v___x_548_;
v___y_517_ = v___x_550_;
goto v___jp_508_;
}
}
}
v___jp_551_:
{
lean_object* v___x_560_; 
lean_inc_ref(v_base_320_);
lean_inc(v_val_335_);
v___x_560_ = l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg(v_val_335_, v_base_320_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v_a_561_; 
v_a_561_ = lean_ctor_get(v___x_560_, 0);
lean_inc(v_a_561_);
lean_dec_ref_known(v___x_560_, 1);
if (lean_obj_tag(v_a_561_) == 1)
{
lean_object* v_val_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_572_; 
v_val_562_ = lean_ctor_get(v_a_561_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v_a_561_);
if (v_isSharedCheck_572_ == 0)
{
v___x_564_ = v_a_561_;
v_isShared_565_ = v_isSharedCheck_572_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_val_562_);
lean_dec(v_a_561_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_572_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_570_; 
v___x_566_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__70));
v___x_567_ = l_Lean_mkConst(v___x_566_, v___x_341_);
v___x_568_ = l_Lean_mkApp4(v___x_567_, v_base_320_, v_semiringInst_321_, v_val_552_, v_val_562_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 0, v___x_568_);
v___x_570_ = v___x_564_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_568_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
v___y_534_ = v_charInst_x3f_553_;
v_noZeroDivInst_x3f_535_ = v___x_570_;
v___y_536_ = v___y_554_;
v___y_537_ = v___y_555_;
v___y_538_ = v___y_556_;
v___y_539_ = v___y_557_;
v___y_540_ = v___y_558_;
v___y_541_ = v___y_559_;
goto v___jp_533_;
}
}
}
else
{
lean_object* v___x_573_; 
lean_dec(v_a_561_);
lean_dec_ref(v_val_552_);
lean_dec_ref_known(v___x_341_, 2);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
v___x_573_ = lean_box(0);
v___y_534_ = v_charInst_x3f_553_;
v_noZeroDivInst_x3f_535_ = v___x_573_;
v___y_536_ = v___y_554_;
v___y_537_ = v___y_555_;
v___y_538_ = v___y_556_;
v___y_539_ = v___y_557_;
v___y_540_ = v___y_558_;
v___y_541_ = v___y_559_;
goto v___jp_533_;
}
}
else
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_581_; 
lean_dec(v_charInst_x3f_553_);
lean_dec_ref(v_val_552_);
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_574_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_581_ == 0)
{
v___x_576_ = v___x_560_;
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v___x_560_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_579_; 
if (v_isShared_577_ == 0)
{
v___x_579_ = v___x_576_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_a_574_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
}
v___jp_582_:
{
lean_object* v___x_589_; 
v___x_589_ = lean_box(0);
v___y_534_ = v___x_589_;
v_noZeroDivInst_x3f_535_ = v___x_589_;
v___y_536_ = v___y_583_;
v___y_537_ = v___y_584_;
v___y_538_ = v___y_585_;
v___y_539_ = v___y_586_;
v___y_540_ = v___y_587_;
v___y_541_ = v___y_588_;
goto v___jp_533_;
}
v___jp_590_:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_597_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__72));
lean_inc_ref(v___x_341_);
v___x_598_ = l_Lean_mkConst(v___x_597_, v___x_341_);
lean_inc_ref(v_base_320_);
v___x_599_ = l_Lean_Expr_app___override(v___x_598_, v_base_320_);
v___x_600_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_599_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_a_601_);
lean_dec_ref_known(v___x_600_, 1);
if (lean_obj_tag(v_a_601_) == 1)
{
lean_object* v_val_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v_val_602_ = lean_ctor_get(v_a_601_, 0);
lean_inc(v_val_602_);
lean_dec_ref_known(v_a_601_, 1);
v___x_603_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__74));
lean_inc_ref(v___x_341_);
v___x_604_ = l_Lean_mkConst(v___x_603_, v___x_341_);
lean_inc_ref(v_base_320_);
v___x_605_ = l_Lean_mkAppB(v___x_604_, v_base_320_, v_val_602_);
v___x_606_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_605_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v_a_607_; 
v_a_607_ = lean_ctor_get(v___x_606_, 0);
lean_inc(v_a_607_);
lean_dec_ref_known(v___x_606_, 1);
if (lean_obj_tag(v_a_607_) == 1)
{
lean_object* v_val_608_; lean_object* v___x_609_; 
v_val_608_ = lean_ctor_get(v_a_607_, 0);
lean_inc(v_val_608_);
lean_dec_ref_known(v_a_607_, 1);
lean_inc_ref(v_semiringInst_321_);
lean_inc_ref(v_base_320_);
lean_inc(v_val_335_);
v___x_609_ = l_Lean_Meta_Sym_Arith_getIsCharInst_x3f(v_val_335_, v_base_320_, v_semiringInst_321_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v_a_610_; 
v_a_610_ = lean_ctor_get(v___x_609_, 0);
lean_inc(v_a_610_);
lean_dec_ref_known(v___x_609_, 1);
if (lean_obj_tag(v_a_610_) == 1)
{
lean_object* v_val_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_631_; 
v_val_611_ = lean_ctor_get(v_a_610_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v_a_610_);
if (v_isSharedCheck_631_ == 0)
{
v___x_613_ = v_a_610_;
v_isShared_614_ = v_isSharedCheck_631_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_val_611_);
lean_dec(v_a_610_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_631_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v_fst_615_; lean_object* v_snd_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_630_; 
v_fst_615_ = lean_ctor_get(v_val_611_, 0);
v_snd_616_ = lean_ctor_get(v_val_611_, 1);
v_isSharedCheck_630_ = !lean_is_exclusive(v_val_611_);
if (v_isSharedCheck_630_ == 0)
{
v___x_618_ = v_val_611_;
v_isShared_619_ = v_isSharedCheck_630_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_snd_616_);
lean_inc(v_fst_615_);
lean_dec(v_val_611_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_630_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_625_; 
v___x_620_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__76));
lean_inc_ref(v___x_341_);
v___x_621_ = l_Lean_mkConst(v___x_620_, v___x_341_);
lean_inc(v_snd_616_);
v___x_622_ = l_Lean_mkRawNatLit(v_snd_616_);
lean_inc(v_val_608_);
lean_inc_ref(v_semiringInst_321_);
lean_inc_ref(v_base_320_);
v___x_623_ = l_Lean_mkApp5(v___x_621_, v_base_320_, v___x_622_, v_semiringInst_321_, v_val_608_, v_fst_615_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v___x_623_);
v___x_625_ = v___x_618_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v_snd_616_);
v___x_625_ = v_reuseFailAlloc_629_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
lean_object* v___x_627_; 
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_625_);
v___x_627_ = v___x_613_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_625_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
v_val_552_ = v_val_608_;
v_charInst_x3f_553_ = v___x_627_;
v___y_554_ = v___y_591_;
v___y_555_ = v___y_592_;
v___y_556_ = v___y_593_;
v___y_557_ = v___y_594_;
v___y_558_ = v___y_595_;
v___y_559_ = v___y_596_;
goto v___jp_551_;
}
}
}
}
}
else
{
lean_object* v___x_632_; 
lean_dec(v_a_610_);
v___x_632_ = lean_box(0);
v_val_552_ = v_val_608_;
v_charInst_x3f_553_ = v___x_632_;
v___y_554_ = v___y_591_;
v___y_555_ = v___y_592_;
v___y_556_ = v___y_593_;
v___y_557_ = v___y_594_;
v___y_558_ = v___y_595_;
v___y_559_ = v___y_596_;
goto v___jp_551_;
}
}
else
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_640_; 
lean_dec(v_val_608_);
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_633_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_640_ == 0)
{
v___x_635_ = v___x_609_;
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_609_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_a_633_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
else
{
if (lean_obj_tag(v_a_607_) == 1)
{
lean_object* v_val_641_; lean_object* v___x_642_; 
v_val_641_ = lean_ctor_get(v_a_607_, 0);
lean_inc(v_val_641_);
lean_dec_ref_known(v_a_607_, 1);
v___x_642_ = lean_box(0);
v_val_552_ = v_val_641_;
v_charInst_x3f_553_ = v___x_642_;
v___y_554_ = v___y_591_;
v___y_555_ = v___y_592_;
v___y_556_ = v___y_593_;
v___y_557_ = v___y_594_;
v___y_558_ = v___y_595_;
v___y_559_ = v___y_596_;
goto v___jp_551_;
}
else
{
lean_dec(v_a_607_);
lean_dec_ref_known(v___x_341_, 2);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
v___y_583_ = v___y_591_;
v___y_584_ = v___y_592_;
v___y_585_ = v___y_593_;
v___y_586_ = v___y_594_;
v___y_587_ = v___y_595_;
v___y_588_ = v___y_596_;
goto v___jp_582_;
}
}
}
else
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_643_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_650_ == 0)
{
v___x_645_ = v___x_606_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_606_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_643_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
else
{
lean_dec(v_a_601_);
lean_dec_ref_known(v___x_341_, 2);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
v___y_583_ = v___y_591_;
v___y_584_ = v___y_592_;
v___y_585_ = v___y_593_;
v___y_586_ = v___y_594_;
v___y_587_ = v___y_595_;
v___y_588_ = v___y_596_;
goto v___jp_582_;
}
}
else
{
lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_658_; 
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_651_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_658_ == 0)
{
v___x_653_ = v___x_600_;
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v___x_600_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_656_; 
if (v_isShared_654_ == 0)
{
v___x_656_ = v___x_653_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_a_651_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
}
else
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_674_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_681_ == 0)
{
v___x_676_ = v___x_481_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_481_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_a_674_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
else
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_682_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_474_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_474_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_a_682_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
else
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_690_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_467_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_467_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
else
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_698_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v___x_456_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_456_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_698_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
else
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_706_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___x_449_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_449_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
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
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_706_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
else
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
lean_dec_ref_known(v___x_420_, 2);
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_714_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v___x_439_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_439_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_a_714_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
else
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
lean_dec_ref_known(v___x_420_, 2);
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_722_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_429_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_429_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
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
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_730_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_417_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_417_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_738_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_410_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_410_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
else
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_746_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_406_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_406_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_a_746_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
else
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_754_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_402_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_402_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
else
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_762_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___x_398_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_398_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
if (v_isShared_765_ == 0)
{
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_762_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
v___jp_353_:
{
lean_object* v___x_358_; 
v___x_358_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v___y_356_, v___y_357_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_object* v_a_359_; lean_object* v_rings_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___f_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v_a_359_ = lean_ctor_get(v___x_358_, 0);
lean_inc(v_a_359_);
lean_dec_ref_known(v___x_358_, 1);
v_rings_360_ = lean_ctor_get(v_a_359_, 1);
lean_inc_ref(v_rings_360_);
lean_dec(v_a_359_);
v___x_361_ = lean_array_get_size(v_rings_360_);
lean_dec_ref(v_rings_360_);
v___x_362_ = lean_box(0);
v___x_363_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v___x_363_, 0, v___x_361_);
lean_ctor_set(v___x_363_, 1, v_type_319_);
lean_ctor_set(v___x_363_, 2, v_val_335_);
lean_ctor_set(v___x_363_, 3, v___x_346_);
lean_ctor_set(v___x_363_, 4, v___x_349_);
lean_ctor_set(v___x_363_, 5, v___y_354_);
lean_ctor_set(v___x_363_, 6, v___x_362_);
lean_ctor_set(v___x_363_, 7, v___x_362_);
lean_ctor_set(v___x_363_, 8, v___x_362_);
lean_ctor_set(v___x_363_, 9, v___x_362_);
lean_ctor_set(v___x_363_, 10, v___x_362_);
lean_ctor_set(v___x_363_, 11, v___x_362_);
lean_ctor_set(v___x_363_, 12, v___x_362_);
lean_ctor_set(v___x_363_, 13, v___x_362_);
lean_ctor_set(v___x_363_, 14, v___x_362_);
lean_ctor_set(v___x_363_, 15, v___x_362_);
v___x_364_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
lean_ctor_set(v___x_364_, 1, v___x_362_);
lean_ctor_set(v___x_364_, 2, v___x_362_);
lean_ctor_set(v___x_364_, 3, v___x_362_);
lean_ctor_set(v___x_364_, 4, v___x_352_);
lean_ctor_set(v___x_364_, 5, v___x_343_);
lean_ctor_set(v___x_364_, 6, v___y_355_);
lean_ctor_set(v___x_364_, 7, v___x_362_);
lean_ctor_set(v___x_364_, 8, v___x_362_);
v___f_365_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__0), 2, 1);
lean_closure_set(v___f_365_, 0, v___x_364_);
v___x_366_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_367_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_366_, v___f_365_, v___y_356_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_377_; 
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_377_ == 0)
{
lean_object* v_unused_378_; 
v_unused_378_ = lean_ctor_get(v___x_367_, 0);
lean_dec(v_unused_378_);
v___x_369_ = v___x_367_;
v_isShared_370_ = v_isSharedCheck_377_;
goto v_resetjp_368_;
}
else
{
lean_dec(v___x_367_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_377_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_372_; 
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 0, v___x_361_);
v___x_372_ = v___x_337_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_361_);
v___x_372_ = v_reuseFailAlloc_376_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
lean_object* v___x_374_; 
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 0, v___x_372_);
v___x_374_ = v___x_369_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_372_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
else
{
lean_object* v_a_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_386_; 
lean_del_object(v___x_337_);
v_a_379_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_386_ == 0)
{
v___x_381_ = v___x_367_;
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_a_379_);
lean_dec(v___x_367_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_384_; 
if (v_isShared_382_ == 0)
{
v___x_384_ = v___x_381_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_a_379_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
}
else
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_394_; 
lean_dec(v___y_355_);
lean_dec(v___y_354_);
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_type_319_);
v_a_387_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_394_ == 0)
{
v___x_389_ = v___x_358_;
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_358_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_392_; 
if (v_isShared_390_ == 0)
{
v___x_392_ = v___x_389_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_387_);
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
}
}
else
{
lean_object* v___x_771_; lean_object* v___x_773_; 
lean_dec(v_a_331_);
lean_dec_ref(v_commSemiringInst_322_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v___x_771_ = lean_box(0);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v___x_771_);
v___x_773_ = v___x_333_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_771_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
else
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
lean_dec_ref(v_commSemiringInst_322_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_776_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_330_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_330_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_776_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___boxed(lean_object* v_type_784_, lean_object* v_base_785_, lean_object* v_semiringInst_786_, lean_object* v_commSemiringInst_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f(v_type_784_, v_base_785_, v_semiringInst_786_, v_commSemiringInst_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_);
lean_dec(v_a_793_);
lean_dec_ref(v_a_792_);
lean_dec(v_a_791_);
lean_dec_ref(v_a_790_);
lean_dec(v_a_789_);
lean_dec_ref(v_a_788_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0(lean_object* v_cls_796_, lean_object* v_msg_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(v_cls_796_, v_msg_797_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___boxed(lean_object* v_cls_806_, lean_object* v_msg_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0(v_cls_806_, v_msg_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
return v_res_815_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__3(void){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__2));
v___x_823_ = l_Lean_stringToMessageData(v___x_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f(lean_object* v_type_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_){
_start:
{
lean_object* v___x_832_; 
lean_inc_ref(v_type_824_);
v___x_832_ = l_Lean_Meta_getDecLevel_x3f(v_type_824_, v_a_827_, v_a_828_, v_a_829_, v_a_830_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_1071_; 
v_a_833_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_835_ = v___x_832_;
v_isShared_836_ = v_isSharedCheck_1071_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_832_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_1071_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
if (lean_obj_tag(v_a_833_) == 1)
{
lean_object* v_val_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_1066_; 
lean_del_object(v___x_835_);
v_val_837_ = lean_ctor_get(v_a_833_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v_a_833_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_839_ = v_a_833_;
v_isShared_840_ = v_isSharedCheck_1066_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_val_837_);
lean_dec(v_a_833_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_1066_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_841_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__13));
v___x_842_ = lean_box(0);
lean_inc(v_val_837_);
v___x_843_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_843_, 0, v_val_837_);
lean_ctor_set(v___x_843_, 1, v___x_842_);
lean_inc_ref(v___x_843_);
v___x_844_ = l_Lean_mkConst(v___x_841_, v___x_843_);
lean_inc_ref(v_type_824_);
v___x_845_ = l_Lean_Expr_app___override(v___x_844_, v_type_824_);
v___x_846_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_845_, v_a_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_1057_; 
v_a_847_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_849_ = v___x_846_;
v_isShared_850_ = v_isSharedCheck_1057_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_846_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_1057_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
if (lean_obj_tag(v_a_847_) == 1)
{
lean_object* v_val_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_1052_; 
lean_del_object(v___x_849_);
v_val_851_ = lean_ctor_get(v_a_847_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v_a_847_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_853_ = v_a_847_;
v_isShared_854_ = v_isSharedCheck_1052_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_val_851_);
lean_dec(v_a_847_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_1052_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v_toCold_858_; lean_object* v_inheritedTraceOptions_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___x_910_; lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v___y_914_; lean_object* v___y_915_; lean_object* v___y_916_; lean_object* v___y_917_; lean_object* v___y_918_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___y_938_; lean_object* v___y_939_; lean_object* v___y_940_; lean_object* v___y_941_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v___y_944_; lean_object* v___y_945_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_986_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1006_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v___x_1037_; lean_object* v_a_1038_; uint8_t v___x_1039_; 
v___x_855_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__7));
lean_inc_ref_n(v___x_843_, 3);
v___x_856_ = l_Lean_mkConst(v___x_855_, v___x_843_);
lean_inc(v_val_851_);
lean_inc_ref_n(v_type_824_, 3);
v___x_857_ = l_Lean_mkAppB(v___x_856_, v_type_824_, v_val_851_);
v_toCold_858_ = lean_ctor_get(v_a_829_, 0);
v_inheritedTraceOptions_859_ = lean_ctor_get(v_toCold_858_, 11);
v___x_860_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__10));
v___x_861_ = l_Lean_mkConst(v___x_860_, v___x_843_);
lean_inc_ref(v___x_857_);
v___x_862_ = l_Lean_mkAppB(v___x_861_, v_type_824_, v___x_857_);
v___x_863_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__12));
v___x_864_ = l_Lean_mkConst(v___x_863_, v___x_843_);
lean_inc_ref(v___x_862_);
v___x_865_ = l_Lean_mkAppB(v___x_864_, v_type_824_, v___x_862_);
v___x_910_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__60));
v___x_1037_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1(v___x_910_, v_inheritedTraceOptions_859_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_);
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_a_1038_);
lean_dec_ref(v___x_1037_);
v___x_1039_ = lean_unbox(v_a_1038_);
lean_dec(v_a_1038_);
if (v___x_1039_ == 0)
{
v___y_1003_ = v_a_825_;
v___y_1004_ = v_a_826_;
v___y_1005_ = v_a_827_;
v___y_1006_ = v_a_828_;
v___y_1007_ = v_a_829_;
v___y_1008_ = v_a_830_;
goto v___jp_1002_;
}
else
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1040_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78);
lean_inc_ref(v_type_824_);
v___x_1041_ = l_Lean_MessageData_ofExpr(v_type_824_);
v___x_1042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1040_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
v___x_1043_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(v___x_910_, v___x_1042_, v_a_827_, v_a_828_, v_a_829_, v_a_830_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_dec_ref_known(v___x_1043_, 1);
v___y_1003_ = v_a_825_;
v___y_1004_ = v_a_826_;
v___y_1005_ = v_a_827_;
v___y_1006_ = v_a_828_;
v___y_1007_ = v_a_829_;
v___y_1008_ = v_a_830_;
goto v___jp_1002_;
}
else
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1051_; 
lean_dec_ref(v___x_865_);
lean_dec_ref(v___x_862_);
lean_dec_ref(v___x_857_);
lean_del_object(v___x_853_);
lean_dec(v_val_851_);
lean_dec_ref_known(v___x_843_, 2);
lean_del_object(v___x_839_);
lean_dec(v_val_837_);
lean_dec_ref(v_type_824_);
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1046_ = v___x_1043_;
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1043_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
if (v_isShared_1047_ == 0)
{
v___x_1049_ = v___x_1046_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_a_1044_);
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
v___jp_866_:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = lean_box(0);
v___x_874_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v___y_871_, v___y_872_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; lean_object* v_rings_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___f_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_a_875_);
lean_dec_ref_known(v___x_874_, 1);
v_rings_876_ = lean_ctor_get(v_a_875_, 1);
lean_inc_ref(v_rings_876_);
lean_dec(v_a_875_);
v___x_877_ = lean_array_get_size(v_rings_876_);
lean_dec_ref(v_rings_876_);
v___x_878_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
lean_ctor_set(v___x_878_, 1, v_type_824_);
lean_ctor_set(v___x_878_, 2, v_val_837_);
lean_ctor_set(v___x_878_, 3, v___x_857_);
lean_ctor_set(v___x_878_, 4, v___x_862_);
lean_ctor_set(v___x_878_, 5, v___y_867_);
lean_ctor_set(v___x_878_, 6, v___x_873_);
lean_ctor_set(v___x_878_, 7, v___x_873_);
lean_ctor_set(v___x_878_, 8, v___x_873_);
lean_ctor_set(v___x_878_, 9, v___x_873_);
lean_ctor_set(v___x_878_, 10, v___x_873_);
lean_ctor_set(v___x_878_, 11, v___x_873_);
lean_ctor_set(v___x_878_, 12, v___x_873_);
lean_ctor_set(v___x_878_, 13, v___x_873_);
lean_ctor_set(v___x_878_, 14, v___x_873_);
lean_ctor_set(v___x_878_, 15, v___x_873_);
v___x_879_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
lean_ctor_set(v___x_879_, 1, v___x_873_);
lean_ctor_set(v___x_879_, 2, v___x_873_);
lean_ctor_set(v___x_879_, 3, v___x_873_);
lean_ctor_set(v___x_879_, 4, v___x_865_);
lean_ctor_set(v___x_879_, 5, v_val_851_);
lean_ctor_set(v___x_879_, 6, v___y_869_);
lean_ctor_set(v___x_879_, 7, v___y_868_);
lean_ctor_set(v___x_879_, 8, v___y_870_);
v___f_880_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__0), 2, 1);
lean_closure_set(v___f_880_, 0, v___x_879_);
v___x_881_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_882_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_881_, v___f_880_, v___y_871_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_892_; 
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_892_ == 0)
{
lean_object* v_unused_893_; 
v_unused_893_ = lean_ctor_get(v___x_882_, 0);
lean_dec(v_unused_893_);
v___x_884_ = v___x_882_;
v_isShared_885_ = v_isSharedCheck_892_;
goto v_resetjp_883_;
}
else
{
lean_dec(v___x_882_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_892_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_887_; 
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v___x_877_);
v___x_887_ = v___x_853_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_877_);
v___x_887_ = v_reuseFailAlloc_891_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
lean_object* v___x_889_; 
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 0, v___x_887_);
v___x_889_ = v___x_884_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_887_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
else
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
lean_del_object(v___x_853_);
v_a_894_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_901_ == 0)
{
v___x_896_ = v___x_882_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_882_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_897_ == 0)
{
v___x_899_ = v___x_896_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_894_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
else
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
lean_dec(v___y_870_);
lean_dec(v___y_869_);
lean_dec(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v___x_865_);
lean_dec_ref(v___x_862_);
lean_dec_ref(v___x_857_);
lean_del_object(v___x_853_);
lean_dec(v_val_851_);
lean_dec(v_val_837_);
lean_dec_ref(v_type_824_);
v_a_902_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_874_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_874_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
v___jp_911_:
{
lean_object* v___x_924_; 
lean_inc_ref(v___y_922_);
if (v_isShared_840_ == 0)
{
lean_ctor_set_tag(v___x_839_, 3);
lean_ctor_set(v___x_839_, 0, v___y_922_);
v___x_924_ = v___x_839_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v___y_922_);
v___x_924_ = v_reuseFailAlloc_936_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_925_ = l_Lean_MessageData_ofFormat(v___x_924_);
lean_inc_ref(v___y_914_);
v___x_926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_926_, 0, v___y_914_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
v___x_927_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(v___x_910_, v___x_926_, v___y_919_, v___y_916_, v___y_918_, v___y_912_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_dec_ref_known(v___x_927_, 1);
v___y_867_ = v___y_913_;
v___y_868_ = v___y_915_;
v___y_869_ = v___y_920_;
v___y_870_ = v___y_921_;
v___y_871_ = v___y_917_;
v___y_872_ = v___y_918_;
goto v___jp_866_;
}
else
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_935_; 
lean_dec(v___y_921_);
lean_dec(v___y_920_);
lean_dec(v___y_915_);
lean_dec(v___y_913_);
lean_dec_ref(v___x_865_);
lean_dec_ref(v___x_862_);
lean_dec_ref(v___x_857_);
lean_del_object(v___x_853_);
lean_dec(v_val_851_);
lean_dec(v_val_837_);
lean_dec_ref(v_type_824_);
v_a_928_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_935_ == 0)
{
v___x_930_ = v___x_927_;
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_927_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_928_);
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
}
v___jp_937_:
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_946_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__1));
v___x_947_ = l_Lean_mkConst(v___x_946_, v___x_843_);
lean_inc_ref(v_type_824_);
v___x_948_ = l_Lean_Expr_app___override(v___x_947_, v_type_824_);
v___x_949_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_948_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; lean_object* v___x_951_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_a_950_);
lean_dec_ref_known(v___x_949_, 1);
lean_inc_ref(v_type_824_);
lean_inc(v_val_837_);
v___x_951_ = l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f(v_val_837_, v_type_824_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_toCold_952_; lean_object* v_options_953_; uint8_t v_hasTrace_954_; 
v_toCold_952_ = lean_ctor_get(v___y_944_, 0);
v_options_953_ = lean_ctor_get(v_toCold_952_, 2);
v_hasTrace_954_ = lean_ctor_get_uint8(v_options_953_, sizeof(void*)*1);
if (v_hasTrace_954_ == 0)
{
lean_object* v_a_955_; 
lean_del_object(v___x_839_);
v_a_955_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_a_955_);
lean_dec_ref_known(v___x_951_, 1);
v___y_867_ = v___y_938_;
v___y_868_ = v_a_950_;
v___y_869_ = v___y_939_;
v___y_870_ = v_a_955_;
v___y_871_ = v___y_941_;
v___y_872_ = v___y_944_;
goto v___jp_866_;
}
else
{
lean_object* v_a_956_; lean_object* v_inheritedTraceOptions_957_; lean_object* v___x_958_; uint8_t v___x_959_; 
v_a_956_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_a_956_);
lean_dec_ref_known(v___x_951_, 1);
v_inheritedTraceOptions_957_ = lean_ctor_get(v_toCold_952_, 11);
v___x_958_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61);
v___x_959_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_957_, v_options_953_, v___x_958_);
if (v___x_959_ == 0)
{
lean_del_object(v___x_839_);
v___y_867_ = v___y_938_;
v___y_868_ = v_a_950_;
v___y_869_ = v___y_939_;
v___y_870_ = v_a_956_;
v___y_871_ = v___y_941_;
v___y_872_ = v___y_944_;
goto v___jp_866_;
}
else
{
lean_object* v___x_960_; 
v___x_960_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__3, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__3_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__3);
if (lean_obj_tag(v_a_956_) == 0)
{
lean_object* v___x_961_; 
v___x_961_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__66));
v___y_912_ = v___y_945_;
v___y_913_ = v___y_938_;
v___y_914_ = v___x_960_;
v___y_915_ = v_a_950_;
v___y_916_ = v___y_943_;
v___y_917_ = v___y_941_;
v___y_918_ = v___y_944_;
v___y_919_ = v___y_942_;
v___y_920_ = v___y_939_;
v___y_921_ = v_a_956_;
v___y_922_ = v___x_961_;
goto v___jp_911_;
}
else
{
lean_object* v___x_962_; 
v___x_962_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__67));
v___y_912_ = v___y_945_;
v___y_913_ = v___y_938_;
v___y_914_ = v___x_960_;
v___y_915_ = v_a_950_;
v___y_916_ = v___y_943_;
v___y_917_ = v___y_941_;
v___y_918_ = v___y_944_;
v___y_919_ = v___y_942_;
v___y_920_ = v___y_939_;
v___y_921_ = v_a_956_;
v___y_922_ = v___x_962_;
goto v___jp_911_;
}
}
}
}
else
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_970_; 
lean_dec(v_a_950_);
lean_dec(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___x_865_);
lean_dec_ref(v___x_862_);
lean_dec_ref(v___x_857_);
lean_del_object(v___x_853_);
lean_dec(v_val_851_);
lean_del_object(v___x_839_);
lean_dec(v_val_837_);
lean_dec_ref(v_type_824_);
v_a_963_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_970_ == 0)
{
v___x_965_ = v___x_951_;
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_951_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_968_; 
if (v_isShared_966_ == 0)
{
v___x_968_ = v___x_965_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_a_963_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
else
{
lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_978_; 
lean_dec(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___x_865_);
lean_dec_ref(v___x_862_);
lean_dec_ref(v___x_857_);
lean_del_object(v___x_853_);
lean_dec(v_val_851_);
lean_del_object(v___x_839_);
lean_dec(v_val_837_);
lean_dec_ref(v_type_824_);
v_a_971_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_978_ == 0)
{
v___x_973_ = v___x_949_;
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_949_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_976_; 
if (v_isShared_974_ == 0)
{
v___x_976_ = v___x_973_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_a_971_);
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
v___jp_979_:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
lean_inc_ref(v___y_989_);
v___x_990_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_990_, 0, v___y_989_);
v___x_991_ = l_Lean_MessageData_ofFormat(v___x_990_);
lean_inc_ref(v___y_983_);
v___x_992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_992_, 0, v___y_983_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(v___x_910_, v___x_992_, v___y_986_, v___y_982_, v___y_985_, v___y_988_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_dec_ref_known(v___x_993_, 1);
v___y_938_ = v___y_980_;
v___y_939_ = v___y_987_;
v___y_940_ = v___y_984_;
v___y_941_ = v___y_981_;
v___y_942_ = v___y_986_;
v___y_943_ = v___y_982_;
v___y_944_ = v___y_985_;
v___y_945_ = v___y_988_;
goto v___jp_937_;
}
else
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1001_; 
lean_dec(v___y_987_);
lean_dec(v___y_980_);
lean_dec_ref(v___x_865_);
lean_dec_ref(v___x_862_);
lean_dec_ref(v___x_857_);
lean_del_object(v___x_853_);
lean_dec(v_val_851_);
lean_dec_ref_known(v___x_843_, 2);
lean_del_object(v___x_839_);
lean_dec(v_val_837_);
lean_dec_ref(v_type_824_);
v_a_994_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_996_ = v___x_993_;
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_993_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_999_; 
if (v_isShared_997_ == 0)
{
v___x_999_ = v___x_996_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_a_994_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
v___jp_1002_:
{
lean_object* v___x_1009_; 
lean_inc_ref(v___x_862_);
lean_inc_ref(v_type_824_);
lean_inc(v_val_837_);
v___x_1009_ = l_Lean_Meta_Sym_Arith_getIsCharInst_x3f(v_val_837_, v_type_824_, v___x_862_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_a_1010_; lean_object* v___x_1011_; 
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
lean_inc(v_a_1010_);
lean_dec_ref_known(v___x_1009_, 1);
lean_inc_ref(v_type_824_);
lean_inc(v_val_837_);
v___x_1011_ = l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg(v_val_837_, v_type_824_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_toCold_1012_; lean_object* v_a_1013_; lean_object* v_inheritedTraceOptions_1014_; lean_object* v___x_1015_; lean_object* v_a_1016_; uint8_t v___x_1017_; 
v_toCold_1012_ = lean_ctor_get(v___y_1007_, 0);
v_a_1013_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_a_1013_);
lean_dec_ref_known(v___x_1011_, 1);
v_inheritedTraceOptions_1014_ = lean_ctor_get(v_toCold_1012_, 11);
v___x_1015_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1(v___x_910_, v_inheritedTraceOptions_1014_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_a_1016_);
lean_dec_ref(v___x_1015_);
v___x_1017_ = lean_unbox(v_a_1016_);
lean_dec(v_a_1016_);
if (v___x_1017_ == 0)
{
v___y_938_ = v_a_1010_;
v___y_939_ = v_a_1013_;
v___y_940_ = v___y_1003_;
v___y_941_ = v___y_1004_;
v___y_942_ = v___y_1005_;
v___y_943_ = v___y_1006_;
v___y_944_ = v___y_1007_;
v___y_945_ = v___y_1008_;
goto v___jp_937_;
}
else
{
lean_object* v___x_1018_; 
v___x_1018_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__65, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__65_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__65);
if (lean_obj_tag(v_a_1013_) == 0)
{
lean_object* v___x_1019_; 
v___x_1019_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__66));
v___y_980_ = v_a_1010_;
v___y_981_ = v___y_1004_;
v___y_982_ = v___y_1006_;
v___y_983_ = v___x_1018_;
v___y_984_ = v___y_1003_;
v___y_985_ = v___y_1007_;
v___y_986_ = v___y_1005_;
v___y_987_ = v_a_1013_;
v___y_988_ = v___y_1008_;
v___y_989_ = v___x_1019_;
goto v___jp_979_;
}
else
{
lean_object* v___x_1020_; 
v___x_1020_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__67));
v___y_980_ = v_a_1010_;
v___y_981_ = v___y_1004_;
v___y_982_ = v___y_1006_;
v___y_983_ = v___x_1018_;
v___y_984_ = v___y_1003_;
v___y_985_ = v___y_1007_;
v___y_986_ = v___y_1005_;
v___y_987_ = v_a_1013_;
v___y_988_ = v___y_1008_;
v___y_989_ = v___x_1020_;
goto v___jp_979_;
}
}
}
else
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1028_; 
lean_dec(v_a_1010_);
lean_dec_ref(v___x_865_);
lean_dec_ref(v___x_862_);
lean_dec_ref(v___x_857_);
lean_del_object(v___x_853_);
lean_dec(v_val_851_);
lean_dec_ref_known(v___x_843_, 2);
lean_del_object(v___x_839_);
lean_dec(v_val_837_);
lean_dec_ref(v_type_824_);
v_a_1021_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1023_ = v___x_1011_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_1011_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1021_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
else
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1036_; 
lean_dec_ref(v___x_865_);
lean_dec_ref(v___x_862_);
lean_dec_ref(v___x_857_);
lean_del_object(v___x_853_);
lean_dec(v_val_851_);
lean_dec_ref_known(v___x_843_, 2);
lean_del_object(v___x_839_);
lean_dec(v_val_837_);
lean_dec_ref(v_type_824_);
v_a_1029_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1031_ = v___x_1009_;
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_1009_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1034_; 
if (v_isShared_1032_ == 0)
{
v___x_1034_ = v___x_1031_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_a_1029_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
}
}
}
else
{
lean_object* v___x_1053_; lean_object* v___x_1055_; 
lean_dec(v_a_847_);
lean_dec_ref_known(v___x_843_, 2);
lean_del_object(v___x_839_);
lean_dec(v_val_837_);
lean_dec_ref(v_type_824_);
v___x_1053_ = lean_box(0);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 0, v___x_1053_);
v___x_1055_ = v___x_849_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1053_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
else
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
lean_dec_ref_known(v___x_843_, 2);
lean_del_object(v___x_839_);
lean_dec(v_val_837_);
lean_dec_ref(v_type_824_);
v_a_1058_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1060_ = v___x_846_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_846_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1061_ == 0)
{
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_a_1058_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
}
else
{
lean_object* v___x_1067_; lean_object* v___x_1069_; 
lean_dec(v_a_833_);
lean_dec_ref(v_type_824_);
v___x_1067_ = lean_box(0);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 0, v___x_1067_);
v___x_1069_ = v___x_835_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1067_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
else
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1079_; 
lean_dec_ref(v_type_824_);
v_a_1072_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1074_ = v___x_832_;
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_832_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
if (v_isShared_1075_ == 0)
{
v___x_1077_ = v___x_1074_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_a_1072_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___boxed(lean_object* v_type_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f(v_type_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
lean_dec(v_a_1086_);
lean_dec_ref(v_a_1085_);
lean_dec(v_a_1084_);
lean_dec_ref(v_a_1083_);
lean_dec(v_a_1082_);
lean_dec_ref(v_a_1081_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f(lean_object* v_type_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_){
_start:
{
lean_object* v___x_1109_; uint8_t v___x_1110_; 
lean_inc_ref(v_type_1101_);
v___x_1109_ = l_Lean_Expr_cleanupAnnotations(v_type_1101_);
v___x_1110_ = l_Lean_Expr_isApp(v___x_1109_);
if (v___x_1110_ == 0)
{
lean_object* v___x_1111_; 
lean_dec_ref(v___x_1109_);
v___x_1111_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f(v_type_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_);
return v___x_1111_;
}
else
{
lean_object* v_arg_1112_; lean_object* v___x_1113_; uint8_t v___x_1114_; 
v_arg_1112_ = lean_ctor_get(v___x_1109_, 1);
lean_inc_ref(v_arg_1112_);
v___x_1113_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1109_);
v___x_1114_ = l_Lean_Expr_isApp(v___x_1113_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; 
lean_dec_ref(v___x_1113_);
lean_dec_ref(v_arg_1112_);
v___x_1115_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f(v_type_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_);
return v___x_1115_;
}
else
{
lean_object* v_arg_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; uint8_t v___x_1119_; 
v_arg_1116_ = lean_ctor_get(v___x_1113_, 1);
lean_inc_ref(v_arg_1116_);
v___x_1117_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1113_);
v___x_1118_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1));
v___x_1119_ = l_Lean_Expr_isConstOf(v___x_1117_, v___x_1118_);
lean_dec_ref(v___x_1117_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1120_; 
lean_dec_ref(v_arg_1116_);
lean_dec_ref(v_arg_1112_);
v___x_1120_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f(v_type_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_);
return v___x_1120_;
}
else
{
lean_object* v___x_1121_; uint8_t v___x_1122_; 
lean_inc_ref(v_arg_1112_);
v___x_1121_ = l_Lean_Expr_cleanupAnnotations(v_arg_1112_);
v___x_1122_ = l_Lean_Expr_isApp(v___x_1121_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1123_; 
lean_dec_ref(v___x_1121_);
lean_dec_ref(v_arg_1116_);
lean_dec_ref(v_arg_1112_);
v___x_1123_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f(v_type_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_);
return v___x_1123_;
}
else
{
lean_object* v_arg_1124_; lean_object* v___x_1125_; uint8_t v___x_1126_; 
v_arg_1124_ = lean_ctor_get(v___x_1121_, 1);
lean_inc_ref(v_arg_1124_);
v___x_1125_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1121_);
v___x_1126_ = l_Lean_Expr_isApp(v___x_1125_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1127_; 
lean_dec_ref(v___x_1125_);
lean_dec_ref(v_arg_1124_);
lean_dec_ref(v_arg_1116_);
lean_dec_ref(v_arg_1112_);
v___x_1127_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f(v_type_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_);
return v___x_1127_;
}
else
{
lean_object* v___x_1128_; lean_object* v___x_1129_; uint8_t v___x_1130_; 
v___x_1128_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1125_);
v___x_1129_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2));
v___x_1130_ = l_Lean_Expr_isConstOf(v___x_1128_, v___x_1129_);
lean_dec_ref(v___x_1128_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1131_; 
lean_dec_ref(v_arg_1124_);
lean_dec_ref(v_arg_1116_);
lean_dec_ref(v_arg_1112_);
v___x_1131_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f(v_type_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_);
return v___x_1131_;
}
else
{
lean_object* v___x_1132_; 
v___x_1132_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f(v_type_1101_, v_arg_1116_, v_arg_1112_, v_arg_1124_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_);
return v___x_1132_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___boxed(lean_object* v_type_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f(v_type_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_);
lean_dec(v_a_1139_);
lean_dec_ref(v_a_1138_);
lean_dec(v_a_1137_);
lean_dec_ref(v_a_1136_);
lean_dec(v_a_1135_);
lean_dec_ref(v_a_1134_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___lam__0(lean_object* v___x_1142_, lean_object* v_s_1143_){
_start:
{
lean_object* v_exp_1144_; lean_object* v_rings_1145_; lean_object* v_semirings_1146_; lean_object* v_ncRings_1147_; lean_object* v_ncSemirings_1148_; lean_object* v_typeClassify_1149_; lean_object* v_orders_1150_; lean_object* v_typeOrderClassify_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1159_; 
v_exp_1144_ = lean_ctor_get(v_s_1143_, 0);
v_rings_1145_ = lean_ctor_get(v_s_1143_, 1);
v_semirings_1146_ = lean_ctor_get(v_s_1143_, 2);
v_ncRings_1147_ = lean_ctor_get(v_s_1143_, 3);
v_ncSemirings_1148_ = lean_ctor_get(v_s_1143_, 4);
v_typeClassify_1149_ = lean_ctor_get(v_s_1143_, 5);
v_orders_1150_ = lean_ctor_get(v_s_1143_, 6);
v_typeOrderClassify_1151_ = lean_ctor_get(v_s_1143_, 7);
v_isSharedCheck_1159_ = !lean_is_exclusive(v_s_1143_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1153_ = v_s_1143_;
v_isShared_1154_ = v_isSharedCheck_1159_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_typeOrderClassify_1151_);
lean_inc(v_orders_1150_);
lean_inc(v_typeClassify_1149_);
lean_inc(v_ncSemirings_1148_);
lean_inc(v_ncRings_1147_);
lean_inc(v_semirings_1146_);
lean_inc(v_rings_1145_);
lean_inc(v_exp_1144_);
lean_dec(v_s_1143_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1159_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1155_; lean_object* v___x_1157_; 
v___x_1155_ = lean_array_push(v_ncRings_1147_, v___x_1142_);
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 3, v___x_1155_);
v___x_1157_ = v___x_1153_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_exp_1144_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v_rings_1145_);
lean_ctor_set(v_reuseFailAlloc_1158_, 2, v_semirings_1146_);
lean_ctor_set(v_reuseFailAlloc_1158_, 3, v___x_1155_);
lean_ctor_set(v_reuseFailAlloc_1158_, 4, v_ncSemirings_1148_);
lean_ctor_set(v_reuseFailAlloc_1158_, 5, v_typeClassify_1149_);
lean_ctor_set(v_reuseFailAlloc_1158_, 6, v_orders_1150_);
lean_ctor_set(v_reuseFailAlloc_1158_, 7, v_typeOrderClassify_1151_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f(lean_object* v_type_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_){
_start:
{
lean_object* v___x_1168_; 
lean_inc_ref(v_type_1160_);
v___x_1168_ = l_Lean_Meta_getDecLevel_x3f(v_type_1160_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1281_; 
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1171_ = v___x_1168_;
v_isShared_1172_ = v_isSharedCheck_1281_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1168_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1281_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
if (lean_obj_tag(v_a_1169_) == 1)
{
lean_object* v_val_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
lean_del_object(v___x_1171_);
v_val_1173_ = lean_ctor_get(v_a_1169_, 0);
lean_inc_n(v_val_1173_, 2);
lean_dec_ref_known(v_a_1169_, 1);
v___x_1174_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__14));
v___x_1175_ = lean_box(0);
v___x_1176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1176_, 0, v_val_1173_);
lean_ctor_set(v___x_1176_, 1, v___x_1175_);
lean_inc_ref(v___x_1176_);
v___x_1177_ = l_Lean_mkConst(v___x_1174_, v___x_1176_);
lean_inc_ref(v_type_1160_);
v___x_1178_ = l_Lean_Expr_app___override(v___x_1177_, v_type_1160_);
v___x_1179_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1178_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_);
if (lean_obj_tag(v___x_1179_) == 0)
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1268_; 
v_a_1180_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1182_ = v___x_1179_;
v_isShared_1183_ = v_isSharedCheck_1268_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1179_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1268_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
if (lean_obj_tag(v_a_1180_) == 1)
{
lean_object* v_toCold_1184_; lean_object* v_options_1185_; lean_object* v_val_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1263_; 
lean_del_object(v___x_1182_);
v_toCold_1184_ = lean_ctor_get(v_a_1165_, 0);
v_options_1185_ = lean_ctor_get(v_toCold_1184_, 2);
v_val_1186_ = lean_ctor_get(v_a_1180_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v_a_1180_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1188_ = v_a_1180_;
v_isShared_1189_ = v_isSharedCheck_1263_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_val_1186_);
lean_dec(v_a_1180_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1263_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v_inheritedTraceOptions_1190_; uint8_t v_hasTrace_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___y_1196_; lean_object* v___y_1197_; lean_object* v___y_1198_; lean_object* v___y_1199_; lean_object* v___y_1200_; lean_object* v___y_1201_; 
v_inheritedTraceOptions_1190_ = lean_ctor_get(v_toCold_1184_, 11);
v_hasTrace_1191_ = lean_ctor_get_uint8(v_options_1185_, sizeof(void*)*1);
v___x_1192_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__10));
v___x_1193_ = l_Lean_mkConst(v___x_1192_, v___x_1176_);
lean_inc(v_val_1186_);
lean_inc_ref(v_type_1160_);
v___x_1194_ = l_Lean_mkAppB(v___x_1193_, v_type_1160_, v_val_1186_);
if (v_hasTrace_1191_ == 0)
{
v___y_1196_ = v_a_1161_;
v___y_1197_ = v_a_1162_;
v___y_1198_ = v_a_1163_;
v___y_1199_ = v_a_1164_;
v___y_1200_ = v_a_1165_;
v___y_1201_ = v_a_1166_;
goto v___jp_1195_;
}
else
{
lean_object* v___x_1248_; lean_object* v___x_1249_; uint8_t v___x_1250_; 
v___x_1248_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__60));
v___x_1249_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61);
v___x_1250_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1190_, v_options_1185_, v___x_1249_);
if (v___x_1250_ == 0)
{
v___y_1196_ = v_a_1161_;
v___y_1197_ = v_a_1162_;
v___y_1198_ = v_a_1163_;
v___y_1199_ = v_a_1164_;
v___y_1200_ = v_a_1165_;
v___y_1201_ = v_a_1166_;
goto v___jp_1195_;
}
else
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1251_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78);
lean_inc_ref(v_type_1160_);
v___x_1252_ = l_Lean_MessageData_ofExpr(v_type_1160_);
v___x_1253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1251_);
lean_ctor_set(v___x_1253_, 1, v___x_1252_);
v___x_1254_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(v___x_1248_, v___x_1253_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_dec_ref_known(v___x_1254_, 1);
v___y_1196_ = v_a_1161_;
v___y_1197_ = v_a_1162_;
v___y_1198_ = v_a_1163_;
v___y_1199_ = v_a_1164_;
v___y_1200_ = v_a_1165_;
v___y_1201_ = v_a_1166_;
goto v___jp_1195_;
}
else
{
lean_object* v_a_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1262_; 
lean_dec_ref(v___x_1194_);
lean_del_object(v___x_1188_);
lean_dec(v_val_1186_);
lean_dec(v_val_1173_);
lean_dec_ref(v_type_1160_);
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1257_ = v___x_1254_;
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_a_1255_);
lean_dec(v___x_1254_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1260_; 
if (v_isShared_1258_ == 0)
{
v___x_1260_ = v___x_1257_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_a_1255_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
}
}
v___jp_1195_:
{
lean_object* v___x_1202_; 
lean_inc_ref(v___x_1194_);
lean_inc_ref(v_type_1160_);
lean_inc(v_val_1173_);
v___x_1202_ = l_Lean_Meta_Sym_Arith_getIsCharInst_x3f(v_val_1173_, v_type_1160_, v___x_1194_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v_a_1203_; lean_object* v___x_1204_; 
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
lean_inc(v_a_1203_);
lean_dec_ref_known(v___x_1202_, 1);
v___x_1204_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v___y_1197_, v___y_1200_);
if (lean_obj_tag(v___x_1204_) == 0)
{
lean_object* v_a_1205_; lean_object* v_ncRings_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___f_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v_a_1205_ = lean_ctor_get(v___x_1204_, 0);
lean_inc(v_a_1205_);
lean_dec_ref_known(v___x_1204_, 1);
v_ncRings_1206_ = lean_ctor_get(v_a_1205_, 3);
lean_inc_ref(v_ncRings_1206_);
lean_dec(v_a_1205_);
v___x_1207_ = lean_array_get_size(v_ncRings_1206_);
lean_dec_ref(v_ncRings_1206_);
v___x_1208_ = lean_box(0);
v___x_1209_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1207_);
lean_ctor_set(v___x_1209_, 1, v_type_1160_);
lean_ctor_set(v___x_1209_, 2, v_val_1173_);
lean_ctor_set(v___x_1209_, 3, v_val_1186_);
lean_ctor_set(v___x_1209_, 4, v___x_1194_);
lean_ctor_set(v___x_1209_, 5, v_a_1203_);
lean_ctor_set(v___x_1209_, 6, v___x_1208_);
lean_ctor_set(v___x_1209_, 7, v___x_1208_);
lean_ctor_set(v___x_1209_, 8, v___x_1208_);
lean_ctor_set(v___x_1209_, 9, v___x_1208_);
lean_ctor_set(v___x_1209_, 10, v___x_1208_);
lean_ctor_set(v___x_1209_, 11, v___x_1208_);
lean_ctor_set(v___x_1209_, 12, v___x_1208_);
lean_ctor_set(v___x_1209_, 13, v___x_1208_);
lean_ctor_set(v___x_1209_, 14, v___x_1208_);
lean_ctor_set(v___x_1209_, 15, v___x_1208_);
v___f_1210_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___lam__0), 2, 1);
lean_closure_set(v___f_1210_, 0, v___x_1209_);
v___x_1211_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_1212_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_1211_, v___f_1210_, v___y_1197_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1222_; 
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1222_ == 0)
{
lean_object* v_unused_1223_; 
v_unused_1223_ = lean_ctor_get(v___x_1212_, 0);
lean_dec(v_unused_1223_);
v___x_1214_ = v___x_1212_;
v_isShared_1215_ = v_isSharedCheck_1222_;
goto v_resetjp_1213_;
}
else
{
lean_dec(v___x_1212_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1222_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1217_; 
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v___x_1207_);
v___x_1217_ = v___x_1188_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v___x_1207_);
v___x_1217_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
lean_object* v___x_1219_; 
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 0, v___x_1217_);
v___x_1219_ = v___x_1214_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v___x_1217_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
}
else
{
lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1231_; 
lean_del_object(v___x_1188_);
v_a_1224_ = lean_ctor_get(v___x_1212_, 0);
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
v_reuseFailAlloc_1230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_a_1224_);
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
else
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1239_; 
lean_dec(v_a_1203_);
lean_dec_ref(v___x_1194_);
lean_del_object(v___x_1188_);
lean_dec(v_val_1186_);
lean_dec(v_val_1173_);
lean_dec_ref(v_type_1160_);
v_a_1232_ = lean_ctor_get(v___x_1204_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1204_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1234_ = v___x_1204_;
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1204_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1237_; 
if (v_isShared_1235_ == 0)
{
v___x_1237_ = v___x_1234_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_a_1232_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
}
else
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
lean_dec_ref(v___x_1194_);
lean_del_object(v___x_1188_);
lean_dec(v_val_1186_);
lean_dec(v_val_1173_);
lean_dec_ref(v_type_1160_);
v_a_1240_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1202_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1202_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
}
}
else
{
lean_object* v___x_1264_; lean_object* v___x_1266_; 
lean_dec(v_a_1180_);
lean_dec_ref_known(v___x_1176_, 2);
lean_dec(v_val_1173_);
lean_dec_ref(v_type_1160_);
v___x_1264_ = lean_box(0);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 0, v___x_1264_);
v___x_1266_ = v___x_1182_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1264_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
else
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
lean_dec_ref_known(v___x_1176_, 2);
lean_dec(v_val_1173_);
lean_dec_ref(v_type_1160_);
v_a_1269_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1271_ = v___x_1179_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1179_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1274_; 
if (v_isShared_1272_ == 0)
{
v___x_1274_ = v___x_1271_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_a_1269_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
}
else
{
lean_object* v___x_1277_; lean_object* v___x_1279_; 
lean_dec(v_a_1169_);
lean_dec_ref(v_type_1160_);
v___x_1277_ = lean_box(0);
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 0, v___x_1277_);
v___x_1279_ = v___x_1171_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___x_1277_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
}
else
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
lean_dec_ref(v_type_1160_);
v_a_1282_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1284_ = v___x_1168_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1168_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1285_ == 0)
{
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1282_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___boxed(lean_object* v_type_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f(v_type_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_);
lean_dec(v_a_1296_);
lean_dec_ref(v_a_1295_);
lean_dec(v_a_1294_);
lean_dec_ref(v_a_1293_);
lean_dec(v_a_1292_);
lean_dec_ref(v_a_1291_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_1299_, lean_object* v_x_1300_, lean_object* v_x_1301_, lean_object* v_x_1302_){
_start:
{
lean_object* v_ks_1303_; lean_object* v_vs_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1330_; 
v_ks_1303_ = lean_ctor_get(v_x_1299_, 0);
v_vs_1304_ = lean_ctor_get(v_x_1299_, 1);
v_isSharedCheck_1330_ = !lean_is_exclusive(v_x_1299_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1306_ = v_x_1299_;
v_isShared_1307_ = v_isSharedCheck_1330_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_vs_1304_);
lean_inc(v_ks_1303_);
lean_dec(v_x_1299_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1330_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1308_; uint8_t v___x_1309_; 
v___x_1308_ = lean_array_get_size(v_ks_1303_);
v___x_1309_ = lean_nat_dec_lt(v_x_1300_, v___x_1308_);
if (v___x_1309_ == 0)
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1313_; 
lean_dec(v_x_1300_);
v___x_1310_ = lean_array_push(v_ks_1303_, v_x_1301_);
v___x_1311_ = lean_array_push(v_vs_1304_, v_x_1302_);
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 1, v___x_1311_);
lean_ctor_set(v___x_1306_, 0, v___x_1310_);
v___x_1313_ = v___x_1306_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v___x_1310_);
lean_ctor_set(v_reuseFailAlloc_1314_, 1, v___x_1311_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
else
{
lean_object* v_k_x27_1315_; size_t v___x_1316_; size_t v___x_1317_; uint8_t v___x_1318_; 
v_k_x27_1315_ = lean_array_fget_borrowed(v_ks_1303_, v_x_1300_);
v___x_1316_ = lean_ptr_addr(v_x_1301_);
v___x_1317_ = lean_ptr_addr(v_k_x27_1315_);
v___x_1318_ = lean_usize_dec_eq(v___x_1316_, v___x_1317_);
if (v___x_1318_ == 0)
{
lean_object* v___x_1320_; 
if (v_isShared_1307_ == 0)
{
v___x_1320_ = v___x_1306_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_ks_1303_);
lean_ctor_set(v_reuseFailAlloc_1324_, 1, v_vs_1304_);
v___x_1320_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1321_ = lean_unsigned_to_nat(1u);
v___x_1322_ = lean_nat_add(v_x_1300_, v___x_1321_);
lean_dec(v_x_1300_);
v_x_1299_ = v___x_1320_;
v_x_1300_ = v___x_1322_;
goto _start;
}
}
else
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1328_; 
v___x_1325_ = lean_array_fset(v_ks_1303_, v_x_1300_, v_x_1301_);
v___x_1326_ = lean_array_fset(v_vs_1304_, v_x_1300_, v_x_1302_);
lean_dec(v_x_1300_);
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 1, v___x_1326_);
lean_ctor_set(v___x_1306_, 0, v___x_1325_);
v___x_1328_ = v___x_1306_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v___x_1325_);
lean_ctor_set(v_reuseFailAlloc_1329_, 1, v___x_1326_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4___redArg(lean_object* v_n_1331_, lean_object* v_k_1332_, lean_object* v_v_1333_){
_start:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1334_ = lean_unsigned_to_nat(0u);
v___x_1335_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_n_1331_, v___x_1334_, v_k_1332_, v_v_1333_);
return v___x_1335_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1336_; 
v___x_1336_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(lean_object* v_x_1337_, size_t v_x_1338_, size_t v_x_1339_, lean_object* v_x_1340_, lean_object* v_x_1341_){
_start:
{
if (lean_obj_tag(v_x_1337_) == 0)
{
lean_object* v_es_1342_; size_t v___x_1343_; size_t v___x_1344_; lean_object* v_j_1345_; lean_object* v___x_1346_; uint8_t v___x_1347_; 
v_es_1342_ = lean_ctor_get(v_x_1337_, 0);
v___x_1343_ = ((size_t)31ULL);
v___x_1344_ = lean_usize_land(v_x_1338_, v___x_1343_);
v_j_1345_ = lean_usize_to_nat(v___x_1344_);
v___x_1346_ = lean_array_get_size(v_es_1342_);
v___x_1347_ = lean_nat_dec_lt(v_j_1345_, v___x_1346_);
if (v___x_1347_ == 0)
{
lean_dec(v_j_1345_);
lean_dec(v_x_1341_);
lean_dec_ref(v_x_1340_);
return v_x_1337_;
}
else
{
lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1388_; 
lean_inc_ref(v_es_1342_);
v_isSharedCheck_1388_ = !lean_is_exclusive(v_x_1337_);
if (v_isSharedCheck_1388_ == 0)
{
lean_object* v_unused_1389_; 
v_unused_1389_ = lean_ctor_get(v_x_1337_, 0);
lean_dec(v_unused_1389_);
v___x_1349_ = v_x_1337_;
v_isShared_1350_ = v_isSharedCheck_1388_;
goto v_resetjp_1348_;
}
else
{
lean_dec(v_x_1337_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1388_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v_v_1351_; lean_object* v___x_1352_; lean_object* v_xs_x27_1353_; lean_object* v___y_1355_; 
v_v_1351_ = lean_array_fget(v_es_1342_, v_j_1345_);
v___x_1352_ = lean_box(0);
v_xs_x27_1353_ = lean_array_fset(v_es_1342_, v_j_1345_, v___x_1352_);
switch(lean_obj_tag(v_v_1351_))
{
case 0:
{
lean_object* v_key_1360_; lean_object* v_val_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1373_; 
v_key_1360_ = lean_ctor_get(v_v_1351_, 0);
v_val_1361_ = lean_ctor_get(v_v_1351_, 1);
v_isSharedCheck_1373_ = !lean_is_exclusive(v_v_1351_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1363_ = v_v_1351_;
v_isShared_1364_ = v_isSharedCheck_1373_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_val_1361_);
lean_inc(v_key_1360_);
lean_dec(v_v_1351_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1373_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
size_t v___x_1365_; size_t v___x_1366_; uint8_t v___x_1367_; 
v___x_1365_ = lean_ptr_addr(v_x_1340_);
v___x_1366_ = lean_ptr_addr(v_key_1360_);
v___x_1367_ = lean_usize_dec_eq(v___x_1365_, v___x_1366_);
if (v___x_1367_ == 0)
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
lean_del_object(v___x_1363_);
v___x_1368_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1360_, v_val_1361_, v_x_1340_, v_x_1341_);
v___x_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1368_);
v___y_1355_ = v___x_1369_;
goto v___jp_1354_;
}
else
{
lean_object* v___x_1371_; 
lean_dec(v_val_1361_);
lean_dec(v_key_1360_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 1, v_x_1341_);
lean_ctor_set(v___x_1363_, 0, v_x_1340_);
v___x_1371_ = v___x_1363_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_x_1340_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v_x_1341_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
v___y_1355_ = v___x_1371_;
goto v___jp_1354_;
}
}
}
}
case 1:
{
lean_object* v_node_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1386_; 
v_node_1374_ = lean_ctor_get(v_v_1351_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v_v_1351_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1376_ = v_v_1351_;
v_isShared_1377_ = v_isSharedCheck_1386_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_node_1374_);
lean_dec(v_v_1351_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1386_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
size_t v___x_1378_; size_t v___x_1379_; size_t v___x_1380_; size_t v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1384_; 
v___x_1378_ = ((size_t)5ULL);
v___x_1379_ = lean_usize_shift_right(v_x_1338_, v___x_1378_);
v___x_1380_ = ((size_t)1ULL);
v___x_1381_ = lean_usize_add(v_x_1339_, v___x_1380_);
v___x_1382_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(v_node_1374_, v___x_1379_, v___x_1381_, v_x_1340_, v_x_1341_);
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 0, v___x_1382_);
v___x_1384_ = v___x_1376_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1382_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
v___y_1355_ = v___x_1384_;
goto v___jp_1354_;
}
}
}
default: 
{
lean_object* v___x_1387_; 
v___x_1387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1387_, 0, v_x_1340_);
lean_ctor_set(v___x_1387_, 1, v_x_1341_);
v___y_1355_ = v___x_1387_;
goto v___jp_1354_;
}
}
v___jp_1354_:
{
lean_object* v___x_1356_; lean_object* v___x_1358_; 
v___x_1356_ = lean_array_fset(v_xs_x27_1353_, v_j_1345_, v___y_1355_);
lean_dec(v_j_1345_);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 0, v___x_1356_);
v___x_1358_ = v___x_1349_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
}
else
{
lean_object* v_ks_1390_; lean_object* v_vs_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1409_; 
v_ks_1390_ = lean_ctor_get(v_x_1337_, 0);
v_vs_1391_ = lean_ctor_get(v_x_1337_, 1);
v_isSharedCheck_1409_ = !lean_is_exclusive(v_x_1337_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1393_ = v_x_1337_;
v_isShared_1394_ = v_isSharedCheck_1409_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_vs_1391_);
lean_inc(v_ks_1390_);
lean_dec(v_x_1337_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1409_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1396_; 
if (v_isShared_1394_ == 0)
{
v___x_1396_ = v___x_1393_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_ks_1390_);
lean_ctor_set(v_reuseFailAlloc_1408_, 1, v_vs_1391_);
v___x_1396_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
lean_object* v_newNode_1397_; size_t v___x_1398_; uint8_t v___x_1399_; 
v_newNode_1397_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4___redArg(v___x_1396_, v_x_1340_, v_x_1341_);
v___x_1398_ = ((size_t)7ULL);
v___x_1399_ = lean_usize_dec_le(v___x_1398_, v_x_1339_);
if (v___x_1399_ == 0)
{
lean_object* v___x_1400_; lean_object* v___x_1401_; uint8_t v___x_1402_; 
v___x_1400_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1397_);
v___x_1401_ = lean_unsigned_to_nat(4u);
v___x_1402_ = lean_nat_dec_lt(v___x_1400_, v___x_1401_);
lean_dec(v___x_1400_);
if (v___x_1402_ == 0)
{
lean_object* v_ks_1403_; lean_object* v_vs_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
v_ks_1403_ = lean_ctor_get(v_newNode_1397_, 0);
lean_inc_ref(v_ks_1403_);
v_vs_1404_ = lean_ctor_get(v_newNode_1397_, 1);
lean_inc_ref(v_vs_1404_);
lean_dec_ref(v_newNode_1397_);
v___x_1405_ = lean_unsigned_to_nat(0u);
v___x_1406_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__0);
v___x_1407_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___redArg(v_x_1339_, v_ks_1403_, v_vs_1404_, v___x_1405_, v___x_1406_);
lean_dec_ref(v_vs_1404_);
lean_dec_ref(v_ks_1403_);
return v___x_1407_;
}
else
{
return v_newNode_1397_;
}
}
else
{
return v_newNode_1397_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___redArg(size_t v_depth_1410_, lean_object* v_keys_1411_, lean_object* v_vals_1412_, lean_object* v_i_1413_, lean_object* v_entries_1414_){
_start:
{
lean_object* v___x_1415_; uint8_t v___x_1416_; 
v___x_1415_ = lean_array_get_size(v_keys_1411_);
v___x_1416_ = lean_nat_dec_lt(v_i_1413_, v___x_1415_);
if (v___x_1416_ == 0)
{
lean_dec(v_i_1413_);
return v_entries_1414_;
}
else
{
lean_object* v_k_1417_; lean_object* v_v_1418_; size_t v___x_1419_; size_t v___x_1420_; size_t v___x_1421_; uint64_t v___x_1422_; size_t v_h_1423_; size_t v___x_1424_; lean_object* v___x_1425_; size_t v___x_1426_; size_t v___x_1427_; size_t v___x_1428_; size_t v_h_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v_k_1417_ = lean_array_fget_borrowed(v_keys_1411_, v_i_1413_);
v_v_1418_ = lean_array_fget_borrowed(v_vals_1412_, v_i_1413_);
v___x_1419_ = lean_ptr_addr(v_k_1417_);
v___x_1420_ = ((size_t)3ULL);
v___x_1421_ = lean_usize_shift_right(v___x_1419_, v___x_1420_);
v___x_1422_ = lean_usize_to_uint64(v___x_1421_);
v_h_1423_ = lean_uint64_to_usize(v___x_1422_);
v___x_1424_ = ((size_t)5ULL);
v___x_1425_ = lean_unsigned_to_nat(1u);
v___x_1426_ = ((size_t)1ULL);
v___x_1427_ = lean_usize_sub(v_depth_1410_, v___x_1426_);
v___x_1428_ = lean_usize_mul(v___x_1424_, v___x_1427_);
v_h_1429_ = lean_usize_shift_right(v_h_1423_, v___x_1428_);
v___x_1430_ = lean_nat_add(v_i_1413_, v___x_1425_);
lean_dec(v_i_1413_);
lean_inc(v_v_1418_);
lean_inc(v_k_1417_);
v___x_1431_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(v_entries_1414_, v_h_1429_, v_depth_1410_, v_k_1417_, v_v_1418_);
v_i_1413_ = v___x_1430_;
v_entries_1414_ = v___x_1431_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_1433_, lean_object* v_keys_1434_, lean_object* v_vals_1435_, lean_object* v_i_1436_, lean_object* v_entries_1437_){
_start:
{
size_t v_depth_boxed_1438_; lean_object* v_res_1439_; 
v_depth_boxed_1438_ = lean_unbox_usize(v_depth_1433_);
lean_dec(v_depth_1433_);
v_res_1439_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___redArg(v_depth_boxed_1438_, v_keys_1434_, v_vals_1435_, v_i_1436_, v_entries_1437_);
lean_dec_ref(v_vals_1435_);
lean_dec_ref(v_keys_1434_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_x_1440_, lean_object* v_x_1441_, lean_object* v_x_1442_, lean_object* v_x_1443_, lean_object* v_x_1444_){
_start:
{
size_t v_x_2146__boxed_1445_; size_t v_x_2147__boxed_1446_; lean_object* v_res_1447_; 
v_x_2146__boxed_1445_ = lean_unbox_usize(v_x_1441_);
lean_dec(v_x_1441_);
v_x_2147__boxed_1446_ = lean_unbox_usize(v_x_1442_);
lean_dec(v_x_1442_);
v_res_1447_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(v_x_1440_, v_x_2146__boxed_1445_, v_x_2147__boxed_1446_, v_x_1443_, v_x_1444_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1___redArg(lean_object* v_x_1448_, lean_object* v_x_1449_, lean_object* v_x_1450_){
_start:
{
size_t v___x_1451_; size_t v___x_1452_; size_t v___x_1453_; uint64_t v___x_1454_; size_t v___x_1455_; size_t v___x_1456_; lean_object* v___x_1457_; 
v___x_1451_ = lean_ptr_addr(v_x_1449_);
v___x_1452_ = ((size_t)3ULL);
v___x_1453_ = lean_usize_shift_right(v___x_1451_, v___x_1452_);
v___x_1454_ = lean_usize_to_uint64(v___x_1453_);
v___x_1455_ = lean_uint64_to_usize(v___x_1454_);
v___x_1456_ = ((size_t)1ULL);
v___x_1457_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(v_x_1448_, v___x_1455_, v___x_1456_, v_x_1449_, v_x_1450_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f___lam__0(lean_object* v_type_1458_, lean_object* v___y_1459_, lean_object* v_s_1460_){
_start:
{
lean_object* v_exp_1461_; lean_object* v_rings_1462_; lean_object* v_semirings_1463_; lean_object* v_ncRings_1464_; lean_object* v_ncSemirings_1465_; lean_object* v_typeClassify_1466_; lean_object* v_orders_1467_; lean_object* v_typeOrderClassify_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1476_; 
v_exp_1461_ = lean_ctor_get(v_s_1460_, 0);
v_rings_1462_ = lean_ctor_get(v_s_1460_, 1);
v_semirings_1463_ = lean_ctor_get(v_s_1460_, 2);
v_ncRings_1464_ = lean_ctor_get(v_s_1460_, 3);
v_ncSemirings_1465_ = lean_ctor_get(v_s_1460_, 4);
v_typeClassify_1466_ = lean_ctor_get(v_s_1460_, 5);
v_orders_1467_ = lean_ctor_get(v_s_1460_, 6);
v_typeOrderClassify_1468_ = lean_ctor_get(v_s_1460_, 7);
v_isSharedCheck_1476_ = !lean_is_exclusive(v_s_1460_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1470_ = v_s_1460_;
v_isShared_1471_ = v_isSharedCheck_1476_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_typeOrderClassify_1468_);
lean_inc(v_orders_1467_);
lean_inc(v_typeClassify_1466_);
lean_inc(v_ncSemirings_1465_);
lean_inc(v_ncRings_1464_);
lean_inc(v_semirings_1463_);
lean_inc(v_rings_1462_);
lean_inc(v_exp_1461_);
lean_dec(v_s_1460_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1476_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1472_; lean_object* v___x_1474_; 
v___x_1472_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1___redArg(v_typeClassify_1466_, v_type_1458_, v___y_1459_);
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 5, v___x_1472_);
v___x_1474_ = v___x_1470_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_exp_1461_);
lean_ctor_set(v_reuseFailAlloc_1475_, 1, v_rings_1462_);
lean_ctor_set(v_reuseFailAlloc_1475_, 2, v_semirings_1463_);
lean_ctor_set(v_reuseFailAlloc_1475_, 3, v_ncRings_1464_);
lean_ctor_set(v_reuseFailAlloc_1475_, 4, v_ncSemirings_1465_);
lean_ctor_set(v_reuseFailAlloc_1475_, 5, v___x_1472_);
lean_ctor_set(v_reuseFailAlloc_1475_, 6, v_orders_1467_);
lean_ctor_set(v_reuseFailAlloc_1475_, 7, v_typeOrderClassify_1468_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1477_, lean_object* v_vals_1478_, lean_object* v_i_1479_, lean_object* v_k_1480_){
_start:
{
lean_object* v___x_1481_; uint8_t v___x_1482_; 
v___x_1481_ = lean_array_get_size(v_keys_1477_);
v___x_1482_ = lean_nat_dec_lt(v_i_1479_, v___x_1481_);
if (v___x_1482_ == 0)
{
lean_object* v___x_1483_; 
lean_dec(v_i_1479_);
v___x_1483_ = lean_box(0);
return v___x_1483_;
}
else
{
lean_object* v_k_x27_1484_; size_t v___x_1485_; size_t v___x_1486_; uint8_t v___x_1487_; 
v_k_x27_1484_ = lean_array_fget_borrowed(v_keys_1477_, v_i_1479_);
v___x_1485_ = lean_ptr_addr(v_k_1480_);
v___x_1486_ = lean_ptr_addr(v_k_x27_1484_);
v___x_1487_ = lean_usize_dec_eq(v___x_1485_, v___x_1486_);
if (v___x_1487_ == 0)
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1488_ = lean_unsigned_to_nat(1u);
v___x_1489_ = lean_nat_add(v_i_1479_, v___x_1488_);
lean_dec(v_i_1479_);
v_i_1479_ = v___x_1489_;
goto _start;
}
else
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1491_ = lean_array_fget_borrowed(v_vals_1478_, v_i_1479_);
lean_dec(v_i_1479_);
lean_inc(v___x_1491_);
v___x_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1491_);
return v___x_1492_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1493_, lean_object* v_vals_1494_, lean_object* v_i_1495_, lean_object* v_k_1496_){
_start:
{
lean_object* v_res_1497_; 
v_res_1497_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1493_, v_vals_1494_, v_i_1495_, v_k_1496_);
lean_dec_ref(v_k_1496_);
lean_dec_ref(v_vals_1494_);
lean_dec_ref(v_keys_1493_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg(lean_object* v_x_1498_, size_t v_x_1499_, lean_object* v_x_1500_){
_start:
{
if (lean_obj_tag(v_x_1498_) == 0)
{
lean_object* v_es_1501_; lean_object* v___x_1502_; size_t v___x_1503_; size_t v___x_1504_; lean_object* v_j_1505_; lean_object* v___x_1506_; 
v_es_1501_ = lean_ctor_get(v_x_1498_, 0);
v___x_1502_ = lean_box(2);
v___x_1503_ = ((size_t)31ULL);
v___x_1504_ = lean_usize_land(v_x_1499_, v___x_1503_);
v_j_1505_ = lean_usize_to_nat(v___x_1504_);
v___x_1506_ = lean_array_get_borrowed(v___x_1502_, v_es_1501_, v_j_1505_);
lean_dec(v_j_1505_);
switch(lean_obj_tag(v___x_1506_))
{
case 0:
{
lean_object* v_key_1507_; lean_object* v_val_1508_; size_t v___x_1509_; size_t v___x_1510_; uint8_t v___x_1511_; 
v_key_1507_ = lean_ctor_get(v___x_1506_, 0);
v_val_1508_ = lean_ctor_get(v___x_1506_, 1);
v___x_1509_ = lean_ptr_addr(v_x_1500_);
v___x_1510_ = lean_ptr_addr(v_key_1507_);
v___x_1511_ = lean_usize_dec_eq(v___x_1509_, v___x_1510_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1512_; 
v___x_1512_ = lean_box(0);
return v___x_1512_;
}
else
{
lean_object* v___x_1513_; 
lean_inc(v_val_1508_);
v___x_1513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1513_, 0, v_val_1508_);
return v___x_1513_;
}
}
case 1:
{
lean_object* v_node_1514_; size_t v___x_1515_; size_t v___x_1516_; 
v_node_1514_ = lean_ctor_get(v___x_1506_, 0);
v___x_1515_ = ((size_t)5ULL);
v___x_1516_ = lean_usize_shift_right(v_x_1499_, v___x_1515_);
v_x_1498_ = v_node_1514_;
v_x_1499_ = v___x_1516_;
goto _start;
}
default: 
{
lean_object* v___x_1518_; 
v___x_1518_ = lean_box(0);
return v___x_1518_;
}
}
}
else
{
lean_object* v_ks_1519_; lean_object* v_vs_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v_ks_1519_ = lean_ctor_get(v_x_1498_, 0);
v_vs_1520_ = lean_ctor_get(v_x_1498_, 1);
v___x_1521_ = lean_unsigned_to_nat(0u);
v___x_1522_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1519_, v_vs_1520_, v___x_1521_, v_x_1500_);
return v___x_1522_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1523_, lean_object* v_x_1524_, lean_object* v_x_1525_){
_start:
{
size_t v_x_2365__boxed_1526_; lean_object* v_res_1527_; 
v_x_2365__boxed_1526_ = lean_unbox_usize(v_x_1524_);
lean_dec(v_x_1524_);
v_res_1527_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg(v_x_1523_, v_x_2365__boxed_1526_, v_x_1525_);
lean_dec_ref(v_x_1525_);
lean_dec_ref(v_x_1523_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(lean_object* v_x_1528_, lean_object* v_x_1529_){
_start:
{
size_t v___x_1530_; size_t v___x_1531_; size_t v___x_1532_; uint64_t v___x_1533_; size_t v___x_1534_; lean_object* v___x_1535_; 
v___x_1530_ = lean_ptr_addr(v_x_1529_);
v___x_1531_ = ((size_t)3ULL);
v___x_1532_ = lean_usize_shift_right(v___x_1530_, v___x_1531_);
v___x_1533_ = lean_usize_to_uint64(v___x_1532_);
v___x_1534_ = lean_uint64_to_usize(v___x_1533_);
v___x_1535_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg(v_x_1528_, v___x_1534_, v_x_1529_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg___boxed(lean_object* v_x_1536_, lean_object* v_x_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(v_x_1536_, v_x_1537_);
lean_dec_ref(v_x_1537_);
lean_dec_ref(v_x_1536_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f(lean_object* v_type_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_1541_, v_a_1544_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1602_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1550_ = v___x_1547_;
v_isShared_1551_ = v_isSharedCheck_1602_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1547_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1602_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v_typeClassify_1552_; lean_object* v___x_1553_; 
v_typeClassify_1552_ = lean_ctor_get(v_a_1548_, 5);
lean_inc_ref(v_typeClassify_1552_);
lean_dec(v_a_1548_);
v___x_1553_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(v_typeClassify_1552_, v_type_1539_);
lean_dec_ref(v_typeClassify_1552_);
if (lean_obj_tag(v___x_1553_) == 1)
{
lean_object* v_val_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1569_; 
lean_dec_ref(v_type_1539_);
v_val_1554_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1556_ = v___x_1553_;
v_isShared_1557_ = v_isSharedCheck_1569_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_val_1554_);
lean_dec(v___x_1553_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1569_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
if (lean_obj_tag(v_val_1554_) == 0)
{
lean_object* v_id_1558_; lean_object* v___x_1560_; 
v_id_1558_ = lean_ctor_get(v_val_1554_, 0);
lean_inc(v_id_1558_);
lean_dec_ref_known(v_val_1554_, 1);
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 0, v_id_1558_);
v___x_1560_ = v___x_1556_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_id_1558_);
v___x_1560_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
lean_object* v___x_1562_; 
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 0, v___x_1560_);
v___x_1562_ = v___x_1550_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v___x_1560_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
else
{
lean_object* v___x_1565_; lean_object* v___x_1567_; 
lean_del_object(v___x_1556_);
lean_dec(v_val_1554_);
v___x_1565_ = lean_box(0);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 0, v___x_1565_);
v___x_1567_ = v___x_1550_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v___x_1565_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
}
else
{
lean_object* v___x_1570_; 
lean_dec(v___x_1553_);
lean_del_object(v___x_1550_);
lean_inc_ref(v_type_1539_);
v___x_1570_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f(v_type_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1601_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1573_ = v___x_1570_;
v_isShared_1574_ = v_isSharedCheck_1601_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1570_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1601_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___y_1576_; 
if (lean_obj_tag(v_a_1571_) == 0)
{
lean_object* v___x_1596_; 
lean_del_object(v___x_1573_);
v___x_1596_ = lean_box(4);
v___y_1576_ = v___x_1596_;
goto v___jp_1575_;
}
else
{
lean_object* v_val_1597_; lean_object* v___x_1599_; 
v_val_1597_ = lean_ctor_get(v_a_1571_, 0);
lean_inc(v_val_1597_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 0, v_val_1597_);
v___x_1599_ = v___x_1573_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_val_1597_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
v___y_1576_ = v___x_1599_;
goto v___jp_1575_;
}
}
v___jp_1575_:
{
lean_object* v___f_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___f_1577_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f___lam__0), 3, 2);
lean_closure_set(v___f_1577_, 0, v_type_1539_);
lean_closure_set(v___f_1577_, 1, v___y_1576_);
v___x_1578_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_1579_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_1578_, v___f_1577_, v_a_1541_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1586_ == 0)
{
lean_object* v_unused_1587_; 
v_unused_1587_ = lean_ctor_get(v___x_1579_, 0);
lean_dec(v_unused_1587_);
v___x_1581_ = v___x_1579_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_dec(v___x_1579_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1584_; 
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 0, v_a_1571_);
v___x_1584_ = v___x_1581_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_a_1571_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
else
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1595_; 
lean_dec(v_a_1571_);
v_a_1588_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1590_ = v___x_1579_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1579_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
if (v_isShared_1591_ == 0)
{
v___x_1593_ = v___x_1590_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_a_1588_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_type_1539_);
return v___x_1570_;
}
}
}
}
else
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
lean_dec_ref(v_type_1539_);
v_a_1603_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1547_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1547_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f___boxed(lean_object* v_type_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f(v_type_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_);
lean_dec(v_a_1617_);
lean_dec_ref(v_a_1616_);
lean_dec(v_a_1615_);
lean_dec_ref(v_a_1614_);
lean_dec(v_a_1613_);
lean_dec_ref(v_a_1612_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0(lean_object* v_00_u03b2_1620_, lean_object* v_x_1621_, lean_object* v_x_1622_){
_start:
{
lean_object* v___x_1623_; 
v___x_1623_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(v_x_1621_, v_x_1622_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___boxed(lean_object* v_00_u03b2_1624_, lean_object* v_x_1625_, lean_object* v_x_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0(v_00_u03b2_1624_, v_x_1625_, v_x_1626_);
lean_dec_ref(v_x_1626_);
lean_dec_ref(v_x_1625_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1(lean_object* v_00_u03b2_1628_, lean_object* v_x_1629_, lean_object* v_x_1630_, lean_object* v_x_1631_){
_start:
{
lean_object* v___x_1632_; 
v___x_1632_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1___redArg(v_x_1629_, v_x_1630_, v_x_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1633_, lean_object* v_x_1634_, size_t v_x_1635_, lean_object* v_x_1636_){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg(v_x_1634_, v_x_1635_, v_x_1636_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1638_, lean_object* v_x_1639_, lean_object* v_x_1640_, lean_object* v_x_1641_){
_start:
{
size_t v_x_2581__boxed_1642_; lean_object* v_res_1643_; 
v_x_2581__boxed_1642_ = lean_unbox_usize(v_x_1640_);
lean_dec(v_x_1640_);
v_res_1643_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0(v_00_u03b2_1638_, v_x_1639_, v_x_2581__boxed_1642_, v_x_1641_);
lean_dec_ref(v_x_1641_);
lean_dec_ref(v_x_1639_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2(lean_object* v_00_u03b2_1644_, lean_object* v_x_1645_, size_t v_x_1646_, size_t v_x_1647_, lean_object* v_x_1648_, lean_object* v_x_1649_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(v_x_1645_, v_x_1646_, v_x_1647_, v_x_1648_, v_x_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1651_, lean_object* v_x_1652_, lean_object* v_x_1653_, lean_object* v_x_1654_, lean_object* v_x_1655_, lean_object* v_x_1656_){
_start:
{
size_t v_x_2592__boxed_1657_; size_t v_x_2593__boxed_1658_; lean_object* v_res_1659_; 
v_x_2592__boxed_1657_ = lean_unbox_usize(v_x_1653_);
lean_dec(v_x_1653_);
v_x_2593__boxed_1658_ = lean_unbox_usize(v_x_1654_);
lean_dec(v_x_1654_);
v_res_1659_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2(v_00_u03b2_1651_, v_x_1652_, v_x_2592__boxed_1657_, v_x_2593__boxed_1658_, v_x_1655_, v_x_1656_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1660_, lean_object* v_keys_1661_, lean_object* v_vals_1662_, lean_object* v_heq_1663_, lean_object* v_i_1664_, lean_object* v_k_1665_){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1661_, v_vals_1662_, v_i_1664_, v_k_1665_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1667_, lean_object* v_keys_1668_, lean_object* v_vals_1669_, lean_object* v_heq_1670_, lean_object* v_i_1671_, lean_object* v_k_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1667_, v_keys_1668_, v_vals_1669_, v_heq_1670_, v_i_1671_, v_k_1672_);
lean_dec_ref(v_k_1672_);
lean_dec_ref(v_vals_1669_);
lean_dec_ref(v_keys_1668_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1674_, lean_object* v_n_1675_, lean_object* v_k_1676_, lean_object* v_v_1677_){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4___redArg(v_n_1675_, v_k_1676_, v_v_1677_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1679_, size_t v_depth_1680_, lean_object* v_keys_1681_, lean_object* v_vals_1682_, lean_object* v_heq_1683_, lean_object* v_i_1684_, lean_object* v_entries_1685_){
_start:
{
lean_object* v___x_1686_; 
v___x_1686_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___redArg(v_depth_1680_, v_keys_1681_, v_vals_1682_, v_i_1684_, v_entries_1685_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1687_, lean_object* v_depth_1688_, lean_object* v_keys_1689_, lean_object* v_vals_1690_, lean_object* v_heq_1691_, lean_object* v_i_1692_, lean_object* v_entries_1693_){
_start:
{
size_t v_depth_boxed_1694_; lean_object* v_res_1695_; 
v_depth_boxed_1694_ = lean_unbox_usize(v_depth_1688_);
lean_dec(v_depth_1688_);
v_res_1695_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5(v_00_u03b2_1687_, v_depth_boxed_1694_, v_keys_1689_, v_vals_1690_, v_heq_1691_, v_i_1692_, v_entries_1693_);
lean_dec_ref(v_vals_1690_);
lean_dec_ref(v_keys_1689_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_1696_, lean_object* v_x_1697_, lean_object* v_x_1698_, lean_object* v_x_1699_, lean_object* v_x_1700_){
_start:
{
lean_object* v___x_1701_; 
v___x_1701_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_x_1697_, v_x_1698_, v_x_1699_, v_x_1700_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__0(lean_object* v_val_1702_, lean_object* v___x_1703_, lean_object* v_s_1704_){
_start:
{
lean_object* v_exp_1705_; lean_object* v_rings_1706_; lean_object* v_semirings_1707_; lean_object* v_ncRings_1708_; lean_object* v_ncSemirings_1709_; lean_object* v_typeClassify_1710_; lean_object* v_orders_1711_; lean_object* v_typeOrderClassify_1712_; lean_object* v___x_1713_; uint8_t v___x_1714_; 
v_exp_1705_ = lean_ctor_get(v_s_1704_, 0);
v_rings_1706_ = lean_ctor_get(v_s_1704_, 1);
v_semirings_1707_ = lean_ctor_get(v_s_1704_, 2);
v_ncRings_1708_ = lean_ctor_get(v_s_1704_, 3);
v_ncSemirings_1709_ = lean_ctor_get(v_s_1704_, 4);
v_typeClassify_1710_ = lean_ctor_get(v_s_1704_, 5);
v_orders_1711_ = lean_ctor_get(v_s_1704_, 6);
v_typeOrderClassify_1712_ = lean_ctor_get(v_s_1704_, 7);
v___x_1713_ = lean_array_get_size(v_rings_1706_);
v___x_1714_ = lean_nat_dec_lt(v_val_1702_, v___x_1713_);
if (v___x_1714_ == 0)
{
lean_dec(v___x_1703_);
return v_s_1704_;
}
else
{
lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1742_; 
lean_inc_ref(v_typeOrderClassify_1712_);
lean_inc_ref(v_orders_1711_);
lean_inc_ref(v_typeClassify_1710_);
lean_inc_ref(v_ncSemirings_1709_);
lean_inc_ref(v_ncRings_1708_);
lean_inc_ref(v_semirings_1707_);
lean_inc_ref(v_rings_1706_);
lean_inc(v_exp_1705_);
v_isSharedCheck_1742_ = !lean_is_exclusive(v_s_1704_);
if (v_isSharedCheck_1742_ == 0)
{
lean_object* v_unused_1743_; lean_object* v_unused_1744_; lean_object* v_unused_1745_; lean_object* v_unused_1746_; lean_object* v_unused_1747_; lean_object* v_unused_1748_; lean_object* v_unused_1749_; lean_object* v_unused_1750_; 
v_unused_1743_ = lean_ctor_get(v_s_1704_, 7);
lean_dec(v_unused_1743_);
v_unused_1744_ = lean_ctor_get(v_s_1704_, 6);
lean_dec(v_unused_1744_);
v_unused_1745_ = lean_ctor_get(v_s_1704_, 5);
lean_dec(v_unused_1745_);
v_unused_1746_ = lean_ctor_get(v_s_1704_, 4);
lean_dec(v_unused_1746_);
v_unused_1747_ = lean_ctor_get(v_s_1704_, 3);
lean_dec(v_unused_1747_);
v_unused_1748_ = lean_ctor_get(v_s_1704_, 2);
lean_dec(v_unused_1748_);
v_unused_1749_ = lean_ctor_get(v_s_1704_, 1);
lean_dec(v_unused_1749_);
v_unused_1750_ = lean_ctor_get(v_s_1704_, 0);
lean_dec(v_unused_1750_);
v___x_1716_ = v_s_1704_;
v_isShared_1717_ = v_isSharedCheck_1742_;
goto v_resetjp_1715_;
}
else
{
lean_dec(v_s_1704_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1742_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v_v_1718_; lean_object* v_toRing_1719_; lean_object* v_invFn_x3f_1720_; lean_object* v_divFn_x3f_1721_; lean_object* v_commSemiringInst_1722_; lean_object* v_commRingInst_1723_; lean_object* v_noZeroDivInst_x3f_1724_; lean_object* v_fieldInst_x3f_1725_; lean_object* v_powIdentityInst_x3f_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1740_; 
v_v_1718_ = lean_array_fget(v_rings_1706_, v_val_1702_);
v_toRing_1719_ = lean_ctor_get(v_v_1718_, 0);
v_invFn_x3f_1720_ = lean_ctor_get(v_v_1718_, 1);
v_divFn_x3f_1721_ = lean_ctor_get(v_v_1718_, 2);
v_commSemiringInst_1722_ = lean_ctor_get(v_v_1718_, 4);
v_commRingInst_1723_ = lean_ctor_get(v_v_1718_, 5);
v_noZeroDivInst_x3f_1724_ = lean_ctor_get(v_v_1718_, 6);
v_fieldInst_x3f_1725_ = lean_ctor_get(v_v_1718_, 7);
v_powIdentityInst_x3f_1726_ = lean_ctor_get(v_v_1718_, 8);
v_isSharedCheck_1740_ = !lean_is_exclusive(v_v_1718_);
if (v_isSharedCheck_1740_ == 0)
{
lean_object* v_unused_1741_; 
v_unused_1741_ = lean_ctor_get(v_v_1718_, 3);
lean_dec(v_unused_1741_);
v___x_1728_ = v_v_1718_;
v_isShared_1729_ = v_isSharedCheck_1740_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_powIdentityInst_x3f_1726_);
lean_inc(v_fieldInst_x3f_1725_);
lean_inc(v_noZeroDivInst_x3f_1724_);
lean_inc(v_commRingInst_1723_);
lean_inc(v_commSemiringInst_1722_);
lean_inc(v_divFn_x3f_1721_);
lean_inc(v_invFn_x3f_1720_);
lean_inc(v_toRing_1719_);
lean_dec(v_v_1718_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1740_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1730_; lean_object* v_xs_x27_1731_; lean_object* v___x_1732_; lean_object* v___x_1734_; 
v___x_1730_ = lean_box(0);
v_xs_x27_1731_ = lean_array_fset(v_rings_1706_, v_val_1702_, v___x_1730_);
v___x_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1703_);
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 3, v___x_1732_);
v___x_1734_ = v___x_1728_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_toRing_1719_);
lean_ctor_set(v_reuseFailAlloc_1739_, 1, v_invFn_x3f_1720_);
lean_ctor_set(v_reuseFailAlloc_1739_, 2, v_divFn_x3f_1721_);
lean_ctor_set(v_reuseFailAlloc_1739_, 3, v___x_1732_);
lean_ctor_set(v_reuseFailAlloc_1739_, 4, v_commSemiringInst_1722_);
lean_ctor_set(v_reuseFailAlloc_1739_, 5, v_commRingInst_1723_);
lean_ctor_set(v_reuseFailAlloc_1739_, 6, v_noZeroDivInst_x3f_1724_);
lean_ctor_set(v_reuseFailAlloc_1739_, 7, v_fieldInst_x3f_1725_);
lean_ctor_set(v_reuseFailAlloc_1739_, 8, v_powIdentityInst_x3f_1726_);
v___x_1734_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
lean_object* v___x_1735_; lean_object* v___x_1737_; 
v___x_1735_ = lean_array_fset(v_xs_x27_1731_, v_val_1702_, v___x_1734_);
if (v_isShared_1717_ == 0)
{
lean_ctor_set(v___x_1716_, 1, v___x_1735_);
v___x_1737_ = v___x_1716_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_exp_1705_);
lean_ctor_set(v_reuseFailAlloc_1738_, 1, v___x_1735_);
lean_ctor_set(v_reuseFailAlloc_1738_, 2, v_semirings_1707_);
lean_ctor_set(v_reuseFailAlloc_1738_, 3, v_ncRings_1708_);
lean_ctor_set(v_reuseFailAlloc_1738_, 4, v_ncSemirings_1709_);
lean_ctor_set(v_reuseFailAlloc_1738_, 5, v_typeClassify_1710_);
lean_ctor_set(v_reuseFailAlloc_1738_, 6, v_orders_1711_);
lean_ctor_set(v_reuseFailAlloc_1738_, 7, v_typeOrderClassify_1712_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__0___boxed(lean_object* v_val_1751_, lean_object* v___x_1752_, lean_object* v_s_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__0(v_val_1751_, v___x_1752_, v_s_1753_);
lean_dec(v_val_1751_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__1(lean_object* v___x_1755_, lean_object* v_s_1756_){
_start:
{
lean_object* v_exp_1757_; lean_object* v_rings_1758_; lean_object* v_semirings_1759_; lean_object* v_ncRings_1760_; lean_object* v_ncSemirings_1761_; lean_object* v_typeClassify_1762_; lean_object* v_orders_1763_; lean_object* v_typeOrderClassify_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1772_; 
v_exp_1757_ = lean_ctor_get(v_s_1756_, 0);
v_rings_1758_ = lean_ctor_get(v_s_1756_, 1);
v_semirings_1759_ = lean_ctor_get(v_s_1756_, 2);
v_ncRings_1760_ = lean_ctor_get(v_s_1756_, 3);
v_ncSemirings_1761_ = lean_ctor_get(v_s_1756_, 4);
v_typeClassify_1762_ = lean_ctor_get(v_s_1756_, 5);
v_orders_1763_ = lean_ctor_get(v_s_1756_, 6);
v_typeOrderClassify_1764_ = lean_ctor_get(v_s_1756_, 7);
v_isSharedCheck_1772_ = !lean_is_exclusive(v_s_1756_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1766_ = v_s_1756_;
v_isShared_1767_ = v_isSharedCheck_1772_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_typeOrderClassify_1764_);
lean_inc(v_orders_1763_);
lean_inc(v_typeClassify_1762_);
lean_inc(v_ncSemirings_1761_);
lean_inc(v_ncRings_1760_);
lean_inc(v_semirings_1759_);
lean_inc(v_rings_1758_);
lean_inc(v_exp_1757_);
lean_dec(v_s_1756_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1772_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1768_; lean_object* v___x_1770_; 
v___x_1768_ = lean_array_push(v_semirings_1759_, v___x_1755_);
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 2, v___x_1768_);
v___x_1770_ = v___x_1766_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_exp_1757_);
lean_ctor_set(v_reuseFailAlloc_1771_, 1, v_rings_1758_);
lean_ctor_set(v_reuseFailAlloc_1771_, 2, v___x_1768_);
lean_ctor_set(v_reuseFailAlloc_1771_, 3, v_ncRings_1760_);
lean_ctor_set(v_reuseFailAlloc_1771_, 4, v_ncSemirings_1761_);
lean_ctor_set(v_reuseFailAlloc_1771_, 5, v_typeClassify_1762_);
lean_ctor_set(v_reuseFailAlloc_1771_, 6, v_orders_1763_);
lean_ctor_set(v_reuseFailAlloc_1771_, 7, v_typeOrderClassify_1764_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1(void){
_start:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1774_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__0));
v___x_1775_ = l_Lean_stringToMessageData(v___x_1774_);
return v___x_1775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f(lean_object* v_type_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_){
_start:
{
lean_object* v___x_1787_; 
lean_inc_ref(v_type_1776_);
v___x_1787_ = l_Lean_Meta_getDecLevel_x3f(v_type_1776_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1924_; 
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1790_ = v___x_1787_;
v_isShared_1791_ = v_isSharedCheck_1924_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1787_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1924_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
if (lean_obj_tag(v_a_1788_) == 1)
{
lean_object* v_val_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
lean_del_object(v___x_1790_);
v_val_1792_ = lean_ctor_get(v_a_1788_, 0);
lean_inc_n(v_val_1792_, 2);
lean_dec_ref_known(v_a_1788_, 1);
v___x_1793_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__18));
v___x_1794_ = lean_box(0);
v___x_1795_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1795_, 0, v_val_1792_);
lean_ctor_set(v___x_1795_, 1, v___x_1794_);
lean_inc_ref(v___x_1795_);
v___x_1796_ = l_Lean_mkConst(v___x_1793_, v___x_1795_);
lean_inc_ref(v_type_1776_);
v___x_1797_ = l_Lean_Expr_app___override(v___x_1796_, v_type_1776_);
v___x_1798_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1797_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_);
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1911_; 
v_a_1799_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1801_ = v___x_1798_;
v_isShared_1802_ = v_isSharedCheck_1911_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1798_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1911_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
if (lean_obj_tag(v_a_1799_) == 1)
{
lean_object* v_val_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
lean_del_object(v___x_1801_);
v_val_1803_ = lean_ctor_get(v_a_1799_, 0);
lean_inc_n(v_val_1803_, 2);
lean_dec_ref_known(v_a_1799_, 1);
v___x_1804_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2));
lean_inc_ref(v___x_1795_);
v___x_1805_ = l_Lean_mkConst(v___x_1804_, v___x_1795_);
lean_inc_ref_n(v_type_1776_, 2);
v___x_1806_ = l_Lean_mkAppB(v___x_1805_, v_type_1776_, v_val_1803_);
v___x_1807_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1));
v___x_1808_ = l_Lean_mkConst(v___x_1807_, v___x_1795_);
lean_inc_ref(v___x_1806_);
v___x_1809_ = l_Lean_mkAppB(v___x_1808_, v_type_1776_, v___x_1806_);
v___x_1810_ = l_Lean_Meta_Sym_canon(v___x_1809_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_a_1811_; lean_object* v___x_1812_; 
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
lean_inc(v_a_1811_);
lean_dec_ref_known(v___x_1810_, 1);
v___x_1812_ = l_Lean_Meta_Sym_shareCommon(v_a_1811_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v_a_1813_; lean_object* v___x_1814_; 
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
lean_inc_n(v_a_1813_, 2);
lean_dec_ref_known(v___x_1812_, 1);
v___x_1814_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f(v_a_1813_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; 
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
lean_inc(v_a_1815_);
lean_dec_ref_known(v___x_1814_, 1);
if (lean_obj_tag(v_a_1815_) == 1)
{
lean_object* v_val_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1867_; 
lean_dec(v_a_1813_);
v_val_1816_ = lean_ctor_get(v_a_1815_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v_a_1815_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1818_ = v_a_1815_;
v_isShared_1819_ = v_isSharedCheck_1867_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_val_1816_);
lean_dec(v_a_1815_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1867_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1820_; 
v___x_1820_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_1778_, v_a_1781_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v_a_1821_; lean_object* v_semirings_1822_; lean_object* v___x_1823_; lean_object* v___f_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___f_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
v_a_1821_ = lean_ctor_get(v___x_1820_, 0);
lean_inc(v_a_1821_);
lean_dec_ref_known(v___x_1820_, 1);
v_semirings_1822_ = lean_ctor_get(v_a_1821_, 2);
lean_inc_ref(v_semirings_1822_);
lean_dec(v_a_1821_);
v___x_1823_ = lean_array_get_size(v_semirings_1822_);
lean_dec_ref(v_semirings_1822_);
lean_inc(v_val_1816_);
v___f_1824_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1824_, 0, v_val_1816_);
lean_closure_set(v___f_1824_, 1, v___x_1823_);
v___x_1825_ = lean_box(0);
v___x_1826_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1823_);
lean_ctor_set(v___x_1826_, 1, v_type_1776_);
lean_ctor_set(v___x_1826_, 2, v_val_1792_);
lean_ctor_set(v___x_1826_, 3, v___x_1806_);
lean_ctor_set(v___x_1826_, 4, v___x_1825_);
lean_ctor_set(v___x_1826_, 5, v___x_1825_);
lean_ctor_set(v___x_1826_, 6, v___x_1825_);
lean_ctor_set(v___x_1826_, 7, v___x_1825_);
lean_ctor_set(v___x_1826_, 8, v___x_1825_);
v___x_1827_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1826_);
lean_ctor_set(v___x_1827_, 1, v_val_1816_);
lean_ctor_set(v___x_1827_, 2, v_val_1803_);
lean_ctor_set(v___x_1827_, 3, v___x_1825_);
lean_ctor_set(v___x_1827_, 4, v___x_1825_);
v___f_1828_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__1), 2, 1);
lean_closure_set(v___f_1828_, 0, v___x_1827_);
v___x_1829_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_1830_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_1829_, v___f_1828_, v_a_1778_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v___x_1831_; 
lean_dec_ref_known(v___x_1830_, 1);
v___x_1831_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_1829_, v___f_1824_, v_a_1778_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1841_; 
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1841_ == 0)
{
lean_object* v_unused_1842_; 
v_unused_1842_ = lean_ctor_get(v___x_1831_, 0);
lean_dec(v_unused_1842_);
v___x_1833_ = v___x_1831_;
v_isShared_1834_ = v_isSharedCheck_1841_;
goto v_resetjp_1832_;
}
else
{
lean_dec(v___x_1831_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1841_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1836_; 
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 0, v___x_1823_);
v___x_1836_ = v___x_1818_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1823_);
v___x_1836_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
lean_object* v___x_1838_; 
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 0, v___x_1836_);
v___x_1838_ = v___x_1833_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1836_);
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
else
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1850_; 
lean_del_object(v___x_1818_);
v_a_1843_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1845_ = v___x_1831_;
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1831_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1848_; 
if (v_isShared_1846_ == 0)
{
v___x_1848_ = v___x_1845_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_a_1843_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
}
else
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
lean_dec_ref(v___f_1824_);
lean_del_object(v___x_1818_);
v_a_1851_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1853_ = v___x_1830_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1830_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_a_1851_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
else
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
lean_del_object(v___x_1818_);
lean_dec(v_val_1816_);
lean_dec_ref(v___x_1806_);
lean_dec(v_val_1803_);
lean_dec(v_val_1792_);
lean_dec_ref(v_type_1776_);
v_a_1859_ = lean_ctor_get(v___x_1820_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___x_1820_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1820_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
if (v_isShared_1862_ == 0)
{
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1859_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
}
}
else
{
lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
lean_dec(v_a_1815_);
lean_dec_ref(v___x_1806_);
lean_dec(v_val_1803_);
lean_dec(v_val_1792_);
lean_dec_ref(v_type_1776_);
v___x_1868_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1);
v___x_1869_ = l_Lean_indentExpr(v_a_1813_);
v___x_1870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1868_);
lean_ctor_set(v___x_1870_, 1, v___x_1869_);
v___x_1871_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1777_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v_a_1872_; uint8_t v_verbose_1873_; 
v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
lean_inc(v_a_1872_);
lean_dec_ref_known(v___x_1871_, 1);
v_verbose_1873_ = lean_ctor_get_uint8(v_a_1872_, 0);
lean_dec(v_a_1872_);
if (v_verbose_1873_ == 0)
{
lean_dec_ref_known(v___x_1870_, 2);
goto v___jp_1784_;
}
else
{
lean_object* v___x_1874_; 
v___x_1874_ = l_Lean_Meta_Sym_reportIssue(v___x_1870_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_dec_ref_known(v___x_1874_, 1);
goto v___jp_1784_;
}
else
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1882_; 
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1877_ = v___x_1874_;
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1874_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1880_; 
if (v_isShared_1878_ == 0)
{
v___x_1880_ = v___x_1877_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_a_1875_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
}
}
else
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1890_; 
lean_dec_ref_known(v___x_1870_, 2);
v_a_1883_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1885_ = v___x_1871_;
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1871_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1886_ == 0)
{
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_a_1883_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
}
}
else
{
lean_dec(v_a_1813_);
lean_dec_ref(v___x_1806_);
lean_dec(v_val_1803_);
lean_dec(v_val_1792_);
lean_dec_ref(v_type_1776_);
return v___x_1814_;
}
}
else
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
lean_dec_ref(v___x_1806_);
lean_dec(v_val_1803_);
lean_dec(v_val_1792_);
lean_dec_ref(v_type_1776_);
v_a_1891_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1893_ = v___x_1812_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1812_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1891_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
else
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1906_; 
lean_dec_ref(v___x_1806_);
lean_dec(v_val_1803_);
lean_dec(v_val_1792_);
lean_dec_ref(v_type_1776_);
v_a_1899_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1901_ = v___x_1810_;
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1810_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1904_; 
if (v_isShared_1902_ == 0)
{
v___x_1904_ = v___x_1901_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_a_1899_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
}
else
{
lean_object* v___x_1907_; lean_object* v___x_1909_; 
lean_dec(v_a_1799_);
lean_dec_ref_known(v___x_1795_, 2);
lean_dec(v_val_1792_);
lean_dec_ref(v_type_1776_);
v___x_1907_ = lean_box(0);
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 0, v___x_1907_);
v___x_1909_ = v___x_1801_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1907_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
else
{
lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1919_; 
lean_dec_ref_known(v___x_1795_, 2);
lean_dec(v_val_1792_);
lean_dec_ref(v_type_1776_);
v_a_1912_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1914_ = v___x_1798_;
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_dec(v___x_1798_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1917_; 
if (v_isShared_1915_ == 0)
{
v___x_1917_ = v___x_1914_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1912_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
}
else
{
lean_object* v___x_1920_; lean_object* v___x_1922_; 
lean_dec(v_a_1788_);
lean_dec_ref(v_type_1776_);
v___x_1920_ = lean_box(0);
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 0, v___x_1920_);
v___x_1922_ = v___x_1790_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v___x_1920_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
else
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1932_; 
lean_dec_ref(v_type_1776_);
v_a_1925_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1927_ = v___x_1787_;
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1787_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1930_; 
if (v_isShared_1928_ == 0)
{
v___x_1930_ = v___x_1927_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_a_1925_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
v___jp_1784_:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1785_ = lean_box(0);
v___x_1786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1785_);
return v___x_1786_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___boxed(lean_object* v_type_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f(v_type_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_);
lean_dec(v_a_1939_);
lean_dec_ref(v_a_1938_);
lean_dec(v_a_1937_);
lean_dec_ref(v_a_1936_);
lean_dec(v_a_1935_);
lean_dec_ref(v_a_1934_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___lam__0(lean_object* v___x_1942_, lean_object* v_s_1943_){
_start:
{
lean_object* v_exp_1944_; lean_object* v_rings_1945_; lean_object* v_semirings_1946_; lean_object* v_ncRings_1947_; lean_object* v_ncSemirings_1948_; lean_object* v_typeClassify_1949_; lean_object* v_orders_1950_; lean_object* v_typeOrderClassify_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1959_; 
v_exp_1944_ = lean_ctor_get(v_s_1943_, 0);
v_rings_1945_ = lean_ctor_get(v_s_1943_, 1);
v_semirings_1946_ = lean_ctor_get(v_s_1943_, 2);
v_ncRings_1947_ = lean_ctor_get(v_s_1943_, 3);
v_ncSemirings_1948_ = lean_ctor_get(v_s_1943_, 4);
v_typeClassify_1949_ = lean_ctor_get(v_s_1943_, 5);
v_orders_1950_ = lean_ctor_get(v_s_1943_, 6);
v_typeOrderClassify_1951_ = lean_ctor_get(v_s_1943_, 7);
v_isSharedCheck_1959_ = !lean_is_exclusive(v_s_1943_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1953_ = v_s_1943_;
v_isShared_1954_ = v_isSharedCheck_1959_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_typeOrderClassify_1951_);
lean_inc(v_orders_1950_);
lean_inc(v_typeClassify_1949_);
lean_inc(v_ncSemirings_1948_);
lean_inc(v_ncRings_1947_);
lean_inc(v_semirings_1946_);
lean_inc(v_rings_1945_);
lean_inc(v_exp_1944_);
lean_dec(v_s_1943_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1959_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1955_; lean_object* v___x_1957_; 
v___x_1955_ = lean_array_push(v_ncSemirings_1948_, v___x_1942_);
if (v_isShared_1954_ == 0)
{
lean_ctor_set(v___x_1953_, 4, v___x_1955_);
v___x_1957_ = v___x_1953_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_exp_1944_);
lean_ctor_set(v_reuseFailAlloc_1958_, 1, v_rings_1945_);
lean_ctor_set(v_reuseFailAlloc_1958_, 2, v_semirings_1946_);
lean_ctor_set(v_reuseFailAlloc_1958_, 3, v_ncRings_1947_);
lean_ctor_set(v_reuseFailAlloc_1958_, 4, v___x_1955_);
lean_ctor_set(v_reuseFailAlloc_1958_, 5, v_typeClassify_1949_);
lean_ctor_set(v_reuseFailAlloc_1958_, 6, v_orders_1950_);
lean_ctor_set(v_reuseFailAlloc_1958_, 7, v_typeOrderClassify_1951_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg(lean_object* v_type_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_){
_start:
{
lean_object* v___x_1967_; 
lean_inc_ref(v_type_1960_);
v___x_1967_ = l_Lean_Meta_getDecLevel_x3f(v_type_1960_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_2041_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_1970_ = v___x_1967_;
v_isShared_1971_ = v_isSharedCheck_2041_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_a_1968_);
lean_dec(v___x_1967_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_2041_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
if (lean_obj_tag(v_a_1968_) == 1)
{
lean_object* v_val_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
lean_del_object(v___x_1970_);
v_val_1972_ = lean_ctor_get(v_a_1968_, 0);
lean_inc_n(v_val_1972_, 2);
lean_dec_ref_known(v_a_1968_, 1);
v___x_1973_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__16));
v___x_1974_ = lean_box(0);
v___x_1975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1975_, 0, v_val_1972_);
lean_ctor_set(v___x_1975_, 1, v___x_1974_);
v___x_1976_ = l_Lean_mkConst(v___x_1973_, v___x_1975_);
lean_inc_ref(v_type_1960_);
v___x_1977_ = l_Lean_Expr_app___override(v___x_1976_, v_type_1960_);
v___x_1978_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1977_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_a_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_2028_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_1981_ = v___x_1978_;
v_isShared_1982_ = v_isSharedCheck_2028_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_a_1979_);
lean_dec(v___x_1978_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_2028_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
if (lean_obj_tag(v_a_1979_) == 1)
{
lean_object* v_val_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_2023_; 
lean_del_object(v___x_1981_);
v_val_1983_ = lean_ctor_get(v_a_1979_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v_a_1979_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_1985_ = v_a_1979_;
v_isShared_1986_ = v_isSharedCheck_2023_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_val_1983_);
lean_dec(v_a_1979_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_2023_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1987_; 
v___x_1987_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_1961_, v_a_1964_);
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_object* v_a_1988_; lean_object* v_ncSemirings_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___f_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
lean_inc(v_a_1988_);
lean_dec_ref_known(v___x_1987_, 1);
v_ncSemirings_1989_ = lean_ctor_get(v_a_1988_, 4);
lean_inc_ref(v_ncSemirings_1989_);
lean_dec(v_a_1988_);
v___x_1990_ = lean_array_get_size(v_ncSemirings_1989_);
lean_dec_ref(v_ncSemirings_1989_);
v___x_1991_ = lean_box(0);
v___x_1992_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1990_);
lean_ctor_set(v___x_1992_, 1, v_type_1960_);
lean_ctor_set(v___x_1992_, 2, v_val_1972_);
lean_ctor_set(v___x_1992_, 3, v_val_1983_);
lean_ctor_set(v___x_1992_, 4, v___x_1991_);
lean_ctor_set(v___x_1992_, 5, v___x_1991_);
lean_ctor_set(v___x_1992_, 6, v___x_1991_);
lean_ctor_set(v___x_1992_, 7, v___x_1991_);
lean_ctor_set(v___x_1992_, 8, v___x_1991_);
v___f_1993_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1993_, 0, v___x_1992_);
v___x_1994_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_1995_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_1994_, v___f_1993_, v_a_1961_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2005_; 
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2005_ == 0)
{
lean_object* v_unused_2006_; 
v_unused_2006_ = lean_ctor_get(v___x_1995_, 0);
lean_dec(v_unused_2006_);
v___x_1997_ = v___x_1995_;
v_isShared_1998_ = v_isSharedCheck_2005_;
goto v_resetjp_1996_;
}
else
{
lean_dec(v___x_1995_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2005_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_2000_; 
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 0, v___x_1990_);
v___x_2000_ = v___x_1985_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v___x_1990_);
v___x_2000_ = v_reuseFailAlloc_2004_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
lean_object* v___x_2002_; 
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 0, v___x_2000_);
v___x_2002_ = v___x_1997_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_2000_);
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
else
{
lean_object* v_a_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2014_; 
lean_del_object(v___x_1985_);
v_a_2007_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_2009_ = v___x_1995_;
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_a_2007_);
lean_dec(v___x_1995_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2012_; 
if (v_isShared_2010_ == 0)
{
v___x_2012_ = v___x_2009_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_a_2007_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
}
else
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2022_; 
lean_del_object(v___x_1985_);
lean_dec(v_val_1983_);
lean_dec(v_val_1972_);
lean_dec_ref(v_type_1960_);
v_a_2015_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2017_ = v___x_1987_;
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v___x_1987_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2020_; 
if (v_isShared_2018_ == 0)
{
v___x_2020_ = v___x_2017_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_a_2015_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
}
}
else
{
lean_object* v___x_2024_; lean_object* v___x_2026_; 
lean_dec(v_a_1979_);
lean_dec(v_val_1972_);
lean_dec_ref(v_type_1960_);
v___x_2024_ = lean_box(0);
if (v_isShared_1982_ == 0)
{
lean_ctor_set(v___x_1981_, 0, v___x_2024_);
v___x_2026_ = v___x_1981_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2024_);
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
else
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
lean_dec(v_val_1972_);
lean_dec_ref(v_type_1960_);
v_a_2029_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_1978_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_1978_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
else
{
lean_object* v___x_2037_; lean_object* v___x_2039_; 
lean_dec(v_a_1968_);
lean_dec_ref(v_type_1960_);
v___x_2037_ = lean_box(0);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 0, v___x_2037_);
v___x_2039_ = v___x_1970_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2037_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
}
else
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2049_; 
lean_dec_ref(v_type_1960_);
v_a_2042_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2044_ = v___x_1967_;
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_1967_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2047_; 
if (v_isShared_2045_ == 0)
{
v___x_2047_ = v___x_2044_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_a_2042_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___boxed(lean_object* v_type_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_){
_start:
{
lean_object* v_res_2057_; 
v_res_2057_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg(v_type_2050_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_);
lean_dec(v_a_2055_);
lean_dec_ref(v_a_2054_);
lean_dec(v_a_2053_);
lean_dec_ref(v_a_2052_);
lean_dec(v_a_2051_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f(lean_object* v_type_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_){
_start:
{
lean_object* v___x_2066_; 
v___x_2066_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg(v_type_2058_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___boxed(lean_object* v_type_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f(v_type_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_);
lean_dec(v_a_2073_);
lean_dec_ref(v_a_2072_);
lean_dec(v_a_2071_);
lean_dec_ref(v_a_2070_);
lean_dec(v_a_2069_);
lean_dec_ref(v_a_2068_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_classify_x3f_go(lean_object* v_type_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_){
_start:
{
lean_object* v___x_2084_; 
lean_inc_ref(v_type_2076_);
v___x_2084_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f(v_type_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2179_; 
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2087_ = v___x_2084_;
v_isShared_2088_ = v_isSharedCheck_2179_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2084_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2179_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
if (lean_obj_tag(v_a_2085_) == 1)
{
lean_object* v_val_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2099_; 
lean_dec_ref(v_type_2076_);
v_val_2089_ = lean_ctor_get(v_a_2085_, 0);
v_isSharedCheck_2099_ = !lean_is_exclusive(v_a_2085_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2091_ = v_a_2085_;
v_isShared_2092_ = v_isSharedCheck_2099_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_val_2089_);
lean_dec(v_a_2085_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2099_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2092_ == 0)
{
lean_ctor_set_tag(v___x_2091_, 0);
v___x_2094_ = v___x_2091_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_val_2089_);
v___x_2094_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
lean_object* v___x_2096_; 
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 0, v___x_2094_);
v___x_2096_ = v___x_2087_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v___x_2094_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
else
{
lean_object* v___x_2100_; 
lean_del_object(v___x_2087_);
lean_dec(v_a_2085_);
lean_inc_ref(v_type_2076_);
v___x_2100_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f(v_type_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_a_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2170_; 
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2103_ = v___x_2100_;
v_isShared_2104_ = v_isSharedCheck_2170_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_a_2101_);
lean_dec(v___x_2100_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2170_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
if (lean_obj_tag(v_a_2101_) == 1)
{
lean_object* v_val_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2115_; 
lean_dec_ref(v_type_2076_);
v_val_2105_ = lean_ctor_get(v_a_2101_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v_a_2101_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2107_ = v_a_2101_;
v_isShared_2108_ = v_isSharedCheck_2115_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_val_2105_);
lean_dec(v_a_2101_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2115_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_val_2105_);
v___x_2110_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
lean_object* v___x_2112_; 
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 0, v___x_2110_);
v___x_2112_ = v___x_2103_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v___x_2110_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
}
else
{
lean_object* v___x_2116_; 
lean_del_object(v___x_2103_);
lean_dec(v_a_2101_);
lean_inc_ref(v_type_2076_);
v___x_2116_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f(v_type_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2161_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2119_ = v___x_2116_;
v_isShared_2120_ = v_isSharedCheck_2161_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_a_2117_);
lean_dec(v___x_2116_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2161_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
if (lean_obj_tag(v_a_2117_) == 1)
{
lean_object* v_val_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2131_; 
lean_dec_ref(v_type_2076_);
v_val_2121_ = lean_ctor_get(v_a_2117_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v_a_2117_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2123_ = v_a_2117_;
v_isShared_2124_ = v_isSharedCheck_2131_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_val_2121_);
lean_dec(v_a_2117_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2131_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2126_; 
if (v_isShared_2124_ == 0)
{
lean_ctor_set_tag(v___x_2123_, 2);
v___x_2126_ = v___x_2123_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_val_2121_);
v___x_2126_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
lean_object* v___x_2128_; 
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 0, v___x_2126_);
v___x_2128_ = v___x_2119_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2126_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
}
else
{
lean_object* v___x_2132_; 
lean_del_object(v___x_2119_);
lean_dec(v_a_2117_);
v___x_2132_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg(v_type_2076_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2152_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2135_ = v___x_2132_;
v_isShared_2136_ = v_isSharedCheck_2152_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2132_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2152_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
if (lean_obj_tag(v_a_2133_) == 1)
{
lean_object* v_val_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2147_; 
v_val_2137_ = lean_ctor_get(v_a_2133_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v_a_2133_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2139_ = v_a_2133_;
v_isShared_2140_ = v_isSharedCheck_2147_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_val_2137_);
lean_dec(v_a_2133_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2147_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
lean_ctor_set_tag(v___x_2139_, 3);
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_val_2137_);
v___x_2142_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
lean_object* v___x_2144_; 
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 0, v___x_2142_);
v___x_2144_ = v___x_2135_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2142_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
}
else
{
lean_object* v___x_2148_; lean_object* v___x_2150_; 
lean_dec(v_a_2133_);
v___x_2148_ = lean_box(4);
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 0, v___x_2148_);
v___x_2150_ = v___x_2135_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v___x_2148_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
}
else
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2160_; 
v_a_2153_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2155_ = v___x_2132_;
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2132_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
if (v_isShared_2156_ == 0)
{
v___x_2158_ = v___x_2155_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_a_2153_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
}
}
}
else
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2169_; 
lean_dec_ref(v_type_2076_);
v_a_2162_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2164_ = v___x_2116_;
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2116_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2167_; 
if (v_isShared_2165_ == 0)
{
v___x_2167_ = v___x_2164_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2162_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
}
}
}
else
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2178_; 
lean_dec_ref(v_type_2076_);
v_a_2171_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2173_ = v___x_2100_;
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2100_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2176_; 
if (v_isShared_2174_ == 0)
{
v___x_2176_ = v___x_2173_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_a_2171_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
}
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
lean_dec_ref(v_type_2076_);
v_a_2180_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_2084_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2084_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
if (v_isShared_2183_ == 0)
{
v___x_2185_ = v___x_2182_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_classify_x3f_go___boxed(lean_object* v_type_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_){
_start:
{
lean_object* v_res_2196_; 
v_res_2196_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_classify_x3f_go(v_type_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_);
lean_dec(v_a_2194_);
lean_dec_ref(v_a_2193_);
lean_dec(v_a_2192_);
lean_dec_ref(v_a_2191_);
lean_dec(v_a_2190_);
lean_dec_ref(v_a_2189_);
return v_res_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classify_x3f___lam__0(lean_object* v_type_2197_, lean_object* v_a_2198_, lean_object* v_s_2199_){
_start:
{
lean_object* v_exp_2200_; lean_object* v_rings_2201_; lean_object* v_semirings_2202_; lean_object* v_ncRings_2203_; lean_object* v_ncSemirings_2204_; lean_object* v_typeClassify_2205_; lean_object* v_orders_2206_; lean_object* v_typeOrderClassify_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2215_; 
v_exp_2200_ = lean_ctor_get(v_s_2199_, 0);
v_rings_2201_ = lean_ctor_get(v_s_2199_, 1);
v_semirings_2202_ = lean_ctor_get(v_s_2199_, 2);
v_ncRings_2203_ = lean_ctor_get(v_s_2199_, 3);
v_ncSemirings_2204_ = lean_ctor_get(v_s_2199_, 4);
v_typeClassify_2205_ = lean_ctor_get(v_s_2199_, 5);
v_orders_2206_ = lean_ctor_get(v_s_2199_, 6);
v_typeOrderClassify_2207_ = lean_ctor_get(v_s_2199_, 7);
v_isSharedCheck_2215_ = !lean_is_exclusive(v_s_2199_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2209_ = v_s_2199_;
v_isShared_2210_ = v_isSharedCheck_2215_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_typeOrderClassify_2207_);
lean_inc(v_orders_2206_);
lean_inc(v_typeClassify_2205_);
lean_inc(v_ncSemirings_2204_);
lean_inc(v_ncRings_2203_);
lean_inc(v_semirings_2202_);
lean_inc(v_rings_2201_);
lean_inc(v_exp_2200_);
lean_dec(v_s_2199_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2215_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2211_; lean_object* v___x_2213_; 
v___x_2211_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1___redArg(v_typeClassify_2205_, v_type_2197_, v_a_2198_);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 5, v___x_2211_);
v___x_2213_ = v___x_2209_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_exp_2200_);
lean_ctor_set(v_reuseFailAlloc_2214_, 1, v_rings_2201_);
lean_ctor_set(v_reuseFailAlloc_2214_, 2, v_semirings_2202_);
lean_ctor_set(v_reuseFailAlloc_2214_, 3, v_ncRings_2203_);
lean_ctor_set(v_reuseFailAlloc_2214_, 4, v_ncSemirings_2204_);
lean_ctor_set(v_reuseFailAlloc_2214_, 5, v___x_2211_);
lean_ctor_set(v_reuseFailAlloc_2214_, 6, v_orders_2206_);
lean_ctor_set(v_reuseFailAlloc_2214_, 7, v_typeOrderClassify_2207_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classify_x3f(lean_object* v_type_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_){
_start:
{
lean_object* v___x_2224_; 
v___x_2224_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_2218_, v_a_2221_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2256_; 
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2227_ = v___x_2224_;
v_isShared_2228_ = v_isSharedCheck_2256_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2224_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2256_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v_typeClassify_2229_; lean_object* v___x_2230_; 
v_typeClassify_2229_ = lean_ctor_get(v_a_2225_, 5);
lean_inc_ref(v_typeClassify_2229_);
lean_dec(v_a_2225_);
v___x_2230_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(v_typeClassify_2229_, v_type_2216_);
lean_dec_ref(v_typeClassify_2229_);
if (lean_obj_tag(v___x_2230_) == 1)
{
lean_object* v_val_2231_; lean_object* v___x_2233_; 
lean_dec_ref(v_type_2216_);
v_val_2231_ = lean_ctor_get(v___x_2230_, 0);
lean_inc(v_val_2231_);
lean_dec_ref_known(v___x_2230_, 1);
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 0, v_val_2231_);
v___x_2233_ = v___x_2227_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_val_2231_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
else
{
lean_object* v___x_2235_; 
lean_dec(v___x_2230_);
lean_del_object(v___x_2227_);
lean_inc_ref(v_type_2216_);
v___x_2235_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_classify_x3f_go(v_type_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_a_2236_; lean_object* v___f_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc_n(v_a_2236_, 2);
lean_dec_ref_known(v___x_2235_, 1);
v___f_2237_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_classify_x3f___lam__0), 3, 2);
lean_closure_set(v___f_2237_, 0, v_type_2216_);
lean_closure_set(v___f_2237_, 1, v_a_2236_);
v___x_2238_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_2239_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_2238_, v___f_2237_, v_a_2218_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2246_ == 0)
{
lean_object* v_unused_2247_; 
v_unused_2247_ = lean_ctor_get(v___x_2239_, 0);
lean_dec(v_unused_2247_);
v___x_2241_ = v___x_2239_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_dec(v___x_2239_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2244_; 
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 0, v_a_2236_);
v___x_2244_ = v___x_2241_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_a_2236_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
else
{
lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2255_; 
lean_dec(v_a_2236_);
v_a_2248_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2250_ = v___x_2239_;
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_dec(v___x_2239_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2253_; 
if (v_isShared_2251_ == 0)
{
v___x_2253_ = v___x_2250_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_a_2248_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
}
}
else
{
lean_dec_ref(v_type_2216_);
return v___x_2235_;
}
}
}
}
else
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2264_; 
lean_dec_ref(v_type_2216_);
v_a_2257_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2259_ = v___x_2224_;
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2224_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2262_; 
if (v_isShared_2260_ == 0)
{
v___x_2262_ = v___x_2259_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_a_2257_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classify_x3f___boxed(lean_object* v_type_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l_Lean_Meta_Sym_Arith_classify_x3f(v_type_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_);
lean_dec(v_a_2271_);
lean_dec_ref(v_a_2270_);
lean_dec(v_a_2269_);
lean_dec_ref(v_a_2268_);
lean_dec(v_a_2267_);
lean_dec_ref(v_a_2266_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_canonFn(lean_object* v_fn_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_){
_start:
{
lean_object* v___x_2282_; 
v___x_2282_ = l_Lean_Meta_Sym_canon(v_fn_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_);
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v_a_2283_; lean_object* v___x_2284_; 
v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
lean_inc(v_a_2283_);
lean_dec_ref_known(v___x_2282_, 1);
v___x_2284_ = l_Lean_Meta_Sym_shareCommon(v_a_2283_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_);
return v___x_2284_;
}
else
{
return v___x_2282_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_canonFn___boxed(lean_object* v_fn_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_canonFn(v_fn_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_);
lean_dec(v_a_2291_);
lean_dec_ref(v_a_2290_);
lean_dec(v_a_2289_);
lean_dec_ref(v_a_2288_);
lean_dec(v_a_2287_);
lean_dec_ref(v_a_2286_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg(lean_object* v_u_2299_, lean_object* v_type_2300_, lean_object* v_semiringInst_2301_, lean_object* v_leInst_2302_, lean_object* v_ltInst_2303_, lean_object* v_isPreorderInst_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_){
_start:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2311_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___closed__1));
v___x_2312_ = lean_box(0);
v___x_2313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2313_, 0, v_u_2299_);
lean_ctor_set(v___x_2313_, 1, v___x_2312_);
v___x_2314_ = l_Lean_mkConst(v___x_2311_, v___x_2313_);
v___x_2315_ = l_Lean_mkApp5(v___x_2314_, v_type_2300_, v_semiringInst_2301_, v_leInst_2302_, v_ltInst_2303_, v_isPreorderInst_2304_);
v___x_2316_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_2315_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
return v___x_2316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___boxed(lean_object* v_u_2317_, lean_object* v_type_2318_, lean_object* v_semiringInst_2319_, lean_object* v_leInst_2320_, lean_object* v_ltInst_2321_, lean_object* v_isPreorderInst_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_){
_start:
{
lean_object* v_res_2329_; 
v_res_2329_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg(v_u_2317_, v_type_2318_, v_semiringInst_2319_, v_leInst_2320_, v_ltInst_2321_, v_isPreorderInst_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_);
lean_dec(v_a_2327_);
lean_dec_ref(v_a_2326_);
lean_dec(v_a_2325_);
lean_dec_ref(v_a_2324_);
lean_dec(v_a_2323_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f(lean_object* v_u_2330_, lean_object* v_type_2331_, lean_object* v_semiringInst_2332_, lean_object* v_leInst_2333_, lean_object* v_ltInst_2334_, lean_object* v_isPreorderInst_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_){
_start:
{
lean_object* v___x_2343_; 
v___x_2343_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg(v_u_2330_, v_type_2331_, v_semiringInst_2332_, v_leInst_2333_, v_ltInst_2334_, v_isPreorderInst_2335_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
return v___x_2343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___boxed(lean_object* v_u_2344_, lean_object* v_type_2345_, lean_object* v_semiringInst_2346_, lean_object* v_leInst_2347_, lean_object* v_ltInst_2348_, lean_object* v_isPreorderInst_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_){
_start:
{
lean_object* v_res_2357_; 
v_res_2357_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f(v_u_2344_, v_type_2345_, v_semiringInst_2346_, v_leInst_2347_, v_ltInst_2348_, v_isPreorderInst_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
lean_dec(v_a_2355_);
lean_dec_ref(v_a_2354_);
lean_dec(v_a_2353_);
lean_dec_ref(v_a_2352_);
lean_dec(v_a_2351_);
lean_dec_ref(v_a_2350_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f_spec__0(lean_object* v_msg_2358_){
_start:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2359_ = l_Lean_instInhabitedExpr;
v___x_2360_ = lean_panic_fn_borrowed(v___x_2359_, v_msg_2358_);
return v___x_2360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___lam__0(lean_object* v___x_2361_, lean_object* v_s_2362_){
_start:
{
lean_object* v_exp_2363_; lean_object* v_rings_2364_; lean_object* v_semirings_2365_; lean_object* v_ncRings_2366_; lean_object* v_ncSemirings_2367_; lean_object* v_typeClassify_2368_; lean_object* v_orders_2369_; lean_object* v_typeOrderClassify_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2378_; 
v_exp_2363_ = lean_ctor_get(v_s_2362_, 0);
v_rings_2364_ = lean_ctor_get(v_s_2362_, 1);
v_semirings_2365_ = lean_ctor_get(v_s_2362_, 2);
v_ncRings_2366_ = lean_ctor_get(v_s_2362_, 3);
v_ncSemirings_2367_ = lean_ctor_get(v_s_2362_, 4);
v_typeClassify_2368_ = lean_ctor_get(v_s_2362_, 5);
v_orders_2369_ = lean_ctor_get(v_s_2362_, 6);
v_typeOrderClassify_2370_ = lean_ctor_get(v_s_2362_, 7);
v_isSharedCheck_2378_ = !lean_is_exclusive(v_s_2362_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2372_ = v_s_2362_;
v_isShared_2373_ = v_isSharedCheck_2378_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_typeOrderClassify_2370_);
lean_inc(v_orders_2369_);
lean_inc(v_typeClassify_2368_);
lean_inc(v_ncSemirings_2367_);
lean_inc(v_ncRings_2366_);
lean_inc(v_semirings_2365_);
lean_inc(v_rings_2364_);
lean_inc(v_exp_2363_);
lean_dec(v_s_2362_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2378_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2374_; lean_object* v___x_2376_; 
v___x_2374_ = lean_array_push(v_orders_2369_, v___x_2361_);
if (v_isShared_2373_ == 0)
{
lean_ctor_set(v___x_2372_, 6, v___x_2374_);
v___x_2376_ = v___x_2372_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_exp_2363_);
lean_ctor_set(v_reuseFailAlloc_2377_, 1, v_rings_2364_);
lean_ctor_set(v_reuseFailAlloc_2377_, 2, v_semirings_2365_);
lean_ctor_set(v_reuseFailAlloc_2377_, 3, v_ncRings_2366_);
lean_ctor_set(v_reuseFailAlloc_2377_, 4, v_ncSemirings_2367_);
lean_ctor_set(v_reuseFailAlloc_2377_, 5, v_typeClassify_2368_);
lean_ctor_set(v_reuseFailAlloc_2377_, 6, v___x_2374_);
lean_ctor_set(v_reuseFailAlloc_2377_, 7, v_typeOrderClassify_2370_);
v___x_2376_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
return v___x_2376_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f(lean_object* v_type_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_){
_start:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2401_ = l_Lean_Meta_Sym_Arith_instInhabitedCommRing_default;
v___x_2402_ = l_Lean_Meta_Sym_Arith_instInhabitedRing_default;
v___x_2403_ = l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring_default;
v___x_2404_ = l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default;
lean_inc_ref(v_type_2393_);
v___x_2405_ = l_Lean_Meta_getDecLevel_x3f(v_type_2393_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_object* v_a_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2745_; 
v_a_2406_ = lean_ctor_get(v___x_2405_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2408_ = v___x_2405_;
v_isShared_2409_ = v_isSharedCheck_2745_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_a_2406_);
lean_dec(v___x_2405_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2745_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
if (lean_obj_tag(v_a_2406_) == 1)
{
lean_object* v_val_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2740_; 
lean_del_object(v___x_2408_);
v_val_2410_ = lean_ctor_get(v_a_2406_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v_a_2406_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2412_ = v_a_2406_;
v_isShared_2413_ = v_isSharedCheck_2740_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_val_2410_);
lean_dec(v_a_2406_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2740_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2414_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__1));
v___x_2415_ = lean_box(0);
lean_inc(v_val_2410_);
v___x_2416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2416_, 0, v_val_2410_);
lean_ctor_set(v___x_2416_, 1, v___x_2415_);
lean_inc_ref(v___x_2416_);
v___x_2417_ = l_Lean_mkConst(v___x_2414_, v___x_2416_);
lean_inc_ref(v_type_2393_);
v___x_2418_ = l_Lean_Expr_app___override(v___x_2417_, v_type_2393_);
v___x_2419_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_2418_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v_a_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2731_; 
v_a_2420_ = lean_ctor_get(v___x_2419_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2422_ = v___x_2419_;
v_isShared_2423_ = v_isSharedCheck_2731_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_a_2420_);
lean_dec(v___x_2419_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2731_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
if (lean_obj_tag(v_a_2420_) == 1)
{
lean_object* v_val_2424_; lean_object* v___x_2425_; 
lean_del_object(v___x_2422_);
v_val_2424_ = lean_ctor_get(v_a_2420_, 0);
lean_inc(v_val_2424_);
lean_inc_ref(v_a_2420_);
lean_inc_ref(v_type_2393_);
lean_inc(v_val_2410_);
v___x_2425_ = l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f(v_val_2410_, v_type_2393_, v_a_2420_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2718_; 
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2428_ = v___x_2425_;
v_isShared_2429_ = v_isSharedCheck_2718_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2425_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2718_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
if (lean_obj_tag(v_a_2426_) == 1)
{
lean_object* v_val_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2713_; 
lean_del_object(v___x_2428_);
v_val_2430_ = lean_ctor_get(v_a_2426_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v_a_2426_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2432_ = v_a_2426_;
v_isShared_2433_ = v_isSharedCheck_2713_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_val_2430_);
lean_dec(v_a_2426_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2713_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2434_; 
lean_inc_ref(v_a_2420_);
lean_inc_ref(v_type_2393_);
lean_inc(v_val_2410_);
v___x_2434_ = l_Lean_Meta_Sym_Arith_mkIsPartialOrderInst_x3f(v_val_2410_, v_type_2393_, v_a_2420_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_);
if (lean_obj_tag(v___x_2434_) == 0)
{
lean_object* v_a_2435_; lean_object* v___x_2436_; 
v_a_2435_ = lean_ctor_get(v___x_2434_, 0);
lean_inc(v_a_2435_);
lean_dec_ref_known(v___x_2434_, 1);
lean_inc_ref(v_a_2420_);
lean_inc_ref(v_type_2393_);
lean_inc(v_val_2410_);
v___x_2436_ = l_Lean_Meta_Sym_Arith_mkIsLinearPreorderInst_x3f(v_val_2410_, v_type_2393_, v_a_2420_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v_a_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; 
v_a_2437_ = lean_ctor_get(v___x_2436_, 0);
lean_inc(v_a_2437_);
lean_dec_ref_known(v___x_2436_, 1);
v___x_2438_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__3));
lean_inc_ref(v___x_2416_);
v___x_2439_ = l_Lean_mkConst(v___x_2438_, v___x_2416_);
lean_inc_ref(v_type_2393_);
v___x_2440_ = l_Lean_Expr_app___override(v___x_2439_, v_type_2393_);
v___x_2441_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_2440_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_);
if (lean_obj_tag(v___x_2441_) == 0)
{
lean_object* v_a_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; 
v_a_2442_ = lean_ctor_get(v___x_2441_, 0);
lean_inc(v_a_2442_);
lean_dec_ref_known(v___x_2441_, 1);
v___x_2443_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__5));
lean_inc_ref(v___x_2416_);
v___x_2444_ = l_Lean_mkConst(v___x_2443_, v___x_2416_);
lean_inc(v_val_2424_);
lean_inc_ref(v_type_2393_);
v___x_2445_ = l_Lean_mkAppB(v___x_2444_, v_type_2393_, v_val_2424_);
v___x_2446_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_canonFn(v___x_2445_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_);
if (lean_obj_tag(v___x_2446_) == 0)
{
lean_object* v_a_2447_; lean_object* v___y_2449_; lean_object* v___y_2450_; lean_object* v_fst_2451_; lean_object* v_fst_2452_; uint8_t v_fst_2453_; lean_object* v_fst_2454_; lean_object* v_fst_2455_; uint8_t v_snd_2456_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v_fst_2495_; lean_object* v_snd_2496_; lean_object* v___y_2497_; lean_object* v___y_2498_; 
v_a_2447_ = lean_ctor_get(v___x_2446_, 0);
lean_inc(v_a_2447_);
lean_dec_ref_known(v___x_2446_, 1);
if (lean_obj_tag(v_a_2442_) == 1)
{
lean_object* v_val_2502_; lean_object* v___x_2503_; 
v_val_2502_ = lean_ctor_get(v_a_2442_, 0);
lean_inc_ref(v_a_2442_);
lean_inc_ref(v_type_2393_);
lean_inc(v_val_2410_);
v___x_2503_ = l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f(v_val_2410_, v_type_2393_, v_a_2442_, v_a_2420_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_);
if (lean_obj_tag(v___x_2503_) == 0)
{
lean_object* v_a_2504_; 
v_a_2504_ = lean_ctor_get(v___x_2503_, 0);
lean_inc(v_a_2504_);
lean_dec_ref_known(v___x_2503_, 1);
if (lean_obj_tag(v_a_2504_) == 0)
{
lean_dec_ref_known(v___x_2416_, 2);
lean_del_object(v___x_2412_);
v_fst_2495_ = v_a_2504_;
v_snd_2496_ = v_a_2504_;
v___y_2497_ = v_a_2395_;
v___y_2498_ = v_a_2398_;
goto v___jp_2494_;
}
else
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2505_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__7));
v___x_2506_ = l_Lean_mkConst(v___x_2505_, v___x_2416_);
lean_inc(v_val_2502_);
lean_inc_ref(v_type_2393_);
v___x_2507_ = l_Lean_mkAppB(v___x_2506_, v_type_2393_, v_val_2502_);
v___x_2508_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_canonFn(v___x_2507_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v_a_2509_; lean_object* v___x_2511_; 
v_a_2509_ = lean_ctor_get(v___x_2508_, 0);
lean_inc(v_a_2509_);
lean_dec_ref_known(v___x_2508_, 1);
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 0, v_a_2509_);
v___x_2511_ = v___x_2412_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v_a_2509_);
v___x_2511_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
uint8_t v___x_2512_; uint8_t v___x_2513_; lean_object* v___x_2514_; 
v___x_2512_ = 0;
v___x_2513_ = 1;
lean_inc_ref(v_type_2393_);
v___x_2514_ = l_Lean_Meta_Sym_Arith_classify_x3f(v_type_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_object* v_a_2515_; 
v_a_2515_ = lean_ctor_get(v___x_2514_, 0);
lean_inc(v_a_2515_);
lean_dec_ref_known(v___x_2514_, 1);
switch(lean_obj_tag(v_a_2515_))
{
case 0:
{
lean_object* v_id_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2551_; 
v_id_2516_ = lean_ctor_get(v_a_2515_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v_a_2515_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2518_ = v_a_2515_;
v_isShared_2519_ = v_isSharedCheck_2551_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_id_2516_);
lean_dec(v_a_2515_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2551_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2520_; 
v___x_2520_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_2395_, v_a_2398_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v_a_2521_; lean_object* v_rings_2522_; lean_object* v___x_2523_; lean_object* v_toRing_2524_; lean_object* v_ringInst_2525_; lean_object* v_semiringInst_2526_; lean_object* v___x_2527_; 
v_a_2521_ = lean_ctor_get(v___x_2520_, 0);
lean_inc(v_a_2521_);
lean_dec_ref_known(v___x_2520_, 1);
v_rings_2522_ = lean_ctor_get(v_a_2521_, 1);
lean_inc_ref(v_rings_2522_);
lean_dec(v_a_2521_);
v___x_2523_ = lean_array_get(v___x_2401_, v_rings_2522_, v_id_2516_);
lean_dec_ref(v_rings_2522_);
v_toRing_2524_ = lean_ctor_get(v___x_2523_, 0);
lean_inc_ref(v_toRing_2524_);
lean_dec(v___x_2523_);
v_ringInst_2525_ = lean_ctor_get(v_toRing_2524_, 3);
lean_inc_ref(v_ringInst_2525_);
v_semiringInst_2526_ = lean_ctor_get(v_toRing_2524_, 4);
lean_inc_ref(v_semiringInst_2526_);
lean_dec_ref(v_toRing_2524_);
lean_inc(v_val_2430_);
lean_inc(v_val_2502_);
lean_inc(v_val_2424_);
lean_inc_ref(v_type_2393_);
lean_inc(v_val_2410_);
v___x_2527_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg(v_val_2410_, v_type_2393_, v_semiringInst_2526_, v_val_2424_, v_val_2502_, v_val_2430_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_);
if (lean_obj_tag(v___x_2527_) == 0)
{
lean_object* v_a_2528_; 
v_a_2528_ = lean_ctor_get(v___x_2527_, 0);
lean_inc(v_a_2528_);
lean_dec_ref_known(v___x_2527_, 1);
if (lean_obj_tag(v_a_2528_) == 1)
{
lean_object* v___x_2530_; 
if (v_isShared_2519_ == 0)
{
lean_ctor_set_tag(v___x_2518_, 1);
v___x_2530_ = v___x_2518_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_id_2516_);
v___x_2530_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2531_ = lean_box(0);
v___x_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2532_, 0, v_ringInst_2525_);
v___y_2449_ = v___x_2511_;
v___y_2450_ = v_a_2504_;
v_fst_2451_ = v___x_2530_;
v_fst_2452_ = v___x_2531_;
v_fst_2453_ = v___x_2513_;
v_fst_2454_ = v___x_2532_;
v_fst_2455_ = v_a_2528_;
v_snd_2456_ = v___x_2513_;
v___y_2457_ = v_a_2395_;
v___y_2458_ = v_a_2398_;
goto v___jp_2448_;
}
}
else
{
lean_object* v___x_2534_; 
lean_dec(v_a_2528_);
lean_dec_ref(v_ringInst_2525_);
lean_del_object(v___x_2518_);
lean_dec(v_id_2516_);
v___x_2534_ = lean_box(0);
v___y_2449_ = v___x_2511_;
v___y_2450_ = v_a_2504_;
v_fst_2451_ = v___x_2534_;
v_fst_2452_ = v___x_2534_;
v_fst_2453_ = v___x_2513_;
v_fst_2454_ = v___x_2534_;
v_fst_2455_ = v___x_2534_;
v_snd_2456_ = v___x_2513_;
v___y_2457_ = v_a_2395_;
v___y_2458_ = v_a_2398_;
goto v___jp_2448_;
}
}
else
{
lean_object* v_a_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2542_; 
lean_dec_ref(v_ringInst_2525_);
lean_del_object(v___x_2518_);
lean_dec(v_id_2516_);
lean_dec_ref(v___x_2511_);
lean_dec_ref_known(v_a_2504_, 1);
lean_dec_ref_known(v_a_2442_, 1);
lean_dec(v_a_2447_);
lean_dec(v_a_2437_);
lean_dec(v_a_2435_);
lean_del_object(v___x_2432_);
lean_dec(v_val_2430_);
lean_dec(v_val_2424_);
lean_dec(v_val_2410_);
lean_dec_ref(v_type_2393_);
v_a_2535_ = lean_ctor_get(v___x_2527_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2527_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2537_ = v___x_2527_;
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_a_2535_);
lean_dec(v___x_2527_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2540_; 
if (v_isShared_2538_ == 0)
{
v___x_2540_ = v___x_2537_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_a_2535_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
}
else
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2550_; 
lean_del_object(v___x_2518_);
lean_dec(v_id_2516_);
lean_dec_ref(v___x_2511_);
lean_dec_ref_known(v_a_2504_, 1);
lean_dec_ref_known(v_a_2442_, 1);
lean_dec(v_a_2447_);
lean_dec(v_a_2437_);
lean_dec(v_a_2435_);
lean_del_object(v___x_2432_);
lean_dec(v_val_2430_);
lean_dec(v_val_2424_);
lean_dec(v_val_2410_);
lean_dec_ref(v_type_2393_);
v_a_2543_ = lean_ctor_get(v___x_2520_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2545_ = v___x_2520_;
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2520_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2548_; 
if (v_isShared_2546_ == 0)
{
v___x_2548_ = v___x_2545_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_a_2543_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
}
}
case 1:
{
lean_object* v_id_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2586_; 
v_id_2552_ = lean_ctor_get(v_a_2515_, 0);
v_isSharedCheck_2586_ = !lean_is_exclusive(v_a_2515_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2554_ = v_a_2515_;
v_isShared_2555_ = v_isSharedCheck_2586_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_id_2552_);
lean_dec(v_a_2515_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2586_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2556_; 
v___x_2556_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_2395_, v_a_2398_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v_a_2557_; lean_object* v_ncRings_2558_; lean_object* v___x_2559_; lean_object* v_ringInst_2560_; lean_object* v_semiringInst_2561_; lean_object* v___x_2562_; 
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
lean_inc(v_a_2557_);
lean_dec_ref_known(v___x_2556_, 1);
v_ncRings_2558_ = lean_ctor_get(v_a_2557_, 3);
lean_inc_ref(v_ncRings_2558_);
lean_dec(v_a_2557_);
v___x_2559_ = lean_array_get(v___x_2402_, v_ncRings_2558_, v_id_2552_);
lean_dec_ref(v_ncRings_2558_);
v_ringInst_2560_ = lean_ctor_get(v___x_2559_, 3);
lean_inc_ref(v_ringInst_2560_);
v_semiringInst_2561_ = lean_ctor_get(v___x_2559_, 4);
lean_inc_ref(v_semiringInst_2561_);
lean_dec(v___x_2559_);
lean_inc(v_val_2430_);
lean_inc(v_val_2502_);
lean_inc(v_val_2424_);
lean_inc_ref(v_type_2393_);
lean_inc(v_val_2410_);
v___x_2562_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg(v_val_2410_, v_type_2393_, v_semiringInst_2561_, v_val_2424_, v_val_2502_, v_val_2430_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_a_2563_; 
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
lean_inc(v_a_2563_);
lean_dec_ref_known(v___x_2562_, 1);
if (lean_obj_tag(v_a_2563_) == 1)
{
lean_object* v___x_2565_; 
if (v_isShared_2555_ == 0)
{
v___x_2565_ = v___x_2554_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_id_2552_);
v___x_2565_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2566_ = lean_box(0);
v___x_2567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2567_, 0, v_ringInst_2560_);
v___y_2449_ = v___x_2511_;
v___y_2450_ = v_a_2504_;
v_fst_2451_ = v___x_2565_;
v_fst_2452_ = v___x_2566_;
v_fst_2453_ = v___x_2513_;
v_fst_2454_ = v___x_2567_;
v_fst_2455_ = v_a_2563_;
v_snd_2456_ = v___x_2512_;
v___y_2457_ = v_a_2395_;
v___y_2458_ = v_a_2398_;
goto v___jp_2448_;
}
}
else
{
lean_object* v___x_2569_; 
lean_dec(v_a_2563_);
lean_dec_ref(v_ringInst_2560_);
lean_del_object(v___x_2554_);
lean_dec(v_id_2552_);
v___x_2569_ = lean_box(0);
v___y_2449_ = v___x_2511_;
v___y_2450_ = v_a_2504_;
v_fst_2451_ = v___x_2569_;
v_fst_2452_ = v___x_2569_;
v_fst_2453_ = v___x_2513_;
v_fst_2454_ = v___x_2569_;
v_fst_2455_ = v___x_2569_;
v_snd_2456_ = v___x_2512_;
v___y_2457_ = v_a_2395_;
v___y_2458_ = v_a_2398_;
goto v___jp_2448_;
}
}
else
{
lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2577_; 
lean_dec_ref(v_ringInst_2560_);
lean_del_object(v___x_2554_);
lean_dec(v_id_2552_);
lean_dec_ref(v___x_2511_);
lean_dec_ref_known(v_a_2504_, 1);
lean_dec_ref_known(v_a_2442_, 1);
lean_dec(v_a_2447_);
lean_dec(v_a_2437_);
lean_dec(v_a_2435_);
lean_del_object(v___x_2432_);
lean_dec(v_val_2430_);
lean_dec(v_val_2424_);
lean_dec(v_val_2410_);
lean_dec_ref(v_type_2393_);
v_a_2570_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2572_ = v___x_2562_;
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___x_2562_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2575_; 
if (v_isShared_2573_ == 0)
{
v___x_2575_ = v___x_2572_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_a_2570_);
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
else
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2585_; 
lean_del_object(v___x_2554_);
lean_dec(v_id_2552_);
lean_dec_ref(v___x_2511_);
lean_dec_ref_known(v_a_2504_, 1);
lean_dec_ref_known(v_a_2442_, 1);
lean_dec(v_a_2447_);
lean_dec(v_a_2437_);
lean_dec(v_a_2435_);
lean_del_object(v___x_2432_);
lean_dec(v_val_2430_);
lean_dec(v_val_2424_);
lean_dec(v_val_2410_);
lean_dec_ref(v_type_2393_);
v_a_2578_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2580_ = v___x_2556_;
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2556_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2583_; 
if (v_isShared_2581_ == 0)
{
v___x_2583_ = v___x_2580_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_a_2578_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
}
}
case 2:
{
lean_object* v_id_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2620_; 
v_id_2587_ = lean_ctor_get(v_a_2515_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v_a_2515_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2589_ = v_a_2515_;
v_isShared_2590_ = v_isSharedCheck_2620_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_id_2587_);
lean_dec(v_a_2515_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2620_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2591_; 
v___x_2591_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_2395_, v_a_2398_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; lean_object* v_semirings_2593_; lean_object* v___x_2594_; lean_object* v_toSemiring_2595_; lean_object* v_semiringInst_2596_; lean_object* v___x_2597_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
lean_inc(v_a_2592_);
lean_dec_ref_known(v___x_2591_, 1);
v_semirings_2593_ = lean_ctor_get(v_a_2592_, 2);
lean_inc_ref(v_semirings_2593_);
lean_dec(v_a_2592_);
v___x_2594_ = lean_array_get(v___x_2403_, v_semirings_2593_, v_id_2587_);
lean_dec_ref(v_semirings_2593_);
v_toSemiring_2595_ = lean_ctor_get(v___x_2594_, 0);
lean_inc_ref(v_toSemiring_2595_);
lean_dec(v___x_2594_);
v_semiringInst_2596_ = lean_ctor_get(v_toSemiring_2595_, 3);
lean_inc_ref(v_semiringInst_2596_);
lean_dec_ref(v_toSemiring_2595_);
lean_inc(v_val_2430_);
lean_inc(v_val_2502_);
lean_inc(v_val_2424_);
lean_inc_ref(v_type_2393_);
lean_inc(v_val_2410_);
v___x_2597_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg(v_val_2410_, v_type_2393_, v_semiringInst_2596_, v_val_2424_, v_val_2502_, v_val_2430_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2598_; 
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
lean_inc(v_a_2598_);
lean_dec_ref_known(v___x_2597_, 1);
if (lean_obj_tag(v_a_2598_) == 1)
{
lean_object* v___x_2599_; lean_object* v___x_2601_; 
v___x_2599_ = lean_box(0);
if (v_isShared_2590_ == 0)
{
lean_ctor_set_tag(v___x_2589_, 1);
v___x_2601_ = v___x_2589_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_id_2587_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
v___y_2449_ = v___x_2511_;
v___y_2450_ = v_a_2504_;
v_fst_2451_ = v___x_2599_;
v_fst_2452_ = v___x_2601_;
v_fst_2453_ = v___x_2513_;
v_fst_2454_ = v___x_2599_;
v_fst_2455_ = v_a_2598_;
v_snd_2456_ = v___x_2512_;
v___y_2457_ = v_a_2395_;
v___y_2458_ = v_a_2398_;
goto v___jp_2448_;
}
}
else
{
lean_object* v___x_2603_; 
lean_dec(v_a_2598_);
lean_del_object(v___x_2589_);
lean_dec(v_id_2587_);
v___x_2603_ = lean_box(0);
v___y_2449_ = v___x_2511_;
v___y_2450_ = v_a_2504_;
v_fst_2451_ = v___x_2603_;
v_fst_2452_ = v___x_2603_;
v_fst_2453_ = v___x_2513_;
v_fst_2454_ = v___x_2603_;
v_fst_2455_ = v___x_2603_;
v_snd_2456_ = v___x_2512_;
v___y_2457_ = v_a_2395_;
v___y_2458_ = v_a_2398_;
goto v___jp_2448_;
}
}
else
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2611_; 
lean_del_object(v___x_2589_);
lean_dec(v_id_2587_);
lean_dec_ref(v___x_2511_);
lean_dec_ref_known(v_a_2504_, 1);
lean_dec_ref_known(v_a_2442_, 1);
lean_dec(v_a_2447_);
lean_dec(v_a_2437_);
lean_dec(v_a_2435_);
lean_del_object(v___x_2432_);
lean_dec(v_val_2430_);
lean_dec(v_val_2424_);
lean_dec(v_val_2410_);
lean_dec_ref(v_type_2393_);
v_a_2604_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2606_ = v___x_2597_;
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2597_);
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
lean_del_object(v___x_2589_);
lean_dec(v_id_2587_);
lean_dec_ref(v___x_2511_);
lean_dec_ref_known(v_a_2504_, 1);
lean_dec_ref_known(v_a_2442_, 1);
lean_dec(v_a_2447_);
lean_dec(v_a_2437_);
lean_dec(v_a_2435_);
lean_del_object(v___x_2432_);
lean_dec(v_val_2430_);
lean_dec(v_val_2424_);
lean_dec(v_val_2410_);
lean_dec_ref(v_type_2393_);
v_a_2612_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2614_ = v___x_2591_;
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2591_);
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
case 3:
{
lean_object* v_id_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2653_; 
v_id_2621_ = lean_ctor_get(v_a_2515_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v_a_2515_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2623_ = v_a_2515_;
v_isShared_2624_ = v_isSharedCheck_2653_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_id_2621_);
lean_dec(v_a_2515_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2653_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2625_; 
v___x_2625_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_2395_, v_a_2398_);
if (lean_obj_tag(v___x_2625_) == 0)
{
lean_object* v_a_2626_; lean_object* v_ncSemirings_2627_; lean_object* v___x_2628_; lean_object* v_semiringInst_2629_; lean_object* v___x_2630_; 
v_a_2626_ = lean_ctor_get(v___x_2625_, 0);
lean_inc(v_a_2626_);
lean_dec_ref_known(v___x_2625_, 1);
v_ncSemirings_2627_ = lean_ctor_get(v_a_2626_, 4);
lean_inc_ref(v_ncSemirings_2627_);
lean_dec(v_a_2626_);
v___x_2628_ = lean_array_get(v___x_2404_, v_ncSemirings_2627_, v_id_2621_);
lean_dec_ref(v_ncSemirings_2627_);
v_semiringInst_2629_ = lean_ctor_get(v___x_2628_, 3);
lean_inc_ref(v_semiringInst_2629_);
lean_dec(v___x_2628_);
lean_inc(v_val_2430_);
lean_inc(v_val_2502_);
lean_inc(v_val_2424_);
lean_inc_ref(v_type_2393_);
lean_inc(v_val_2410_);
v___x_2630_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg(v_val_2410_, v_type_2393_, v_semiringInst_2629_, v_val_2424_, v_val_2502_, v_val_2430_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_);
if (lean_obj_tag(v___x_2630_) == 0)
{
lean_object* v_a_2631_; 
v_a_2631_ = lean_ctor_get(v___x_2630_, 0);
lean_inc(v_a_2631_);
lean_dec_ref_known(v___x_2630_, 1);
if (lean_obj_tag(v_a_2631_) == 1)
{
lean_object* v___x_2632_; lean_object* v___x_2634_; 
v___x_2632_ = lean_box(0);
if (v_isShared_2624_ == 0)
{
lean_ctor_set_tag(v___x_2623_, 1);
v___x_2634_ = v___x_2623_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_id_2621_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
v___y_2449_ = v___x_2511_;
v___y_2450_ = v_a_2504_;
v_fst_2451_ = v___x_2632_;
v_fst_2452_ = v___x_2634_;
v_fst_2453_ = v___x_2512_;
v_fst_2454_ = v___x_2632_;
v_fst_2455_ = v_a_2631_;
v_snd_2456_ = v___x_2512_;
v___y_2457_ = v_a_2395_;
v___y_2458_ = v_a_2398_;
goto v___jp_2448_;
}
}
else
{
lean_object* v___x_2636_; 
lean_dec(v_a_2631_);
lean_del_object(v___x_2623_);
lean_dec(v_id_2621_);
v___x_2636_ = lean_box(0);
v___y_2449_ = v___x_2511_;
v___y_2450_ = v_a_2504_;
v_fst_2451_ = v___x_2636_;
v_fst_2452_ = v___x_2636_;
v_fst_2453_ = v___x_2513_;
v_fst_2454_ = v___x_2636_;
v_fst_2455_ = v___x_2636_;
v_snd_2456_ = v___x_2512_;
v___y_2457_ = v_a_2395_;
v___y_2458_ = v_a_2398_;
goto v___jp_2448_;
}
}
else
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2644_; 
lean_del_object(v___x_2623_);
lean_dec(v_id_2621_);
lean_dec_ref(v___x_2511_);
lean_dec_ref_known(v_a_2504_, 1);
lean_dec_ref_known(v_a_2442_, 1);
lean_dec(v_a_2447_);
lean_dec(v_a_2437_);
lean_dec(v_a_2435_);
lean_del_object(v___x_2432_);
lean_dec(v_val_2430_);
lean_dec(v_val_2424_);
lean_dec(v_val_2410_);
lean_dec_ref(v_type_2393_);
v_a_2637_ = lean_ctor_get(v___x_2630_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2639_ = v___x_2630_;
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2630_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2642_; 
if (v_isShared_2640_ == 0)
{
v___x_2642_ = v___x_2639_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_a_2637_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
}
else
{
lean_object* v_a_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2652_; 
lean_del_object(v___x_2623_);
lean_dec(v_id_2621_);
lean_dec_ref(v___x_2511_);
lean_dec_ref_known(v_a_2504_, 1);
lean_dec_ref_known(v_a_2442_, 1);
lean_dec(v_a_2447_);
lean_dec(v_a_2437_);
lean_dec(v_a_2435_);
lean_del_object(v___x_2432_);
lean_dec(v_val_2430_);
lean_dec(v_val_2424_);
lean_dec(v_val_2410_);
lean_dec_ref(v_type_2393_);
v_a_2645_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2647_ = v___x_2625_;
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_a_2645_);
lean_dec(v___x_2625_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2650_; 
if (v_isShared_2648_ == 0)
{
v___x_2650_ = v___x_2647_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_a_2645_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
}
}
}
default: 
{
lean_object* v___x_2654_; 
v___x_2654_ = lean_box(0);
v___y_2449_ = v___x_2511_;
v___y_2450_ = v_a_2504_;
v_fst_2451_ = v___x_2654_;
v_fst_2452_ = v___x_2654_;
v_fst_2453_ = v___x_2513_;
v_fst_2454_ = v___x_2654_;
v_fst_2455_ = v___x_2654_;
v_snd_2456_ = v___x_2512_;
v___y_2457_ = v_a_2395_;
v___y_2458_ = v_a_2398_;
goto v___jp_2448_;
}
}
}
else
{
lean_object* v_a_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2662_; 
lean_dec_ref(v___x_2511_);
lean_dec_ref_known(v_a_2504_, 1);
lean_dec_ref_known(v_a_2442_, 1);
lean_dec(v_a_2447_);
lean_dec(v_a_2437_);
lean_dec(v_a_2435_);
lean_del_object(v___x_2432_);
lean_dec(v_val_2430_);
lean_dec(v_val_2424_);
lean_dec(v_val_2410_);
lean_dec_ref(v_type_2393_);
v_a_2655_ = lean_ctor_get(v___x_2514_, 0);
v_isSharedCheck_2662_ = !lean_is_exclusive(v___x_2514_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2657_ = v___x_2514_;
v_isShared_2658_ = v_isSharedCheck_2662_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_a_2655_);
lean_dec(v___x_2514_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2662_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v___x_2660_; 
if (v_isShared_2658_ == 0)
{
v___x_2660_ = v___x_2657_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_a_2655_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
}
}
}
else
{
lean_object* v_a_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2671_; 
lean_dec_ref_known(v_a_2504_, 1);
lean_dec_ref_known(v_a_2442_, 1);
lean_dec(v_a_2447_);
lean_dec(v_a_2437_);
lean_dec(v_a_2435_);
lean_del_object(v___x_2432_);
lean_dec(v_val_2430_);
lean_dec(v_val_2424_);
lean_del_object(v___x_2412_);
lean_dec(v_val_2410_);
lean_dec_ref(v_type_2393_);
v_a_2664_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2666_ = v___x_2508_;
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_a_2664_);
lean_dec(v___x_2508_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2669_; 
if (v_isShared_2667_ == 0)
{
v___x_2669_ = v___x_2666_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_a_2664_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
}
}
}
else
{
lean_object* v_a_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2679_; 
lean_dec_ref_known(v_a_2442_, 1);
lean_dec(v_a_2447_);
lean_dec(v_a_2437_);
lean_dec(v_a_2435_);
lean_del_object(v___x_2432_);
lean_dec(v_val_2430_);
lean_dec(v_val_2424_);
lean_dec_ref_known(v___x_2416_, 2);
lean_del_object(v___x_2412_);
lean_dec(v_val_2410_);
lean_dec_ref(v_type_2393_);
v_a_2672_ = lean_ctor_get(v___x_2503_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2503_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2674_ = v___x_2503_;
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_a_2672_);
lean_dec(v___x_2503_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2677_; 
if (v_isShared_2675_ == 0)
{
v___x_2677_ = v___x_2674_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_a_2672_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
}
}
else
{
lean_object* v___x_2680_; 
lean_dec_ref_known(v_a_2420_, 1);
lean_dec_ref_known(v___x_2416_, 2);
lean_del_object(v___x_2412_);
v___x_2680_ = lean_box(0);
v_fst_2495_ = v___x_2680_;
v_snd_2496_ = v___x_2680_;
v___y_2497_ = v_a_2395_;
v___y_2498_ = v_a_2398_;
goto v___jp_2494_;
}
v___jp_2448_:
{
lean_object* v___x_2459_; 
v___x_2459_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v___y_2457_, v___y_2458_);
if (lean_obj_tag(v___x_2459_) == 0)
{
lean_object* v_a_2460_; lean_object* v_orders_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___f_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
v_a_2460_ = lean_ctor_get(v___x_2459_, 0);
lean_inc(v_a_2460_);
lean_dec_ref_known(v___x_2459_, 1);
v_orders_2461_ = lean_ctor_get(v_a_2460_, 6);
lean_inc_ref(v_orders_2461_);
lean_dec(v_a_2460_);
v___x_2462_ = lean_array_get_size(v_orders_2461_);
lean_dec_ref(v_orders_2461_);
v___x_2463_ = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(v___x_2463_, 0, v___x_2462_);
lean_ctor_set(v___x_2463_, 1, v_type_2393_);
lean_ctor_set(v___x_2463_, 2, v_val_2410_);
lean_ctor_set(v___x_2463_, 3, v_val_2430_);
lean_ctor_set(v___x_2463_, 4, v_val_2424_);
lean_ctor_set(v___x_2463_, 5, v_a_2442_);
lean_ctor_set(v___x_2463_, 6, v_a_2435_);
lean_ctor_set(v___x_2463_, 7, v_a_2437_);
lean_ctor_set(v___x_2463_, 8, v___y_2450_);
lean_ctor_set(v___x_2463_, 9, v_fst_2451_);
lean_ctor_set(v___x_2463_, 10, v_fst_2452_);
lean_ctor_set(v___x_2463_, 11, v_fst_2454_);
lean_ctor_set(v___x_2463_, 12, v_fst_2455_);
lean_ctor_set(v___x_2463_, 13, v_a_2447_);
lean_ctor_set(v___x_2463_, 14, v___y_2449_);
lean_ctor_set_uint8(v___x_2463_, sizeof(void*)*15, v_snd_2456_);
lean_ctor_set_uint8(v___x_2463_, sizeof(void*)*15 + 1, v_fst_2453_);
v___f_2464_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___lam__0), 2, 1);
lean_closure_set(v___f_2464_, 0, v___x_2463_);
v___x_2465_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_2466_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_2465_, v___f_2464_, v___y_2457_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2476_; 
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2476_ == 0)
{
lean_object* v_unused_2477_; 
v_unused_2477_ = lean_ctor_get(v___x_2466_, 0);
lean_dec(v_unused_2477_);
v___x_2468_ = v___x_2466_;
v_isShared_2469_ = v_isSharedCheck_2476_;
goto v_resetjp_2467_;
}
else
{
lean_dec(v___x_2466_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2476_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2471_; 
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 0, v___x_2462_);
v___x_2471_ = v___x_2432_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___x_2462_);
v___x_2471_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
lean_object* v___x_2473_; 
if (v_isShared_2469_ == 0)
{
lean_ctor_set(v___x_2468_, 0, v___x_2471_);
v___x_2473_ = v___x_2468_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v___x_2471_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
}
else
{
lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2485_; 
lean_del_object(v___x_2432_);
v_a_2478_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2480_ = v___x_2466_;
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_dec(v___x_2466_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2483_; 
if (v_isShared_2481_ == 0)
{
v___x_2483_ = v___x_2480_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_a_2478_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
}
else
{
lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2493_; 
lean_dec(v_fst_2455_);
lean_dec(v_fst_2454_);
lean_dec(v_fst_2452_);
lean_dec(v_fst_2451_);
lean_dec(v___y_2450_);
lean_dec(v___y_2449_);
lean_dec(v_a_2447_);
lean_dec(v_a_2442_);
lean_dec(v_a_2437_);
lean_dec(v_a_2435_);
lean_del_object(v___x_2432_);
lean_dec(v_val_2430_);
lean_dec(v_val_2424_);
lean_dec(v_val_2410_);
lean_dec_ref(v_type_2393_);
v_a_2486_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2488_ = v___x_2459_;
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v___x_2459_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2491_; 
if (v_isShared_2489_ == 0)
{
v___x_2491_ = v___x_2488_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2486_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
}
v___jp_2494_:
{
uint8_t v___x_2499_; lean_object* v___x_2500_; uint8_t v___x_2501_; 
v___x_2499_ = 1;
v___x_2500_ = lean_box(0);
v___x_2501_ = 0;
lean_inc_n(v_fst_2495_, 2);
v___y_2449_ = v_snd_2496_;
v___y_2450_ = v_fst_2495_;
v_fst_2451_ = v___x_2500_;
v_fst_2452_ = v___x_2500_;
v_fst_2453_ = v___x_2499_;
v_fst_2454_ = v_fst_2495_;
v_fst_2455_ = v_fst_2495_;
v_snd_2456_ = v___x_2501_;
v___y_2457_ = v___y_2497_;
v___y_2458_ = v___y_2498_;
goto v___jp_2448_;
}
}
else
{
lean_object* v_a_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2688_; 
lean_dec(v_a_2442_);
lean_dec(v_a_2437_);
lean_dec(v_a_2435_);
lean_del_object(v___x_2432_);
lean_dec(v_val_2430_);
lean_dec(v_val_2424_);
lean_dec_ref_known(v_a_2420_, 1);
lean_dec_ref_known(v___x_2416_, 2);
lean_del_object(v___x_2412_);
lean_dec(v_val_2410_);
lean_dec_ref(v_type_2393_);
v_a_2681_ = lean_ctor_get(v___x_2446_, 0);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2683_ = v___x_2446_;
v_isShared_2684_ = v_isSharedCheck_2688_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_a_2681_);
lean_dec(v___x_2446_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2688_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___x_2686_; 
if (v_isShared_2684_ == 0)
{
v___x_2686_ = v___x_2683_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_a_2681_);
v___x_2686_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
return v___x_2686_;
}
}
}
}
else
{
lean_object* v_a_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2696_; 
lean_dec(v_a_2437_);
lean_dec(v_a_2435_);
lean_del_object(v___x_2432_);
lean_dec(v_val_2430_);
lean_dec(v_val_2424_);
lean_dec_ref_known(v_a_2420_, 1);
lean_dec_ref_known(v___x_2416_, 2);
lean_del_object(v___x_2412_);
lean_dec(v_val_2410_);
lean_dec_ref(v_type_2393_);
v_a_2689_ = lean_ctor_get(v___x_2441_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2441_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2691_ = v___x_2441_;
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_a_2689_);
lean_dec(v___x_2441_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2694_; 
if (v_isShared_2692_ == 0)
{
v___x_2694_ = v___x_2691_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_a_2689_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
}
else
{
lean_object* v_a_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2704_; 
lean_dec(v_a_2435_);
lean_del_object(v___x_2432_);
lean_dec(v_val_2430_);
lean_dec(v_val_2424_);
lean_dec_ref_known(v_a_2420_, 1);
lean_dec_ref_known(v___x_2416_, 2);
lean_del_object(v___x_2412_);
lean_dec(v_val_2410_);
lean_dec_ref(v_type_2393_);
v_a_2697_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2699_ = v___x_2436_;
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_a_2697_);
lean_dec(v___x_2436_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v___x_2702_; 
if (v_isShared_2700_ == 0)
{
v___x_2702_ = v___x_2699_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_a_2697_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
}
}
else
{
lean_object* v_a_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2712_; 
lean_del_object(v___x_2432_);
lean_dec(v_val_2430_);
lean_dec_ref_known(v_a_2420_, 1);
lean_dec(v_val_2424_);
lean_dec_ref_known(v___x_2416_, 2);
lean_del_object(v___x_2412_);
lean_dec(v_val_2410_);
lean_dec_ref(v_type_2393_);
v_a_2705_ = lean_ctor_get(v___x_2434_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2434_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2707_ = v___x_2434_;
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_a_2705_);
lean_dec(v___x_2434_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v___x_2710_; 
if (v_isShared_2708_ == 0)
{
v___x_2710_ = v___x_2707_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_a_2705_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
}
}
}
else
{
lean_object* v___x_2714_; lean_object* v___x_2716_; 
lean_dec(v_a_2426_);
lean_dec(v_val_2424_);
lean_dec_ref_known(v_a_2420_, 1);
lean_dec_ref_known(v___x_2416_, 2);
lean_del_object(v___x_2412_);
lean_dec(v_val_2410_);
lean_dec_ref(v_type_2393_);
v___x_2714_ = lean_box(0);
if (v_isShared_2429_ == 0)
{
lean_ctor_set(v___x_2428_, 0, v___x_2714_);
v___x_2716_ = v___x_2428_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v___x_2714_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
}
else
{
lean_object* v_a_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2726_; 
lean_dec(v_val_2424_);
lean_dec_ref_known(v_a_2420_, 1);
lean_dec_ref_known(v___x_2416_, 2);
lean_del_object(v___x_2412_);
lean_dec(v_val_2410_);
lean_dec_ref(v_type_2393_);
v_a_2719_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2721_ = v___x_2425_;
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_a_2719_);
lean_dec(v___x_2425_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v___x_2724_; 
if (v_isShared_2722_ == 0)
{
v___x_2724_ = v___x_2721_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_a_2719_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
}
else
{
lean_object* v___x_2727_; lean_object* v___x_2729_; 
lean_dec(v_a_2420_);
lean_dec_ref_known(v___x_2416_, 2);
lean_del_object(v___x_2412_);
lean_dec(v_val_2410_);
lean_dec_ref(v_type_2393_);
v___x_2727_ = lean_box(0);
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 0, v___x_2727_);
v___x_2729_ = v___x_2422_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v___x_2727_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
}
}
else
{
lean_object* v_a_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2739_; 
lean_dec_ref_known(v___x_2416_, 2);
lean_del_object(v___x_2412_);
lean_dec(v_val_2410_);
lean_dec_ref(v_type_2393_);
v_a_2732_ = lean_ctor_get(v___x_2419_, 0);
v_isSharedCheck_2739_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2734_ = v___x_2419_;
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_a_2732_);
lean_dec(v___x_2419_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2737_; 
if (v_isShared_2735_ == 0)
{
v___x_2737_ = v___x_2734_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_a_2732_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
}
}
}
else
{
lean_object* v___x_2741_; lean_object* v___x_2743_; 
lean_dec(v_a_2406_);
lean_dec_ref(v_type_2393_);
v___x_2741_ = lean_box(0);
if (v_isShared_2409_ == 0)
{
lean_ctor_set(v___x_2408_, 0, v___x_2741_);
v___x_2743_ = v___x_2408_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v___x_2741_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
}
else
{
lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2753_; 
lean_dec_ref(v_type_2393_);
v_a_2746_ = lean_ctor_get(v___x_2405_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2748_ = v___x_2405_;
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_dec(v___x_2405_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2751_; 
if (v_isShared_2749_ == 0)
{
v___x_2751_ = v___x_2748_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_a_2746_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___boxed(lean_object* v_type_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_){
_start:
{
lean_object* v_res_2762_; 
v_res_2762_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f(v_type_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_);
lean_dec(v_a_2760_);
lean_dec_ref(v_a_2759_);
lean_dec(v_a_2758_);
lean_dec_ref(v_a_2757_);
lean_dec(v_a_2756_);
lean_dec_ref(v_a_2755_);
return v_res_2762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classifyOrder_x3f___lam__0(lean_object* v_type_2763_, lean_object* v_a_2764_, lean_object* v_s_2765_){
_start:
{
lean_object* v_exp_2766_; lean_object* v_rings_2767_; lean_object* v_semirings_2768_; lean_object* v_ncRings_2769_; lean_object* v_ncSemirings_2770_; lean_object* v_typeClassify_2771_; lean_object* v_orders_2772_; lean_object* v_typeOrderClassify_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2781_; 
v_exp_2766_ = lean_ctor_get(v_s_2765_, 0);
v_rings_2767_ = lean_ctor_get(v_s_2765_, 1);
v_semirings_2768_ = lean_ctor_get(v_s_2765_, 2);
v_ncRings_2769_ = lean_ctor_get(v_s_2765_, 3);
v_ncSemirings_2770_ = lean_ctor_get(v_s_2765_, 4);
v_typeClassify_2771_ = lean_ctor_get(v_s_2765_, 5);
v_orders_2772_ = lean_ctor_get(v_s_2765_, 6);
v_typeOrderClassify_2773_ = lean_ctor_get(v_s_2765_, 7);
v_isSharedCheck_2781_ = !lean_is_exclusive(v_s_2765_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2775_ = v_s_2765_;
v_isShared_2776_ = v_isSharedCheck_2781_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_typeOrderClassify_2773_);
lean_inc(v_orders_2772_);
lean_inc(v_typeClassify_2771_);
lean_inc(v_ncSemirings_2770_);
lean_inc(v_ncRings_2769_);
lean_inc(v_semirings_2768_);
lean_inc(v_rings_2767_);
lean_inc(v_exp_2766_);
lean_dec(v_s_2765_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2781_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v___x_2777_; lean_object* v___x_2779_; 
v___x_2777_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1___redArg(v_typeOrderClassify_2773_, v_type_2763_, v_a_2764_);
if (v_isShared_2776_ == 0)
{
lean_ctor_set(v___x_2775_, 7, v___x_2777_);
v___x_2779_ = v___x_2775_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_exp_2766_);
lean_ctor_set(v_reuseFailAlloc_2780_, 1, v_rings_2767_);
lean_ctor_set(v_reuseFailAlloc_2780_, 2, v_semirings_2768_);
lean_ctor_set(v_reuseFailAlloc_2780_, 3, v_ncRings_2769_);
lean_ctor_set(v_reuseFailAlloc_2780_, 4, v_ncSemirings_2770_);
lean_ctor_set(v_reuseFailAlloc_2780_, 5, v_typeClassify_2771_);
lean_ctor_set(v_reuseFailAlloc_2780_, 6, v_orders_2772_);
lean_ctor_set(v_reuseFailAlloc_2780_, 7, v___x_2777_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classifyOrder_x3f(lean_object* v_type_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_){
_start:
{
lean_object* v___x_2790_; 
v___x_2790_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_2784_, v_a_2787_);
if (lean_obj_tag(v___x_2790_) == 0)
{
lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2822_; 
v_a_2791_ = lean_ctor_get(v___x_2790_, 0);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2790_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2793_ = v___x_2790_;
v_isShared_2794_ = v_isSharedCheck_2822_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_dec(v___x_2790_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2822_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v_typeOrderClassify_2795_; lean_object* v___x_2796_; 
v_typeOrderClassify_2795_ = lean_ctor_get(v_a_2791_, 7);
lean_inc_ref(v_typeOrderClassify_2795_);
lean_dec(v_a_2791_);
v___x_2796_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(v_typeOrderClassify_2795_, v_type_2782_);
lean_dec_ref(v_typeOrderClassify_2795_);
if (lean_obj_tag(v___x_2796_) == 1)
{
lean_object* v_val_2797_; lean_object* v___x_2799_; 
lean_dec_ref(v_type_2782_);
v_val_2797_ = lean_ctor_get(v___x_2796_, 0);
lean_inc(v_val_2797_);
lean_dec_ref_known(v___x_2796_, 1);
if (v_isShared_2794_ == 0)
{
lean_ctor_set(v___x_2793_, 0, v_val_2797_);
v___x_2799_ = v___x_2793_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_val_2797_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
else
{
lean_object* v___x_2801_; 
lean_dec(v___x_2796_);
lean_del_object(v___x_2793_);
lean_inc_ref(v_type_2782_);
v___x_2801_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f(v_type_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_);
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_object* v_a_2802_; lean_object* v___f_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
lean_inc_n(v_a_2802_, 2);
lean_dec_ref_known(v___x_2801_, 1);
v___f_2803_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_classifyOrder_x3f___lam__0), 3, 2);
lean_closure_set(v___f_2803_, 0, v_type_2782_);
lean_closure_set(v___f_2803_, 1, v_a_2802_);
v___x_2804_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_2805_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_2804_, v___f_2803_, v_a_2784_);
if (lean_obj_tag(v___x_2805_) == 0)
{
lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2812_; 
v_isSharedCheck_2812_ = !lean_is_exclusive(v___x_2805_);
if (v_isSharedCheck_2812_ == 0)
{
lean_object* v_unused_2813_; 
v_unused_2813_ = lean_ctor_get(v___x_2805_, 0);
lean_dec(v_unused_2813_);
v___x_2807_ = v___x_2805_;
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
else
{
lean_dec(v___x_2805_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2810_; 
if (v_isShared_2808_ == 0)
{
lean_ctor_set(v___x_2807_, 0, v_a_2802_);
v___x_2810_ = v___x_2807_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_a_2802_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
}
else
{
lean_object* v_a_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2821_; 
lean_dec(v_a_2802_);
v_a_2814_ = lean_ctor_get(v___x_2805_, 0);
v_isSharedCheck_2821_ = !lean_is_exclusive(v___x_2805_);
if (v_isSharedCheck_2821_ == 0)
{
v___x_2816_ = v___x_2805_;
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
else
{
lean_inc(v_a_2814_);
lean_dec(v___x_2805_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
lean_object* v___x_2819_; 
if (v_isShared_2817_ == 0)
{
v___x_2819_ = v___x_2816_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v_a_2814_);
v___x_2819_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
return v___x_2819_;
}
}
}
}
else
{
lean_dec_ref(v_type_2782_);
return v___x_2801_;
}
}
}
}
else
{
lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2830_; 
lean_dec_ref(v_type_2782_);
v_a_2823_ = lean_ctor_get(v___x_2790_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2790_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2825_ = v___x_2790_;
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_dec(v___x_2790_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2828_; 
if (v_isShared_2826_ == 0)
{
v___x_2828_ = v___x_2825_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_a_2823_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
return v___x_2828_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classifyOrder_x3f___boxed(lean_object* v_type_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_){
_start:
{
lean_object* v_res_2839_; 
v_res_2839_ = l_Lean_Meta_Sym_Arith_classifyOrder_x3f(v_type_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_);
lean_dec(v_a_2837_);
lean_dec_ref(v_a_2836_);
lean_dec(v_a_2835_);
lean_dec_ref(v_a_2834_);
lean_dec(v_a_2833_);
lean_dec_ref(v_a_2832_);
return v_res_2839_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Insts(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_SynthInstance(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Canon(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_DecLevel(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ring(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Classify(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_Arith_Insts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Canon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_DecLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Arith_Classify(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Arith_Insts(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_SynthInstance(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Canon(uint8_t builtin);
lean_object* initialize_Lean_Meta_DecLevel(uint8_t builtin);
lean_object* initialize_Init_Grind_Ring(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Arith_Classify(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Arith_Insts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Canon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_DecLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_Classify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Arith_Classify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Arith_Classify(builtin);
}
#ifdef __cplusplus
}
#endif
