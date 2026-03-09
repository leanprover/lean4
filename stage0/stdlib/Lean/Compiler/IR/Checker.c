// Lean compiler output
// Module: Lean.Compiler.IR.Checker
// Imports: public import Lean.Compiler.IR.CompilerM
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
lean_object* lean_get_max_ctor_fields(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getMaxCtorFields___boxed(lean_object*);
static lean_once_cell_t l_Lean_IR_Checker_maxCtorFields___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_Checker_maxCtorFields___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_maxCtorFields;
lean_object* lean_get_max_ctor_scalars_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getMaxCtorScalarsSize___boxed(lean_object*);
static lean_once_cell_t l_Lean_IR_Checker_maxCtorScalarsSize___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_Checker_maxCtorScalarsSize___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_maxCtorScalarsSize;
lean_object* lean_get_max_ctor_tag(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getMaxCtorTag___boxed(lean_object*);
static lean_once_cell_t l_Lean_IR_Checker_maxCtorTag___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_Checker_maxCtorTag___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_maxCtorTag;
lean_object* lean_get_usize_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getUSizeSize___boxed(lean_object*);
static lean_once_cell_t l_Lean_IR_Checker_usizeSize___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_Checker_usizeSize___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_usizeSize;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__5;
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_Checker_throwCheckerError___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "failed to compile definition, compiler IR check failed at `"};
static const lean_object* l_Lean_IR_Checker_throwCheckerError___redArg___closed__0 = (const lean_object*)&l_Lean_IR_Checker_throwCheckerError___redArg___closed__0_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_once_cell_t l_Lean_IR_Checker_throwCheckerError___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_Checker_throwCheckerError___redArg___closed__1;
static const lean_string_object l_Lean_IR_Checker_throwCheckerError___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "`. Error: "};
static const lean_object* l_Lean_IR_Checker_throwCheckerError___redArg___closed__2 = (const lean_object*)&l_Lean_IR_Checker_throwCheckerError___redArg___closed__2_value;
static lean_once_cell_t l_Lean_IR_Checker_throwCheckerError___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_Checker_throwCheckerError___redArg___closed__3;
lean_object* l_Lean_IR_Decl_name(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_Checker_markIndex___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "variable / join point index "};
static const lean_object* l_Lean_IR_Checker_markIndex___closed__0 = (const lean_object*)&l_Lean_IR_Checker_markIndex___closed__0_value;
static const lean_string_object l_Lean_IR_Checker_markIndex___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = " has already been used"};
static const lean_object* l_Lean_IR_Checker_markIndex___closed__1 = (const lean_object*)&l_Lean_IR_Checker_markIndex___closed__1_value;
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_Checker_getDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "depends on declaration '"};
static const lean_object* l_Lean_IR_Checker_getDecl___closed__0 = (const lean_object*)&l_Lean_IR_Checker_getDecl___closed__0_value;
static const lean_string_object l_Lean_IR_Checker_getDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 80, .m_capacity = 80, .m_length = 79, .m_data = "', which has no executable code; consider marking definition as 'noncomputable'"};
static const lean_object* l_Lean_IR_Checker_getDecl___closed__1 = (const lean_object*)&l_Lean_IR_Checker_getDecl___closed__1_value;
lean_object* l_Lean_IR_findEnvDecl_x27(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_Checker_checkVar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "unknown variable '"};
static const lean_object* l_Lean_IR_Checker_checkVar___closed__0 = (const lean_object*)&l_Lean_IR_Checker_checkVar___closed__0_value;
static const lean_string_object l_Lean_IR_Checker_checkVar___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "x_"};
static const lean_object* l_Lean_IR_Checker_checkVar___closed__1 = (const lean_object*)&l_Lean_IR_Checker_checkVar___closed__1_value;
static const lean_string_object l_Lean_IR_Checker_checkVar___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_IR_Checker_checkVar___closed__2 = (const lean_object*)&l_Lean_IR_Checker_checkVar___closed__2_value;
uint8_t l_Lean_IR_LocalContext_isLocalVar(lean_object*, lean_object*);
uint8_t l_Lean_IR_LocalContext_isParam(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_Checker_checkJP___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "unknown join point '"};
static const lean_object* l_Lean_IR_Checker_checkJP___closed__0 = (const lean_object*)&l_Lean_IR_Checker_checkJP___closed__0_value;
static const lean_string_object l_Lean_IR_Checker_checkJP___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "block_"};
static const lean_object* l_Lean_IR_Checker_checkJP___closed__1 = (const lean_object*)&l_Lean_IR_Checker_checkJP___closed__1_value;
uint8_t l_Lean_IR_LocalContext_isJP(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_Checker_checkEqTypes___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 34, .m_data = "unexpected type '{ty₁}' != '{ty₂}'"};
static const lean_object* l_Lean_IR_Checker_checkEqTypes___closed__0 = (const lean_object*)&l_Lean_IR_Checker_checkEqTypes___closed__0_value;
uint8_t l_Lean_IR_instBEqIRType_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_Checker_checkType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "unexpected type '"};
static const lean_object* l_Lean_IR_Checker_checkType___closed__0 = (const lean_object*)&l_Lean_IR_Checker_checkType___closed__0_value;
static const lean_string_object l_Lean_IR_Checker_checkType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_IR_Checker_checkType___closed__1 = (const lean_object*)&l_Lean_IR_Checker_checkType___closed__1_value;
lean_object* l_Lean_IR_instToFormatIRType___private__1(lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_Checker_checkObjType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "object expected"};
static const lean_object* l_Lean_IR_Checker_checkObjType___closed__0 = (const lean_object*)&l_Lean_IR_Checker_checkObjType___closed__0_value;
uint8_t l_Lean_IR_IRType_isObj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_Checker_checkScalarType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "scalar expected"};
static const lean_object* l_Lean_IR_Checker_checkScalarType___closed__0 = (const lean_object*)&l_Lean_IR_Checker_checkScalarType___closed__0_value;
uint8_t l_Lean_IR_IRType_isScalar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_getType(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_Checker_checkFullApp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "incorrect number of arguments to '"};
static const lean_object* l_Lean_IR_Checker_checkFullApp___closed__0 = (const lean_object*)&l_Lean_IR_Checker_checkFullApp___closed__0_value;
static const lean_string_object l_Lean_IR_Checker_checkFullApp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "', "};
static const lean_object* l_Lean_IR_Checker_checkFullApp___closed__1 = (const lean_object*)&l_Lean_IR_Checker_checkFullApp___closed__1_value;
static const lean_string_object l_Lean_IR_Checker_checkFullApp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = " provided, "};
static const lean_object* l_Lean_IR_Checker_checkFullApp___closed__2 = (const lean_object*)&l_Lean_IR_Checker_checkFullApp___closed__2_value;
static const lean_string_object l_Lean_IR_Checker_checkFullApp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " expected"};
static const lean_object* l_Lean_IR_Checker_checkFullApp___closed__3 = (const lean_object*)&l_Lean_IR_Checker_checkFullApp___closed__3_value;
lean_object* l_Lean_IR_Decl_params(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_Checker_checkPartialApp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "too many arguments to partial application '"};
static const lean_object* l_Lean_IR_Checker_checkPartialApp___closed__0 = (const lean_object*)&l_Lean_IR_Checker_checkPartialApp___closed__0_value;
static const lean_string_object l_Lean_IR_Checker_checkPartialApp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "', num. args: "};
static const lean_object* l_Lean_IR_Checker_checkPartialApp___closed__1 = (const lean_object*)&l_Lean_IR_Checker_checkPartialApp___closed__1_value;
static const lean_string_object l_Lean_IR_Checker_checkPartialApp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = ", arity: "};
static const lean_object* l_Lean_IR_Checker_checkPartialApp___closed__2 = (const lean_object*)&l_Lean_IR_Checker_checkPartialApp___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_Checker_checkExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "constructor '"};
static const lean_object* l_Lean_IR_Checker_checkExpr___closed__0 = (const lean_object*)&l_Lean_IR_Checker_checkExpr___closed__0_value;
static const lean_string_object l_Lean_IR_Checker_checkExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "' has too many scalar fields"};
static const lean_object* l_Lean_IR_Checker_checkExpr___closed__1 = (const lean_object*)&l_Lean_IR_Checker_checkExpr___closed__1_value;
static const lean_string_object l_Lean_IR_Checker_checkExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "' has too many fields"};
static const lean_object* l_Lean_IR_Checker_checkExpr___closed__2 = (const lean_object*)&l_Lean_IR_Checker_checkExpr___closed__2_value;
static const lean_string_object l_Lean_IR_Checker_checkExpr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "tag for constructor '"};
static const lean_object* l_Lean_IR_Checker_checkExpr___closed__3 = (const lean_object*)&l_Lean_IR_Checker_checkExpr___closed__3_value;
static const lean_string_object l_Lean_IR_Checker_checkExpr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "' is too big, this is a limitation of the current runtime"};
static const lean_object* l_Lean_IR_Checker_checkExpr___closed__4 = (const lean_object*)&l_Lean_IR_Checker_checkExpr___closed__4_value;
static const lean_string_object l_Lean_IR_Checker_checkExpr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "invalid proj index"};
static const lean_object* l_Lean_IR_Checker_checkExpr___closed__5 = (const lean_object*)&l_Lean_IR_Checker_checkExpr___closed__5_value;
static const lean_string_object l_Lean_IR_Checker_checkExpr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "unexpected IR type '"};
static const lean_object* l_Lean_IR_Checker_checkExpr___closed__6 = (const lean_object*)&l_Lean_IR_Checker_checkExpr___closed__6_value;
uint8_t l_Lean_IR_CtorInfo_isRef(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_addParam(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_IR_Checker_withParams___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_Checker_withParams___closed__0;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
static lean_once_cell_t l_Lean_IR_Checker_withParams___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_Checker_withParams___closed__1;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_Checker_withParams___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_Checker_withParams___closed__2 = (const lean_object*)&l_Lean_IR_Checker_withParams___closed__2_value;
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_Checker_withParams___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_Checker_withParams___closed__3 = (const lean_object*)&l_Lean_IR_Checker_withParams___closed__3_value;
static const lean_closure_object l_Lean_IR_Checker_withParams___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_Checker_withParams___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_Checker_withParams___closed__4 = (const lean_object*)&l_Lean_IR_Checker_withParams___closed__4_value;
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFnBody(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_addLocal(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_addJP(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Alt_body(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFnBody___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getMaxCtorFields___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_max_ctor_fields(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_maxCtorFields___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_get_max_ctor_fields(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_maxCtorFields(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_IR_Checker_maxCtorFields___closed__0, &l_Lean_IR_Checker_maxCtorFields___closed__0_once, _init_l_Lean_IR_Checker_maxCtorFields___closed__0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getMaxCtorScalarsSize___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_max_ctor_scalars_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_maxCtorScalarsSize___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_get_max_ctor_scalars_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_maxCtorScalarsSize(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_IR_Checker_maxCtorScalarsSize___closed__0, &l_Lean_IR_Checker_maxCtorScalarsSize___closed__0_once, _init_l_Lean_IR_Checker_maxCtorScalarsSize___closed__0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getMaxCtorTag___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_max_ctor_tag(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_maxCtorTag___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_get_max_ctor_tag(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_maxCtorTag(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_IR_Checker_maxCtorTag___closed__0, &l_Lean_IR_Checker_maxCtorTag___closed__0_once, _init_l_Lean_IR_Checker_maxCtorTag___closed__0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getUSizeSize___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_usize_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_usizeSize___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_get_usize_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_usizeSize(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_IR_Checker_usizeSize___closed__0, &l_Lean_IR_Checker_usizeSize___closed__0_once, _init_l_Lean_IR_Checker_usizeSize___closed__0);
return x_1;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_1);
lean_ctor_set(x_3, 6, x_1);
lean_ctor_set(x_3, 7, x_1);
lean_ctor_set(x_3, 8, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__4(void) {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(32u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__3);
x_6 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set_usize(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__4);
x_3 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__2);
x_9 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__5);
lean_inc_ref(x_7);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
lean_ctor_set(x_10, 3, x_7);
x_11 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_1);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_15; 
x_5 = lean_ctor_get(x_2, 5);
x_6 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0(x_1, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
x_15 = !lean_is_exclusive(x_6);
if (x_15 == 0)
{
x_8 = x_6;
x_9 = x_15;
goto block_14;
}
else
{
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
if (x_9 == 0)
{
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_10);
x_11 = x_8;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_10);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_Checker_throwCheckerError___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_IR_Checker_throwCheckerError___redArg___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_throwCheckerError___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_IR_Checker_throwCheckerError___redArg___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = lean_ctor_get(x_2, 1);
x_8 = l_Lean_IR_Decl_name(x_7);
x_9 = lean_obj_once(&l_Lean_IR_Checker_throwCheckerError___redArg___closed__1, &l_Lean_IR_Checker_throwCheckerError___redArg___closed__1_once, _init_l_Lean_IR_Checker_throwCheckerError___redArg___closed__1);
x_10 = 0;
x_11 = l_Lean_MessageData_ofConstName(x_8, x_10);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_obj_once(&l_Lean_IR_Checker_throwCheckerError___redArg___closed__3, &l_Lean_IR_Checker_throwCheckerError___redArg___closed__3_once, _init_l_Lean_IR_Checker_throwCheckerError___redArg___closed__3);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_stringToMessageData(x_1);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___redArg(x_16, x_4, x_5);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_throwCheckerError___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_Checker_throwCheckerError___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_Checker_throwCheckerError(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___redArg(x_2, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_289; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 3);
x_8 = lean_ctor_get(x_3, 4);
x_289 = !lean_is_exclusive(x_3);
if (x_289 == 0)
{
x_9 = x_3;
x_10 = x_289;
goto block_288;
}
else
{
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = x_289;
goto block_288;
}
block_288:
{
uint8_t x_11; 
x_11 = lean_nat_dec_lt(x_1, x_5);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = lean_nat_dec_eq(x_1, x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
x_13 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1___redArg(x_1, x_2, x_8);
x_14 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_13, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_13, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_13, 4);
lean_inc(x_20);
x_21 = lean_unsigned_to_nat(3u);
x_22 = lean_nat_mul(x_21, x_15);
x_23 = lean_nat_dec_lt(x_22, x_16);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_24 = lean_nat_add(x_14, x_15);
x_25 = lean_nat_add(x_24, x_16);
lean_dec(x_16);
lean_dec(x_24);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_13);
lean_ctor_set(x_9, 0, x_25);
x_26 = x_9;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_5);
lean_ctor_set(x_28, 2, x_6);
lean_ctor_set(x_28, 3, x_7);
lean_ctor_set(x_28, 4, x_13);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
else
{
lean_object* x_29; uint8_t x_30; uint8_t x_92; 
x_92 = !lean_is_exclusive(x_13);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_13, 4);
lean_dec(x_93);
x_94 = lean_ctor_get(x_13, 3);
lean_dec(x_94);
x_95 = lean_ctor_get(x_13, 2);
lean_dec(x_95);
x_96 = lean_ctor_get(x_13, 1);
lean_dec(x_96);
x_97 = lean_ctor_get(x_13, 0);
lean_dec(x_97);
x_29 = x_13;
x_30 = x_92;
goto block_91;
}
else
{
lean_dec(x_13);
x_29 = lean_box(0);
x_30 = x_92;
goto block_91;
}
block_91:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_31 = lean_ctor_get(x_19, 0);
x_32 = lean_ctor_get(x_19, 1);
x_33 = lean_ctor_get(x_19, 2);
x_34 = lean_ctor_get(x_19, 3);
x_35 = lean_ctor_get(x_19, 4);
x_36 = lean_ctor_get(x_20, 0);
x_37 = lean_unsigned_to_nat(2u);
x_38 = lean_nat_mul(x_37, x_36);
x_39 = lean_nat_dec_lt(x_31, x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; uint8_t x_67; 
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
x_67 = !lean_is_exclusive(x_19);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_19, 4);
lean_dec(x_68);
x_69 = lean_ctor_get(x_19, 3);
lean_dec(x_69);
x_70 = lean_ctor_get(x_19, 2);
lean_dec(x_70);
x_71 = lean_ctor_get(x_19, 1);
lean_dec(x_71);
x_72 = lean_ctor_get(x_19, 0);
lean_dec(x_72);
x_40 = x_19;
x_41 = x_67;
goto block_66;
}
else
{
lean_dec(x_19);
x_40 = lean_box(0);
x_41 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_55; 
x_42 = lean_nat_add(x_14, x_15);
x_43 = lean_nat_add(x_42, x_16);
lean_dec(x_16);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_34, 0);
lean_inc(x_64);
x_55 = x_64;
goto block_63;
}
else
{
lean_object* x_65; 
x_65 = lean_unsigned_to_nat(0u);
x_55 = x_65;
goto block_63;
}
block_54:
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_nat_add(x_44, x_46);
lean_dec(x_46);
lean_dec(x_44);
if (x_41 == 0)
{
lean_ctor_set(x_40, 4, x_20);
lean_ctor_set(x_40, 3, x_35);
lean_ctor_set(x_40, 2, x_18);
lean_ctor_set(x_40, 1, x_17);
lean_ctor_set(x_40, 0, x_47);
x_48 = x_40;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_17);
lean_ctor_set(x_53, 2, x_18);
lean_ctor_set(x_53, 3, x_35);
lean_ctor_set(x_53, 4, x_20);
x_48 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_49; 
if (x_30 == 0)
{
lean_ctor_set(x_29, 4, x_48);
lean_ctor_set(x_29, 3, x_45);
lean_ctor_set(x_29, 2, x_33);
lean_ctor_set(x_29, 1, x_32);
lean_ctor_set(x_29, 0, x_43);
x_49 = x_29;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_51, 0, x_43);
lean_ctor_set(x_51, 1, x_32);
lean_ctor_set(x_51, 2, x_33);
lean_ctor_set(x_51, 3, x_45);
lean_ctor_set(x_51, 4, x_48);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
block_63:
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_nat_add(x_42, x_55);
lean_dec(x_55);
lean_dec(x_42);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_34);
lean_ctor_set(x_9, 0, x_56);
x_57 = x_9;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set(x_62, 1, x_5);
lean_ctor_set(x_62, 2, x_6);
lean_ctor_set(x_62, 3, x_7);
lean_ctor_set(x_62, 4, x_34);
x_57 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_58; 
x_58 = lean_nat_add(x_14, x_36);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_35, 0);
lean_inc(x_59);
x_44 = x_58;
x_45 = x_57;
x_46 = x_59;
goto block_54;
}
else
{
lean_object* x_60; 
x_60 = lean_unsigned_to_nat(0u);
x_44 = x_58;
x_45 = x_57;
x_46 = x_60;
goto block_54;
}
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_del_object(x_9);
x_73 = lean_nat_add(x_14, x_15);
x_74 = lean_nat_add(x_73, x_16);
lean_dec(x_16);
x_75 = lean_nat_add(x_73, x_31);
lean_dec(x_73);
lean_inc_ref(x_7);
if (x_30 == 0)
{
lean_ctor_set(x_29, 4, x_19);
lean_ctor_set(x_29, 3, x_7);
lean_ctor_set(x_29, 2, x_6);
lean_ctor_set(x_29, 1, x_5);
lean_ctor_set(x_29, 0, x_75);
x_76 = x_29;
goto block_89;
}
else
{
lean_object* x_90; 
x_90 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_90, 0, x_75);
lean_ctor_set(x_90, 1, x_5);
lean_ctor_set(x_90, 2, x_6);
lean_ctor_set(x_90, 3, x_7);
lean_ctor_set(x_90, 4, x_19);
x_76 = x_90;
goto block_89;
}
block_89:
{
lean_object* x_77; uint8_t x_78; uint8_t x_83; 
x_83 = !lean_is_exclusive(x_7);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_84 = lean_ctor_get(x_7, 4);
lean_dec(x_84);
x_85 = lean_ctor_get(x_7, 3);
lean_dec(x_85);
x_86 = lean_ctor_get(x_7, 2);
lean_dec(x_86);
x_87 = lean_ctor_get(x_7, 1);
lean_dec(x_87);
x_88 = lean_ctor_get(x_7, 0);
lean_dec(x_88);
x_77 = x_7;
x_78 = x_83;
goto block_82;
}
else
{
lean_dec(x_7);
x_77 = lean_box(0);
x_78 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_79; 
if (x_78 == 0)
{
lean_ctor_set(x_77, 4, x_20);
lean_ctor_set(x_77, 3, x_76);
lean_ctor_set(x_77, 2, x_18);
lean_ctor_set(x_77, 1, x_17);
lean_ctor_set(x_77, 0, x_74);
x_79 = x_77;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_81, 0, x_74);
lean_ctor_set(x_81, 1, x_17);
lean_ctor_set(x_81, 2, x_18);
lean_ctor_set(x_81, 3, x_76);
lean_ctor_set(x_81, 4, x_20);
x_79 = x_81;
goto block_80;
}
block_80:
{
return x_79;
}
}
}
}
}
}
}
else
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_13, 3);
lean_inc(x_98);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; uint8_t x_124; 
x_99 = lean_ctor_get(x_13, 4);
x_100 = lean_ctor_get(x_13, 1);
x_101 = lean_ctor_get(x_13, 2);
x_124 = !lean_is_exclusive(x_13);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_13, 3);
lean_dec(x_125);
x_126 = lean_ctor_get(x_13, 0);
lean_dec(x_126);
x_102 = x_13;
x_103 = x_124;
goto block_123;
}
else
{
lean_inc(x_99);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_13);
x_102 = lean_box(0);
x_103 = x_124;
goto block_123;
}
block_123:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; uint8_t x_119; 
x_104 = lean_ctor_get(x_98, 1);
x_105 = lean_ctor_get(x_98, 2);
x_119 = !lean_is_exclusive(x_98);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_98, 4);
lean_dec(x_120);
x_121 = lean_ctor_get(x_98, 3);
lean_dec(x_121);
x_122 = lean_ctor_get(x_98, 0);
lean_dec(x_122);
x_106 = x_98;
x_107 = x_119;
goto block_118;
}
else
{
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_98);
x_106 = lean_box(0);
x_107 = x_119;
goto block_118;
}
block_118:
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_unsigned_to_nat(3u);
lean_inc_n(x_99, 2);
if (x_107 == 0)
{
lean_ctor_set(x_106, 4, x_99);
lean_ctor_set(x_106, 3, x_99);
lean_ctor_set(x_106, 2, x_6);
lean_ctor_set(x_106, 1, x_5);
lean_ctor_set(x_106, 0, x_14);
x_109 = x_106;
goto block_116;
}
else
{
lean_object* x_117; 
x_117 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_117, 0, x_14);
lean_ctor_set(x_117, 1, x_5);
lean_ctor_set(x_117, 2, x_6);
lean_ctor_set(x_117, 3, x_99);
lean_ctor_set(x_117, 4, x_99);
x_109 = x_117;
goto block_116;
}
block_116:
{
lean_object* x_110; 
lean_inc(x_99);
if (x_103 == 0)
{
lean_ctor_set(x_102, 3, x_99);
lean_ctor_set(x_102, 0, x_14);
x_110 = x_102;
goto block_114;
}
else
{
lean_object* x_115; 
x_115 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_115, 0, x_14);
lean_ctor_set(x_115, 1, x_100);
lean_ctor_set(x_115, 2, x_101);
lean_ctor_set(x_115, 3, x_99);
lean_ctor_set(x_115, 4, x_99);
x_110 = x_115;
goto block_114;
}
block_114:
{
lean_object* x_111; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_110);
lean_ctor_set(x_9, 3, x_109);
lean_ctor_set(x_9, 2, x_105);
lean_ctor_set(x_9, 1, x_104);
lean_ctor_set(x_9, 0, x_108);
x_111 = x_9;
goto block_112;
}
else
{
lean_object* x_113; 
x_113 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_113, 0, x_108);
lean_ctor_set(x_113, 1, x_104);
lean_ctor_set(x_113, 2, x_105);
lean_ctor_set(x_113, 3, x_109);
lean_ctor_set(x_113, 4, x_110);
x_111 = x_113;
goto block_112;
}
block_112:
{
return x_111;
}
}
}
}
}
}
else
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_13, 4);
lean_inc(x_127);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; uint8_t x_140; 
x_128 = lean_ctor_get(x_13, 1);
x_129 = lean_ctor_get(x_13, 2);
x_140 = !lean_is_exclusive(x_13);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_13, 4);
lean_dec(x_141);
x_142 = lean_ctor_get(x_13, 3);
lean_dec(x_142);
x_143 = lean_ctor_get(x_13, 0);
lean_dec(x_143);
x_130 = x_13;
x_131 = x_140;
goto block_139;
}
else
{
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_13);
x_130 = lean_box(0);
x_131 = x_140;
goto block_139;
}
block_139:
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_unsigned_to_nat(3u);
if (x_131 == 0)
{
lean_ctor_set(x_130, 4, x_98);
lean_ctor_set(x_130, 2, x_6);
lean_ctor_set(x_130, 1, x_5);
lean_ctor_set(x_130, 0, x_14);
x_133 = x_130;
goto block_137;
}
else
{
lean_object* x_138; 
x_138 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_138, 0, x_14);
lean_ctor_set(x_138, 1, x_5);
lean_ctor_set(x_138, 2, x_6);
lean_ctor_set(x_138, 3, x_98);
lean_ctor_set(x_138, 4, x_98);
x_133 = x_138;
goto block_137;
}
block_137:
{
lean_object* x_134; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_127);
lean_ctor_set(x_9, 3, x_133);
lean_ctor_set(x_9, 2, x_129);
lean_ctor_set(x_9, 1, x_128);
lean_ctor_set(x_9, 0, x_132);
x_134 = x_9;
goto block_135;
}
else
{
lean_object* x_136; 
x_136 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_136, 0, x_132);
lean_ctor_set(x_136, 1, x_128);
lean_ctor_set(x_136, 2, x_129);
lean_ctor_set(x_136, 3, x_133);
lean_ctor_set(x_136, 4, x_127);
x_134 = x_136;
goto block_135;
}
block_135:
{
return x_134;
}
}
}
}
else
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_unsigned_to_nat(2u);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_13);
lean_ctor_set(x_9, 3, x_127);
lean_ctor_set(x_9, 0, x_144);
x_145 = x_9;
goto block_146;
}
else
{
lean_object* x_147; 
x_147 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_5);
lean_ctor_set(x_147, 2, x_6);
lean_ctor_set(x_147, 3, x_127);
lean_ctor_set(x_147, 4, x_13);
x_145 = x_147;
goto block_146;
}
block_146:
{
return x_145;
}
}
}
}
}
else
{
lean_object* x_148; 
lean_dec(x_6);
lean_dec(x_5);
if (x_10 == 0)
{
lean_ctor_set(x_9, 2, x_2);
lean_ctor_set(x_9, 1, x_1);
x_148 = x_9;
goto block_149;
}
else
{
lean_object* x_150; 
x_150 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_150, 0, x_4);
lean_ctor_set(x_150, 1, x_1);
lean_ctor_set(x_150, 2, x_2);
lean_ctor_set(x_150, 3, x_7);
lean_ctor_set(x_150, 4, x_8);
x_148 = x_150;
goto block_149;
}
block_149:
{
return x_148;
}
}
}
else
{
lean_object* x_151; lean_object* x_152; 
lean_dec(x_4);
x_151 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1___redArg(x_1, x_2, x_7);
x_152 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_153 = lean_ctor_get(x_8, 0);
x_154 = lean_ctor_get(x_151, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_151, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_151, 2);
lean_inc(x_156);
x_157 = lean_ctor_get(x_151, 3);
lean_inc(x_157);
x_158 = lean_ctor_get(x_151, 4);
lean_inc(x_158);
x_159 = lean_unsigned_to_nat(3u);
x_160 = lean_nat_mul(x_159, x_153);
x_161 = lean_nat_dec_lt(x_160, x_154);
lean_dec(x_160);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
x_162 = lean_nat_add(x_152, x_154);
lean_dec(x_154);
x_163 = lean_nat_add(x_162, x_153);
lean_dec(x_162);
if (x_10 == 0)
{
lean_ctor_set(x_9, 3, x_151);
lean_ctor_set(x_9, 0, x_163);
x_164 = x_9;
goto block_165;
}
else
{
lean_object* x_166; 
x_166 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_5);
lean_ctor_set(x_166, 2, x_6);
lean_ctor_set(x_166, 3, x_151);
lean_ctor_set(x_166, 4, x_8);
x_164 = x_166;
goto block_165;
}
block_165:
{
return x_164;
}
}
else
{
lean_object* x_167; uint8_t x_168; uint8_t x_232; 
x_232 = !lean_is_exclusive(x_151);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_233 = lean_ctor_get(x_151, 4);
lean_dec(x_233);
x_234 = lean_ctor_get(x_151, 3);
lean_dec(x_234);
x_235 = lean_ctor_get(x_151, 2);
lean_dec(x_235);
x_236 = lean_ctor_get(x_151, 1);
lean_dec(x_236);
x_237 = lean_ctor_get(x_151, 0);
lean_dec(x_237);
x_167 = x_151;
x_168 = x_232;
goto block_231;
}
else
{
lean_dec(x_151);
x_167 = lean_box(0);
x_168 = x_232;
goto block_231;
}
block_231:
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_169 = lean_ctor_get(x_157, 0);
x_170 = lean_ctor_get(x_158, 0);
x_171 = lean_ctor_get(x_158, 1);
x_172 = lean_ctor_get(x_158, 2);
x_173 = lean_ctor_get(x_158, 3);
x_174 = lean_ctor_get(x_158, 4);
x_175 = lean_unsigned_to_nat(2u);
x_176 = lean_nat_mul(x_175, x_169);
x_177 = lean_nat_dec_lt(x_170, x_176);
lean_dec(x_176);
if (x_177 == 0)
{
lean_object* x_178; uint8_t x_179; uint8_t x_206; 
lean_inc(x_174);
lean_inc(x_173);
lean_inc(x_172);
lean_inc(x_171);
x_206 = !lean_is_exclusive(x_158);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_207 = lean_ctor_get(x_158, 4);
lean_dec(x_207);
x_208 = lean_ctor_get(x_158, 3);
lean_dec(x_208);
x_209 = lean_ctor_get(x_158, 2);
lean_dec(x_209);
x_210 = lean_ctor_get(x_158, 1);
lean_dec(x_210);
x_211 = lean_ctor_get(x_158, 0);
lean_dec(x_211);
x_178 = x_158;
x_179 = x_206;
goto block_205;
}
else
{
lean_dec(x_158);
x_178 = lean_box(0);
x_179 = x_206;
goto block_205;
}
block_205:
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_193; lean_object* x_194; 
x_180 = lean_nat_add(x_152, x_154);
lean_dec(x_154);
x_181 = lean_nat_add(x_180, x_153);
lean_dec(x_180);
x_193 = lean_nat_add(x_152, x_169);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_203; 
x_203 = lean_ctor_get(x_173, 0);
lean_inc(x_203);
x_194 = x_203;
goto block_202;
}
else
{
lean_object* x_204; 
x_204 = lean_unsigned_to_nat(0u);
x_194 = x_204;
goto block_202;
}
block_192:
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_nat_add(x_183, x_184);
lean_dec(x_184);
lean_dec(x_183);
if (x_179 == 0)
{
lean_ctor_set(x_178, 4, x_8);
lean_ctor_set(x_178, 3, x_174);
lean_ctor_set(x_178, 2, x_6);
lean_ctor_set(x_178, 1, x_5);
lean_ctor_set(x_178, 0, x_185);
x_186 = x_178;
goto block_190;
}
else
{
lean_object* x_191; 
x_191 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_191, 0, x_185);
lean_ctor_set(x_191, 1, x_5);
lean_ctor_set(x_191, 2, x_6);
lean_ctor_set(x_191, 3, x_174);
lean_ctor_set(x_191, 4, x_8);
x_186 = x_191;
goto block_190;
}
block_190:
{
lean_object* x_187; 
if (x_168 == 0)
{
lean_ctor_set(x_167, 4, x_186);
lean_ctor_set(x_167, 3, x_182);
lean_ctor_set(x_167, 2, x_172);
lean_ctor_set(x_167, 1, x_171);
lean_ctor_set(x_167, 0, x_181);
x_187 = x_167;
goto block_188;
}
else
{
lean_object* x_189; 
x_189 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_189, 0, x_181);
lean_ctor_set(x_189, 1, x_171);
lean_ctor_set(x_189, 2, x_172);
lean_ctor_set(x_189, 3, x_182);
lean_ctor_set(x_189, 4, x_186);
x_187 = x_189;
goto block_188;
}
block_188:
{
return x_187;
}
}
}
block_202:
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_nat_add(x_193, x_194);
lean_dec(x_194);
lean_dec(x_193);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_173);
lean_ctor_set(x_9, 3, x_157);
lean_ctor_set(x_9, 2, x_156);
lean_ctor_set(x_9, 1, x_155);
lean_ctor_set(x_9, 0, x_195);
x_196 = x_9;
goto block_200;
}
else
{
lean_object* x_201; 
x_201 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_201, 0, x_195);
lean_ctor_set(x_201, 1, x_155);
lean_ctor_set(x_201, 2, x_156);
lean_ctor_set(x_201, 3, x_157);
lean_ctor_set(x_201, 4, x_173);
x_196 = x_201;
goto block_200;
}
block_200:
{
lean_object* x_197; 
x_197 = lean_nat_add(x_152, x_153);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_198; 
x_198 = lean_ctor_get(x_174, 0);
lean_inc(x_198);
x_182 = x_196;
x_183 = x_197;
x_184 = x_198;
goto block_192;
}
else
{
lean_object* x_199; 
x_199 = lean_unsigned_to_nat(0u);
x_182 = x_196;
x_183 = x_197;
x_184 = x_199;
goto block_192;
}
}
}
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_del_object(x_9);
x_212 = lean_nat_add(x_152, x_154);
lean_dec(x_154);
x_213 = lean_nat_add(x_212, x_153);
lean_dec(x_212);
x_214 = lean_nat_add(x_152, x_153);
x_215 = lean_nat_add(x_214, x_170);
lean_dec(x_214);
lean_inc_ref(x_8);
if (x_168 == 0)
{
lean_ctor_set(x_167, 4, x_8);
lean_ctor_set(x_167, 3, x_158);
lean_ctor_set(x_167, 2, x_6);
lean_ctor_set(x_167, 1, x_5);
lean_ctor_set(x_167, 0, x_215);
x_216 = x_167;
goto block_229;
}
else
{
lean_object* x_230; 
x_230 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_230, 0, x_215);
lean_ctor_set(x_230, 1, x_5);
lean_ctor_set(x_230, 2, x_6);
lean_ctor_set(x_230, 3, x_158);
lean_ctor_set(x_230, 4, x_8);
x_216 = x_230;
goto block_229;
}
block_229:
{
lean_object* x_217; uint8_t x_218; uint8_t x_223; 
x_223 = !lean_is_exclusive(x_8);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_224 = lean_ctor_get(x_8, 4);
lean_dec(x_224);
x_225 = lean_ctor_get(x_8, 3);
lean_dec(x_225);
x_226 = lean_ctor_get(x_8, 2);
lean_dec(x_226);
x_227 = lean_ctor_get(x_8, 1);
lean_dec(x_227);
x_228 = lean_ctor_get(x_8, 0);
lean_dec(x_228);
x_217 = x_8;
x_218 = x_223;
goto block_222;
}
else
{
lean_dec(x_8);
x_217 = lean_box(0);
x_218 = x_223;
goto block_222;
}
block_222:
{
lean_object* x_219; 
if (x_218 == 0)
{
lean_ctor_set(x_217, 4, x_216);
lean_ctor_set(x_217, 3, x_157);
lean_ctor_set(x_217, 2, x_156);
lean_ctor_set(x_217, 1, x_155);
lean_ctor_set(x_217, 0, x_213);
x_219 = x_217;
goto block_220;
}
else
{
lean_object* x_221; 
x_221 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_221, 0, x_213);
lean_ctor_set(x_221, 1, x_155);
lean_ctor_set(x_221, 2, x_156);
lean_ctor_set(x_221, 3, x_157);
lean_ctor_set(x_221, 4, x_216);
x_219 = x_221;
goto block_220;
}
block_220:
{
return x_219;
}
}
}
}
}
}
}
else
{
lean_object* x_238; 
x_238 = lean_ctor_get(x_151, 3);
lean_inc(x_238);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; uint8_t x_252; 
x_239 = lean_ctor_get(x_151, 4);
x_240 = lean_ctor_get(x_151, 1);
x_241 = lean_ctor_get(x_151, 2);
x_252 = !lean_is_exclusive(x_151);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; 
x_253 = lean_ctor_get(x_151, 3);
lean_dec(x_253);
x_254 = lean_ctor_get(x_151, 0);
lean_dec(x_254);
x_242 = x_151;
x_243 = x_252;
goto block_251;
}
else
{
lean_inc(x_239);
lean_inc(x_241);
lean_inc(x_240);
lean_dec(x_151);
x_242 = lean_box(0);
x_243 = x_252;
goto block_251;
}
block_251:
{
lean_object* x_244; lean_object* x_245; 
x_244 = lean_unsigned_to_nat(3u);
lean_inc(x_239);
if (x_243 == 0)
{
lean_ctor_set(x_242, 3, x_239);
lean_ctor_set(x_242, 2, x_6);
lean_ctor_set(x_242, 1, x_5);
lean_ctor_set(x_242, 0, x_152);
x_245 = x_242;
goto block_249;
}
else
{
lean_object* x_250; 
x_250 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_250, 0, x_152);
lean_ctor_set(x_250, 1, x_5);
lean_ctor_set(x_250, 2, x_6);
lean_ctor_set(x_250, 3, x_239);
lean_ctor_set(x_250, 4, x_239);
x_245 = x_250;
goto block_249;
}
block_249:
{
lean_object* x_246; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_245);
lean_ctor_set(x_9, 3, x_238);
lean_ctor_set(x_9, 2, x_241);
lean_ctor_set(x_9, 1, x_240);
lean_ctor_set(x_9, 0, x_244);
x_246 = x_9;
goto block_247;
}
else
{
lean_object* x_248; 
x_248 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_248, 0, x_244);
lean_ctor_set(x_248, 1, x_240);
lean_ctor_set(x_248, 2, x_241);
lean_ctor_set(x_248, 3, x_238);
lean_ctor_set(x_248, 4, x_245);
x_246 = x_248;
goto block_247;
}
block_247:
{
return x_246;
}
}
}
}
else
{
lean_object* x_255; 
x_255 = lean_ctor_get(x_151, 4);
lean_inc(x_255);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; uint8_t x_280; 
x_256 = lean_ctor_get(x_151, 1);
x_257 = lean_ctor_get(x_151, 2);
x_280 = !lean_is_exclusive(x_151);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_281 = lean_ctor_get(x_151, 4);
lean_dec(x_281);
x_282 = lean_ctor_get(x_151, 3);
lean_dec(x_282);
x_283 = lean_ctor_get(x_151, 0);
lean_dec(x_283);
x_258 = x_151;
x_259 = x_280;
goto block_279;
}
else
{
lean_inc(x_257);
lean_inc(x_256);
lean_dec(x_151);
x_258 = lean_box(0);
x_259 = x_280;
goto block_279;
}
block_279:
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; uint8_t x_275; 
x_260 = lean_ctor_get(x_255, 1);
x_261 = lean_ctor_get(x_255, 2);
x_275 = !lean_is_exclusive(x_255);
if (x_275 == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_276 = lean_ctor_get(x_255, 4);
lean_dec(x_276);
x_277 = lean_ctor_get(x_255, 3);
lean_dec(x_277);
x_278 = lean_ctor_get(x_255, 0);
lean_dec(x_278);
x_262 = x_255;
x_263 = x_275;
goto block_274;
}
else
{
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_255);
x_262 = lean_box(0);
x_263 = x_275;
goto block_274;
}
block_274:
{
lean_object* x_264; lean_object* x_265; 
x_264 = lean_unsigned_to_nat(3u);
if (x_263 == 0)
{
lean_ctor_set(x_262, 4, x_238);
lean_ctor_set(x_262, 3, x_238);
lean_ctor_set(x_262, 2, x_257);
lean_ctor_set(x_262, 1, x_256);
lean_ctor_set(x_262, 0, x_152);
x_265 = x_262;
goto block_272;
}
else
{
lean_object* x_273; 
x_273 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_273, 0, x_152);
lean_ctor_set(x_273, 1, x_256);
lean_ctor_set(x_273, 2, x_257);
lean_ctor_set(x_273, 3, x_238);
lean_ctor_set(x_273, 4, x_238);
x_265 = x_273;
goto block_272;
}
block_272:
{
lean_object* x_266; 
if (x_259 == 0)
{
lean_ctor_set(x_258, 4, x_238);
lean_ctor_set(x_258, 2, x_6);
lean_ctor_set(x_258, 1, x_5);
lean_ctor_set(x_258, 0, x_152);
x_266 = x_258;
goto block_270;
}
else
{
lean_object* x_271; 
x_271 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_271, 0, x_152);
lean_ctor_set(x_271, 1, x_5);
lean_ctor_set(x_271, 2, x_6);
lean_ctor_set(x_271, 3, x_238);
lean_ctor_set(x_271, 4, x_238);
x_266 = x_271;
goto block_270;
}
block_270:
{
lean_object* x_267; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_266);
lean_ctor_set(x_9, 3, x_265);
lean_ctor_set(x_9, 2, x_261);
lean_ctor_set(x_9, 1, x_260);
lean_ctor_set(x_9, 0, x_264);
x_267 = x_9;
goto block_268;
}
else
{
lean_object* x_269; 
x_269 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_269, 0, x_264);
lean_ctor_set(x_269, 1, x_260);
lean_ctor_set(x_269, 2, x_261);
lean_ctor_set(x_269, 3, x_265);
lean_ctor_set(x_269, 4, x_266);
x_267 = x_269;
goto block_268;
}
block_268:
{
return x_267;
}
}
}
}
}
}
else
{
lean_object* x_284; lean_object* x_285; 
x_284 = lean_unsigned_to_nat(2u);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_255);
lean_ctor_set(x_9, 3, x_151);
lean_ctor_set(x_9, 0, x_284);
x_285 = x_9;
goto block_286;
}
else
{
lean_object* x_287; 
x_287 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_287, 0, x_284);
lean_ctor_set(x_287, 1, x_5);
lean_ctor_set(x_287, 2, x_6);
lean_ctor_set(x_287, 3, x_151);
lean_ctor_set(x_287, 4, x_255);
x_285 = x_287;
goto block_286;
}
block_286:
{
return x_285;
}
}
}
}
}
}
}
else
{
lean_object* x_290; lean_object* x_291; 
x_290 = lean_unsigned_to_nat(1u);
x_291 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_1);
lean_ctor_set(x_291, 2, x_2);
lean_ctor_set(x_291, 3, x_3);
lean_ctor_set(x_291, 4, x_3);
return x_291;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_ctor_get(x_2, 4);
x_6 = lean_nat_dec_lt(x_1, x_3);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = lean_nat_dec_eq(x_1, x_3);
if (x_7 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_7;
}
}
else
{
x_2 = x_4;
goto _start;
}
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_13; lean_object* x_19; uint8_t x_20; 
x_19 = lean_st_ref_get(x_3);
x_20 = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg(x_1, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
x_13 = x_3;
goto block_18;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = ((lean_object*)(l_Lean_IR_Checker_markIndex___closed__0));
x_22 = l_Nat_reprFast(x_1);
x_23 = lean_string_append(x_21, x_22);
lean_dec_ref(x_22);
x_24 = ((lean_object*)(l_Lean_IR_Checker_markIndex___closed__1));
x_25 = lean_string_append(x_23, x_24);
x_26 = l_Lean_IR_Checker_throwCheckerError___redArg(x_25, x_2, x_3, x_4, x_5);
return x_26;
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_st_ref_set(x_7, x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_8);
return x_11;
}
block_18:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_st_ref_take(x_13);
x_15 = lean_box(0);
x_16 = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg(x_1, x_14);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1___redArg(x_1, x_15, x_14);
x_7 = x_13;
x_8 = x_15;
x_9 = x_17;
goto block_12;
}
else
{
lean_dec(x_1);
x_7 = x_13;
x_8 = x_15;
x_9 = x_14;
goto block_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_markIndex(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_markIndex(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_markVar(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_markIndex(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_markJP(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_1);
x_10 = l_Lean_IR_findEnvDecl_x27(x_8, x_1, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = ((lean_object*)(l_Lean_IR_Checker_getDecl___closed__0));
x_12 = 1;
x_13 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_1, x_12);
x_14 = lean_string_append(x_11, x_13);
lean_dec_ref(x_13);
x_15 = ((lean_object*)(l_Lean_IR_Checker_getDecl___closed__1));
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Lean_IR_Checker_throwCheckerError___redArg(x_16, x_2, x_3, x_4, x_5);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_25; 
lean_dec(x_1);
x_18 = lean_ctor_get(x_10, 0);
x_25 = !lean_is_exclusive(x_10);
if (x_25 == 0)
{
x_19 = x_10;
x_20 = x_25;
goto block_24;
}
else
{
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_box(0);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_20 == 0)
{
lean_ctor_set_tag(x_19, 0);
x_21 = x_19;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_18);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_getDecl(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = l_Lean_IR_LocalContext_isLocalVar(x_19, x_1);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = l_Lean_IR_LocalContext_isParam(x_19, x_1);
x_7 = x_21;
goto block_18;
}
else
{
x_7 = x_20;
goto block_18;
}
block_18:
{
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__0));
x_9 = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__1));
x_10 = l_Nat_reprFast(x_1);
x_11 = lean_string_append(x_9, x_10);
lean_dec_ref(x_10);
x_12 = lean_string_append(x_8, x_11);
lean_dec_ref(x_11);
x_13 = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
x_14 = lean_string_append(x_12, x_13);
x_15 = l_Lean_IR_Checker_throwCheckerError___redArg(x_14, x_2, x_3, x_4, x_5);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_checkVar(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = l_Lean_IR_LocalContext_isJP(x_7, x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = ((lean_object*)(l_Lean_IR_Checker_checkJP___closed__0));
x_10 = ((lean_object*)(l_Lean_IR_Checker_checkJP___closed__1));
x_11 = l_Nat_reprFast(x_1);
x_12 = lean_string_append(x_10, x_11);
lean_dec_ref(x_11);
x_13 = lean_string_append(x_9, x_12);
lean_dec_ref(x_12);
x_14 = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
x_15 = lean_string_append(x_13, x_14);
x_16 = l_Lean_IR_Checker_throwCheckerError___redArg(x_15, x_2, x_3, x_4, x_5);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_checkJP(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = l_Lean_IR_Checker_checkVar(x_7, x_2, x_3, x_4, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_checkArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget_borrowed(x_1, x_2);
lean_inc(x_11);
x_12 = l_Lean_IR_Checker_checkArg(x_11, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; size_t x_14; size_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_2 = x_15;
x_4 = x_13;
goto _start;
}
else
{
return x_12;
}
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_4);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_get_size(x_1);
x_9 = lean_box(0);
x_10 = lean_nat_dec_lt(x_7, x_8);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_9);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_8, x_8);
if (x_12 == 0)
{
if (x_10 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_9);
return x_13;
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_8);
x_16 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(x_1, x_14, x_15, x_9, x_2, x_3, x_4, x_5);
return x_16;
}
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_8);
x_19 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(x_1, x_17, x_18, x_9, x_2, x_3, x_4, x_5);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_checkArgs(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_IR_instBEqIRType_beq(x_1, x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = ((lean_object*)(l_Lean_IR_Checker_checkEqTypes___closed__0));
x_10 = l_Lean_IR_Checker_throwCheckerError___redArg(x_9, x_3, x_4, x_5, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_Checker_checkEqTypes(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; uint8_t x_10; 
lean_inc(x_1);
x_9 = lean_apply_1(x_2, x_1);
x_10 = lean_unbox(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
x_12 = l_Lean_IR_instToFormatIRType___private__1(x_1);
x_13 = l_Std_Format_defWidth;
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Std_Format_pretty(x_12, x_13, x_14, x_14);
x_16 = lean_string_append(x_11, x_15);
lean_dec_ref(x_15);
x_17 = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
x_18 = lean_string_append(x_16, x_17);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_3, 0);
x_20 = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
x_21 = lean_string_append(x_18, x_20);
x_22 = lean_string_append(x_21, x_19);
x_23 = l_Lean_IR_Checker_throwCheckerError___redArg(x_22, x_4, x_5, x_6, x_7);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = l_Lean_IR_Checker_throwCheckerError___redArg(x_18, x_4, x_5, x_6, x_7);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_1);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_IR_Checker_checkType(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_IR_IRType_isObj(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_8 = ((lean_object*)(l_Lean_IR_Checker_checkObjType___closed__0));
x_9 = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
x_10 = l_Lean_IR_instToFormatIRType___private__1(x_1);
x_11 = l_Std_Format_defWidth;
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Std_Format_pretty(x_10, x_11, x_12, x_12);
x_14 = lean_string_append(x_9, x_13);
lean_dec_ref(x_13);
x_15 = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
x_16 = lean_string_append(x_14, x_15);
x_17 = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_8);
x_20 = l_Lean_IR_Checker_throwCheckerError___redArg(x_19, x_2, x_3, x_4, x_5);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_checkObjType(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_IR_IRType_isScalar(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_8 = ((lean_object*)(l_Lean_IR_Checker_checkScalarType___closed__0));
x_9 = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
x_10 = l_Lean_IR_instToFormatIRType___private__1(x_1);
x_11 = l_Std_Format_defWidth;
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Std_Format_pretty(x_10, x_11, x_12, x_12);
x_14 = lean_string_append(x_9, x_13);
lean_dec_ref(x_13);
x_15 = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
x_16 = lean_string_append(x_14, x_15);
x_17 = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_8);
x_20 = l_Lean_IR_Checker_throwCheckerError___redArg(x_19, x_2, x_3, x_4, x_5);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_checkScalarType(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = l_Lean_IR_LocalContext_getType(x_7, x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__0));
x_10 = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__1));
x_11 = l_Nat_reprFast(x_1);
x_12 = lean_string_append(x_10, x_11);
lean_dec_ref(x_11);
x_13 = lean_string_append(x_9, x_12);
lean_dec_ref(x_12);
x_14 = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
x_15 = lean_string_append(x_13, x_14);
x_16 = l_Lean_IR_Checker_throwCheckerError___redArg(x_15, x_2, x_3, x_4, x_5);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_24; 
lean_dec(x_1);
x_17 = lean_ctor_get(x_8, 0);
x_24 = !lean_is_exclusive(x_8);
if (x_24 == 0)
{
x_18 = x_8;
x_19 = x_24;
goto block_23;
}
else
{
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_box(0);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; 
if (x_19 == 0)
{
lean_ctor_set_tag(x_18, 0);
x_20 = x_18;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_17);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_getType(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_IR_Checker_getType(x_1, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_34; 
x_10 = lean_ctor_get(x_9, 0);
x_34 = !lean_is_exclusive(x_9);
if (x_34 == 0)
{
x_11 = x_9;
x_12 = x_34;
goto block_33;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_13; uint8_t x_14; 
lean_inc(x_10);
x_13 = lean_apply_1(x_2, x_10);
x_14 = lean_unbox(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_del_object(x_11);
x_15 = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
x_16 = l_Lean_IR_instToFormatIRType___private__1(x_10);
x_17 = l_Std_Format_defWidth;
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Std_Format_pretty(x_16, x_17, x_18, x_18);
x_20 = lean_string_append(x_15, x_19);
lean_dec_ref(x_19);
x_21 = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
x_22 = lean_string_append(x_20, x_21);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_3, 0);
x_24 = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
x_25 = lean_string_append(x_22, x_24);
x_26 = lean_string_append(x_25, x_23);
x_27 = l_Lean_IR_Checker_throwCheckerError___redArg(x_26, x_4, x_5, x_6, x_7);
return x_27;
}
else
{
lean_object* x_28; 
x_28 = l_Lean_IR_Checker_throwCheckerError___redArg(x_22, x_4, x_5, x_6, x_7);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_10);
x_29 = lean_box(0);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_29);
x_30 = x_11;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_29);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_42; 
lean_dec_ref(x_2);
x_35 = lean_ctor_get(x_9, 0);
x_42 = !lean_is_exclusive(x_9);
if (x_42 == 0)
{
x_36 = x_9;
x_37 = x_42;
goto block_41;
}
else
{
lean_inc(x_35);
lean_dec(x_9);
x_36 = lean_box(0);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_37 == 0)
{
x_38 = x_36;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_35);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_IR_Checker_checkVarType(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_getType(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_30; 
x_8 = lean_ctor_get(x_7, 0);
x_30 = !lean_is_exclusive(x_7);
if (x_30 == 0)
{
x_9 = x_7;
x_10 = x_30;
goto block_29;
}
else
{
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = x_30;
goto block_29;
}
block_29:
{
uint8_t x_11; 
x_11 = l_Lean_IR_IRType_isObj(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_del_object(x_9);
x_12 = ((lean_object*)(l_Lean_IR_Checker_checkObjType___closed__0));
x_13 = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
x_14 = l_Lean_IR_instToFormatIRType___private__1(x_8);
x_15 = l_Std_Format_defWidth;
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Std_Format_pretty(x_14, x_15, x_16, x_16);
x_18 = lean_string_append(x_13, x_17);
lean_dec_ref(x_17);
x_19 = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
x_20 = lean_string_append(x_18, x_19);
x_21 = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_string_append(x_22, x_12);
x_24 = l_Lean_IR_Checker_throwCheckerError___redArg(x_23, x_2, x_3, x_4, x_5);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_8);
x_25 = lean_box(0);
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_25);
x_26 = x_9;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_38; 
x_31 = lean_ctor_get(x_7, 0);
x_38 = !lean_is_exclusive(x_7);
if (x_38 == 0)
{
x_32 = x_7;
x_33 = x_38;
goto block_37;
}
else
{
lean_inc(x_31);
lean_dec(x_7);
x_32 = lean_box(0);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_33 == 0)
{
x_34 = x_32;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_31);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_checkObjVar(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_getType(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_30; 
x_8 = lean_ctor_get(x_7, 0);
x_30 = !lean_is_exclusive(x_7);
if (x_30 == 0)
{
x_9 = x_7;
x_10 = x_30;
goto block_29;
}
else
{
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = x_30;
goto block_29;
}
block_29:
{
uint8_t x_11; 
x_11 = l_Lean_IR_IRType_isScalar(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_del_object(x_9);
x_12 = ((lean_object*)(l_Lean_IR_Checker_checkScalarType___closed__0));
x_13 = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
x_14 = l_Lean_IR_instToFormatIRType___private__1(x_8);
x_15 = l_Std_Format_defWidth;
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Std_Format_pretty(x_14, x_15, x_16, x_16);
x_18 = lean_string_append(x_13, x_17);
lean_dec_ref(x_17);
x_19 = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
x_20 = lean_string_append(x_18, x_19);
x_21 = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_string_append(x_22, x_12);
x_24 = l_Lean_IR_Checker_throwCheckerError___redArg(x_23, x_2, x_3, x_4, x_5);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_8);
x_25 = lean_box(0);
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_25);
x_26 = x_9;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_38; 
x_31 = lean_ctor_get(x_7, 0);
x_38 = !lean_is_exclusive(x_7);
if (x_38 == 0)
{
x_32 = x_7;
x_33 = x_38;
goto block_37;
}
else
{
lean_inc(x_31);
lean_dec(x_7);
x_32 = lean_box(0);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_33 == 0)
{
x_34 = x_32;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_31);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_checkScalarVar(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_IR_Checker_getDecl(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_array_get_size(x_2);
x_11 = l_Lean_IR_Decl_params(x_9);
lean_dec(x_9);
x_12 = lean_array_get_size(x_11);
lean_dec_ref(x_11);
x_13 = lean_nat_dec_eq(x_10, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_14 = ((lean_object*)(l_Lean_IR_Checker_checkFullApp___closed__0));
x_15 = 1;
x_16 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_1, x_15);
x_17 = lean_string_append(x_14, x_16);
lean_dec_ref(x_16);
x_18 = ((lean_object*)(l_Lean_IR_Checker_checkFullApp___closed__1));
x_19 = lean_string_append(x_17, x_18);
x_20 = l_Nat_reprFast(x_10);
x_21 = lean_string_append(x_19, x_20);
lean_dec_ref(x_20);
x_22 = ((lean_object*)(l_Lean_IR_Checker_checkFullApp___closed__2));
x_23 = lean_string_append(x_21, x_22);
x_24 = l_Nat_reprFast(x_12);
x_25 = lean_string_append(x_23, x_24);
lean_dec_ref(x_24);
x_26 = ((lean_object*)(l_Lean_IR_Checker_checkFullApp___closed__3));
x_27 = lean_string_append(x_25, x_26);
x_28 = l_Lean_IR_Checker_throwCheckerError___redArg(x_27, x_3, x_4, x_5, x_6);
return x_28;
}
else
{
lean_object* x_29; 
lean_dec(x_1);
x_29 = l_Lean_IR_Checker_checkArgs(x_2, x_3, x_4, x_5, x_6);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_37; 
lean_dec(x_1);
x_30 = lean_ctor_get(x_8, 0);
x_37 = !lean_is_exclusive(x_8);
if (x_37 == 0)
{
x_31 = x_8;
x_32 = x_37;
goto block_36;
}
else
{
lean_inc(x_30);
lean_dec(x_8);
x_31 = lean_box(0);
x_32 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_33; 
if (x_32 == 0)
{
x_33 = x_31;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_30);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_Checker_checkFullApp(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_IR_Checker_getDecl(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_array_get_size(x_2);
x_11 = l_Lean_IR_Decl_params(x_9);
lean_dec(x_9);
x_12 = lean_array_get_size(x_11);
lean_dec_ref(x_11);
x_13 = lean_nat_dec_lt(x_10, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_14 = ((lean_object*)(l_Lean_IR_Checker_checkPartialApp___closed__0));
x_15 = 1;
x_16 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_1, x_15);
x_17 = lean_string_append(x_14, x_16);
lean_dec_ref(x_16);
x_18 = ((lean_object*)(l_Lean_IR_Checker_checkPartialApp___closed__1));
x_19 = lean_string_append(x_17, x_18);
x_20 = l_Nat_reprFast(x_10);
x_21 = lean_string_append(x_19, x_20);
lean_dec_ref(x_20);
x_22 = ((lean_object*)(l_Lean_IR_Checker_checkPartialApp___closed__2));
x_23 = lean_string_append(x_21, x_22);
x_24 = l_Nat_reprFast(x_12);
x_25 = lean_string_append(x_23, x_24);
lean_dec_ref(x_24);
x_26 = l_Lean_IR_Checker_throwCheckerError___redArg(x_25, x_3, x_4, x_5, x_6);
return x_26;
}
else
{
lean_object* x_27; 
lean_dec(x_1);
x_27 = l_Lean_IR_Checker_checkArgs(x_2, x_3, x_4, x_5, x_6);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_35; 
lean_dec(x_1);
x_28 = lean_ctor_get(x_8, 0);
x_35 = !lean_is_exclusive(x_8);
if (x_35 == 0)
{
x_29 = x_8;
x_30 = x_35;
goto block_34;
}
else
{
lean_inc(x_28);
lean_dec(x_8);
x_29 = lean_box(0);
x_30 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_31; 
if (x_30 == 0)
{
x_31 = x_29;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_28);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_Checker_checkPartialApp(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_54; lean_object* x_62; uint8_t x_63; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_9);
lean_dec_ref(x_2);
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
x_22 = lean_ctor_get(x_8, 2);
x_23 = lean_ctor_get(x_8, 3);
x_24 = lean_ctor_get(x_8, 4);
x_62 = l_Lean_IR_Checker_maxCtorTag;
x_63 = lean_nat_dec_lt(x_62, x_21);
if (x_63 == 0)
{
x_54 = x_63;
goto block_61;
}
else
{
uint8_t x_64; 
x_64 = l_Lean_IR_CtorInfo_isRef(x_8);
x_54 = x_64;
goto block_61;
}
block_19:
{
uint8_t x_14; 
x_14 = l_Lean_IR_CtorInfo_isRef(x_8);
lean_dec_ref(x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec_ref(x_9);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = l_Lean_IR_Checker_checkObjType(x_1, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec_ref(x_17);
x_18 = l_Lean_IR_Checker_checkArgs(x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_9);
return x_18;
}
else
{
lean_dec_ref(x_9);
return x_17;
}
}
}
block_40:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = l_Lean_IR_Checker_maxCtorScalarsSize;
x_30 = l_Lean_IR_Checker_usizeSize;
x_31 = lean_nat_mul(x_23, x_30);
x_32 = lean_nat_add(x_24, x_31);
lean_dec(x_31);
x_33 = lean_nat_dec_lt(x_29, x_32);
lean_dec(x_32);
if (x_33 == 0)
{
x_10 = x_25;
x_11 = x_26;
x_12 = x_27;
x_13 = x_28;
goto block_19;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_inc(x_20);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_1);
x_34 = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__0));
x_35 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_20, x_33);
x_36 = lean_string_append(x_34, x_35);
lean_dec_ref(x_35);
x_37 = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__1));
x_38 = lean_string_append(x_36, x_37);
x_39 = l_Lean_IR_Checker_throwCheckerError___redArg(x_38, x_25, x_26, x_27, x_28);
return x_39;
}
}
block_53:
{
lean_object* x_45; uint8_t x_46; 
x_45 = l_Lean_IR_Checker_maxCtorFields;
x_46 = lean_nat_dec_lt(x_45, x_22);
if (x_46 == 0)
{
x_25 = x_41;
x_26 = x_42;
x_27 = x_43;
x_28 = x_44;
goto block_40;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_inc(x_20);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_1);
x_47 = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__0));
x_48 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_20, x_46);
x_49 = lean_string_append(x_47, x_48);
lean_dec_ref(x_48);
x_50 = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__2));
x_51 = lean_string_append(x_49, x_50);
x_52 = l_Lean_IR_Checker_throwCheckerError___redArg(x_51, x_41, x_42, x_43, x_44);
return x_52;
}
}
block_61:
{
if (x_54 == 0)
{
x_41 = x_3;
x_42 = x_4;
x_43 = x_5;
x_44 = x_6;
goto block_53;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_inc(x_20);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_1);
x_55 = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__3));
x_56 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_20, x_54);
x_57 = lean_string_append(x_55, x_56);
lean_dec_ref(x_56);
x_58 = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__4));
x_59 = lean_string_append(x_57, x_58);
x_60 = l_Lean_IR_Checker_throwCheckerError___redArg(x_59, x_3, x_4, x_5, x_6);
return x_60;
}
}
}
case 1:
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_2, 1);
lean_inc(x_65);
lean_dec_ref(x_2);
x_66 = l_Lean_IR_Checker_checkObjVar(x_65, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; 
lean_dec_ref(x_66);
x_67 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4, x_5, x_6);
return x_67;
}
else
{
lean_dec(x_1);
return x_66;
}
}
case 2:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_2, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_69);
lean_dec_ref(x_2);
x_70 = l_Lean_IR_Checker_checkObjVar(x_68, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; 
lean_dec_ref(x_70);
x_71 = l_Lean_IR_Checker_checkArgs(x_69, x_3, x_4, x_5, x_6);
lean_dec_ref(x_69);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; 
lean_dec_ref(x_71);
x_72 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4, x_5, x_6);
return x_72;
}
else
{
lean_dec(x_1);
return x_71;
}
}
else
{
lean_dec_ref(x_69);
lean_dec(x_1);
return x_70;
}
}
case 3:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_2, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_2, 1);
lean_inc(x_74);
lean_dec_ref(x_2);
x_75 = l_Lean_IR_Checker_getType(x_74, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_121; 
x_76 = lean_ctor_get(x_75, 0);
x_121 = !lean_is_exclusive(x_75);
if (x_121 == 0)
{
x_77 = x_75;
x_78 = x_121;
goto block_120;
}
else
{
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_box(0);
x_78 = x_121;
goto block_120;
}
block_120:
{
switch (lean_obj_tag(x_76)) {
case 7:
{
lean_object* x_79; 
lean_del_object(x_77);
lean_dec(x_73);
x_79 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4, x_5, x_6);
return x_79;
}
case 8:
{
lean_object* x_80; 
lean_del_object(x_77);
lean_dec(x_73);
x_80 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4, x_5, x_6);
return x_80;
}
case 10:
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_81 = lean_ctor_get(x_76, 1);
lean_inc_ref(x_81);
lean_dec_ref(x_76);
x_82 = lean_array_get_size(x_81);
x_83 = lean_nat_dec_lt(x_73, x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
lean_dec_ref(x_81);
lean_del_object(x_77);
lean_dec(x_73);
lean_dec(x_1);
x_84 = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__5));
x_85 = l_Lean_IR_Checker_throwCheckerError___redArg(x_84, x_3, x_4, x_5, x_6);
return x_85;
}
else
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_array_fget(x_81, x_73);
lean_dec(x_73);
lean_dec_ref(x_81);
x_87 = l_Lean_IR_instBEqIRType_beq(x_86, x_1);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
lean_del_object(x_77);
x_88 = ((lean_object*)(l_Lean_IR_Checker_checkEqTypes___closed__0));
x_89 = l_Lean_IR_Checker_throwCheckerError___redArg(x_88, x_3, x_4, x_5, x_6);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_box(0);
if (x_78 == 0)
{
lean_ctor_set(x_77, 0, x_90);
x_91 = x_77;
goto block_92;
}
else
{
lean_object* x_93; 
x_93 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_93, 0, x_90);
x_91 = x_93;
goto block_92;
}
block_92:
{
return x_91;
}
}
}
}
case 11:
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_94 = lean_ctor_get(x_76, 1);
lean_inc_ref(x_94);
lean_dec_ref(x_76);
x_95 = lean_array_get_size(x_94);
x_96 = lean_nat_dec_lt(x_73, x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
lean_dec_ref(x_94);
lean_del_object(x_77);
lean_dec(x_73);
lean_dec(x_1);
x_97 = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__5));
x_98 = l_Lean_IR_Checker_throwCheckerError___redArg(x_97, x_3, x_4, x_5, x_6);
return x_98;
}
else
{
lean_object* x_99; uint8_t x_100; 
x_99 = lean_array_fget(x_94, x_73);
lean_dec(x_73);
lean_dec_ref(x_94);
x_100 = l_Lean_IR_instBEqIRType_beq(x_99, x_1);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
lean_del_object(x_77);
x_101 = ((lean_object*)(l_Lean_IR_Checker_checkEqTypes___closed__0));
x_102 = l_Lean_IR_Checker_throwCheckerError___redArg(x_101, x_3, x_4, x_5, x_6);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_box(0);
if (x_78 == 0)
{
lean_ctor_set(x_77, 0, x_103);
x_104 = x_77;
goto block_105;
}
else
{
lean_object* x_106; 
x_106 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_106, 0, x_103);
x_104 = x_106;
goto block_105;
}
block_105:
{
return x_104;
}
}
}
}
case 12:
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_73);
lean_dec(x_1);
x_107 = lean_box(0);
if (x_78 == 0)
{
lean_ctor_set(x_77, 0, x_107);
x_108 = x_77;
goto block_109;
}
else
{
lean_object* x_110; 
x_110 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_110, 0, x_107);
x_108 = x_110;
goto block_109;
}
block_109:
{
return x_108;
}
}
default: 
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_del_object(x_77);
lean_dec(x_73);
lean_dec(x_1);
x_111 = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__6));
x_112 = l_Lean_IR_instToFormatIRType___private__1(x_76);
x_113 = l_Std_Format_defWidth;
x_114 = lean_unsigned_to_nat(0u);
x_115 = l_Std_Format_pretty(x_112, x_113, x_114, x_114);
x_116 = lean_string_append(x_111, x_115);
lean_dec_ref(x_115);
x_117 = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
x_118 = lean_string_append(x_116, x_117);
x_119 = l_Lean_IR_Checker_throwCheckerError___redArg(x_118, x_3, x_4, x_5, x_6);
return x_119;
}
}
}
}
else
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; uint8_t x_129; 
lean_dec(x_73);
lean_dec(x_1);
x_122 = lean_ctor_get(x_75, 0);
x_129 = !lean_is_exclusive(x_75);
if (x_129 == 0)
{
x_123 = x_75;
x_124 = x_129;
goto block_128;
}
else
{
lean_inc(x_122);
lean_dec(x_75);
x_123 = lean_box(0);
x_124 = x_129;
goto block_128;
}
block_128:
{
lean_object* x_125; 
if (x_124 == 0)
{
x_125 = x_123;
goto block_126;
}
else
{
lean_object* x_127; 
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_122);
x_125 = x_127;
goto block_126;
}
block_126:
{
return x_125;
}
}
}
}
case 4:
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_2, 1);
lean_inc(x_130);
lean_dec_ref(x_2);
x_131 = l_Lean_IR_Checker_checkObjVar(x_130, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; uint8_t x_133; uint8_t x_150; 
x_150 = !lean_is_exclusive(x_131);
if (x_150 == 0)
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_131, 0);
lean_dec(x_151);
x_132 = x_131;
x_133 = x_150;
goto block_149;
}
else
{
lean_dec(x_131);
x_132 = lean_box(0);
x_133 = x_150;
goto block_149;
}
block_149:
{
lean_object* x_134; uint8_t x_135; 
x_134 = lean_box(5);
lean_inc(x_1);
x_135 = l_Lean_IR_instBEqIRType_beq(x_1, x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_del_object(x_132);
x_136 = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
x_137 = l_Lean_IR_instToFormatIRType___private__1(x_1);
x_138 = l_Std_Format_defWidth;
x_139 = lean_unsigned_to_nat(0u);
x_140 = l_Std_Format_pretty(x_137, x_138, x_139, x_139);
x_141 = lean_string_append(x_136, x_140);
lean_dec_ref(x_140);
x_142 = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
x_143 = lean_string_append(x_141, x_142);
x_144 = l_Lean_IR_Checker_throwCheckerError___redArg(x_143, x_3, x_4, x_5, x_6);
return x_144;
}
else
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_1);
x_145 = lean_box(0);
if (x_133 == 0)
{
lean_ctor_set(x_132, 0, x_145);
x_146 = x_132;
goto block_147;
}
else
{
lean_object* x_148; 
x_148 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_148, 0, x_145);
x_146 = x_148;
goto block_147;
}
block_147:
{
return x_146;
}
}
}
}
else
{
lean_dec(x_1);
return x_131;
}
}
case 5:
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_2, 2);
lean_inc(x_152);
lean_dec_ref(x_2);
x_153 = l_Lean_IR_Checker_checkObjVar(x_152, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; 
lean_dec_ref(x_153);
x_154 = l_Lean_IR_Checker_checkScalarType(x_1, x_3, x_4, x_5, x_6);
return x_154;
}
else
{
lean_dec(x_1);
return x_153;
}
}
case 6:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_1);
x_155 = lean_ctor_get(x_2, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_156);
lean_dec_ref(x_2);
x_157 = l_Lean_IR_Checker_checkFullApp(x_155, x_156, x_3, x_4, x_5, x_6);
lean_dec_ref(x_156);
return x_157;
}
case 7:
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_2, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_159);
lean_dec_ref(x_2);
x_160 = l_Lean_IR_Checker_checkPartialApp(x_158, x_159, x_3, x_4, x_5, x_6);
lean_dec_ref(x_159);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; 
lean_dec_ref(x_160);
x_161 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4, x_5, x_6);
return x_161;
}
else
{
lean_dec(x_1);
return x_160;
}
}
case 8:
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_2, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_163);
lean_dec_ref(x_2);
x_164 = l_Lean_IR_Checker_checkObjVar(x_162, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; 
lean_dec_ref(x_164);
x_165 = l_Lean_IR_Checker_checkArgs(x_163, x_3, x_4, x_5, x_6);
lean_dec_ref(x_163);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; 
lean_dec_ref(x_165);
x_166 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4, x_5, x_6);
return x_166;
}
else
{
lean_dec(x_1);
return x_165;
}
}
else
{
lean_dec_ref(x_163);
lean_dec(x_1);
return x_164;
}
}
case 9:
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_2, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_2, 1);
lean_inc(x_168);
lean_dec_ref(x_2);
x_169 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; 
lean_dec_ref(x_169);
lean_inc(x_168);
x_170 = l_Lean_IR_Checker_checkScalarVar(x_168, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; 
lean_dec_ref(x_170);
x_171 = l_Lean_IR_Checker_getType(x_168, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; uint8_t x_174; uint8_t x_190; 
x_172 = lean_ctor_get(x_171, 0);
x_190 = !lean_is_exclusive(x_171);
if (x_190 == 0)
{
x_173 = x_171;
x_174 = x_190;
goto block_189;
}
else
{
lean_inc(x_172);
lean_dec(x_171);
x_173 = lean_box(0);
x_174 = x_190;
goto block_189;
}
block_189:
{
uint8_t x_175; 
lean_inc(x_172);
x_175 = l_Lean_IR_instBEqIRType_beq(x_172, x_167);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_del_object(x_173);
x_176 = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
x_177 = l_Lean_IR_instToFormatIRType___private__1(x_172);
x_178 = l_Std_Format_defWidth;
x_179 = lean_unsigned_to_nat(0u);
x_180 = l_Std_Format_pretty(x_177, x_178, x_179, x_179);
x_181 = lean_string_append(x_176, x_180);
lean_dec_ref(x_180);
x_182 = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
x_183 = lean_string_append(x_181, x_182);
x_184 = l_Lean_IR_Checker_throwCheckerError___redArg(x_183, x_3, x_4, x_5, x_6);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; 
lean_dec(x_172);
x_185 = lean_box(0);
if (x_174 == 0)
{
lean_ctor_set(x_173, 0, x_185);
x_186 = x_173;
goto block_187;
}
else
{
lean_object* x_188; 
x_188 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_188, 0, x_185);
x_186 = x_188;
goto block_187;
}
block_187:
{
return x_186;
}
}
}
}
else
{
lean_object* x_191; lean_object* x_192; uint8_t x_193; uint8_t x_198; 
lean_dec(x_167);
x_191 = lean_ctor_get(x_171, 0);
x_198 = !lean_is_exclusive(x_171);
if (x_198 == 0)
{
x_192 = x_171;
x_193 = x_198;
goto block_197;
}
else
{
lean_inc(x_191);
lean_dec(x_171);
x_192 = lean_box(0);
x_193 = x_198;
goto block_197;
}
block_197:
{
lean_object* x_194; 
if (x_193 == 0)
{
x_194 = x_192;
goto block_195;
}
else
{
lean_object* x_196; 
x_196 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_196, 0, x_191);
x_194 = x_196;
goto block_195;
}
block_195:
{
return x_194;
}
}
}
}
else
{
lean_dec(x_168);
lean_dec(x_167);
return x_170;
}
}
else
{
lean_dec(x_168);
lean_dec(x_167);
return x_169;
}
}
case 10:
{
lean_object* x_199; lean_object* x_200; 
x_199 = lean_ctor_get(x_2, 0);
lean_inc(x_199);
lean_dec_ref(x_2);
x_200 = l_Lean_IR_Checker_checkScalarType(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; 
lean_dec_ref(x_200);
x_201 = l_Lean_IR_Checker_checkObjVar(x_199, x_3, x_4, x_5, x_6);
return x_201;
}
else
{
lean_dec(x_199);
return x_200;
}
}
case 11:
{
lean_object* x_202; lean_object* x_203; uint8_t x_204; uint8_t x_211; 
x_202 = lean_ctor_get(x_2, 0);
x_211 = !lean_is_exclusive(x_2);
if (x_211 == 0)
{
x_203 = x_2;
x_204 = x_211;
goto block_210;
}
else
{
lean_inc(x_202);
lean_dec(x_2);
x_203 = lean_box(0);
x_204 = x_211;
goto block_210;
}
block_210:
{
if (lean_obj_tag(x_202) == 1)
{
lean_object* x_205; 
lean_dec_ref(x_202);
lean_del_object(x_203);
x_205 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4, x_5, x_6);
return x_205;
}
else
{
lean_object* x_206; lean_object* x_207; 
lean_dec_ref(x_202);
lean_dec(x_1);
x_206 = lean_box(0);
if (x_204 == 0)
{
lean_ctor_set_tag(x_203, 0);
lean_ctor_set(x_203, 0, x_206);
x_207 = x_203;
goto block_208;
}
else
{
lean_object* x_209; 
x_209 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_209, 0, x_206);
x_207 = x_209;
goto block_208;
}
block_208:
{
return x_207;
}
}
}
}
default: 
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_ctor_get(x_2, 0);
lean_inc(x_212);
lean_dec_ref(x_2);
x_213 = l_Lean_IR_Checker_checkObjVar(x_212, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; uint8_t x_215; uint8_t x_232; 
x_232 = !lean_is_exclusive(x_213);
if (x_232 == 0)
{
lean_object* x_233; 
x_233 = lean_ctor_get(x_213, 0);
lean_dec(x_233);
x_214 = x_213;
x_215 = x_232;
goto block_231;
}
else
{
lean_dec(x_213);
x_214 = lean_box(0);
x_215 = x_232;
goto block_231;
}
block_231:
{
lean_object* x_216; uint8_t x_217; 
x_216 = lean_box(1);
lean_inc(x_1);
x_217 = l_Lean_IR_instBEqIRType_beq(x_1, x_216);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_del_object(x_214);
x_218 = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
x_219 = l_Lean_IR_instToFormatIRType___private__1(x_1);
x_220 = l_Std_Format_defWidth;
x_221 = lean_unsigned_to_nat(0u);
x_222 = l_Std_Format_pretty(x_219, x_220, x_221, x_221);
x_223 = lean_string_append(x_218, x_222);
lean_dec_ref(x_222);
x_224 = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
x_225 = lean_string_append(x_223, x_224);
x_226 = l_Lean_IR_Checker_throwCheckerError___redArg(x_225, x_3, x_4, x_5, x_6);
return x_226;
}
else
{
lean_object* x_227; lean_object* x_228; 
lean_dec(x_1);
x_227 = lean_box(0);
if (x_215 == 0)
{
lean_ctor_set(x_214, 0, x_227);
x_228 = x_214;
goto block_229;
}
else
{
lean_object* x_230; 
x_230 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_230, 0, x_227);
x_228 = x_230;
goto block_229;
}
block_229:
{
return x_228;
}
}
}
}
else
{
lean_dec(x_1);
return x_213;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_Checker_checkExpr(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = l_Lean_IR_Checker_markIndex(x_8, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; uint8_t x_17; 
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_9, 0);
lean_dec(x_18);
x_10 = x_9;
x_11 = x_17;
goto block_16;
}
else
{
lean_dec(x_9);
x_10 = lean_box(0);
x_11 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_IR_LocalContext_addParam(x_1, x_2);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_12);
x_13 = x_10;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_19 = lean_ctor_get(x_9, 0);
x_26 = !lean_is_exclusive(x_9);
if (x_26 == 0)
{
x_20 = x_9;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_dec(x_9);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_Checker_withParams___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_IR_Checker_withParams___closed__0, &l_Lean_IR_Checker_withParams___closed__0_once, _init_l_Lean_IR_Checker_withParams___closed__0);
x_2 = l_ReaderT_instMonad___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_69; 
x_8 = lean_obj_once(&l_Lean_IR_Checker_withParams___closed__1, &l_Lean_IR_Checker_withParams___closed__1_once, _init_l_Lean_IR_Checker_withParams___closed__1);
x_9 = lean_ctor_get(x_8, 0);
x_69 = !lean_is_exclusive(x_8);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_8, 1);
lean_dec(x_70);
x_10 = x_8;
x_11 = x_69;
goto block_68;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_66; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 2);
x_14 = lean_ctor_get(x_9, 3);
x_15 = lean_ctor_get(x_9, 4);
x_66 = !lean_is_exclusive(x_9);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_9, 1);
lean_dec(x_67);
x_16 = x_9;
x_17 = x_66;
goto block_65;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_9);
x_16 = lean_box(0);
x_17 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = ((lean_object*)(l_Lean_IR_Checker_withParams___closed__2));
x_19 = ((lean_object*)(l_Lean_IR_Checker_withParams___closed__3));
lean_inc_ref(x_12);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_20, 0, x_12);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_21, 0, x_12);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_15);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_24, 0, x_14);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_25, 0, x_13);
if (x_17 == 0)
{
lean_ctor_set(x_16, 4, x_23);
lean_ctor_set(x_16, 3, x_24);
lean_ctor_set(x_16, 2, x_25);
lean_ctor_set(x_16, 1, x_18);
lean_ctor_set(x_16, 0, x_22);
x_26 = x_16;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_64, 0, x_22);
lean_ctor_set(x_64, 1, x_18);
lean_ctor_set(x_64, 2, x_25);
lean_ctor_set(x_64, 3, x_24);
lean_ctor_set(x_64, 4, x_23);
x_26 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_27; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_19);
lean_ctor_set(x_10, 0, x_26);
x_27 = x_10;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_26);
lean_ctor_set(x_62, 1, x_19);
x_27 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_37; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_28 = l_ReaderT_instMonad___redArg(x_27);
x_29 = l_ReaderT_instMonad___redArg(x_28);
x_30 = lean_ctor_get(x_3, 0);
x_31 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_31);
x_32 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_32);
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_array_get_size(x_1);
x_50 = lean_nat_dec_lt(x_48, x_49);
if (x_50 == 0)
{
lean_inc(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_33 = x_30;
goto block_36;
}
else
{
lean_object* x_51; uint8_t x_52; 
x_51 = ((lean_object*)(l_Lean_IR_Checker_withParams___closed__4));
x_52 = lean_nat_dec_le(x_49, x_49);
if (x_52 == 0)
{
if (x_50 == 0)
{
lean_inc(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_33 = x_30;
goto block_36;
}
else
{
size_t x_53; size_t x_54; lean_object* x_55; lean_object* x_56; 
x_53 = 0;
x_54 = lean_usize_of_nat(x_49);
lean_inc(x_30);
x_55 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_29, x_51, x_1, x_53, x_54, x_30);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_56 = lean_apply_5(x_55, x_3, x_4, x_5, x_6, lean_box(0));
x_37 = x_56;
goto block_47;
}
}
else
{
size_t x_57; size_t x_58; lean_object* x_59; lean_object* x_60; 
x_57 = 0;
x_58 = lean_usize_of_nat(x_49);
lean_inc(x_30);
x_59 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_29, x_51, x_1, x_57, x_58, x_30);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_60 = lean_apply_5(x_59, x_3, x_4, x_5, x_6, lean_box(0));
x_37 = x_60;
goto block_47;
}
}
block_36:
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
lean_ctor_set(x_34, 2, x_32);
x_35 = lean_apply_5(x_2, x_34, x_4, x_5, x_6, lean_box(0));
return x_35;
}
block_47:
{
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_33 = x_38;
goto block_36;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_46; 
lean_dec_ref(x_32);
lean_dec_ref(x_31);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_39 = lean_ctor_get(x_37, 0);
x_46 = !lean_is_exclusive(x_37);
if (x_46 == 0)
{
x_40 = x_37;
x_41 = x_46;
goto block_45;
}
else
{
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_box(0);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_41 == 0)
{
x_42 = x_40;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_39);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_Checker_withParams(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_array_uget_borrowed(x_1, x_2);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = l_Lean_IR_Checker_markIndex(x_12, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; size_t x_15; size_t x_16; 
lean_dec_ref(x_13);
lean_inc(x_11);
x_14 = l_Lean_IR_LocalContext_addParam(x_4, x_11);
x_15 = 1;
x_16 = lean_usize_add(x_2, x_15);
x_2 = x_16;
x_4 = x_14;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_25; 
lean_dec(x_4);
x_18 = lean_ctor_get(x_13, 0);
x_25 = !lean_is_exclusive(x_13);
if (x_25 == 0)
{
x_19 = x_13;
x_20 = x_25;
goto block_24;
}
else
{
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_box(0);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_20 == 0)
{
x_21 = x_19;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_18);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_4);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFnBody(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_18);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
lean_dec_ref(x_1);
lean_inc_ref(x_18);
lean_inc(x_17);
x_20 = l_Lean_IR_Checker_checkExpr(x_17, x_18, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_dec_ref(x_20);
lean_inc(x_16);
x_21 = l_Lean_IR_Checker_markIndex(x_16, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_33; 
lean_dec_ref(x_21);
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
x_33 = !lean_is_exclusive(x_2);
if (x_33 == 0)
{
x_25 = x_2;
x_26 = x_33;
goto block_32;
}
else
{
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_25 = lean_box(0);
x_26 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Lean_IR_LocalContext_addLocal(x_22, x_16, x_17, x_18);
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_27);
x_28 = x_25;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_23);
lean_ctor_set(x_31, 2, x_24);
x_28 = x_31;
goto block_30;
}
block_30:
{
x_1 = x_19;
x_2 = x_28;
goto _start;
}
}
}
else
{
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec_ref(x_2);
return x_21;
}
}
else
{
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec_ref(x_2);
return x_20;
}
}
case 1:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_35);
x_36 = lean_ctor_get(x_1, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 3);
lean_inc(x_37);
lean_dec_ref(x_1);
lean_inc(x_34);
x_38 = l_Lean_IR_Checker_markIndex(x_34, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_49; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
lean_dec_ref(x_38);
x_39 = lean_ctor_get(x_2, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_40);
x_41 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_41);
x_60 = lean_unsigned_to_nat(0u);
x_61 = lean_array_get_size(x_35);
x_62 = lean_nat_dec_lt(x_60, x_61);
if (x_62 == 0)
{
lean_dec_ref(x_2);
lean_inc(x_39);
x_42 = x_39;
goto block_48;
}
else
{
uint8_t x_63; 
x_63 = lean_nat_dec_le(x_61, x_61);
if (x_63 == 0)
{
if (x_62 == 0)
{
lean_dec_ref(x_2);
lean_inc(x_39);
x_42 = x_39;
goto block_48;
}
else
{
size_t x_64; size_t x_65; lean_object* x_66; 
x_64 = 0;
x_65 = lean_usize_of_nat(x_61);
lean_inc(x_39);
x_66 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(x_35, x_64, x_65, x_39, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
x_49 = x_66;
goto block_59;
}
}
else
{
size_t x_67; size_t x_68; lean_object* x_69; 
x_67 = 0;
x_68 = lean_usize_of_nat(x_61);
lean_inc(x_39);
x_69 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(x_35, x_67, x_68, x_39, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
x_49 = x_69;
goto block_59;
}
}
block_48:
{
lean_object* x_43; lean_object* x_44; 
lean_inc_ref(x_41);
lean_inc_ref(x_40);
x_43 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
lean_ctor_set(x_43, 2, x_41);
lean_inc(x_36);
x_44 = l_Lean_IR_Checker_checkFnBody(x_36, x_43, x_3, x_4, x_5);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec_ref(x_44);
x_45 = l_Lean_IR_LocalContext_addJP(x_39, x_34, x_35, x_36);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_40);
lean_ctor_set(x_46, 2, x_41);
x_1 = x_37;
x_2 = x_46;
goto _start;
}
else
{
lean_dec_ref(x_41);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
return x_44;
}
}
block_59:
{
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
x_42 = x_50;
goto block_48;
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_58; 
lean_dec_ref(x_41);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
x_51 = lean_ctor_get(x_49, 0);
x_58 = !lean_is_exclusive(x_49);
if (x_58 == 0)
{
x_52 = x_49;
x_53 = x_58;
goto block_57;
}
else
{
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_box(0);
x_53 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_54; 
if (x_53 == 0)
{
x_54 = x_52;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_51);
x_54 = x_56;
goto block_55;
}
block_55:
{
return x_54;
}
}
}
}
}
else
{
lean_dec(x_37);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_2);
return x_38;
}
}
case 2:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_1, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_1, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_1, 3);
lean_inc(x_72);
lean_dec_ref(x_1);
x_73 = l_Lean_IR_Checker_checkVar(x_70, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; 
lean_dec_ref(x_73);
x_74 = l_Lean_IR_Checker_checkArg(x_71, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_74) == 0)
{
lean_dec_ref(x_74);
x_1 = x_72;
goto _start;
}
else
{
lean_dec(x_72);
lean_dec_ref(x_2);
return x_74;
}
}
else
{
lean_dec(x_72);
lean_dec(x_71);
lean_dec_ref(x_2);
return x_73;
}
}
case 3:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_1, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_1, 2);
lean_inc(x_77);
lean_dec_ref(x_1);
x_78 = l_Lean_IR_Checker_checkVar(x_76, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_78) == 0)
{
lean_dec_ref(x_78);
x_1 = x_77;
goto _start;
}
else
{
lean_dec(x_77);
lean_dec_ref(x_2);
return x_78;
}
}
case 4:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_1, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_1, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_1, 3);
lean_inc(x_82);
lean_dec_ref(x_1);
x_83 = l_Lean_IR_Checker_checkVar(x_80, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; 
lean_dec_ref(x_83);
x_84 = l_Lean_IR_Checker_checkVar(x_81, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_84) == 0)
{
lean_dec_ref(x_84);
x_1 = x_82;
goto _start;
}
else
{
lean_dec(x_82);
lean_dec_ref(x_2);
return x_84;
}
}
else
{
lean_dec(x_82);
lean_dec(x_81);
lean_dec_ref(x_2);
return x_83;
}
}
case 5:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_1, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_1, 3);
lean_inc(x_87);
x_88 = lean_ctor_get(x_1, 5);
lean_inc(x_88);
lean_dec_ref(x_1);
x_89 = l_Lean_IR_Checker_checkVar(x_86, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; 
lean_dec_ref(x_89);
x_90 = l_Lean_IR_Checker_checkVar(x_87, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_90) == 0)
{
lean_dec_ref(x_90);
x_1 = x_88;
goto _start;
}
else
{
lean_dec(x_88);
lean_dec_ref(x_2);
return x_90;
}
}
else
{
lean_dec(x_88);
lean_dec(x_87);
lean_dec_ref(x_2);
return x_89;
}
}
case 8:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_1, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_1, 1);
lean_inc(x_93);
lean_dec_ref(x_1);
x_94 = l_Lean_IR_Checker_checkVar(x_92, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_94) == 0)
{
lean_dec_ref(x_94);
x_1 = x_93;
goto _start;
}
else
{
lean_dec(x_93);
lean_dec_ref(x_2);
return x_94;
}
}
case 9:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_1, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_97);
lean_dec_ref(x_1);
x_98 = l_Lean_IR_Checker_checkVar(x_96, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; uint8_t x_100; uint8_t x_119; 
x_119 = !lean_is_exclusive(x_98);
if (x_119 == 0)
{
lean_object* x_120; 
x_120 = lean_ctor_get(x_98, 0);
lean_dec(x_120);
x_99 = x_98;
x_100 = x_119;
goto block_118;
}
else
{
lean_dec(x_98);
x_99 = lean_box(0);
x_100 = x_119;
goto block_118;
}
block_118:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_101 = lean_unsigned_to_nat(0u);
x_102 = lean_array_get_size(x_97);
x_103 = lean_box(0);
x_104 = lean_nat_dec_lt(x_101, x_102);
if (x_104 == 0)
{
lean_object* x_105; 
lean_dec_ref(x_97);
lean_dec_ref(x_2);
if (x_100 == 0)
{
lean_ctor_set(x_99, 0, x_103);
x_105 = x_99;
goto block_106;
}
else
{
lean_object* x_107; 
x_107 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_107, 0, x_103);
x_105 = x_107;
goto block_106;
}
block_106:
{
return x_105;
}
}
else
{
uint8_t x_108; 
x_108 = lean_nat_dec_le(x_102, x_102);
if (x_108 == 0)
{
if (x_104 == 0)
{
lean_object* x_109; 
lean_dec_ref(x_97);
lean_dec_ref(x_2);
if (x_100 == 0)
{
lean_ctor_set(x_99, 0, x_103);
x_109 = x_99;
goto block_110;
}
else
{
lean_object* x_111; 
x_111 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_111, 0, x_103);
x_109 = x_111;
goto block_110;
}
block_110:
{
return x_109;
}
}
else
{
size_t x_112; size_t x_113; lean_object* x_114; 
lean_del_object(x_99);
x_112 = 0;
x_113 = lean_usize_of_nat(x_102);
x_114 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(x_97, x_112, x_113, x_103, x_2, x_3, x_4, x_5);
lean_dec_ref(x_97);
return x_114;
}
}
else
{
size_t x_115; size_t x_116; lean_object* x_117; 
lean_del_object(x_99);
x_115 = 0;
x_116 = lean_usize_of_nat(x_102);
x_117 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(x_97, x_115, x_116, x_103, x_2, x_3, x_4, x_5);
lean_dec_ref(x_97);
return x_117;
}
}
}
}
else
{
lean_dec_ref(x_97);
lean_dec_ref(x_2);
return x_98;
}
}
case 10:
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_1, 0);
lean_inc(x_121);
lean_dec_ref(x_1);
x_122 = l_Lean_IR_Checker_checkArg(x_121, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
return x_122;
}
case 11:
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_1, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_124);
lean_dec_ref(x_1);
x_125 = l_Lean_IR_Checker_checkJP(x_123, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; 
lean_dec_ref(x_125);
x_126 = l_Lean_IR_Checker_checkArgs(x_124, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_124);
return x_126;
}
else
{
lean_dec_ref(x_124);
lean_dec_ref(x_2);
return x_125;
}
}
case 12:
{
lean_object* x_127; lean_object* x_128; 
lean_dec_ref(x_2);
x_127 = lean_box(0);
x_128 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_128, 0, x_127);
return x_128;
}
default: 
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_1, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_1, 2);
lean_inc(x_130);
lean_dec(x_1);
x_7 = x_129;
x_8 = x_130;
x_9 = x_2;
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
goto block_15;
}
}
block_15:
{
lean_object* x_13; 
x_13 = l_Lean_IR_Checker_checkVar(x_7, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_dec_ref(x_13);
x_1 = x_8;
x_2 = x_9;
x_3 = x_10;
x_4 = x_11;
x_5 = x_12;
goto _start;
}
else
{
lean_dec_ref(x_9);
lean_dec(x_8);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_array_uget_borrowed(x_1, x_2);
x_12 = l_Lean_IR_Alt_body(x_11);
lean_inc_ref(x_5);
x_13 = l_Lean_IR_Checker_checkFnBody(x_12, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; size_t x_15; size_t x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = 1;
x_16 = lean_usize_add(x_2, x_15);
x_2 = x_16;
x_4 = x_14;
goto _start;
}
else
{
lean_dec_ref(x_5);
return x_13;
}
}
else
{
lean_object* x_18; 
lean_dec_ref(x_5);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_4);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFnBody___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_checkFnBody(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_16; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_11);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_array_get_size(x_7);
x_29 = lean_nat_dec_lt(x_27, x_28);
if (x_29 == 0)
{
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_12 = x_9;
goto block_15;
}
else
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_28, x_28);
if (x_30 == 0)
{
if (x_29 == 0)
{
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_12 = x_9;
goto block_15;
}
else
{
size_t x_31; size_t x_32; lean_object* x_33; 
x_31 = 0;
x_32 = lean_usize_of_nat(x_28);
x_33 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(x_7, x_31, x_32, x_9, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_7);
x_16 = x_33;
goto block_26;
}
}
else
{
size_t x_34; size_t x_35; lean_object* x_36; 
x_34 = 0;
x_35 = lean_usize_of_nat(x_28);
x_36 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(x_7, x_34, x_35, x_9, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_7);
x_16 = x_36;
goto block_26;
}
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
x_14 = l_Lean_IR_Checker_checkFnBody(x_8, x_13, x_3, x_4, x_5);
return x_14;
}
block_26:
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_12 = x_17;
goto block_15;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_25; 
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_8);
x_18 = lean_ctor_get(x_16, 0);
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
x_19 = x_16;
x_20 = x_25;
goto block_24;
}
else
{
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_20 == 0)
{
x_21 = x_19;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_18);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_37 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_37);
lean_dec_ref(x_1);
x_38 = lean_box(0);
x_57 = lean_unsigned_to_nat(0u);
x_58 = lean_array_get_size(x_37);
x_59 = lean_nat_dec_lt(x_57, x_58);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec_ref(x_37);
lean_dec_ref(x_2);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_38);
return x_60;
}
else
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_2, 0);
lean_inc(x_61);
x_62 = lean_nat_dec_le(x_58, x_58);
if (x_62 == 0)
{
if (x_59 == 0)
{
lean_object* x_63; 
lean_dec(x_61);
lean_dec_ref(x_37);
lean_dec_ref(x_2);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_38);
return x_63;
}
else
{
size_t x_64; size_t x_65; lean_object* x_66; 
x_64 = 0;
x_65 = lean_usize_of_nat(x_58);
x_66 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(x_37, x_64, x_65, x_61, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_37);
x_39 = x_66;
goto block_56;
}
}
else
{
size_t x_67; size_t x_68; lean_object* x_69; 
x_67 = 0;
x_68 = lean_usize_of_nat(x_58);
x_69 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(x_37, x_67, x_68, x_61, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_37);
x_39 = x_69;
goto block_56;
}
}
block_56:
{
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; uint8_t x_46; 
x_46 = !lean_is_exclusive(x_39);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_39, 0);
lean_dec(x_47);
x_40 = x_39;
x_41 = x_46;
goto block_45;
}
else
{
lean_dec(x_39);
x_40 = lean_box(0);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_41 == 0)
{
lean_ctor_set(x_40, 0, x_38);
x_42 = x_40;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_38);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_55; 
x_48 = lean_ctor_get(x_39, 0);
x_55 = !lean_is_exclusive(x_39);
if (x_55 == 0)
{
x_49 = x_39;
x_50 = x_55;
goto block_54;
}
else
{
lean_inc(x_48);
lean_dec(x_39);
x_49 = lean_box(0);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
if (x_50 == 0)
{
x_51 = x_49;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_48);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_checkDecl(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_box(1);
x_7 = lean_st_mk_ref(x_6);
lean_inc_ref(x_2);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 2, x_1);
x_9 = l_Lean_IR_Checker_checkDecl(x_2, x_8, x_7, x_3, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_18; 
x_10 = lean_ctor_get(x_9, 0);
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
x_11 = x_9;
x_12 = x_18;
goto block_17;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_st_ref_get(x_7);
lean_dec(x_7);
lean_dec(x_13);
if (x_12 == 0)
{
x_14 = x_11;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_10);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
else
{
lean_dec(x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_checkDecl(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_3, x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget_borrowed(x_2, x_3);
lean_inc(x_10);
lean_inc_ref(x_1);
x_11 = l_Lean_IR_checkDecl(x_1, x_10, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; size_t x_13; size_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
x_5 = x_12;
goto _start;
}
else
{
lean_dec_ref(x_1);
return x_11;
}
}
else
{
lean_object* x_16; 
lean_dec_ref(x_1);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_5);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(x_1, x_2, x_9, x_10, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get_size(x_1);
x_7 = lean_box(0);
x_8 = lean_nat_dec_lt(x_5, x_6);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_1);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_6, x_6);
if (x_10 == 0)
{
if (x_8 == 0)
{
lean_object* x_11; 
lean_dec_ref(x_1);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_7);
return x_11;
}
else
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = 0;
x_13 = lean_usize_of_nat(x_6);
lean_inc_ref(x_1);
x_14 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(x_1, x_1, x_12, x_13, x_7, x_2, x_3);
lean_dec_ref(x_1);
return x_14;
}
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_6);
lean_inc_ref(x_1);
x_17 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(x_1, x_1, x_15, x_16, x_7, x_2, x_3);
lean_dec_ref(x_1);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_checkDecls(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
lean_object* runtime_initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_IR_Checker(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_IR_CompilerM(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_Checker_maxCtorFields = _init_l_Lean_IR_Checker_maxCtorFields();
lean_mark_persistent(l_Lean_IR_Checker_maxCtorFields);
l_Lean_IR_Checker_maxCtorScalarsSize = _init_l_Lean_IR_Checker_maxCtorScalarsSize();
lean_mark_persistent(l_Lean_IR_Checker_maxCtorScalarsSize);
l_Lean_IR_Checker_maxCtorTag = _init_l_Lean_IR_Checker_maxCtorTag();
lean_mark_persistent(l_Lean_IR_Checker_maxCtorTag);
l_Lean_IR_Checker_usizeSize = _init_l_Lean_IR_Checker_usizeSize();
lean_mark_persistent(l_Lean_IR_Checker_usizeSize);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_IR_Checker(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_Checker(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_IR_CompilerM(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_Checker(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_IR_Checker(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_IR_Checker(builtin);
}
#ifdef __cplusplus
}
#endif
