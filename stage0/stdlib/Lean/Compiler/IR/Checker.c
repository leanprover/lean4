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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_name(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_IR_LocalContext_isLocalVar(lean_object*, lean_object*);
uint8_t l_Lean_IR_LocalContext_isParam(lean_object*, lean_object*);
uint8_t l_Lean_IR_CtorInfo_isRef(lean_object*);
uint8_t l_Lean_IR_IRType_isObj(lean_object*);
lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_IR_LocalContext_getType(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_Lean_IR_instBEqIRType_beq(lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isScalar(lean_object*);
lean_object* l_Lean_IR_findEnvDecl_x27(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_params(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_IR_LocalContext_addLocal(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_addJP(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_addParam(lean_object*, lean_object*);
lean_object* l_Lean_IR_Alt_body(lean_object*);
uint8_t l_Lean_IR_LocalContext_isJP(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
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
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_Checker_throwCheckerError___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "failed to compile definition, compiler IR check failed at `"};
static const lean_object* l_Lean_IR_Checker_throwCheckerError___redArg___closed__0 = (const lean_object*)&l_Lean_IR_Checker_throwCheckerError___redArg___closed__0_value;
static lean_once_cell_t l_Lean_IR_Checker_throwCheckerError___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_Checker_throwCheckerError___redArg___closed__1;
static const lean_string_object l_Lean_IR_Checker_throwCheckerError___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "`. Error: "};
static const lean_object* l_Lean_IR_Checker_throwCheckerError___redArg___closed__2 = (const lean_object*)&l_Lean_IR_Checker_throwCheckerError___redArg___closed__2_value;
static lean_once_cell_t l_Lean_IR_Checker_throwCheckerError___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_Checker_throwCheckerError___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_Checker_markIndex___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "variable / join point index "};
static const lean_object* l_Lean_IR_Checker_markIndex___closed__0 = (const lean_object*)&l_Lean_IR_Checker_markIndex___closed__0_value;
static const lean_string_object l_Lean_IR_Checker_markIndex___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = " has already been used"};
static const lean_object* l_Lean_IR_Checker_markIndex___closed__1 = (const lean_object*)&l_Lean_IR_Checker_markIndex___closed__1_value;
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
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_Checker_checkVar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "unknown variable '"};
static const lean_object* l_Lean_IR_Checker_checkVar___closed__0 = (const lean_object*)&l_Lean_IR_Checker_checkVar___closed__0_value;
static const lean_string_object l_Lean_IR_Checker_checkVar___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "x_"};
static const lean_object* l_Lean_IR_Checker_checkVar___closed__1 = (const lean_object*)&l_Lean_IR_Checker_checkVar___closed__1_value;
static const lean_string_object l_Lean_IR_Checker_checkVar___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_IR_Checker_checkVar___closed__2 = (const lean_object*)&l_Lean_IR_Checker_checkVar___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_Checker_checkJP___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "unknown join point '"};
static const lean_object* l_Lean_IR_Checker_checkJP___closed__0 = (const lean_object*)&l_Lean_IR_Checker_checkJP___closed__0_value;
static const lean_string_object l_Lean_IR_Checker_checkJP___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "block_"};
static const lean_object* l_Lean_IR_Checker_checkJP___closed__1 = (const lean_object*)&l_Lean_IR_Checker_checkJP___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_Checker_checkEqTypes___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 34, .m_data = "unexpected type '{ty₁}' != '{ty₂}'"};
static const lean_object* l_Lean_IR_Checker_checkEqTypes___closed__0 = (const lean_object*)&l_Lean_IR_Checker_checkEqTypes___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_Checker_checkType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "unexpected type '"};
static const lean_object* l_Lean_IR_Checker_checkType___closed__0 = (const lean_object*)&l_Lean_IR_Checker_checkType___closed__0_value;
static const lean_string_object l_Lean_IR_Checker_checkType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_IR_Checker_checkType___closed__1 = (const lean_object*)&l_Lean_IR_Checker_checkType___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_Checker_checkObjType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "object expected"};
static const lean_object* l_Lean_IR_Checker_checkObjType___closed__0 = (const lean_object*)&l_Lean_IR_Checker_checkObjType___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_Checker_checkScalarType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "scalar expected"};
static const lean_object* l_Lean_IR_Checker_checkScalarType___closed__0 = (const lean_object*)&l_Lean_IR_Checker_checkScalarType___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_IR_Checker_withParams___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_Checker_withParams___closed__0;
static lean_once_cell_t l_Lean_IR_Checker_withParams___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_Checker_withParams___closed__1;
static const lean_closure_object l_Lean_IR_Checker_withParams___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_Checker_withParams___closed__2 = (const lean_object*)&l_Lean_IR_Checker_withParams___closed__2_value;
static const lean_closure_object l_Lean_IR_Checker_withParams___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_Checker_withParams___closed__3 = (const lean_object*)&l_Lean_IR_Checker_withParams___closed__3_value;
static const lean_closure_object l_Lean_IR_Checker_withParams___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_Checker_withParams___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_Checker_withParams___closed__4 = (const lean_object*)&l_Lean_IR_Checker_withParams___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFnBody(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFnBody___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getMaxCtorFields___boxed(lean_object* v_a_00___x40___internal___hyg_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = lean_get_max_ctor_fields(v_a_00___x40___internal___hyg_2_);
return v_res_3_;
}
}
static lean_object* _init_l_Lean_IR_Checker_maxCtorFields___closed__0(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_box(0);
v___x_5_ = lean_get_max_ctor_fields(v___x_4_);
return v___x_5_;
}
}
static lean_object* _init_l_Lean_IR_Checker_maxCtorFields(void){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_obj_once(&l_Lean_IR_Checker_maxCtorFields___closed__0, &l_Lean_IR_Checker_maxCtorFields___closed__0_once, _init_l_Lean_IR_Checker_maxCtorFields___closed__0);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getMaxCtorScalarsSize___boxed(lean_object* v_a_00___x40___internal___hyg_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = lean_get_max_ctor_scalars_size(v_a_00___x40___internal___hyg_8_);
return v_res_9_;
}
}
static lean_object* _init_l_Lean_IR_Checker_maxCtorScalarsSize___closed__0(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = lean_box(0);
v___x_11_ = lean_get_max_ctor_scalars_size(v___x_10_);
return v___x_11_;
}
}
static lean_object* _init_l_Lean_IR_Checker_maxCtorScalarsSize(void){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_obj_once(&l_Lean_IR_Checker_maxCtorScalarsSize___closed__0, &l_Lean_IR_Checker_maxCtorScalarsSize___closed__0_once, _init_l_Lean_IR_Checker_maxCtorScalarsSize___closed__0);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getMaxCtorTag___boxed(lean_object* v_a_00___x40___internal___hyg_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = lean_get_max_ctor_tag(v_a_00___x40___internal___hyg_14_);
return v_res_15_;
}
}
static lean_object* _init_l_Lean_IR_Checker_maxCtorTag___closed__0(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = lean_box(0);
v___x_17_ = lean_get_max_ctor_tag(v___x_16_);
return v___x_17_;
}
}
static lean_object* _init_l_Lean_IR_Checker_maxCtorTag(void){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lean_obj_once(&l_Lean_IR_Checker_maxCtorTag___closed__0, &l_Lean_IR_Checker_maxCtorTag___closed__0_once, _init_l_Lean_IR_Checker_maxCtorTag___closed__0);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getUSizeSize___boxed(lean_object* v_a_00___x40___internal___hyg_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = lean_get_usize_size(v_a_00___x40___internal___hyg_20_);
return v_res_21_;
}
}
static lean_object* _init_l_Lean_IR_Checker_usizeSize___closed__0(void){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = lean_box(0);
v___x_23_ = lean_get_usize_size(v___x_22_);
return v___x_23_;
}
}
static lean_object* _init_l_Lean_IR_Checker_usizeSize(void){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lean_obj_once(&l_Lean_IR_Checker_usizeSize___closed__0, &l_Lean_IR_Checker_usizeSize___closed__0_once, _init_l_Lean_IR_Checker_usizeSize___closed__0);
return v___x_24_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_25_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__0);
v___x_27_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_27_, 0, v___x_26_);
return v___x_27_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_28_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1);
v___x_29_ = lean_unsigned_to_nat(0u);
v___x_30_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_30_, 0, v___x_29_);
lean_ctor_set(v___x_30_, 1, v___x_29_);
lean_ctor_set(v___x_30_, 2, v___x_29_);
lean_ctor_set(v___x_30_, 3, v___x_29_);
lean_ctor_set(v___x_30_, 4, v___x_28_);
lean_ctor_set(v___x_30_, 5, v___x_28_);
lean_ctor_set(v___x_30_, 6, v___x_28_);
lean_ctor_set(v___x_30_, 7, v___x_28_);
lean_ctor_set(v___x_30_, 8, v___x_28_);
lean_ctor_set(v___x_30_, 9, v___x_28_);
return v___x_30_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_31_ = lean_unsigned_to_nat(32u);
v___x_32_ = lean_mk_empty_array_with_capacity(v___x_31_);
v___x_33_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_33_, 0, v___x_32_);
return v___x_33_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_34_ = ((size_t)5ULL);
v___x_35_ = lean_unsigned_to_nat(0u);
v___x_36_ = lean_unsigned_to_nat(32u);
v___x_37_ = lean_mk_empty_array_with_capacity(v___x_36_);
v___x_38_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__3);
v___x_39_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_39_, 0, v___x_38_);
lean_ctor_set(v___x_39_, 1, v___x_37_);
lean_ctor_set(v___x_39_, 2, v___x_35_);
lean_ctor_set(v___x_39_, 3, v___x_35_);
lean_ctor_set_usize(v___x_39_, 4, v___x_34_);
return v___x_39_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_40_ = lean_box(1);
v___x_41_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__4);
v___x_42_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1);
v___x_43_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
lean_ctor_set(v___x_43_, 1, v___x_41_);
lean_ctor_set(v___x_43_, 2, v___x_40_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0(lean_object* v_msgData_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v___x_48_; lean_object* v_env_49_; lean_object* v_options_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_48_ = lean_st_ref_get(v___y_46_);
v_env_49_ = lean_ctor_get(v___x_48_, 0);
lean_inc_ref(v_env_49_);
lean_dec(v___x_48_);
v_options_50_ = lean_ctor_get(v___y_45_, 2);
v___x_51_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__2);
v___x_52_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_50_);
v___x_53_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_53_, 0, v_env_49_);
lean_ctor_set(v___x_53_, 1, v___x_51_);
lean_ctor_set(v___x_53_, 2, v___x_52_);
lean_ctor_set(v___x_53_, 3, v_options_50_);
v___x_54_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
lean_ctor_set(v___x_54_, 1, v_msgData_44_);
v___x_55_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___boxed(lean_object* v_msgData_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0(v_msgData_56_, v___y_57_, v___y_58_);
lean_dec(v___y_58_);
lean_dec_ref(v___y_57_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___redArg(lean_object* v_msg_61_, lean_object* v___y_62_, lean_object* v___y_63_){
_start:
{
lean_object* v_ref_65_; lean_object* v___x_66_; lean_object* v_a_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_75_; 
v_ref_65_ = lean_ctor_get(v___y_62_, 5);
v___x_66_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0(v_msg_61_, v___y_62_, v___y_63_);
v_a_67_ = lean_ctor_get(v___x_66_, 0);
v_isSharedCheck_75_ = !lean_is_exclusive(v___x_66_);
if (v_isSharedCheck_75_ == 0)
{
v___x_69_ = v___x_66_;
v_isShared_70_ = v_isSharedCheck_75_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_a_67_);
lean_dec(v___x_66_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_75_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___x_71_; lean_object* v___x_73_; 
lean_inc(v_ref_65_);
v___x_71_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_71_, 0, v_ref_65_);
lean_ctor_set(v___x_71_, 1, v_a_67_);
if (v_isShared_70_ == 0)
{
lean_ctor_set_tag(v___x_69_, 1);
lean_ctor_set(v___x_69_, 0, v___x_71_);
v___x_73_ = v___x_69_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v___x_71_);
v___x_73_ = v_reuseFailAlloc_74_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
return v___x_73_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___redArg___boxed(lean_object* v_msg_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___redArg(v_msg_76_, v___y_77_, v___y_78_);
lean_dec(v___y_78_);
lean_dec_ref(v___y_77_);
return v_res_80_;
}
}
static lean_object* _init_l_Lean_IR_Checker_throwCheckerError___redArg___closed__1(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_82_ = ((lean_object*)(l_Lean_IR_Checker_throwCheckerError___redArg___closed__0));
v___x_83_ = l_Lean_stringToMessageData(v___x_82_);
return v___x_83_;
}
}
static lean_object* _init_l_Lean_IR_Checker_throwCheckerError___redArg___closed__3(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = ((lean_object*)(l_Lean_IR_Checker_throwCheckerError___redArg___closed__2));
v___x_86_ = l_Lean_stringToMessageData(v___x_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError___redArg(lean_object* v_msg_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_){
_start:
{
lean_object* v_currentDecl_93_; lean_object* v___x_94_; lean_object* v___x_95_; uint8_t v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v_currentDecl_93_ = lean_ctor_get(v_a_88_, 1);
v___x_94_ = l_Lean_IR_Decl_name(v_currentDecl_93_);
v___x_95_ = lean_obj_once(&l_Lean_IR_Checker_throwCheckerError___redArg___closed__1, &l_Lean_IR_Checker_throwCheckerError___redArg___closed__1_once, _init_l_Lean_IR_Checker_throwCheckerError___redArg___closed__1);
v___x_96_ = 0;
v___x_97_ = l_Lean_MessageData_ofConstName(v___x_94_, v___x_96_);
v___x_98_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_95_);
lean_ctor_set(v___x_98_, 1, v___x_97_);
v___x_99_ = lean_obj_once(&l_Lean_IR_Checker_throwCheckerError___redArg___closed__3, &l_Lean_IR_Checker_throwCheckerError___redArg___closed__3_once, _init_l_Lean_IR_Checker_throwCheckerError___redArg___closed__3);
v___x_100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_100_, 0, v___x_98_);
lean_ctor_set(v___x_100_, 1, v___x_99_);
v___x_101_ = l_Lean_stringToMessageData(v_msg_87_);
v___x_102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_102_, 0, v___x_100_);
lean_ctor_set(v___x_102_, 1, v___x_101_);
v___x_103_ = l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___redArg(v___x_102_, v_a_90_, v_a_91_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError___redArg___boxed(lean_object* v_msg_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_);
lean_dec(v_a_108_);
lean_dec_ref(v_a_107_);
lean_dec(v_a_106_);
lean_dec_ref(v_a_105_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError(lean_object* v_00_u03b1_111_, lean_object* v_msg_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_112_, v_a_113_, v_a_114_, v_a_115_, v_a_116_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError___boxed(lean_object* v_00_u03b1_119_, lean_object* v_msg_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Lean_IR_Checker_throwCheckerError(v_00_u03b1_119_, v_msg_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_);
lean_dec(v_a_124_);
lean_dec_ref(v_a_123_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0(lean_object* v_00_u03b1_127_, lean_object* v_msg_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___redArg(v_msg_128_, v___y_131_, v___y_132_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___boxed(lean_object* v_00_u03b1_135_, lean_object* v_msg_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0(v_00_u03b1_135_, v_msg_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1___redArg(lean_object* v_k_143_, lean_object* v_v_144_, lean_object* v_t_145_){
_start:
{
if (lean_obj_tag(v_t_145_) == 0)
{
lean_object* v_size_146_; lean_object* v_k_147_; lean_object* v_v_148_; lean_object* v_l_149_; lean_object* v_r_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_431_; 
v_size_146_ = lean_ctor_get(v_t_145_, 0);
v_k_147_ = lean_ctor_get(v_t_145_, 1);
v_v_148_ = lean_ctor_get(v_t_145_, 2);
v_l_149_ = lean_ctor_get(v_t_145_, 3);
v_r_150_ = lean_ctor_get(v_t_145_, 4);
v_isSharedCheck_431_ = !lean_is_exclusive(v_t_145_);
if (v_isSharedCheck_431_ == 0)
{
v___x_152_ = v_t_145_;
v_isShared_153_ = v_isSharedCheck_431_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_r_150_);
lean_inc(v_l_149_);
lean_inc(v_v_148_);
lean_inc(v_k_147_);
lean_inc(v_size_146_);
lean_dec(v_t_145_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_431_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
uint8_t v___x_154_; 
v___x_154_ = lean_nat_dec_lt(v_k_143_, v_k_147_);
if (v___x_154_ == 0)
{
uint8_t v___x_155_; 
v___x_155_ = lean_nat_dec_eq(v_k_143_, v_k_147_);
if (v___x_155_ == 0)
{
lean_object* v_impl_156_; lean_object* v___x_157_; 
lean_dec(v_size_146_);
v_impl_156_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1___redArg(v_k_143_, v_v_144_, v_r_150_);
v___x_157_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_149_) == 0)
{
lean_object* v_size_158_; lean_object* v_size_159_; lean_object* v_k_160_; lean_object* v_v_161_; lean_object* v_l_162_; lean_object* v_r_163_; lean_object* v___x_164_; lean_object* v___x_165_; uint8_t v___x_166_; 
v_size_158_ = lean_ctor_get(v_l_149_, 0);
v_size_159_ = lean_ctor_get(v_impl_156_, 0);
lean_inc(v_size_159_);
v_k_160_ = lean_ctor_get(v_impl_156_, 1);
lean_inc(v_k_160_);
v_v_161_ = lean_ctor_get(v_impl_156_, 2);
lean_inc(v_v_161_);
v_l_162_ = lean_ctor_get(v_impl_156_, 3);
lean_inc(v_l_162_);
v_r_163_ = lean_ctor_get(v_impl_156_, 4);
lean_inc(v_r_163_);
v___x_164_ = lean_unsigned_to_nat(3u);
v___x_165_ = lean_nat_mul(v___x_164_, v_size_158_);
v___x_166_ = lean_nat_dec_lt(v___x_165_, v_size_159_);
lean_dec(v___x_165_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_170_; 
lean_dec(v_r_163_);
lean_dec(v_l_162_);
lean_dec(v_v_161_);
lean_dec(v_k_160_);
v___x_167_ = lean_nat_add(v___x_157_, v_size_158_);
v___x_168_ = lean_nat_add(v___x_167_, v_size_159_);
lean_dec(v_size_159_);
lean_dec(v___x_167_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 4, v_impl_156_);
lean_ctor_set(v___x_152_, 0, v___x_168_);
v___x_170_ = v___x_152_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_168_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v_k_147_);
lean_ctor_set(v_reuseFailAlloc_171_, 2, v_v_148_);
lean_ctor_set(v_reuseFailAlloc_171_, 3, v_l_149_);
lean_ctor_set(v_reuseFailAlloc_171_, 4, v_impl_156_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
else
{
lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_235_; 
v_isSharedCheck_235_ = !lean_is_exclusive(v_impl_156_);
if (v_isSharedCheck_235_ == 0)
{
lean_object* v_unused_236_; lean_object* v_unused_237_; lean_object* v_unused_238_; lean_object* v_unused_239_; lean_object* v_unused_240_; 
v_unused_236_ = lean_ctor_get(v_impl_156_, 4);
lean_dec(v_unused_236_);
v_unused_237_ = lean_ctor_get(v_impl_156_, 3);
lean_dec(v_unused_237_);
v_unused_238_ = lean_ctor_get(v_impl_156_, 2);
lean_dec(v_unused_238_);
v_unused_239_ = lean_ctor_get(v_impl_156_, 1);
lean_dec(v_unused_239_);
v_unused_240_ = lean_ctor_get(v_impl_156_, 0);
lean_dec(v_unused_240_);
v___x_173_ = v_impl_156_;
v_isShared_174_ = v_isSharedCheck_235_;
goto v_resetjp_172_;
}
else
{
lean_dec(v_impl_156_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_235_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v_size_175_; lean_object* v_k_176_; lean_object* v_v_177_; lean_object* v_l_178_; lean_object* v_r_179_; lean_object* v_size_180_; lean_object* v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
v_size_175_ = lean_ctor_get(v_l_162_, 0);
v_k_176_ = lean_ctor_get(v_l_162_, 1);
v_v_177_ = lean_ctor_get(v_l_162_, 2);
v_l_178_ = lean_ctor_get(v_l_162_, 3);
v_r_179_ = lean_ctor_get(v_l_162_, 4);
v_size_180_ = lean_ctor_get(v_r_163_, 0);
v___x_181_ = lean_unsigned_to_nat(2u);
v___x_182_ = lean_nat_mul(v___x_181_, v_size_180_);
v___x_183_ = lean_nat_dec_lt(v_size_175_, v___x_182_);
lean_dec(v___x_182_);
if (v___x_183_ == 0)
{
lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_211_; 
lean_inc(v_r_179_);
lean_inc(v_l_178_);
lean_inc(v_v_177_);
lean_inc(v_k_176_);
v_isSharedCheck_211_ = !lean_is_exclusive(v_l_162_);
if (v_isSharedCheck_211_ == 0)
{
lean_object* v_unused_212_; lean_object* v_unused_213_; lean_object* v_unused_214_; lean_object* v_unused_215_; lean_object* v_unused_216_; 
v_unused_212_ = lean_ctor_get(v_l_162_, 4);
lean_dec(v_unused_212_);
v_unused_213_ = lean_ctor_get(v_l_162_, 3);
lean_dec(v_unused_213_);
v_unused_214_ = lean_ctor_get(v_l_162_, 2);
lean_dec(v_unused_214_);
v_unused_215_ = lean_ctor_get(v_l_162_, 1);
lean_dec(v_unused_215_);
v_unused_216_ = lean_ctor_get(v_l_162_, 0);
lean_dec(v_unused_216_);
v___x_185_ = v_l_162_;
v_isShared_186_ = v_isSharedCheck_211_;
goto v_resetjp_184_;
}
else
{
lean_dec(v_l_162_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_211_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___y_190_; lean_object* v___y_191_; lean_object* v___y_192_; lean_object* v___y_201_; 
v___x_187_ = lean_nat_add(v___x_157_, v_size_158_);
v___x_188_ = lean_nat_add(v___x_187_, v_size_159_);
lean_dec(v_size_159_);
if (lean_obj_tag(v_l_178_) == 0)
{
lean_object* v_size_209_; 
v_size_209_ = lean_ctor_get(v_l_178_, 0);
lean_inc(v_size_209_);
v___y_201_ = v_size_209_;
goto v___jp_200_;
}
else
{
lean_object* v___x_210_; 
v___x_210_ = lean_unsigned_to_nat(0u);
v___y_201_ = v___x_210_;
goto v___jp_200_;
}
v___jp_189_:
{
lean_object* v___x_193_; lean_object* v___x_195_; 
v___x_193_ = lean_nat_add(v___y_191_, v___y_192_);
lean_dec(v___y_192_);
lean_dec(v___y_191_);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 4, v_r_163_);
lean_ctor_set(v___x_185_, 3, v_r_179_);
lean_ctor_set(v___x_185_, 2, v_v_161_);
lean_ctor_set(v___x_185_, 1, v_k_160_);
lean_ctor_set(v___x_185_, 0, v___x_193_);
v___x_195_ = v___x_185_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_193_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v_k_160_);
lean_ctor_set(v_reuseFailAlloc_199_, 2, v_v_161_);
lean_ctor_set(v_reuseFailAlloc_199_, 3, v_r_179_);
lean_ctor_set(v_reuseFailAlloc_199_, 4, v_r_163_);
v___x_195_ = v_reuseFailAlloc_199_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
lean_object* v___x_197_; 
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 4, v___x_195_);
lean_ctor_set(v___x_173_, 3, v___y_190_);
lean_ctor_set(v___x_173_, 2, v_v_177_);
lean_ctor_set(v___x_173_, 1, v_k_176_);
lean_ctor_set(v___x_173_, 0, v___x_188_);
v___x_197_ = v___x_173_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_188_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v_k_176_);
lean_ctor_set(v_reuseFailAlloc_198_, 2, v_v_177_);
lean_ctor_set(v_reuseFailAlloc_198_, 3, v___y_190_);
lean_ctor_set(v_reuseFailAlloc_198_, 4, v___x_195_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
v___jp_200_:
{
lean_object* v___x_202_; lean_object* v___x_204_; 
v___x_202_ = lean_nat_add(v___x_187_, v___y_201_);
lean_dec(v___y_201_);
lean_dec(v___x_187_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 4, v_l_178_);
lean_ctor_set(v___x_152_, 0, v___x_202_);
v___x_204_ = v___x_152_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v___x_202_);
lean_ctor_set(v_reuseFailAlloc_208_, 1, v_k_147_);
lean_ctor_set(v_reuseFailAlloc_208_, 2, v_v_148_);
lean_ctor_set(v_reuseFailAlloc_208_, 3, v_l_149_);
lean_ctor_set(v_reuseFailAlloc_208_, 4, v_l_178_);
v___x_204_ = v_reuseFailAlloc_208_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
lean_object* v___x_205_; 
v___x_205_ = lean_nat_add(v___x_157_, v_size_180_);
if (lean_obj_tag(v_r_179_) == 0)
{
lean_object* v_size_206_; 
v_size_206_ = lean_ctor_get(v_r_179_, 0);
lean_inc(v_size_206_);
v___y_190_ = v___x_204_;
v___y_191_ = v___x_205_;
v___y_192_ = v_size_206_;
goto v___jp_189_;
}
else
{
lean_object* v___x_207_; 
v___x_207_ = lean_unsigned_to_nat(0u);
v___y_190_ = v___x_204_;
v___y_191_ = v___x_205_;
v___y_192_ = v___x_207_;
goto v___jp_189_;
}
}
}
}
}
else
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_221_; 
lean_del_object(v___x_152_);
v___x_217_ = lean_nat_add(v___x_157_, v_size_158_);
v___x_218_ = lean_nat_add(v___x_217_, v_size_159_);
lean_dec(v_size_159_);
v___x_219_ = lean_nat_add(v___x_217_, v_size_175_);
lean_dec(v___x_217_);
lean_inc_ref(v_l_149_);
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 4, v_l_162_);
lean_ctor_set(v___x_173_, 3, v_l_149_);
lean_ctor_set(v___x_173_, 2, v_v_148_);
lean_ctor_set(v___x_173_, 1, v_k_147_);
lean_ctor_set(v___x_173_, 0, v___x_219_);
v___x_221_ = v___x_173_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_219_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v_k_147_);
lean_ctor_set(v_reuseFailAlloc_234_, 2, v_v_148_);
lean_ctor_set(v_reuseFailAlloc_234_, 3, v_l_149_);
lean_ctor_set(v_reuseFailAlloc_234_, 4, v_l_162_);
v___x_221_ = v_reuseFailAlloc_234_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_228_; 
v_isSharedCheck_228_ = !lean_is_exclusive(v_l_149_);
if (v_isSharedCheck_228_ == 0)
{
lean_object* v_unused_229_; lean_object* v_unused_230_; lean_object* v_unused_231_; lean_object* v_unused_232_; lean_object* v_unused_233_; 
v_unused_229_ = lean_ctor_get(v_l_149_, 4);
lean_dec(v_unused_229_);
v_unused_230_ = lean_ctor_get(v_l_149_, 3);
lean_dec(v_unused_230_);
v_unused_231_ = lean_ctor_get(v_l_149_, 2);
lean_dec(v_unused_231_);
v_unused_232_ = lean_ctor_get(v_l_149_, 1);
lean_dec(v_unused_232_);
v_unused_233_ = lean_ctor_get(v_l_149_, 0);
lean_dec(v_unused_233_);
v___x_223_ = v_l_149_;
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
else
{
lean_dec(v_l_149_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_226_; 
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 4, v_r_163_);
lean_ctor_set(v___x_223_, 3, v___x_221_);
lean_ctor_set(v___x_223_, 2, v_v_161_);
lean_ctor_set(v___x_223_, 1, v_k_160_);
lean_ctor_set(v___x_223_, 0, v___x_218_);
v___x_226_ = v___x_223_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_218_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v_k_160_);
lean_ctor_set(v_reuseFailAlloc_227_, 2, v_v_161_);
lean_ctor_set(v_reuseFailAlloc_227_, 3, v___x_221_);
lean_ctor_set(v_reuseFailAlloc_227_, 4, v_r_163_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_241_; 
v_l_241_ = lean_ctor_get(v_impl_156_, 3);
lean_inc(v_l_241_);
if (lean_obj_tag(v_l_241_) == 0)
{
lean_object* v_r_242_; lean_object* v_k_243_; lean_object* v_v_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_267_; 
v_r_242_ = lean_ctor_get(v_impl_156_, 4);
v_k_243_ = lean_ctor_get(v_impl_156_, 1);
v_v_244_ = lean_ctor_get(v_impl_156_, 2);
v_isSharedCheck_267_ = !lean_is_exclusive(v_impl_156_);
if (v_isSharedCheck_267_ == 0)
{
lean_object* v_unused_268_; lean_object* v_unused_269_; 
v_unused_268_ = lean_ctor_get(v_impl_156_, 3);
lean_dec(v_unused_268_);
v_unused_269_ = lean_ctor_get(v_impl_156_, 0);
lean_dec(v_unused_269_);
v___x_246_ = v_impl_156_;
v_isShared_247_ = v_isSharedCheck_267_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_r_242_);
lean_inc(v_v_244_);
lean_inc(v_k_243_);
lean_dec(v_impl_156_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_267_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v_k_248_; lean_object* v_v_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_263_; 
v_k_248_ = lean_ctor_get(v_l_241_, 1);
v_v_249_ = lean_ctor_get(v_l_241_, 2);
v_isSharedCheck_263_ = !lean_is_exclusive(v_l_241_);
if (v_isSharedCheck_263_ == 0)
{
lean_object* v_unused_264_; lean_object* v_unused_265_; lean_object* v_unused_266_; 
v_unused_264_ = lean_ctor_get(v_l_241_, 4);
lean_dec(v_unused_264_);
v_unused_265_ = lean_ctor_get(v_l_241_, 3);
lean_dec(v_unused_265_);
v_unused_266_ = lean_ctor_get(v_l_241_, 0);
lean_dec(v_unused_266_);
v___x_251_ = v_l_241_;
v_isShared_252_ = v_isSharedCheck_263_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_v_249_);
lean_inc(v_k_248_);
lean_dec(v_l_241_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_263_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_253_; lean_object* v___x_255_; 
v___x_253_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_242_, 2);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 4, v_r_242_);
lean_ctor_set(v___x_251_, 3, v_r_242_);
lean_ctor_set(v___x_251_, 2, v_v_148_);
lean_ctor_set(v___x_251_, 1, v_k_147_);
lean_ctor_set(v___x_251_, 0, v___x_157_);
v___x_255_ = v___x_251_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_157_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v_k_147_);
lean_ctor_set(v_reuseFailAlloc_262_, 2, v_v_148_);
lean_ctor_set(v_reuseFailAlloc_262_, 3, v_r_242_);
lean_ctor_set(v_reuseFailAlloc_262_, 4, v_r_242_);
v___x_255_ = v_reuseFailAlloc_262_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
lean_object* v___x_257_; 
lean_inc(v_r_242_);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 3, v_r_242_);
lean_ctor_set(v___x_246_, 0, v___x_157_);
v___x_257_ = v___x_246_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_157_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_k_243_);
lean_ctor_set(v_reuseFailAlloc_261_, 2, v_v_244_);
lean_ctor_set(v_reuseFailAlloc_261_, 3, v_r_242_);
lean_ctor_set(v_reuseFailAlloc_261_, 4, v_r_242_);
v___x_257_ = v_reuseFailAlloc_261_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
lean_object* v___x_259_; 
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 4, v___x_257_);
lean_ctor_set(v___x_152_, 3, v___x_255_);
lean_ctor_set(v___x_152_, 2, v_v_249_);
lean_ctor_set(v___x_152_, 1, v_k_248_);
lean_ctor_set(v___x_152_, 0, v___x_253_);
v___x_259_ = v___x_152_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_253_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v_k_248_);
lean_ctor_set(v_reuseFailAlloc_260_, 2, v_v_249_);
lean_ctor_set(v_reuseFailAlloc_260_, 3, v___x_255_);
lean_ctor_set(v_reuseFailAlloc_260_, 4, v___x_257_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
}
}
else
{
lean_object* v_r_270_; 
v_r_270_ = lean_ctor_get(v_impl_156_, 4);
lean_inc(v_r_270_);
if (lean_obj_tag(v_r_270_) == 0)
{
lean_object* v_k_271_; lean_object* v_v_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_283_; 
v_k_271_ = lean_ctor_get(v_impl_156_, 1);
v_v_272_ = lean_ctor_get(v_impl_156_, 2);
v_isSharedCheck_283_ = !lean_is_exclusive(v_impl_156_);
if (v_isSharedCheck_283_ == 0)
{
lean_object* v_unused_284_; lean_object* v_unused_285_; lean_object* v_unused_286_; 
v_unused_284_ = lean_ctor_get(v_impl_156_, 4);
lean_dec(v_unused_284_);
v_unused_285_ = lean_ctor_get(v_impl_156_, 3);
lean_dec(v_unused_285_);
v_unused_286_ = lean_ctor_get(v_impl_156_, 0);
lean_dec(v_unused_286_);
v___x_274_ = v_impl_156_;
v_isShared_275_ = v_isSharedCheck_283_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_v_272_);
lean_inc(v_k_271_);
lean_dec(v_impl_156_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_283_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_276_; lean_object* v___x_278_; 
v___x_276_ = lean_unsigned_to_nat(3u);
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 4, v_l_241_);
lean_ctor_set(v___x_274_, 2, v_v_148_);
lean_ctor_set(v___x_274_, 1, v_k_147_);
lean_ctor_set(v___x_274_, 0, v___x_157_);
v___x_278_ = v___x_274_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_157_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v_k_147_);
lean_ctor_set(v_reuseFailAlloc_282_, 2, v_v_148_);
lean_ctor_set(v_reuseFailAlloc_282_, 3, v_l_241_);
lean_ctor_set(v_reuseFailAlloc_282_, 4, v_l_241_);
v___x_278_ = v_reuseFailAlloc_282_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
lean_object* v___x_280_; 
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 4, v_r_270_);
lean_ctor_set(v___x_152_, 3, v___x_278_);
lean_ctor_set(v___x_152_, 2, v_v_272_);
lean_ctor_set(v___x_152_, 1, v_k_271_);
lean_ctor_set(v___x_152_, 0, v___x_276_);
v___x_280_ = v___x_152_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v___x_276_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v_k_271_);
lean_ctor_set(v_reuseFailAlloc_281_, 2, v_v_272_);
lean_ctor_set(v_reuseFailAlloc_281_, 3, v___x_278_);
lean_ctor_set(v_reuseFailAlloc_281_, 4, v_r_270_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
}
else
{
lean_object* v___x_287_; lean_object* v___x_289_; 
v___x_287_ = lean_unsigned_to_nat(2u);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 4, v_impl_156_);
lean_ctor_set(v___x_152_, 3, v_r_270_);
lean_ctor_set(v___x_152_, 0, v___x_287_);
v___x_289_ = v___x_152_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v___x_287_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v_k_147_);
lean_ctor_set(v_reuseFailAlloc_290_, 2, v_v_148_);
lean_ctor_set(v_reuseFailAlloc_290_, 3, v_r_270_);
lean_ctor_set(v_reuseFailAlloc_290_, 4, v_impl_156_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
}
}
else
{
lean_object* v___x_292_; 
lean_dec(v_v_148_);
lean_dec(v_k_147_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 2, v_v_144_);
lean_ctor_set(v___x_152_, 1, v_k_143_);
v___x_292_ = v___x_152_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_size_146_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v_k_143_);
lean_ctor_set(v_reuseFailAlloc_293_, 2, v_v_144_);
lean_ctor_set(v_reuseFailAlloc_293_, 3, v_l_149_);
lean_ctor_set(v_reuseFailAlloc_293_, 4, v_r_150_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
else
{
lean_object* v_impl_294_; lean_object* v___x_295_; 
lean_dec(v_size_146_);
v_impl_294_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1___redArg(v_k_143_, v_v_144_, v_l_149_);
v___x_295_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_150_) == 0)
{
lean_object* v_size_296_; lean_object* v_size_297_; lean_object* v_k_298_; lean_object* v_v_299_; lean_object* v_l_300_; lean_object* v_r_301_; lean_object* v___x_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
v_size_296_ = lean_ctor_get(v_r_150_, 0);
v_size_297_ = lean_ctor_get(v_impl_294_, 0);
lean_inc(v_size_297_);
v_k_298_ = lean_ctor_get(v_impl_294_, 1);
lean_inc(v_k_298_);
v_v_299_ = lean_ctor_get(v_impl_294_, 2);
lean_inc(v_v_299_);
v_l_300_ = lean_ctor_get(v_impl_294_, 3);
lean_inc(v_l_300_);
v_r_301_ = lean_ctor_get(v_impl_294_, 4);
lean_inc(v_r_301_);
v___x_302_ = lean_unsigned_to_nat(3u);
v___x_303_ = lean_nat_mul(v___x_302_, v_size_296_);
v___x_304_ = lean_nat_dec_lt(v___x_303_, v_size_297_);
lean_dec(v___x_303_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_308_; 
lean_dec(v_r_301_);
lean_dec(v_l_300_);
lean_dec(v_v_299_);
lean_dec(v_k_298_);
v___x_305_ = lean_nat_add(v___x_295_, v_size_297_);
lean_dec(v_size_297_);
v___x_306_ = lean_nat_add(v___x_305_, v_size_296_);
lean_dec(v___x_305_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 3, v_impl_294_);
lean_ctor_set(v___x_152_, 0, v___x_306_);
v___x_308_ = v___x_152_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v___x_306_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v_k_147_);
lean_ctor_set(v_reuseFailAlloc_309_, 2, v_v_148_);
lean_ctor_set(v_reuseFailAlloc_309_, 3, v_impl_294_);
lean_ctor_set(v_reuseFailAlloc_309_, 4, v_r_150_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
else
{
lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_375_; 
v_isSharedCheck_375_ = !lean_is_exclusive(v_impl_294_);
if (v_isSharedCheck_375_ == 0)
{
lean_object* v_unused_376_; lean_object* v_unused_377_; lean_object* v_unused_378_; lean_object* v_unused_379_; lean_object* v_unused_380_; 
v_unused_376_ = lean_ctor_get(v_impl_294_, 4);
lean_dec(v_unused_376_);
v_unused_377_ = lean_ctor_get(v_impl_294_, 3);
lean_dec(v_unused_377_);
v_unused_378_ = lean_ctor_get(v_impl_294_, 2);
lean_dec(v_unused_378_);
v_unused_379_ = lean_ctor_get(v_impl_294_, 1);
lean_dec(v_unused_379_);
v_unused_380_ = lean_ctor_get(v_impl_294_, 0);
lean_dec(v_unused_380_);
v___x_311_ = v_impl_294_;
v_isShared_312_ = v_isSharedCheck_375_;
goto v_resetjp_310_;
}
else
{
lean_dec(v_impl_294_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_375_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v_size_313_; lean_object* v_size_314_; lean_object* v_k_315_; lean_object* v_v_316_; lean_object* v_l_317_; lean_object* v_r_318_; lean_object* v___x_319_; lean_object* v___x_320_; uint8_t v___x_321_; 
v_size_313_ = lean_ctor_get(v_l_300_, 0);
v_size_314_ = lean_ctor_get(v_r_301_, 0);
v_k_315_ = lean_ctor_get(v_r_301_, 1);
v_v_316_ = lean_ctor_get(v_r_301_, 2);
v_l_317_ = lean_ctor_get(v_r_301_, 3);
v_r_318_ = lean_ctor_get(v_r_301_, 4);
v___x_319_ = lean_unsigned_to_nat(2u);
v___x_320_ = lean_nat_mul(v___x_319_, v_size_313_);
v___x_321_ = lean_nat_dec_lt(v_size_314_, v___x_320_);
lean_dec(v___x_320_);
if (v___x_321_ == 0)
{
lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_350_; 
lean_inc(v_r_318_);
lean_inc(v_l_317_);
lean_inc(v_v_316_);
lean_inc(v_k_315_);
v_isSharedCheck_350_ = !lean_is_exclusive(v_r_301_);
if (v_isSharedCheck_350_ == 0)
{
lean_object* v_unused_351_; lean_object* v_unused_352_; lean_object* v_unused_353_; lean_object* v_unused_354_; lean_object* v_unused_355_; 
v_unused_351_ = lean_ctor_get(v_r_301_, 4);
lean_dec(v_unused_351_);
v_unused_352_ = lean_ctor_get(v_r_301_, 3);
lean_dec(v_unused_352_);
v_unused_353_ = lean_ctor_get(v_r_301_, 2);
lean_dec(v_unused_353_);
v_unused_354_ = lean_ctor_get(v_r_301_, 1);
lean_dec(v_unused_354_);
v_unused_355_ = lean_ctor_get(v_r_301_, 0);
lean_dec(v_unused_355_);
v___x_323_ = v_r_301_;
v_isShared_324_ = v_isSharedCheck_350_;
goto v_resetjp_322_;
}
else
{
lean_dec(v_r_301_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_350_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v___x_338_; lean_object* v___y_340_; 
v___x_325_ = lean_nat_add(v___x_295_, v_size_297_);
lean_dec(v_size_297_);
v___x_326_ = lean_nat_add(v___x_325_, v_size_296_);
lean_dec(v___x_325_);
v___x_338_ = lean_nat_add(v___x_295_, v_size_313_);
if (lean_obj_tag(v_l_317_) == 0)
{
lean_object* v_size_348_; 
v_size_348_ = lean_ctor_get(v_l_317_, 0);
lean_inc(v_size_348_);
v___y_340_ = v_size_348_;
goto v___jp_339_;
}
else
{
lean_object* v___x_349_; 
v___x_349_ = lean_unsigned_to_nat(0u);
v___y_340_ = v___x_349_;
goto v___jp_339_;
}
v___jp_327_:
{
lean_object* v___x_331_; lean_object* v___x_333_; 
v___x_331_ = lean_nat_add(v___y_328_, v___y_330_);
lean_dec(v___y_330_);
lean_dec(v___y_328_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 4, v_r_150_);
lean_ctor_set(v___x_323_, 3, v_r_318_);
lean_ctor_set(v___x_323_, 2, v_v_148_);
lean_ctor_set(v___x_323_, 1, v_k_147_);
lean_ctor_set(v___x_323_, 0, v___x_331_);
v___x_333_ = v___x_323_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_331_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_k_147_);
lean_ctor_set(v_reuseFailAlloc_337_, 2, v_v_148_);
lean_ctor_set(v_reuseFailAlloc_337_, 3, v_r_318_);
lean_ctor_set(v_reuseFailAlloc_337_, 4, v_r_150_);
v___x_333_ = v_reuseFailAlloc_337_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
lean_object* v___x_335_; 
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 4, v___x_333_);
lean_ctor_set(v___x_311_, 3, v___y_329_);
lean_ctor_set(v___x_311_, 2, v_v_316_);
lean_ctor_set(v___x_311_, 1, v_k_315_);
lean_ctor_set(v___x_311_, 0, v___x_326_);
v___x_335_ = v___x_311_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_326_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v_k_315_);
lean_ctor_set(v_reuseFailAlloc_336_, 2, v_v_316_);
lean_ctor_set(v_reuseFailAlloc_336_, 3, v___y_329_);
lean_ctor_set(v_reuseFailAlloc_336_, 4, v___x_333_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
v___jp_339_:
{
lean_object* v___x_341_; lean_object* v___x_343_; 
v___x_341_ = lean_nat_add(v___x_338_, v___y_340_);
lean_dec(v___y_340_);
lean_dec(v___x_338_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 4, v_l_317_);
lean_ctor_set(v___x_152_, 3, v_l_300_);
lean_ctor_set(v___x_152_, 2, v_v_299_);
lean_ctor_set(v___x_152_, 1, v_k_298_);
lean_ctor_set(v___x_152_, 0, v___x_341_);
v___x_343_ = v___x_152_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v___x_341_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v_k_298_);
lean_ctor_set(v_reuseFailAlloc_347_, 2, v_v_299_);
lean_ctor_set(v_reuseFailAlloc_347_, 3, v_l_300_);
lean_ctor_set(v_reuseFailAlloc_347_, 4, v_l_317_);
v___x_343_ = v_reuseFailAlloc_347_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
lean_object* v___x_344_; 
v___x_344_ = lean_nat_add(v___x_295_, v_size_296_);
if (lean_obj_tag(v_r_318_) == 0)
{
lean_object* v_size_345_; 
v_size_345_ = lean_ctor_get(v_r_318_, 0);
lean_inc(v_size_345_);
v___y_328_ = v___x_344_;
v___y_329_ = v___x_343_;
v___y_330_ = v_size_345_;
goto v___jp_327_;
}
else
{
lean_object* v___x_346_; 
v___x_346_ = lean_unsigned_to_nat(0u);
v___y_328_ = v___x_344_;
v___y_329_ = v___x_343_;
v___y_330_ = v___x_346_;
goto v___jp_327_;
}
}
}
}
}
else
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_361_; 
lean_del_object(v___x_152_);
v___x_356_ = lean_nat_add(v___x_295_, v_size_297_);
lean_dec(v_size_297_);
v___x_357_ = lean_nat_add(v___x_356_, v_size_296_);
lean_dec(v___x_356_);
v___x_358_ = lean_nat_add(v___x_295_, v_size_296_);
v___x_359_ = lean_nat_add(v___x_358_, v_size_314_);
lean_dec(v___x_358_);
lean_inc_ref(v_r_150_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 4, v_r_150_);
lean_ctor_set(v___x_311_, 3, v_r_301_);
lean_ctor_set(v___x_311_, 2, v_v_148_);
lean_ctor_set(v___x_311_, 1, v_k_147_);
lean_ctor_set(v___x_311_, 0, v___x_359_);
v___x_361_ = v___x_311_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_359_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v_k_147_);
lean_ctor_set(v_reuseFailAlloc_374_, 2, v_v_148_);
lean_ctor_set(v_reuseFailAlloc_374_, 3, v_r_301_);
lean_ctor_set(v_reuseFailAlloc_374_, 4, v_r_150_);
v___x_361_ = v_reuseFailAlloc_374_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_368_; 
v_isSharedCheck_368_ = !lean_is_exclusive(v_r_150_);
if (v_isSharedCheck_368_ == 0)
{
lean_object* v_unused_369_; lean_object* v_unused_370_; lean_object* v_unused_371_; lean_object* v_unused_372_; lean_object* v_unused_373_; 
v_unused_369_ = lean_ctor_get(v_r_150_, 4);
lean_dec(v_unused_369_);
v_unused_370_ = lean_ctor_get(v_r_150_, 3);
lean_dec(v_unused_370_);
v_unused_371_ = lean_ctor_get(v_r_150_, 2);
lean_dec(v_unused_371_);
v_unused_372_ = lean_ctor_get(v_r_150_, 1);
lean_dec(v_unused_372_);
v_unused_373_ = lean_ctor_get(v_r_150_, 0);
lean_dec(v_unused_373_);
v___x_363_ = v_r_150_;
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
else
{
lean_dec(v_r_150_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_366_; 
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 4, v___x_361_);
lean_ctor_set(v___x_363_, 3, v_l_300_);
lean_ctor_set(v___x_363_, 2, v_v_299_);
lean_ctor_set(v___x_363_, 1, v_k_298_);
lean_ctor_set(v___x_363_, 0, v___x_357_);
v___x_366_ = v___x_363_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_357_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v_k_298_);
lean_ctor_set(v_reuseFailAlloc_367_, 2, v_v_299_);
lean_ctor_set(v_reuseFailAlloc_367_, 3, v_l_300_);
lean_ctor_set(v_reuseFailAlloc_367_, 4, v___x_361_);
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
}
}
}
else
{
lean_object* v_l_381_; 
v_l_381_ = lean_ctor_get(v_impl_294_, 3);
lean_inc(v_l_381_);
if (lean_obj_tag(v_l_381_) == 0)
{
lean_object* v_r_382_; lean_object* v_k_383_; lean_object* v_v_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_395_; 
v_r_382_ = lean_ctor_get(v_impl_294_, 4);
v_k_383_ = lean_ctor_get(v_impl_294_, 1);
v_v_384_ = lean_ctor_get(v_impl_294_, 2);
v_isSharedCheck_395_ = !lean_is_exclusive(v_impl_294_);
if (v_isSharedCheck_395_ == 0)
{
lean_object* v_unused_396_; lean_object* v_unused_397_; 
v_unused_396_ = lean_ctor_get(v_impl_294_, 3);
lean_dec(v_unused_396_);
v_unused_397_ = lean_ctor_get(v_impl_294_, 0);
lean_dec(v_unused_397_);
v___x_386_ = v_impl_294_;
v_isShared_387_ = v_isSharedCheck_395_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_r_382_);
lean_inc(v_v_384_);
lean_inc(v_k_383_);
lean_dec(v_impl_294_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_395_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_388_; lean_object* v___x_390_; 
v___x_388_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_382_);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 3, v_r_382_);
lean_ctor_set(v___x_386_, 2, v_v_148_);
lean_ctor_set(v___x_386_, 1, v_k_147_);
lean_ctor_set(v___x_386_, 0, v___x_295_);
v___x_390_ = v___x_386_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_295_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v_k_147_);
lean_ctor_set(v_reuseFailAlloc_394_, 2, v_v_148_);
lean_ctor_set(v_reuseFailAlloc_394_, 3, v_r_382_);
lean_ctor_set(v_reuseFailAlloc_394_, 4, v_r_382_);
v___x_390_ = v_reuseFailAlloc_394_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
lean_object* v___x_392_; 
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 4, v___x_390_);
lean_ctor_set(v___x_152_, 3, v_l_381_);
lean_ctor_set(v___x_152_, 2, v_v_384_);
lean_ctor_set(v___x_152_, 1, v_k_383_);
lean_ctor_set(v___x_152_, 0, v___x_388_);
v___x_392_ = v___x_152_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v___x_388_);
lean_ctor_set(v_reuseFailAlloc_393_, 1, v_k_383_);
lean_ctor_set(v_reuseFailAlloc_393_, 2, v_v_384_);
lean_ctor_set(v_reuseFailAlloc_393_, 3, v_l_381_);
lean_ctor_set(v_reuseFailAlloc_393_, 4, v___x_390_);
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
else
{
lean_object* v_r_398_; 
v_r_398_ = lean_ctor_get(v_impl_294_, 4);
lean_inc(v_r_398_);
if (lean_obj_tag(v_r_398_) == 0)
{
lean_object* v_k_399_; lean_object* v_v_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_423_; 
v_k_399_ = lean_ctor_get(v_impl_294_, 1);
v_v_400_ = lean_ctor_get(v_impl_294_, 2);
v_isSharedCheck_423_ = !lean_is_exclusive(v_impl_294_);
if (v_isSharedCheck_423_ == 0)
{
lean_object* v_unused_424_; lean_object* v_unused_425_; lean_object* v_unused_426_; 
v_unused_424_ = lean_ctor_get(v_impl_294_, 4);
lean_dec(v_unused_424_);
v_unused_425_ = lean_ctor_get(v_impl_294_, 3);
lean_dec(v_unused_425_);
v_unused_426_ = lean_ctor_get(v_impl_294_, 0);
lean_dec(v_unused_426_);
v___x_402_ = v_impl_294_;
v_isShared_403_ = v_isSharedCheck_423_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_v_400_);
lean_inc(v_k_399_);
lean_dec(v_impl_294_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_423_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v_k_404_; lean_object* v_v_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_419_; 
v_k_404_ = lean_ctor_get(v_r_398_, 1);
v_v_405_ = lean_ctor_get(v_r_398_, 2);
v_isSharedCheck_419_ = !lean_is_exclusive(v_r_398_);
if (v_isSharedCheck_419_ == 0)
{
lean_object* v_unused_420_; lean_object* v_unused_421_; lean_object* v_unused_422_; 
v_unused_420_ = lean_ctor_get(v_r_398_, 4);
lean_dec(v_unused_420_);
v_unused_421_ = lean_ctor_get(v_r_398_, 3);
lean_dec(v_unused_421_);
v_unused_422_ = lean_ctor_get(v_r_398_, 0);
lean_dec(v_unused_422_);
v___x_407_ = v_r_398_;
v_isShared_408_ = v_isSharedCheck_419_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_v_405_);
lean_inc(v_k_404_);
lean_dec(v_r_398_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_419_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_409_; lean_object* v___x_411_; 
v___x_409_ = lean_unsigned_to_nat(3u);
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 4, v_l_381_);
lean_ctor_set(v___x_407_, 3, v_l_381_);
lean_ctor_set(v___x_407_, 2, v_v_400_);
lean_ctor_set(v___x_407_, 1, v_k_399_);
lean_ctor_set(v___x_407_, 0, v___x_295_);
v___x_411_ = v___x_407_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_295_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v_k_399_);
lean_ctor_set(v_reuseFailAlloc_418_, 2, v_v_400_);
lean_ctor_set(v_reuseFailAlloc_418_, 3, v_l_381_);
lean_ctor_set(v_reuseFailAlloc_418_, 4, v_l_381_);
v___x_411_ = v_reuseFailAlloc_418_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
lean_object* v___x_413_; 
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 4, v_l_381_);
lean_ctor_set(v___x_402_, 2, v_v_148_);
lean_ctor_set(v___x_402_, 1, v_k_147_);
lean_ctor_set(v___x_402_, 0, v___x_295_);
v___x_413_ = v___x_402_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_295_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v_k_147_);
lean_ctor_set(v_reuseFailAlloc_417_, 2, v_v_148_);
lean_ctor_set(v_reuseFailAlloc_417_, 3, v_l_381_);
lean_ctor_set(v_reuseFailAlloc_417_, 4, v_l_381_);
v___x_413_ = v_reuseFailAlloc_417_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
lean_object* v___x_415_; 
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 4, v___x_413_);
lean_ctor_set(v___x_152_, 3, v___x_411_);
lean_ctor_set(v___x_152_, 2, v_v_405_);
lean_ctor_set(v___x_152_, 1, v_k_404_);
lean_ctor_set(v___x_152_, 0, v___x_409_);
v___x_415_ = v___x_152_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_409_);
lean_ctor_set(v_reuseFailAlloc_416_, 1, v_k_404_);
lean_ctor_set(v_reuseFailAlloc_416_, 2, v_v_405_);
lean_ctor_set(v_reuseFailAlloc_416_, 3, v___x_411_);
lean_ctor_set(v_reuseFailAlloc_416_, 4, v___x_413_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
}
}
else
{
lean_object* v___x_427_; lean_object* v___x_429_; 
v___x_427_ = lean_unsigned_to_nat(2u);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 4, v_r_398_);
lean_ctor_set(v___x_152_, 3, v_impl_294_);
lean_ctor_set(v___x_152_, 0, v___x_427_);
v___x_429_ = v___x_152_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_427_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v_k_147_);
lean_ctor_set(v_reuseFailAlloc_430_, 2, v_v_148_);
lean_ctor_set(v_reuseFailAlloc_430_, 3, v_impl_294_);
lean_ctor_set(v_reuseFailAlloc_430_, 4, v_r_398_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = lean_unsigned_to_nat(1u);
v___x_433_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
lean_ctor_set(v___x_433_, 1, v_k_143_);
lean_ctor_set(v___x_433_, 2, v_v_144_);
lean_ctor_set(v___x_433_, 3, v_t_145_);
lean_ctor_set(v___x_433_, 4, v_t_145_);
return v___x_433_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg(lean_object* v_k_434_, lean_object* v_t_435_){
_start:
{
if (lean_obj_tag(v_t_435_) == 0)
{
lean_object* v_k_436_; lean_object* v_l_437_; lean_object* v_r_438_; uint8_t v___x_439_; 
v_k_436_ = lean_ctor_get(v_t_435_, 1);
v_l_437_ = lean_ctor_get(v_t_435_, 3);
v_r_438_ = lean_ctor_get(v_t_435_, 4);
v___x_439_ = lean_nat_dec_lt(v_k_434_, v_k_436_);
if (v___x_439_ == 0)
{
uint8_t v___x_440_; 
v___x_440_ = lean_nat_dec_eq(v_k_434_, v_k_436_);
if (v___x_440_ == 0)
{
v_t_435_ = v_r_438_;
goto _start;
}
else
{
return v___x_440_;
}
}
else
{
v_t_435_ = v_l_437_;
goto _start;
}
}
else
{
uint8_t v___x_443_; 
v___x_443_ = 0;
return v___x_443_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg___boxed(lean_object* v_k_444_, lean_object* v_t_445_){
_start:
{
uint8_t v_res_446_; lean_object* v_r_447_; 
v_res_446_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg(v_k_444_, v_t_445_);
lean_dec(v_t_445_);
lean_dec(v_k_444_);
v_r_447_ = lean_box(v_res_446_);
return v_r_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex(lean_object* v_i_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_){
_start:
{
lean_object* v___y_457_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___y_463_; lean_object* v___x_468_; uint8_t v___x_469_; 
v___x_468_ = lean_st_ref_get(v_a_452_);
v___x_469_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg(v_i_450_, v___x_468_);
lean_dec(v___x_468_);
if (v___x_469_ == 0)
{
v___y_463_ = v_a_452_;
goto v___jp_462_;
}
else
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_470_ = ((lean_object*)(l_Lean_IR_Checker_markIndex___closed__0));
v___x_471_ = l_Nat_reprFast(v_i_450_);
v___x_472_ = lean_string_append(v___x_470_, v___x_471_);
lean_dec_ref(v___x_471_);
v___x_473_ = ((lean_object*)(l_Lean_IR_Checker_markIndex___closed__1));
v___x_474_ = lean_string_append(v___x_472_, v___x_473_);
v___x_475_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_474_, v_a_451_, v_a_452_, v_a_453_, v_a_454_);
return v___x_475_;
}
v___jp_456_:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = lean_st_ref_set(v___y_457_, v___y_459_);
v___x_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_461_, 0, v___y_458_);
return v___x_461_;
}
v___jp_462_:
{
lean_object* v___x_464_; lean_object* v___x_465_; uint8_t v___x_466_; 
v___x_464_ = lean_st_ref_take(v___y_463_);
v___x_465_ = lean_box(0);
v___x_466_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg(v_i_450_, v___x_464_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; 
v___x_467_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1___redArg(v_i_450_, v___x_465_, v___x_464_);
v___y_457_ = v___y_463_;
v___y_458_ = v___x_465_;
v___y_459_ = v___x_467_;
goto v___jp_456_;
}
else
{
lean_dec(v_i_450_);
v___y_457_ = v___y_463_;
v___y_458_ = v___x_465_;
v___y_459_ = v___x_464_;
goto v___jp_456_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex___boxed(lean_object* v_i_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Lean_IR_Checker_markIndex(v_i_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_);
lean_dec(v_a_480_);
lean_dec_ref(v_a_479_);
lean_dec(v_a_478_);
lean_dec_ref(v_a_477_);
return v_res_482_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0(lean_object* v_00_u03b2_483_, lean_object* v_k_484_, lean_object* v_t_485_){
_start:
{
uint8_t v___x_486_; 
v___x_486_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg(v_k_484_, v_t_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___boxed(lean_object* v_00_u03b2_487_, lean_object* v_k_488_, lean_object* v_t_489_){
_start:
{
uint8_t v_res_490_; lean_object* v_r_491_; 
v_res_490_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0(v_00_u03b2_487_, v_k_488_, v_t_489_);
lean_dec(v_t_489_);
lean_dec(v_k_488_);
v_r_491_ = lean_box(v_res_490_);
return v_r_491_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1(lean_object* v_00_u03b2_492_, lean_object* v_k_493_, lean_object* v_v_494_, lean_object* v_t_495_, lean_object* v_hl_496_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1___redArg(v_k_493_, v_v_494_, v_t_495_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar(lean_object* v_x_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Lean_IR_Checker_markIndex(v_x_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar___boxed(lean_object* v_x_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Lean_IR_Checker_markVar(v_x_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_);
lean_dec(v_a_509_);
lean_dec_ref(v_a_508_);
lean_dec(v_a_507_);
lean_dec_ref(v_a_506_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP(lean_object* v_j_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_Lean_IR_Checker_markIndex(v_j_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP___boxed(lean_object* v_j_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Lean_IR_Checker_markJP(v_j_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_);
lean_dec(v_a_523_);
lean_dec_ref(v_a_522_);
lean_dec(v_a_521_);
lean_dec_ref(v_a_520_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl(lean_object* v_c_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_){
_start:
{
lean_object* v___x_534_; lean_object* v_env_535_; lean_object* v_decls_536_; lean_object* v___x_537_; 
v___x_534_ = lean_st_ref_get(v_a_532_);
v_env_535_ = lean_ctor_get(v___x_534_, 0);
lean_inc_ref(v_env_535_);
lean_dec(v___x_534_);
v_decls_536_ = lean_ctor_get(v_a_529_, 2);
lean_inc(v_c_528_);
v___x_537_ = l_Lean_IR_findEnvDecl_x27(v_env_535_, v_c_528_, v_decls_536_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v___x_538_; uint8_t v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_538_ = ((lean_object*)(l_Lean_IR_Checker_getDecl___closed__0));
v___x_539_ = 1;
v___x_540_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_c_528_, v___x_539_);
v___x_541_ = lean_string_append(v___x_538_, v___x_540_);
lean_dec_ref(v___x_540_);
v___x_542_ = ((lean_object*)(l_Lean_IR_Checker_getDecl___closed__1));
v___x_543_ = lean_string_append(v___x_541_, v___x_542_);
v___x_544_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_543_, v_a_529_, v_a_530_, v_a_531_, v_a_532_);
return v___x_544_;
}
else
{
lean_object* v_val_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
lean_dec(v_c_528_);
v_val_545_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v___x_537_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_val_545_);
lean_dec(v___x_537_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
lean_ctor_set_tag(v___x_547_, 0);
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_val_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl___boxed(lean_object* v_c_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lean_IR_Checker_getDecl(v_c_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_);
lean_dec(v_a_557_);
lean_dec_ref(v_a_556_);
lean_dec(v_a_555_);
lean_dec_ref(v_a_554_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar(lean_object* v_x_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_){
_start:
{
uint8_t v___y_570_; lean_object* v_localCtx_581_; uint8_t v___x_582_; 
v_localCtx_581_ = lean_ctor_get(v_a_564_, 0);
v___x_582_ = l_Lean_IR_LocalContext_isLocalVar(v_localCtx_581_, v_x_563_);
if (v___x_582_ == 0)
{
uint8_t v___x_583_; 
v___x_583_ = l_Lean_IR_LocalContext_isParam(v_localCtx_581_, v_x_563_);
v___y_570_ = v___x_583_;
goto v___jp_569_;
}
else
{
v___y_570_ = v___x_582_;
goto v___jp_569_;
}
v___jp_569_:
{
if (v___y_570_ == 0)
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_571_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__0));
v___x_572_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__1));
v___x_573_ = l_Nat_reprFast(v_x_563_);
v___x_574_ = lean_string_append(v___x_572_, v___x_573_);
lean_dec_ref(v___x_573_);
v___x_575_ = lean_string_append(v___x_571_, v___x_574_);
lean_dec_ref(v___x_574_);
v___x_576_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v___x_577_ = lean_string_append(v___x_575_, v___x_576_);
v___x_578_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_577_, v_a_564_, v_a_565_, v_a_566_, v_a_567_);
return v___x_578_;
}
else
{
lean_object* v___x_579_; lean_object* v___x_580_; 
lean_dec(v_x_563_);
v___x_579_ = lean_box(0);
v___x_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
return v___x_580_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar___boxed(lean_object* v_x_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Lean_IR_Checker_checkVar(v_x_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_);
lean_dec(v_a_588_);
lean_dec_ref(v_a_587_);
lean_dec(v_a_586_);
lean_dec_ref(v_a_585_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP(lean_object* v_j_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_){
_start:
{
lean_object* v_localCtx_599_; uint8_t v___x_600_; 
v_localCtx_599_ = lean_ctor_get(v_a_594_, 0);
v___x_600_ = l_Lean_IR_LocalContext_isJP(v_localCtx_599_, v_j_593_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_601_ = ((lean_object*)(l_Lean_IR_Checker_checkJP___closed__0));
v___x_602_ = ((lean_object*)(l_Lean_IR_Checker_checkJP___closed__1));
v___x_603_ = l_Nat_reprFast(v_j_593_);
v___x_604_ = lean_string_append(v___x_602_, v___x_603_);
lean_dec_ref(v___x_603_);
v___x_605_ = lean_string_append(v___x_601_, v___x_604_);
lean_dec_ref(v___x_604_);
v___x_606_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v___x_607_ = lean_string_append(v___x_605_, v___x_606_);
v___x_608_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_607_, v_a_594_, v_a_595_, v_a_596_, v_a_597_);
return v___x_608_;
}
else
{
lean_object* v___x_609_; lean_object* v___x_610_; 
lean_dec(v_j_593_);
v___x_609_ = lean_box(0);
v___x_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
return v___x_610_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP___boxed(lean_object* v_j_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Lean_IR_Checker_checkJP(v_j_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_);
lean_dec(v_a_615_);
lean_dec_ref(v_a_614_);
lean_dec(v_a_613_);
lean_dec_ref(v_a_612_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg(lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_){
_start:
{
if (lean_obj_tag(v_a_618_) == 0)
{
lean_object* v_id_624_; lean_object* v___x_625_; 
v_id_624_ = lean_ctor_get(v_a_618_, 0);
lean_inc(v_id_624_);
lean_dec_ref(v_a_618_);
v___x_625_ = l_Lean_IR_Checker_checkVar(v_id_624_, v_a_619_, v_a_620_, v_a_621_, v_a_622_);
return v___x_625_;
}
else
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = lean_box(0);
v___x_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
return v___x_627_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg___boxed(lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lean_IR_Checker_checkArg(v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_);
lean_dec(v_a_632_);
lean_dec_ref(v_a_631_);
lean_dec(v_a_630_);
lean_dec_ref(v_a_629_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(lean_object* v_as_635_, size_t v_i_636_, size_t v_stop_637_, lean_object* v_b_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
uint8_t v___x_644_; 
v___x_644_ = lean_usize_dec_eq(v_i_636_, v_stop_637_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = lean_array_uget_borrowed(v_as_635_, v_i_636_);
lean_inc(v___x_645_);
v___x_646_ = l_Lean_IR_Checker_checkArg(v___x_645_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; size_t v___x_648_; size_t v___x_649_; 
v_a_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_a_647_);
lean_dec_ref(v___x_646_);
v___x_648_ = ((size_t)1ULL);
v___x_649_ = lean_usize_add(v_i_636_, v___x_648_);
v_i_636_ = v___x_649_;
v_b_638_ = v_a_647_;
goto _start;
}
else
{
return v___x_646_;
}
}
else
{
lean_object* v___x_651_; 
v___x_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_651_, 0, v_b_638_);
return v___x_651_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0___boxed(lean_object* v_as_652_, lean_object* v_i_653_, lean_object* v_stop_654_, lean_object* v_b_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
size_t v_i_boxed_661_; size_t v_stop_boxed_662_; lean_object* v_res_663_; 
v_i_boxed_661_ = lean_unbox_usize(v_i_653_);
lean_dec(v_i_653_);
v_stop_boxed_662_ = lean_unbox_usize(v_stop_654_);
lean_dec(v_stop_654_);
v_res_663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(v_as_652_, v_i_boxed_661_, v_stop_boxed_662_, v_b_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec_ref(v_as_652_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs(lean_object* v_as_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
v___x_670_ = lean_unsigned_to_nat(0u);
v___x_671_ = lean_array_get_size(v_as_664_);
v___x_672_ = lean_box(0);
v___x_673_ = lean_nat_dec_lt(v___x_670_, v___x_671_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; 
v___x_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_674_, 0, v___x_672_);
return v___x_674_;
}
else
{
uint8_t v___x_675_; 
v___x_675_ = lean_nat_dec_le(v___x_671_, v___x_671_);
if (v___x_675_ == 0)
{
if (v___x_673_ == 0)
{
lean_object* v___x_676_; 
v___x_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_676_, 0, v___x_672_);
return v___x_676_;
}
else
{
size_t v___x_677_; size_t v___x_678_; lean_object* v___x_679_; 
v___x_677_ = ((size_t)0ULL);
v___x_678_ = lean_usize_of_nat(v___x_671_);
v___x_679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(v_as_664_, v___x_677_, v___x_678_, v___x_672_, v_a_665_, v_a_666_, v_a_667_, v_a_668_);
return v___x_679_;
}
}
else
{
size_t v___x_680_; size_t v___x_681_; lean_object* v___x_682_; 
v___x_680_ = ((size_t)0ULL);
v___x_681_ = lean_usize_of_nat(v___x_671_);
v___x_682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(v_as_664_, v___x_680_, v___x_681_, v___x_672_, v_a_665_, v_a_666_, v_a_667_, v_a_668_);
return v___x_682_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs___boxed(lean_object* v_as_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_IR_Checker_checkArgs(v_as_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_);
lean_dec(v_a_687_);
lean_dec_ref(v_a_686_);
lean_dec(v_a_685_);
lean_dec_ref(v_a_684_);
lean_dec_ref(v_as_683_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes(lean_object* v_ty_u2081_691_, lean_object* v_ty_u2082_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_){
_start:
{
uint8_t v___x_698_; 
v___x_698_ = l_Lean_IR_instBEqIRType_beq(v_ty_u2081_691_, v_ty_u2082_692_);
if (v___x_698_ == 0)
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = ((lean_object*)(l_Lean_IR_Checker_checkEqTypes___closed__0));
v___x_700_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_699_, v_a_693_, v_a_694_, v_a_695_, v_a_696_);
return v___x_700_;
}
else
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = lean_box(0);
v___x_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_702_, 0, v___x_701_);
return v___x_702_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes___boxed(lean_object* v_ty_u2081_703_, lean_object* v_ty_u2082_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Lean_IR_Checker_checkEqTypes(v_ty_u2081_703_, v_ty_u2082_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
lean_dec(v_a_708_);
lean_dec_ref(v_a_707_);
lean_dec(v_a_706_);
lean_dec_ref(v_a_705_);
lean_dec(v_ty_u2082_704_);
lean_dec(v_ty_u2081_703_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType(lean_object* v_ty_713_, lean_object* v_p_714_, lean_object* v_suffix_x3f_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_){
_start:
{
lean_object* v___x_721_; uint8_t v___x_722_; 
lean_inc(v_ty_713_);
v___x_721_ = lean_apply_1(v_p_714_, v_ty_713_);
v___x_722_ = lean_unbox(v___x_721_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v_msg_730_; 
v___x_723_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_724_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_713_);
v___x_725_ = l_Std_Format_defWidth;
v___x_726_ = lean_unsigned_to_nat(0u);
v___x_727_ = l_Std_Format_pretty(v___x_724_, v___x_725_, v___x_726_, v___x_726_);
v___x_728_ = lean_string_append(v___x_723_, v___x_727_);
lean_dec_ref(v___x_727_);
v___x_729_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_730_ = lean_string_append(v___x_728_, v___x_729_);
if (lean_obj_tag(v_suffix_x3f_715_) == 1)
{
lean_object* v_val_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v_msg_734_; lean_object* v___x_735_; 
v_val_731_ = lean_ctor_get(v_suffix_x3f_715_, 0);
v___x_732_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_733_ = lean_string_append(v_msg_730_, v___x_732_);
v_msg_734_ = lean_string_append(v___x_733_, v_val_731_);
v___x_735_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_734_, v_a_716_, v_a_717_, v_a_718_, v_a_719_);
return v___x_735_;
}
else
{
lean_object* v___x_736_; 
v___x_736_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_730_, v_a_716_, v_a_717_, v_a_718_, v_a_719_);
return v___x_736_;
}
}
else
{
lean_object* v___x_737_; lean_object* v___x_738_; 
lean_dec(v_ty_713_);
v___x_737_ = lean_box(0);
v___x_738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
return v___x_738_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType___boxed(lean_object* v_ty_739_, lean_object* v_p_740_, lean_object* v_suffix_x3f_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lean_IR_Checker_checkType(v_ty_739_, v_p_740_, v_suffix_x3f_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_);
lean_dec(v_a_745_);
lean_dec_ref(v_a_744_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
lean_dec(v_suffix_x3f_741_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType(lean_object* v_ty_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_){
_start:
{
uint8_t v___x_755_; 
v___x_755_ = l_Lean_IR_IRType_isObj(v_ty_749_);
if (v___x_755_ == 0)
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v_msg_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v_msg_767_; lean_object* v___x_768_; 
v___x_756_ = ((lean_object*)(l_Lean_IR_Checker_checkObjType___closed__0));
v___x_757_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_758_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_749_);
v___x_759_ = l_Std_Format_defWidth;
v___x_760_ = lean_unsigned_to_nat(0u);
v___x_761_ = l_Std_Format_pretty(v___x_758_, v___x_759_, v___x_760_, v___x_760_);
v___x_762_ = lean_string_append(v___x_757_, v___x_761_);
lean_dec_ref(v___x_761_);
v___x_763_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_764_ = lean_string_append(v___x_762_, v___x_763_);
v___x_765_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_766_ = lean_string_append(v_msg_764_, v___x_765_);
v_msg_767_ = lean_string_append(v___x_766_, v___x_756_);
v___x_768_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_767_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
return v___x_768_;
}
else
{
lean_object* v___x_769_; lean_object* v___x_770_; 
lean_dec(v_ty_749_);
v___x_769_ = lean_box(0);
v___x_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
return v___x_770_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType___boxed(lean_object* v_ty_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lean_IR_Checker_checkObjType(v_ty_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_);
lean_dec(v_a_775_);
lean_dec_ref(v_a_774_);
lean_dec(v_a_773_);
lean_dec_ref(v_a_772_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType(lean_object* v_ty_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_){
_start:
{
uint8_t v___x_785_; 
v___x_785_ = l_Lean_IR_IRType_isScalar(v_ty_779_);
if (v___x_785_ == 0)
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v_msg_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v_msg_797_; lean_object* v___x_798_; 
v___x_786_ = ((lean_object*)(l_Lean_IR_Checker_checkScalarType___closed__0));
v___x_787_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_788_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_779_);
v___x_789_ = l_Std_Format_defWidth;
v___x_790_ = lean_unsigned_to_nat(0u);
v___x_791_ = l_Std_Format_pretty(v___x_788_, v___x_789_, v___x_790_, v___x_790_);
v___x_792_ = lean_string_append(v___x_787_, v___x_791_);
lean_dec_ref(v___x_791_);
v___x_793_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_794_ = lean_string_append(v___x_792_, v___x_793_);
v___x_795_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_796_ = lean_string_append(v_msg_794_, v___x_795_);
v_msg_797_ = lean_string_append(v___x_796_, v___x_786_);
v___x_798_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_797_, v_a_780_, v_a_781_, v_a_782_, v_a_783_);
return v___x_798_;
}
else
{
lean_object* v___x_799_; lean_object* v___x_800_; 
lean_dec(v_ty_779_);
v___x_799_ = lean_box(0);
v___x_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
return v___x_800_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType___boxed(lean_object* v_ty_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Lean_IR_Checker_checkScalarType(v_ty_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType(lean_object* v_x_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_){
_start:
{
lean_object* v_localCtx_814_; lean_object* v___x_815_; 
v_localCtx_814_ = lean_ctor_get(v_a_809_, 0);
v___x_815_ = l_Lean_IR_LocalContext_getType(v_localCtx_814_, v_x_808_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_816_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__0));
v___x_817_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__1));
v___x_818_ = l_Nat_reprFast(v_x_808_);
v___x_819_ = lean_string_append(v___x_817_, v___x_818_);
lean_dec_ref(v___x_818_);
v___x_820_ = lean_string_append(v___x_816_, v___x_819_);
lean_dec_ref(v___x_819_);
v___x_821_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v___x_822_ = lean_string_append(v___x_820_, v___x_821_);
v___x_823_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_822_, v_a_809_, v_a_810_, v_a_811_, v_a_812_);
return v___x_823_;
}
else
{
lean_object* v_val_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_831_; 
lean_dec(v_x_808_);
v_val_824_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_831_ == 0)
{
v___x_826_ = v___x_815_;
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_val_824_);
lean_dec(v___x_815_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
lean_ctor_set_tag(v___x_826_, 0);
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_val_824_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType___boxed(lean_object* v_x_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Lean_IR_Checker_getType(v_x_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_);
lean_dec(v_a_836_);
lean_dec_ref(v_a_835_);
lean_dec(v_a_834_);
lean_dec_ref(v_a_833_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType(lean_object* v_x_839_, lean_object* v_p_840_, lean_object* v_suffix_x3f_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_Lean_IR_Checker_getType(v_x_839_, v_a_842_, v_a_843_, v_a_844_, v_a_845_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_872_; 
v_a_848_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_872_ == 0)
{
v___x_850_ = v___x_847_;
v_isShared_851_ = v_isSharedCheck_872_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_847_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_872_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_852_; uint8_t v___x_853_; 
lean_inc(v_a_848_);
v___x_852_ = lean_apply_1(v_p_840_, v_a_848_);
v___x_853_ = lean_unbox(v___x_852_);
if (v___x_853_ == 0)
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v_msg_861_; 
lean_del_object(v___x_850_);
v___x_854_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_855_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_848_);
v___x_856_ = l_Std_Format_defWidth;
v___x_857_ = lean_unsigned_to_nat(0u);
v___x_858_ = l_Std_Format_pretty(v___x_855_, v___x_856_, v___x_857_, v___x_857_);
v___x_859_ = lean_string_append(v___x_854_, v___x_858_);
lean_dec_ref(v___x_858_);
v___x_860_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_861_ = lean_string_append(v___x_859_, v___x_860_);
if (lean_obj_tag(v_suffix_x3f_841_) == 1)
{
lean_object* v_val_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v_msg_865_; lean_object* v___x_866_; 
v_val_862_ = lean_ctor_get(v_suffix_x3f_841_, 0);
v___x_863_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_864_ = lean_string_append(v_msg_861_, v___x_863_);
v_msg_865_ = lean_string_append(v___x_864_, v_val_862_);
v___x_866_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_865_, v_a_842_, v_a_843_, v_a_844_, v_a_845_);
return v___x_866_;
}
else
{
lean_object* v___x_867_; 
v___x_867_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_861_, v_a_842_, v_a_843_, v_a_844_, v_a_845_);
return v___x_867_;
}
}
else
{
lean_object* v___x_868_; lean_object* v___x_870_; 
lean_dec(v_a_848_);
v___x_868_ = lean_box(0);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 0, v___x_868_);
v___x_870_ = v___x_850_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_868_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
else
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
lean_dec_ref(v_p_840_);
v_a_873_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_880_ == 0)
{
v___x_875_ = v___x_847_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_847_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_873_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType___boxed(lean_object* v_x_881_, lean_object* v_p_882_, lean_object* v_suffix_x3f_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Lean_IR_Checker_checkVarType(v_x_881_, v_p_882_, v_suffix_x3f_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_);
lean_dec(v_a_887_);
lean_dec_ref(v_a_886_);
lean_dec(v_a_885_);
lean_dec_ref(v_a_884_);
lean_dec(v_suffix_x3f_883_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar(lean_object* v_x_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l_Lean_IR_Checker_getType(v_x_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_919_; 
v_a_897_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_919_ == 0)
{
v___x_899_ = v___x_896_;
v_isShared_900_ = v_isSharedCheck_919_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_896_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_919_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
uint8_t v___x_901_; 
v___x_901_ = l_Lean_IR_IRType_isObj(v_a_897_);
if (v___x_901_ == 0)
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v_msg_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v_msg_913_; lean_object* v___x_914_; 
lean_del_object(v___x_899_);
v___x_902_ = ((lean_object*)(l_Lean_IR_Checker_checkObjType___closed__0));
v___x_903_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_904_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_897_);
v___x_905_ = l_Std_Format_defWidth;
v___x_906_ = lean_unsigned_to_nat(0u);
v___x_907_ = l_Std_Format_pretty(v___x_904_, v___x_905_, v___x_906_, v___x_906_);
v___x_908_ = lean_string_append(v___x_903_, v___x_907_);
lean_dec_ref(v___x_907_);
v___x_909_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_910_ = lean_string_append(v___x_908_, v___x_909_);
v___x_911_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_912_ = lean_string_append(v_msg_910_, v___x_911_);
v_msg_913_ = lean_string_append(v___x_912_, v___x_902_);
v___x_914_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_913_, v_a_891_, v_a_892_, v_a_893_, v_a_894_);
return v___x_914_;
}
else
{
lean_object* v___x_915_; lean_object* v___x_917_; 
lean_dec(v_a_897_);
v___x_915_ = lean_box(0);
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 0, v___x_915_);
v___x_917_ = v___x_899_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v___x_915_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
else
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_927_; 
v_a_920_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_927_ == 0)
{
v___x_922_ = v___x_896_;
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_896_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_920_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar___boxed(lean_object* v_x_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Lean_IR_Checker_checkObjVar(v_x_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar(lean_object* v_x_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l_Lean_IR_Checker_getType(v_x_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_964_; 
v_a_942_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_964_ == 0)
{
v___x_944_ = v___x_941_;
v_isShared_945_ = v_isSharedCheck_964_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_941_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_964_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
uint8_t v___x_946_; 
v___x_946_ = l_Lean_IR_IRType_isScalar(v_a_942_);
if (v___x_946_ == 0)
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v_msg_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v_msg_958_; lean_object* v___x_959_; 
lean_del_object(v___x_944_);
v___x_947_ = ((lean_object*)(l_Lean_IR_Checker_checkScalarType___closed__0));
v___x_948_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_949_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_942_);
v___x_950_ = l_Std_Format_defWidth;
v___x_951_ = lean_unsigned_to_nat(0u);
v___x_952_ = l_Std_Format_pretty(v___x_949_, v___x_950_, v___x_951_, v___x_951_);
v___x_953_ = lean_string_append(v___x_948_, v___x_952_);
lean_dec_ref(v___x_952_);
v___x_954_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_955_ = lean_string_append(v___x_953_, v___x_954_);
v___x_956_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_957_ = lean_string_append(v_msg_955_, v___x_956_);
v_msg_958_ = lean_string_append(v___x_957_, v___x_947_);
v___x_959_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_958_, v_a_936_, v_a_937_, v_a_938_, v_a_939_);
return v___x_959_;
}
else
{
lean_object* v___x_960_; lean_object* v___x_962_; 
lean_dec(v_a_942_);
v___x_960_ = lean_box(0);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 0, v___x_960_);
v___x_962_ = v___x_944_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v___x_960_);
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
else
{
lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_972_; 
v_a_965_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_972_ == 0)
{
v___x_967_ = v___x_941_;
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v___x_941_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_970_; 
if (v_isShared_968_ == 0)
{
v___x_970_ = v___x_967_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_a_965_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar___boxed(lean_object* v_x_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_IR_Checker_checkScalarVar(v_x_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_);
lean_dec(v_a_977_);
lean_dec_ref(v_a_976_);
lean_dec(v_a_975_);
lean_dec_ref(v_a_974_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp(lean_object* v_c_984_, lean_object* v_ys_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_){
_start:
{
lean_object* v___x_991_; 
lean_inc(v_c_984_);
v___x_991_ = l_Lean_IR_Checker_getDecl(v_c_984_, v_a_986_, v_a_987_, v_a_988_, v_a_989_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v_a_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; uint8_t v___x_996_; 
v_a_992_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_a_992_);
lean_dec_ref(v___x_991_);
v___x_993_ = lean_array_get_size(v_ys_985_);
v___x_994_ = l_Lean_IR_Decl_params(v_a_992_);
lean_dec(v_a_992_);
v___x_995_ = lean_array_get_size(v___x_994_);
lean_dec_ref(v___x_994_);
v___x_996_ = lean_nat_dec_eq(v___x_993_, v___x_995_);
if (v___x_996_ == 0)
{
lean_object* v___x_997_; uint8_t v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_997_ = ((lean_object*)(l_Lean_IR_Checker_checkFullApp___closed__0));
v___x_998_ = 1;
v___x_999_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_c_984_, v___x_998_);
v___x_1000_ = lean_string_append(v___x_997_, v___x_999_);
lean_dec_ref(v___x_999_);
v___x_1001_ = ((lean_object*)(l_Lean_IR_Checker_checkFullApp___closed__1));
v___x_1002_ = lean_string_append(v___x_1000_, v___x_1001_);
v___x_1003_ = l_Nat_reprFast(v___x_993_);
v___x_1004_ = lean_string_append(v___x_1002_, v___x_1003_);
lean_dec_ref(v___x_1003_);
v___x_1005_ = ((lean_object*)(l_Lean_IR_Checker_checkFullApp___closed__2));
v___x_1006_ = lean_string_append(v___x_1004_, v___x_1005_);
v___x_1007_ = l_Nat_reprFast(v___x_995_);
v___x_1008_ = lean_string_append(v___x_1006_, v___x_1007_);
lean_dec_ref(v___x_1007_);
v___x_1009_ = ((lean_object*)(l_Lean_IR_Checker_checkFullApp___closed__3));
v___x_1010_ = lean_string_append(v___x_1008_, v___x_1009_);
v___x_1011_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1010_, v_a_986_, v_a_987_, v_a_988_, v_a_989_);
return v___x_1011_;
}
else
{
lean_object* v___x_1012_; 
lean_dec(v_c_984_);
v___x_1012_ = l_Lean_IR_Checker_checkArgs(v_ys_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_);
return v___x_1012_;
}
}
else
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
lean_dec(v_c_984_);
v_a_1013_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_991_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_991_);
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
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp___boxed(lean_object* v_c_1021_, lean_object* v_ys_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_Lean_IR_Checker_checkFullApp(v_c_1021_, v_ys_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_);
lean_dec(v_a_1026_);
lean_dec_ref(v_a_1025_);
lean_dec(v_a_1024_);
lean_dec_ref(v_a_1023_);
lean_dec_ref(v_ys_1022_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp(lean_object* v_c_1032_, lean_object* v_ys_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v___x_1039_; 
lean_inc(v_c_1032_);
v___x_1039_ = l_Lean_IR_Checker_getDecl(v_c_1032_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v_a_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; uint8_t v___x_1044_; 
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
lean_inc(v_a_1040_);
lean_dec_ref(v___x_1039_);
v___x_1041_ = lean_array_get_size(v_ys_1033_);
v___x_1042_ = l_Lean_IR_Decl_params(v_a_1040_);
lean_dec(v_a_1040_);
v___x_1043_ = lean_array_get_size(v___x_1042_);
lean_dec_ref(v___x_1042_);
v___x_1044_ = lean_nat_dec_lt(v___x_1041_, v___x_1043_);
if (v___x_1044_ == 0)
{
lean_object* v___x_1045_; uint8_t v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1045_ = ((lean_object*)(l_Lean_IR_Checker_checkPartialApp___closed__0));
v___x_1046_ = 1;
v___x_1047_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_c_1032_, v___x_1046_);
v___x_1048_ = lean_string_append(v___x_1045_, v___x_1047_);
lean_dec_ref(v___x_1047_);
v___x_1049_ = ((lean_object*)(l_Lean_IR_Checker_checkPartialApp___closed__1));
v___x_1050_ = lean_string_append(v___x_1048_, v___x_1049_);
v___x_1051_ = l_Nat_reprFast(v___x_1041_);
v___x_1052_ = lean_string_append(v___x_1050_, v___x_1051_);
lean_dec_ref(v___x_1051_);
v___x_1053_ = ((lean_object*)(l_Lean_IR_Checker_checkPartialApp___closed__2));
v___x_1054_ = lean_string_append(v___x_1052_, v___x_1053_);
v___x_1055_ = l_Nat_reprFast(v___x_1043_);
v___x_1056_ = lean_string_append(v___x_1054_, v___x_1055_);
lean_dec_ref(v___x_1055_);
v___x_1057_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1056_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_);
return v___x_1057_;
}
else
{
lean_object* v___x_1058_; 
lean_dec(v_c_1032_);
v___x_1058_ = l_Lean_IR_Checker_checkArgs(v_ys_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_);
return v___x_1058_;
}
}
else
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1066_; 
lean_dec(v_c_1032_);
v_a_1059_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1061_ = v___x_1039_;
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1039_);
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
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp___boxed(lean_object* v_c_1067_, lean_object* v_ys_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Lean_IR_Checker_checkPartialApp(v_c_1067_, v_ys_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_);
lean_dec(v_a_1072_);
lean_dec_ref(v_a_1071_);
lean_dec(v_a_1070_);
lean_dec_ref(v_a_1069_);
lean_dec_ref(v_ys_1068_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr(lean_object* v_ty_1082_, lean_object* v_e_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_){
_start:
{
switch(lean_obj_tag(v_e_1083_))
{
case 0:
{
lean_object* v_i_1089_; lean_object* v_ys_1090_; lean_object* v___y_1092_; lean_object* v___y_1093_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v_name_1101_; lean_object* v_cidx_1102_; lean_object* v_size_1103_; lean_object* v_usize_1104_; lean_object* v_ssize_1105_; lean_object* v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1126_; uint8_t v___y_1136_; lean_object* v___x_1143_; uint8_t v___x_1144_; 
v_i_1089_ = lean_ctor_get(v_e_1083_, 0);
lean_inc_ref(v_i_1089_);
v_ys_1090_ = lean_ctor_get(v_e_1083_, 1);
lean_inc_ref(v_ys_1090_);
lean_dec_ref(v_e_1083_);
v_name_1101_ = lean_ctor_get(v_i_1089_, 0);
v_cidx_1102_ = lean_ctor_get(v_i_1089_, 1);
v_size_1103_ = lean_ctor_get(v_i_1089_, 2);
v_usize_1104_ = lean_ctor_get(v_i_1089_, 3);
v_ssize_1105_ = lean_ctor_get(v_i_1089_, 4);
v___x_1143_ = l_Lean_IR_Checker_maxCtorTag;
v___x_1144_ = lean_nat_dec_lt(v___x_1143_, v_cidx_1102_);
if (v___x_1144_ == 0)
{
v___y_1136_ = v___x_1144_;
goto v___jp_1135_;
}
else
{
uint8_t v___x_1145_; 
v___x_1145_ = l_Lean_IR_CtorInfo_isRef(v_i_1089_);
v___y_1136_ = v___x_1145_;
goto v___jp_1135_;
}
v___jp_1091_:
{
uint8_t v___x_1096_; 
v___x_1096_ = l_Lean_IR_CtorInfo_isRef(v_i_1089_);
lean_dec_ref(v_i_1089_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
lean_dec_ref(v_ys_1090_);
lean_dec(v_ty_1082_);
v___x_1097_ = lean_box(0);
v___x_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
return v___x_1098_;
}
else
{
lean_object* v___x_1099_; 
v___x_1099_ = l_Lean_IR_Checker_checkObjType(v_ty_1082_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v___x_1100_; 
lean_dec_ref(v___x_1099_);
v___x_1100_ = l_Lean_IR_Checker_checkArgs(v_ys_1090_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
lean_dec_ref(v_ys_1090_);
return v___x_1100_;
}
else
{
lean_dec_ref(v_ys_1090_);
return v___x_1099_;
}
}
}
v___jp_1106_:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; uint8_t v___x_1115_; 
v___x_1111_ = l_Lean_IR_Checker_maxCtorScalarsSize;
v___x_1112_ = l_Lean_IR_Checker_usizeSize;
v___x_1113_ = lean_nat_mul(v_usize_1104_, v___x_1112_);
v___x_1114_ = lean_nat_add(v_ssize_1105_, v___x_1113_);
lean_dec(v___x_1113_);
v___x_1115_ = lean_nat_dec_lt(v___x_1111_, v___x_1114_);
lean_dec(v___x_1114_);
if (v___x_1115_ == 0)
{
v___y_1092_ = v___y_1107_;
v___y_1093_ = v___y_1108_;
v___y_1094_ = v___y_1109_;
v___y_1095_ = v___y_1110_;
goto v___jp_1091_;
}
else
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
lean_inc(v_name_1101_);
lean_dec_ref(v_ys_1090_);
lean_dec_ref(v_i_1089_);
lean_dec(v_ty_1082_);
v___x_1116_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__0));
v___x_1117_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1101_, v___x_1115_);
v___x_1118_ = lean_string_append(v___x_1116_, v___x_1117_);
lean_dec_ref(v___x_1117_);
v___x_1119_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__1));
v___x_1120_ = lean_string_append(v___x_1118_, v___x_1119_);
v___x_1121_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1120_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_);
return v___x_1121_;
}
}
v___jp_1122_:
{
lean_object* v___x_1127_; uint8_t v___x_1128_; 
v___x_1127_ = l_Lean_IR_Checker_maxCtorFields;
v___x_1128_ = lean_nat_dec_lt(v___x_1127_, v_size_1103_);
if (v___x_1128_ == 0)
{
v___y_1107_ = v___y_1123_;
v___y_1108_ = v___y_1124_;
v___y_1109_ = v___y_1125_;
v___y_1110_ = v___y_1126_;
goto v___jp_1106_;
}
else
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
lean_inc(v_name_1101_);
lean_dec_ref(v_ys_1090_);
lean_dec_ref(v_i_1089_);
lean_dec(v_ty_1082_);
v___x_1129_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__0));
v___x_1130_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1101_, v___x_1128_);
v___x_1131_ = lean_string_append(v___x_1129_, v___x_1130_);
lean_dec_ref(v___x_1130_);
v___x_1132_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__2));
v___x_1133_ = lean_string_append(v___x_1131_, v___x_1132_);
v___x_1134_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1133_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
return v___x_1134_;
}
}
v___jp_1135_:
{
if (v___y_1136_ == 0)
{
v___y_1123_ = v_a_1084_;
v___y_1124_ = v_a_1085_;
v___y_1125_ = v_a_1086_;
v___y_1126_ = v_a_1087_;
goto v___jp_1122_;
}
else
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
lean_inc(v_name_1101_);
lean_dec_ref(v_ys_1090_);
lean_dec_ref(v_i_1089_);
lean_dec(v_ty_1082_);
v___x_1137_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__3));
v___x_1138_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1101_, v___y_1136_);
v___x_1139_ = lean_string_append(v___x_1137_, v___x_1138_);
lean_dec_ref(v___x_1138_);
v___x_1140_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__4));
v___x_1141_ = lean_string_append(v___x_1139_, v___x_1140_);
v___x_1142_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1141_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
return v___x_1142_;
}
}
}
case 1:
{
lean_object* v_x_1146_; lean_object* v___x_1147_; 
v_x_1146_ = lean_ctor_get(v_e_1083_, 1);
lean_inc(v_x_1146_);
lean_dec_ref(v_e_1083_);
v___x_1147_ = l_Lean_IR_Checker_checkObjVar(v_x_1146_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v___x_1148_; 
lean_dec_ref(v___x_1147_);
v___x_1148_ = l_Lean_IR_Checker_checkObjType(v_ty_1082_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
return v___x_1148_;
}
else
{
lean_dec(v_ty_1082_);
return v___x_1147_;
}
}
case 2:
{
lean_object* v_x_1149_; lean_object* v_ys_1150_; lean_object* v___x_1151_; 
v_x_1149_ = lean_ctor_get(v_e_1083_, 0);
lean_inc(v_x_1149_);
v_ys_1150_ = lean_ctor_get(v_e_1083_, 2);
lean_inc_ref(v_ys_1150_);
lean_dec_ref(v_e_1083_);
v___x_1151_ = l_Lean_IR_Checker_checkObjVar(v_x_1149_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v___x_1152_; 
lean_dec_ref(v___x_1151_);
v___x_1152_ = l_Lean_IR_Checker_checkArgs(v_ys_1150_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
lean_dec_ref(v_ys_1150_);
if (lean_obj_tag(v___x_1152_) == 0)
{
lean_object* v___x_1153_; 
lean_dec_ref(v___x_1152_);
v___x_1153_ = l_Lean_IR_Checker_checkObjType(v_ty_1082_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
return v___x_1153_;
}
else
{
lean_dec(v_ty_1082_);
return v___x_1152_;
}
}
else
{
lean_dec_ref(v_ys_1150_);
lean_dec(v_ty_1082_);
return v___x_1151_;
}
}
case 3:
{
lean_object* v_i_1154_; lean_object* v_x_1155_; lean_object* v___x_1156_; 
v_i_1154_ = lean_ctor_get(v_e_1083_, 0);
lean_inc(v_i_1154_);
v_x_1155_ = lean_ctor_get(v_e_1083_, 1);
lean_inc(v_x_1155_);
lean_dec_ref(v_e_1083_);
v___x_1156_ = l_Lean_IR_Checker_getType(v_x_1155_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1202_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1159_ = v___x_1156_;
v_isShared_1160_ = v_isSharedCheck_1202_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1156_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1202_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
switch(lean_obj_tag(v_a_1157_))
{
case 7:
{
lean_object* v___x_1161_; 
lean_del_object(v___x_1159_);
lean_dec(v_i_1154_);
v___x_1161_ = l_Lean_IR_Checker_checkObjType(v_ty_1082_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
return v___x_1161_;
}
case 8:
{
lean_object* v___x_1162_; 
lean_del_object(v___x_1159_);
lean_dec(v_i_1154_);
v___x_1162_ = l_Lean_IR_Checker_checkObjType(v_ty_1082_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
return v___x_1162_;
}
case 10:
{
lean_object* v_types_1163_; lean_object* v___x_1164_; uint8_t v___x_1165_; 
v_types_1163_ = lean_ctor_get(v_a_1157_, 1);
lean_inc_ref(v_types_1163_);
lean_dec_ref(v_a_1157_);
v___x_1164_ = lean_array_get_size(v_types_1163_);
v___x_1165_ = lean_nat_dec_lt(v_i_1154_, v___x_1164_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
lean_dec_ref(v_types_1163_);
lean_del_object(v___x_1159_);
lean_dec(v_i_1154_);
lean_dec(v_ty_1082_);
v___x_1166_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__5));
v___x_1167_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1166_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
return v___x_1167_;
}
else
{
lean_object* v___x_1168_; uint8_t v___x_1169_; 
v___x_1168_ = lean_array_fget(v_types_1163_, v_i_1154_);
lean_dec(v_i_1154_);
lean_dec_ref(v_types_1163_);
v___x_1169_ = l_Lean_IR_instBEqIRType_beq(v___x_1168_, v_ty_1082_);
lean_dec(v_ty_1082_);
lean_dec(v___x_1168_);
if (v___x_1169_ == 0)
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
lean_del_object(v___x_1159_);
v___x_1170_ = ((lean_object*)(l_Lean_IR_Checker_checkEqTypes___closed__0));
v___x_1171_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1170_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
return v___x_1171_;
}
else
{
lean_object* v___x_1172_; lean_object* v___x_1174_; 
v___x_1172_ = lean_box(0);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v___x_1172_);
v___x_1174_ = v___x_1159_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v___x_1172_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
}
case 11:
{
lean_object* v_types_1176_; lean_object* v___x_1177_; uint8_t v___x_1178_; 
v_types_1176_ = lean_ctor_get(v_a_1157_, 1);
lean_inc_ref(v_types_1176_);
lean_dec_ref(v_a_1157_);
v___x_1177_ = lean_array_get_size(v_types_1176_);
v___x_1178_ = lean_nat_dec_lt(v_i_1154_, v___x_1177_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
lean_dec_ref(v_types_1176_);
lean_del_object(v___x_1159_);
lean_dec(v_i_1154_);
lean_dec(v_ty_1082_);
v___x_1179_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__5));
v___x_1180_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1179_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
return v___x_1180_;
}
else
{
lean_object* v___x_1181_; uint8_t v___x_1182_; 
v___x_1181_ = lean_array_fget(v_types_1176_, v_i_1154_);
lean_dec(v_i_1154_);
lean_dec_ref(v_types_1176_);
v___x_1182_ = l_Lean_IR_instBEqIRType_beq(v___x_1181_, v_ty_1082_);
lean_dec(v_ty_1082_);
lean_dec(v___x_1181_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; lean_object* v___x_1184_; 
lean_del_object(v___x_1159_);
v___x_1183_ = ((lean_object*)(l_Lean_IR_Checker_checkEqTypes___closed__0));
v___x_1184_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1183_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
return v___x_1184_;
}
else
{
lean_object* v___x_1185_; lean_object* v___x_1187_; 
v___x_1185_ = lean_box(0);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v___x_1185_);
v___x_1187_ = v___x_1159_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1185_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
case 12:
{
lean_object* v___x_1189_; lean_object* v___x_1191_; 
lean_dec(v_i_1154_);
lean_dec(v_ty_1082_);
v___x_1189_ = lean_box(0);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v___x_1189_);
v___x_1191_ = v___x_1159_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1189_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
default: 
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
lean_del_object(v___x_1159_);
lean_dec(v_i_1154_);
lean_dec(v_ty_1082_);
v___x_1193_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__6));
v___x_1194_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_1157_);
v___x_1195_ = l_Std_Format_defWidth;
v___x_1196_ = lean_unsigned_to_nat(0u);
v___x_1197_ = l_Std_Format_pretty(v___x_1194_, v___x_1195_, v___x_1196_, v___x_1196_);
v___x_1198_ = lean_string_append(v___x_1193_, v___x_1197_);
lean_dec_ref(v___x_1197_);
v___x_1199_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v___x_1200_ = lean_string_append(v___x_1198_, v___x_1199_);
v___x_1201_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1200_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
return v___x_1201_;
}
}
}
}
else
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
lean_dec(v_i_1154_);
lean_dec(v_ty_1082_);
v_a_1203_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1205_ = v___x_1156_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1156_);
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
case 4:
{
lean_object* v_x_1211_; lean_object* v___x_1212_; 
v_x_1211_ = lean_ctor_get(v_e_1083_, 1);
lean_inc(v_x_1211_);
lean_dec_ref(v_e_1083_);
v___x_1212_ = l_Lean_IR_Checker_checkObjVar(v_x_1211_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1231_; 
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1231_ == 0)
{
lean_object* v_unused_1232_; 
v_unused_1232_ = lean_ctor_get(v___x_1212_, 0);
lean_dec(v_unused_1232_);
v___x_1214_ = v___x_1212_;
v_isShared_1215_ = v_isSharedCheck_1231_;
goto v_resetjp_1213_;
}
else
{
lean_dec(v___x_1212_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1231_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1216_; uint8_t v___x_1217_; 
v___x_1216_ = lean_box(5);
v___x_1217_ = l_Lean_IR_instBEqIRType_beq(v_ty_1082_, v___x_1216_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v_msg_1225_; lean_object* v___x_1226_; 
lean_del_object(v___x_1214_);
v___x_1218_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_1219_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_1082_);
v___x_1220_ = l_Std_Format_defWidth;
v___x_1221_ = lean_unsigned_to_nat(0u);
v___x_1222_ = l_Std_Format_pretty(v___x_1219_, v___x_1220_, v___x_1221_, v___x_1221_);
v___x_1223_ = lean_string_append(v___x_1218_, v___x_1222_);
lean_dec_ref(v___x_1222_);
v___x_1224_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_1225_ = lean_string_append(v___x_1223_, v___x_1224_);
v___x_1226_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_1225_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
return v___x_1226_;
}
else
{
lean_object* v___x_1227_; lean_object* v___x_1229_; 
lean_dec(v_ty_1082_);
v___x_1227_ = lean_box(0);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 0, v___x_1227_);
v___x_1229_ = v___x_1214_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1227_);
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
lean_dec(v_ty_1082_);
return v___x_1212_;
}
}
case 5:
{
lean_object* v_x_1233_; lean_object* v___x_1234_; 
v_x_1233_ = lean_ctor_get(v_e_1083_, 2);
lean_inc(v_x_1233_);
lean_dec_ref(v_e_1083_);
v___x_1234_ = l_Lean_IR_Checker_checkObjVar(v_x_1233_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v___x_1235_; 
lean_dec_ref(v___x_1234_);
v___x_1235_ = l_Lean_IR_Checker_checkScalarType(v_ty_1082_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
return v___x_1235_;
}
else
{
lean_dec(v_ty_1082_);
return v___x_1234_;
}
}
case 6:
{
lean_object* v_c_1236_; lean_object* v_ys_1237_; lean_object* v___x_1238_; 
lean_dec(v_ty_1082_);
v_c_1236_ = lean_ctor_get(v_e_1083_, 0);
lean_inc(v_c_1236_);
v_ys_1237_ = lean_ctor_get(v_e_1083_, 1);
lean_inc_ref(v_ys_1237_);
lean_dec_ref(v_e_1083_);
v___x_1238_ = l_Lean_IR_Checker_checkFullApp(v_c_1236_, v_ys_1237_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
lean_dec_ref(v_ys_1237_);
return v___x_1238_;
}
case 7:
{
lean_object* v_c_1239_; lean_object* v_ys_1240_; lean_object* v___x_1241_; 
v_c_1239_ = lean_ctor_get(v_e_1083_, 0);
lean_inc(v_c_1239_);
v_ys_1240_ = lean_ctor_get(v_e_1083_, 1);
lean_inc_ref(v_ys_1240_);
lean_dec_ref(v_e_1083_);
v___x_1241_ = l_Lean_IR_Checker_checkPartialApp(v_c_1239_, v_ys_1240_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
lean_dec_ref(v_ys_1240_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v___x_1242_; 
lean_dec_ref(v___x_1241_);
v___x_1242_ = l_Lean_IR_Checker_checkObjType(v_ty_1082_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
return v___x_1242_;
}
else
{
lean_dec(v_ty_1082_);
return v___x_1241_;
}
}
case 8:
{
lean_object* v_x_1243_; lean_object* v_ys_1244_; lean_object* v___x_1245_; 
v_x_1243_ = lean_ctor_get(v_e_1083_, 0);
lean_inc(v_x_1243_);
v_ys_1244_ = lean_ctor_get(v_e_1083_, 1);
lean_inc_ref(v_ys_1244_);
lean_dec_ref(v_e_1083_);
v___x_1245_ = l_Lean_IR_Checker_checkObjVar(v_x_1243_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v___x_1246_; 
lean_dec_ref(v___x_1245_);
v___x_1246_ = l_Lean_IR_Checker_checkArgs(v_ys_1244_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
lean_dec_ref(v_ys_1244_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v___x_1247_; 
lean_dec_ref(v___x_1246_);
v___x_1247_ = l_Lean_IR_Checker_checkObjType(v_ty_1082_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
return v___x_1247_;
}
else
{
lean_dec(v_ty_1082_);
return v___x_1246_;
}
}
else
{
lean_dec_ref(v_ys_1244_);
lean_dec(v_ty_1082_);
return v___x_1245_;
}
}
case 9:
{
lean_object* v_ty_1248_; lean_object* v_x_1249_; lean_object* v___x_1250_; 
v_ty_1248_ = lean_ctor_get(v_e_1083_, 0);
lean_inc(v_ty_1248_);
v_x_1249_ = lean_ctor_get(v_e_1083_, 1);
lean_inc(v_x_1249_);
lean_dec_ref(v_e_1083_);
v___x_1250_ = l_Lean_IR_Checker_checkObjType(v_ty_1082_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_object* v___x_1251_; 
lean_dec_ref(v___x_1250_);
lean_inc(v_x_1249_);
v___x_1251_ = l_Lean_IR_Checker_checkScalarVar(v_x_1249_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v___x_1252_; 
lean_dec_ref(v___x_1251_);
v___x_1252_ = l_Lean_IR_Checker_getType(v_x_1249_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_object* v_a_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1271_; 
v_a_1253_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1255_ = v___x_1252_;
v_isShared_1256_ = v_isSharedCheck_1271_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_a_1253_);
lean_dec(v___x_1252_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1271_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
uint8_t v___x_1257_; 
v___x_1257_ = l_Lean_IR_instBEqIRType_beq(v_a_1253_, v_ty_1248_);
lean_dec(v_ty_1248_);
if (v___x_1257_ == 0)
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v_msg_1265_; lean_object* v___x_1266_; 
lean_del_object(v___x_1255_);
v___x_1258_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_1259_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_1253_);
v___x_1260_ = l_Std_Format_defWidth;
v___x_1261_ = lean_unsigned_to_nat(0u);
v___x_1262_ = l_Std_Format_pretty(v___x_1259_, v___x_1260_, v___x_1261_, v___x_1261_);
v___x_1263_ = lean_string_append(v___x_1258_, v___x_1262_);
lean_dec_ref(v___x_1262_);
v___x_1264_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_1265_ = lean_string_append(v___x_1263_, v___x_1264_);
v___x_1266_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_1265_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
return v___x_1266_;
}
else
{
lean_object* v___x_1267_; lean_object* v___x_1269_; 
lean_dec(v_a_1253_);
v___x_1267_ = lean_box(0);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 0, v___x_1267_);
v___x_1269_ = v___x_1255_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1267_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
else
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1279_; 
lean_dec(v_ty_1248_);
v_a_1272_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1274_ = v___x_1252_;
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1252_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1275_ == 0)
{
v___x_1277_ = v___x_1274_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_a_1272_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
else
{
lean_dec(v_x_1249_);
lean_dec(v_ty_1248_);
return v___x_1251_;
}
}
else
{
lean_dec(v_x_1249_);
lean_dec(v_ty_1248_);
return v___x_1250_;
}
}
case 10:
{
lean_object* v_x_1280_; lean_object* v___x_1281_; 
v_x_1280_ = lean_ctor_get(v_e_1083_, 0);
lean_inc(v_x_1280_);
lean_dec_ref(v_e_1083_);
v___x_1281_ = l_Lean_IR_Checker_checkScalarType(v_ty_1082_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v___x_1282_; 
lean_dec_ref(v___x_1281_);
v___x_1282_ = l_Lean_IR_Checker_checkObjVar(v_x_1280_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
return v___x_1282_;
}
else
{
lean_dec(v_x_1280_);
return v___x_1281_;
}
}
case 11:
{
lean_object* v_v_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1292_; 
v_v_1283_ = lean_ctor_get(v_e_1083_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v_e_1083_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1285_ = v_e_1083_;
v_isShared_1286_ = v_isSharedCheck_1292_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_v_1283_);
lean_dec(v_e_1083_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1292_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
if (lean_obj_tag(v_v_1283_) == 1)
{
lean_object* v___x_1287_; 
lean_dec_ref(v_v_1283_);
lean_del_object(v___x_1285_);
v___x_1287_ = l_Lean_IR_Checker_checkObjType(v_ty_1082_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
return v___x_1287_;
}
else
{
lean_object* v___x_1288_; lean_object* v___x_1290_; 
lean_dec_ref(v_v_1283_);
lean_dec(v_ty_1082_);
v___x_1288_ = lean_box(0);
if (v_isShared_1286_ == 0)
{
lean_ctor_set_tag(v___x_1285_, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1288_);
v___x_1290_ = v___x_1285_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1288_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
default: 
{
lean_object* v_x_1293_; lean_object* v___x_1294_; 
v_x_1293_ = lean_ctor_get(v_e_1083_, 0);
lean_inc(v_x_1293_);
lean_dec_ref(v_e_1083_);
v___x_1294_ = l_Lean_IR_Checker_checkObjVar(v_x_1293_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
if (lean_obj_tag(v___x_1294_) == 0)
{
lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1313_; 
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1313_ == 0)
{
lean_object* v_unused_1314_; 
v_unused_1314_ = lean_ctor_get(v___x_1294_, 0);
lean_dec(v_unused_1314_);
v___x_1296_ = v___x_1294_;
v_isShared_1297_ = v_isSharedCheck_1313_;
goto v_resetjp_1295_;
}
else
{
lean_dec(v___x_1294_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1313_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1298_; uint8_t v___x_1299_; 
v___x_1298_ = lean_box(1);
v___x_1299_ = l_Lean_IR_instBEqIRType_beq(v_ty_1082_, v___x_1298_);
if (v___x_1299_ == 0)
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v_msg_1307_; lean_object* v___x_1308_; 
lean_del_object(v___x_1296_);
v___x_1300_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_1301_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_1082_);
v___x_1302_ = l_Std_Format_defWidth;
v___x_1303_ = lean_unsigned_to_nat(0u);
v___x_1304_ = l_Std_Format_pretty(v___x_1301_, v___x_1302_, v___x_1303_, v___x_1303_);
v___x_1305_ = lean_string_append(v___x_1300_, v___x_1304_);
lean_dec_ref(v___x_1304_);
v___x_1306_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_1307_ = lean_string_append(v___x_1305_, v___x_1306_);
v___x_1308_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_1307_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
return v___x_1308_;
}
else
{
lean_object* v___x_1309_; lean_object* v___x_1311_; 
lean_dec(v_ty_1082_);
v___x_1309_ = lean_box(0);
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 0, v___x_1309_);
v___x_1311_ = v___x_1296_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1309_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
}
else
{
lean_dec(v_ty_1082_);
return v___x_1294_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___boxed(lean_object* v_ty_1315_, lean_object* v_e_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l_Lean_IR_Checker_checkExpr(v_ty_1315_, v_e_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
lean_dec(v_a_1318_);
lean_dec_ref(v_a_1317_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__0(lean_object* v_ctx_1323_, lean_object* v_p_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
lean_object* v_x_1330_; lean_object* v___x_1331_; 
v_x_1330_ = lean_ctor_get(v_p_1324_, 0);
lean_inc(v_x_1330_);
v___x_1331_ = l_Lean_IR_Checker_markIndex(v_x_1330_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1339_; 
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1339_ == 0)
{
lean_object* v_unused_1340_; 
v_unused_1340_ = lean_ctor_get(v___x_1331_, 0);
lean_dec(v_unused_1340_);
v___x_1333_ = v___x_1331_;
v_isShared_1334_ = v_isSharedCheck_1339_;
goto v_resetjp_1332_;
}
else
{
lean_dec(v___x_1331_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1339_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1335_; lean_object* v___x_1337_; 
v___x_1335_ = l_Lean_IR_LocalContext_addParam(v_ctx_1323_, v_p_1324_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 0, v___x_1335_);
v___x_1337_ = v___x_1333_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v___x_1335_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
else
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
lean_dec_ref(v_p_1324_);
lean_dec(v_ctx_1323_);
v_a_1341_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1343_ = v___x_1331_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1331_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1346_; 
if (v_isShared_1344_ == 0)
{
v___x_1346_ = v___x_1343_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1341_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__0___boxed(lean_object* v_ctx_1349_, lean_object* v_p_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l_Lean_IR_Checker_withParams___lam__0(v_ctx_1349_, v_p_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
return v_res_1356_;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__0(void){
_start:
{
lean_object* v___x_1357_; 
v___x_1357_ = l_instMonadEIO(lean_box(0));
return v___x_1357_;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__1(void){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1358_ = lean_obj_once(&l_Lean_IR_Checker_withParams___closed__0, &l_Lean_IR_Checker_withParams___closed__0_once, _init_l_Lean_IR_Checker_withParams___closed__0);
v___x_1359_ = l_StateRefT_x27_instMonad___redArg(v___x_1358_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams(lean_object* v_ps_1363_, lean_object* v_k_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_){
_start:
{
lean_object* v___x_1370_; lean_object* v_toApplicative_1371_; lean_object* v_toFunctor_1372_; lean_object* v_toSeq_1373_; lean_object* v_toSeqLeft_1374_; lean_object* v_toSeqRight_1375_; lean_object* v___f_1376_; lean_object* v___f_1377_; lean_object* v___f_1378_; lean_object* v___f_1379_; lean_object* v___x_1380_; lean_object* v___f_1381_; lean_object* v___f_1382_; lean_object* v___f_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v_localCtx_1388_; lean_object* v_currentDecl_1389_; lean_object* v_decls_1390_; lean_object* v_a_1392_; lean_object* v___y_1396_; lean_object* v___x_1406_; lean_object* v___x_1407_; uint8_t v___x_1408_; 
v___x_1370_ = lean_obj_once(&l_Lean_IR_Checker_withParams___closed__1, &l_Lean_IR_Checker_withParams___closed__1_once, _init_l_Lean_IR_Checker_withParams___closed__1);
v_toApplicative_1371_ = lean_ctor_get(v___x_1370_, 0);
v_toFunctor_1372_ = lean_ctor_get(v_toApplicative_1371_, 0);
v_toSeq_1373_ = lean_ctor_get(v_toApplicative_1371_, 2);
v_toSeqLeft_1374_ = lean_ctor_get(v_toApplicative_1371_, 3);
v_toSeqRight_1375_ = lean_ctor_get(v_toApplicative_1371_, 4);
v___f_1376_ = ((lean_object*)(l_Lean_IR_Checker_withParams___closed__2));
v___f_1377_ = ((lean_object*)(l_Lean_IR_Checker_withParams___closed__3));
lean_inc_ref_n(v_toFunctor_1372_, 2);
v___f_1378_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1378_, 0, v_toFunctor_1372_);
v___f_1379_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1379_, 0, v_toFunctor_1372_);
v___x_1380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1380_, 0, v___f_1378_);
lean_ctor_set(v___x_1380_, 1, v___f_1379_);
lean_inc(v_toSeqRight_1375_);
v___f_1381_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1381_, 0, v_toSeqRight_1375_);
lean_inc(v_toSeqLeft_1374_);
v___f_1382_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1382_, 0, v_toSeqLeft_1374_);
lean_inc(v_toSeq_1373_);
v___f_1383_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1383_, 0, v_toSeq_1373_);
v___x_1384_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1380_);
lean_ctor_set(v___x_1384_, 1, v___f_1376_);
lean_ctor_set(v___x_1384_, 2, v___f_1383_);
lean_ctor_set(v___x_1384_, 3, v___f_1382_);
lean_ctor_set(v___x_1384_, 4, v___f_1381_);
v___x_1385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1384_);
lean_ctor_set(v___x_1385_, 1, v___f_1377_);
v___x_1386_ = l_StateRefT_x27_instMonad___redArg(v___x_1385_);
v___x_1387_ = l_ReaderT_instMonad___redArg(v___x_1386_);
v_localCtx_1388_ = lean_ctor_get(v_a_1365_, 0);
v_currentDecl_1389_ = lean_ctor_get(v_a_1365_, 1);
v_decls_1390_ = lean_ctor_get(v_a_1365_, 2);
v___x_1406_ = lean_unsigned_to_nat(0u);
v___x_1407_ = lean_array_get_size(v_ps_1363_);
v___x_1408_ = lean_nat_dec_lt(v___x_1406_, v___x_1407_);
if (v___x_1408_ == 0)
{
lean_dec_ref(v___x_1387_);
lean_dec_ref(v_ps_1363_);
lean_inc(v_localCtx_1388_);
v_a_1392_ = v_localCtx_1388_;
goto v___jp_1391_;
}
else
{
lean_object* v___f_1409_; uint8_t v___x_1410_; 
v___f_1409_ = ((lean_object*)(l_Lean_IR_Checker_withParams___closed__4));
v___x_1410_ = lean_nat_dec_le(v___x_1407_, v___x_1407_);
if (v___x_1410_ == 0)
{
if (v___x_1408_ == 0)
{
lean_dec_ref(v___x_1387_);
lean_dec_ref(v_ps_1363_);
lean_inc(v_localCtx_1388_);
v_a_1392_ = v_localCtx_1388_;
goto v___jp_1391_;
}
else
{
size_t v___x_1411_; size_t v___x_1412_; lean_object* v___x_1045__overap_1413_; lean_object* v___x_1414_; 
v___x_1411_ = ((size_t)0ULL);
v___x_1412_ = lean_usize_of_nat(v___x_1407_);
lean_inc(v_localCtx_1388_);
v___x_1045__overap_1413_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1387_, v___f_1409_, v_ps_1363_, v___x_1411_, v___x_1412_, v_localCtx_1388_);
lean_inc(v_a_1368_);
lean_inc_ref(v_a_1367_);
lean_inc(v_a_1366_);
lean_inc_ref(v_a_1365_);
v___x_1414_ = lean_apply_5(v___x_1045__overap_1413_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, lean_box(0));
v___y_1396_ = v___x_1414_;
goto v___jp_1395_;
}
}
else
{
size_t v___x_1415_; size_t v___x_1416_; lean_object* v___x_1050__overap_1417_; lean_object* v___x_1418_; 
v___x_1415_ = ((size_t)0ULL);
v___x_1416_ = lean_usize_of_nat(v___x_1407_);
lean_inc(v_localCtx_1388_);
v___x_1050__overap_1417_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1387_, v___f_1409_, v_ps_1363_, v___x_1415_, v___x_1416_, v_localCtx_1388_);
lean_inc(v_a_1368_);
lean_inc_ref(v_a_1367_);
lean_inc(v_a_1366_);
lean_inc_ref(v_a_1365_);
v___x_1418_ = lean_apply_5(v___x_1050__overap_1417_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, lean_box(0));
v___y_1396_ = v___x_1418_;
goto v___jp_1395_;
}
}
v___jp_1391_:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; 
lean_inc_ref(v_decls_1390_);
lean_inc_ref(v_currentDecl_1389_);
v___x_1393_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1393_, 0, v_a_1392_);
lean_ctor_set(v___x_1393_, 1, v_currentDecl_1389_);
lean_ctor_set(v___x_1393_, 2, v_decls_1390_);
lean_inc(v_a_1368_);
lean_inc_ref(v_a_1367_);
lean_inc(v_a_1366_);
v___x_1394_ = lean_apply_5(v_k_1364_, v___x_1393_, v_a_1366_, v_a_1367_, v_a_1368_, lean_box(0));
return v___x_1394_;
}
v___jp_1395_:
{
if (lean_obj_tag(v___y_1396_) == 0)
{
lean_object* v_a_1397_; 
v_a_1397_ = lean_ctor_get(v___y_1396_, 0);
lean_inc(v_a_1397_);
lean_dec_ref(v___y_1396_);
v_a_1392_ = v_a_1397_;
goto v___jp_1391_;
}
else
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1405_; 
lean_dec_ref(v_k_1364_);
v_a_1398_ = lean_ctor_get(v___y_1396_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___y_1396_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1400_ = v___y_1396_;
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___y_1396_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1403_; 
if (v_isShared_1401_ == 0)
{
v___x_1403_ = v___x_1400_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_a_1398_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___boxed(lean_object* v_ps_1419_, lean_object* v_k_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_Lean_IR_Checker_withParams(v_ps_1419_, v_k_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_);
lean_dec(v_a_1424_);
lean_dec_ref(v_a_1423_);
lean_dec(v_a_1422_);
lean_dec_ref(v_a_1421_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(lean_object* v_as_1427_, size_t v_i_1428_, size_t v_stop_1429_, lean_object* v_b_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
uint8_t v___x_1436_; 
v___x_1436_ = lean_usize_dec_eq(v_i_1428_, v_stop_1429_);
if (v___x_1436_ == 0)
{
lean_object* v___x_1437_; lean_object* v_x_1438_; lean_object* v___x_1439_; 
v___x_1437_ = lean_array_uget_borrowed(v_as_1427_, v_i_1428_);
v_x_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc(v_x_1438_);
v___x_1439_ = l_Lean_IR_Checker_markIndex(v_x_1438_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v___x_1440_; size_t v___x_1441_; size_t v___x_1442_; 
lean_dec_ref(v___x_1439_);
lean_inc(v___x_1437_);
v___x_1440_ = l_Lean_IR_LocalContext_addParam(v_b_1430_, v___x_1437_);
v___x_1441_ = ((size_t)1ULL);
v___x_1442_ = lean_usize_add(v_i_1428_, v___x_1441_);
v_i_1428_ = v___x_1442_;
v_b_1430_ = v___x_1440_;
goto _start;
}
else
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1451_; 
lean_dec(v_b_1430_);
v_a_1444_ = lean_ctor_get(v___x_1439_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1446_ = v___x_1439_;
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___x_1439_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1449_; 
if (v_isShared_1447_ == 0)
{
v___x_1449_ = v___x_1446_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_a_1444_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
}
else
{
lean_object* v___x_1452_; 
v___x_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1452_, 0, v_b_1430_);
return v___x_1452_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0___boxed(lean_object* v_as_1453_, lean_object* v_i_1454_, lean_object* v_stop_1455_, lean_object* v_b_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
size_t v_i_boxed_1462_; size_t v_stop_boxed_1463_; lean_object* v_res_1464_; 
v_i_boxed_1462_ = lean_unbox_usize(v_i_1454_);
lean_dec(v_i_1454_);
v_stop_boxed_1463_ = lean_unbox_usize(v_stop_1455_);
lean_dec(v_stop_1455_);
v_res_1464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_as_1453_, v_i_boxed_1462_, v_stop_boxed_1463_, v_b_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec_ref(v_as_1453_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFnBody(lean_object* v_fnBody_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_){
_start:
{
lean_object* v_x_1472_; lean_object* v_b_1473_; lean_object* v___y_1474_; lean_object* v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1477_; 
switch(lean_obj_tag(v_fnBody_1465_))
{
case 0:
{
lean_object* v_x_1480_; lean_object* v_ty_1481_; lean_object* v_e_1482_; lean_object* v_b_1483_; lean_object* v___x_1484_; 
v_x_1480_ = lean_ctor_get(v_fnBody_1465_, 0);
lean_inc(v_x_1480_);
v_ty_1481_ = lean_ctor_get(v_fnBody_1465_, 1);
lean_inc_n(v_ty_1481_, 2);
v_e_1482_ = lean_ctor_get(v_fnBody_1465_, 2);
lean_inc_ref_n(v_e_1482_, 2);
v_b_1483_ = lean_ctor_get(v_fnBody_1465_, 3);
lean_inc(v_b_1483_);
lean_dec_ref(v_fnBody_1465_);
v___x_1484_ = l_Lean_IR_Checker_checkExpr(v_ty_1481_, v_e_1482_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v___x_1485_; 
lean_dec_ref(v___x_1484_);
lean_inc(v_x_1480_);
v___x_1485_ = l_Lean_IR_Checker_markIndex(v_x_1480_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_localCtx_1486_; lean_object* v_currentDecl_1487_; lean_object* v_decls_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
lean_dec_ref(v___x_1485_);
v_localCtx_1486_ = lean_ctor_get(v_a_1466_, 0);
lean_inc(v_localCtx_1486_);
v_currentDecl_1487_ = lean_ctor_get(v_a_1466_, 1);
lean_inc_ref(v_currentDecl_1487_);
v_decls_1488_ = lean_ctor_get(v_a_1466_, 2);
lean_inc_ref(v_decls_1488_);
lean_dec_ref(v_a_1466_);
v___x_1489_ = l_Lean_IR_LocalContext_addLocal(v_localCtx_1486_, v_x_1480_, v_ty_1481_, v_e_1482_);
v___x_1490_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1489_);
lean_ctor_set(v___x_1490_, 1, v_currentDecl_1487_);
lean_ctor_set(v___x_1490_, 2, v_decls_1488_);
v_fnBody_1465_ = v_b_1483_;
v_a_1466_ = v___x_1490_;
goto _start;
}
else
{
lean_dec(v_b_1483_);
lean_dec_ref(v_e_1482_);
lean_dec(v_ty_1481_);
lean_dec(v_x_1480_);
lean_dec_ref(v_a_1466_);
return v___x_1485_;
}
}
else
{
lean_dec(v_b_1483_);
lean_dec_ref(v_e_1482_);
lean_dec(v_ty_1481_);
lean_dec(v_x_1480_);
lean_dec_ref(v_a_1466_);
return v___x_1484_;
}
}
case 1:
{
lean_object* v_j_1492_; lean_object* v_xs_1493_; lean_object* v_v_1494_; lean_object* v_b_1495_; lean_object* v___x_1496_; 
v_j_1492_ = lean_ctor_get(v_fnBody_1465_, 0);
lean_inc_n(v_j_1492_, 2);
v_xs_1493_ = lean_ctor_get(v_fnBody_1465_, 1);
lean_inc_ref(v_xs_1493_);
v_v_1494_ = lean_ctor_get(v_fnBody_1465_, 2);
lean_inc(v_v_1494_);
v_b_1495_ = lean_ctor_get(v_fnBody_1465_, 3);
lean_inc(v_b_1495_);
lean_dec_ref(v_fnBody_1465_);
v___x_1496_ = l_Lean_IR_Checker_markIndex(v_j_1492_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_localCtx_1497_; lean_object* v_currentDecl_1498_; lean_object* v_decls_1499_; lean_object* v_a_1501_; lean_object* v___y_1508_; lean_object* v___x_1518_; lean_object* v___x_1519_; uint8_t v___x_1520_; 
lean_dec_ref(v___x_1496_);
v_localCtx_1497_ = lean_ctor_get(v_a_1466_, 0);
lean_inc(v_localCtx_1497_);
v_currentDecl_1498_ = lean_ctor_get(v_a_1466_, 1);
lean_inc_ref(v_currentDecl_1498_);
v_decls_1499_ = lean_ctor_get(v_a_1466_, 2);
lean_inc_ref(v_decls_1499_);
v___x_1518_ = lean_unsigned_to_nat(0u);
v___x_1519_ = lean_array_get_size(v_xs_1493_);
v___x_1520_ = lean_nat_dec_lt(v___x_1518_, v___x_1519_);
if (v___x_1520_ == 0)
{
lean_dec_ref(v_a_1466_);
lean_inc(v_localCtx_1497_);
v_a_1501_ = v_localCtx_1497_;
goto v___jp_1500_;
}
else
{
uint8_t v___x_1521_; 
v___x_1521_ = lean_nat_dec_le(v___x_1519_, v___x_1519_);
if (v___x_1521_ == 0)
{
if (v___x_1520_ == 0)
{
lean_dec_ref(v_a_1466_);
lean_inc(v_localCtx_1497_);
v_a_1501_ = v_localCtx_1497_;
goto v___jp_1500_;
}
else
{
size_t v___x_1522_; size_t v___x_1523_; lean_object* v___x_1524_; 
v___x_1522_ = ((size_t)0ULL);
v___x_1523_ = lean_usize_of_nat(v___x_1519_);
lean_inc(v_localCtx_1497_);
v___x_1524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_xs_1493_, v___x_1522_, v___x_1523_, v_localCtx_1497_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_);
lean_dec_ref(v_a_1466_);
v___y_1508_ = v___x_1524_;
goto v___jp_1507_;
}
}
else
{
size_t v___x_1525_; size_t v___x_1526_; lean_object* v___x_1527_; 
v___x_1525_ = ((size_t)0ULL);
v___x_1526_ = lean_usize_of_nat(v___x_1519_);
lean_inc(v_localCtx_1497_);
v___x_1527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_xs_1493_, v___x_1525_, v___x_1526_, v_localCtx_1497_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_);
lean_dec_ref(v_a_1466_);
v___y_1508_ = v___x_1527_;
goto v___jp_1507_;
}
}
v___jp_1500_:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
lean_inc_ref(v_decls_1499_);
lean_inc_ref(v_currentDecl_1498_);
v___x_1502_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1502_, 0, v_a_1501_);
lean_ctor_set(v___x_1502_, 1, v_currentDecl_1498_);
lean_ctor_set(v___x_1502_, 2, v_decls_1499_);
lean_inc(v_v_1494_);
v___x_1503_ = l_Lean_IR_Checker_checkFnBody(v_v_1494_, v___x_1502_, v_a_1467_, v_a_1468_, v_a_1469_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v___x_1504_; lean_object* v___x_1505_; 
lean_dec_ref(v___x_1503_);
v___x_1504_ = l_Lean_IR_LocalContext_addJP(v_localCtx_1497_, v_j_1492_, v_xs_1493_, v_v_1494_);
v___x_1505_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1504_);
lean_ctor_set(v___x_1505_, 1, v_currentDecl_1498_);
lean_ctor_set(v___x_1505_, 2, v_decls_1499_);
v_fnBody_1465_ = v_b_1495_;
v_a_1466_ = v___x_1505_;
goto _start;
}
else
{
lean_dec_ref(v_decls_1499_);
lean_dec_ref(v_currentDecl_1498_);
lean_dec(v_localCtx_1497_);
lean_dec(v_b_1495_);
lean_dec(v_v_1494_);
lean_dec_ref(v_xs_1493_);
lean_dec(v_j_1492_);
return v___x_1503_;
}
}
v___jp_1507_:
{
if (lean_obj_tag(v___y_1508_) == 0)
{
lean_object* v_a_1509_; 
v_a_1509_ = lean_ctor_get(v___y_1508_, 0);
lean_inc(v_a_1509_);
lean_dec_ref(v___y_1508_);
v_a_1501_ = v_a_1509_;
goto v___jp_1500_;
}
else
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1517_; 
lean_dec_ref(v_decls_1499_);
lean_dec_ref(v_currentDecl_1498_);
lean_dec(v_localCtx_1497_);
lean_dec(v_b_1495_);
lean_dec(v_v_1494_);
lean_dec_ref(v_xs_1493_);
lean_dec(v_j_1492_);
v_a_1510_ = lean_ctor_get(v___y_1508_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___y_1508_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1512_ = v___y_1508_;
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___y_1508_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1513_ == 0)
{
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1510_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
}
else
{
lean_dec(v_b_1495_);
lean_dec(v_v_1494_);
lean_dec_ref(v_xs_1493_);
lean_dec(v_j_1492_);
lean_dec_ref(v_a_1466_);
return v___x_1496_;
}
}
case 2:
{
lean_object* v_x_1528_; lean_object* v_y_1529_; lean_object* v_b_1530_; lean_object* v___x_1531_; 
v_x_1528_ = lean_ctor_get(v_fnBody_1465_, 0);
lean_inc(v_x_1528_);
v_y_1529_ = lean_ctor_get(v_fnBody_1465_, 2);
lean_inc(v_y_1529_);
v_b_1530_ = lean_ctor_get(v_fnBody_1465_, 3);
lean_inc(v_b_1530_);
lean_dec_ref(v_fnBody_1465_);
v___x_1531_ = l_Lean_IR_Checker_checkVar(v_x_1528_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v___x_1532_; 
lean_dec_ref(v___x_1531_);
v___x_1532_ = l_Lean_IR_Checker_checkArg(v_y_1529_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_dec_ref(v___x_1532_);
v_fnBody_1465_ = v_b_1530_;
goto _start;
}
else
{
lean_dec(v_b_1530_);
lean_dec_ref(v_a_1466_);
return v___x_1532_;
}
}
else
{
lean_dec(v_b_1530_);
lean_dec(v_y_1529_);
lean_dec_ref(v_a_1466_);
return v___x_1531_;
}
}
case 3:
{
lean_object* v_x_1534_; lean_object* v_b_1535_; lean_object* v___x_1536_; 
v_x_1534_ = lean_ctor_get(v_fnBody_1465_, 0);
lean_inc(v_x_1534_);
v_b_1535_ = lean_ctor_get(v_fnBody_1465_, 2);
lean_inc(v_b_1535_);
lean_dec_ref(v_fnBody_1465_);
v___x_1536_ = l_Lean_IR_Checker_checkVar(v_x_1534_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_dec_ref(v___x_1536_);
v_fnBody_1465_ = v_b_1535_;
goto _start;
}
else
{
lean_dec(v_b_1535_);
lean_dec_ref(v_a_1466_);
return v___x_1536_;
}
}
case 4:
{
lean_object* v_x_1538_; lean_object* v_y_1539_; lean_object* v_b_1540_; lean_object* v___x_1541_; 
v_x_1538_ = lean_ctor_get(v_fnBody_1465_, 0);
lean_inc(v_x_1538_);
v_y_1539_ = lean_ctor_get(v_fnBody_1465_, 2);
lean_inc(v_y_1539_);
v_b_1540_ = lean_ctor_get(v_fnBody_1465_, 3);
lean_inc(v_b_1540_);
lean_dec_ref(v_fnBody_1465_);
v___x_1541_ = l_Lean_IR_Checker_checkVar(v_x_1538_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v___x_1542_; 
lean_dec_ref(v___x_1541_);
v___x_1542_ = l_Lean_IR_Checker_checkVar(v_y_1539_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_dec_ref(v___x_1542_);
v_fnBody_1465_ = v_b_1540_;
goto _start;
}
else
{
lean_dec(v_b_1540_);
lean_dec_ref(v_a_1466_);
return v___x_1542_;
}
}
else
{
lean_dec(v_b_1540_);
lean_dec(v_y_1539_);
lean_dec_ref(v_a_1466_);
return v___x_1541_;
}
}
case 5:
{
lean_object* v_x_1544_; lean_object* v_y_1545_; lean_object* v_b_1546_; lean_object* v___x_1547_; 
v_x_1544_ = lean_ctor_get(v_fnBody_1465_, 0);
lean_inc(v_x_1544_);
v_y_1545_ = lean_ctor_get(v_fnBody_1465_, 3);
lean_inc(v_y_1545_);
v_b_1546_ = lean_ctor_get(v_fnBody_1465_, 5);
lean_inc(v_b_1546_);
lean_dec_ref(v_fnBody_1465_);
v___x_1547_ = l_Lean_IR_Checker_checkVar(v_x_1544_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v___x_1548_; 
lean_dec_ref(v___x_1547_);
v___x_1548_ = l_Lean_IR_Checker_checkVar(v_y_1545_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_dec_ref(v___x_1548_);
v_fnBody_1465_ = v_b_1546_;
goto _start;
}
else
{
lean_dec(v_b_1546_);
lean_dec_ref(v_a_1466_);
return v___x_1548_;
}
}
else
{
lean_dec(v_b_1546_);
lean_dec(v_y_1545_);
lean_dec_ref(v_a_1466_);
return v___x_1547_;
}
}
case 8:
{
lean_object* v_x_1550_; lean_object* v_b_1551_; lean_object* v___x_1552_; 
v_x_1550_ = lean_ctor_get(v_fnBody_1465_, 0);
lean_inc(v_x_1550_);
v_b_1551_ = lean_ctor_get(v_fnBody_1465_, 1);
lean_inc(v_b_1551_);
lean_dec_ref(v_fnBody_1465_);
v___x_1552_ = l_Lean_IR_Checker_checkVar(v_x_1550_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_dec_ref(v___x_1552_);
v_fnBody_1465_ = v_b_1551_;
goto _start;
}
else
{
lean_dec(v_b_1551_);
lean_dec_ref(v_a_1466_);
return v___x_1552_;
}
}
case 9:
{
lean_object* v_x_1554_; lean_object* v_cs_1555_; lean_object* v___x_1556_; 
v_x_1554_ = lean_ctor_get(v_fnBody_1465_, 1);
lean_inc(v_x_1554_);
v_cs_1555_ = lean_ctor_get(v_fnBody_1465_, 3);
lean_inc_ref(v_cs_1555_);
lean_dec_ref(v_fnBody_1465_);
v___x_1556_ = l_Lean_IR_Checker_checkVar(v_x_1554_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1577_; 
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1577_ == 0)
{
lean_object* v_unused_1578_; 
v_unused_1578_ = lean_ctor_get(v___x_1556_, 0);
lean_dec(v_unused_1578_);
v___x_1558_ = v___x_1556_;
v_isShared_1559_ = v_isSharedCheck_1577_;
goto v_resetjp_1557_;
}
else
{
lean_dec(v___x_1556_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1577_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; uint8_t v___x_1563_; 
v___x_1560_ = lean_unsigned_to_nat(0u);
v___x_1561_ = lean_array_get_size(v_cs_1555_);
v___x_1562_ = lean_box(0);
v___x_1563_ = lean_nat_dec_lt(v___x_1560_, v___x_1561_);
if (v___x_1563_ == 0)
{
lean_object* v___x_1565_; 
lean_dec_ref(v_cs_1555_);
lean_dec_ref(v_a_1466_);
if (v_isShared_1559_ == 0)
{
lean_ctor_set(v___x_1558_, 0, v___x_1562_);
v___x_1565_ = v___x_1558_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1562_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
else
{
uint8_t v___x_1567_; 
v___x_1567_ = lean_nat_dec_le(v___x_1561_, v___x_1561_);
if (v___x_1567_ == 0)
{
if (v___x_1563_ == 0)
{
lean_object* v___x_1569_; 
lean_dec_ref(v_cs_1555_);
lean_dec_ref(v_a_1466_);
if (v_isShared_1559_ == 0)
{
lean_ctor_set(v___x_1558_, 0, v___x_1562_);
v___x_1569_ = v___x_1558_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1562_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
else
{
size_t v___x_1571_; size_t v___x_1572_; lean_object* v___x_1573_; 
lean_del_object(v___x_1558_);
v___x_1571_ = ((size_t)0ULL);
v___x_1572_ = lean_usize_of_nat(v___x_1561_);
v___x_1573_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(v_cs_1555_, v___x_1571_, v___x_1572_, v___x_1562_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_);
lean_dec_ref(v_a_1466_);
lean_dec_ref(v_cs_1555_);
return v___x_1573_;
}
}
else
{
size_t v___x_1574_; size_t v___x_1575_; lean_object* v___x_1576_; 
lean_del_object(v___x_1558_);
v___x_1574_ = ((size_t)0ULL);
v___x_1575_ = lean_usize_of_nat(v___x_1561_);
v___x_1576_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(v_cs_1555_, v___x_1574_, v___x_1575_, v___x_1562_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_);
lean_dec_ref(v_a_1466_);
lean_dec_ref(v_cs_1555_);
return v___x_1576_;
}
}
}
}
else
{
lean_dec_ref(v_cs_1555_);
lean_dec_ref(v_a_1466_);
return v___x_1556_;
}
}
case 10:
{
lean_object* v_x_1579_; lean_object* v___x_1580_; 
v_x_1579_ = lean_ctor_get(v_fnBody_1465_, 0);
lean_inc(v_x_1579_);
lean_dec_ref(v_fnBody_1465_);
v___x_1580_ = l_Lean_IR_Checker_checkArg(v_x_1579_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_);
lean_dec_ref(v_a_1466_);
return v___x_1580_;
}
case 11:
{
lean_object* v_j_1581_; lean_object* v_ys_1582_; lean_object* v___x_1583_; 
v_j_1581_ = lean_ctor_get(v_fnBody_1465_, 0);
lean_inc(v_j_1581_);
v_ys_1582_ = lean_ctor_get(v_fnBody_1465_, 1);
lean_inc_ref(v_ys_1582_);
lean_dec_ref(v_fnBody_1465_);
v___x_1583_ = l_Lean_IR_Checker_checkJP(v_j_1581_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v___x_1584_; 
lean_dec_ref(v___x_1583_);
v___x_1584_ = l_Lean_IR_Checker_checkArgs(v_ys_1582_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_);
lean_dec_ref(v_a_1466_);
lean_dec_ref(v_ys_1582_);
return v___x_1584_;
}
else
{
lean_dec_ref(v_ys_1582_);
lean_dec_ref(v_a_1466_);
return v___x_1583_;
}
}
case 12:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
lean_dec_ref(v_a_1466_);
v___x_1585_ = lean_box(0);
v___x_1586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1585_);
return v___x_1586_;
}
default: 
{
lean_object* v_x_1587_; lean_object* v_b_1588_; 
v_x_1587_ = lean_ctor_get(v_fnBody_1465_, 0);
lean_inc(v_x_1587_);
v_b_1588_ = lean_ctor_get(v_fnBody_1465_, 2);
lean_inc(v_b_1588_);
lean_dec(v_fnBody_1465_);
v_x_1472_ = v_x_1587_;
v_b_1473_ = v_b_1588_;
v___y_1474_ = v_a_1466_;
v___y_1475_ = v_a_1467_;
v___y_1476_ = v_a_1468_;
v___y_1477_ = v_a_1469_;
goto v___jp_1471_;
}
}
v___jp_1471_:
{
lean_object* v___x_1478_; 
v___x_1478_ = l_Lean_IR_Checker_checkVar(v_x_1472_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_dec_ref(v___x_1478_);
v_fnBody_1465_ = v_b_1473_;
v_a_1466_ = v___y_1474_;
v_a_1467_ = v___y_1475_;
v_a_1468_ = v___y_1476_;
v_a_1469_ = v___y_1477_;
goto _start;
}
else
{
lean_dec_ref(v___y_1474_);
lean_dec(v_b_1473_);
return v___x_1478_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(lean_object* v_as_1589_, size_t v_i_1590_, size_t v_stop_1591_, lean_object* v_b_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
uint8_t v___x_1598_; 
v___x_1598_ = lean_usize_dec_eq(v_i_1590_, v_stop_1591_);
if (v___x_1598_ == 0)
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1599_ = lean_array_uget_borrowed(v_as_1589_, v_i_1590_);
v___x_1600_ = l_Lean_IR_Alt_body(v___x_1599_);
lean_inc_ref(v___y_1593_);
v___x_1601_ = l_Lean_IR_Checker_checkFnBody(v___x_1600_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; size_t v___x_1603_; size_t v___x_1604_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_a_1602_);
lean_dec_ref(v___x_1601_);
v___x_1603_ = ((size_t)1ULL);
v___x_1604_ = lean_usize_add(v_i_1590_, v___x_1603_);
v_i_1590_ = v___x_1604_;
v_b_1592_ = v_a_1602_;
goto _start;
}
else
{
return v___x_1601_;
}
}
else
{
lean_object* v___x_1606_; 
v___x_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1606_, 0, v_b_1592_);
return v___x_1606_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1___boxed(lean_object* v_as_1607_, lean_object* v_i_1608_, lean_object* v_stop_1609_, lean_object* v_b_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
size_t v_i_boxed_1616_; size_t v_stop_boxed_1617_; lean_object* v_res_1618_; 
v_i_boxed_1616_ = lean_unbox_usize(v_i_1608_);
lean_dec(v_i_1608_);
v_stop_boxed_1617_ = lean_unbox_usize(v_stop_1609_);
lean_dec(v_stop_1609_);
v_res_1618_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(v_as_1607_, v_i_boxed_1616_, v_stop_boxed_1617_, v_b_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
lean_dec_ref(v_as_1607_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFnBody___boxed(lean_object* v_fnBody_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_Lean_IR_Checker_checkFnBody(v_fnBody_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_);
lean_dec(v_a_1623_);
lean_dec_ref(v_a_1622_);
lean_dec(v_a_1621_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkDecl(lean_object* v_x_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_){
_start:
{
if (lean_obj_tag(v_x_1626_) == 0)
{
lean_object* v_xs_1632_; lean_object* v_body_1633_; lean_object* v_localCtx_1634_; lean_object* v_currentDecl_1635_; lean_object* v_decls_1636_; lean_object* v_a_1638_; lean_object* v___y_1642_; lean_object* v___x_1652_; lean_object* v___x_1653_; uint8_t v___x_1654_; 
v_xs_1632_ = lean_ctor_get(v_x_1626_, 1);
lean_inc_ref(v_xs_1632_);
v_body_1633_ = lean_ctor_get(v_x_1626_, 3);
lean_inc(v_body_1633_);
lean_dec_ref(v_x_1626_);
v_localCtx_1634_ = lean_ctor_get(v_a_1627_, 0);
v_currentDecl_1635_ = lean_ctor_get(v_a_1627_, 1);
v_decls_1636_ = lean_ctor_get(v_a_1627_, 2);
v___x_1652_ = lean_unsigned_to_nat(0u);
v___x_1653_ = lean_array_get_size(v_xs_1632_);
v___x_1654_ = lean_nat_dec_lt(v___x_1652_, v___x_1653_);
if (v___x_1654_ == 0)
{
lean_dec_ref(v_xs_1632_);
lean_inc(v_localCtx_1634_);
v_a_1638_ = v_localCtx_1634_;
goto v___jp_1637_;
}
else
{
uint8_t v___x_1655_; 
v___x_1655_ = lean_nat_dec_le(v___x_1653_, v___x_1653_);
if (v___x_1655_ == 0)
{
if (v___x_1654_ == 0)
{
lean_dec_ref(v_xs_1632_);
lean_inc(v_localCtx_1634_);
v_a_1638_ = v_localCtx_1634_;
goto v___jp_1637_;
}
else
{
size_t v___x_1656_; size_t v___x_1657_; lean_object* v___x_1658_; 
v___x_1656_ = ((size_t)0ULL);
v___x_1657_ = lean_usize_of_nat(v___x_1653_);
lean_inc(v_localCtx_1634_);
v___x_1658_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_xs_1632_, v___x_1656_, v___x_1657_, v_localCtx_1634_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_);
lean_dec_ref(v_xs_1632_);
v___y_1642_ = v___x_1658_;
goto v___jp_1641_;
}
}
else
{
size_t v___x_1659_; size_t v___x_1660_; lean_object* v___x_1661_; 
v___x_1659_ = ((size_t)0ULL);
v___x_1660_ = lean_usize_of_nat(v___x_1653_);
lean_inc(v_localCtx_1634_);
v___x_1661_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_xs_1632_, v___x_1659_, v___x_1660_, v_localCtx_1634_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_);
lean_dec_ref(v_xs_1632_);
v___y_1642_ = v___x_1661_;
goto v___jp_1641_;
}
}
v___jp_1637_:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
lean_inc_ref(v_decls_1636_);
lean_inc_ref(v_currentDecl_1635_);
v___x_1639_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1639_, 0, v_a_1638_);
lean_ctor_set(v___x_1639_, 1, v_currentDecl_1635_);
lean_ctor_set(v___x_1639_, 2, v_decls_1636_);
v___x_1640_ = l_Lean_IR_Checker_checkFnBody(v_body_1633_, v___x_1639_, v_a_1628_, v_a_1629_, v_a_1630_);
return v___x_1640_;
}
v___jp_1641_:
{
if (lean_obj_tag(v___y_1642_) == 0)
{
lean_object* v_a_1643_; 
v_a_1643_ = lean_ctor_get(v___y_1642_, 0);
lean_inc(v_a_1643_);
lean_dec_ref(v___y_1642_);
v_a_1638_ = v_a_1643_;
goto v___jp_1637_;
}
else
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1651_; 
lean_dec(v_body_1633_);
v_a_1644_ = lean_ctor_get(v___y_1642_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___y_1642_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1646_ = v___y_1642_;
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___y_1642_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
if (v_isShared_1647_ == 0)
{
v___x_1649_ = v___x_1646_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1644_);
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
else
{
lean_object* v_xs_1662_; lean_object* v___x_1663_; lean_object* v___y_1665_; lean_object* v___x_1682_; lean_object* v___x_1683_; uint8_t v___x_1684_; 
v_xs_1662_ = lean_ctor_get(v_x_1626_, 1);
lean_inc_ref(v_xs_1662_);
lean_dec_ref(v_x_1626_);
v___x_1663_ = lean_box(0);
v___x_1682_ = lean_unsigned_to_nat(0u);
v___x_1683_ = lean_array_get_size(v_xs_1662_);
v___x_1684_ = lean_nat_dec_lt(v___x_1682_, v___x_1683_);
if (v___x_1684_ == 0)
{
lean_object* v___x_1685_; 
lean_dec_ref(v_xs_1662_);
v___x_1685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1663_);
return v___x_1685_;
}
else
{
lean_object* v_localCtx_1686_; uint8_t v___x_1687_; 
v_localCtx_1686_ = lean_ctor_get(v_a_1627_, 0);
v___x_1687_ = lean_nat_dec_le(v___x_1683_, v___x_1683_);
if (v___x_1687_ == 0)
{
if (v___x_1684_ == 0)
{
lean_object* v___x_1688_; 
lean_dec_ref(v_xs_1662_);
v___x_1688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1663_);
return v___x_1688_;
}
else
{
size_t v___x_1689_; size_t v___x_1690_; lean_object* v___x_1691_; 
v___x_1689_ = ((size_t)0ULL);
v___x_1690_ = lean_usize_of_nat(v___x_1683_);
lean_inc(v_localCtx_1686_);
v___x_1691_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_xs_1662_, v___x_1689_, v___x_1690_, v_localCtx_1686_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_);
lean_dec_ref(v_xs_1662_);
v___y_1665_ = v___x_1691_;
goto v___jp_1664_;
}
}
else
{
size_t v___x_1692_; size_t v___x_1693_; lean_object* v___x_1694_; 
v___x_1692_ = ((size_t)0ULL);
v___x_1693_ = lean_usize_of_nat(v___x_1683_);
lean_inc(v_localCtx_1686_);
v___x_1694_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_xs_1662_, v___x_1692_, v___x_1693_, v_localCtx_1686_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_);
lean_dec_ref(v_xs_1662_);
v___y_1665_ = v___x_1694_;
goto v___jp_1664_;
}
}
v___jp_1664_:
{
if (lean_obj_tag(v___y_1665_) == 0)
{
lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
v_isSharedCheck_1672_ = !lean_is_exclusive(v___y_1665_);
if (v_isSharedCheck_1672_ == 0)
{
lean_object* v_unused_1673_; 
v_unused_1673_ = lean_ctor_get(v___y_1665_, 0);
lean_dec(v_unused_1673_);
v___x_1667_ = v___y_1665_;
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
else
{
lean_dec(v___y_1665_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 0, v___x_1663_);
v___x_1670_ = v___x_1667_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1663_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
else
{
lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1681_; 
v_a_1674_ = lean_ctor_get(v___y_1665_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___y_1665_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1676_ = v___y_1665_;
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_dec(v___y_1665_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkDecl___boxed(lean_object* v_x_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lean_IR_Checker_checkDecl(v_x_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_);
lean_dec(v_a_1699_);
lean_dec_ref(v_a_1698_);
lean_dec(v_a_1697_);
lean_dec_ref(v_a_1696_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl(lean_object* v_decls_1702_, lean_object* v_decl_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_){
_start:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1707_ = lean_box(1);
v___x_1708_ = lean_st_mk_ref(v___x_1707_);
lean_inc_ref(v_decl_1703_);
v___x_1709_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1707_);
lean_ctor_set(v___x_1709_, 1, v_decl_1703_);
lean_ctor_set(v___x_1709_, 2, v_decls_1702_);
v___x_1710_ = l_Lean_IR_Checker_checkDecl(v_decl_1703_, v___x_1709_, v___x_1708_, v_a_1704_, v_a_1705_);
lean_dec_ref(v___x_1709_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1719_; 
v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1713_ = v___x_1710_;
v_isShared_1714_ = v_isSharedCheck_1719_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v___x_1710_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1719_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1715_; lean_object* v___x_1717_; 
v___x_1715_ = lean_st_ref_get(v___x_1708_);
lean_dec(v___x_1708_);
lean_dec(v___x_1715_);
if (v_isShared_1714_ == 0)
{
v___x_1717_ = v___x_1713_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_a_1711_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
else
{
lean_dec(v___x_1708_);
return v___x_1710_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl___boxed(lean_object* v_decls_1720_, lean_object* v_decl_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l_Lean_IR_checkDecl(v_decls_1720_, v_decl_1721_, v_a_1722_, v_a_1723_);
lean_dec(v_a_1723_);
lean_dec_ref(v_a_1722_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(lean_object* v_decls_1726_, lean_object* v_as_1727_, size_t v_i_1728_, size_t v_stop_1729_, lean_object* v_b_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
uint8_t v___x_1734_; 
v___x_1734_ = lean_usize_dec_eq(v_i_1728_, v_stop_1729_);
if (v___x_1734_ == 0)
{
lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1735_ = lean_array_uget_borrowed(v_as_1727_, v_i_1728_);
lean_inc(v___x_1735_);
lean_inc_ref(v_decls_1726_);
v___x_1736_ = l_Lean_IR_checkDecl(v_decls_1726_, v___x_1735_, v___y_1731_, v___y_1732_);
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_object* v_a_1737_; size_t v___x_1738_; size_t v___x_1739_; 
v_a_1737_ = lean_ctor_get(v___x_1736_, 0);
lean_inc(v_a_1737_);
lean_dec_ref(v___x_1736_);
v___x_1738_ = ((size_t)1ULL);
v___x_1739_ = lean_usize_add(v_i_1728_, v___x_1738_);
v_i_1728_ = v___x_1739_;
v_b_1730_ = v_a_1737_;
goto _start;
}
else
{
lean_dec_ref(v_decls_1726_);
return v___x_1736_;
}
}
else
{
lean_object* v___x_1741_; 
lean_dec_ref(v_decls_1726_);
v___x_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1741_, 0, v_b_1730_);
return v___x_1741_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0___boxed(lean_object* v_decls_1742_, lean_object* v_as_1743_, lean_object* v_i_1744_, lean_object* v_stop_1745_, lean_object* v_b_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
size_t v_i_boxed_1750_; size_t v_stop_boxed_1751_; lean_object* v_res_1752_; 
v_i_boxed_1750_ = lean_unbox_usize(v_i_1744_);
lean_dec(v_i_1744_);
v_stop_boxed_1751_ = lean_unbox_usize(v_stop_1745_);
lean_dec(v_stop_1745_);
v_res_1752_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(v_decls_1742_, v_as_1743_, v_i_boxed_1750_, v_stop_boxed_1751_, v_b_1746_, v___y_1747_, v___y_1748_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
lean_dec_ref(v_as_1743_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls(lean_object* v_decls_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_){
_start:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; uint8_t v___x_1760_; 
v___x_1757_ = lean_unsigned_to_nat(0u);
v___x_1758_ = lean_array_get_size(v_decls_1753_);
v___x_1759_ = lean_box(0);
v___x_1760_ = lean_nat_dec_lt(v___x_1757_, v___x_1758_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; 
lean_dec_ref(v_decls_1753_);
v___x_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1759_);
return v___x_1761_;
}
else
{
uint8_t v___x_1762_; 
v___x_1762_ = lean_nat_dec_le(v___x_1758_, v___x_1758_);
if (v___x_1762_ == 0)
{
if (v___x_1760_ == 0)
{
lean_object* v___x_1763_; 
lean_dec_ref(v_decls_1753_);
v___x_1763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1759_);
return v___x_1763_;
}
else
{
size_t v___x_1764_; size_t v___x_1765_; lean_object* v___x_1766_; 
v___x_1764_ = ((size_t)0ULL);
v___x_1765_ = lean_usize_of_nat(v___x_1758_);
lean_inc_ref(v_decls_1753_);
v___x_1766_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(v_decls_1753_, v_decls_1753_, v___x_1764_, v___x_1765_, v___x_1759_, v_a_1754_, v_a_1755_);
lean_dec_ref(v_decls_1753_);
return v___x_1766_;
}
}
else
{
size_t v___x_1767_; size_t v___x_1768_; lean_object* v___x_1769_; 
v___x_1767_ = ((size_t)0ULL);
v___x_1768_ = lean_usize_of_nat(v___x_1758_);
lean_inc_ref(v_decls_1753_);
v___x_1769_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(v_decls_1753_, v_decls_1753_, v___x_1767_, v___x_1768_, v___x_1759_, v_a_1754_, v_a_1755_);
lean_dec_ref(v_decls_1753_);
return v___x_1769_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls___boxed(lean_object* v_decls_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Lean_IR_checkDecls(v_decls_1770_, v_a_1771_, v_a_1772_);
lean_dec(v_a_1772_);
lean_dec_ref(v_a_1771_);
return v_res_1774_;
}
}
lean_object* runtime_initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_IR_Checker(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_IR_CompilerM(builtin);
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
res = initialize_Lean_Compiler_IR_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_Checker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_IR_Checker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_IR_Checker(builtin);
}
#ifdef __cplusplus
}
#endif
