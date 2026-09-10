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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
v___x_30_ = lean_alloc_ctor(0, 11, 0);
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
lean_ctor_set(v___x_30_, 10, v___x_28_);
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
lean_object* v___x_48_; lean_object* v_toCold_49_; lean_object* v_env_50_; lean_object* v_options_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_48_ = lean_st_ref_get(v___y_46_);
v_toCold_49_ = lean_ctor_get(v___y_45_, 0);
v_env_50_ = lean_ctor_get(v___x_48_, 0);
lean_inc_ref(v_env_50_);
lean_dec(v___x_48_);
v_options_51_ = lean_ctor_get(v_toCold_49_, 2);
v___x_52_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__2);
v___x_53_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_51_);
v___x_54_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_54_, 0, v_env_50_);
lean_ctor_set(v___x_54_, 1, v___x_52_);
lean_ctor_set(v___x_54_, 2, v___x_53_);
lean_ctor_set(v___x_54_, 3, v_options_51_);
v___x_55_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
lean_ctor_set(v___x_55_, 1, v_msgData_44_);
v___x_56_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0___boxed(lean_object* v_msgData_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0(v_msgData_57_, v___y_58_, v___y_59_);
lean_dec(v___y_59_);
lean_dec_ref(v___y_58_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___redArg(lean_object* v_msg_62_, lean_object* v___y_63_, lean_object* v___y_64_){
_start:
{
lean_object* v_ref_66_; lean_object* v___x_67_; lean_object* v_a_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_76_; 
v_ref_66_ = lean_ctor_get(v___y_63_, 2);
v___x_67_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0_spec__0(v_msg_62_, v___y_63_, v___y_64_);
v_a_68_ = lean_ctor_get(v___x_67_, 0);
v_isSharedCheck_76_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_76_ == 0)
{
v___x_70_ = v___x_67_;
v_isShared_71_ = v_isSharedCheck_76_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_a_68_);
lean_dec(v___x_67_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_76_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
lean_object* v___x_72_; lean_object* v___x_74_; 
lean_inc(v_ref_66_);
v___x_72_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_72_, 0, v_ref_66_);
lean_ctor_set(v___x_72_, 1, v_a_68_);
if (v_isShared_71_ == 0)
{
lean_ctor_set_tag(v___x_70_, 1);
lean_ctor_set(v___x_70_, 0, v___x_72_);
v___x_74_ = v___x_70_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v___x_72_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
return v___x_74_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___redArg___boxed(lean_object* v_msg_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___redArg(v_msg_77_, v___y_78_, v___y_79_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
return v_res_81_;
}
}
static lean_object* _init_l_Lean_IR_Checker_throwCheckerError___redArg___closed__1(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = ((lean_object*)(l_Lean_IR_Checker_throwCheckerError___redArg___closed__0));
v___x_84_ = l_Lean_stringToMessageData(v___x_83_);
return v___x_84_;
}
}
static lean_object* _init_l_Lean_IR_Checker_throwCheckerError___redArg___closed__3(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = ((lean_object*)(l_Lean_IR_Checker_throwCheckerError___redArg___closed__2));
v___x_87_ = l_Lean_stringToMessageData(v___x_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError___redArg(lean_object* v_msg_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_){
_start:
{
lean_object* v_currentDecl_94_; lean_object* v___x_95_; lean_object* v___x_96_; uint8_t v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v_currentDecl_94_ = lean_ctor_get(v_a_89_, 1);
v___x_95_ = l_Lean_IR_Decl_name(v_currentDecl_94_);
v___x_96_ = lean_obj_once(&l_Lean_IR_Checker_throwCheckerError___redArg___closed__1, &l_Lean_IR_Checker_throwCheckerError___redArg___closed__1_once, _init_l_Lean_IR_Checker_throwCheckerError___redArg___closed__1);
v___x_97_ = 0;
v___x_98_ = l_Lean_MessageData_ofConstName(v___x_95_, v___x_97_);
v___x_99_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_96_);
lean_ctor_set(v___x_99_, 1, v___x_98_);
v___x_100_ = lean_obj_once(&l_Lean_IR_Checker_throwCheckerError___redArg___closed__3, &l_Lean_IR_Checker_throwCheckerError___redArg___closed__3_once, _init_l_Lean_IR_Checker_throwCheckerError___redArg___closed__3);
v___x_101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_99_);
lean_ctor_set(v___x_101_, 1, v___x_100_);
v___x_102_ = l_Lean_stringToMessageData(v_msg_88_);
v___x_103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_101_);
lean_ctor_set(v___x_103_, 1, v___x_102_);
v___x_104_ = l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___redArg(v___x_103_, v_a_91_, v_a_92_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError___redArg___boxed(lean_object* v_msg_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_);
lean_dec(v_a_109_);
lean_dec_ref(v_a_108_);
lean_dec(v_a_107_);
lean_dec_ref(v_a_106_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError(lean_object* v_00_u03b1_112_, lean_object* v_msg_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_113_, v_a_114_, v_a_115_, v_a_116_, v_a_117_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError___boxed(lean_object* v_00_u03b1_120_, lean_object* v_msg_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lean_IR_Checker_throwCheckerError(v_00_u03b1_120_, v_msg_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_);
lean_dec(v_a_125_);
lean_dec_ref(v_a_124_);
lean_dec(v_a_123_);
lean_dec_ref(v_a_122_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0(lean_object* v_00_u03b1_128_, lean_object* v_msg_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___redArg(v_msg_129_, v___y_132_, v___y_133_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0___boxed(lean_object* v_00_u03b1_136_, lean_object* v_msg_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Lean_throwError___at___00Lean_IR_Checker_throwCheckerError_spec__0(v_00_u03b1_136_, v_msg_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1___redArg(lean_object* v_k_144_, lean_object* v_v_145_, lean_object* v_t_146_){
_start:
{
if (lean_obj_tag(v_t_146_) == 0)
{
lean_object* v_size_147_; lean_object* v_k_148_; lean_object* v_v_149_; lean_object* v_l_150_; lean_object* v_r_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_432_; 
v_size_147_ = lean_ctor_get(v_t_146_, 0);
v_k_148_ = lean_ctor_get(v_t_146_, 1);
v_v_149_ = lean_ctor_get(v_t_146_, 2);
v_l_150_ = lean_ctor_get(v_t_146_, 3);
v_r_151_ = lean_ctor_get(v_t_146_, 4);
v_isSharedCheck_432_ = !lean_is_exclusive(v_t_146_);
if (v_isSharedCheck_432_ == 0)
{
v___x_153_ = v_t_146_;
v_isShared_154_ = v_isSharedCheck_432_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_r_151_);
lean_inc(v_l_150_);
lean_inc(v_v_149_);
lean_inc(v_k_148_);
lean_inc(v_size_147_);
lean_dec(v_t_146_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_432_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
uint8_t v___x_155_; 
v___x_155_ = lean_nat_dec_lt(v_k_144_, v_k_148_);
if (v___x_155_ == 0)
{
uint8_t v___x_156_; 
v___x_156_ = lean_nat_dec_eq(v_k_144_, v_k_148_);
if (v___x_156_ == 0)
{
lean_object* v_impl_157_; lean_object* v___x_158_; 
lean_dec(v_size_147_);
v_impl_157_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1___redArg(v_k_144_, v_v_145_, v_r_151_);
v___x_158_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_150_) == 0)
{
lean_object* v_size_159_; lean_object* v_size_160_; lean_object* v_k_161_; lean_object* v_v_162_; lean_object* v_l_163_; lean_object* v_r_164_; lean_object* v___x_165_; lean_object* v___x_166_; uint8_t v___x_167_; 
v_size_159_ = lean_ctor_get(v_l_150_, 0);
v_size_160_ = lean_ctor_get(v_impl_157_, 0);
lean_inc(v_size_160_);
v_k_161_ = lean_ctor_get(v_impl_157_, 1);
lean_inc(v_k_161_);
v_v_162_ = lean_ctor_get(v_impl_157_, 2);
lean_inc(v_v_162_);
v_l_163_ = lean_ctor_get(v_impl_157_, 3);
lean_inc(v_l_163_);
v_r_164_ = lean_ctor_get(v_impl_157_, 4);
lean_inc(v_r_164_);
v___x_165_ = lean_unsigned_to_nat(3u);
v___x_166_ = lean_nat_mul(v___x_165_, v_size_159_);
v___x_167_ = lean_nat_dec_lt(v___x_166_, v_size_160_);
lean_dec(v___x_166_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_171_; 
lean_dec(v_r_164_);
lean_dec(v_l_163_);
lean_dec(v_v_162_);
lean_dec(v_k_161_);
v___x_168_ = lean_nat_add(v___x_158_, v_size_159_);
v___x_169_ = lean_nat_add(v___x_168_, v_size_160_);
lean_dec(v_size_160_);
lean_dec(v___x_168_);
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 4, v_impl_157_);
lean_ctor_set(v___x_153_, 0, v___x_169_);
v___x_171_ = v___x_153_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_169_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v_k_148_);
lean_ctor_set(v_reuseFailAlloc_172_, 2, v_v_149_);
lean_ctor_set(v_reuseFailAlloc_172_, 3, v_l_150_);
lean_ctor_set(v_reuseFailAlloc_172_, 4, v_impl_157_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
else
{
lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_236_; 
v_isSharedCheck_236_ = !lean_is_exclusive(v_impl_157_);
if (v_isSharedCheck_236_ == 0)
{
lean_object* v_unused_237_; lean_object* v_unused_238_; lean_object* v_unused_239_; lean_object* v_unused_240_; lean_object* v_unused_241_; 
v_unused_237_ = lean_ctor_get(v_impl_157_, 4);
lean_dec(v_unused_237_);
v_unused_238_ = lean_ctor_get(v_impl_157_, 3);
lean_dec(v_unused_238_);
v_unused_239_ = lean_ctor_get(v_impl_157_, 2);
lean_dec(v_unused_239_);
v_unused_240_ = lean_ctor_get(v_impl_157_, 1);
lean_dec(v_unused_240_);
v_unused_241_ = lean_ctor_get(v_impl_157_, 0);
lean_dec(v_unused_241_);
v___x_174_ = v_impl_157_;
v_isShared_175_ = v_isSharedCheck_236_;
goto v_resetjp_173_;
}
else
{
lean_dec(v_impl_157_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_236_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v_size_176_; lean_object* v_k_177_; lean_object* v_v_178_; lean_object* v_l_179_; lean_object* v_r_180_; lean_object* v_size_181_; lean_object* v___x_182_; lean_object* v___x_183_; uint8_t v___x_184_; 
v_size_176_ = lean_ctor_get(v_l_163_, 0);
v_k_177_ = lean_ctor_get(v_l_163_, 1);
v_v_178_ = lean_ctor_get(v_l_163_, 2);
v_l_179_ = lean_ctor_get(v_l_163_, 3);
v_r_180_ = lean_ctor_get(v_l_163_, 4);
v_size_181_ = lean_ctor_get(v_r_164_, 0);
v___x_182_ = lean_unsigned_to_nat(2u);
v___x_183_ = lean_nat_mul(v___x_182_, v_size_181_);
v___x_184_ = lean_nat_dec_lt(v_size_176_, v___x_183_);
lean_dec(v___x_183_);
if (v___x_184_ == 0)
{
lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_212_; 
lean_inc(v_r_180_);
lean_inc(v_l_179_);
lean_inc(v_v_178_);
lean_inc(v_k_177_);
v_isSharedCheck_212_ = !lean_is_exclusive(v_l_163_);
if (v_isSharedCheck_212_ == 0)
{
lean_object* v_unused_213_; lean_object* v_unused_214_; lean_object* v_unused_215_; lean_object* v_unused_216_; lean_object* v_unused_217_; 
v_unused_213_ = lean_ctor_get(v_l_163_, 4);
lean_dec(v_unused_213_);
v_unused_214_ = lean_ctor_get(v_l_163_, 3);
lean_dec(v_unused_214_);
v_unused_215_ = lean_ctor_get(v_l_163_, 2);
lean_dec(v_unused_215_);
v_unused_216_ = lean_ctor_get(v_l_163_, 1);
lean_dec(v_unused_216_);
v_unused_217_ = lean_ctor_get(v_l_163_, 0);
lean_dec(v_unused_217_);
v___x_186_ = v_l_163_;
v_isShared_187_ = v_isSharedCheck_212_;
goto v_resetjp_185_;
}
else
{
lean_dec(v_l_163_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_212_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___y_191_; lean_object* v___y_192_; lean_object* v___y_193_; lean_object* v___y_202_; 
v___x_188_ = lean_nat_add(v___x_158_, v_size_159_);
v___x_189_ = lean_nat_add(v___x_188_, v_size_160_);
lean_dec(v_size_160_);
if (lean_obj_tag(v_l_179_) == 0)
{
lean_object* v_size_210_; 
v_size_210_ = lean_ctor_get(v_l_179_, 0);
lean_inc(v_size_210_);
v___y_202_ = v_size_210_;
goto v___jp_201_;
}
else
{
lean_object* v___x_211_; 
v___x_211_ = lean_unsigned_to_nat(0u);
v___y_202_ = v___x_211_;
goto v___jp_201_;
}
v___jp_190_:
{
lean_object* v___x_194_; lean_object* v___x_196_; 
v___x_194_ = lean_nat_add(v___y_192_, v___y_193_);
lean_dec(v___y_193_);
lean_dec(v___y_192_);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 4, v_r_164_);
lean_ctor_set(v___x_186_, 3, v_r_180_);
lean_ctor_set(v___x_186_, 2, v_v_162_);
lean_ctor_set(v___x_186_, 1, v_k_161_);
lean_ctor_set(v___x_186_, 0, v___x_194_);
v___x_196_ = v___x_186_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_194_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v_k_161_);
lean_ctor_set(v_reuseFailAlloc_200_, 2, v_v_162_);
lean_ctor_set(v_reuseFailAlloc_200_, 3, v_r_180_);
lean_ctor_set(v_reuseFailAlloc_200_, 4, v_r_164_);
v___x_196_ = v_reuseFailAlloc_200_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
lean_object* v___x_198_; 
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 4, v___x_196_);
lean_ctor_set(v___x_174_, 3, v___y_191_);
lean_ctor_set(v___x_174_, 2, v_v_178_);
lean_ctor_set(v___x_174_, 1, v_k_177_);
lean_ctor_set(v___x_174_, 0, v___x_189_);
v___x_198_ = v___x_174_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_189_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v_k_177_);
lean_ctor_set(v_reuseFailAlloc_199_, 2, v_v_178_);
lean_ctor_set(v_reuseFailAlloc_199_, 3, v___y_191_);
lean_ctor_set(v_reuseFailAlloc_199_, 4, v___x_196_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
v___jp_201_:
{
lean_object* v___x_203_; lean_object* v___x_205_; 
v___x_203_ = lean_nat_add(v___x_188_, v___y_202_);
lean_dec(v___y_202_);
lean_dec(v___x_188_);
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 4, v_l_179_);
lean_ctor_set(v___x_153_, 0, v___x_203_);
v___x_205_ = v___x_153_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v___x_203_);
lean_ctor_set(v_reuseFailAlloc_209_, 1, v_k_148_);
lean_ctor_set(v_reuseFailAlloc_209_, 2, v_v_149_);
lean_ctor_set(v_reuseFailAlloc_209_, 3, v_l_150_);
lean_ctor_set(v_reuseFailAlloc_209_, 4, v_l_179_);
v___x_205_ = v_reuseFailAlloc_209_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
lean_object* v___x_206_; 
v___x_206_ = lean_nat_add(v___x_158_, v_size_181_);
if (lean_obj_tag(v_r_180_) == 0)
{
lean_object* v_size_207_; 
v_size_207_ = lean_ctor_get(v_r_180_, 0);
lean_inc(v_size_207_);
v___y_191_ = v___x_205_;
v___y_192_ = v___x_206_;
v___y_193_ = v_size_207_;
goto v___jp_190_;
}
else
{
lean_object* v___x_208_; 
v___x_208_ = lean_unsigned_to_nat(0u);
v___y_191_ = v___x_205_;
v___y_192_ = v___x_206_;
v___y_193_ = v___x_208_;
goto v___jp_190_;
}
}
}
}
}
else
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_222_; 
lean_del_object(v___x_153_);
v___x_218_ = lean_nat_add(v___x_158_, v_size_159_);
v___x_219_ = lean_nat_add(v___x_218_, v_size_160_);
lean_dec(v_size_160_);
v___x_220_ = lean_nat_add(v___x_218_, v_size_176_);
lean_dec(v___x_218_);
lean_inc_ref(v_l_150_);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 4, v_l_163_);
lean_ctor_set(v___x_174_, 3, v_l_150_);
lean_ctor_set(v___x_174_, 2, v_v_149_);
lean_ctor_set(v___x_174_, 1, v_k_148_);
lean_ctor_set(v___x_174_, 0, v___x_220_);
v___x_222_ = v___x_174_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_220_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v_k_148_);
lean_ctor_set(v_reuseFailAlloc_235_, 2, v_v_149_);
lean_ctor_set(v_reuseFailAlloc_235_, 3, v_l_150_);
lean_ctor_set(v_reuseFailAlloc_235_, 4, v_l_163_);
v___x_222_ = v_reuseFailAlloc_235_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_229_; 
v_isSharedCheck_229_ = !lean_is_exclusive(v_l_150_);
if (v_isSharedCheck_229_ == 0)
{
lean_object* v_unused_230_; lean_object* v_unused_231_; lean_object* v_unused_232_; lean_object* v_unused_233_; lean_object* v_unused_234_; 
v_unused_230_ = lean_ctor_get(v_l_150_, 4);
lean_dec(v_unused_230_);
v_unused_231_ = lean_ctor_get(v_l_150_, 3);
lean_dec(v_unused_231_);
v_unused_232_ = lean_ctor_get(v_l_150_, 2);
lean_dec(v_unused_232_);
v_unused_233_ = lean_ctor_get(v_l_150_, 1);
lean_dec(v_unused_233_);
v_unused_234_ = lean_ctor_get(v_l_150_, 0);
lean_dec(v_unused_234_);
v___x_224_ = v_l_150_;
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
else
{
lean_dec(v_l_150_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_227_; 
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 4, v_r_164_);
lean_ctor_set(v___x_224_, 3, v___x_222_);
lean_ctor_set(v___x_224_, 2, v_v_162_);
lean_ctor_set(v___x_224_, 1, v_k_161_);
lean_ctor_set(v___x_224_, 0, v___x_219_);
v___x_227_ = v___x_224_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v___x_219_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v_k_161_);
lean_ctor_set(v_reuseFailAlloc_228_, 2, v_v_162_);
lean_ctor_set(v_reuseFailAlloc_228_, 3, v___x_222_);
lean_ctor_set(v_reuseFailAlloc_228_, 4, v_r_164_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_242_; 
v_l_242_ = lean_ctor_get(v_impl_157_, 3);
lean_inc(v_l_242_);
if (lean_obj_tag(v_l_242_) == 0)
{
lean_object* v_r_243_; lean_object* v_k_244_; lean_object* v_v_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_268_; 
v_r_243_ = lean_ctor_get(v_impl_157_, 4);
v_k_244_ = lean_ctor_get(v_impl_157_, 1);
v_v_245_ = lean_ctor_get(v_impl_157_, 2);
v_isSharedCheck_268_ = !lean_is_exclusive(v_impl_157_);
if (v_isSharedCheck_268_ == 0)
{
lean_object* v_unused_269_; lean_object* v_unused_270_; 
v_unused_269_ = lean_ctor_get(v_impl_157_, 3);
lean_dec(v_unused_269_);
v_unused_270_ = lean_ctor_get(v_impl_157_, 0);
lean_dec(v_unused_270_);
v___x_247_ = v_impl_157_;
v_isShared_248_ = v_isSharedCheck_268_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_r_243_);
lean_inc(v_v_245_);
lean_inc(v_k_244_);
lean_dec(v_impl_157_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_268_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v_k_249_; lean_object* v_v_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_264_; 
v_k_249_ = lean_ctor_get(v_l_242_, 1);
v_v_250_ = lean_ctor_get(v_l_242_, 2);
v_isSharedCheck_264_ = !lean_is_exclusive(v_l_242_);
if (v_isSharedCheck_264_ == 0)
{
lean_object* v_unused_265_; lean_object* v_unused_266_; lean_object* v_unused_267_; 
v_unused_265_ = lean_ctor_get(v_l_242_, 4);
lean_dec(v_unused_265_);
v_unused_266_ = lean_ctor_get(v_l_242_, 3);
lean_dec(v_unused_266_);
v_unused_267_ = lean_ctor_get(v_l_242_, 0);
lean_dec(v_unused_267_);
v___x_252_ = v_l_242_;
v_isShared_253_ = v_isSharedCheck_264_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_v_250_);
lean_inc(v_k_249_);
lean_dec(v_l_242_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_264_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_254_; lean_object* v___x_256_; 
v___x_254_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_243_, 2);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 4, v_r_243_);
lean_ctor_set(v___x_252_, 3, v_r_243_);
lean_ctor_set(v___x_252_, 2, v_v_149_);
lean_ctor_set(v___x_252_, 1, v_k_148_);
lean_ctor_set(v___x_252_, 0, v___x_158_);
v___x_256_ = v___x_252_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_158_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v_k_148_);
lean_ctor_set(v_reuseFailAlloc_263_, 2, v_v_149_);
lean_ctor_set(v_reuseFailAlloc_263_, 3, v_r_243_);
lean_ctor_set(v_reuseFailAlloc_263_, 4, v_r_243_);
v___x_256_ = v_reuseFailAlloc_263_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
lean_object* v___x_258_; 
lean_inc(v_r_243_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 3, v_r_243_);
lean_ctor_set(v___x_247_, 0, v___x_158_);
v___x_258_ = v___x_247_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_158_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v_k_244_);
lean_ctor_set(v_reuseFailAlloc_262_, 2, v_v_245_);
lean_ctor_set(v_reuseFailAlloc_262_, 3, v_r_243_);
lean_ctor_set(v_reuseFailAlloc_262_, 4, v_r_243_);
v___x_258_ = v_reuseFailAlloc_262_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
lean_object* v___x_260_; 
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 4, v___x_258_);
lean_ctor_set(v___x_153_, 3, v___x_256_);
lean_ctor_set(v___x_153_, 2, v_v_250_);
lean_ctor_set(v___x_153_, 1, v_k_249_);
lean_ctor_set(v___x_153_, 0, v___x_254_);
v___x_260_ = v___x_153_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_254_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_k_249_);
lean_ctor_set(v_reuseFailAlloc_261_, 2, v_v_250_);
lean_ctor_set(v_reuseFailAlloc_261_, 3, v___x_256_);
lean_ctor_set(v_reuseFailAlloc_261_, 4, v___x_258_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
}
}
else
{
lean_object* v_r_271_; 
v_r_271_ = lean_ctor_get(v_impl_157_, 4);
lean_inc(v_r_271_);
if (lean_obj_tag(v_r_271_) == 0)
{
lean_object* v_k_272_; lean_object* v_v_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_284_; 
v_k_272_ = lean_ctor_get(v_impl_157_, 1);
v_v_273_ = lean_ctor_get(v_impl_157_, 2);
v_isSharedCheck_284_ = !lean_is_exclusive(v_impl_157_);
if (v_isSharedCheck_284_ == 0)
{
lean_object* v_unused_285_; lean_object* v_unused_286_; lean_object* v_unused_287_; 
v_unused_285_ = lean_ctor_get(v_impl_157_, 4);
lean_dec(v_unused_285_);
v_unused_286_ = lean_ctor_get(v_impl_157_, 3);
lean_dec(v_unused_286_);
v_unused_287_ = lean_ctor_get(v_impl_157_, 0);
lean_dec(v_unused_287_);
v___x_275_ = v_impl_157_;
v_isShared_276_ = v_isSharedCheck_284_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_v_273_);
lean_inc(v_k_272_);
lean_dec(v_impl_157_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_284_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_277_; lean_object* v___x_279_; 
v___x_277_ = lean_unsigned_to_nat(3u);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 4, v_l_242_);
lean_ctor_set(v___x_275_, 2, v_v_149_);
lean_ctor_set(v___x_275_, 1, v_k_148_);
lean_ctor_set(v___x_275_, 0, v___x_158_);
v___x_279_ = v___x_275_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_158_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v_k_148_);
lean_ctor_set(v_reuseFailAlloc_283_, 2, v_v_149_);
lean_ctor_set(v_reuseFailAlloc_283_, 3, v_l_242_);
lean_ctor_set(v_reuseFailAlloc_283_, 4, v_l_242_);
v___x_279_ = v_reuseFailAlloc_283_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
lean_object* v___x_281_; 
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 4, v_r_271_);
lean_ctor_set(v___x_153_, 3, v___x_279_);
lean_ctor_set(v___x_153_, 2, v_v_273_);
lean_ctor_set(v___x_153_, 1, v_k_272_);
lean_ctor_set(v___x_153_, 0, v___x_277_);
v___x_281_ = v___x_153_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_277_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v_k_272_);
lean_ctor_set(v_reuseFailAlloc_282_, 2, v_v_273_);
lean_ctor_set(v_reuseFailAlloc_282_, 3, v___x_279_);
lean_ctor_set(v_reuseFailAlloc_282_, 4, v_r_271_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
else
{
lean_object* v___x_288_; lean_object* v___x_290_; 
v___x_288_ = lean_unsigned_to_nat(2u);
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 4, v_impl_157_);
lean_ctor_set(v___x_153_, 3, v_r_271_);
lean_ctor_set(v___x_153_, 0, v___x_288_);
v___x_290_ = v___x_153_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v___x_288_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v_k_148_);
lean_ctor_set(v_reuseFailAlloc_291_, 2, v_v_149_);
lean_ctor_set(v_reuseFailAlloc_291_, 3, v_r_271_);
lean_ctor_set(v_reuseFailAlloc_291_, 4, v_impl_157_);
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
else
{
lean_object* v___x_293_; 
lean_dec(v_v_149_);
lean_dec(v_k_148_);
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 2, v_v_145_);
lean_ctor_set(v___x_153_, 1, v_k_144_);
v___x_293_ = v___x_153_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_size_147_);
lean_ctor_set(v_reuseFailAlloc_294_, 1, v_k_144_);
lean_ctor_set(v_reuseFailAlloc_294_, 2, v_v_145_);
lean_ctor_set(v_reuseFailAlloc_294_, 3, v_l_150_);
lean_ctor_set(v_reuseFailAlloc_294_, 4, v_r_151_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
else
{
lean_object* v_impl_295_; lean_object* v___x_296_; 
lean_dec(v_size_147_);
v_impl_295_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1___redArg(v_k_144_, v_v_145_, v_l_150_);
v___x_296_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_151_) == 0)
{
lean_object* v_size_297_; lean_object* v_size_298_; lean_object* v_k_299_; lean_object* v_v_300_; lean_object* v_l_301_; lean_object* v_r_302_; lean_object* v___x_303_; lean_object* v___x_304_; uint8_t v___x_305_; 
v_size_297_ = lean_ctor_get(v_r_151_, 0);
v_size_298_ = lean_ctor_get(v_impl_295_, 0);
lean_inc(v_size_298_);
v_k_299_ = lean_ctor_get(v_impl_295_, 1);
lean_inc(v_k_299_);
v_v_300_ = lean_ctor_get(v_impl_295_, 2);
lean_inc(v_v_300_);
v_l_301_ = lean_ctor_get(v_impl_295_, 3);
lean_inc(v_l_301_);
v_r_302_ = lean_ctor_get(v_impl_295_, 4);
lean_inc(v_r_302_);
v___x_303_ = lean_unsigned_to_nat(3u);
v___x_304_ = lean_nat_mul(v___x_303_, v_size_297_);
v___x_305_ = lean_nat_dec_lt(v___x_304_, v_size_298_);
lean_dec(v___x_304_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_309_; 
lean_dec(v_r_302_);
lean_dec(v_l_301_);
lean_dec(v_v_300_);
lean_dec(v_k_299_);
v___x_306_ = lean_nat_add(v___x_296_, v_size_298_);
lean_dec(v_size_298_);
v___x_307_ = lean_nat_add(v___x_306_, v_size_297_);
lean_dec(v___x_306_);
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 3, v_impl_295_);
lean_ctor_set(v___x_153_, 0, v___x_307_);
v___x_309_ = v___x_153_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___x_307_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v_k_148_);
lean_ctor_set(v_reuseFailAlloc_310_, 2, v_v_149_);
lean_ctor_set(v_reuseFailAlloc_310_, 3, v_impl_295_);
lean_ctor_set(v_reuseFailAlloc_310_, 4, v_r_151_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
else
{
lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_376_; 
v_isSharedCheck_376_ = !lean_is_exclusive(v_impl_295_);
if (v_isSharedCheck_376_ == 0)
{
lean_object* v_unused_377_; lean_object* v_unused_378_; lean_object* v_unused_379_; lean_object* v_unused_380_; lean_object* v_unused_381_; 
v_unused_377_ = lean_ctor_get(v_impl_295_, 4);
lean_dec(v_unused_377_);
v_unused_378_ = lean_ctor_get(v_impl_295_, 3);
lean_dec(v_unused_378_);
v_unused_379_ = lean_ctor_get(v_impl_295_, 2);
lean_dec(v_unused_379_);
v_unused_380_ = lean_ctor_get(v_impl_295_, 1);
lean_dec(v_unused_380_);
v_unused_381_ = lean_ctor_get(v_impl_295_, 0);
lean_dec(v_unused_381_);
v___x_312_ = v_impl_295_;
v_isShared_313_ = v_isSharedCheck_376_;
goto v_resetjp_311_;
}
else
{
lean_dec(v_impl_295_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_376_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v_size_314_; lean_object* v_size_315_; lean_object* v_k_316_; lean_object* v_v_317_; lean_object* v_l_318_; lean_object* v_r_319_; lean_object* v___x_320_; lean_object* v___x_321_; uint8_t v___x_322_; 
v_size_314_ = lean_ctor_get(v_l_301_, 0);
v_size_315_ = lean_ctor_get(v_r_302_, 0);
v_k_316_ = lean_ctor_get(v_r_302_, 1);
v_v_317_ = lean_ctor_get(v_r_302_, 2);
v_l_318_ = lean_ctor_get(v_r_302_, 3);
v_r_319_ = lean_ctor_get(v_r_302_, 4);
v___x_320_ = lean_unsigned_to_nat(2u);
v___x_321_ = lean_nat_mul(v___x_320_, v_size_314_);
v___x_322_ = lean_nat_dec_lt(v_size_315_, v___x_321_);
lean_dec(v___x_321_);
if (v___x_322_ == 0)
{
lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_351_; 
lean_inc(v_r_319_);
lean_inc(v_l_318_);
lean_inc(v_v_317_);
lean_inc(v_k_316_);
v_isSharedCheck_351_ = !lean_is_exclusive(v_r_302_);
if (v_isSharedCheck_351_ == 0)
{
lean_object* v_unused_352_; lean_object* v_unused_353_; lean_object* v_unused_354_; lean_object* v_unused_355_; lean_object* v_unused_356_; 
v_unused_352_ = lean_ctor_get(v_r_302_, 4);
lean_dec(v_unused_352_);
v_unused_353_ = lean_ctor_get(v_r_302_, 3);
lean_dec(v_unused_353_);
v_unused_354_ = lean_ctor_get(v_r_302_, 2);
lean_dec(v_unused_354_);
v_unused_355_ = lean_ctor_get(v_r_302_, 1);
lean_dec(v_unused_355_);
v_unused_356_ = lean_ctor_get(v_r_302_, 0);
lean_dec(v_unused_356_);
v___x_324_ = v_r_302_;
v_isShared_325_ = v_isSharedCheck_351_;
goto v_resetjp_323_;
}
else
{
lean_dec(v_r_302_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_351_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v___y_331_; lean_object* v___x_339_; lean_object* v___y_341_; 
v___x_326_ = lean_nat_add(v___x_296_, v_size_298_);
lean_dec(v_size_298_);
v___x_327_ = lean_nat_add(v___x_326_, v_size_297_);
lean_dec(v___x_326_);
v___x_339_ = lean_nat_add(v___x_296_, v_size_314_);
if (lean_obj_tag(v_l_318_) == 0)
{
lean_object* v_size_349_; 
v_size_349_ = lean_ctor_get(v_l_318_, 0);
lean_inc(v_size_349_);
v___y_341_ = v_size_349_;
goto v___jp_340_;
}
else
{
lean_object* v___x_350_; 
v___x_350_ = lean_unsigned_to_nat(0u);
v___y_341_ = v___x_350_;
goto v___jp_340_;
}
v___jp_328_:
{
lean_object* v___x_332_; lean_object* v___x_334_; 
v___x_332_ = lean_nat_add(v___y_329_, v___y_331_);
lean_dec(v___y_331_);
lean_dec(v___y_329_);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 4, v_r_151_);
lean_ctor_set(v___x_324_, 3, v_r_319_);
lean_ctor_set(v___x_324_, 2, v_v_149_);
lean_ctor_set(v___x_324_, 1, v_k_148_);
lean_ctor_set(v___x_324_, 0, v___x_332_);
v___x_334_ = v___x_324_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v___x_332_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v_k_148_);
lean_ctor_set(v_reuseFailAlloc_338_, 2, v_v_149_);
lean_ctor_set(v_reuseFailAlloc_338_, 3, v_r_319_);
lean_ctor_set(v_reuseFailAlloc_338_, 4, v_r_151_);
v___x_334_ = v_reuseFailAlloc_338_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
lean_object* v___x_336_; 
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 4, v___x_334_);
lean_ctor_set(v___x_312_, 3, v___y_330_);
lean_ctor_set(v___x_312_, 2, v_v_317_);
lean_ctor_set(v___x_312_, 1, v_k_316_);
lean_ctor_set(v___x_312_, 0, v___x_327_);
v___x_336_ = v___x_312_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_327_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_k_316_);
lean_ctor_set(v_reuseFailAlloc_337_, 2, v_v_317_);
lean_ctor_set(v_reuseFailAlloc_337_, 3, v___y_330_);
lean_ctor_set(v_reuseFailAlloc_337_, 4, v___x_334_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
v___jp_340_:
{
lean_object* v___x_342_; lean_object* v___x_344_; 
v___x_342_ = lean_nat_add(v___x_339_, v___y_341_);
lean_dec(v___y_341_);
lean_dec(v___x_339_);
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 4, v_l_318_);
lean_ctor_set(v___x_153_, 3, v_l_301_);
lean_ctor_set(v___x_153_, 2, v_v_300_);
lean_ctor_set(v___x_153_, 1, v_k_299_);
lean_ctor_set(v___x_153_, 0, v___x_342_);
v___x_344_ = v___x_153_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v___x_342_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v_k_299_);
lean_ctor_set(v_reuseFailAlloc_348_, 2, v_v_300_);
lean_ctor_set(v_reuseFailAlloc_348_, 3, v_l_301_);
lean_ctor_set(v_reuseFailAlloc_348_, 4, v_l_318_);
v___x_344_ = v_reuseFailAlloc_348_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
lean_object* v___x_345_; 
v___x_345_ = lean_nat_add(v___x_296_, v_size_297_);
if (lean_obj_tag(v_r_319_) == 0)
{
lean_object* v_size_346_; 
v_size_346_ = lean_ctor_get(v_r_319_, 0);
lean_inc(v_size_346_);
v___y_329_ = v___x_345_;
v___y_330_ = v___x_344_;
v___y_331_ = v_size_346_;
goto v___jp_328_;
}
else
{
lean_object* v___x_347_; 
v___x_347_ = lean_unsigned_to_nat(0u);
v___y_329_ = v___x_345_;
v___y_330_ = v___x_344_;
v___y_331_ = v___x_347_;
goto v___jp_328_;
}
}
}
}
}
else
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_362_; 
lean_del_object(v___x_153_);
v___x_357_ = lean_nat_add(v___x_296_, v_size_298_);
lean_dec(v_size_298_);
v___x_358_ = lean_nat_add(v___x_357_, v_size_297_);
lean_dec(v___x_357_);
v___x_359_ = lean_nat_add(v___x_296_, v_size_297_);
v___x_360_ = lean_nat_add(v___x_359_, v_size_315_);
lean_dec(v___x_359_);
lean_inc_ref(v_r_151_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 4, v_r_151_);
lean_ctor_set(v___x_312_, 3, v_r_302_);
lean_ctor_set(v___x_312_, 2, v_v_149_);
lean_ctor_set(v___x_312_, 1, v_k_148_);
lean_ctor_set(v___x_312_, 0, v___x_360_);
v___x_362_ = v___x_312_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_360_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v_k_148_);
lean_ctor_set(v_reuseFailAlloc_375_, 2, v_v_149_);
lean_ctor_set(v_reuseFailAlloc_375_, 3, v_r_302_);
lean_ctor_set(v_reuseFailAlloc_375_, 4, v_r_151_);
v___x_362_ = v_reuseFailAlloc_375_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
v_isSharedCheck_369_ = !lean_is_exclusive(v_r_151_);
if (v_isSharedCheck_369_ == 0)
{
lean_object* v_unused_370_; lean_object* v_unused_371_; lean_object* v_unused_372_; lean_object* v_unused_373_; lean_object* v_unused_374_; 
v_unused_370_ = lean_ctor_get(v_r_151_, 4);
lean_dec(v_unused_370_);
v_unused_371_ = lean_ctor_get(v_r_151_, 3);
lean_dec(v_unused_371_);
v_unused_372_ = lean_ctor_get(v_r_151_, 2);
lean_dec(v_unused_372_);
v_unused_373_ = lean_ctor_get(v_r_151_, 1);
lean_dec(v_unused_373_);
v_unused_374_ = lean_ctor_get(v_r_151_, 0);
lean_dec(v_unused_374_);
v___x_364_ = v_r_151_;
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
else
{
lean_dec(v_r_151_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 4, v___x_362_);
lean_ctor_set(v___x_364_, 3, v_l_301_);
lean_ctor_set(v___x_364_, 2, v_v_300_);
lean_ctor_set(v___x_364_, 1, v_k_299_);
lean_ctor_set(v___x_364_, 0, v___x_358_);
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___x_358_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v_k_299_);
lean_ctor_set(v_reuseFailAlloc_368_, 2, v_v_300_);
lean_ctor_set(v_reuseFailAlloc_368_, 3, v_l_301_);
lean_ctor_set(v_reuseFailAlloc_368_, 4, v___x_362_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_382_; 
v_l_382_ = lean_ctor_get(v_impl_295_, 3);
lean_inc(v_l_382_);
if (lean_obj_tag(v_l_382_) == 0)
{
lean_object* v_r_383_; lean_object* v_k_384_; lean_object* v_v_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_396_; 
v_r_383_ = lean_ctor_get(v_impl_295_, 4);
v_k_384_ = lean_ctor_get(v_impl_295_, 1);
v_v_385_ = lean_ctor_get(v_impl_295_, 2);
v_isSharedCheck_396_ = !lean_is_exclusive(v_impl_295_);
if (v_isSharedCheck_396_ == 0)
{
lean_object* v_unused_397_; lean_object* v_unused_398_; 
v_unused_397_ = lean_ctor_get(v_impl_295_, 3);
lean_dec(v_unused_397_);
v_unused_398_ = lean_ctor_get(v_impl_295_, 0);
lean_dec(v_unused_398_);
v___x_387_ = v_impl_295_;
v_isShared_388_ = v_isSharedCheck_396_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_r_383_);
lean_inc(v_v_385_);
lean_inc(v_k_384_);
lean_dec(v_impl_295_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_396_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_389_; lean_object* v___x_391_; 
v___x_389_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_383_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 3, v_r_383_);
lean_ctor_set(v___x_387_, 2, v_v_149_);
lean_ctor_set(v___x_387_, 1, v_k_148_);
lean_ctor_set(v___x_387_, 0, v___x_296_);
v___x_391_ = v___x_387_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_296_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_k_148_);
lean_ctor_set(v_reuseFailAlloc_395_, 2, v_v_149_);
lean_ctor_set(v_reuseFailAlloc_395_, 3, v_r_383_);
lean_ctor_set(v_reuseFailAlloc_395_, 4, v_r_383_);
v___x_391_ = v_reuseFailAlloc_395_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
lean_object* v___x_393_; 
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 4, v___x_391_);
lean_ctor_set(v___x_153_, 3, v_l_382_);
lean_ctor_set(v___x_153_, 2, v_v_385_);
lean_ctor_set(v___x_153_, 1, v_k_384_);
lean_ctor_set(v___x_153_, 0, v___x_389_);
v___x_393_ = v___x_153_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_389_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v_k_384_);
lean_ctor_set(v_reuseFailAlloc_394_, 2, v_v_385_);
lean_ctor_set(v_reuseFailAlloc_394_, 3, v_l_382_);
lean_ctor_set(v_reuseFailAlloc_394_, 4, v___x_391_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
else
{
lean_object* v_r_399_; 
v_r_399_ = lean_ctor_get(v_impl_295_, 4);
lean_inc(v_r_399_);
if (lean_obj_tag(v_r_399_) == 0)
{
lean_object* v_k_400_; lean_object* v_v_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_424_; 
v_k_400_ = lean_ctor_get(v_impl_295_, 1);
v_v_401_ = lean_ctor_get(v_impl_295_, 2);
v_isSharedCheck_424_ = !lean_is_exclusive(v_impl_295_);
if (v_isSharedCheck_424_ == 0)
{
lean_object* v_unused_425_; lean_object* v_unused_426_; lean_object* v_unused_427_; 
v_unused_425_ = lean_ctor_get(v_impl_295_, 4);
lean_dec(v_unused_425_);
v_unused_426_ = lean_ctor_get(v_impl_295_, 3);
lean_dec(v_unused_426_);
v_unused_427_ = lean_ctor_get(v_impl_295_, 0);
lean_dec(v_unused_427_);
v___x_403_ = v_impl_295_;
v_isShared_404_ = v_isSharedCheck_424_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_v_401_);
lean_inc(v_k_400_);
lean_dec(v_impl_295_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_424_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v_k_405_; lean_object* v_v_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_420_; 
v_k_405_ = lean_ctor_get(v_r_399_, 1);
v_v_406_ = lean_ctor_get(v_r_399_, 2);
v_isSharedCheck_420_ = !lean_is_exclusive(v_r_399_);
if (v_isSharedCheck_420_ == 0)
{
lean_object* v_unused_421_; lean_object* v_unused_422_; lean_object* v_unused_423_; 
v_unused_421_ = lean_ctor_get(v_r_399_, 4);
lean_dec(v_unused_421_);
v_unused_422_ = lean_ctor_get(v_r_399_, 3);
lean_dec(v_unused_422_);
v_unused_423_ = lean_ctor_get(v_r_399_, 0);
lean_dec(v_unused_423_);
v___x_408_ = v_r_399_;
v_isShared_409_ = v_isSharedCheck_420_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_v_406_);
lean_inc(v_k_405_);
lean_dec(v_r_399_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_420_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_410_; lean_object* v___x_412_; 
v___x_410_ = lean_unsigned_to_nat(3u);
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 4, v_l_382_);
lean_ctor_set(v___x_408_, 3, v_l_382_);
lean_ctor_set(v___x_408_, 2, v_v_401_);
lean_ctor_set(v___x_408_, 1, v_k_400_);
lean_ctor_set(v___x_408_, 0, v___x_296_);
v___x_412_ = v___x_408_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_296_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v_k_400_);
lean_ctor_set(v_reuseFailAlloc_419_, 2, v_v_401_);
lean_ctor_set(v_reuseFailAlloc_419_, 3, v_l_382_);
lean_ctor_set(v_reuseFailAlloc_419_, 4, v_l_382_);
v___x_412_ = v_reuseFailAlloc_419_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
lean_object* v___x_414_; 
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 4, v_l_382_);
lean_ctor_set(v___x_403_, 2, v_v_149_);
lean_ctor_set(v___x_403_, 1, v_k_148_);
lean_ctor_set(v___x_403_, 0, v___x_296_);
v___x_414_ = v___x_403_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_296_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v_k_148_);
lean_ctor_set(v_reuseFailAlloc_418_, 2, v_v_149_);
lean_ctor_set(v_reuseFailAlloc_418_, 3, v_l_382_);
lean_ctor_set(v_reuseFailAlloc_418_, 4, v_l_382_);
v___x_414_ = v_reuseFailAlloc_418_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
lean_object* v___x_416_; 
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 4, v___x_414_);
lean_ctor_set(v___x_153_, 3, v___x_412_);
lean_ctor_set(v___x_153_, 2, v_v_406_);
lean_ctor_set(v___x_153_, 1, v_k_405_);
lean_ctor_set(v___x_153_, 0, v___x_410_);
v___x_416_ = v___x_153_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_410_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v_k_405_);
lean_ctor_set(v_reuseFailAlloc_417_, 2, v_v_406_);
lean_ctor_set(v_reuseFailAlloc_417_, 3, v___x_412_);
lean_ctor_set(v_reuseFailAlloc_417_, 4, v___x_414_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
}
}
else
{
lean_object* v___x_428_; lean_object* v___x_430_; 
v___x_428_ = lean_unsigned_to_nat(2u);
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 4, v_r_399_);
lean_ctor_set(v___x_153_, 3, v_impl_295_);
lean_ctor_set(v___x_153_, 0, v___x_428_);
v___x_430_ = v___x_153_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v___x_428_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v_k_148_);
lean_ctor_set(v_reuseFailAlloc_431_, 2, v_v_149_);
lean_ctor_set(v_reuseFailAlloc_431_, 3, v_impl_295_);
lean_ctor_set(v_reuseFailAlloc_431_, 4, v_r_399_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = lean_unsigned_to_nat(1u);
v___x_434_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
lean_ctor_set(v___x_434_, 1, v_k_144_);
lean_ctor_set(v___x_434_, 2, v_v_145_);
lean_ctor_set(v___x_434_, 3, v_t_146_);
lean_ctor_set(v___x_434_, 4, v_t_146_);
return v___x_434_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg(lean_object* v_k_435_, lean_object* v_t_436_){
_start:
{
if (lean_obj_tag(v_t_436_) == 0)
{
lean_object* v_k_437_; lean_object* v_l_438_; lean_object* v_r_439_; uint8_t v___x_440_; 
v_k_437_ = lean_ctor_get(v_t_436_, 1);
v_l_438_ = lean_ctor_get(v_t_436_, 3);
v_r_439_ = lean_ctor_get(v_t_436_, 4);
v___x_440_ = lean_nat_dec_lt(v_k_435_, v_k_437_);
if (v___x_440_ == 0)
{
uint8_t v___x_441_; 
v___x_441_ = lean_nat_dec_eq(v_k_435_, v_k_437_);
if (v___x_441_ == 0)
{
v_t_436_ = v_r_439_;
goto _start;
}
else
{
return v___x_441_;
}
}
else
{
v_t_436_ = v_l_438_;
goto _start;
}
}
else
{
uint8_t v___x_444_; 
v___x_444_ = 0;
return v___x_444_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg___boxed(lean_object* v_k_445_, lean_object* v_t_446_){
_start:
{
uint8_t v_res_447_; lean_object* v_r_448_; 
v_res_447_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg(v_k_445_, v_t_446_);
lean_dec(v_t_446_);
lean_dec(v_k_445_);
v_r_448_ = lean_box(v_res_447_);
return v_r_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex(lean_object* v_i_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_){
_start:
{
lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___y_460_; lean_object* v___y_464_; lean_object* v___x_469_; uint8_t v___x_470_; 
v___x_469_ = lean_st_ref_get(v_a_453_);
v___x_470_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg(v_i_451_, v___x_469_);
lean_dec(v___x_469_);
if (v___x_470_ == 0)
{
v___y_464_ = v_a_453_;
goto v___jp_463_;
}
else
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_471_ = ((lean_object*)(l_Lean_IR_Checker_markIndex___closed__0));
v___x_472_ = l_Nat_reprFast(v_i_451_);
v___x_473_ = lean_string_append(v___x_471_, v___x_472_);
lean_dec_ref(v___x_472_);
v___x_474_ = ((lean_object*)(l_Lean_IR_Checker_markIndex___closed__1));
v___x_475_ = lean_string_append(v___x_473_, v___x_474_);
v___x_476_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_475_, v_a_452_, v_a_453_, v_a_454_, v_a_455_);
return v___x_476_;
}
v___jp_457_:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = lean_st_ref_put(v___y_458_, v___y_460_);
v___x_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_462_, 0, v___y_459_);
return v___x_462_;
}
v___jp_463_:
{
lean_object* v___x_465_; lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_465_ = lean_st_ref_take(v___y_464_);
v___x_466_ = lean_box(0);
v___x_467_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg(v_i_451_, v___x_465_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; 
v___x_468_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1___redArg(v_i_451_, v___x_466_, v___x_465_);
v___y_458_ = v___y_464_;
v___y_459_ = v___x_466_;
v___y_460_ = v___x_468_;
goto v___jp_457_;
}
else
{
lean_dec(v_i_451_);
v___y_458_ = v___y_464_;
v___y_459_ = v___x_466_;
v___y_460_ = v___x_465_;
goto v___jp_457_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex___boxed(lean_object* v_i_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lean_IR_Checker_markIndex(v_i_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_);
lean_dec(v_a_481_);
lean_dec_ref(v_a_480_);
lean_dec(v_a_479_);
lean_dec_ref(v_a_478_);
return v_res_483_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0(lean_object* v_00_u03b2_484_, lean_object* v_k_485_, lean_object* v_t_486_){
_start:
{
uint8_t v___x_487_; 
v___x_487_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___redArg(v_k_485_, v_t_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0___boxed(lean_object* v_00_u03b2_488_, lean_object* v_k_489_, lean_object* v_t_490_){
_start:
{
uint8_t v_res_491_; lean_object* v_r_492_; 
v_res_491_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_Checker_markIndex_spec__0(v_00_u03b2_488_, v_k_489_, v_t_490_);
lean_dec(v_t_490_);
lean_dec(v_k_489_);
v_r_492_ = lean_box(v_res_491_);
return v_r_492_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1(lean_object* v_00_u03b2_493_, lean_object* v_k_494_, lean_object* v_v_495_, lean_object* v_t_496_, lean_object* v_hl_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_Checker_markIndex_spec__1___redArg(v_k_494_, v_v_495_, v_t_496_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar(lean_object* v_x_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Lean_IR_Checker_markIndex(v_x_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar___boxed(lean_object* v_x_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Lean_IR_Checker_markVar(v_x_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_);
lean_dec(v_a_510_);
lean_dec_ref(v_a_509_);
lean_dec(v_a_508_);
lean_dec_ref(v_a_507_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP(lean_object* v_j_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Lean_IR_Checker_markIndex(v_j_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP___boxed(lean_object* v_j_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Lean_IR_Checker_markJP(v_j_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_);
lean_dec(v_a_524_);
lean_dec_ref(v_a_523_);
lean_dec(v_a_522_);
lean_dec_ref(v_a_521_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl(lean_object* v_c_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_){
_start:
{
lean_object* v___x_535_; lean_object* v_env_536_; lean_object* v_decls_537_; lean_object* v___x_538_; 
v___x_535_ = lean_st_ref_get(v_a_533_);
v_env_536_ = lean_ctor_get(v___x_535_, 0);
lean_inc_ref(v_env_536_);
lean_dec(v___x_535_);
v_decls_537_ = lean_ctor_get(v_a_530_, 2);
lean_inc(v_c_529_);
v___x_538_ = l_Lean_IR_findEnvDecl_x27(v_env_536_, v_c_529_, v_decls_537_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v___x_539_; uint8_t v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_539_ = ((lean_object*)(l_Lean_IR_Checker_getDecl___closed__0));
v___x_540_ = 1;
v___x_541_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_c_529_, v___x_540_);
v___x_542_ = lean_string_append(v___x_539_, v___x_541_);
lean_dec_ref(v___x_541_);
v___x_543_ = ((lean_object*)(l_Lean_IR_Checker_getDecl___closed__1));
v___x_544_ = lean_string_append(v___x_542_, v___x_543_);
v___x_545_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_544_, v_a_530_, v_a_531_, v_a_532_, v_a_533_);
return v___x_545_;
}
else
{
lean_object* v_val_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_553_; 
lean_dec(v_c_529_);
v_val_546_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_553_ == 0)
{
v___x_548_ = v___x_538_;
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_val_546_);
lean_dec(v___x_538_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_551_; 
if (v_isShared_549_ == 0)
{
lean_ctor_set_tag(v___x_548_, 0);
v___x_551_ = v___x_548_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_val_546_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl___boxed(lean_object* v_c_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_IR_Checker_getDecl(v_c_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_);
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
lean_dec(v_a_556_);
lean_dec_ref(v_a_555_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar(lean_object* v_x_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_){
_start:
{
uint8_t v___y_571_; lean_object* v_localCtx_582_; uint8_t v___x_583_; 
v_localCtx_582_ = lean_ctor_get(v_a_565_, 0);
v___x_583_ = l_Lean_IR_LocalContext_isLocalVar(v_localCtx_582_, v_x_564_);
if (v___x_583_ == 0)
{
uint8_t v___x_584_; 
v___x_584_ = l_Lean_IR_LocalContext_isParam(v_localCtx_582_, v_x_564_);
v___y_571_ = v___x_584_;
goto v___jp_570_;
}
else
{
v___y_571_ = v___x_583_;
goto v___jp_570_;
}
v___jp_570_:
{
if (v___y_571_ == 0)
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_572_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__0));
v___x_573_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__1));
v___x_574_ = l_Nat_reprFast(v_x_564_);
v___x_575_ = lean_string_append(v___x_573_, v___x_574_);
lean_dec_ref(v___x_574_);
v___x_576_ = lean_string_append(v___x_572_, v___x_575_);
lean_dec_ref(v___x_575_);
v___x_577_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v___x_578_ = lean_string_append(v___x_576_, v___x_577_);
v___x_579_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_578_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
return v___x_579_;
}
else
{
lean_object* v___x_580_; lean_object* v___x_581_; 
lean_dec(v_x_564_);
v___x_580_ = lean_box(0);
v___x_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
return v___x_581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar___boxed(lean_object* v_x_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Lean_IR_Checker_checkVar(v_x_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_);
lean_dec(v_a_589_);
lean_dec_ref(v_a_588_);
lean_dec(v_a_587_);
lean_dec_ref(v_a_586_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP(lean_object* v_j_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_){
_start:
{
lean_object* v_localCtx_600_; uint8_t v___x_601_; 
v_localCtx_600_ = lean_ctor_get(v_a_595_, 0);
v___x_601_ = l_Lean_IR_LocalContext_isJP(v_localCtx_600_, v_j_594_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_602_ = ((lean_object*)(l_Lean_IR_Checker_checkJP___closed__0));
v___x_603_ = ((lean_object*)(l_Lean_IR_Checker_checkJP___closed__1));
v___x_604_ = l_Nat_reprFast(v_j_594_);
v___x_605_ = lean_string_append(v___x_603_, v___x_604_);
lean_dec_ref(v___x_604_);
v___x_606_ = lean_string_append(v___x_602_, v___x_605_);
lean_dec_ref(v___x_605_);
v___x_607_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v___x_608_ = lean_string_append(v___x_606_, v___x_607_);
v___x_609_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_608_, v_a_595_, v_a_596_, v_a_597_, v_a_598_);
return v___x_609_;
}
else
{
lean_object* v___x_610_; lean_object* v___x_611_; 
lean_dec(v_j_594_);
v___x_610_ = lean_box(0);
v___x_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
return v___x_611_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP___boxed(lean_object* v_j_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_IR_Checker_checkJP(v_j_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_);
lean_dec(v_a_616_);
lean_dec_ref(v_a_615_);
lean_dec(v_a_614_);
lean_dec_ref(v_a_613_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg(lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_){
_start:
{
if (lean_obj_tag(v_a_619_) == 0)
{
lean_object* v_id_625_; lean_object* v___x_626_; 
v_id_625_ = lean_ctor_get(v_a_619_, 0);
lean_inc(v_id_625_);
lean_dec_ref_known(v_a_619_, 1);
v___x_626_ = l_Lean_IR_Checker_checkVar(v_id_625_, v_a_620_, v_a_621_, v_a_622_, v_a_623_);
return v___x_626_;
}
else
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = lean_box(0);
v___x_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
return v___x_628_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg___boxed(lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Lean_IR_Checker_checkArg(v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_);
lean_dec(v_a_633_);
lean_dec_ref(v_a_632_);
lean_dec(v_a_631_);
lean_dec_ref(v_a_630_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(lean_object* v_as_636_, size_t v_i_637_, size_t v_stop_638_, lean_object* v_b_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
uint8_t v___x_645_; 
v___x_645_ = lean_usize_dec_eq(v_i_637_, v_stop_638_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = lean_array_uget_borrowed(v_as_636_, v_i_637_);
lean_inc(v___x_646_);
v___x_647_ = l_Lean_IR_Checker_checkArg(v___x_646_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_a_648_; size_t v___x_649_; size_t v___x_650_; 
v_a_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc(v_a_648_);
lean_dec_ref_known(v___x_647_, 1);
v___x_649_ = ((size_t)1ULL);
v___x_650_ = lean_usize_add(v_i_637_, v___x_649_);
v_i_637_ = v___x_650_;
v_b_639_ = v_a_648_;
goto _start;
}
else
{
return v___x_647_;
}
}
else
{
lean_object* v___x_652_; 
v___x_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_652_, 0, v_b_639_);
return v___x_652_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0___boxed(lean_object* v_as_653_, lean_object* v_i_654_, lean_object* v_stop_655_, lean_object* v_b_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
size_t v_i_boxed_662_; size_t v_stop_boxed_663_; lean_object* v_res_664_; 
v_i_boxed_662_ = lean_unbox_usize(v_i_654_);
lean_dec(v_i_654_);
v_stop_boxed_663_ = lean_unbox_usize(v_stop_655_);
lean_dec(v_stop_655_);
v_res_664_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(v_as_653_, v_i_boxed_662_, v_stop_boxed_663_, v_b_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec_ref(v_as_653_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs(lean_object* v_as_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
v___x_671_ = lean_unsigned_to_nat(0u);
v___x_672_ = lean_array_get_size(v_as_665_);
v___x_673_ = lean_box(0);
v___x_674_ = lean_nat_dec_lt(v___x_671_, v___x_672_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; 
v___x_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_675_, 0, v___x_673_);
return v___x_675_;
}
else
{
uint8_t v___x_676_; 
v___x_676_ = lean_nat_dec_le(v___x_672_, v___x_672_);
if (v___x_676_ == 0)
{
if (v___x_674_ == 0)
{
lean_object* v___x_677_; 
v___x_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_673_);
return v___x_677_;
}
else
{
size_t v___x_678_; size_t v___x_679_; lean_object* v___x_680_; 
v___x_678_ = ((size_t)0ULL);
v___x_679_ = lean_usize_of_nat(v___x_672_);
v___x_680_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(v_as_665_, v___x_678_, v___x_679_, v___x_673_, v_a_666_, v_a_667_, v_a_668_, v_a_669_);
return v___x_680_;
}
}
else
{
size_t v___x_681_; size_t v___x_682_; lean_object* v___x_683_; 
v___x_681_ = ((size_t)0ULL);
v___x_682_ = lean_usize_of_nat(v___x_672_);
v___x_683_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkArgs_spec__0(v_as_665_, v___x_681_, v___x_682_, v___x_673_, v_a_666_, v_a_667_, v_a_668_, v_a_669_);
return v___x_683_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs___boxed(lean_object* v_as_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Lean_IR_Checker_checkArgs(v_as_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_);
lean_dec(v_a_688_);
lean_dec_ref(v_a_687_);
lean_dec(v_a_686_);
lean_dec_ref(v_a_685_);
lean_dec_ref(v_as_684_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes(lean_object* v_ty_u2081_692_, lean_object* v_ty_u2082_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_){
_start:
{
uint8_t v___x_699_; 
v___x_699_ = l_Lean_IR_instBEqIRType_beq(v_ty_u2081_692_, v_ty_u2082_693_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_700_ = ((lean_object*)(l_Lean_IR_Checker_checkEqTypes___closed__0));
v___x_701_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_700_, v_a_694_, v_a_695_, v_a_696_, v_a_697_);
return v___x_701_;
}
else
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = lean_box(0);
v___x_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
return v___x_703_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes___boxed(lean_object* v_ty_u2081_704_, lean_object* v_ty_u2082_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_IR_Checker_checkEqTypes(v_ty_u2081_704_, v_ty_u2082_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_);
lean_dec(v_a_709_);
lean_dec_ref(v_a_708_);
lean_dec(v_a_707_);
lean_dec_ref(v_a_706_);
lean_dec(v_ty_u2082_705_);
lean_dec(v_ty_u2081_704_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType(lean_object* v_ty_714_, lean_object* v_p_715_, lean_object* v_suffix_x3f_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_){
_start:
{
lean_object* v___x_722_; uint8_t v___x_723_; 
lean_inc(v_ty_714_);
v___x_722_ = lean_apply_1(v_p_715_, v_ty_714_);
v___x_723_ = lean_unbox(v___x_722_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v_msg_731_; 
v___x_724_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_725_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_714_);
v___x_726_ = l_Std_Format_defWidth;
v___x_727_ = lean_unsigned_to_nat(0u);
v___x_728_ = l_Std_Format_pretty(v___x_725_, v___x_726_, v___x_727_, v___x_727_);
v___x_729_ = lean_string_append(v___x_724_, v___x_728_);
lean_dec_ref(v___x_728_);
v___x_730_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_731_ = lean_string_append(v___x_729_, v___x_730_);
if (lean_obj_tag(v_suffix_x3f_716_) == 1)
{
lean_object* v_val_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v_msg_735_; lean_object* v___x_736_; 
v_val_732_ = lean_ctor_get(v_suffix_x3f_716_, 0);
v___x_733_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_734_ = lean_string_append(v_msg_731_, v___x_733_);
v_msg_735_ = lean_string_append(v___x_734_, v_val_732_);
v___x_736_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_735_, v_a_717_, v_a_718_, v_a_719_, v_a_720_);
return v___x_736_;
}
else
{
lean_object* v___x_737_; 
v___x_737_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_731_, v_a_717_, v_a_718_, v_a_719_, v_a_720_);
return v___x_737_;
}
}
else
{
lean_object* v___x_738_; lean_object* v___x_739_; 
lean_dec(v_ty_714_);
v___x_738_ = lean_box(0);
v___x_739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_739_, 0, v___x_738_);
return v___x_739_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType___boxed(lean_object* v_ty_740_, lean_object* v_p_741_, lean_object* v_suffix_x3f_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Lean_IR_Checker_checkType(v_ty_740_, v_p_741_, v_suffix_x3f_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_);
lean_dec(v_a_746_);
lean_dec_ref(v_a_745_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
lean_dec(v_suffix_x3f_742_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType(lean_object* v_ty_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_){
_start:
{
uint8_t v___x_756_; 
v___x_756_ = l_Lean_IR_IRType_isObj(v_ty_750_);
if (v___x_756_ == 0)
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v_msg_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v_msg_768_; lean_object* v___x_769_; 
v___x_757_ = ((lean_object*)(l_Lean_IR_Checker_checkObjType___closed__0));
v___x_758_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_759_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_750_);
v___x_760_ = l_Std_Format_defWidth;
v___x_761_ = lean_unsigned_to_nat(0u);
v___x_762_ = l_Std_Format_pretty(v___x_759_, v___x_760_, v___x_761_, v___x_761_);
v___x_763_ = lean_string_append(v___x_758_, v___x_762_);
lean_dec_ref(v___x_762_);
v___x_764_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_765_ = lean_string_append(v___x_763_, v___x_764_);
v___x_766_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_767_ = lean_string_append(v_msg_765_, v___x_766_);
v_msg_768_ = lean_string_append(v___x_767_, v___x_757_);
v___x_769_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_768_, v_a_751_, v_a_752_, v_a_753_, v_a_754_);
return v___x_769_;
}
else
{
lean_object* v___x_770_; lean_object* v___x_771_; 
lean_dec(v_ty_750_);
v___x_770_ = lean_box(0);
v___x_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
return v___x_771_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType___boxed(lean_object* v_ty_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lean_IR_Checker_checkObjType(v_ty_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
lean_dec(v_a_776_);
lean_dec_ref(v_a_775_);
lean_dec(v_a_774_);
lean_dec_ref(v_a_773_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType(lean_object* v_ty_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_){
_start:
{
uint8_t v___x_786_; 
v___x_786_ = l_Lean_IR_IRType_isScalar(v_ty_780_);
if (v___x_786_ == 0)
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v_msg_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v_msg_798_; lean_object* v___x_799_; 
v___x_787_ = ((lean_object*)(l_Lean_IR_Checker_checkScalarType___closed__0));
v___x_788_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_789_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_780_);
v___x_790_ = l_Std_Format_defWidth;
v___x_791_ = lean_unsigned_to_nat(0u);
v___x_792_ = l_Std_Format_pretty(v___x_789_, v___x_790_, v___x_791_, v___x_791_);
v___x_793_ = lean_string_append(v___x_788_, v___x_792_);
lean_dec_ref(v___x_792_);
v___x_794_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_795_ = lean_string_append(v___x_793_, v___x_794_);
v___x_796_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_797_ = lean_string_append(v_msg_795_, v___x_796_);
v_msg_798_ = lean_string_append(v___x_797_, v___x_787_);
v___x_799_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_798_, v_a_781_, v_a_782_, v_a_783_, v_a_784_);
return v___x_799_;
}
else
{
lean_object* v___x_800_; lean_object* v___x_801_; 
lean_dec(v_ty_780_);
v___x_800_ = lean_box(0);
v___x_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
return v___x_801_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType___boxed(lean_object* v_ty_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lean_IR_Checker_checkScalarType(v_ty_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType(lean_object* v_x_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_){
_start:
{
lean_object* v_localCtx_815_; lean_object* v___x_816_; 
v_localCtx_815_ = lean_ctor_get(v_a_810_, 0);
v___x_816_ = l_Lean_IR_LocalContext_getType(v_localCtx_815_, v_x_809_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_817_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__0));
v___x_818_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__1));
v___x_819_ = l_Nat_reprFast(v_x_809_);
v___x_820_ = lean_string_append(v___x_818_, v___x_819_);
lean_dec_ref(v___x_819_);
v___x_821_ = lean_string_append(v___x_817_, v___x_820_);
lean_dec_ref(v___x_820_);
v___x_822_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v___x_823_ = lean_string_append(v___x_821_, v___x_822_);
v___x_824_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_823_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
return v___x_824_;
}
else
{
lean_object* v_val_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_832_; 
lean_dec(v_x_809_);
v_val_825_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_832_ == 0)
{
v___x_827_ = v___x_816_;
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_val_825_);
lean_dec(v___x_816_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
lean_ctor_set_tag(v___x_827_, 0);
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_val_825_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType___boxed(lean_object* v_x_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lean_IR_Checker_getType(v_x_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_);
lean_dec(v_a_837_);
lean_dec_ref(v_a_836_);
lean_dec(v_a_835_);
lean_dec_ref(v_a_834_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType(lean_object* v_x_840_, lean_object* v_p_841_, lean_object* v_suffix_x3f_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l_Lean_IR_Checker_getType(v_x_840_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_873_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_873_ == 0)
{
v___x_851_ = v___x_848_;
v_isShared_852_ = v_isSharedCheck_873_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_848_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_873_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_853_; uint8_t v___x_854_; 
lean_inc(v_a_849_);
v___x_853_ = lean_apply_1(v_p_841_, v_a_849_);
v___x_854_ = lean_unbox(v___x_853_);
if (v___x_854_ == 0)
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v_msg_862_; 
lean_del_object(v___x_851_);
v___x_855_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_856_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_849_);
v___x_857_ = l_Std_Format_defWidth;
v___x_858_ = lean_unsigned_to_nat(0u);
v___x_859_ = l_Std_Format_pretty(v___x_856_, v___x_857_, v___x_858_, v___x_858_);
v___x_860_ = lean_string_append(v___x_855_, v___x_859_);
lean_dec_ref(v___x_859_);
v___x_861_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_862_ = lean_string_append(v___x_860_, v___x_861_);
if (lean_obj_tag(v_suffix_x3f_842_) == 1)
{
lean_object* v_val_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v_msg_866_; lean_object* v___x_867_; 
v_val_863_ = lean_ctor_get(v_suffix_x3f_842_, 0);
v___x_864_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_865_ = lean_string_append(v_msg_862_, v___x_864_);
v_msg_866_ = lean_string_append(v___x_865_, v_val_863_);
v___x_867_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_866_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
return v___x_867_;
}
else
{
lean_object* v___x_868_; 
v___x_868_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_862_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
return v___x_868_;
}
}
else
{
lean_object* v___x_869_; lean_object* v___x_871_; 
lean_dec(v_a_849_);
v___x_869_ = lean_box(0);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 0, v___x_869_);
v___x_871_ = v___x_851_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_869_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
else
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_881_; 
lean_dec_ref(v_p_841_);
v_a_874_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_881_ == 0)
{
v___x_876_ = v___x_848_;
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_848_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_879_; 
if (v_isShared_877_ == 0)
{
v___x_879_ = v___x_876_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_a_874_);
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
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType___boxed(lean_object* v_x_882_, lean_object* v_p_883_, lean_object* v_suffix_x3f_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Lean_IR_Checker_checkVarType(v_x_882_, v_p_883_, v_suffix_x3f_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_);
lean_dec(v_a_888_);
lean_dec_ref(v_a_887_);
lean_dec(v_a_886_);
lean_dec_ref(v_a_885_);
lean_dec(v_suffix_x3f_884_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar(lean_object* v_x_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = l_Lean_IR_Checker_getType(v_x_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_920_; 
v_a_898_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_920_ == 0)
{
v___x_900_ = v___x_897_;
v_isShared_901_ = v_isSharedCheck_920_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_897_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_920_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
uint8_t v___x_902_; 
v___x_902_ = l_Lean_IR_IRType_isObj(v_a_898_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v_msg_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v_msg_914_; lean_object* v___x_915_; 
lean_del_object(v___x_900_);
v___x_903_ = ((lean_object*)(l_Lean_IR_Checker_checkObjType___closed__0));
v___x_904_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_905_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_898_);
v___x_906_ = l_Std_Format_defWidth;
v___x_907_ = lean_unsigned_to_nat(0u);
v___x_908_ = l_Std_Format_pretty(v___x_905_, v___x_906_, v___x_907_, v___x_907_);
v___x_909_ = lean_string_append(v___x_904_, v___x_908_);
lean_dec_ref(v___x_908_);
v___x_910_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_911_ = lean_string_append(v___x_909_, v___x_910_);
v___x_912_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_913_ = lean_string_append(v_msg_911_, v___x_912_);
v_msg_914_ = lean_string_append(v___x_913_, v___x_903_);
v___x_915_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_914_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
return v___x_915_;
}
else
{
lean_object* v___x_916_; lean_object* v___x_918_; 
lean_dec(v_a_898_);
v___x_916_ = lean_box(0);
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 0, v___x_916_);
v___x_918_ = v___x_900_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_916_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
else
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_928_; 
v_a_921_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_928_ == 0)
{
v___x_923_ = v___x_897_;
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_897_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_926_; 
if (v_isShared_924_ == 0)
{
v___x_926_ = v___x_923_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_a_921_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar___boxed(lean_object* v_x_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Lean_IR_Checker_checkObjVar(v_x_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_);
lean_dec(v_a_933_);
lean_dec_ref(v_a_932_);
lean_dec(v_a_931_);
lean_dec_ref(v_a_930_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar(lean_object* v_x_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = l_Lean_IR_Checker_getType(v_x_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_965_; 
v_a_943_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_965_ == 0)
{
v___x_945_ = v___x_942_;
v_isShared_946_ = v_isSharedCheck_965_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___x_942_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_965_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
uint8_t v___x_947_; 
v___x_947_ = l_Lean_IR_IRType_isScalar(v_a_943_);
if (v___x_947_ == 0)
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v_msg_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v_msg_959_; lean_object* v___x_960_; 
lean_del_object(v___x_945_);
v___x_948_ = ((lean_object*)(l_Lean_IR_Checker_checkScalarType___closed__0));
v___x_949_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_950_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_943_);
v___x_951_ = l_Std_Format_defWidth;
v___x_952_ = lean_unsigned_to_nat(0u);
v___x_953_ = l_Std_Format_pretty(v___x_950_, v___x_951_, v___x_952_, v___x_952_);
v___x_954_ = lean_string_append(v___x_949_, v___x_953_);
lean_dec_ref(v___x_953_);
v___x_955_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_956_ = lean_string_append(v___x_954_, v___x_955_);
v___x_957_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__1));
v___x_958_ = lean_string_append(v_msg_956_, v___x_957_);
v_msg_959_ = lean_string_append(v___x_958_, v___x_948_);
v___x_960_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_959_, v_a_937_, v_a_938_, v_a_939_, v_a_940_);
return v___x_960_;
}
else
{
lean_object* v___x_961_; lean_object* v___x_963_; 
lean_dec(v_a_943_);
v___x_961_ = lean_box(0);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 0, v___x_961_);
v___x_963_ = v___x_945_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_961_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
else
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
v_a_966_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_973_ == 0)
{
v___x_968_ = v___x_942_;
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_942_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
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
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar___boxed(lean_object* v_x_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lean_IR_Checker_checkScalarVar(v_x_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_);
lean_dec(v_a_978_);
lean_dec_ref(v_a_977_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp(lean_object* v_c_985_, lean_object* v_ys_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_){
_start:
{
lean_object* v___x_992_; 
lean_inc(v_c_985_);
v___x_992_ = l_Lean_IR_Checker_getDecl(v_c_985_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; uint8_t v___x_997_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
lean_inc(v_a_993_);
lean_dec_ref_known(v___x_992_, 1);
v___x_994_ = lean_array_get_size(v_ys_986_);
v___x_995_ = l_Lean_IR_Decl_params(v_a_993_);
lean_dec(v_a_993_);
v___x_996_ = lean_array_get_size(v___x_995_);
lean_dec_ref(v___x_995_);
v___x_997_ = lean_nat_dec_eq(v___x_994_, v___x_996_);
if (v___x_997_ == 0)
{
lean_object* v___x_998_; uint8_t v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_998_ = ((lean_object*)(l_Lean_IR_Checker_checkFullApp___closed__0));
v___x_999_ = 1;
v___x_1000_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_c_985_, v___x_999_);
v___x_1001_ = lean_string_append(v___x_998_, v___x_1000_);
lean_dec_ref(v___x_1000_);
v___x_1002_ = ((lean_object*)(l_Lean_IR_Checker_checkFullApp___closed__1));
v___x_1003_ = lean_string_append(v___x_1001_, v___x_1002_);
v___x_1004_ = l_Nat_reprFast(v___x_994_);
v___x_1005_ = lean_string_append(v___x_1003_, v___x_1004_);
lean_dec_ref(v___x_1004_);
v___x_1006_ = ((lean_object*)(l_Lean_IR_Checker_checkFullApp___closed__2));
v___x_1007_ = lean_string_append(v___x_1005_, v___x_1006_);
v___x_1008_ = l_Nat_reprFast(v___x_996_);
v___x_1009_ = lean_string_append(v___x_1007_, v___x_1008_);
lean_dec_ref(v___x_1008_);
v___x_1010_ = ((lean_object*)(l_Lean_IR_Checker_checkFullApp___closed__3));
v___x_1011_ = lean_string_append(v___x_1009_, v___x_1010_);
v___x_1012_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1011_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
return v___x_1012_;
}
else
{
lean_object* v___x_1013_; 
lean_dec(v_c_985_);
v___x_1013_ = l_Lean_IR_Checker_checkArgs(v_ys_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
return v___x_1013_;
}
}
else
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
lean_dec(v_c_985_);
v_a_1014_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_992_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_992_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp___boxed(lean_object* v_c_1022_, lean_object* v_ys_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_Lean_IR_Checker_checkFullApp(v_c_1022_, v_ys_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_);
lean_dec(v_a_1027_);
lean_dec_ref(v_a_1026_);
lean_dec(v_a_1025_);
lean_dec_ref(v_a_1024_);
lean_dec_ref(v_ys_1023_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp(lean_object* v_c_1033_, lean_object* v_ys_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_){
_start:
{
lean_object* v___x_1040_; 
lean_inc(v_c_1033_);
v___x_1040_ = l_Lean_IR_Checker_getDecl(v_c_1033_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v_a_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; uint8_t v___x_1045_; 
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
lean_inc(v_a_1041_);
lean_dec_ref_known(v___x_1040_, 1);
v___x_1042_ = lean_array_get_size(v_ys_1034_);
v___x_1043_ = l_Lean_IR_Decl_params(v_a_1041_);
lean_dec(v_a_1041_);
v___x_1044_ = lean_array_get_size(v___x_1043_);
lean_dec_ref(v___x_1043_);
v___x_1045_ = lean_nat_dec_lt(v___x_1042_, v___x_1044_);
if (v___x_1045_ == 0)
{
lean_object* v___x_1046_; uint8_t v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1046_ = ((lean_object*)(l_Lean_IR_Checker_checkPartialApp___closed__0));
v___x_1047_ = 1;
v___x_1048_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_c_1033_, v___x_1047_);
v___x_1049_ = lean_string_append(v___x_1046_, v___x_1048_);
lean_dec_ref(v___x_1048_);
v___x_1050_ = ((lean_object*)(l_Lean_IR_Checker_checkPartialApp___closed__1));
v___x_1051_ = lean_string_append(v___x_1049_, v___x_1050_);
v___x_1052_ = l_Nat_reprFast(v___x_1042_);
v___x_1053_ = lean_string_append(v___x_1051_, v___x_1052_);
lean_dec_ref(v___x_1052_);
v___x_1054_ = ((lean_object*)(l_Lean_IR_Checker_checkPartialApp___closed__2));
v___x_1055_ = lean_string_append(v___x_1053_, v___x_1054_);
v___x_1056_ = l_Nat_reprFast(v___x_1044_);
v___x_1057_ = lean_string_append(v___x_1055_, v___x_1056_);
lean_dec_ref(v___x_1056_);
v___x_1058_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1057_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_);
return v___x_1058_;
}
else
{
lean_object* v___x_1059_; 
lean_dec(v_c_1033_);
v___x_1059_ = l_Lean_IR_Checker_checkArgs(v_ys_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_);
return v___x_1059_;
}
}
else
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1067_; 
lean_dec(v_c_1033_);
v_a_1060_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1062_ = v___x_1040_;
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1040_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1063_ == 0)
{
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_a_1060_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp___boxed(lean_object* v_c_1068_, lean_object* v_ys_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Lean_IR_Checker_checkPartialApp(v_c_1068_, v_ys_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_);
lean_dec(v_a_1073_);
lean_dec_ref(v_a_1072_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
lean_dec_ref(v_ys_1069_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr(lean_object* v_ty_1083_, lean_object* v_e_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_){
_start:
{
switch(lean_obj_tag(v_e_1084_))
{
case 0:
{
lean_object* v_i_1090_; lean_object* v_ys_1091_; lean_object* v___y_1093_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v_name_1102_; lean_object* v_cidx_1103_; lean_object* v_size_1104_; lean_object* v_usize_1105_; lean_object* v_ssize_1106_; lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v___x_1136_; uint8_t v___x_1137_; 
v_i_1090_ = lean_ctor_get(v_e_1084_, 0);
lean_inc_ref(v_i_1090_);
v_ys_1091_ = lean_ctor_get(v_e_1084_, 1);
lean_inc_ref(v_ys_1091_);
lean_dec_ref_known(v_e_1084_, 2);
v_name_1102_ = lean_ctor_get(v_i_1090_, 0);
v_cidx_1103_ = lean_ctor_get(v_i_1090_, 1);
v_size_1104_ = lean_ctor_get(v_i_1090_, 2);
v_usize_1105_ = lean_ctor_get(v_i_1090_, 3);
v_ssize_1106_ = lean_ctor_get(v_i_1090_, 4);
v___x_1136_ = l_Lean_IR_Checker_maxCtorTag;
v___x_1137_ = lean_nat_dec_lt(v___x_1136_, v_cidx_1103_);
if (v___x_1137_ == 0)
{
v___y_1124_ = v_a_1085_;
v___y_1125_ = v_a_1086_;
v___y_1126_ = v_a_1087_;
v___y_1127_ = v_a_1088_;
goto v___jp_1123_;
}
else
{
uint8_t v___x_1138_; 
v___x_1138_ = l_Lean_IR_CtorInfo_isRef(v_i_1090_);
if (v___x_1138_ == 0)
{
v___y_1124_ = v_a_1085_;
v___y_1125_ = v_a_1086_;
v___y_1126_ = v_a_1087_;
v___y_1127_ = v_a_1088_;
goto v___jp_1123_;
}
else
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
lean_inc(v_name_1102_);
lean_dec_ref(v_ys_1091_);
lean_dec_ref(v_i_1090_);
lean_dec(v_ty_1083_);
v___x_1139_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__3));
v___x_1140_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1102_, v___x_1138_);
v___x_1141_ = lean_string_append(v___x_1139_, v___x_1140_);
lean_dec_ref(v___x_1140_);
v___x_1142_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__4));
v___x_1143_ = lean_string_append(v___x_1141_, v___x_1142_);
v___x_1144_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1143_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
return v___x_1144_;
}
}
v___jp_1092_:
{
uint8_t v___x_1097_; 
v___x_1097_ = l_Lean_IR_CtorInfo_isRef(v_i_1090_);
lean_dec_ref(v_i_1090_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
lean_dec_ref(v_ys_1091_);
lean_dec(v_ty_1083_);
v___x_1098_ = lean_box(0);
v___x_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
return v___x_1099_;
}
else
{
lean_object* v___x_1100_; 
v___x_1100_ = l_Lean_IR_Checker_checkObjType(v_ty_1083_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_object* v___x_1101_; 
lean_dec_ref_known(v___x_1100_, 1);
v___x_1101_ = l_Lean_IR_Checker_checkArgs(v_ys_1091_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_);
lean_dec_ref(v_ys_1091_);
return v___x_1101_;
}
else
{
lean_dec_ref(v_ys_1091_);
return v___x_1100_;
}
}
}
v___jp_1107_:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; uint8_t v___x_1116_; 
v___x_1112_ = l_Lean_IR_Checker_maxCtorScalarsSize;
v___x_1113_ = l_Lean_IR_Checker_usizeSize;
v___x_1114_ = lean_nat_mul(v_usize_1105_, v___x_1113_);
v___x_1115_ = lean_nat_add(v_ssize_1106_, v___x_1114_);
lean_dec(v___x_1114_);
v___x_1116_ = lean_nat_dec_lt(v___x_1112_, v___x_1115_);
lean_dec(v___x_1115_);
if (v___x_1116_ == 0)
{
v___y_1093_ = v___y_1108_;
v___y_1094_ = v___y_1109_;
v___y_1095_ = v___y_1110_;
v___y_1096_ = v___y_1111_;
goto v___jp_1092_;
}
else
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
lean_inc(v_name_1102_);
lean_dec_ref(v_ys_1091_);
lean_dec_ref(v_i_1090_);
lean_dec(v_ty_1083_);
v___x_1117_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__0));
v___x_1118_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1102_, v___x_1116_);
v___x_1119_ = lean_string_append(v___x_1117_, v___x_1118_);
lean_dec_ref(v___x_1118_);
v___x_1120_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__1));
v___x_1121_ = lean_string_append(v___x_1119_, v___x_1120_);
v___x_1122_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1121_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
return v___x_1122_;
}
}
v___jp_1123_:
{
lean_object* v___x_1128_; uint8_t v___x_1129_; 
v___x_1128_ = l_Lean_IR_Checker_maxCtorFields;
v___x_1129_ = lean_nat_dec_lt(v___x_1128_, v_size_1104_);
if (v___x_1129_ == 0)
{
v___y_1108_ = v___y_1124_;
v___y_1109_ = v___y_1125_;
v___y_1110_ = v___y_1126_;
v___y_1111_ = v___y_1127_;
goto v___jp_1107_;
}
else
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
lean_inc(v_name_1102_);
lean_dec_ref(v_ys_1091_);
lean_dec_ref(v_i_1090_);
lean_dec(v_ty_1083_);
v___x_1130_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__0));
v___x_1131_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1102_, v___x_1129_);
v___x_1132_ = lean_string_append(v___x_1130_, v___x_1131_);
lean_dec_ref(v___x_1131_);
v___x_1133_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__2));
v___x_1134_ = lean_string_append(v___x_1132_, v___x_1133_);
v___x_1135_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1134_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
return v___x_1135_;
}
}
}
case 1:
{
lean_object* v_x_1145_; lean_object* v___x_1146_; 
v_x_1145_ = lean_ctor_get(v_e_1084_, 1);
lean_inc(v_x_1145_);
lean_dec_ref_known(v_e_1084_, 2);
v___x_1146_ = l_Lean_IR_Checker_checkObjVar(v_x_1145_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v___x_1147_; 
lean_dec_ref_known(v___x_1146_, 1);
v___x_1147_ = l_Lean_IR_Checker_checkObjType(v_ty_1083_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
return v___x_1147_;
}
else
{
lean_dec(v_ty_1083_);
return v___x_1146_;
}
}
case 2:
{
lean_object* v_x_1148_; lean_object* v_ys_1149_; lean_object* v___x_1150_; 
v_x_1148_ = lean_ctor_get(v_e_1084_, 0);
lean_inc(v_x_1148_);
v_ys_1149_ = lean_ctor_get(v_e_1084_, 2);
lean_inc_ref(v_ys_1149_);
lean_dec_ref_known(v_e_1084_, 3);
v___x_1150_ = l_Lean_IR_Checker_checkObjVar(v_x_1148_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_object* v___x_1151_; 
lean_dec_ref_known(v___x_1150_, 1);
v___x_1151_ = l_Lean_IR_Checker_checkArgs(v_ys_1149_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
lean_dec_ref(v_ys_1149_);
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v___x_1152_; 
lean_dec_ref_known(v___x_1151_, 1);
v___x_1152_ = l_Lean_IR_Checker_checkObjType(v_ty_1083_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
return v___x_1152_;
}
else
{
lean_dec(v_ty_1083_);
return v___x_1151_;
}
}
else
{
lean_dec_ref(v_ys_1149_);
lean_dec(v_ty_1083_);
return v___x_1150_;
}
}
case 3:
{
lean_object* v_i_1153_; lean_object* v_x_1154_; lean_object* v___x_1155_; 
v_i_1153_ = lean_ctor_get(v_e_1084_, 0);
lean_inc(v_i_1153_);
v_x_1154_ = lean_ctor_get(v_e_1084_, 1);
lean_inc(v_x_1154_);
lean_dec_ref_known(v_e_1084_, 2);
v___x_1155_ = l_Lean_IR_Checker_getType(v_x_1154_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1201_; 
v_a_1156_ = lean_ctor_get(v___x_1155_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1158_ = v___x_1155_;
v_isShared_1159_ = v_isSharedCheck_1201_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1155_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1201_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
switch(lean_obj_tag(v_a_1156_))
{
case 7:
{
lean_object* v___x_1160_; 
lean_del_object(v___x_1158_);
lean_dec(v_i_1153_);
v___x_1160_ = l_Lean_IR_Checker_checkObjType(v_ty_1083_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
return v___x_1160_;
}
case 8:
{
lean_object* v___x_1161_; 
lean_del_object(v___x_1158_);
lean_dec(v_i_1153_);
v___x_1161_ = l_Lean_IR_Checker_checkObjType(v_ty_1083_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
return v___x_1161_;
}
case 10:
{
lean_object* v_types_1162_; lean_object* v___x_1163_; uint8_t v___x_1164_; 
v_types_1162_ = lean_ctor_get(v_a_1156_, 1);
lean_inc_ref(v_types_1162_);
lean_dec_ref_known(v_a_1156_, 2);
v___x_1163_ = lean_array_get_size(v_types_1162_);
v___x_1164_ = lean_nat_dec_lt(v_i_1153_, v___x_1163_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
lean_dec_ref(v_types_1162_);
lean_del_object(v___x_1158_);
lean_dec(v_i_1153_);
lean_dec(v_ty_1083_);
v___x_1165_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__5));
v___x_1166_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1165_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
return v___x_1166_;
}
else
{
lean_object* v___x_1167_; uint8_t v___x_1168_; 
v___x_1167_ = lean_array_fget(v_types_1162_, v_i_1153_);
lean_dec(v_i_1153_);
lean_dec_ref(v_types_1162_);
v___x_1168_ = l_Lean_IR_instBEqIRType_beq(v___x_1167_, v_ty_1083_);
lean_dec(v_ty_1083_);
lean_dec(v___x_1167_);
if (v___x_1168_ == 0)
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
lean_del_object(v___x_1158_);
v___x_1169_ = ((lean_object*)(l_Lean_IR_Checker_checkEqTypes___closed__0));
v___x_1170_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1169_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
return v___x_1170_;
}
else
{
lean_object* v___x_1171_; lean_object* v___x_1173_; 
v___x_1171_ = lean_box(0);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 0, v___x_1171_);
v___x_1173_ = v___x_1158_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1171_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
case 11:
{
lean_object* v_types_1175_; lean_object* v___x_1176_; uint8_t v___x_1177_; 
v_types_1175_ = lean_ctor_get(v_a_1156_, 1);
lean_inc_ref(v_types_1175_);
lean_dec_ref_known(v_a_1156_, 2);
v___x_1176_ = lean_array_get_size(v_types_1175_);
v___x_1177_ = lean_nat_dec_lt(v_i_1153_, v___x_1176_);
if (v___x_1177_ == 0)
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
lean_dec_ref(v_types_1175_);
lean_del_object(v___x_1158_);
lean_dec(v_i_1153_);
lean_dec(v_ty_1083_);
v___x_1178_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__5));
v___x_1179_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1178_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
return v___x_1179_;
}
else
{
lean_object* v___x_1180_; uint8_t v___x_1181_; 
v___x_1180_ = lean_array_fget(v_types_1175_, v_i_1153_);
lean_dec(v_i_1153_);
lean_dec_ref(v_types_1175_);
v___x_1181_ = l_Lean_IR_instBEqIRType_beq(v___x_1180_, v_ty_1083_);
lean_dec(v_ty_1083_);
lean_dec(v___x_1180_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
lean_del_object(v___x_1158_);
v___x_1182_ = ((lean_object*)(l_Lean_IR_Checker_checkEqTypes___closed__0));
v___x_1183_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1182_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
return v___x_1183_;
}
else
{
lean_object* v___x_1184_; lean_object* v___x_1186_; 
v___x_1184_ = lean_box(0);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 0, v___x_1184_);
v___x_1186_ = v___x_1158_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1184_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
case 12:
{
lean_object* v___x_1188_; lean_object* v___x_1190_; 
lean_dec(v_i_1153_);
lean_dec(v_ty_1083_);
v___x_1188_ = lean_box(0);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 0, v___x_1188_);
v___x_1190_ = v___x_1158_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___x_1188_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
default: 
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
lean_del_object(v___x_1158_);
lean_dec(v_i_1153_);
lean_dec(v_ty_1083_);
v___x_1192_ = ((lean_object*)(l_Lean_IR_Checker_checkExpr___closed__6));
v___x_1193_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_1156_);
v___x_1194_ = l_Std_Format_defWidth;
v___x_1195_ = lean_unsigned_to_nat(0u);
v___x_1196_ = l_Std_Format_pretty(v___x_1193_, v___x_1194_, v___x_1195_, v___x_1195_);
v___x_1197_ = lean_string_append(v___x_1192_, v___x_1196_);
lean_dec_ref(v___x_1196_);
v___x_1198_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v___x_1199_ = lean_string_append(v___x_1197_, v___x_1198_);
v___x_1200_ = l_Lean_IR_Checker_throwCheckerError___redArg(v___x_1199_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
return v___x_1200_;
}
}
}
}
else
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1209_; 
lean_dec(v_i_1153_);
lean_dec(v_ty_1083_);
v_a_1202_ = lean_ctor_get(v___x_1155_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1204_ = v___x_1155_;
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1155_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1207_; 
if (v_isShared_1205_ == 0)
{
v___x_1207_ = v___x_1204_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_a_1202_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
case 4:
{
lean_object* v_x_1210_; lean_object* v___x_1211_; 
v_x_1210_ = lean_ctor_get(v_e_1084_, 1);
lean_inc(v_x_1210_);
lean_dec_ref_known(v_e_1084_, 2);
v___x_1211_ = l_Lean_IR_Checker_checkObjVar(v_x_1210_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1230_; 
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1230_ == 0)
{
lean_object* v_unused_1231_; 
v_unused_1231_ = lean_ctor_get(v___x_1211_, 0);
lean_dec(v_unused_1231_);
v___x_1213_ = v___x_1211_;
v_isShared_1214_ = v_isSharedCheck_1230_;
goto v_resetjp_1212_;
}
else
{
lean_dec(v___x_1211_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1230_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1215_; uint8_t v___x_1216_; 
v___x_1215_ = lean_box(5);
v___x_1216_ = l_Lean_IR_instBEqIRType_beq(v_ty_1083_, v___x_1215_);
if (v___x_1216_ == 0)
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v_msg_1224_; lean_object* v___x_1225_; 
lean_del_object(v___x_1213_);
v___x_1217_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_1218_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_1083_);
v___x_1219_ = l_Std_Format_defWidth;
v___x_1220_ = lean_unsigned_to_nat(0u);
v___x_1221_ = l_Std_Format_pretty(v___x_1218_, v___x_1219_, v___x_1220_, v___x_1220_);
v___x_1222_ = lean_string_append(v___x_1217_, v___x_1221_);
lean_dec_ref(v___x_1221_);
v___x_1223_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_1224_ = lean_string_append(v___x_1222_, v___x_1223_);
v___x_1225_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_1224_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
return v___x_1225_;
}
else
{
lean_object* v___x_1226_; lean_object* v___x_1228_; 
lean_dec(v_ty_1083_);
v___x_1226_ = lean_box(0);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 0, v___x_1226_);
v___x_1228_ = v___x_1213_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1226_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
else
{
lean_dec(v_ty_1083_);
return v___x_1211_;
}
}
case 5:
{
lean_object* v_x_1232_; lean_object* v___x_1233_; 
v_x_1232_ = lean_ctor_get(v_e_1084_, 2);
lean_inc(v_x_1232_);
lean_dec_ref_known(v_e_1084_, 3);
v___x_1233_ = l_Lean_IR_Checker_checkObjVar(v_x_1232_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_object* v___x_1234_; 
lean_dec_ref_known(v___x_1233_, 1);
v___x_1234_ = l_Lean_IR_Checker_checkScalarType(v_ty_1083_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
return v___x_1234_;
}
else
{
lean_dec(v_ty_1083_);
return v___x_1233_;
}
}
case 6:
{
lean_object* v_c_1235_; lean_object* v_ys_1236_; lean_object* v___x_1237_; 
lean_dec(v_ty_1083_);
v_c_1235_ = lean_ctor_get(v_e_1084_, 0);
lean_inc(v_c_1235_);
v_ys_1236_ = lean_ctor_get(v_e_1084_, 1);
lean_inc_ref(v_ys_1236_);
lean_dec_ref_known(v_e_1084_, 2);
v___x_1237_ = l_Lean_IR_Checker_checkFullApp(v_c_1235_, v_ys_1236_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
lean_dec_ref(v_ys_1236_);
return v___x_1237_;
}
case 7:
{
lean_object* v_c_1238_; lean_object* v_ys_1239_; lean_object* v___x_1240_; 
v_c_1238_ = lean_ctor_get(v_e_1084_, 0);
lean_inc(v_c_1238_);
v_ys_1239_ = lean_ctor_get(v_e_1084_, 1);
lean_inc_ref(v_ys_1239_);
lean_dec_ref_known(v_e_1084_, 2);
v___x_1240_ = l_Lean_IR_Checker_checkPartialApp(v_c_1238_, v_ys_1239_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
lean_dec_ref(v_ys_1239_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v___x_1241_; 
lean_dec_ref_known(v___x_1240_, 1);
v___x_1241_ = l_Lean_IR_Checker_checkObjType(v_ty_1083_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
return v___x_1241_;
}
else
{
lean_dec(v_ty_1083_);
return v___x_1240_;
}
}
case 8:
{
lean_object* v_x_1242_; lean_object* v_ys_1243_; lean_object* v___x_1244_; 
v_x_1242_ = lean_ctor_get(v_e_1084_, 0);
lean_inc(v_x_1242_);
v_ys_1243_ = lean_ctor_get(v_e_1084_, 1);
lean_inc_ref(v_ys_1243_);
lean_dec_ref_known(v_e_1084_, 2);
v___x_1244_ = l_Lean_IR_Checker_checkObjVar(v_x_1242_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v___x_1245_; 
lean_dec_ref_known(v___x_1244_, 1);
v___x_1245_ = l_Lean_IR_Checker_checkArgs(v_ys_1243_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
lean_dec_ref(v_ys_1243_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v___x_1246_; 
lean_dec_ref_known(v___x_1245_, 1);
v___x_1246_ = l_Lean_IR_Checker_checkObjType(v_ty_1083_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
return v___x_1246_;
}
else
{
lean_dec(v_ty_1083_);
return v___x_1245_;
}
}
else
{
lean_dec_ref(v_ys_1243_);
lean_dec(v_ty_1083_);
return v___x_1244_;
}
}
case 9:
{
lean_object* v_ty_1247_; lean_object* v_x_1248_; lean_object* v___x_1249_; 
v_ty_1247_ = lean_ctor_get(v_e_1084_, 0);
lean_inc(v_ty_1247_);
v_x_1248_ = lean_ctor_get(v_e_1084_, 1);
lean_inc(v_x_1248_);
lean_dec_ref_known(v_e_1084_, 2);
v___x_1249_ = l_Lean_IR_Checker_checkObjType(v_ty_1083_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v___x_1250_; 
lean_dec_ref_known(v___x_1249_, 1);
lean_inc(v_x_1248_);
v___x_1250_ = l_Lean_IR_Checker_checkScalarVar(v_x_1248_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_object* v___x_1251_; 
lean_dec_ref_known(v___x_1250_, 1);
v___x_1251_ = l_Lean_IR_Checker_getType(v_x_1248_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1270_; 
v_a_1252_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1254_ = v___x_1251_;
v_isShared_1255_ = v_isSharedCheck_1270_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v___x_1251_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1270_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
uint8_t v___x_1256_; 
v___x_1256_ = l_Lean_IR_instBEqIRType_beq(v_a_1252_, v_ty_1247_);
lean_dec(v_ty_1247_);
if (v___x_1256_ == 0)
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v_msg_1264_; lean_object* v___x_1265_; 
lean_del_object(v___x_1254_);
v___x_1257_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_1258_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_1252_);
v___x_1259_ = l_Std_Format_defWidth;
v___x_1260_ = lean_unsigned_to_nat(0u);
v___x_1261_ = l_Std_Format_pretty(v___x_1258_, v___x_1259_, v___x_1260_, v___x_1260_);
v___x_1262_ = lean_string_append(v___x_1257_, v___x_1261_);
lean_dec_ref(v___x_1261_);
v___x_1263_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_1264_ = lean_string_append(v___x_1262_, v___x_1263_);
v___x_1265_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_1264_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
return v___x_1265_;
}
else
{
lean_object* v___x_1266_; lean_object* v___x_1268_; 
lean_dec(v_a_1252_);
v___x_1266_ = lean_box(0);
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 0, v___x_1266_);
v___x_1268_ = v___x_1254_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v___x_1266_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
}
else
{
lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1278_; 
lean_dec(v_ty_1247_);
v_a_1271_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1273_ = v___x_1251_;
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1251_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1276_; 
if (v_isShared_1274_ == 0)
{
v___x_1276_ = v___x_1273_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_a_1271_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
}
else
{
lean_dec(v_x_1248_);
lean_dec(v_ty_1247_);
return v___x_1250_;
}
}
else
{
lean_dec(v_x_1248_);
lean_dec(v_ty_1247_);
return v___x_1249_;
}
}
case 10:
{
lean_object* v_x_1279_; lean_object* v___x_1280_; 
v_x_1279_ = lean_ctor_get(v_e_1084_, 0);
lean_inc(v_x_1279_);
lean_dec_ref_known(v_e_1084_, 1);
v___x_1280_ = l_Lean_IR_Checker_checkScalarType(v_ty_1083_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v___x_1281_; 
lean_dec_ref_known(v___x_1280_, 1);
v___x_1281_ = l_Lean_IR_Checker_checkObjVar(v_x_1279_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
return v___x_1281_;
}
else
{
lean_dec(v_x_1279_);
return v___x_1280_;
}
}
case 11:
{
lean_object* v_v_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1291_; 
v_v_1282_ = lean_ctor_get(v_e_1084_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v_e_1084_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1284_ = v_e_1084_;
v_isShared_1285_ = v_isSharedCheck_1291_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_v_1282_);
lean_dec(v_e_1084_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1291_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
if (lean_obj_tag(v_v_1282_) == 1)
{
lean_object* v___x_1286_; 
lean_dec_ref_known(v_v_1282_, 1);
lean_del_object(v___x_1284_);
v___x_1286_ = l_Lean_IR_Checker_checkObjType(v_ty_1083_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
return v___x_1286_;
}
else
{
lean_object* v___x_1287_; lean_object* v___x_1289_; 
lean_dec_ref(v_v_1282_);
lean_dec(v_ty_1083_);
v___x_1287_ = lean_box(0);
if (v_isShared_1285_ == 0)
{
lean_ctor_set_tag(v___x_1284_, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1287_);
v___x_1289_ = v___x_1284_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1287_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
default: 
{
lean_object* v_x_1292_; lean_object* v___x_1293_; 
v_x_1292_ = lean_ctor_get(v_e_1084_, 0);
lean_inc(v_x_1292_);
lean_dec_ref_known(v_e_1084_, 1);
v___x_1293_ = l_Lean_IR_Checker_checkObjVar(v_x_1292_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1312_; 
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1312_ == 0)
{
lean_object* v_unused_1313_; 
v_unused_1313_ = lean_ctor_get(v___x_1293_, 0);
lean_dec(v_unused_1313_);
v___x_1295_ = v___x_1293_;
v_isShared_1296_ = v_isSharedCheck_1312_;
goto v_resetjp_1294_;
}
else
{
lean_dec(v___x_1293_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1312_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1297_; uint8_t v___x_1298_; 
v___x_1297_ = lean_box(1);
v___x_1298_ = l_Lean_IR_instBEqIRType_beq(v_ty_1083_, v___x_1297_);
if (v___x_1298_ == 0)
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v_msg_1306_; lean_object* v___x_1307_; 
lean_del_object(v___x_1295_);
v___x_1299_ = ((lean_object*)(l_Lean_IR_Checker_checkType___closed__0));
v___x_1300_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_1083_);
v___x_1301_ = l_Std_Format_defWidth;
v___x_1302_ = lean_unsigned_to_nat(0u);
v___x_1303_ = l_Std_Format_pretty(v___x_1300_, v___x_1301_, v___x_1302_, v___x_1302_);
v___x_1304_ = lean_string_append(v___x_1299_, v___x_1303_);
lean_dec_ref(v___x_1303_);
v___x_1305_ = ((lean_object*)(l_Lean_IR_Checker_checkVar___closed__2));
v_msg_1306_ = lean_string_append(v___x_1304_, v___x_1305_);
v___x_1307_ = l_Lean_IR_Checker_throwCheckerError___redArg(v_msg_1306_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
return v___x_1307_;
}
else
{
lean_object* v___x_1308_; lean_object* v___x_1310_; 
lean_dec(v_ty_1083_);
v___x_1308_ = lean_box(0);
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 0, v___x_1308_);
v___x_1310_ = v___x_1295_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v___x_1308_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
}
else
{
lean_dec(v_ty_1083_);
return v___x_1293_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___boxed(lean_object* v_ty_1314_, lean_object* v_e_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_Lean_IR_Checker_checkExpr(v_ty_1314_, v_e_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_);
lean_dec(v_a_1319_);
lean_dec_ref(v_a_1318_);
lean_dec(v_a_1317_);
lean_dec_ref(v_a_1316_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__0(lean_object* v_ctx_1322_, lean_object* v_p_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v_x_1329_; lean_object* v___x_1330_; 
v_x_1329_ = lean_ctor_get(v_p_1323_, 0);
lean_inc(v_x_1329_);
v___x_1330_ = l_Lean_IR_Checker_markIndex(v_x_1329_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1338_; 
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1338_ == 0)
{
lean_object* v_unused_1339_; 
v_unused_1339_ = lean_ctor_get(v___x_1330_, 0);
lean_dec(v_unused_1339_);
v___x_1332_ = v___x_1330_;
v_isShared_1333_ = v_isSharedCheck_1338_;
goto v_resetjp_1331_;
}
else
{
lean_dec(v___x_1330_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1338_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1334_; lean_object* v___x_1336_; 
v___x_1334_ = l_Lean_IR_LocalContext_addParam(v_ctx_1322_, v_p_1323_);
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 0, v___x_1334_);
v___x_1336_ = v___x_1332_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v___x_1334_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
}
else
{
lean_object* v_a_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1347_; 
lean_dec_ref(v_p_1323_);
lean_dec(v_ctx_1322_);
v_a_1340_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1342_ = v___x_1330_;
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_a_1340_);
lean_dec(v___x_1330_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1345_; 
if (v_isShared_1343_ == 0)
{
v___x_1345_ = v___x_1342_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_a_1340_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__0___boxed(lean_object* v_ctx_1348_, lean_object* v_p_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_Lean_IR_Checker_withParams___lam__0(v_ctx_1348_, v_p_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
return v_res_1355_;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__0(void){
_start:
{
lean_object* v___x_1356_; 
v___x_1356_ = l_instMonadEIO(lean_box(0));
return v___x_1356_;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__1(void){
_start:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1357_ = lean_obj_once(&l_Lean_IR_Checker_withParams___closed__0, &l_Lean_IR_Checker_withParams___closed__0_once, _init_l_Lean_IR_Checker_withParams___closed__0);
v___x_1358_ = l_StateRefT_x27_instMonad___redArg(v___x_1357_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams(lean_object* v_ps_1362_, lean_object* v_k_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_){
_start:
{
lean_object* v___x_1369_; lean_object* v_toApplicative_1370_; lean_object* v_toFunctor_1371_; lean_object* v_toSeq_1372_; lean_object* v_toSeqLeft_1373_; lean_object* v_toSeqRight_1374_; lean_object* v___f_1375_; lean_object* v___f_1376_; lean_object* v___f_1377_; lean_object* v___f_1378_; lean_object* v___x_1379_; lean_object* v___f_1380_; lean_object* v___f_1381_; lean_object* v___f_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v_localCtx_1387_; lean_object* v_currentDecl_1388_; lean_object* v_decls_1389_; lean_object* v_a_1391_; lean_object* v___y_1395_; lean_object* v___x_1405_; lean_object* v___x_1406_; uint8_t v___x_1407_; 
v___x_1369_ = lean_obj_once(&l_Lean_IR_Checker_withParams___closed__1, &l_Lean_IR_Checker_withParams___closed__1_once, _init_l_Lean_IR_Checker_withParams___closed__1);
v_toApplicative_1370_ = lean_ctor_get(v___x_1369_, 0);
v_toFunctor_1371_ = lean_ctor_get(v_toApplicative_1370_, 0);
v_toSeq_1372_ = lean_ctor_get(v_toApplicative_1370_, 2);
v_toSeqLeft_1373_ = lean_ctor_get(v_toApplicative_1370_, 3);
v_toSeqRight_1374_ = lean_ctor_get(v_toApplicative_1370_, 4);
v___f_1375_ = ((lean_object*)(l_Lean_IR_Checker_withParams___closed__2));
v___f_1376_ = ((lean_object*)(l_Lean_IR_Checker_withParams___closed__3));
lean_inc_ref_n(v_toFunctor_1371_, 2);
v___f_1377_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1377_, 0, v_toFunctor_1371_);
v___f_1378_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1378_, 0, v_toFunctor_1371_);
v___x_1379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1379_, 0, v___f_1377_);
lean_ctor_set(v___x_1379_, 1, v___f_1378_);
lean_inc(v_toSeqRight_1374_);
v___f_1380_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1380_, 0, v_toSeqRight_1374_);
lean_inc(v_toSeqLeft_1373_);
v___f_1381_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1381_, 0, v_toSeqLeft_1373_);
lean_inc(v_toSeq_1372_);
v___f_1382_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1382_, 0, v_toSeq_1372_);
v___x_1383_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1379_);
lean_ctor_set(v___x_1383_, 1, v___f_1375_);
lean_ctor_set(v___x_1383_, 2, v___f_1382_);
lean_ctor_set(v___x_1383_, 3, v___f_1381_);
lean_ctor_set(v___x_1383_, 4, v___f_1380_);
v___x_1384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1383_);
lean_ctor_set(v___x_1384_, 1, v___f_1376_);
v___x_1385_ = l_StateRefT_x27_instMonad___redArg(v___x_1384_);
v___x_1386_ = l_ReaderT_instMonad___redArg(v___x_1385_);
v_localCtx_1387_ = lean_ctor_get(v_a_1364_, 0);
v_currentDecl_1388_ = lean_ctor_get(v_a_1364_, 1);
v_decls_1389_ = lean_ctor_get(v_a_1364_, 2);
v___x_1405_ = lean_unsigned_to_nat(0u);
v___x_1406_ = lean_array_get_size(v_ps_1362_);
v___x_1407_ = lean_nat_dec_lt(v___x_1405_, v___x_1406_);
if (v___x_1407_ == 0)
{
lean_dec_ref(v___x_1386_);
lean_dec_ref(v_ps_1362_);
lean_inc(v_localCtx_1387_);
v_a_1391_ = v_localCtx_1387_;
goto v___jp_1390_;
}
else
{
lean_object* v___f_1408_; uint8_t v___x_1409_; 
v___f_1408_ = ((lean_object*)(l_Lean_IR_Checker_withParams___closed__4));
v___x_1409_ = lean_nat_dec_le(v___x_1406_, v___x_1406_);
if (v___x_1409_ == 0)
{
if (v___x_1407_ == 0)
{
lean_dec_ref(v___x_1386_);
lean_dec_ref(v_ps_1362_);
lean_inc(v_localCtx_1387_);
v_a_1391_ = v_localCtx_1387_;
goto v___jp_1390_;
}
else
{
size_t v___x_1410_; size_t v___x_1411_; lean_object* v___x_1038__overap_1412_; lean_object* v___x_1413_; 
v___x_1410_ = ((size_t)0ULL);
v___x_1411_ = lean_usize_of_nat(v___x_1406_);
lean_inc(v_localCtx_1387_);
v___x_1038__overap_1412_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1386_, v___f_1408_, v_ps_1362_, v___x_1410_, v___x_1411_, v_localCtx_1387_);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
v___x_1413_ = lean_apply_5(v___x_1038__overap_1412_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, lean_box(0));
v___y_1395_ = v___x_1413_;
goto v___jp_1394_;
}
}
else
{
size_t v___x_1414_; size_t v___x_1415_; lean_object* v___x_1042__overap_1416_; lean_object* v___x_1417_; 
v___x_1414_ = ((size_t)0ULL);
v___x_1415_ = lean_usize_of_nat(v___x_1406_);
lean_inc(v_localCtx_1387_);
v___x_1042__overap_1416_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1386_, v___f_1408_, v_ps_1362_, v___x_1414_, v___x_1415_, v_localCtx_1387_);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
v___x_1417_ = lean_apply_5(v___x_1042__overap_1416_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, lean_box(0));
v___y_1395_ = v___x_1417_;
goto v___jp_1394_;
}
}
v___jp_1390_:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
lean_inc_ref(v_decls_1389_);
lean_inc_ref(v_currentDecl_1388_);
v___x_1392_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1392_, 0, v_a_1391_);
lean_ctor_set(v___x_1392_, 1, v_currentDecl_1388_);
lean_ctor_set(v___x_1392_, 2, v_decls_1389_);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
v___x_1393_ = lean_apply_5(v_k_1363_, v___x_1392_, v_a_1365_, v_a_1366_, v_a_1367_, lean_box(0));
return v___x_1393_;
}
v___jp_1394_:
{
if (lean_obj_tag(v___y_1395_) == 0)
{
lean_object* v_a_1396_; 
v_a_1396_ = lean_ctor_get(v___y_1395_, 0);
lean_inc(v_a_1396_);
lean_dec_ref_known(v___y_1395_, 1);
v_a_1391_ = v_a_1396_;
goto v___jp_1390_;
}
else
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1404_; 
lean_dec_ref(v_k_1363_);
v_a_1397_ = lean_ctor_get(v___y_1395_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___y_1395_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1399_ = v___y_1395_;
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___y_1395_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1400_ == 0)
{
v___x_1402_ = v___x_1399_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1397_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___boxed(lean_object* v_ps_1418_, lean_object* v_k_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Lean_IR_Checker_withParams(v_ps_1418_, v_k_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_);
lean_dec(v_a_1423_);
lean_dec_ref(v_a_1422_);
lean_dec(v_a_1421_);
lean_dec_ref(v_a_1420_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(lean_object* v_as_1426_, size_t v_i_1427_, size_t v_stop_1428_, lean_object* v_b_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
uint8_t v___x_1435_; 
v___x_1435_ = lean_usize_dec_eq(v_i_1427_, v_stop_1428_);
if (v___x_1435_ == 0)
{
lean_object* v___x_1436_; lean_object* v_x_1437_; lean_object* v___x_1438_; 
v___x_1436_ = lean_array_uget_borrowed(v_as_1426_, v_i_1427_);
v_x_1437_ = lean_ctor_get(v___x_1436_, 0);
lean_inc(v_x_1437_);
v___x_1438_ = l_Lean_IR_Checker_markIndex(v_x_1437_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_object* v___x_1439_; size_t v___x_1440_; size_t v___x_1441_; 
lean_dec_ref_known(v___x_1438_, 1);
lean_inc(v___x_1436_);
v___x_1439_ = l_Lean_IR_LocalContext_addParam(v_b_1429_, v___x_1436_);
v___x_1440_ = ((size_t)1ULL);
v___x_1441_ = lean_usize_add(v_i_1427_, v___x_1440_);
v_i_1427_ = v___x_1441_;
v_b_1429_ = v___x_1439_;
goto _start;
}
else
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
lean_dec(v_b_1429_);
v_a_1443_ = lean_ctor_get(v___x_1438_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1438_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1438_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1443_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
else
{
lean_object* v___x_1451_; 
v___x_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1451_, 0, v_b_1429_);
return v___x_1451_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0___boxed(lean_object* v_as_1452_, lean_object* v_i_1453_, lean_object* v_stop_1454_, lean_object* v_b_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
size_t v_i_boxed_1461_; size_t v_stop_boxed_1462_; lean_object* v_res_1463_; 
v_i_boxed_1461_ = lean_unbox_usize(v_i_1453_);
lean_dec(v_i_1453_);
v_stop_boxed_1462_ = lean_unbox_usize(v_stop_1454_);
lean_dec(v_stop_1454_);
v_res_1463_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_as_1452_, v_i_boxed_1461_, v_stop_boxed_1462_, v_b_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec_ref(v_as_1452_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFnBody(lean_object* v_fnBody_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_){
_start:
{
lean_object* v_x_1471_; lean_object* v_b_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1475_; lean_object* v___y_1476_; 
switch(lean_obj_tag(v_fnBody_1464_))
{
case 0:
{
lean_object* v_x_1479_; lean_object* v_ty_1480_; lean_object* v_e_1481_; lean_object* v_b_1482_; lean_object* v___x_1483_; 
v_x_1479_ = lean_ctor_get(v_fnBody_1464_, 0);
lean_inc(v_x_1479_);
v_ty_1480_ = lean_ctor_get(v_fnBody_1464_, 1);
lean_inc_n(v_ty_1480_, 2);
v_e_1481_ = lean_ctor_get(v_fnBody_1464_, 2);
lean_inc_ref_n(v_e_1481_, 2);
v_b_1482_ = lean_ctor_get(v_fnBody_1464_, 3);
lean_inc(v_b_1482_);
lean_dec_ref_known(v_fnBody_1464_, 4);
v___x_1483_ = l_Lean_IR_Checker_checkExpr(v_ty_1480_, v_e_1481_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v___x_1484_; 
lean_dec_ref_known(v___x_1483_, 1);
lean_inc(v_x_1479_);
v___x_1484_ = l_Lean_IR_Checker_markIndex(v_x_1479_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v_localCtx_1485_; lean_object* v_currentDecl_1486_; lean_object* v_decls_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
lean_dec_ref_known(v___x_1484_, 1);
v_localCtx_1485_ = lean_ctor_get(v_a_1465_, 0);
lean_inc(v_localCtx_1485_);
v_currentDecl_1486_ = lean_ctor_get(v_a_1465_, 1);
lean_inc_ref(v_currentDecl_1486_);
v_decls_1487_ = lean_ctor_get(v_a_1465_, 2);
lean_inc_ref(v_decls_1487_);
lean_dec_ref(v_a_1465_);
v___x_1488_ = l_Lean_IR_LocalContext_addLocal(v_localCtx_1485_, v_x_1479_, v_ty_1480_, v_e_1481_);
v___x_1489_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1488_);
lean_ctor_set(v___x_1489_, 1, v_currentDecl_1486_);
lean_ctor_set(v___x_1489_, 2, v_decls_1487_);
v_fnBody_1464_ = v_b_1482_;
v_a_1465_ = v___x_1489_;
goto _start;
}
else
{
lean_dec(v_b_1482_);
lean_dec_ref(v_e_1481_);
lean_dec(v_ty_1480_);
lean_dec(v_x_1479_);
lean_dec_ref(v_a_1465_);
return v___x_1484_;
}
}
else
{
lean_dec(v_b_1482_);
lean_dec_ref(v_e_1481_);
lean_dec(v_ty_1480_);
lean_dec(v_x_1479_);
lean_dec_ref(v_a_1465_);
return v___x_1483_;
}
}
case 1:
{
lean_object* v_j_1491_; lean_object* v_xs_1492_; lean_object* v_v_1493_; lean_object* v_b_1494_; lean_object* v___x_1495_; 
v_j_1491_ = lean_ctor_get(v_fnBody_1464_, 0);
lean_inc_n(v_j_1491_, 2);
v_xs_1492_ = lean_ctor_get(v_fnBody_1464_, 1);
lean_inc_ref(v_xs_1492_);
v_v_1493_ = lean_ctor_get(v_fnBody_1464_, 2);
lean_inc(v_v_1493_);
v_b_1494_ = lean_ctor_get(v_fnBody_1464_, 3);
lean_inc(v_b_1494_);
lean_dec_ref_known(v_fnBody_1464_, 4);
v___x_1495_ = l_Lean_IR_Checker_markIndex(v_j_1491_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v_localCtx_1496_; lean_object* v_currentDecl_1497_; lean_object* v_decls_1498_; lean_object* v_a_1500_; lean_object* v___x_1506_; lean_object* v___x_1507_; uint8_t v___x_1508_; 
lean_dec_ref_known(v___x_1495_, 1);
v_localCtx_1496_ = lean_ctor_get(v_a_1465_, 0);
lean_inc(v_localCtx_1496_);
v_currentDecl_1497_ = lean_ctor_get(v_a_1465_, 1);
lean_inc_ref(v_currentDecl_1497_);
v_decls_1498_ = lean_ctor_get(v_a_1465_, 2);
lean_inc_ref(v_decls_1498_);
v___x_1506_ = lean_unsigned_to_nat(0u);
v___x_1507_ = lean_array_get_size(v_xs_1492_);
v___x_1508_ = lean_nat_dec_lt(v___x_1506_, v___x_1507_);
if (v___x_1508_ == 0)
{
lean_dec_ref(v_a_1465_);
lean_inc(v_localCtx_1496_);
v_a_1500_ = v_localCtx_1496_;
goto v___jp_1499_;
}
else
{
size_t v___x_1509_; size_t v___x_1510_; lean_object* v___x_1511_; 
v___x_1509_ = ((size_t)0ULL);
v___x_1510_ = lean_usize_of_nat(v___x_1507_);
lean_inc(v_localCtx_1496_);
v___x_1511_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_xs_1492_, v___x_1509_, v___x_1510_, v_localCtx_1496_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
lean_dec_ref(v_a_1465_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v_a_1512_; 
v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
lean_inc(v_a_1512_);
lean_dec_ref_known(v___x_1511_, 1);
v_a_1500_ = v_a_1512_;
goto v___jp_1499_;
}
else
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1520_; 
lean_dec_ref(v_decls_1498_);
lean_dec_ref(v_currentDecl_1497_);
lean_dec(v_localCtx_1496_);
lean_dec(v_b_1494_);
lean_dec(v_v_1493_);
lean_dec_ref(v_xs_1492_);
lean_dec(v_j_1491_);
v_a_1513_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1515_ = v___x_1511_;
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1511_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1513_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
v___jp_1499_:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
lean_inc_ref(v_decls_1498_);
lean_inc_ref(v_currentDecl_1497_);
v___x_1501_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1501_, 0, v_a_1500_);
lean_ctor_set(v___x_1501_, 1, v_currentDecl_1497_);
lean_ctor_set(v___x_1501_, 2, v_decls_1498_);
lean_inc(v_v_1493_);
v___x_1502_ = l_Lean_IR_Checker_checkFnBody(v_v_1493_, v___x_1501_, v_a_1466_, v_a_1467_, v_a_1468_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
lean_dec_ref_known(v___x_1502_, 1);
v___x_1503_ = l_Lean_IR_LocalContext_addJP(v_localCtx_1496_, v_j_1491_, v_xs_1492_, v_v_1493_);
v___x_1504_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1503_);
lean_ctor_set(v___x_1504_, 1, v_currentDecl_1497_);
lean_ctor_set(v___x_1504_, 2, v_decls_1498_);
v_fnBody_1464_ = v_b_1494_;
v_a_1465_ = v___x_1504_;
goto _start;
}
else
{
lean_dec_ref(v_decls_1498_);
lean_dec_ref(v_currentDecl_1497_);
lean_dec(v_localCtx_1496_);
lean_dec(v_b_1494_);
lean_dec(v_v_1493_);
lean_dec_ref(v_xs_1492_);
lean_dec(v_j_1491_);
return v___x_1502_;
}
}
}
else
{
lean_dec(v_b_1494_);
lean_dec(v_v_1493_);
lean_dec_ref(v_xs_1492_);
lean_dec(v_j_1491_);
lean_dec_ref(v_a_1465_);
return v___x_1495_;
}
}
case 2:
{
lean_object* v_x_1521_; lean_object* v_y_1522_; lean_object* v_b_1523_; lean_object* v___x_1524_; 
v_x_1521_ = lean_ctor_get(v_fnBody_1464_, 0);
lean_inc(v_x_1521_);
v_y_1522_ = lean_ctor_get(v_fnBody_1464_, 2);
lean_inc(v_y_1522_);
v_b_1523_ = lean_ctor_get(v_fnBody_1464_, 3);
lean_inc(v_b_1523_);
lean_dec_ref_known(v_fnBody_1464_, 4);
v___x_1524_ = l_Lean_IR_Checker_checkVar(v_x_1521_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v___x_1525_; 
lean_dec_ref_known(v___x_1524_, 1);
v___x_1525_ = l_Lean_IR_Checker_checkArg(v_y_1522_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
if (lean_obj_tag(v___x_1525_) == 0)
{
lean_dec_ref_known(v___x_1525_, 1);
v_fnBody_1464_ = v_b_1523_;
goto _start;
}
else
{
lean_dec(v_b_1523_);
lean_dec_ref(v_a_1465_);
return v___x_1525_;
}
}
else
{
lean_dec(v_b_1523_);
lean_dec(v_y_1522_);
lean_dec_ref(v_a_1465_);
return v___x_1524_;
}
}
case 3:
{
lean_object* v_x_1527_; lean_object* v_b_1528_; lean_object* v___x_1529_; 
v_x_1527_ = lean_ctor_get(v_fnBody_1464_, 0);
lean_inc(v_x_1527_);
v_b_1528_ = lean_ctor_get(v_fnBody_1464_, 2);
lean_inc(v_b_1528_);
lean_dec_ref_known(v_fnBody_1464_, 3);
v___x_1529_ = l_Lean_IR_Checker_checkVar(v_x_1527_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_dec_ref_known(v___x_1529_, 1);
v_fnBody_1464_ = v_b_1528_;
goto _start;
}
else
{
lean_dec(v_b_1528_);
lean_dec_ref(v_a_1465_);
return v___x_1529_;
}
}
case 4:
{
lean_object* v_x_1531_; lean_object* v_y_1532_; lean_object* v_b_1533_; lean_object* v___x_1534_; 
v_x_1531_ = lean_ctor_get(v_fnBody_1464_, 0);
lean_inc(v_x_1531_);
v_y_1532_ = lean_ctor_get(v_fnBody_1464_, 2);
lean_inc(v_y_1532_);
v_b_1533_ = lean_ctor_get(v_fnBody_1464_, 3);
lean_inc(v_b_1533_);
lean_dec_ref_known(v_fnBody_1464_, 4);
v___x_1534_ = l_Lean_IR_Checker_checkVar(v_x_1531_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v___x_1535_; 
lean_dec_ref_known(v___x_1534_, 1);
v___x_1535_ = l_Lean_IR_Checker_checkVar(v_y_1532_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_dec_ref_known(v___x_1535_, 1);
v_fnBody_1464_ = v_b_1533_;
goto _start;
}
else
{
lean_dec(v_b_1533_);
lean_dec_ref(v_a_1465_);
return v___x_1535_;
}
}
else
{
lean_dec(v_b_1533_);
lean_dec(v_y_1532_);
lean_dec_ref(v_a_1465_);
return v___x_1534_;
}
}
case 5:
{
lean_object* v_x_1537_; lean_object* v_y_1538_; lean_object* v_b_1539_; lean_object* v___x_1540_; 
v_x_1537_ = lean_ctor_get(v_fnBody_1464_, 0);
lean_inc(v_x_1537_);
v_y_1538_ = lean_ctor_get(v_fnBody_1464_, 3);
lean_inc(v_y_1538_);
v_b_1539_ = lean_ctor_get(v_fnBody_1464_, 5);
lean_inc(v_b_1539_);
lean_dec_ref_known(v_fnBody_1464_, 6);
v___x_1540_ = l_Lean_IR_Checker_checkVar(v_x_1537_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v___x_1541_; 
lean_dec_ref_known(v___x_1540_, 1);
v___x_1541_ = l_Lean_IR_Checker_checkVar(v_y_1538_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_dec_ref_known(v___x_1541_, 1);
v_fnBody_1464_ = v_b_1539_;
goto _start;
}
else
{
lean_dec(v_b_1539_);
lean_dec_ref(v_a_1465_);
return v___x_1541_;
}
}
else
{
lean_dec(v_b_1539_);
lean_dec(v_y_1538_);
lean_dec_ref(v_a_1465_);
return v___x_1540_;
}
}
case 8:
{
lean_object* v_x_1543_; lean_object* v_b_1544_; lean_object* v___x_1545_; 
v_x_1543_ = lean_ctor_get(v_fnBody_1464_, 0);
lean_inc(v_x_1543_);
v_b_1544_ = lean_ctor_get(v_fnBody_1464_, 1);
lean_inc(v_b_1544_);
lean_dec_ref_known(v_fnBody_1464_, 2);
v___x_1545_ = l_Lean_IR_Checker_checkVar(v_x_1543_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_dec_ref_known(v___x_1545_, 1);
v_fnBody_1464_ = v_b_1544_;
goto _start;
}
else
{
lean_dec(v_b_1544_);
lean_dec_ref(v_a_1465_);
return v___x_1545_;
}
}
case 9:
{
lean_object* v_x_1547_; lean_object* v_cs_1548_; lean_object* v___x_1549_; 
v_x_1547_ = lean_ctor_get(v_fnBody_1464_, 1);
lean_inc(v_x_1547_);
v_cs_1548_ = lean_ctor_get(v_fnBody_1464_, 3);
lean_inc_ref(v_cs_1548_);
lean_dec_ref_known(v_fnBody_1464_, 4);
v___x_1549_ = l_Lean_IR_Checker_checkVar(v_x_1547_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1570_; 
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1570_ == 0)
{
lean_object* v_unused_1571_; 
v_unused_1571_ = lean_ctor_get(v___x_1549_, 0);
lean_dec(v_unused_1571_);
v___x_1551_ = v___x_1549_;
v_isShared_1552_ = v_isSharedCheck_1570_;
goto v_resetjp_1550_;
}
else
{
lean_dec(v___x_1549_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1570_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; uint8_t v___x_1556_; 
v___x_1553_ = lean_unsigned_to_nat(0u);
v___x_1554_ = lean_array_get_size(v_cs_1548_);
v___x_1555_ = lean_box(0);
v___x_1556_ = lean_nat_dec_lt(v___x_1553_, v___x_1554_);
if (v___x_1556_ == 0)
{
lean_object* v___x_1558_; 
lean_dec_ref(v_cs_1548_);
lean_dec_ref(v_a_1465_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 0, v___x_1555_);
v___x_1558_ = v___x_1551_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1555_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
else
{
uint8_t v___x_1560_; 
v___x_1560_ = lean_nat_dec_le(v___x_1554_, v___x_1554_);
if (v___x_1560_ == 0)
{
if (v___x_1556_ == 0)
{
lean_object* v___x_1562_; 
lean_dec_ref(v_cs_1548_);
lean_dec_ref(v_a_1465_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 0, v___x_1555_);
v___x_1562_ = v___x_1551_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v___x_1555_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
else
{
size_t v___x_1564_; size_t v___x_1565_; lean_object* v___x_1566_; 
lean_del_object(v___x_1551_);
v___x_1564_ = ((size_t)0ULL);
v___x_1565_ = lean_usize_of_nat(v___x_1554_);
v___x_1566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(v_cs_1548_, v___x_1564_, v___x_1565_, v___x_1555_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
lean_dec_ref(v_a_1465_);
lean_dec_ref(v_cs_1548_);
return v___x_1566_;
}
}
else
{
size_t v___x_1567_; size_t v___x_1568_; lean_object* v___x_1569_; 
lean_del_object(v___x_1551_);
v___x_1567_ = ((size_t)0ULL);
v___x_1568_ = lean_usize_of_nat(v___x_1554_);
v___x_1569_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(v_cs_1548_, v___x_1567_, v___x_1568_, v___x_1555_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
lean_dec_ref(v_a_1465_);
lean_dec_ref(v_cs_1548_);
return v___x_1569_;
}
}
}
}
else
{
lean_dec_ref(v_cs_1548_);
lean_dec_ref(v_a_1465_);
return v___x_1549_;
}
}
case 10:
{
lean_object* v_x_1572_; lean_object* v___x_1573_; 
v_x_1572_ = lean_ctor_get(v_fnBody_1464_, 0);
lean_inc(v_x_1572_);
lean_dec_ref_known(v_fnBody_1464_, 1);
v___x_1573_ = l_Lean_IR_Checker_checkArg(v_x_1572_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
lean_dec_ref(v_a_1465_);
return v___x_1573_;
}
case 11:
{
lean_object* v_j_1574_; lean_object* v_ys_1575_; lean_object* v___x_1576_; 
v_j_1574_ = lean_ctor_get(v_fnBody_1464_, 0);
lean_inc(v_j_1574_);
v_ys_1575_ = lean_ctor_get(v_fnBody_1464_, 1);
lean_inc_ref(v_ys_1575_);
lean_dec_ref_known(v_fnBody_1464_, 2);
v___x_1576_ = l_Lean_IR_Checker_checkJP(v_j_1574_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v___x_1577_; 
lean_dec_ref_known(v___x_1576_, 1);
v___x_1577_ = l_Lean_IR_Checker_checkArgs(v_ys_1575_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
lean_dec_ref(v_a_1465_);
lean_dec_ref(v_ys_1575_);
return v___x_1577_;
}
else
{
lean_dec_ref(v_ys_1575_);
lean_dec_ref(v_a_1465_);
return v___x_1576_;
}
}
case 12:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; 
lean_dec_ref(v_a_1465_);
v___x_1578_ = lean_box(0);
v___x_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1578_);
return v___x_1579_;
}
default: 
{
lean_object* v_x_1580_; lean_object* v_b_1581_; 
v_x_1580_ = lean_ctor_get(v_fnBody_1464_, 0);
lean_inc(v_x_1580_);
v_b_1581_ = lean_ctor_get(v_fnBody_1464_, 2);
lean_inc(v_b_1581_);
lean_dec(v_fnBody_1464_);
v_x_1471_ = v_x_1580_;
v_b_1472_ = v_b_1581_;
v___y_1473_ = v_a_1465_;
v___y_1474_ = v_a_1466_;
v___y_1475_ = v_a_1467_;
v___y_1476_ = v_a_1468_;
goto v___jp_1470_;
}
}
v___jp_1470_:
{
lean_object* v___x_1477_; 
v___x_1477_ = l_Lean_IR_Checker_checkVar(v_x_1471_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_dec_ref_known(v___x_1477_, 1);
v_fnBody_1464_ = v_b_1472_;
v_a_1465_ = v___y_1473_;
v_a_1466_ = v___y_1474_;
v_a_1467_ = v___y_1475_;
v_a_1468_ = v___y_1476_;
goto _start;
}
else
{
lean_dec_ref(v___y_1473_);
lean_dec(v_b_1472_);
return v___x_1477_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(lean_object* v_as_1582_, size_t v_i_1583_, size_t v_stop_1584_, lean_object* v_b_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
uint8_t v___x_1591_; 
v___x_1591_ = lean_usize_dec_eq(v_i_1583_, v_stop_1584_);
if (v___x_1591_ == 0)
{
lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1592_ = lean_array_uget_borrowed(v_as_1582_, v_i_1583_);
v___x_1593_ = l_Lean_IR_Alt_body(v___x_1592_);
lean_inc_ref(v___y_1586_);
v___x_1594_ = l_Lean_IR_Checker_checkFnBody(v___x_1593_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_a_1595_; size_t v___x_1596_; size_t v___x_1597_; 
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_a_1595_);
lean_dec_ref_known(v___x_1594_, 1);
v___x_1596_ = ((size_t)1ULL);
v___x_1597_ = lean_usize_add(v_i_1583_, v___x_1596_);
v_i_1583_ = v___x_1597_;
v_b_1585_ = v_a_1595_;
goto _start;
}
else
{
return v___x_1594_;
}
}
else
{
lean_object* v___x_1599_; 
v___x_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1599_, 0, v_b_1585_);
return v___x_1599_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1___boxed(lean_object* v_as_1600_, lean_object* v_i_1601_, lean_object* v_stop_1602_, lean_object* v_b_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
size_t v_i_boxed_1609_; size_t v_stop_boxed_1610_; lean_object* v_res_1611_; 
v_i_boxed_1609_ = lean_unbox_usize(v_i_1601_);
lean_dec(v_i_1601_);
v_stop_boxed_1610_ = lean_unbox_usize(v_stop_1602_);
lean_dec(v_stop_1602_);
v_res_1611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__1(v_as_1600_, v_i_boxed_1609_, v_stop_boxed_1610_, v_b_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec_ref(v_as_1600_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFnBody___boxed(lean_object* v_fnBody_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_Lean_IR_Checker_checkFnBody(v_fnBody_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_);
lean_dec(v_a_1616_);
lean_dec_ref(v_a_1615_);
lean_dec(v_a_1614_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkDecl(lean_object* v_x_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_){
_start:
{
if (lean_obj_tag(v_x_1619_) == 0)
{
lean_object* v_xs_1625_; lean_object* v_body_1626_; lean_object* v_localCtx_1627_; lean_object* v_currentDecl_1628_; lean_object* v_decls_1629_; lean_object* v_a_1631_; lean_object* v___x_1634_; lean_object* v___x_1635_; uint8_t v___x_1636_; 
v_xs_1625_ = lean_ctor_get(v_x_1619_, 1);
lean_inc_ref(v_xs_1625_);
v_body_1626_ = lean_ctor_get(v_x_1619_, 3);
lean_inc(v_body_1626_);
lean_dec_ref_known(v_x_1619_, 5);
v_localCtx_1627_ = lean_ctor_get(v_a_1620_, 0);
v_currentDecl_1628_ = lean_ctor_get(v_a_1620_, 1);
v_decls_1629_ = lean_ctor_get(v_a_1620_, 2);
v___x_1634_ = lean_unsigned_to_nat(0u);
v___x_1635_ = lean_array_get_size(v_xs_1625_);
v___x_1636_ = lean_nat_dec_lt(v___x_1634_, v___x_1635_);
if (v___x_1636_ == 0)
{
lean_dec_ref(v_xs_1625_);
lean_inc(v_localCtx_1627_);
v_a_1631_ = v_localCtx_1627_;
goto v___jp_1630_;
}
else
{
size_t v___x_1637_; size_t v___x_1638_; lean_object* v___x_1639_; 
v___x_1637_ = ((size_t)0ULL);
v___x_1638_ = lean_usize_of_nat(v___x_1635_);
lean_inc(v_localCtx_1627_);
v___x_1639_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_xs_1625_, v___x_1637_, v___x_1638_, v_localCtx_1627_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_);
lean_dec_ref(v_xs_1625_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_a_1640_);
lean_dec_ref_known(v___x_1639_, 1);
v_a_1631_ = v_a_1640_;
goto v___jp_1630_;
}
else
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1648_; 
lean_dec(v_body_1626_);
v_a_1641_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1643_ = v___x_1639_;
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1639_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1646_; 
if (v_isShared_1644_ == 0)
{
v___x_1646_ = v___x_1643_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_a_1641_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
}
v___jp_1630_:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; 
lean_inc_ref(v_decls_1629_);
lean_inc_ref(v_currentDecl_1628_);
v___x_1632_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1632_, 0, v_a_1631_);
lean_ctor_set(v___x_1632_, 1, v_currentDecl_1628_);
lean_ctor_set(v___x_1632_, 2, v_decls_1629_);
v___x_1633_ = l_Lean_IR_Checker_checkFnBody(v_body_1626_, v___x_1632_, v_a_1621_, v_a_1622_, v_a_1623_);
return v___x_1633_;
}
}
else
{
lean_object* v_xs_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; uint8_t v___x_1653_; 
v_xs_1649_ = lean_ctor_get(v_x_1619_, 1);
lean_inc_ref(v_xs_1649_);
lean_dec_ref_known(v_x_1619_, 4);
v___x_1650_ = lean_box(0);
v___x_1651_ = lean_unsigned_to_nat(0u);
v___x_1652_ = lean_array_get_size(v_xs_1649_);
v___x_1653_ = lean_nat_dec_lt(v___x_1651_, v___x_1652_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1654_; 
lean_dec_ref(v_xs_1649_);
v___x_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1650_);
return v___x_1654_;
}
else
{
lean_object* v_localCtx_1655_; size_t v___x_1656_; size_t v___x_1657_; lean_object* v___x_1658_; 
v_localCtx_1655_ = lean_ctor_get(v_a_1620_, 0);
v___x_1656_ = ((size_t)0ULL);
v___x_1657_ = lean_usize_of_nat(v___x_1652_);
lean_inc(v_localCtx_1655_);
v___x_1658_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Checker_checkFnBody_spec__0(v_xs_1649_, v___x_1656_, v___x_1657_, v_localCtx_1655_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_);
lean_dec_ref(v_xs_1649_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1665_; 
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1665_ == 0)
{
lean_object* v_unused_1666_; 
v_unused_1666_ = lean_ctor_get(v___x_1658_, 0);
lean_dec(v_unused_1666_);
v___x_1660_ = v___x_1658_;
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
else
{
lean_dec(v___x_1658_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1663_; 
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 0, v___x_1650_);
v___x_1663_ = v___x_1660_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1650_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
else
{
lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1674_; 
v_a_1667_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1669_ = v___x_1658_;
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v___x_1658_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1672_; 
if (v_isShared_1670_ == 0)
{
v___x_1672_ = v___x_1669_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_a_1667_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkDecl___boxed(lean_object* v_x_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l_Lean_IR_Checker_checkDecl(v_x_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_);
lean_dec(v_a_1679_);
lean_dec_ref(v_a_1678_);
lean_dec(v_a_1677_);
lean_dec_ref(v_a_1676_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl(lean_object* v_decls_1682_, lean_object* v_decl_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_){
_start:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1687_ = lean_box(1);
v___x_1688_ = lean_st_mk_ref(v___x_1687_);
lean_inc_ref(v_decl_1683_);
v___x_1689_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1687_);
lean_ctor_set(v___x_1689_, 1, v_decl_1683_);
lean_ctor_set(v___x_1689_, 2, v_decls_1682_);
v___x_1690_ = l_Lean_IR_Checker_checkDecl(v_decl_1683_, v___x_1689_, v___x_1688_, v_a_1684_, v_a_1685_);
lean_dec_ref_known(v___x_1689_, 3);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1699_; 
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1693_ = v___x_1690_;
v_isShared_1694_ = v_isSharedCheck_1699_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1690_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1699_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1695_; lean_object* v___x_1697_; 
v___x_1695_ = lean_st_ref_get(v___x_1688_);
lean_dec(v___x_1688_);
lean_dec(v___x_1695_);
if (v_isShared_1694_ == 0)
{
v___x_1697_ = v___x_1693_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_a_1691_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
else
{
lean_dec(v___x_1688_);
return v___x_1690_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl___boxed(lean_object* v_decls_1700_, lean_object* v_decl_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l_Lean_IR_checkDecl(v_decls_1700_, v_decl_1701_, v_a_1702_, v_a_1703_);
lean_dec(v_a_1703_);
lean_dec_ref(v_a_1702_);
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(lean_object* v_decls_1706_, lean_object* v_as_1707_, size_t v_i_1708_, size_t v_stop_1709_, lean_object* v_b_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
uint8_t v___x_1714_; 
v___x_1714_ = lean_usize_dec_eq(v_i_1708_, v_stop_1709_);
if (v___x_1714_ == 0)
{
lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1715_ = lean_array_uget_borrowed(v_as_1707_, v_i_1708_);
lean_inc(v___x_1715_);
lean_inc_ref(v_decls_1706_);
v___x_1716_ = l_Lean_IR_checkDecl(v_decls_1706_, v___x_1715_, v___y_1711_, v___y_1712_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v_a_1717_; size_t v___x_1718_; size_t v___x_1719_; 
v_a_1717_ = lean_ctor_get(v___x_1716_, 0);
lean_inc(v_a_1717_);
lean_dec_ref_known(v___x_1716_, 1);
v___x_1718_ = ((size_t)1ULL);
v___x_1719_ = lean_usize_add(v_i_1708_, v___x_1718_);
v_i_1708_ = v___x_1719_;
v_b_1710_ = v_a_1717_;
goto _start;
}
else
{
lean_dec_ref(v_decls_1706_);
return v___x_1716_;
}
}
else
{
lean_object* v___x_1721_; 
lean_dec_ref(v_decls_1706_);
v___x_1721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1721_, 0, v_b_1710_);
return v___x_1721_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0___boxed(lean_object* v_decls_1722_, lean_object* v_as_1723_, lean_object* v_i_1724_, lean_object* v_stop_1725_, lean_object* v_b_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
size_t v_i_boxed_1730_; size_t v_stop_boxed_1731_; lean_object* v_res_1732_; 
v_i_boxed_1730_ = lean_unbox_usize(v_i_1724_);
lean_dec(v_i_1724_);
v_stop_boxed_1731_ = lean_unbox_usize(v_stop_1725_);
lean_dec(v_stop_1725_);
v_res_1732_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(v_decls_1722_, v_as_1723_, v_i_boxed_1730_, v_stop_boxed_1731_, v_b_1726_, v___y_1727_, v___y_1728_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec_ref(v_as_1723_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls(lean_object* v_decls_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_){
_start:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; uint8_t v___x_1740_; 
v___x_1737_ = lean_unsigned_to_nat(0u);
v___x_1738_ = lean_array_get_size(v_decls_1733_);
v___x_1739_ = lean_box(0);
v___x_1740_ = lean_nat_dec_lt(v___x_1737_, v___x_1738_);
if (v___x_1740_ == 0)
{
lean_object* v___x_1741_; 
lean_dec_ref(v_decls_1733_);
v___x_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1739_);
return v___x_1741_;
}
else
{
uint8_t v___x_1742_; 
v___x_1742_ = lean_nat_dec_le(v___x_1738_, v___x_1738_);
if (v___x_1742_ == 0)
{
if (v___x_1740_ == 0)
{
lean_object* v___x_1743_; 
lean_dec_ref(v_decls_1733_);
v___x_1743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1739_);
return v___x_1743_;
}
else
{
size_t v___x_1744_; size_t v___x_1745_; lean_object* v___x_1746_; 
v___x_1744_ = ((size_t)0ULL);
v___x_1745_ = lean_usize_of_nat(v___x_1738_);
lean_inc_ref(v_decls_1733_);
v___x_1746_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(v_decls_1733_, v_decls_1733_, v___x_1744_, v___x_1745_, v___x_1739_, v_a_1734_, v_a_1735_);
lean_dec_ref(v_decls_1733_);
return v___x_1746_;
}
}
else
{
size_t v___x_1747_; size_t v___x_1748_; lean_object* v___x_1749_; 
v___x_1747_ = ((size_t)0ULL);
v___x_1748_ = lean_usize_of_nat(v___x_1738_);
lean_inc_ref(v_decls_1733_);
v___x_1749_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_checkDecls_spec__0(v_decls_1733_, v_decls_1733_, v___x_1747_, v___x_1748_, v___x_1739_, v_a_1734_, v_a_1735_);
lean_dec_ref(v_decls_1733_);
return v___x_1749_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls___boxed(lean_object* v_decls_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l_Lean_IR_checkDecls(v_decls_1750_, v_a_1751_, v_a_1752_);
lean_dec(v_a_1752_);
lean_dec_ref(v_a_1751_);
return v_res_1754_;
}
}
lean_object* runtime_initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_IR_Checker(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
