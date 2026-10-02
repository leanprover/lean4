// Lean compiler output
// Module: Lean.Attributes
// Imports: public import Lean.CoreM public import Lean.Compiler.MetaAttr
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
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_setState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_initializing();
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t l_Lean_EnvExtension_asyncMayModify___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_asyncPrefix_x3f(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_instInhabitedEnvExtension_default___redArg();
extern lean_object* l_Lean_instInhabitedMessageData_default;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Array_reverse___redArg(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
extern lean_object* l_Lean_ResolveName_backward_privateInPublic_warn;
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_addParenHeuristic(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instInhabitedAttributeApplicationTime_default;
LEAN_EXPORT uint8_t l_Lean_instInhabitedAttributeApplicationTime;
LEAN_EXPORT uint8_t l_Lean_instBEqAttributeApplicationTime_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instBEqAttributeApplicationTime_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqAttributeApplicationTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqAttributeApplicationTime_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqAttributeApplicationTime___closed__0 = (const lean_object*)&l_Lean_instBEqAttributeApplicationTime___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqAttributeApplicationTime = (const lean_object*)&l_Lean_instBEqAttributeApplicationTime___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instMonadLiftImportMAttrM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadLiftImportMAttrM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_instMonadLiftImportMAttrM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instMonadLiftImportMAttrM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instMonadLiftImportMAttrM___closed__0 = (const lean_object*)&l_Lean_instMonadLiftImportMAttrM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instMonadLiftImportMAttrM = (const lean_object*)&l_Lean_instMonadLiftImportMAttrM___closed__0_value;
static const lean_string_object l_Lean_AttributeImplCore_ref___autoParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__0 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value;
static const lean_string_object l_Lean_AttributeImplCore_ref___autoParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__1 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__1_value;
static const lean_string_object l_Lean_AttributeImplCore_ref___autoParam___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__2 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__2_value;
static const lean_string_object l_Lean_AttributeImplCore_ref___autoParam___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__3 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__3_value;
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__4_value_aux_0),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__4_value_aux_1),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__4_value_aux_2),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__4 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__4_value;
static const lean_array_object l_Lean_AttributeImplCore_ref___autoParam___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__5 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__5_value;
static const lean_string_object l_Lean_AttributeImplCore_ref___autoParam___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__6 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__6_value;
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__7_value_aux_0),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__7_value_aux_1),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__7_value_aux_2),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__7 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__7_value;
static const lean_string_object l_Lean_AttributeImplCore_ref___autoParam___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__8 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__8_value;
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__9 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__9_value;
static const lean_string_object l_Lean_AttributeImplCore_ref___autoParam___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__10 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__10_value;
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__11_value_aux_0),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__11_value_aux_1),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__11_value_aux_2),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__11 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__11_value;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__12;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__13;
static const lean_string_object l_Lean_AttributeImplCore_ref___autoParam___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__14 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__14_value;
static const lean_string_object l_Lean_AttributeImplCore_ref___autoParam___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "declName"};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__15 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__15_value;
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__16_value_aux_0),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__16_value_aux_1),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__16_value_aux_2),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__15_value),LEAN_SCALAR_PTR_LITERAL(113, 211, 58, 33, 138, 196, 138, 106)}};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__16 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__16_value;
static const lean_string_object l_Lean_AttributeImplCore_ref___autoParam___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "decl_name%"};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__17 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__17_value;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__18;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__19;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__20;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__21;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__22;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__23;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__24;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__25;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__26;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__27;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__28;
LEAN_EXPORT lean_object* l_Lean_AttributeImplCore_ref___autoParam;
static const lean_string_object l_Lean_instInhabitedAttributeImplCore_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "instInhabitedAttributeImplCore"};
static const lean_object* l_Lean_instInhabitedAttributeImplCore_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__0_value;
static const lean_string_object l_Lean_instInhabitedAttributeImplCore_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "default"};
static const lean_object* l_Lean_instInhabitedAttributeImplCore_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__1_value;
static const lean_ctor_object l_Lean_instInhabitedAttributeImplCore_default___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instInhabitedAttributeImplCore_default___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__2_value_aux_0),((lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(188, 168, 67, 30, 9, 195, 195, 250)}};
static const lean_ctor_object l_Lean_instInhabitedAttributeImplCore_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__2_value_aux_1),((lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__1_value),LEAN_SCALAR_PTR_LITERAL(6, 28, 76, 169, 127, 73, 161, 93)}};
static const lean_object* l_Lean_instInhabitedAttributeImplCore_default___closed__2 = (const lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__2_value;
static const lean_string_object l_Lean_instInhabitedAttributeImplCore_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_instInhabitedAttributeImplCore_default___closed__3 = (const lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__3_value;
static const lean_ctor_object l_Lean_instInhabitedAttributeImplCore_default___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_instInhabitedAttributeImplCore_default___closed__4 = (const lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedAttributeImplCore_default = (const lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedAttributeImplCore = (const lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instBEqAttributeKind_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqAttributeKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqAttributeKind_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqAttributeKind___closed__0 = (const lean_object*)&l_Lean_instBEqAttributeKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqAttributeKind = (const lean_object*)&l_Lean_instBEqAttributeKind___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_instInhabitedAttributeKind_default;
LEAN_EXPORT uint8_t l_Lean_instInhabitedAttributeKind;
static const lean_string_object l_Lean_instToStringAttributeKind___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "global"};
static const lean_object* l_Lean_instToStringAttributeKind___lam__0___closed__0 = (const lean_object*)&l_Lean_instToStringAttributeKind___lam__0___closed__0_value;
static const lean_string_object l_Lean_instToStringAttributeKind___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "local"};
static const lean_object* l_Lean_instToStringAttributeKind___lam__0___closed__1 = (const lean_object*)&l_Lean_instToStringAttributeKind___lam__0___closed__1_value;
static const lean_string_object l_Lean_instToStringAttributeKind___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "scoped"};
static const lean_object* l_Lean_instToStringAttributeKind___lam__0___closed__2 = (const lean_object*)&l_Lean_instToStringAttributeKind___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_instToStringAttributeKind___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_instToStringAttributeKind___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instToStringAttributeKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToStringAttributeKind___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToStringAttributeKind___closed__0 = (const lean_object*)&l_Lean_instToStringAttributeKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToStringAttributeKind = (const lean_object*)&l_Lean_instToStringAttributeKind___closed__0_value;
static lean_once_cell_t l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__0 = (const lean_object*)&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1;
static const lean_string_object l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__2 = (const lean_object*)&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_instInhabitedAttributeImpl_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedAttributeImpl_default___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedAttributeImpl_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__0_value;
static const lean_closure_object l_Lean_instInhabitedAttributeImpl_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedAttributeImpl_default___lam__1___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__4_value)} };
static const lean_object* l_Lean_instInhabitedAttributeImpl_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__1_value;
static const lean_ctor_object l_Lean_instInhabitedAttributeImpl_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__4_value),((lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__0_value),((lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__1_value)}};
static const lean_object* l_Lean_instInhabitedAttributeImpl_default___closed__2 = (const lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedAttributeImpl_default = (const lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT const lean_object* l_Lean_instInhabitedAttributeImpl = (const lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__2_value;
static lean_once_cell_t l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_attributeMapRef;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_registerBuiltinAttribute___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 86, .m_capacity = 86, .m_length = 85, .m_data = "Failed to register attribute: Attributes can only be registered during initialization"};
static const lean_object* l_Lean_registerBuiltinAttribute___closed__0 = (const lean_object*)&l_Lean_registerBuiltinAttribute___closed__0_value;
static lean_once_cell_t l_Lean_registerBuiltinAttribute___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerBuiltinAttribute___closed__1;
static const lean_string_object l_Lean_registerBuiltinAttribute___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Invalid builtin attribute declaration: `"};
static const lean_object* l_Lean_registerBuiltinAttribute___closed__2 = (const lean_object*)&l_Lean_registerBuiltinAttribute___closed__2_value;
static const lean_string_object l_Lean_registerBuiltinAttribute___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "` has already been used"};
static const lean_object* l_Lean_registerBuiltinAttribute___closed__3 = (const lean_object*)&l_Lean_registerBuiltinAttribute___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerBuiltinAttribute___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___closed__0 = (const lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__0_value;
static const lean_string_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "class"};
static const lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___closed__1 = (const lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__1_value;
static const lean_ctor_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__2_value_aux_0),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__2_value_aux_1),((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__2_value_aux_2),((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(149, 14, 146, 125, 144, 1, 65, 64)}};
static const lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___closed__2 = (const lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__2_value;
static const lean_string_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = "Unexpected attribute argument: This attribute takes no arguments"};
static const lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___closed__3 = (const lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__3_value;
static lean_once_cell_t l_Lean_Attribute_Builtin_ensureNoArgs___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___closed__4;
static const lean_string_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___closed__5 = (const lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__5_value;
static const lean_ctor_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__6_value_aux_0),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__6_value_aux_1),((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__6_value_aux_2),((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__5_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___closed__6 = (const lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "macro"};
static const lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___closed__0 = (const lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__1_value_aux_1),((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__1_value_aux_2),((lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(17, 202, 70, 6, 8, 133, 137, 74)}};
static const lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___closed__1 = (const lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__1_value;
static const lean_string_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "export"};
static const lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___closed__2 = (const lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__2_value;
static const lean_ctor_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__3_value_aux_0),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__3_value_aux_1),((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__3_value_aux_2),((lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(43, 70, 85, 26, 88, 142, 178, 115)}};
static const lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___closed__3 = (const lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__3_value;
static const lean_string_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Unexpected attribute argument"};
static const lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___closed__4 = (const lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__4_value;
static lean_once_cell_t l_Lean_Attribute_Builtin_getIdent_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___closed__5;
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Attribute_Builtin_getIdent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "Unexpected attribute argument: Expected identifier, but found"};
static const lean_object* l_Lean_Attribute_Builtin_getIdent___closed__0 = (const lean_object*)&l_Lean_Attribute_Builtin_getIdent___closed__0_value;
static lean_once_cell_t l_Lean_Attribute_Builtin_getIdent___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Attribute_Builtin_getIdent___closed__1;
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getAttrParamOptPrio___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "Unexpected attribute argument: Expected a priority, but found"};
static const lean_object* l_Lean_getAttrParamOptPrio___closed__0 = (const lean_object*)&l_Lean_getAttrParamOptPrio___closed__0_value;
static lean_once_cell_t l_Lean_getAttrParamOptPrio___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getAttrParamOptPrio___closed__1;
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Attribute_Builtin_getPrio___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "Unexpected attribute argument: Expected an optional priority, but found"};
static const lean_object* l_Lean_Attribute_Builtin_getPrio___closed__0 = (const lean_object*)&l_Lean_Attribute_Builtin_getPrio___closed__0_value;
static lean_once_cell_t l_Lean_Attribute_Builtin_getPrio___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Attribute_Builtin_getPrio___closed__1;
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrMustBeGlobal___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Invalid attribute scope: Attribute `["};
static const lean_object* l_Lean_throwAttrMustBeGlobal___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "]` must be global, not `"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___redArg___closed__4_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Cannot add attribute `["};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` to declaration `"};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "` because it is in an imported module"};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___redArg___closed__4_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrNotInAsyncCtx___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "` because it is not from the present async context"};
static const lean_object* l_Lean_throwAttrNotInAsyncCtx___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrNotInAsyncCtx___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " `"};
static const lean_object* l_Lean_throwAttrNotInAsyncCtx___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "]`: Declaration `"};
static const lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "` has type"};
static const lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "\nbut `["};
static const lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__4_value;
static lean_once_cell_t l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5;
static const lean_string_object l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "]` can only be added to declarations of type"};
static const lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__6 = (const lean_object*)&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__6_value;
static lean_once_cell_t l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7;
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Private declaration `"};
static const lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__0 = (const lean_object*)&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1;
static const lean_string_object l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 167, .m_capacity = 167, .m_length = 166, .m_data = "` accessed publicly; this is allowed only because the `backward.privateInPublic` option is enabled. \n\nDisable `backward.privateInPublic.warn` to silence this warning."};
static const lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__2 = (const lean_object*)&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_ensureAttrDeclIsPublic___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "` must be public"};
static const lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0___closed__0 = (const lean_object*)&l_Lean_ensureAttrDeclIsPublic___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_ensureAttrDeclIsMeta___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` must be marked as `meta`"};
static const lean_object* l_Lean_ensureAttrDeclIsMeta___closed__0 = (const lean_object*)&l_Lean_ensureAttrDeclIsMeta___closed__0_value;
static lean_once_cell_t l_Lean_ensureAttrDeclIsMeta___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ensureAttrDeclIsMeta___closed__1;
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_instInhabitedTagAttribute_default___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "(`Inhabited.default` for `IO.Error`)"};
static const lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0___closed__0 = (const lean_object*)&l_Lean_instInhabitedTagAttribute_default___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Lean_instInhabitedTagAttribute_default___lam__0___closed__0_value)}};
static const lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1 = (const lean_object*)&l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0 = (const lean_object*)&l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedTagAttribute_default___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0_value),((lean_object*)&l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0_value),((lean_object*)&l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0_value)}};
static const lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2___closed__1 = (const lean_object*)&l_Lean_instInhabitedTagAttribute_default___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lean_instInhabitedTagAttribute_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedTagAttribute_default___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedTagAttribute_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedTagAttribute_default___closed__0_value;
static const lean_closure_object l_Lean_instInhabitedTagAttribute_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedTagAttribute_default___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedTagAttribute_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedTagAttribute_default___closed__1_value;
static const lean_closure_object l_Lean_instInhabitedTagAttribute_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedTagAttribute_default___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedTagAttribute_default___closed__2 = (const lean_object*)&l_Lean_instInhabitedTagAttribute_default___closed__2_value;
static const lean_closure_object l_Lean_instInhabitedTagAttribute_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedTagAttribute_default___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedTagAttribute_default___closed__3 = (const lean_object*)&l_Lean_instInhabitedTagAttribute_default___closed__3_value;
static lean_once_cell_t l_Lean_instInhabitedTagAttribute_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedTagAttribute_default___closed__4;
static lean_once_cell_t l_Lean_instInhabitedTagAttribute_default___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedTagAttribute_default___closed__5;
static lean_once_cell_t l_Lean_instInhabitedTagAttribute_default___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedTagAttribute_default___closed__6;
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute;
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___auto__1;
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_registerTagAttribute___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "tag attribute"};
static const lean_object* l_Lean_registerTagAttribute___lam__2___closed__0 = (const lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_registerTagAttribute___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__0_value)}};
static const lean_object* l_Lean_registerTagAttribute___lam__2___closed__1 = (const lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__1_value;
static const lean_ctor_object l_Lean_registerTagAttribute___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_registerTagAttribute___lam__2___closed__2 = (const lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__2_value;
static const lean_string_object l_Lean_registerTagAttribute___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "number of local entries: "};
static const lean_object* l_Lean_registerTagAttribute___lam__2___closed__3 = (const lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__3_value;
static const lean_ctor_object l_Lean_registerTagAttribute___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__3_value)}};
static const lean_object* l_Lean_registerTagAttribute___lam__2___closed__4 = (const lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__4_value;
static const lean_ctor_object l_Lean_registerTagAttribute___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__2_value),((lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__4_value)}};
static const lean_object* l_Lean_registerTagAttribute___lam__2___closed__5 = (const lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_registerTagAttribute___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerTagAttribute___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerTagAttribute___closed__0 = (const lean_object*)&l_Lean_registerTagAttribute___closed__0_value;
static const lean_closure_object l_Lean_registerTagAttribute___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerTagAttribute___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerTagAttribute___closed__1 = (const lean_object*)&l_Lean_registerTagAttribute___closed__1_value;
static const lean_closure_object l_Lean_registerTagAttribute___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerTagAttribute___lam__2, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerTagAttribute___closed__2 = (const lean_object*)&l_Lean_registerTagAttribute___closed__2_value;
static const lean_closure_object l_Lean_registerTagAttribute___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerTagAttribute___lam__3, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerTagAttribute___closed__3 = (const lean_object*)&l_Lean_registerTagAttribute___closed__3_value;
static const lean_closure_object l_Lean_registerTagAttribute___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_NameSet_insert, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerTagAttribute___closed__4 = (const lean_object*)&l_Lean_registerTagAttribute___closed__4_value;
static lean_once_cell_t l_Lean_registerTagAttribute___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerTagAttribute___closed__5;
static lean_once_cell_t l_Lean_registerTagAttribute___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerTagAttribute___closed__6;
static const lean_ctor_object l_Lean_registerTagAttribute___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_registerTagAttribute___closed__1_value)}};
static const lean_object* l_Lean_registerTagAttribute___closed__7 = (const lean_object*)&l_Lean_registerTagAttribute___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_hasTag___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0_value),((lean_object*)&l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0_value),((lean_object*)&l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0_value)}};
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lean_instInhabitedParametricAttribute_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___closed__0 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___redArg___closed__0_value;
static const lean_closure_object l_Lean_instInhabitedParametricAttribute_default___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___closed__1 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___redArg___closed__1_value;
static const lean_closure_object l_Lean_instInhabitedParametricAttribute_default___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___closed__2 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___redArg___closed__2_value;
static const lean_closure_object l_Lean_instInhabitedParametricAttribute_default___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___closed__3 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___redArg___closed__3_value;
static lean_once_cell_t l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4;
static lean_once_cell_t l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_instInhabitedParametricAttribute_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedParametricAttribute_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "parametric attribute"};
static const lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__0_value)}};
static const lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__1_value;
static const lean_ctor_object l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__2 = (const lean_object*)&l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__2_value;
static const lean_ctor_object l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__2_value),((lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__4_value)}};
static const lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__3 = (const lean_object*)&l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_registerParametricAttributeExt___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerParametricAttributeExt___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerParametricAttributeExt___redArg___closed__0 = (const lean_object*)&l_Lean_registerParametricAttributeExt___redArg___closed__0_value;
static const lean_closure_object l_Lean_registerParametricAttributeExt___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerParametricAttributeExt___redArg___lam__2, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerParametricAttributeExt___redArg___closed__1 = (const lean_object*)&l_Lean_registerParametricAttributeExt___redArg___closed__1_value;
static const lean_closure_object l_Lean_registerParametricAttributeExt___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerParametricAttributeExt___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerParametricAttributeExt___redArg___closed__2 = (const lean_object*)&l_Lean_registerParametricAttributeExt___redArg___closed__2_value;
static const lean_ctor_object l_Lean_registerParametricAttributeExt___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_registerParametricAttributeExt___redArg___closed__3 = (const lean_object*)&l_Lean_registerParametricAttributeExt___redArg___closed__3_value;
static const lean_closure_object l_Lean_registerParametricAttributeExt___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerParametricAttributeExt___redArg___lam__4___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_registerParametricAttributeExt___redArg___closed__3_value)} };
static const lean_object* l_Lean_registerParametricAttributeExt___redArg___closed__4 = (const lean_object*)&l_Lean_registerParametricAttributeExt___redArg___closed__4_value;
static const lean_closure_object l_Lean_registerParametricAttributeExt___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerParametricAttributeExt___redArg___lam__5___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_registerParametricAttributeExt___redArg___closed__3_value)} };
static const lean_object* l_Lean_registerParametricAttributeExt___redArg___closed__5 = (const lean_object*)&l_Lean_registerParametricAttributeExt___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__3 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__3_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__4 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__4_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__5 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__5_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__6 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__6_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__7 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__7_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__8 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__8_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__9 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__9_value;
static const lean_ctor_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__3_value),((lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__4_value)}};
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__10 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__10_value;
static const lean_ctor_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__10_value),((lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__5_value),((lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__6_value),((lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__7_value),((lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__8_value)}};
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__11 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__11_value;
static const lean_ctor_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__11_value),((lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__9_value)}};
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__12 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__12_value;
static const lean_ctor_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__13 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__13_value;
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Failed to add parametric attribute `["};
static const lean_object* l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0 = (const lean_object*)&l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0_value;
static const lean_string_object l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "]` to `"};
static const lean_object* l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1 = (const lean_object*)&l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1_value;
static const lean_string_object l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "`: Attribute has already been set"};
static const lean_object* l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__2 = (const lean_object*)&l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__2_value;
static const lean_string_object l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "`: Declaration is in an imported module"};
static const lean_object* l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__3 = (const lean_object*)&l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instInhabitedEnumAttributes_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___closed__0 = (const lean_object*)&l_Lean_instInhabitedEnumAttributes_default___redArg___closed__0_value;
static const lean_closure_object l_Lean_instInhabitedEnumAttributes_default___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___closed__1 = (const lean_object*)&l_Lean_instInhabitedEnumAttributes_default___redArg___closed__1_value;
static const lean_closure_object l_Lean_instInhabitedEnumAttributes_default___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___closed__2 = (const lean_object*)&l_Lean_instInhabitedEnumAttributes_default___redArg___closed__2_value;
static lean_once_cell_t l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3;
static lean_once_cell_t l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_instInhabitedEnumAttributes_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedEnumAttributes_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___auto__1;
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_registerEnumAttributes___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "enumeration attribute extension"};
static const lean_object* l_Lean_registerEnumAttributes___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_registerEnumAttributes___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_registerEnumAttributes___redArg___lam__2___closed__0_value)}};
static const lean_object* l_Lean_registerEnumAttributes___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___lam__2___closed__1_value;
static const lean_ctor_object l_Lean_registerEnumAttributes___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_registerEnumAttributes___redArg___lam__2___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_registerEnumAttributes___redArg___lam__2___closed__2 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___lam__2___closed__2_value;
static const lean_ctor_object l_Lean_registerEnumAttributes___redArg___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_registerEnumAttributes___redArg___lam__2___closed__2_value),((lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__4_value)}};
static const lean_object* l_Lean_registerEnumAttributes___redArg___lam__2___closed__3 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___lam__2___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_registerEnumAttributes___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerEnumAttributes___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerEnumAttributes___redArg___closed__0 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___closed__0_value;
static const lean_closure_object l_Lean_registerEnumAttributes___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerEnumAttributes___redArg___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerEnumAttributes___redArg___closed__1 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___closed__1_value;
static const lean_closure_object l_Lean_registerEnumAttributes___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerEnumAttributes___redArg___lam__2, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerEnumAttributes___redArg___closed__2 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___closed__2_value;
static const lean_closure_object l_Lean_registerEnumAttributes___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerEnumAttributes___redArg___lam__3___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerEnumAttributes___redArg___closed__3 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___closed__3_value;
static const lean_closure_object l_Lean_registerEnumAttributes___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerEnumAttributes___redArg___lam__4, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerEnumAttributes___redArg___closed__4 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___closed__4_value;
static const lean_closure_object l_Lean_registerEnumAttributes___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerTagAttribute___lam__6___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_registerEnumAttributes___redArg___closed__5 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___closed__5_value;
static const lean_closure_object l_Lean_registerEnumAttributes___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerEnumAttributes___redArg___lam__6___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_registerEnumAttributes___redArg___closed__6 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___closed__6_value;
static const lean_ctor_object l_Lean_registerEnumAttributes___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_registerEnumAttributes___redArg___closed__7 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___closed__7_value;
static const lean_ctor_object l_Lean_registerEnumAttributes___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_registerEnumAttributes___redArg___closed__1_value)}};
static const lean_object* l_Lean_registerEnumAttributes___redArg___closed__8 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_EnumAttributes_setValue___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Internal error calling `"};
static const lean_object* l_Lean_EnumAttributes_setValue___redArg___closed__0 = (const lean_object*)&l_Lean_EnumAttributes_setValue___redArg___closed__0_value;
static const lean_string_object l_Lean_EnumAttributes_setValue___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = ".setValue` for `"};
static const lean_object* l_Lean_EnumAttributes_setValue___redArg___closed__1 = (const lean_object*)&l_Lean_EnumAttributes_setValue___redArg___closed__1_value;
static const lean_string_object l_Lean_EnumAttributes_setValue___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = ": Declaration is not from this async context `"};
static const lean_object* l_Lean_EnumAttributes_setValue___redArg___closed__2 = (const lean_object*)&l_Lean_EnumAttributes_setValue___redArg___closed__2_value;
static const lean_string_object l_Lean_EnumAttributes_setValue___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Lean_EnumAttributes_setValue___redArg___closed__3 = (const lean_object*)&l_Lean_EnumAttributes_setValue___redArg___closed__3_value;
static const lean_string_object l_Lean_EnumAttributes_setValue___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "(some "};
static const lean_object* l_Lean_EnumAttributes_setValue___redArg___closed__4 = (const lean_object*)&l_Lean_EnumAttributes_setValue___redArg___closed__4_value;
static const lean_string_object l_Lean_EnumAttributes_setValue___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_EnumAttributes_setValue___redArg___closed__5 = (const lean_object*)&l_Lean_EnumAttributes_setValue___redArg___closed__5_value;
static const lean_string_object l_Lean_EnumAttributes_setValue___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = ": Attribute has already been set"};
static const lean_object* l_Lean_EnumAttributes_setValue___redArg___closed__6 = (const lean_object*)&l_Lean_EnumAttributes_setValue___redArg___closed__6_value;
static const lean_string_object l_Lean_EnumAttributes_setValue___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = ": Declaration is in an imported module"};
static const lean_object* l_Lean_EnumAttributes_setValue___redArg___closed__7 = (const lean_object*)&l_Lean_EnumAttributes_setValue___redArg___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_attributeImplBuilderTableRef;
static const lean_string_object l_Lean_registerAttributeImplBuilder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Attribute implementation builder `"};
static const lean_object* l_Lean_registerAttributeImplBuilder___closed__0 = (const lean_object*)&l_Lean_registerAttributeImplBuilder___closed__0_value;
static const lean_string_object l_Lean_registerAttributeImplBuilder___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "` has already been declared"};
static const lean_object* l_Lean_registerAttributeImplBuilder___closed__1 = (const lean_object*)&l_Lean_registerAttributeImplBuilder___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_mkAttributeImplOfEntry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Unknown attribute implementation builder `"};
static const lean_object* l_Lean_mkAttributeImplOfEntry___closed__0 = (const lean_object*)&l_Lean_mkAttributeImplOfEntry___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_instInhabitedAttributeExtensionState_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedAttributeExtensionState_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeExtensionState_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeExtensionState;
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial();
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed(lean_object*);
static const lean_string_object l_Lean_mkAttributeImplOfConstantUnsafe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 104, .m_capacity = 104, .m_length = 103, .m_data = "Unexpected attribute implementation type: `{.ofConstName declName}` is not of type `Lean.AttributeImpl`"};
static const lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___closed__0 = (const lean_object*)&l_Lean_mkAttributeImplOfConstantUnsafe___closed__0_value;
static const lean_ctor_object l_Lean_mkAttributeImplOfConstantUnsafe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_mkAttributeImplOfConstantUnsafe___closed__0_value)}};
static const lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___closed__1 = (const lean_object*)&l_Lean_mkAttributeImplOfConstantUnsafe___closed__1_value;
static const lean_string_object l_Lean_mkAttributeImplOfConstantUnsafe___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___closed__2 = (const lean_object*)&l_Lean_mkAttributeImplOfConstantUnsafe___closed__2_value;
static const lean_string_object l_Lean_mkAttributeImplOfConstantUnsafe___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "AttributeImpl"};
static const lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___closed__3 = (const lean_object*)&l_Lean_mkAttributeImplOfConstantUnsafe___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_addAttrEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object*);
static const lean_closure_object l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Attributes_0__Lean_initFn___lam__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Attributes_0__Lean_initFn___lam__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Attributes_0__Lean_initFn___closed__3_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "attributeExtension"};
static const lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__3_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Attributes_0__Lean_initFn___closed__3_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Attributes_0__Lean_initFn___closed__3_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(219, 25, 250, 145, 208, 184, 170, 105)}};
static const lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Attributes_0__Lean_addAttrEntry, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_attributeExtension;
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames();
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames___boxed(lean_object*);
static const lean_string_object l_Lean_getBuiltinAttributeImpl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Unknown attribute `"};
static const lean_object* l_Lean_getBuiltinAttributeImpl___closed__0 = (const lean_object*)&l_Lean_getBuiltinAttributeImpl___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isAttribute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isAttribute___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAttributeNames(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAttributeImpl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_add(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_add___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_erase(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_erase___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_update_env_attributes(lean_object*);
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_get_num_attributes();
LEAN_EXPORT lean_object* l_Lean_getNumBuiltinAttributesImpl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorIdx(uint8_t v_x_1_){
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
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_AttributeApplicationTime_ctorIdx(v_x_boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_AttributeApplicationTime_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
uint8_t v_t_boxed_21_; lean_object* v_res_22_; 
v_t_boxed_21_ = lean_unbox(v_t_18_);
v_res_22_ = l_Lean_AttributeApplicationTime_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_boxed_21_, v_h_19_, v_k_20_);
lean_dec(v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim___redArg(lean_object* v_afterTypeChecking_23_){
_start:
{
lean_inc(v_afterTypeChecking_23_);
return v_afterTypeChecking_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim___redArg___boxed(lean_object* v_afterTypeChecking_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_AttributeApplicationTime_afterTypeChecking_elim___redArg(v_afterTypeChecking_24_);
lean_dec(v_afterTypeChecking_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim(lean_object* v_motive_26_, uint8_t v_t_27_, lean_object* v_h_28_, lean_object* v_afterTypeChecking_29_){
_start:
{
lean_inc(v_afterTypeChecking_29_);
return v_afterTypeChecking_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim___boxed(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_afterTypeChecking_33_){
_start:
{
uint8_t v_t_boxed_34_; lean_object* v_res_35_; 
v_t_boxed_34_ = lean_unbox(v_t_31_);
v_res_35_ = l_Lean_AttributeApplicationTime_afterTypeChecking_elim(v_motive_30_, v_t_boxed_34_, v_h_32_, v_afterTypeChecking_33_);
lean_dec(v_afterTypeChecking_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim___redArg(lean_object* v_afterCompilation_36_){
_start:
{
lean_inc(v_afterCompilation_36_);
return v_afterCompilation_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim___redArg___boxed(lean_object* v_afterCompilation_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_AttributeApplicationTime_afterCompilation_elim___redArg(v_afterCompilation_37_);
lean_dec(v_afterCompilation_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim(lean_object* v_motive_39_, uint8_t v_t_40_, lean_object* v_h_41_, lean_object* v_afterCompilation_42_){
_start:
{
lean_inc(v_afterCompilation_42_);
return v_afterCompilation_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim___boxed(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_afterCompilation_46_){
_start:
{
uint8_t v_t_boxed_47_; lean_object* v_res_48_; 
v_t_boxed_47_ = lean_unbox(v_t_44_);
v_res_48_ = l_Lean_AttributeApplicationTime_afterCompilation_elim(v_motive_43_, v_t_boxed_47_, v_h_45_, v_afterCompilation_46_);
lean_dec(v_afterCompilation_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim___redArg(lean_object* v_beforeElaboration_49_){
_start:
{
lean_inc(v_beforeElaboration_49_);
return v_beforeElaboration_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim___redArg___boxed(lean_object* v_beforeElaboration_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_AttributeApplicationTime_beforeElaboration_elim___redArg(v_beforeElaboration_50_);
lean_dec(v_beforeElaboration_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim(lean_object* v_motive_52_, uint8_t v_t_53_, lean_object* v_h_54_, lean_object* v_beforeElaboration_55_){
_start:
{
lean_inc(v_beforeElaboration_55_);
return v_beforeElaboration_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim___boxed(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_beforeElaboration_59_){
_start:
{
uint8_t v_t_boxed_60_; lean_object* v_res_61_; 
v_t_boxed_60_ = lean_unbox(v_t_57_);
v_res_61_ = l_Lean_AttributeApplicationTime_beforeElaboration_elim(v_motive_56_, v_t_boxed_60_, v_h_58_, v_beforeElaboration_59_);
lean_dec(v_beforeElaboration_59_);
return v_res_61_;
}
}
static uint8_t _init_l_Lean_instInhabitedAttributeApplicationTime_default(void){
_start:
{
uint8_t v___x_62_; 
v___x_62_ = 0;
return v___x_62_;
}
}
static uint8_t _init_l_Lean_instInhabitedAttributeApplicationTime(void){
_start:
{
uint8_t v___x_63_; 
v___x_63_ = 0;
return v___x_63_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqAttributeApplicationTime_beq(uint8_t v_x_64_, uint8_t v_y_65_){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; uint8_t v___x_68_; 
v___x_66_ = l_Lean_AttributeApplicationTime_ctorIdx(v_x_64_);
v___x_67_ = l_Lean_AttributeApplicationTime_ctorIdx(v_y_65_);
v___x_68_ = lean_nat_dec_eq(v___x_66_, v___x_67_);
lean_dec(v___x_67_);
lean_dec(v___x_66_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqAttributeApplicationTime_beq___boxed(lean_object* v_x_69_, lean_object* v_y_70_){
_start:
{
uint8_t v_x_21__boxed_71_; uint8_t v_y_22__boxed_72_; uint8_t v_res_73_; lean_object* v_r_74_; 
v_x_21__boxed_71_ = lean_unbox(v_x_69_);
v_y_22__boxed_72_ = lean_unbox(v_y_70_);
v_res_73_ = l_Lean_instBEqAttributeApplicationTime_beq(v_x_21__boxed_71_, v_y_22__boxed_72_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLiftImportMAttrM___lam__0(lean_object* v_00_u03b1_77_, lean_object* v_x_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v___x_82_; lean_object* v_env_83_; lean_object* v_ref_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_82_ = lean_st_ref_get(v___y_80_);
v_env_83_ = lean_ctor_get(v___x_82_, 0);
lean_inc_ref(v_env_83_);
lean_dec(v___x_82_);
v_ref_84_ = lean_ctor_get(v___y_79_, 2);
v___x_85_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_79_);
v___x_86_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_86_, 0, v_env_83_);
lean_ctor_set(v___x_86_, 1, v___x_85_);
v___x_87_ = lean_apply_2(v_x_78_, v___x_86_, lean_box(0));
if (lean_obj_tag(v___x_87_) == 0)
{
lean_object* v_a_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_95_; 
v_a_88_ = lean_ctor_get(v___x_87_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_95_ == 0)
{
v___x_90_ = v___x_87_;
v_isShared_91_ = v_isSharedCheck_95_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_a_88_);
lean_dec(v___x_87_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_95_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_93_; 
if (v_isShared_91_ == 0)
{
v___x_93_ = v___x_90_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v_a_88_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
else
{
lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_107_; 
v_a_96_ = lean_ctor_get(v___x_87_, 0);
v_isSharedCheck_107_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_107_ == 0)
{
v___x_98_ = v___x_87_;
v_isShared_99_ = v_isSharedCheck_107_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v___x_87_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_107_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_105_; 
v___x_100_ = lean_io_error_to_string(v_a_96_);
v___x_101_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
v___x_102_ = l_Lean_MessageData_ofFormat(v___x_101_);
lean_inc(v_ref_84_);
v___x_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_103_, 0, v_ref_84_);
lean_ctor_set(v___x_103_, 1, v___x_102_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 0, v___x_103_);
v___x_105_ = v___x_98_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v___x_103_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLiftImportMAttrM___lam__0___boxed(lean_object* v_00_u03b1_108_, lean_object* v_x_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lean_instMonadLiftImportMAttrM___lam__0(v_00_u03b1_108_, v_x_109_, v___y_110_, v___y_111_);
lean_dec(v___y_111_);
lean_dec_ref(v___y_110_);
return v_res_113_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__12(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__10));
v___x_143_ = l_Lean_mkAtom(v___x_142_);
return v___x_143_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__13(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_144_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__12, &l_Lean_AttributeImplCore_ref___autoParam___closed__12_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__12);
v___x_145_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_146_ = lean_array_push(v___x_145_, v___x_144_);
return v___x_146_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__18(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__17));
v___x_156_ = l_Lean_mkAtom(v___x_155_);
return v___x_156_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__19(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_157_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__18, &l_Lean_AttributeImplCore_ref___autoParam___closed__18_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__18);
v___x_158_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_159_ = lean_array_push(v___x_158_, v___x_157_);
return v___x_159_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__20(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_160_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__19, &l_Lean_AttributeImplCore_ref___autoParam___closed__19_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__19);
v___x_161_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__16));
v___x_162_ = lean_box(2);
v___x_163_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
lean_ctor_set(v___x_163_, 1, v___x_161_);
lean_ctor_set(v___x_163_, 2, v___x_160_);
return v___x_163_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__21(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_164_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__20, &l_Lean_AttributeImplCore_ref___autoParam___closed__20_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__20);
v___x_165_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__13, &l_Lean_AttributeImplCore_ref___autoParam___closed__13_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__13);
v___x_166_ = lean_array_push(v___x_165_, v___x_164_);
return v___x_166_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__22(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_167_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__21, &l_Lean_AttributeImplCore_ref___autoParam___closed__21_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__21);
v___x_168_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__11));
v___x_169_ = lean_box(2);
v___x_170_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v___x_168_);
lean_ctor_set(v___x_170_, 2, v___x_167_);
return v___x_170_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__23(void){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_171_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__22, &l_Lean_AttributeImplCore_ref___autoParam___closed__22_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__22);
v___x_172_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_173_ = lean_array_push(v___x_172_, v___x_171_);
return v___x_173_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__24(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_174_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__23, &l_Lean_AttributeImplCore_ref___autoParam___closed__23_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__23);
v___x_175_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__9));
v___x_176_ = lean_box(2);
v___x_177_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
lean_ctor_set(v___x_177_, 1, v___x_175_);
lean_ctor_set(v___x_177_, 2, v___x_174_);
return v___x_177_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__25(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_178_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__24, &l_Lean_AttributeImplCore_ref___autoParam___closed__24_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__24);
v___x_179_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_180_ = lean_array_push(v___x_179_, v___x_178_);
return v___x_180_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__26(void){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_181_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__25, &l_Lean_AttributeImplCore_ref___autoParam___closed__25_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__25);
v___x_182_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__7));
v___x_183_ = lean_box(2);
v___x_184_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
lean_ctor_set(v___x_184_, 1, v___x_182_);
lean_ctor_set(v___x_184_, 2, v___x_181_);
return v___x_184_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__27(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_185_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__26, &l_Lean_AttributeImplCore_ref___autoParam___closed__26_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__26);
v___x_186_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_187_ = lean_array_push(v___x_186_, v___x_185_);
return v___x_187_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_188_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__27, &l_Lean_AttributeImplCore_ref___autoParam___closed__27_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__27);
v___x_189_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__4));
v___x_190_ = lean_box(2);
v___x_191_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
lean_ctor_set(v___x_191_, 1, v___x_189_);
lean_ctor_set(v___x_191_, 2, v___x_188_);
return v___x_191_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam(void){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorIdx(uint8_t v_x_207_){
_start:
{
switch(v_x_207_)
{
case 0:
{
lean_object* v___x_208_; 
v___x_208_ = lean_unsigned_to_nat(0u);
return v___x_208_;
}
case 1:
{
lean_object* v___x_209_; 
v___x_209_ = lean_unsigned_to_nat(1u);
return v___x_209_;
}
default: 
{
lean_object* v___x_210_; 
v___x_210_ = lean_unsigned_to_nat(2u);
return v___x_210_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorIdx___boxed(lean_object* v_x_211_){
_start:
{
uint8_t v_x_boxed_212_; lean_object* v_res_213_; 
v_x_boxed_212_ = lean_unbox(v_x_211_);
v_res_213_ = l_Lean_AttributeKind_ctorIdx(v_x_boxed_212_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___redArg(lean_object* v_k_214_){
_start:
{
lean_inc(v_k_214_);
return v_k_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___redArg___boxed(lean_object* v_k_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_AttributeKind_ctorElim___redArg(v_k_215_);
lean_dec(v_k_215_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim(lean_object* v_motive_217_, lean_object* v_ctorIdx_218_, uint8_t v_t_219_, lean_object* v_h_220_, lean_object* v_k_221_){
_start:
{
lean_inc(v_k_221_);
return v_k_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___boxed(lean_object* v_motive_222_, lean_object* v_ctorIdx_223_, lean_object* v_t_224_, lean_object* v_h_225_, lean_object* v_k_226_){
_start:
{
uint8_t v_t_boxed_227_; lean_object* v_res_228_; 
v_t_boxed_227_ = lean_unbox(v_t_224_);
v_res_228_ = l_Lean_AttributeKind_ctorElim(v_motive_222_, v_ctorIdx_223_, v_t_boxed_227_, v_h_225_, v_k_226_);
lean_dec(v_k_226_);
lean_dec(v_ctorIdx_223_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim___redArg(lean_object* v_global_229_){
_start:
{
lean_inc(v_global_229_);
return v_global_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim___redArg___boxed(lean_object* v_global_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_AttributeKind_global_elim___redArg(v_global_230_);
lean_dec(v_global_230_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim(lean_object* v_motive_232_, uint8_t v_t_233_, lean_object* v_h_234_, lean_object* v_global_235_){
_start:
{
lean_inc(v_global_235_);
return v_global_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim___boxed(lean_object* v_motive_236_, lean_object* v_t_237_, lean_object* v_h_238_, lean_object* v_global_239_){
_start:
{
uint8_t v_t_boxed_240_; lean_object* v_res_241_; 
v_t_boxed_240_ = lean_unbox(v_t_237_);
v_res_241_ = l_Lean_AttributeKind_global_elim(v_motive_236_, v_t_boxed_240_, v_h_238_, v_global_239_);
lean_dec(v_global_239_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim___redArg(lean_object* v_local_242_){
_start:
{
lean_inc(v_local_242_);
return v_local_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim___redArg___boxed(lean_object* v_local_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_AttributeKind_local_elim___redArg(v_local_243_);
lean_dec(v_local_243_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim(lean_object* v_motive_245_, uint8_t v_t_246_, lean_object* v_h_247_, lean_object* v_local_248_){
_start:
{
lean_inc(v_local_248_);
return v_local_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim___boxed(lean_object* v_motive_249_, lean_object* v_t_250_, lean_object* v_h_251_, lean_object* v_local_252_){
_start:
{
uint8_t v_t_boxed_253_; lean_object* v_res_254_; 
v_t_boxed_253_ = lean_unbox(v_t_250_);
v_res_254_ = l_Lean_AttributeKind_local_elim(v_motive_249_, v_t_boxed_253_, v_h_251_, v_local_252_);
lean_dec(v_local_252_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___redArg(lean_object* v_scoped_255_){
_start:
{
lean_inc(v_scoped_255_);
return v_scoped_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___redArg___boxed(lean_object* v_scoped_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_AttributeKind_scoped_elim___redArg(v_scoped_256_);
lean_dec(v_scoped_256_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim(lean_object* v_motive_258_, uint8_t v_t_259_, lean_object* v_h_260_, lean_object* v_scoped_261_){
_start:
{
lean_inc(v_scoped_261_);
return v_scoped_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___boxed(lean_object* v_motive_262_, lean_object* v_t_263_, lean_object* v_h_264_, lean_object* v_scoped_265_){
_start:
{
uint8_t v_t_boxed_266_; lean_object* v_res_267_; 
v_t_boxed_266_ = lean_unbox(v_t_263_);
v_res_267_ = l_Lean_AttributeKind_scoped_elim(v_motive_262_, v_t_boxed_266_, v_h_264_, v_scoped_265_);
lean_dec(v_scoped_265_);
return v_res_267_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t v_x_268_, uint8_t v_y_269_){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_270_ = l_Lean_AttributeKind_ctorIdx(v_x_268_);
v___x_271_ = l_Lean_AttributeKind_ctorIdx(v_y_269_);
v___x_272_ = lean_nat_dec_eq(v___x_270_, v___x_271_);
lean_dec(v___x_271_);
lean_dec(v___x_270_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqAttributeKind_beq___boxed(lean_object* v_x_273_, lean_object* v_y_274_){
_start:
{
uint8_t v_x_21__boxed_275_; uint8_t v_y_22__boxed_276_; uint8_t v_res_277_; lean_object* v_r_278_; 
v_x_21__boxed_275_ = lean_unbox(v_x_273_);
v_y_22__boxed_276_ = lean_unbox(v_y_274_);
v_res_277_ = l_Lean_instBEqAttributeKind_beq(v_x_21__boxed_275_, v_y_22__boxed_276_);
v_r_278_ = lean_box(v_res_277_);
return v_r_278_;
}
}
static uint8_t _init_l_Lean_instInhabitedAttributeKind_default(void){
_start:
{
uint8_t v___x_281_; 
v___x_281_ = 0;
return v___x_281_;
}
}
static uint8_t _init_l_Lean_instInhabitedAttributeKind(void){
_start:
{
uint8_t v___x_282_; 
v___x_282_ = 0;
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringAttributeKind___lam__0(uint8_t v_x_286_){
_start:
{
switch(v_x_286_)
{
case 0:
{
lean_object* v___x_287_; 
v___x_287_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
return v___x_287_;
}
case 1:
{
lean_object* v___x_288_; 
v___x_288_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
return v___x_288_;
}
default: 
{
lean_object* v___x_289_; 
v___x_289_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
return v___x_289_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringAttributeKind___lam__0___boxed(lean_object* v_x_290_){
_start:
{
uint8_t v_x_36__boxed_291_; lean_object* v_res_292_; 
v_x_36__boxed_291_ = lean_unbox(v_x_290_);
v_res_292_ = l_Lean_instToStringAttributeKind___lam__0(v_x_36__boxed_291_);
return v_res_292_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_295_ = l_Lean_instInhabitedMessageData_default;
v___x_296_ = lean_box(0);
v___x_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v___x_295_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__0(lean_object* v_x_298_, lean_object* v___y_299_, uint8_t v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0, &l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0);
v___x_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__0___boxed(lean_object* v_x_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
uint8_t v___y_1022__boxed_312_; lean_object* v_res_313_; 
v___y_1022__boxed_312_ = lean_unbox(v___y_308_);
v_res_313_ = l_Lean_instInhabitedAttributeImpl_default___lam__0(v_x_306_, v___y_307_, v___y_1022__boxed_312_, v___y_309_, v___y_310_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
lean_dec(v___y_307_);
lean_dec(v_x_306_);
return v_res_313_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_314_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0);
v___x_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
return v___x_316_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_317_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1);
v___x_318_ = lean_unsigned_to_nat(0u);
v___x_319_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
lean_ctor_set(v___x_319_, 2, v___x_318_);
lean_ctor_set(v___x_319_, 3, v___x_318_);
lean_ctor_set(v___x_319_, 4, v___x_317_);
lean_ctor_set(v___x_319_, 5, v___x_317_);
lean_ctor_set(v___x_319_, 6, v___x_317_);
lean_ctor_set(v___x_319_, 7, v___x_317_);
lean_ctor_set(v___x_319_, 8, v___x_317_);
lean_ctor_set(v___x_319_, 9, v___x_317_);
lean_ctor_set(v___x_319_, 10, v___x_317_);
return v___x_319_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_320_ = lean_unsigned_to_nat(32u);
v___x_321_ = lean_mk_empty_array_with_capacity(v___x_320_);
v___x_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
return v___x_322_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_323_ = ((size_t)5ULL);
v___x_324_ = lean_unsigned_to_nat(0u);
v___x_325_ = lean_unsigned_to_nat(32u);
v___x_326_ = lean_mk_empty_array_with_capacity(v___x_325_);
v___x_327_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3);
v___x_328_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_328_, 0, v___x_327_);
lean_ctor_set(v___x_328_, 1, v___x_326_);
lean_ctor_set(v___x_328_, 2, v___x_324_);
lean_ctor_set(v___x_328_, 3, v___x_324_);
lean_ctor_set_usize(v___x_328_, 4, v___x_323_);
return v___x_328_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_329_ = lean_box(1);
v___x_330_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4);
v___x_331_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1);
v___x_332_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
lean_ctor_set(v___x_332_, 1, v___x_330_);
lean_ctor_set(v___x_332_, 2, v___x_329_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(lean_object* v_msgData_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
lean_object* v___x_337_; lean_object* v_toCold_338_; lean_object* v_env_339_; lean_object* v_options_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_337_ = lean_st_ref_get(v___y_335_);
v_toCold_338_ = lean_ctor_get(v___y_334_, 0);
v_env_339_ = lean_ctor_get(v___x_337_, 0);
lean_inc_ref(v_env_339_);
lean_dec(v___x_337_);
v_options_340_ = lean_ctor_get(v_toCold_338_, 2);
v___x_341_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2);
v___x_342_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_340_);
v___x_343_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_343_, 0, v_env_339_);
lean_ctor_set(v___x_343_, 1, v___x_341_);
lean_ctor_set(v___x_343_, 2, v___x_342_);
lean_ctor_set(v___x_343_, 3, v_options_340_);
v___x_344_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
lean_ctor_set(v___x_344_, 1, v_msgData_333_);
v___x_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___boxed(lean_object* v_msgData_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v_msgData_346_, v___y_347_, v___y_348_);
lean_dec(v___y_348_);
lean_dec_ref(v___y_347_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(lean_object* v_msg_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v_ref_355_; lean_object* v___x_356_; lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_365_; 
v_ref_355_ = lean_ctor_get(v___y_352_, 2);
v___x_356_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v_msg_351_, v___y_352_, v___y_353_);
v_a_357_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_365_ == 0)
{
v___x_359_ = v___x_356_;
v_isShared_360_ = v_isSharedCheck_365_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v___x_356_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_365_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_361_; lean_object* v___x_363_; 
lean_inc(v_ref_355_);
v___x_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_361_, 0, v_ref_355_);
lean_ctor_set(v___x_361_, 1, v_a_357_);
if (v_isShared_360_ == 0)
{
lean_ctor_set_tag(v___x_359_, 1);
lean_ctor_set(v___x_359_, 0, v___x_361_);
v___x_363_ = v___x_359_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_361_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg___boxed(lean_object* v_msg_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v_msg_366_, v___y_367_, v___y_368_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
return v_res_370_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__0));
v___x_373_ = l_Lean_stringToMessageData(v___x_372_);
return v___x_373_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__2));
v___x_376_ = l_Lean_stringToMessageData(v___x_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1(lean_object* v___x_377_, lean_object* v_decl_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v_name_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v_name_382_ = lean_ctor_get(v___x_377_, 1);
lean_inc(v_name_382_);
lean_dec_ref(v___x_377_);
v___x_383_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_384_ = l_Lean_MessageData_ofName(v_name_382_);
v___x_385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_385_, 0, v___x_383_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
v___x_386_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_387_, 0, v___x_385_);
lean_ctor_set(v___x_387_, 1, v___x_386_);
v___x_388_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_387_, v___y_379_, v___y_380_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1___boxed(lean_object* v___x_389_, lean_object* v_decl_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lean_instInhabitedAttributeImpl_default___lam__1(v___x_389_, v_decl_390_, v___y_391_, v___y_392_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec(v_decl_390_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0(lean_object* v_00_u03b1_403_, lean_object* v_msg_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v_msg_404_, v___y_405_, v___y_406_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___boxed(lean_object* v_00_u03b1_409_, lean_object* v_msg_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0(v_00_u03b1_409_, v_msg_410_, v___y_411_, v___y_412_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
return v_res_414_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_416_ = lean_box(0);
v___x_417_ = lean_unsigned_to_nat(16u);
v___x_418_ = lean_mk_array(v___x_417_, v___x_416_);
return v___x_418_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_419_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_420_ = lean_unsigned_to_nat(0u);
v___x_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
lean_ctor_set(v___x_421_, 1, v___x_419_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_423_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_424_ = lean_st_mk_ref(v___x_423_);
v___x_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2____boxed(lean_object* v_a_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_();
return v_res_427_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(lean_object* v_a_428_, lean_object* v_x_429_){
_start:
{
if (lean_obj_tag(v_x_429_) == 0)
{
uint8_t v___x_430_; 
v___x_430_ = 0;
return v___x_430_;
}
else
{
lean_object* v_key_431_; lean_object* v_tail_432_; uint8_t v___x_433_; 
v_key_431_ = lean_ctor_get(v_x_429_, 0);
v_tail_432_ = lean_ctor_get(v_x_429_, 2);
v___x_433_ = lean_name_eq(v_key_431_, v_a_428_);
if (v___x_433_ == 0)
{
v_x_429_ = v_tail_432_;
goto _start;
}
else
{
return v___x_433_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg___boxed(lean_object* v_a_435_, lean_object* v_x_436_){
_start:
{
uint8_t v_res_437_; lean_object* v_r_438_; 
v_res_437_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_435_, v_x_436_);
lean_dec(v_x_436_);
lean_dec(v_a_435_);
v_r_438_ = lean_box(v_res_437_);
return v_r_438_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(lean_object* v_m_439_, lean_object* v_a_440_){
_start:
{
lean_object* v_buckets_441_; lean_object* v___x_442_; uint64_t v___y_444_; 
v_buckets_441_ = lean_ctor_get(v_m_439_, 1);
v___x_442_ = lean_array_get_size(v_buckets_441_);
if (lean_obj_tag(v_a_440_) == 0)
{
uint64_t v___x_458_; 
v___x_458_ = 1723ULL;
v___y_444_ = v___x_458_;
goto v___jp_443_;
}
else
{
uint64_t v_hash_459_; 
v_hash_459_ = lean_ctor_get_uint64(v_a_440_, sizeof(void*)*2);
v___y_444_ = v_hash_459_;
goto v___jp_443_;
}
v___jp_443_:
{
uint64_t v___x_445_; uint64_t v___x_446_; uint64_t v_fold_447_; uint64_t v___x_448_; uint64_t v___x_449_; uint64_t v___x_450_; size_t v___x_451_; size_t v___x_452_; size_t v___x_453_; size_t v___x_454_; size_t v___x_455_; lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_445_ = 32ULL;
v___x_446_ = lean_uint64_shift_right(v___y_444_, v___x_445_);
v_fold_447_ = lean_uint64_xor(v___y_444_, v___x_446_);
v___x_448_ = 16ULL;
v___x_449_ = lean_uint64_shift_right(v_fold_447_, v___x_448_);
v___x_450_ = lean_uint64_xor(v_fold_447_, v___x_449_);
v___x_451_ = lean_uint64_to_usize(v___x_450_);
v___x_452_ = lean_usize_of_nat(v___x_442_);
v___x_453_ = ((size_t)1ULL);
v___x_454_ = lean_usize_sub(v___x_452_, v___x_453_);
v___x_455_ = lean_usize_land(v___x_451_, v___x_454_);
v___x_456_ = lean_array_uget_borrowed(v_buckets_441_, v___x_455_);
v___x_457_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_440_, v___x_456_);
return v___x_457_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___boxed(lean_object* v_m_460_, lean_object* v_a_461_){
_start:
{
uint8_t v_res_462_; lean_object* v_r_463_; 
v_res_462_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_m_460_, v_a_461_);
lean_dec(v_a_461_);
lean_dec_ref(v_m_460_);
v_r_463_ = lean_box(v_res_462_);
return v_r_463_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(lean_object* v_a_464_, lean_object* v_b_465_, lean_object* v_x_466_){
_start:
{
if (lean_obj_tag(v_x_466_) == 0)
{
lean_dec(v_b_465_);
lean_dec(v_a_464_);
return v_x_466_;
}
else
{
lean_object* v_key_467_; lean_object* v_value_468_; lean_object* v_tail_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_481_; 
v_key_467_ = lean_ctor_get(v_x_466_, 0);
v_value_468_ = lean_ctor_get(v_x_466_, 1);
v_tail_469_ = lean_ctor_get(v_x_466_, 2);
v_isSharedCheck_481_ = !lean_is_exclusive(v_x_466_);
if (v_isSharedCheck_481_ == 0)
{
v___x_471_ = v_x_466_;
v_isShared_472_ = v_isSharedCheck_481_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_tail_469_);
lean_inc(v_value_468_);
lean_inc(v_key_467_);
lean_dec(v_x_466_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_481_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
uint8_t v___x_473_; 
v___x_473_ = lean_name_eq(v_key_467_, v_a_464_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; lean_object* v___x_476_; 
v___x_474_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(v_a_464_, v_b_465_, v_tail_469_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 2, v___x_474_);
v___x_476_ = v___x_471_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_key_467_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v_value_468_);
lean_ctor_set(v_reuseFailAlloc_477_, 2, v___x_474_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
else
{
lean_object* v___x_479_; 
lean_dec(v_value_468_);
lean_dec(v_key_467_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 1, v_b_465_);
lean_ctor_set(v___x_471_, 0, v_a_464_);
v___x_479_ = v___x_471_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_a_464_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v_b_465_);
lean_ctor_set(v_reuseFailAlloc_480_, 2, v_tail_469_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_482_, lean_object* v_x_483_){
_start:
{
if (lean_obj_tag(v_x_483_) == 0)
{
return v_x_482_;
}
else
{
lean_object* v_key_484_; lean_object* v_value_485_; lean_object* v_tail_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_512_; 
v_key_484_ = lean_ctor_get(v_x_483_, 0);
v_value_485_ = lean_ctor_get(v_x_483_, 1);
v_tail_486_ = lean_ctor_get(v_x_483_, 2);
v_isSharedCheck_512_ = !lean_is_exclusive(v_x_483_);
if (v_isSharedCheck_512_ == 0)
{
v___x_488_ = v_x_483_;
v_isShared_489_ = v_isSharedCheck_512_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_tail_486_);
lean_inc(v_value_485_);
lean_inc(v_key_484_);
lean_dec(v_x_483_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_512_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_490_; uint64_t v___y_492_; 
v___x_490_ = lean_array_get_size(v_x_482_);
if (lean_obj_tag(v_key_484_) == 0)
{
uint64_t v___x_510_; 
v___x_510_ = 1723ULL;
v___y_492_ = v___x_510_;
goto v___jp_491_;
}
else
{
uint64_t v_hash_511_; 
v_hash_511_ = lean_ctor_get_uint64(v_key_484_, sizeof(void*)*2);
v___y_492_ = v_hash_511_;
goto v___jp_491_;
}
v___jp_491_:
{
uint64_t v___x_493_; uint64_t v___x_494_; uint64_t v_fold_495_; uint64_t v___x_496_; uint64_t v___x_497_; uint64_t v___x_498_; size_t v___x_499_; size_t v___x_500_; size_t v___x_501_; size_t v___x_502_; size_t v___x_503_; lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_493_ = 32ULL;
v___x_494_ = lean_uint64_shift_right(v___y_492_, v___x_493_);
v_fold_495_ = lean_uint64_xor(v___y_492_, v___x_494_);
v___x_496_ = 16ULL;
v___x_497_ = lean_uint64_shift_right(v_fold_495_, v___x_496_);
v___x_498_ = lean_uint64_xor(v_fold_495_, v___x_497_);
v___x_499_ = lean_uint64_to_usize(v___x_498_);
v___x_500_ = lean_usize_of_nat(v___x_490_);
v___x_501_ = ((size_t)1ULL);
v___x_502_ = lean_usize_sub(v___x_500_, v___x_501_);
v___x_503_ = lean_usize_land(v___x_499_, v___x_502_);
v___x_504_ = lean_array_uget_borrowed(v_x_482_, v___x_503_);
lean_inc(v___x_504_);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 2, v___x_504_);
v___x_506_ = v___x_488_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_key_484_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v_value_485_);
lean_ctor_set(v_reuseFailAlloc_509_, 2, v___x_504_);
v___x_506_ = v_reuseFailAlloc_509_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
lean_object* v___x_507_; 
v___x_507_ = lean_array_uset(v_x_482_, v___x_503_, v___x_506_);
v_x_482_ = v___x_507_;
v_x_483_ = v_tail_486_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(lean_object* v_i_513_, lean_object* v_source_514_, lean_object* v_target_515_){
_start:
{
lean_object* v___x_516_; uint8_t v___x_517_; 
v___x_516_ = lean_array_get_size(v_source_514_);
v___x_517_ = lean_nat_dec_lt(v_i_513_, v___x_516_);
if (v___x_517_ == 0)
{
lean_dec_ref(v_source_514_);
lean_dec(v_i_513_);
return v_target_515_;
}
else
{
lean_object* v_es_518_; lean_object* v___x_519_; lean_object* v_source_520_; lean_object* v_target_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v_es_518_ = lean_array_fget(v_source_514_, v_i_513_);
v___x_519_ = lean_box(0);
v_source_520_ = lean_array_fset(v_source_514_, v_i_513_, v___x_519_);
v_target_521_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(v_target_515_, v_es_518_);
v___x_522_ = lean_unsigned_to_nat(1u);
v___x_523_ = lean_nat_add(v_i_513_, v___x_522_);
lean_dec(v_i_513_);
v_i_513_ = v___x_523_;
v_source_514_ = v_source_520_;
v_target_515_ = v_target_521_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(lean_object* v_data_525_){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v_nbuckets_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_526_ = lean_array_get_size(v_data_525_);
v___x_527_ = lean_unsigned_to_nat(2u);
v_nbuckets_528_ = lean_nat_mul(v___x_526_, v___x_527_);
v___x_529_ = lean_unsigned_to_nat(0u);
v___x_530_ = lean_box(0);
v___x_531_ = lean_mk_array(v_nbuckets_528_, v___x_530_);
v___x_532_ = lean_array_propagate_mark(v_data_525_, v___x_531_);
v___x_533_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(v___x_529_, v_data_525_, v___x_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(lean_object* v_m_534_, lean_object* v_a_535_, lean_object* v_b_536_){
_start:
{
lean_object* v_size_537_; lean_object* v_buckets_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_584_; 
v_size_537_ = lean_ctor_get(v_m_534_, 0);
v_buckets_538_ = lean_ctor_get(v_m_534_, 1);
v_isSharedCheck_584_ = !lean_is_exclusive(v_m_534_);
if (v_isSharedCheck_584_ == 0)
{
v___x_540_ = v_m_534_;
v_isShared_541_ = v_isSharedCheck_584_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_buckets_538_);
lean_inc(v_size_537_);
lean_dec(v_m_534_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_584_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_542_; uint64_t v___y_544_; 
v___x_542_ = lean_array_get_size(v_buckets_538_);
if (lean_obj_tag(v_a_535_) == 0)
{
uint64_t v___x_582_; 
v___x_582_ = 1723ULL;
v___y_544_ = v___x_582_;
goto v___jp_543_;
}
else
{
uint64_t v_hash_583_; 
v_hash_583_ = lean_ctor_get_uint64(v_a_535_, sizeof(void*)*2);
v___y_544_ = v_hash_583_;
goto v___jp_543_;
}
v___jp_543_:
{
uint64_t v___x_545_; uint64_t v___x_546_; uint64_t v_fold_547_; uint64_t v___x_548_; uint64_t v___x_549_; uint64_t v___x_550_; size_t v___x_551_; size_t v___x_552_; size_t v___x_553_; size_t v___x_554_; size_t v___x_555_; lean_object* v_bkt_556_; uint8_t v___x_557_; 
v___x_545_ = 32ULL;
v___x_546_ = lean_uint64_shift_right(v___y_544_, v___x_545_);
v_fold_547_ = lean_uint64_xor(v___y_544_, v___x_546_);
v___x_548_ = 16ULL;
v___x_549_ = lean_uint64_shift_right(v_fold_547_, v___x_548_);
v___x_550_ = lean_uint64_xor(v_fold_547_, v___x_549_);
v___x_551_ = lean_uint64_to_usize(v___x_550_);
v___x_552_ = lean_usize_of_nat(v___x_542_);
v___x_553_ = ((size_t)1ULL);
v___x_554_ = lean_usize_sub(v___x_552_, v___x_553_);
v___x_555_ = lean_usize_land(v___x_551_, v___x_554_);
v_bkt_556_ = lean_array_uget_borrowed(v_buckets_538_, v___x_555_);
v___x_557_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_535_, v_bkt_556_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; lean_object* v_size_x27_559_; lean_object* v___x_560_; lean_object* v_buckets_x27_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_558_ = lean_unsigned_to_nat(1u);
v_size_x27_559_ = lean_nat_add(v_size_537_, v___x_558_);
lean_dec(v_size_537_);
lean_inc(v_bkt_556_);
v___x_560_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_560_, 0, v_a_535_);
lean_ctor_set(v___x_560_, 1, v_b_536_);
lean_ctor_set(v___x_560_, 2, v_bkt_556_);
v_buckets_x27_561_ = lean_array_uset(v_buckets_538_, v___x_555_, v___x_560_);
v___x_562_ = lean_unsigned_to_nat(4u);
v___x_563_ = lean_nat_mul(v_size_x27_559_, v___x_562_);
v___x_564_ = lean_unsigned_to_nat(3u);
v___x_565_ = lean_nat_div(v___x_563_, v___x_564_);
lean_dec(v___x_563_);
v___x_566_ = lean_array_get_size(v_buckets_x27_561_);
v___x_567_ = lean_nat_dec_le(v___x_565_, v___x_566_);
lean_dec(v___x_565_);
if (v___x_567_ == 0)
{
lean_object* v_val_568_; lean_object* v___x_570_; 
v_val_568_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(v_buckets_x27_561_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 1, v_val_568_);
lean_ctor_set(v___x_540_, 0, v_size_x27_559_);
v___x_570_ = v___x_540_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_size_x27_559_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_val_568_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
else
{
lean_object* v___x_573_; 
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 1, v_buckets_x27_561_);
lean_ctor_set(v___x_540_, 0, v_size_x27_559_);
v___x_573_ = v___x_540_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_size_x27_559_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v_buckets_x27_561_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
else
{
lean_object* v___x_575_; lean_object* v_buckets_x27_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_580_; 
lean_inc(v_bkt_556_);
v___x_575_ = lean_box(0);
v_buckets_x27_576_ = lean_array_uset(v_buckets_538_, v___x_555_, v___x_575_);
v___x_577_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(v_a_535_, v_b_536_, v_bkt_556_);
v___x_578_ = lean_array_uset(v_buckets_x27_576_, v___x_555_, v___x_577_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 1, v___x_578_);
v___x_580_ = v___x_540_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_size_537_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v___x_578_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_registerBuiltinAttribute___closed__1(void){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__0));
v___x_587_ = lean_mk_io_user_error(v___x_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerBuiltinAttribute(lean_object* v_attr_590_){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v_toAttributeImplCore_594_; lean_object* v_name_595_; uint8_t v___x_596_; 
v___x_592_ = l_Lean_attributeMapRef;
v___x_593_ = lean_st_ref_get(v___x_592_);
v_toAttributeImplCore_594_ = lean_ctor_get(v_attr_590_, 0);
v_name_595_ = lean_ctor_get(v_toAttributeImplCore_594_, 1);
lean_inc(v_name_595_);
v___x_596_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_593_, v_name_595_);
lean_dec(v___x_593_);
if (v___x_596_ == 0)
{
uint8_t v___x_597_; 
v___x_597_ = l_Lean_initializing();
if (v___x_597_ == 0)
{
lean_object* v___x_598_; lean_object* v___x_599_; 
lean_dec(v_name_595_);
lean_dec_ref(v_attr_590_);
v___x_598_ = lean_obj_once(&l_Lean_registerBuiltinAttribute___closed__1, &l_Lean_registerBuiltinAttribute___closed__1_once, _init_l_Lean_registerBuiltinAttribute___closed__1);
v___x_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
return v___x_599_;
}
else
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_600_ = lean_st_ref_take(v___x_592_);
v___x_601_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_600_, v_name_595_, v_attr_590_);
v___x_602_ = lean_st_ref_put(v___x_592_, v___x_601_);
v___x_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
return v___x_603_;
}
}
else
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
lean_dec_ref(v_attr_590_);
v___x_604_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_605_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_595_, v___x_596_);
v___x_606_ = lean_string_append(v___x_604_, v___x_605_);
lean_dec_ref(v___x_605_);
v___x_607_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_608_ = lean_string_append(v___x_606_, v___x_607_);
v___x_609_ = lean_mk_io_user_error(v___x_608_);
v___x_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
return v___x_610_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerBuiltinAttribute___boxed(lean_object* v_attr_611_, lean_object* v_a_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Lean_registerBuiltinAttribute(v_attr_611_);
return v_res_613_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0(lean_object* v_00_u03b2_614_, lean_object* v_m_615_, lean_object* v_a_616_){
_start:
{
uint8_t v___x_617_; 
v___x_617_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_m_615_, v_a_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___boxed(lean_object* v_00_u03b2_618_, lean_object* v_m_619_, lean_object* v_a_620_){
_start:
{
uint8_t v_res_621_; lean_object* v_r_622_; 
v_res_621_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0(v_00_u03b2_618_, v_m_619_, v_a_620_);
lean_dec(v_a_620_);
lean_dec_ref(v_m_619_);
v_r_622_ = lean_box(v_res_621_);
return v_r_622_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1(lean_object* v_00_u03b2_623_, lean_object* v_m_624_, lean_object* v_a_625_, lean_object* v_b_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_m_624_, v_a_625_, v_b_626_);
return v___x_627_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0(lean_object* v_00_u03b2_628_, lean_object* v_a_629_, lean_object* v_x_630_){
_start:
{
uint8_t v___x_631_; 
v___x_631_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_629_, v_x_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___boxed(lean_object* v_00_u03b2_632_, lean_object* v_a_633_, lean_object* v_x_634_){
_start:
{
uint8_t v_res_635_; lean_object* v_r_636_; 
v_res_635_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0(v_00_u03b2_632_, v_a_633_, v_x_634_);
lean_dec(v_x_634_);
lean_dec(v_a_633_);
v_r_636_ = lean_box(v_res_635_);
return v_r_636_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2(lean_object* v_00_u03b2_637_, lean_object* v_data_638_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(v_data_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3(lean_object* v_00_u03b2_640_, lean_object* v_a_641_, lean_object* v_b_642_, lean_object* v_x_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(v_a_641_, v_b_642_, v_x_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_645_, lean_object* v_i_646_, lean_object* v_source_647_, lean_object* v_target_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(v_i_646_, v_source_647_, v_target_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_650_, lean_object* v_x_651_, lean_object* v_x_652_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(v_x_651_, v_x_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(lean_object* v_ref_654_, lean_object* v_msg_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
lean_object* v_toCold_659_; lean_object* v_currRecDepth_660_; lean_object* v_ref_661_; uint16_t v_optionFlags_662_; uint8_t v_suppressElabErrors_663_; uint8_t v_isRecordingDeps_664_; lean_object* v_ref_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v_toCold_659_ = lean_ctor_get(v___y_656_, 0);
v_currRecDepth_660_ = lean_ctor_get(v___y_656_, 1);
v_ref_661_ = lean_ctor_get(v___y_656_, 2);
v_optionFlags_662_ = lean_ctor_get_uint16(v___y_656_, sizeof(void*)*3);
v_suppressElabErrors_663_ = lean_ctor_get_uint8(v___y_656_, sizeof(void*)*3 + 2);
v_isRecordingDeps_664_ = lean_ctor_get_uint8(v___y_656_, sizeof(void*)*3 + 3);
v_ref_665_ = l_Lean_replaceRef(v_ref_654_, v_ref_661_);
lean_inc(v_currRecDepth_660_);
lean_inc_ref(v_toCold_659_);
v___x_666_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_666_, 0, v_toCold_659_);
lean_ctor_set(v___x_666_, 1, v_currRecDepth_660_);
lean_ctor_set(v___x_666_, 2, v_ref_665_);
lean_ctor_set_uint16(v___x_666_, sizeof(void*)*3, v_optionFlags_662_);
lean_ctor_set_uint8(v___x_666_, sizeof(void*)*3 + 2, v_suppressElabErrors_663_);
lean_ctor_set_uint8(v___x_666_, sizeof(void*)*3 + 3, v_isRecordingDeps_664_);
v___x_667_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v_msg_655_, v___x_666_, v___y_657_);
lean_dec_ref_known(v___x_666_, 3);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg___boxed(lean_object* v_ref_668_, lean_object* v_msg_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_ref_668_, v_msg_669_, v___y_670_, v___y_671_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v_ref_668_);
return v_res_673_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_ensureNoArgs___closed__4(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__3));
v___x_683_ = l_Lean_stringToMessageData(v___x_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object* v_stx_690_, lean_object* v_a_691_, lean_object* v_a_692_){
_start:
{
lean_object* v___x_694_; uint8_t v___y_705_; lean_object* v___x_711_; uint8_t v___x_712_; 
lean_inc(v_stx_690_);
v___x_694_ = l_Lean_Syntax_getKind(v_stx_690_);
v___x_711_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_712_ = lean_name_eq(v___x_694_, v___x_711_);
if (v___x_712_ == 0)
{
v___y_705_ = v___x_712_;
goto v___jp_704_;
}
else
{
lean_object* v___x_713_; lean_object* v___x_714_; uint8_t v___x_715_; 
v___x_713_ = lean_unsigned_to_nat(1u);
v___x_714_ = l_Lean_Syntax_getArg(v_stx_690_, v___x_713_);
v___x_715_ = l_Lean_Syntax_isNone(v___x_714_);
lean_dec(v___x_714_);
v___y_705_ = v___x_715_;
goto v___jp_704_;
}
v___jp_695_:
{
lean_object* v___x_696_; uint8_t v___x_697_; 
v___x_696_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__2));
v___x_697_ = lean_name_eq(v___x_694_, v___x_696_);
lean_dec(v___x_694_);
if (v___x_697_ == 0)
{
if (lean_obj_tag(v_stx_690_) == 0)
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = lean_box(0);
v___x_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
return v___x_699_;
}
else
{
lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_700_ = lean_obj_once(&l_Lean_Attribute_Builtin_ensureNoArgs___closed__4, &l_Lean_Attribute_Builtin_ensureNoArgs___closed__4_once, _init_l_Lean_Attribute_Builtin_ensureNoArgs___closed__4);
v___x_701_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_690_, v___x_700_, v_a_691_, v_a_692_);
lean_dec(v_stx_690_);
return v___x_701_;
}
}
else
{
lean_object* v___x_702_; lean_object* v___x_703_; 
lean_dec(v_stx_690_);
v___x_702_ = lean_box(0);
v___x_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
return v___x_703_;
}
}
v___jp_704_:
{
if (v___y_705_ == 0)
{
goto v___jp_695_;
}
else
{
lean_object* v___x_706_; lean_object* v___x_707_; uint8_t v___x_708_; 
v___x_706_ = lean_unsigned_to_nat(2u);
v___x_707_ = l_Lean_Syntax_getArg(v_stx_690_, v___x_706_);
v___x_708_ = l_Lean_Syntax_isNone(v___x_707_);
lean_dec(v___x_707_);
if (v___x_708_ == 0)
{
goto v___jp_695_;
}
else
{
lean_object* v___x_709_; lean_object* v___x_710_; 
lean_dec(v___x_694_);
lean_dec(v_stx_690_);
v___x_709_ = lean_box(0);
v___x_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
return v___x_710_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___boxed(lean_object* v_stx_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_716_, v_a_717_, v_a_718_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0(lean_object* v_00_u03b1_721_, lean_object* v_ref_722_, lean_object* v_msg_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_ref_722_, v_msg_723_, v___y_724_, v___y_725_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___boxed(lean_object* v_00_u03b1_728_, lean_object* v_ref_729_, lean_object* v_msg_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0(v_00_u03b1_728_, v_ref_729_, v_msg_730_, v___y_731_, v___y_732_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v_ref_729_);
return v_res_734_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getIdent_x3f___closed__5(void){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__4));
v___x_749_ = l_Lean_stringToMessageData(v___x_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f(lean_object* v_stx_750_, lean_object* v_a_751_, lean_object* v_a_752_){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; uint8_t v___x_764_; 
lean_inc(v_stx_750_);
v___x_762_ = l_Lean_Syntax_getKind(v_stx_750_);
v___x_763_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_764_ = lean_name_eq(v___x_762_, v___x_763_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; uint8_t v___x_766_; 
v___x_765_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__1));
v___x_766_ = lean_name_eq(v___x_762_, v___x_765_);
if (v___x_766_ == 0)
{
lean_object* v___x_767_; uint8_t v___x_768_; 
v___x_767_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__3));
v___x_768_ = lean_name_eq(v___x_762_, v___x_767_);
lean_dec(v___x_762_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = lean_obj_once(&l_Lean_Attribute_Builtin_getIdent_x3f___closed__5, &l_Lean_Attribute_Builtin_getIdent_x3f___closed__5_once, _init_l_Lean_Attribute_Builtin_getIdent_x3f___closed__5);
v___x_770_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_750_, v___x_769_, v_a_751_, v_a_752_);
lean_dec(v_stx_750_);
return v___x_770_;
}
else
{
goto v___jp_754_;
}
}
else
{
lean_dec(v___x_762_);
goto v___jp_754_;
}
}
else
{
lean_object* v___x_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
lean_dec(v___x_762_);
v___x_771_ = lean_unsigned_to_nat(1u);
v___x_772_ = l_Lean_Syntax_getArg(v_stx_750_, v___x_771_);
lean_dec(v_stx_750_);
v___x_773_ = l_Lean_Syntax_isNone(v___x_772_);
if (v___x_773_ == 0)
{
if (v___x_764_ == 0)
{
lean_dec(v___x_772_);
goto v___jp_759_;
}
else
{
lean_object* v___x_774_; lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_774_ = lean_unsigned_to_nat(0u);
v___x_775_ = l_Lean_Syntax_getArg(v___x_772_, v___x_774_);
lean_dec(v___x_772_);
v___x_776_ = l_Lean_Syntax_isIdent(v___x_775_);
if (v___x_776_ == 0)
{
lean_dec(v___x_775_);
goto v___jp_759_;
}
else
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_777_, 0, v___x_775_);
v___x_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
return v___x_778_;
}
}
}
else
{
lean_dec(v___x_772_);
goto v___jp_759_;
}
}
v___jp_754_:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_755_ = lean_unsigned_to_nat(1u);
v___x_756_ = l_Lean_Syntax_getArg(v_stx_750_, v___x_755_);
lean_dec(v_stx_750_);
v___x_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
v___x_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_758_, 0, v___x_757_);
return v___x_758_;
}
v___jp_759_:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = lean_box(0);
v___x_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
return v___x_761_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___boxed(lean_object* v_stx_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_779_, v_a_780_, v_a_781_);
lean_dec(v_a_781_);
lean_dec_ref(v_a_780_);
return v_res_783_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getIdent___closed__1(void){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent___closed__0));
v___x_786_ = l_Lean_stringToMessageData(v___x_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent(lean_object* v_stx_787_, lean_object* v_a_788_, lean_object* v_a_789_){
_start:
{
lean_object* v___x_791_; 
lean_inc(v_stx_787_);
v___x_791_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_787_, v_a_788_, v_a_789_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_805_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_805_ == 0)
{
v___x_794_ = v___x_791_;
v_isShared_795_ = v_isSharedCheck_805_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_791_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_805_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
if (lean_obj_tag(v_a_792_) == 0)
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
lean_del_object(v___x_794_);
v___x_796_ = lean_obj_once(&l_Lean_Attribute_Builtin_getIdent___closed__1, &l_Lean_Attribute_Builtin_getIdent___closed__1_once, _init_l_Lean_Attribute_Builtin_getIdent___closed__1);
lean_inc(v_stx_787_);
v___x_797_ = l_Lean_MessageData_ofSyntax(v_stx_787_);
v___x_798_ = l_Lean_indentD(v___x_797_);
v___x_799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_799_, 0, v___x_796_);
lean_ctor_set(v___x_799_, 1, v___x_798_);
v___x_800_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_787_, v___x_799_, v_a_788_, v_a_789_);
lean_dec(v_stx_787_);
return v___x_800_;
}
else
{
lean_object* v_val_801_; lean_object* v___x_803_; 
lean_dec(v_stx_787_);
v_val_801_ = lean_ctor_get(v_a_792_, 0);
lean_inc(v_val_801_);
lean_dec_ref_known(v_a_792_, 1);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 0, v_val_801_);
v___x_803_ = v___x_794_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_val_801_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
else
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_813_; 
lean_dec(v_stx_787_);
v_a_806_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_813_ == 0)
{
v___x_808_ = v___x_791_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_791_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_806_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent___boxed(lean_object* v_stx_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lean_Attribute_Builtin_getIdent(v_stx_814_, v_a_815_, v_a_816_);
lean_dec(v_a_816_);
lean_dec_ref(v_a_815_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f(lean_object* v_stx_819_, lean_object* v_a_820_, lean_object* v_a_821_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_819_, v_a_820_, v_a_821_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_844_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_844_ == 0)
{
v___x_826_ = v___x_823_;
v_isShared_827_ = v_isSharedCheck_844_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_823_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_844_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
if (lean_obj_tag(v_a_824_) == 0)
{
lean_object* v___x_828_; lean_object* v___x_830_; 
v___x_828_ = lean_box(0);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v___x_828_);
v___x_830_ = v___x_826_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_828_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
else
{
lean_object* v_val_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_843_; 
v_val_832_ = lean_ctor_get(v_a_824_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v_a_824_);
if (v_isSharedCheck_843_ == 0)
{
v___x_834_ = v_a_824_;
v_isShared_835_ = v_isSharedCheck_843_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_val_832_);
lean_dec(v_a_824_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_843_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_836_; lean_object* v___x_838_; 
v___x_836_ = l_Lean_Syntax_getId(v_val_832_);
lean_dec(v_val_832_);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 0, v___x_836_);
v___x_838_ = v___x_834_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_836_);
v___x_838_ = v_reuseFailAlloc_842_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
lean_object* v___x_840_; 
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v___x_838_);
v___x_840_ = v___x_826_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_838_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
}
}
else
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
v_a_845_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_852_ == 0)
{
v___x_847_ = v___x_823_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_823_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_a_845_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f___boxed(lean_object* v_stx_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Lean_Attribute_Builtin_getId_x3f(v_stx_853_, v_a_854_, v_a_855_);
lean_dec(v_a_855_);
lean_dec_ref(v_a_854_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId(lean_object* v_stx_858_, lean_object* v_a_859_, lean_object* v_a_860_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_Attribute_Builtin_getIdent(v_stx_858_, v_a_859_, v_a_860_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_871_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_871_ == 0)
{
v___x_865_ = v___x_862_;
v_isShared_866_ = v_isSharedCheck_871_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_862_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_871_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_867_; lean_object* v___x_869_; 
v___x_867_ = l_Lean_Syntax_getId(v_a_863_);
lean_dec(v_a_863_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___x_867_);
v___x_869_ = v___x_865_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_867_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
else
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
v_a_872_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_862_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_862_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_872_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId___boxed(lean_object* v_stx_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_Attribute_Builtin_getId(v_stx_880_, v_a_881_, v_a_882_);
lean_dec(v_a_882_);
lean_dec_ref(v_a_881_);
return v_res_884_;
}
}
static lean_object* _init_l_Lean_getAttrParamOptPrio___closed__1(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = ((lean_object*)(l_Lean_getAttrParamOptPrio___closed__0));
v___x_887_ = l_Lean_stringToMessageData(v___x_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio(lean_object* v_optPrioStx_888_, lean_object* v_a_889_, lean_object* v_a_890_){
_start:
{
uint8_t v___x_892_; 
v___x_892_ = l_Lean_Syntax_isNone(v_optPrioStx_888_);
if (v___x_892_ == 0)
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_893_ = lean_unsigned_to_nat(0u);
v___x_894_ = l_Lean_Syntax_getArg(v_optPrioStx_888_, v___x_893_);
v___x_895_ = l_Lean_Syntax_isNatLit_x3f(v___x_894_);
lean_dec(v___x_894_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_896_ = lean_obj_once(&l_Lean_getAttrParamOptPrio___closed__1, &l_Lean_getAttrParamOptPrio___closed__1_once, _init_l_Lean_getAttrParamOptPrio___closed__1);
lean_inc(v_optPrioStx_888_);
v___x_897_ = l_Lean_MessageData_ofSyntax(v_optPrioStx_888_);
v___x_898_ = l_Lean_indentD(v___x_897_);
v___x_899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_896_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
v___x_900_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_optPrioStx_888_, v___x_899_, v_a_889_, v_a_890_);
lean_dec(v_optPrioStx_888_);
return v___x_900_;
}
else
{
lean_object* v_val_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_908_; 
lean_dec(v_optPrioStx_888_);
v_val_901_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_908_ == 0)
{
v___x_903_ = v___x_895_;
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_val_901_);
lean_dec(v___x_895_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_904_ == 0)
{
lean_ctor_set_tag(v___x_903_, 0);
v___x_906_ = v___x_903_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_val_901_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
else
{
lean_object* v___x_909_; lean_object* v___x_910_; 
lean_dec(v_optPrioStx_888_);
v___x_909_ = lean_unsigned_to_nat(1000u);
v___x_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_910_, 0, v___x_909_);
return v___x_910_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio___boxed(lean_object* v_optPrioStx_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Lean_getAttrParamOptPrio(v_optPrioStx_911_, v_a_912_, v_a_913_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
return v_res_915_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getPrio___closed__1(void){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_917_ = ((lean_object*)(l_Lean_Attribute_Builtin_getPrio___closed__0));
v___x_918_ = l_Lean_stringToMessageData(v___x_917_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio(lean_object* v_stx_919_, lean_object* v_a_920_, lean_object* v_a_921_){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; uint8_t v___x_925_; 
lean_inc(v_stx_919_);
v___x_923_ = l_Lean_Syntax_getKind(v_stx_919_);
v___x_924_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_925_ = lean_name_eq(v___x_923_, v___x_924_);
lean_dec(v___x_923_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_926_ = lean_obj_once(&l_Lean_Attribute_Builtin_getPrio___closed__1, &l_Lean_Attribute_Builtin_getPrio___closed__1_once, _init_l_Lean_Attribute_Builtin_getPrio___closed__1);
lean_inc(v_stx_919_);
v___x_927_ = l_Lean_MessageData_ofSyntax(v_stx_919_);
v___x_928_ = l_Lean_indentD(v___x_927_);
v___x_929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_926_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
v___x_930_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_919_, v___x_929_, v_a_920_, v_a_921_);
lean_dec(v_stx_919_);
return v___x_930_;
}
else
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_931_ = lean_unsigned_to_nat(1u);
v___x_932_ = l_Lean_Syntax_getArg(v_stx_919_, v___x_931_);
lean_dec(v_stx_919_);
v___x_933_ = l_Lean_getAttrParamOptPrio(v___x_932_, v_a_920_, v_a_921_);
return v___x_933_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio___boxed(lean_object* v_stx_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lean_Attribute_Builtin_getPrio(v_stx_934_, v_a_935_, v_a_936_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
return v_res_938_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1(void){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__0));
v___x_941_ = l_Lean_stringToMessageData(v___x_940_);
return v___x_941_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__2));
v___x_944_ = l_Lean_stringToMessageData(v___x_943_);
return v___x_944_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5(void){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_947_ = l_Lean_stringToMessageData(v___x_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg(lean_object* v_inst_948_, lean_object* v_inst_949_, lean_object* v_name_950_, uint8_t v_kind_951_){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___y_958_; 
v___x_952_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_953_ = l_Lean_MessageData_ofName(v_name_950_);
v___x_954_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_952_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v___x_955_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_954_);
lean_ctor_set(v___x_956_, 1, v___x_955_);
switch(v_kind_951_)
{
case 0:
{
lean_object* v___x_965_; 
v___x_965_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_958_ = v___x_965_;
goto v___jp_957_;
}
case 1:
{
lean_object* v___x_966_; 
v___x_966_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_958_ = v___x_966_;
goto v___jp_957_;
}
default: 
{
lean_object* v___x_967_; 
v___x_967_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_958_ = v___x_967_;
goto v___jp_957_;
}
}
v___jp_957_:
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
lean_inc_ref(v___y_958_);
v___x_959_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_959_, 0, v___y_958_);
v___x_960_ = l_Lean_MessageData_ofFormat(v___x_959_);
v___x_961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_956_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
v___x_962_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_961_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
v___x_964_ = l_Lean_throwError___redArg(v_inst_948_, v_inst_949_, v___x_963_);
return v___x_964_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg___boxed(lean_object* v_inst_968_, lean_object* v_inst_969_, lean_object* v_name_970_, lean_object* v_kind_971_){
_start:
{
uint8_t v_kind_boxed_972_; lean_object* v_res_973_; 
v_kind_boxed_972_ = lean_unbox(v_kind_971_);
v_res_973_ = l_Lean_throwAttrMustBeGlobal___redArg(v_inst_968_, v_inst_969_, v_name_970_, v_kind_boxed_972_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal(lean_object* v_m_974_, lean_object* v_inst_975_, lean_object* v_inst_976_, lean_object* v_00_u03b1_977_, lean_object* v_name_978_, uint8_t v_kind_979_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l_Lean_throwAttrMustBeGlobal___redArg(v_inst_975_, v_inst_976_, v_name_978_, v_kind_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___boxed(lean_object* v_m_981_, lean_object* v_inst_982_, lean_object* v_inst_983_, lean_object* v_00_u03b1_984_, lean_object* v_name_985_, lean_object* v_kind_986_){
_start:
{
uint8_t v_kind_boxed_987_; lean_object* v_res_988_; 
v_kind_boxed_987_ = lean_unbox(v_kind_986_);
v_res_988_ = l_Lean_throwAttrMustBeGlobal(v_m_981_, v_inst_982_, v_inst_983_, v_00_u03b1_984_, v_name_985_, v_kind_boxed_987_);
return v_res_988_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1(void){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__0));
v___x_991_ = l_Lean_stringToMessageData(v___x_990_);
return v___x_991_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__2));
v___x_994_ = l_Lean_stringToMessageData(v___x_993_);
return v___x_994_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5(void){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__4));
v___x_997_ = l_Lean_stringToMessageData(v___x_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___redArg(lean_object* v_inst_998_, lean_object* v_inst_999_, lean_object* v_attrName_1000_, lean_object* v_declName_1001_){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; uint8_t v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1002_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1003_ = l_Lean_MessageData_ofName(v_attrName_1000_);
v___x_1004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1002_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1006_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1004_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
v___x_1007_ = 0;
v___x_1008_ = l_Lean_MessageData_ofConstName(v_declName_1001_, v___x_1007_);
v___x_1009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1006_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1009_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = l_Lean_throwError___redArg(v_inst_998_, v_inst_999_, v___x_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule(lean_object* v_m_1013_, lean_object* v_inst_1014_, lean_object* v_inst_1015_, lean_object* v_00_u03b1_1016_, lean_object* v_attrName_1017_, lean_object* v_declName_1018_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_1014_, v_inst_1015_, v_attrName_1017_, v_declName_1018_);
return v___x_1019_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1(void){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___redArg___closed__0));
v___x_1022_ = l_Lean_stringToMessageData(v___x_1021_);
return v___x_1022_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___redArg___closed__2));
v___x_1025_ = l_Lean_stringToMessageData(v___x_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___redArg(lean_object* v_inst_1026_, lean_object* v_inst_1027_, lean_object* v_attrName_1028_, lean_object* v_declName_1029_, lean_object* v_asyncPrefix_x3f_1030_){
_start:
{
lean_object* v___y_1032_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1030_) == 0)
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Lean_MessageData_nil;
v___y_1032_ = v___x_1045_;
goto v___jp_1031_;
}
else
{
lean_object* v_val_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v_val_1046_ = lean_ctor_get(v_asyncPrefix_x3f_1030_, 0);
lean_inc(v_val_1046_);
lean_dec_ref_known(v_asyncPrefix_x3f_1030_, 1);
v___x_1047_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1048_ = l_Lean_MessageData_ofName(v_val_1046_);
v___x_1049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1047_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
v___x_1050_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1049_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
v___y_1032_ = v___x_1051_;
goto v___jp_1031_;
}
v___jp_1031_:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; uint8_t v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1033_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1034_ = l_Lean_MessageData_ofName(v_attrName_1028_);
v___x_1035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1033_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
v___x_1036_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1035_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
v___x_1038_ = 0;
v___x_1039_ = l_Lean_MessageData_ofConstName(v_declName_1029_, v___x_1038_);
v___x_1040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1037_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1040_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
v___x_1043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
lean_ctor_set(v___x_1043_, 1, v___y_1032_);
v___x_1044_ = l_Lean_throwError___redArg(v_inst_1026_, v_inst_1027_, v___x_1043_);
return v___x_1044_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx(lean_object* v_m_1052_, lean_object* v_inst_1053_, lean_object* v_inst_1054_, lean_object* v_00_u03b1_1055_, lean_object* v_attrName_1056_, lean_object* v_declName_1057_, lean_object* v_asyncPrefix_x3f_1058_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_1053_, v_inst_1054_, v_attrName_1056_, v_declName_1057_, v_asyncPrefix_x3f_1058_);
return v___x_1059_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1(void){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__0));
v___x_1062_ = l_Lean_stringToMessageData(v___x_1061_);
return v___x_1062_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3(void){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__2));
v___x_1065_ = l_Lean_stringToMessageData(v___x_1064_);
return v___x_1065_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5(void){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__4));
v___x_1068_ = l_Lean_stringToMessageData(v___x_1067_);
return v___x_1068_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7(void){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1070_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__6));
v___x_1071_ = l_Lean_stringToMessageData(v___x_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg(lean_object* v_inst_1072_, lean_object* v_inst_1073_, lean_object* v_attrName_1074_, lean_object* v_declName_1075_, lean_object* v_givenType_1076_, lean_object* v_expectedType_1077_){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; uint8_t v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1078_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1079_ = l_Lean_MessageData_ofName(v_attrName_1074_);
lean_inc_ref(v___x_1079_);
v___x_1080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1078_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1080_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
v___x_1083_ = 0;
v___x_1084_ = l_Lean_MessageData_ofConstName(v_declName_1075_, v___x_1083_);
v___x_1085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1082_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3);
v___x_1087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1085_);
lean_ctor_set(v___x_1087_, 1, v___x_1086_);
v___x_1088_ = l_Lean_indentExpr(v_givenType_1076_);
v___x_1089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1087_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
v___x_1090_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5);
v___x_1091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1089_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
v___x_1092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1091_);
lean_ctor_set(v___x_1092_, 1, v___x_1079_);
v___x_1093_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7);
v___x_1094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1092_);
lean_ctor_set(v___x_1094_, 1, v___x_1093_);
v___x_1095_ = l_Lean_indentExpr(v_expectedType_1077_);
v___x_1096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1094_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
v___x_1097_ = l_Lean_throwError___redArg(v_inst_1072_, v_inst_1073_, v___x_1096_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType(lean_object* v_m_1098_, lean_object* v_inst_1099_, lean_object* v_inst_1100_, lean_object* v_00_u03b1_1101_, lean_object* v_attrName_1102_, lean_object* v_declName_1103_, lean_object* v_givenType_1104_, lean_object* v_expectedType_1105_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = l_Lean_throwAttrDeclNotOfExpectedType___redArg(v_inst_1099_, v_inst_1100_, v_attrName_1102_, v_declName_1103_, v_givenType_1104_, v_expectedType_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(lean_object* v_constName_1107_, uint8_t v_skipRealize_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v___x_1111_; lean_object* v_env_1112_; uint8_t v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1111_ = lean_st_ref_get(v___y_1109_);
v_env_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc_ref(v_env_1112_);
lean_dec(v___x_1111_);
v___x_1113_ = l_Lean_Environment_contains(v_env_1112_, v_constName_1107_, v_skipRealize_1108_);
v___x_1114_ = lean_box(v___x_1113_);
v___x_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg___boxed(lean_object* v_constName_1116_, lean_object* v_skipRealize_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
uint8_t v_skipRealize_boxed_1120_; lean_object* v_res_1121_; 
v_skipRealize_boxed_1120_ = lean_unbox(v_skipRealize_1117_);
v_res_1121_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_constName_1116_, v_skipRealize_boxed_1120_, v___y_1118_);
lean_dec(v___y_1118_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(lean_object* v_constName_1122_, uint8_t v_skipRealize_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_constName_1122_, v_skipRealize_1123_, v___y_1125_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___boxed(lean_object* v_constName_1128_, lean_object* v_skipRealize_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
uint8_t v_skipRealize_boxed_1133_; lean_object* v_res_1134_; 
v_skipRealize_boxed_1133_ = lean_unbox(v_skipRealize_1129_);
v_res_1134_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(v_constName_1128_, v_skipRealize_boxed_1133_, v___y_1130_, v___y_1131_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(lean_object* v___y_1135_, uint8_t v_isExporting_1136_, lean_object* v___x_1137_, lean_object* v_a_x3f_1138_){
_start:
{
lean_object* v___x_1140_; lean_object* v_env_1141_; lean_object* v_nextMacroScope_1142_; lean_object* v_ngen_1143_; lean_object* v_auxDeclNGen_1144_; lean_object* v_traceState_1145_; lean_object* v_recordedDeps_1146_; lean_object* v_messages_1147_; lean_object* v_infoState_1148_; lean_object* v_snapshotTasks_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1160_; 
v___x_1140_ = lean_st_ref_take(v___y_1135_);
v_env_1141_ = lean_ctor_get(v___x_1140_, 0);
v_nextMacroScope_1142_ = lean_ctor_get(v___x_1140_, 1);
v_ngen_1143_ = lean_ctor_get(v___x_1140_, 2);
v_auxDeclNGen_1144_ = lean_ctor_get(v___x_1140_, 3);
v_traceState_1145_ = lean_ctor_get(v___x_1140_, 4);
v_recordedDeps_1146_ = lean_ctor_get(v___x_1140_, 6);
v_messages_1147_ = lean_ctor_get(v___x_1140_, 7);
v_infoState_1148_ = lean_ctor_get(v___x_1140_, 8);
v_snapshotTasks_1149_ = lean_ctor_get(v___x_1140_, 9);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1160_ == 0)
{
lean_object* v_unused_1161_; 
v_unused_1161_ = lean_ctor_get(v___x_1140_, 5);
lean_dec(v_unused_1161_);
v___x_1151_ = v___x_1140_;
v_isShared_1152_ = v_isSharedCheck_1160_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_snapshotTasks_1149_);
lean_inc(v_infoState_1148_);
lean_inc(v_messages_1147_);
lean_inc(v_recordedDeps_1146_);
lean_inc(v_traceState_1145_);
lean_inc(v_auxDeclNGen_1144_);
lean_inc(v_ngen_1143_);
lean_inc(v_nextMacroScope_1142_);
lean_inc(v_env_1141_);
lean_dec(v___x_1140_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1160_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1156_; 
v___x_1153_ = lean_box(0);
v___x_1154_ = l_Lean_Environment_setExporting(v_env_1141_, v_isExporting_1136_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 5, v___x_1137_);
lean_ctor_set(v___x_1151_, 0, v___x_1154_);
v___x_1156_ = v___x_1151_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1154_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v_nextMacroScope_1142_);
lean_ctor_set(v_reuseFailAlloc_1159_, 2, v_ngen_1143_);
lean_ctor_set(v_reuseFailAlloc_1159_, 3, v_auxDeclNGen_1144_);
lean_ctor_set(v_reuseFailAlloc_1159_, 4, v_traceState_1145_);
lean_ctor_set(v_reuseFailAlloc_1159_, 5, v___x_1137_);
lean_ctor_set(v_reuseFailAlloc_1159_, 6, v_recordedDeps_1146_);
lean_ctor_set(v_reuseFailAlloc_1159_, 7, v_messages_1147_);
lean_ctor_set(v_reuseFailAlloc_1159_, 8, v_infoState_1148_);
lean_ctor_set(v_reuseFailAlloc_1159_, 9, v_snapshotTasks_1149_);
v___x_1156_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1157_ = lean_st_ref_put(v___y_1135_, v___x_1156_);
v___x_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1153_);
return v___x_1158_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0___boxed(lean_object* v___y_1162_, lean_object* v_isExporting_1163_, lean_object* v___x_1164_, lean_object* v_a_x3f_1165_, lean_object* v___y_1166_){
_start:
{
uint8_t v_isExporting_boxed_1167_; lean_object* v_res_1168_; 
v_isExporting_boxed_1167_ = lean_unbox(v_isExporting_1163_);
v_res_1168_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1162_, v_isExporting_boxed_1167_, v___x_1164_, v_a_x3f_1165_);
lean_dec(v_a_x3f_1165_);
lean_dec(v___y_1162_);
return v_res_1168_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1169_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0);
v___x_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1169_);
return v___x_1170_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1171_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0);
v___x_1172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1171_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(lean_object* v_x_1173_, uint8_t v_isExporting_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v___x_1178_; lean_object* v_env_1179_; lean_object* v___x_1180_; uint8_t v_isModule_1181_; 
v___x_1178_ = lean_st_ref_get(v___y_1176_);
v_env_1179_ = lean_ctor_get(v___x_1178_, 0);
lean_inc_ref(v_env_1179_);
lean_dec(v___x_1178_);
v___x_1180_ = l_Lean_Environment_header(v_env_1179_);
v_isModule_1181_ = lean_ctor_get_uint8(v___x_1180_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1180_);
if (v_isModule_1181_ == 0)
{
lean_object* v___x_1182_; 
lean_dec_ref(v_env_1179_);
lean_inc(v___y_1176_);
lean_inc_ref(v___y_1175_);
v___x_1182_ = lean_apply_3(v_x_1173_, v___y_1175_, v___y_1176_, lean_box(0));
return v___x_1182_;
}
else
{
uint8_t v_isExporting_1183_; 
v_isExporting_1183_ = lean_ctor_get_uint8(v_env_1179_, sizeof(void*)*8);
lean_dec_ref(v_env_1179_);
if (v_isExporting_1174_ == 0)
{
if (v_isExporting_1183_ == 0)
{
lean_object* v___x_1235_; 
lean_inc(v___y_1176_);
lean_inc_ref(v___y_1175_);
v___x_1235_ = lean_apply_3(v_x_1173_, v___y_1175_, v___y_1176_, lean_box(0));
return v___x_1235_;
}
else
{
goto v___jp_1184_;
}
}
else
{
if (v_isExporting_1183_ == 0)
{
goto v___jp_1184_;
}
else
{
lean_object* v___x_1236_; 
lean_inc(v___y_1176_);
lean_inc_ref(v___y_1175_);
v___x_1236_ = lean_apply_3(v_x_1173_, v___y_1175_, v___y_1176_, lean_box(0));
return v___x_1236_;
}
}
v___jp_1184_:
{
lean_object* v___x_1185_; lean_object* v_env_1186_; lean_object* v_nextMacroScope_1187_; lean_object* v_ngen_1188_; lean_object* v_auxDeclNGen_1189_; lean_object* v_traceState_1190_; lean_object* v_recordedDeps_1191_; lean_object* v_messages_1192_; lean_object* v_infoState_1193_; lean_object* v_snapshotTasks_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1233_; 
v___x_1185_ = lean_st_ref_take(v___y_1176_);
v_env_1186_ = lean_ctor_get(v___x_1185_, 0);
v_nextMacroScope_1187_ = lean_ctor_get(v___x_1185_, 1);
v_ngen_1188_ = lean_ctor_get(v___x_1185_, 2);
v_auxDeclNGen_1189_ = lean_ctor_get(v___x_1185_, 3);
v_traceState_1190_ = lean_ctor_get(v___x_1185_, 4);
v_recordedDeps_1191_ = lean_ctor_get(v___x_1185_, 6);
v_messages_1192_ = lean_ctor_get(v___x_1185_, 7);
v_infoState_1193_ = lean_ctor_get(v___x_1185_, 8);
v_snapshotTasks_1194_ = lean_ctor_get(v___x_1185_, 9);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1233_ == 0)
{
lean_object* v_unused_1234_; 
v_unused_1234_ = lean_ctor_get(v___x_1185_, 5);
lean_dec(v_unused_1234_);
v___x_1196_ = v___x_1185_;
v_isShared_1197_ = v_isSharedCheck_1233_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_snapshotTasks_1194_);
lean_inc(v_infoState_1193_);
lean_inc(v_messages_1192_);
lean_inc(v_recordedDeps_1191_);
lean_inc(v_traceState_1190_);
lean_inc(v_auxDeclNGen_1189_);
lean_inc(v_ngen_1188_);
lean_inc(v_nextMacroScope_1187_);
lean_inc(v_env_1186_);
lean_dec(v___x_1185_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1233_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1201_; 
v___x_1198_ = l_Lean_Environment_setExporting(v_env_1186_, v_isExporting_1174_);
v___x_1199_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 5, v___x_1199_);
lean_ctor_set(v___x_1196_, 0, v___x_1198_);
v___x_1201_ = v___x_1196_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1198_);
lean_ctor_set(v_reuseFailAlloc_1232_, 1, v_nextMacroScope_1187_);
lean_ctor_set(v_reuseFailAlloc_1232_, 2, v_ngen_1188_);
lean_ctor_set(v_reuseFailAlloc_1232_, 3, v_auxDeclNGen_1189_);
lean_ctor_set(v_reuseFailAlloc_1232_, 4, v_traceState_1190_);
lean_ctor_set(v_reuseFailAlloc_1232_, 5, v___x_1199_);
lean_ctor_set(v_reuseFailAlloc_1232_, 6, v_recordedDeps_1191_);
lean_ctor_set(v_reuseFailAlloc_1232_, 7, v_messages_1192_);
lean_ctor_set(v_reuseFailAlloc_1232_, 8, v_infoState_1193_);
lean_ctor_set(v_reuseFailAlloc_1232_, 9, v_snapshotTasks_1194_);
v___x_1201_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
lean_object* v___x_1202_; lean_object* v_r_1203_; 
v___x_1202_ = lean_st_ref_put(v___y_1176_, v___x_1201_);
lean_inc(v___y_1176_);
lean_inc_ref(v___y_1175_);
v_r_1203_ = lean_apply_3(v_x_1173_, v___y_1175_, v___y_1176_, lean_box(0));
if (lean_obj_tag(v_r_1203_) == 0)
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1220_; 
v_a_1204_ = lean_ctor_get(v_r_1203_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v_r_1203_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1206_ = v_r_1203_;
v_isShared_1207_ = v_isSharedCheck_1220_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v_r_1203_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1220_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1209_; 
lean_inc(v_a_1204_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set_tag(v___x_1206_, 1);
v___x_1209_ = v___x_1206_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_a_1204_);
v___x_1209_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
lean_object* v___x_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
v___x_1210_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1176_, v_isExporting_1183_, v___x_1199_, v___x_1209_);
lean_dec_ref(v___x_1209_);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1217_ == 0)
{
lean_object* v_unused_1218_; 
v_unused_1218_ = lean_ctor_get(v___x_1210_, 0);
lean_dec(v_unused_1218_);
v___x_1212_ = v___x_1210_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_dec(v___x_1210_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 0, v_a_1204_);
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1204_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
}
else
{
lean_object* v_a_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
v_a_1221_ = lean_ctor_get(v_r_1203_, 0);
lean_inc(v_a_1221_);
lean_dec_ref_known(v_r_1203_, 1);
v___x_1222_ = lean_box(0);
v___x_1223_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1176_, v_isExporting_1183_, v___x_1199_, v___x_1222_);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1230_ == 0)
{
lean_object* v_unused_1231_; 
v_unused_1231_ = lean_ctor_get(v___x_1223_, 0);
lean_dec(v_unused_1231_);
v___x_1225_ = v___x_1223_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_dec(v___x_1223_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
lean_ctor_set_tag(v___x_1225_, 1);
lean_ctor_set(v___x_1225_, 0, v_a_1221_);
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1221_);
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
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___boxed(lean_object* v_x_1237_, lean_object* v_isExporting_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
uint8_t v_isExporting_boxed_1242_; lean_object* v_res_1243_; 
v_isExporting_boxed_1242_ = lean_unbox(v_isExporting_1238_);
v_res_1243_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1237_, v_isExporting_boxed_1242_, v___y_1239_, v___y_1240_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(lean_object* v_00_u03b1_1244_, lean_object* v_x_1245_, uint8_t v_isExporting_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
lean_object* v___x_1250_; 
v___x_1250_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1245_, v_isExporting_1246_, v___y_1247_, v___y_1248_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___boxed(lean_object* v_00_u03b1_1251_, lean_object* v_x_1252_, lean_object* v_isExporting_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
uint8_t v_isExporting_boxed_1257_; lean_object* v_res_1258_; 
v_isExporting_boxed_1257_ = lean_unbox(v_isExporting_1253_);
v_res_1258_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(v_00_u03b1_1251_, v_x_1252_, v_isExporting_boxed_1257_, v___y_1254_, v___y_1255_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
return v_res_1258_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(lean_object* v_opts_1259_, lean_object* v_opt_1260_){
_start:
{
lean_object* v_name_1261_; lean_object* v_defValue_1262_; lean_object* v_map_1263_; lean_object* v___x_1264_; 
v_name_1261_ = lean_ctor_get(v_opt_1260_, 0);
v_defValue_1262_ = lean_ctor_get(v_opt_1260_, 1);
v_map_1263_ = lean_ctor_get(v_opts_1259_, 0);
v___x_1264_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1263_, v_name_1261_);
if (lean_obj_tag(v___x_1264_) == 0)
{
uint8_t v___x_1265_; 
v___x_1265_ = lean_unbox(v_defValue_1262_);
return v___x_1265_;
}
else
{
lean_object* v_val_1266_; 
v_val_1266_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_val_1266_);
lean_dec_ref_known(v___x_1264_, 1);
if (lean_obj_tag(v_val_1266_) == 1)
{
uint8_t v_v_1267_; 
v_v_1267_ = lean_ctor_get_uint8(v_val_1266_, 0);
lean_dec_ref_known(v_val_1266_, 0);
return v_v_1267_;
}
else
{
uint8_t v___x_1268_; 
lean_dec(v_val_1266_);
v___x_1268_ = lean_unbox(v_defValue_1262_);
return v___x_1268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3___boxed(lean_object* v_opts_1269_, lean_object* v_opt_1270_){
_start:
{
uint8_t v_res_1271_; lean_object* v_r_1272_; 
v_res_1271_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_opts_1269_, v_opt_1270_);
lean_dec_ref(v_opt_1270_);
lean_dec_ref(v_opts_1269_);
v_r_1272_ = lean_box(v_res_1271_);
return v_r_1272_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(uint8_t v_suppressElabErrors_1280_, uint8_t v___y_1281_, lean_object* v_x_1282_){
_start:
{
if (lean_obj_tag(v_x_1282_) == 1)
{
lean_object* v_pre_1283_; 
v_pre_1283_ = lean_ctor_get(v_x_1282_, 0);
switch(lean_obj_tag(v_pre_1283_))
{
case 1:
{
lean_object* v_pre_1284_; 
v_pre_1284_ = lean_ctor_get(v_pre_1283_, 0);
switch(lean_obj_tag(v_pre_1284_))
{
case 0:
{
lean_object* v_str_1285_; lean_object* v_str_1286_; lean_object* v___x_1287_; uint8_t v___x_1288_; 
v_str_1285_ = lean_ctor_get(v_x_1282_, 1);
v_str_1286_ = lean_ctor_get(v_pre_1283_, 1);
v___x_1287_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__0));
v___x_1288_ = lean_string_dec_eq(v_str_1286_, v___x_1287_);
if (v___x_1288_ == 0)
{
lean_object* v___x_1289_; uint8_t v___x_1290_; 
v___x_1289_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__2));
v___x_1290_ = lean_string_dec_eq(v_str_1286_, v___x_1289_);
if (v___x_1290_ == 0)
{
return v___x_1290_;
}
else
{
lean_object* v___x_1291_; uint8_t v___x_1292_; 
v___x_1291_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__1));
v___x_1292_ = lean_string_dec_eq(v_str_1285_, v___x_1291_);
if (v___x_1292_ == 0)
{
return v___x_1292_;
}
else
{
return v_suppressElabErrors_1280_;
}
}
}
else
{
lean_object* v___x_1293_; uint8_t v___x_1294_; 
v___x_1293_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__2));
v___x_1294_ = lean_string_dec_eq(v_str_1285_, v___x_1293_);
if (v___x_1294_ == 0)
{
return v___x_1294_;
}
else
{
return v_suppressElabErrors_1280_;
}
}
}
case 1:
{
lean_object* v_pre_1295_; 
v_pre_1295_ = lean_ctor_get(v_pre_1284_, 0);
if (lean_obj_tag(v_pre_1295_) == 0)
{
lean_object* v_str_1296_; lean_object* v_str_1297_; lean_object* v_str_1298_; lean_object* v___x_1299_; uint8_t v___x_1300_; 
v_str_1296_ = lean_ctor_get(v_x_1282_, 1);
v_str_1297_ = lean_ctor_get(v_pre_1283_, 1);
v_str_1298_ = lean_ctor_get(v_pre_1284_, 1);
v___x_1299_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__3));
v___x_1300_ = lean_string_dec_eq(v_str_1298_, v___x_1299_);
if (v___x_1300_ == 0)
{
return v___x_1300_;
}
else
{
lean_object* v___x_1301_; uint8_t v___x_1302_; 
v___x_1301_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__4));
v___x_1302_ = lean_string_dec_eq(v_str_1297_, v___x_1301_);
if (v___x_1302_ == 0)
{
return v___x_1302_;
}
else
{
lean_object* v___x_1303_; uint8_t v___x_1304_; 
v___x_1303_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__5));
v___x_1304_ = lean_string_dec_eq(v_str_1296_, v___x_1303_);
if (v___x_1304_ == 0)
{
return v___x_1304_;
}
else
{
return v_suppressElabErrors_1280_;
}
}
}
}
else
{
return v___y_1281_;
}
}
default: 
{
return v___y_1281_;
}
}
}
case 0:
{
lean_object* v_str_1305_; lean_object* v___x_1306_; uint8_t v___x_1307_; 
v_str_1305_ = lean_ctor_get(v_x_1282_, 1);
v___x_1306_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__6));
v___x_1307_ = lean_string_dec_eq(v_str_1305_, v___x_1306_);
if (v___x_1307_ == 0)
{
return v___x_1307_;
}
else
{
return v_suppressElabErrors_1280_;
}
}
default: 
{
return v___y_1281_;
}
}
}
else
{
return v___y_1281_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed(lean_object* v_suppressElabErrors_1308_, lean_object* v___y_1309_, lean_object* v_x_1310_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1311_; uint8_t v___y_5082__boxed_1312_; uint8_t v_res_1313_; lean_object* v_r_1314_; 
v_suppressElabErrors_boxed_1311_ = lean_unbox(v_suppressElabErrors_1308_);
v___y_5082__boxed_1312_ = lean_unbox(v___y_1309_);
v_res_1313_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(v_suppressElabErrors_boxed_1311_, v___y_5082__boxed_1312_, v_x_1310_);
lean_dec(v_x_1310_);
v_r_1314_ = lean_box(v_res_1313_);
return v_r_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(lean_object* v_ref_1315_, lean_object* v_msgData_1316_, uint8_t v_severity_1317_, uint8_t v_isSilent_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v___y_1323_; lean_object* v___y_1324_; uint8_t v___y_1325_; lean_object* v___y_1326_; uint8_t v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v_toCold_1330_; lean_object* v___y_1331_; lean_object* v___y_1360_; lean_object* v___y_1361_; uint8_t v___y_1362_; lean_object* v___y_1363_; lean_object* v___y_1364_; uint8_t v___y_1365_; uint8_t v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1387_; uint8_t v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; uint8_t v___y_1391_; uint8_t v___y_1392_; lean_object* v___y_1393_; uint8_t v___y_1397_; uint8_t v___y_1398_; uint8_t v___y_1399_; uint8_t v___x_1410_; uint8_t v___y_1412_; uint8_t v___y_1413_; uint8_t v___y_1414_; uint8_t v___y_1416_; uint8_t v___x_1424_; 
v___x_1410_ = 2;
v___x_1424_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1317_, v___x_1410_);
if (v___x_1424_ == 0)
{
v___y_1416_ = v___x_1424_;
goto v___jp_1415_;
}
else
{
uint8_t v___x_1425_; 
lean_inc_ref(v_msgData_1316_);
v___x_1425_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1316_);
v___y_1416_ = v___x_1425_;
goto v___jp_1415_;
}
v___jp_1322_:
{
lean_object* v_currNamespace_1332_; lean_object* v_openDecls_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v_env_1338_; lean_object* v_nextMacroScope_1339_; lean_object* v_ngen_1340_; lean_object* v_auxDeclNGen_1341_; lean_object* v_traceState_1342_; lean_object* v_cache_1343_; lean_object* v_recordedDeps_1344_; lean_object* v_messages_1345_; lean_object* v_infoState_1346_; lean_object* v_snapshotTasks_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1358_; 
v_currNamespace_1332_ = lean_ctor_get(v_toCold_1330_, 4);
v_openDecls_1333_ = lean_ctor_get(v_toCold_1330_, 5);
lean_inc(v_openDecls_1333_);
lean_inc(v_currNamespace_1332_);
v___x_1334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1334_, 0, v_currNamespace_1332_);
lean_ctor_set(v___x_1334_, 1, v_openDecls_1333_);
v___x_1335_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
lean_ctor_set(v___x_1335_, 1, v___y_1324_);
lean_inc_ref(v___y_1326_);
lean_inc_ref(v___y_1329_);
v___x_1336_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1336_, 0, v___y_1329_);
lean_ctor_set(v___x_1336_, 1, v___y_1323_);
lean_ctor_set(v___x_1336_, 2, v___y_1328_);
lean_ctor_set(v___x_1336_, 3, v___y_1326_);
lean_ctor_set(v___x_1336_, 4, v___x_1335_);
lean_ctor_set_uint8(v___x_1336_, sizeof(void*)*5, v___y_1327_);
lean_ctor_set_uint8(v___x_1336_, sizeof(void*)*5 + 1, v___y_1325_);
lean_ctor_set_uint8(v___x_1336_, sizeof(void*)*5 + 2, v_isSilent_1318_);
v___x_1337_ = lean_st_ref_take(v___y_1331_);
v_env_1338_ = lean_ctor_get(v___x_1337_, 0);
v_nextMacroScope_1339_ = lean_ctor_get(v___x_1337_, 1);
v_ngen_1340_ = lean_ctor_get(v___x_1337_, 2);
v_auxDeclNGen_1341_ = lean_ctor_get(v___x_1337_, 3);
v_traceState_1342_ = lean_ctor_get(v___x_1337_, 4);
v_cache_1343_ = lean_ctor_get(v___x_1337_, 5);
v_recordedDeps_1344_ = lean_ctor_get(v___x_1337_, 6);
v_messages_1345_ = lean_ctor_get(v___x_1337_, 7);
v_infoState_1346_ = lean_ctor_get(v___x_1337_, 8);
v_snapshotTasks_1347_ = lean_ctor_get(v___x_1337_, 9);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1349_ = v___x_1337_;
v_isShared_1350_ = v_isSharedCheck_1358_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_snapshotTasks_1347_);
lean_inc(v_infoState_1346_);
lean_inc(v_messages_1345_);
lean_inc(v_recordedDeps_1344_);
lean_inc(v_cache_1343_);
lean_inc(v_traceState_1342_);
lean_inc(v_auxDeclNGen_1341_);
lean_inc(v_ngen_1340_);
lean_inc(v_nextMacroScope_1339_);
lean_inc(v_env_1338_);
lean_dec(v___x_1337_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1358_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1354_; 
v___x_1351_ = lean_box(0);
v___x_1352_ = l_Lean_MessageLog_add(v___x_1336_, v_messages_1345_);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 7, v___x_1352_);
v___x_1354_ = v___x_1349_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_env_1338_);
lean_ctor_set(v_reuseFailAlloc_1357_, 1, v_nextMacroScope_1339_);
lean_ctor_set(v_reuseFailAlloc_1357_, 2, v_ngen_1340_);
lean_ctor_set(v_reuseFailAlloc_1357_, 3, v_auxDeclNGen_1341_);
lean_ctor_set(v_reuseFailAlloc_1357_, 4, v_traceState_1342_);
lean_ctor_set(v_reuseFailAlloc_1357_, 5, v_cache_1343_);
lean_ctor_set(v_reuseFailAlloc_1357_, 6, v_recordedDeps_1344_);
lean_ctor_set(v_reuseFailAlloc_1357_, 7, v___x_1352_);
lean_ctor_set(v_reuseFailAlloc_1357_, 8, v_infoState_1346_);
lean_ctor_set(v_reuseFailAlloc_1357_, 9, v_snapshotTasks_1347_);
v___x_1354_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1355_ = lean_st_ref_put(v___y_1331_, v___x_1354_);
v___x_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1351_);
return v___x_1356_;
}
}
}
v___jp_1359_:
{
lean_object* v_fileName_1368_; lean_object* v_fileMap_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1385_; 
v_fileName_1368_ = lean_ctor_get(v___y_1363_, 0);
v_fileMap_1369_ = lean_ctor_get(v___y_1363_, 1);
v___x_1370_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1316_);
v___x_1371_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v___x_1370_, v___y_1319_, v___y_1320_);
v_a_1372_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1374_ = v___x_1371_;
v_isShared_1375_ = v_isSharedCheck_1385_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1371_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1385_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
lean_inc_ref_n(v_fileMap_1369_, 2);
v___x_1376_ = l_Lean_FileMap_toPosition(v_fileMap_1369_, v___y_1364_);
lean_dec(v___y_1364_);
v___x_1377_ = l_Lean_FileMap_toPosition(v_fileMap_1369_, v___y_1367_);
lean_dec(v___y_1367_);
v___x_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1377_);
v___x_1379_ = ((lean_object*)(l_Lean_instInhabitedAttributeImplCore_default___closed__3));
if (v___y_1362_ == 0)
{
lean_del_object(v___x_1374_);
lean_dec_ref(v___y_1360_);
v___y_1323_ = v___x_1376_;
v___y_1324_ = v_a_1372_;
v___y_1325_ = v___y_1365_;
v___y_1326_ = v___x_1379_;
v___y_1327_ = v___y_1366_;
v___y_1328_ = v___x_1378_;
v___y_1329_ = v_fileName_1368_;
v_toCold_1330_ = v___y_1361_;
v___y_1331_ = v___y_1320_;
goto v___jp_1322_;
}
else
{
uint8_t v___x_1380_; 
lean_inc(v_a_1372_);
v___x_1380_ = l_Lean_MessageData_hasTag(v___y_1360_, v_a_1372_);
if (v___x_1380_ == 0)
{
lean_object* v___x_1381_; lean_object* v___x_1383_; 
lean_dec_ref_known(v___x_1378_, 1);
lean_dec_ref(v___x_1376_);
lean_dec(v_a_1372_);
v___x_1381_ = lean_box(0);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 0, v___x_1381_);
v___x_1383_ = v___x_1374_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1381_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
else
{
lean_del_object(v___x_1374_);
v___y_1323_ = v___x_1376_;
v___y_1324_ = v_a_1372_;
v___y_1325_ = v___y_1365_;
v___y_1326_ = v___x_1379_;
v___y_1327_ = v___y_1366_;
v___y_1328_ = v___x_1378_;
v___y_1329_ = v_fileName_1368_;
v_toCold_1330_ = v___y_1361_;
v___y_1331_ = v___y_1320_;
goto v___jp_1322_;
}
}
}
}
v___jp_1386_:
{
lean_object* v___x_1394_; 
v___x_1394_ = l_Lean_Syntax_getTailPos_x3f(v___y_1390_, v___y_1392_);
lean_dec(v___y_1390_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_inc(v___y_1393_);
v___y_1360_ = v___y_1387_;
v___y_1361_ = v___y_1389_;
v___y_1362_ = v___y_1388_;
v___y_1363_ = v___y_1389_;
v___y_1364_ = v___y_1393_;
v___y_1365_ = v___y_1391_;
v___y_1366_ = v___y_1392_;
v___y_1367_ = v___y_1393_;
goto v___jp_1359_;
}
else
{
lean_object* v_val_1395_; 
v_val_1395_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_val_1395_);
lean_dec_ref_known(v___x_1394_, 1);
v___y_1360_ = v___y_1387_;
v___y_1361_ = v___y_1389_;
v___y_1362_ = v___y_1388_;
v___y_1363_ = v___y_1389_;
v___y_1364_ = v___y_1393_;
v___y_1365_ = v___y_1391_;
v___y_1366_ = v___y_1392_;
v___y_1367_ = v_val_1395_;
goto v___jp_1359_;
}
}
v___jp_1396_:
{
lean_object* v_toCold_1400_; lean_object* v_ref_1401_; uint8_t v_suppressElabErrors_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___f_1405_; lean_object* v_ref_1406_; lean_object* v___x_1407_; 
v_toCold_1400_ = lean_ctor_get(v___y_1319_, 0);
v_ref_1401_ = lean_ctor_get(v___y_1319_, 2);
v_suppressElabErrors_1402_ = lean_ctor_get_uint8(v___y_1319_, sizeof(void*)*3 + 2);
v___x_1403_ = lean_box(v_suppressElabErrors_1402_);
v___x_1404_ = lean_box(v___y_1397_);
v___f_1405_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1405_, 0, v___x_1403_);
lean_closure_set(v___f_1405_, 1, v___x_1404_);
v_ref_1406_ = l_Lean_replaceRef(v_ref_1315_, v_ref_1401_);
v___x_1407_ = l_Lean_Syntax_getPos_x3f(v_ref_1406_, v___y_1398_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v___x_1408_; 
v___x_1408_ = lean_unsigned_to_nat(0u);
v___y_1387_ = v___f_1405_;
v___y_1388_ = v_suppressElabErrors_1402_;
v___y_1389_ = v_toCold_1400_;
v___y_1390_ = v_ref_1406_;
v___y_1391_ = v___y_1399_;
v___y_1392_ = v___y_1398_;
v___y_1393_ = v___x_1408_;
goto v___jp_1386_;
}
else
{
lean_object* v_val_1409_; 
v_val_1409_ = lean_ctor_get(v___x_1407_, 0);
lean_inc(v_val_1409_);
lean_dec_ref_known(v___x_1407_, 1);
v___y_1387_ = v___f_1405_;
v___y_1388_ = v_suppressElabErrors_1402_;
v___y_1389_ = v_toCold_1400_;
v___y_1390_ = v_ref_1406_;
v___y_1391_ = v___y_1399_;
v___y_1392_ = v___y_1398_;
v___y_1393_ = v_val_1409_;
goto v___jp_1386_;
}
}
v___jp_1411_:
{
if (v___y_1414_ == 0)
{
v___y_1397_ = v___y_1412_;
v___y_1398_ = v___y_1413_;
v___y_1399_ = v_severity_1317_;
goto v___jp_1396_;
}
else
{
v___y_1397_ = v___y_1412_;
v___y_1398_ = v___y_1413_;
v___y_1399_ = v___x_1410_;
goto v___jp_1396_;
}
}
v___jp_1415_:
{
if (v___y_1416_ == 0)
{
uint8_t v___x_1417_; uint8_t v___x_1418_; 
v___x_1417_ = 1;
v___x_1418_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1317_, v___x_1417_);
if (v___x_1418_ == 0)
{
v___y_1412_ = v___y_1416_;
v___y_1413_ = v___y_1416_;
v___y_1414_ = v___x_1418_;
goto v___jp_1411_;
}
else
{
lean_object* v___x_1419_; lean_object* v___x_1420_; uint8_t v___x_1421_; 
v___x_1419_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1319_);
v___x_1420_ = l_Lean_warningAsError;
v___x_1421_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v___x_1419_, v___x_1420_);
lean_dec_ref(v___x_1419_);
v___y_1412_ = v___y_1416_;
v___y_1413_ = v___y_1416_;
v___y_1414_ = v___x_1421_;
goto v___jp_1411_;
}
}
else
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
lean_dec_ref(v_msgData_1316_);
v___x_1422_ = lean_box(0);
v___x_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1422_);
return v___x_1423_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___boxed(lean_object* v_ref_1426_, lean_object* v_msgData_1427_, lean_object* v_severity_1428_, lean_object* v_isSilent_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
uint8_t v_severity_boxed_1433_; uint8_t v_isSilent_boxed_1434_; lean_object* v_res_1435_; 
v_severity_boxed_1433_ = lean_unbox(v_severity_1428_);
v_isSilent_boxed_1434_ = lean_unbox(v_isSilent_1429_);
v_res_1435_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1426_, v_msgData_1427_, v_severity_boxed_1433_, v_isSilent_boxed_1434_, v___y_1430_, v___y_1431_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec(v_ref_1426_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(lean_object* v_msgData_1436_, uint8_t v_severity_1437_, uint8_t v_isSilent_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
lean_object* v_ref_1442_; lean_object* v___x_1443_; 
v_ref_1442_ = lean_ctor_get(v___y_1439_, 2);
v___x_1443_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1442_, v_msgData_1436_, v_severity_1437_, v_isSilent_1438_, v___y_1439_, v___y_1440_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5___boxed(lean_object* v_msgData_1444_, lean_object* v_severity_1445_, lean_object* v_isSilent_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
uint8_t v_severity_boxed_1450_; uint8_t v_isSilent_boxed_1451_; lean_object* v_res_1452_; 
v_severity_boxed_1450_ = lean_unbox(v_severity_1445_);
v_isSilent_boxed_1451_ = lean_unbox(v_isSilent_1446_);
v_res_1452_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1444_, v_severity_boxed_1450_, v_isSilent_boxed_1451_, v___y_1447_, v___y_1448_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(lean_object* v_msgData_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
uint8_t v___x_1457_; uint8_t v___x_1458_; lean_object* v___x_1459_; 
v___x_1457_ = 1;
v___x_1458_ = 0;
v___x_1459_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1453_, v___x_1457_, v___x_1458_, v___y_1454_, v___y_1455_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1___boxed(lean_object* v_msgData_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v_msgData_1460_, v___y_1461_, v___y_1462_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(lean_object* v_opt_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v___x_1468_; uint8_t v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1468_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1466_);
v___x_1469_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v___x_1468_, v_opt_1465_);
lean_dec_ref(v___x_1468_);
v___x_1470_ = lean_box(v___x_1469_);
v___x_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg___boxed(lean_object* v_opt_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1472_, v___y_1473_);
lean_dec_ref(v___y_1473_);
lean_dec_ref(v_opt_1472_);
return v_res_1475_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1477_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__0));
v___x_1478_ = l_Lean_stringToMessageData(v___x_1477_);
return v___x_1478_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1480_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__2));
v___x_1481_ = l_Lean_stringToMessageData(v___x_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(lean_object* v_id_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
lean_object* v___x_1486_; lean_object* v_env_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1509_; 
v___x_1486_ = lean_st_ref_get(v___y_1484_);
v_env_1487_ = lean_ctor_get(v___x_1486_, 0);
lean_inc_ref(v_env_1487_);
lean_dec(v___x_1486_);
v___x_1488_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1489_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v___x_1488_, v___y_1483_);
v_a_1490_ = lean_ctor_get(v___x_1489_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1489_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1492_ = v___x_1489_;
v_isShared_1493_ = v_isSharedCheck_1509_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1489_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1509_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
uint8_t v_isExporting_1499_; 
v_isExporting_1499_ = lean_ctor_get_uint8(v_env_1487_, sizeof(void*)*8);
lean_dec_ref(v_env_1487_);
if (v_isExporting_1499_ == 0)
{
lean_dec(v_a_1490_);
lean_dec(v_id_1482_);
goto v___jp_1494_;
}
else
{
uint8_t v___x_1500_; 
v___x_1500_ = l_Lean_isPrivateName(v_id_1482_);
if (v___x_1500_ == 0)
{
lean_dec(v_a_1490_);
lean_dec(v_id_1482_);
goto v___jp_1494_;
}
else
{
uint8_t v___x_1501_; 
v___x_1501_ = lean_unbox(v_a_1490_);
lean_dec(v_a_1490_);
if (v___x_1501_ == 0)
{
lean_dec(v_id_1482_);
goto v___jp_1494_;
}
else
{
lean_object* v___x_1502_; uint8_t v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
lean_del_object(v___x_1492_);
v___x_1502_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1);
v___x_1503_ = 0;
v___x_1504_ = l_Lean_MessageData_ofConstName(v_id_1482_, v___x_1503_);
v___x_1505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1502_);
lean_ctor_set(v___x_1505_, 1, v___x_1504_);
v___x_1506_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3);
v___x_1507_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1505_);
lean_ctor_set(v___x_1507_, 1, v___x_1506_);
v___x_1508_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v___x_1507_, v___y_1483_, v___y_1484_);
return v___x_1508_;
}
}
}
v___jp_1494_:
{
lean_object* v___x_1495_; lean_object* v___x_1497_; 
v___x_1495_ = lean_box(0);
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 0, v___x_1495_);
v___x_1497_ = v___x_1492_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1495_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___boxed(lean_object* v_id_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_id_1510_, v___y_1511_, v___y_1512_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
return v_res_1514_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1516_ = ((lean_object*)(l_Lean_ensureAttrDeclIsPublic___lam__0___closed__0));
v___x_1517_ = l_Lean_stringToMessageData(v___x_1516_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0(lean_object* v_declName_1518_, uint8_t v_isModule_1519_, lean_object* v_attrName_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v___x_1524_; 
lean_inc(v_declName_1518_);
v___x_1524_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_declName_1518_, v___y_1521_, v___y_1522_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v___x_1525_; lean_object* v_a_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1546_; 
lean_dec_ref_known(v___x_1524_, 1);
lean_inc(v_declName_1518_);
v___x_1525_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_declName_1518_, v_isModule_1519_, v___y_1522_);
v_a_1526_ = lean_ctor_get(v___x_1525_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1528_ = v___x_1525_;
v_isShared_1529_ = v_isSharedCheck_1546_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_a_1526_);
lean_dec(v___x_1525_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1546_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
uint8_t v___x_1530_; 
v___x_1530_ = lean_unbox(v_a_1526_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; uint8_t v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
lean_del_object(v___x_1528_);
v___x_1531_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1532_ = l_Lean_MessageData_ofName(v_attrName_1520_);
v___x_1533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1531_);
lean_ctor_set(v___x_1533_, 1, v___x_1532_);
v___x_1534_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1533_);
lean_ctor_set(v___x_1535_, 1, v___x_1534_);
v___x_1536_ = lean_unbox(v_a_1526_);
lean_dec(v_a_1526_);
v___x_1537_ = l_Lean_MessageData_ofConstName(v_declName_1518_, v___x_1536_);
v___x_1538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1535_);
lean_ctor_set(v___x_1538_, 1, v___x_1537_);
v___x_1539_ = lean_obj_once(&l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1, &l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1_once, _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1);
v___x_1540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1538_);
lean_ctor_set(v___x_1540_, 1, v___x_1539_);
v___x_1541_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1540_, v___y_1521_, v___y_1522_);
return v___x_1541_;
}
else
{
lean_object* v___x_1542_; lean_object* v___x_1544_; 
lean_dec(v_a_1526_);
lean_dec(v_attrName_1520_);
lean_dec(v_declName_1518_);
v___x_1542_ = lean_box(0);
if (v_isShared_1529_ == 0)
{
lean_ctor_set(v___x_1528_, 0, v___x_1542_);
v___x_1544_ = v___x_1528_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1542_);
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
lean_dec(v_attrName_1520_);
lean_dec(v_declName_1518_);
return v___x_1524_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0___boxed(lean_object* v_declName_1547_, lean_object* v_isModule_1548_, lean_object* v_attrName_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
uint8_t v_isModule_boxed_1553_; lean_object* v_res_1554_; 
v_isModule_boxed_1553_ = lean_unbox(v_isModule_1548_);
v_res_1554_ = l_Lean_ensureAttrDeclIsPublic___lam__0(v_declName_1547_, v_isModule_boxed_1553_, v_attrName_1549_, v___y_1550_, v___y_1551_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic(lean_object* v_attrName_1555_, lean_object* v_declName_1556_, uint8_t v_attrKind_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_){
_start:
{
lean_object* v___x_1561_; lean_object* v_env_1565_; lean_object* v___x_1566_; uint8_t v_isModule_1567_; 
v___x_1561_ = lean_st_ref_get(v_a_1559_);
v_env_1565_ = lean_ctor_get(v___x_1561_, 0);
lean_inc_ref(v_env_1565_);
lean_dec(v___x_1561_);
v___x_1566_ = l_Lean_Environment_header(v_env_1565_);
lean_dec_ref(v_env_1565_);
v_isModule_1567_ = lean_ctor_get_uint8(v___x_1566_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1566_);
if (v_isModule_1567_ == 0)
{
lean_dec(v_declName_1556_);
lean_dec(v_attrName_1555_);
goto v___jp_1562_;
}
else
{
uint8_t v___x_1568_; uint8_t v___x_1569_; 
v___x_1568_ = 1;
v___x_1569_ = l_Lean_instBEqAttributeKind_beq(v_attrKind_1557_, v___x_1568_);
if (v___x_1569_ == 0)
{
lean_object* v___x_1570_; lean_object* v___f_1571_; lean_object* v___x_1572_; 
v___x_1570_ = lean_box(v_isModule_1567_);
v___f_1571_ = lean_alloc_closure((void*)(l_Lean_ensureAttrDeclIsPublic___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1571_, 0, v_declName_1556_);
lean_closure_set(v___f_1571_, 1, v___x_1570_);
lean_closure_set(v___f_1571_, 2, v_attrName_1555_);
v___x_1572_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v___f_1571_, v_isModule_1567_, v_a_1558_, v_a_1559_);
return v___x_1572_;
}
else
{
lean_dec(v_declName_1556_);
lean_dec(v_attrName_1555_);
goto v___jp_1562_;
}
}
v___jp_1562_:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1563_ = lean_box(0);
v___x_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1563_);
return v___x_1564_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___boxed(lean_object* v_attrName_1573_, lean_object* v_declName_1574_, lean_object* v_attrKind_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_){
_start:
{
uint8_t v_attrKind_boxed_1579_; lean_object* v_res_1580_; 
v_attrKind_boxed_1579_ = lean_unbox(v_attrKind_1575_);
v_res_1580_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1573_, v_declName_1574_, v_attrKind_boxed_1579_, v_a_1576_, v_a_1577_);
lean_dec(v_a_1577_);
lean_dec_ref(v_a_1576_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(lean_object* v_opt_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1581_, v___y_1582_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___boxed(lean_object* v_opt_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(v_opt_1586_, v___y_1587_, v___y_1588_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec_ref(v_opt_1586_);
return v_res_1590_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsMeta___closed__1(void){
_start:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1592_ = ((lean_object*)(l_Lean_ensureAttrDeclIsMeta___closed__0));
v___x_1593_ = l_Lean_stringToMessageData(v___x_1592_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object* v_attrName_1594_, lean_object* v_declName_1595_, uint8_t v_attrKind_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_){
_start:
{
lean_object* v___x_1600_; lean_object* v_env_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; uint8_t v_isModule_1604_; 
v___x_1600_ = lean_st_ref_get(v_a_1598_);
v_env_1601_ = lean_ctor_get(v___x_1600_, 0);
lean_inc_ref(v_env_1601_);
lean_dec(v___x_1600_);
v___x_1602_ = lean_st_ref_get(v_a_1598_);
v___x_1603_ = l_Lean_Environment_header(v_env_1601_);
lean_dec_ref(v_env_1601_);
v_isModule_1604_ = lean_ctor_get_uint8(v___x_1603_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1603_);
if (v_isModule_1604_ == 0)
{
lean_object* v___x_1605_; 
lean_dec(v___x_1602_);
v___x_1605_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1594_, v_declName_1595_, v_attrKind_1596_, v_a_1597_, v_a_1598_);
return v___x_1605_;
}
else
{
lean_object* v_env_1606_; uint8_t v___x_1607_; 
v_env_1606_ = lean_ctor_get(v___x_1602_, 0);
lean_inc_ref(v_env_1606_);
lean_dec(v___x_1602_);
lean_inc(v_declName_1595_);
v___x_1607_ = l_Lean_isMarkedMeta(v_env_1606_, v_declName_1595_);
if (v___x_1607_ == 0)
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1608_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1609_ = l_Lean_MessageData_ofName(v_attrName_1594_);
v___x_1610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1608_);
lean_ctor_set(v___x_1610_, 1, v___x_1609_);
v___x_1611_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1610_);
lean_ctor_set(v___x_1612_, 1, v___x_1611_);
v___x_1613_ = l_Lean_MessageData_ofConstName(v_declName_1595_, v___x_1607_);
v___x_1614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1612_);
lean_ctor_set(v___x_1614_, 1, v___x_1613_);
v___x_1615_ = lean_obj_once(&l_Lean_ensureAttrDeclIsMeta___closed__1, &l_Lean_ensureAttrDeclIsMeta___closed__1_once, _init_l_Lean_ensureAttrDeclIsMeta___closed__1);
v___x_1616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1614_);
lean_ctor_set(v___x_1616_, 1, v___x_1615_);
v___x_1617_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1616_, v_a_1597_, v_a_1598_);
return v___x_1617_;
}
else
{
lean_object* v___x_1618_; 
v___x_1618_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1594_, v_declName_1595_, v_attrKind_1596_, v_a_1597_, v_a_1598_);
return v___x_1618_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta___boxed(lean_object* v_attrName_1619_, lean_object* v_declName_1620_, lean_object* v_attrKind_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_){
_start:
{
uint8_t v_attrKind_boxed_1625_; lean_object* v_res_1626_; 
v_attrKind_boxed_1625_ = lean_unbox(v_attrKind_1621_);
v_res_1626_ = l_Lean_ensureAttrDeclIsMeta(v_attrName_1619_, v_declName_1620_, v_attrKind_boxed_1625_, v_a_1622_, v_a_1623_);
lean_dec(v_a_1623_);
lean_dec_ref(v_a_1622_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0(lean_object* v_x_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1633_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_1634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1633_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0___boxed(lean_object* v_x_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l_Lean_instInhabitedTagAttribute_default___lam__0(v_x_1635_, v___y_1636_);
lean_dec_ref(v___y_1636_);
lean_dec_ref(v_x_1635_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1(lean_object* v_s_1639_, lean_object* v_x_1640_){
_start:
{
lean_inc(v_s_1639_);
return v_s_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1___boxed(lean_object* v_s_1641_, lean_object* v_x_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l_Lean_instInhabitedTagAttribute_default___lam__1(v_s_1641_, v_x_1642_);
lean_dec(v_x_1642_);
lean_dec(v_s_1641_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2(lean_object* v_x_1648_, lean_object* v_x_1649_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__1));
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2___boxed(lean_object* v_x_1651_, lean_object* v_x_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l_Lean_instInhabitedTagAttribute_default___lam__2(v_x_1651_, v_x_1652_);
lean_dec(v_x_1652_);
lean_dec_ref(v_x_1651_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3(lean_object* v_x_1654_){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = lean_box(0);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3___boxed(lean_object* v_x_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_Lean_instInhabitedTagAttribute_default___lam__3(v_x_1656_);
lean_dec(v_x_1656_);
return v_res_1657_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = l_Lean_instInhabitedEnvExtension_default___redArg();
return v___x_1662_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_1663_; lean_object* v___f_1664_; lean_object* v___f_1665_; lean_object* v___f_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___f_1663_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_1664_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__2));
v___f_1665_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__1));
v___f_1666_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__0));
v___x_1667_ = lean_box(0);
v___x_1668_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_1669_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1668_);
lean_ctor_set(v___x_1669_, 1, v___x_1667_);
lean_ctor_set(v___x_1669_, 2, v___f_1666_);
lean_ctor_set(v___x_1669_, 3, v___f_1665_);
lean_ctor_set(v___x_1669_, 4, v___f_1664_);
lean_ctor_set(v___x_1669_, 5, v___f_1663_);
return v___x_1669_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__6(void){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1670_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__5, &l_Lean_instInhabitedTagAttribute_default___closed__5_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__5);
v___x_1671_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_1672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1671_);
lean_ctor_set(v___x_1672_, 1, v___x_1670_);
return v___x_1672_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default(void){
_start:
{
lean_object* v___x_1673_; 
v___x_1673_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__6, &l_Lean_instInhabitedTagAttribute_default___closed__6_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__6);
return v___x_1673_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute(void){
_start:
{
lean_object* v___x_1674_; 
v___x_1674_ = l_Lean_instInhabitedTagAttribute_default;
return v___x_1674_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___auto__1(void){
_start:
{
lean_object* v___x_1675_; 
v___x_1675_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0(lean_object* v_x_1676_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0___boxed(lean_object* v_x_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_Lean_registerTagAttribute___lam__0(v_x_1678_);
lean_dec(v_x_1678_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0(lean_object* v_newState_1680_, lean_object* v_x_1681_, lean_object* v_x_1682_){
_start:
{
if (lean_obj_tag(v_x_1682_) == 0)
{
return v_x_1681_;
}
else
{
lean_object* v_head_1683_; lean_object* v_tail_1684_; uint8_t v___x_1685_; 
v_head_1683_ = lean_ctor_get(v_x_1682_, 0);
lean_inc(v_head_1683_);
v_tail_1684_ = lean_ctor_get(v_x_1682_, 1);
lean_inc(v_tail_1684_);
lean_dec_ref_known(v_x_1682_, 2);
v___x_1685_ = l_Lean_NameSet_contains(v_newState_1680_, v_head_1683_);
if (v___x_1685_ == 0)
{
lean_dec(v_head_1683_);
v_x_1682_ = v_tail_1684_;
goto _start;
}
else
{
lean_object* v___x_1687_; 
v___x_1687_ = l_Lean_NameSet_insert(v_x_1681_, v_head_1683_);
v_x_1681_ = v___x_1687_;
v_x_1682_ = v_tail_1684_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0___boxed(lean_object* v_newState_1689_, lean_object* v_x_1690_, lean_object* v_x_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1689_, v_x_1690_, v_x_1691_);
lean_dec(v_newState_1689_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1(lean_object* v_x_1693_, lean_object* v_newState_1694_, lean_object* v_newConsts_1695_, lean_object* v_s_1696_){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1694_, v_s_1696_, v_newConsts_1695_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1___boxed(lean_object* v_x_1698_, lean_object* v_newState_1699_, lean_object* v_newConsts_1700_, lean_object* v_s_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Lean_registerTagAttribute___lam__1(v_x_1698_, v_newState_1699_, v_newConsts_1700_, v_s_1701_);
lean_dec(v_newState_1699_);
lean_dec(v_x_1698_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__2(lean_object* v_s_1715_){
_start:
{
lean_object* v___x_1716_; lean_object* v___y_1718_; 
v___x_1716_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__5));
if (lean_obj_tag(v_s_1715_) == 0)
{
lean_object* v_size_1722_; 
v_size_1722_ = lean_ctor_get(v_s_1715_, 0);
lean_inc(v_size_1722_);
lean_dec_ref_known(v_s_1715_, 5);
v___y_1718_ = v_size_1722_;
goto v___jp_1717_;
}
else
{
lean_object* v___x_1723_; 
v___x_1723_ = lean_unsigned_to_nat(0u);
v___y_1718_ = v___x_1723_;
goto v___jp_1717_;
}
v___jp_1717_:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1719_ = l_Nat_reprFast(v___y_1718_);
v___x_1720_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1719_);
v___x_1721_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1716_);
lean_ctor_set(v___x_1721_, 1, v___x_1720_);
return v___x_1721_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(lean_object* v_hi_1724_, lean_object* v_pivot_1725_, lean_object* v_as_1726_, lean_object* v_i_1727_, lean_object* v_k_1728_){
_start:
{
uint8_t v___x_1729_; 
v___x_1729_ = lean_nat_dec_lt(v_k_1728_, v_hi_1724_);
if (v___x_1729_ == 0)
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
lean_dec(v_k_1728_);
v___x_1730_ = lean_array_fswap(v_as_1726_, v_i_1727_, v_hi_1724_);
v___x_1731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1731_, 0, v_i_1727_);
lean_ctor_set(v___x_1731_, 1, v___x_1730_);
return v___x_1731_;
}
else
{
lean_object* v___x_1732_; uint8_t v___x_1733_; 
v___x_1732_ = lean_array_fget_borrowed(v_as_1726_, v_k_1728_);
v___x_1733_ = l_Lean_Name_quickLt(v___x_1732_, v_pivot_1725_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1734_ = lean_unsigned_to_nat(1u);
v___x_1735_ = lean_nat_add(v_k_1728_, v___x_1734_);
lean_dec(v_k_1728_);
v_k_1728_ = v___x_1735_;
goto _start;
}
else
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1737_ = lean_array_fswap(v_as_1726_, v_i_1727_, v_k_1728_);
v___x_1738_ = lean_unsigned_to_nat(1u);
v___x_1739_ = lean_nat_add(v_i_1727_, v___x_1738_);
lean_dec(v_i_1727_);
v___x_1740_ = lean_nat_add(v_k_1728_, v___x_1738_);
lean_dec(v_k_1728_);
v_as_1726_ = v___x_1737_;
v_i_1727_ = v___x_1739_;
v_k_1728_ = v___x_1740_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg___boxed(lean_object* v_hi_1742_, lean_object* v_pivot_1743_, lean_object* v_as_1744_, lean_object* v_i_1745_, lean_object* v_k_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1742_, v_pivot_1743_, v_as_1744_, v_i_1745_, v_k_1746_);
lean_dec(v_pivot_1743_);
lean_dec(v_hi_1742_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(lean_object* v_n_1748_, lean_object* v_as_1749_, lean_object* v_lo_1750_, lean_object* v_hi_1751_){
_start:
{
lean_object* v___y_1753_; uint8_t v___x_1763_; 
v___x_1763_ = lean_nat_dec_lt(v_lo_1750_, v_hi_1751_);
if (v___x_1763_ == 0)
{
lean_dec(v_lo_1750_);
return v_as_1749_;
}
else
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v_mid_1766_; lean_object* v___y_1768_; lean_object* v___y_1774_; lean_object* v___x_1779_; lean_object* v___x_1780_; uint8_t v___x_1781_; 
v___x_1764_ = lean_nat_add(v_lo_1750_, v_hi_1751_);
v___x_1765_ = lean_unsigned_to_nat(1u);
v_mid_1766_ = lean_nat_shiftr(v___x_1764_, v___x_1765_);
lean_dec(v___x_1764_);
v___x_1779_ = lean_array_fget_borrowed(v_as_1749_, v_mid_1766_);
v___x_1780_ = lean_array_fget_borrowed(v_as_1749_, v_lo_1750_);
v___x_1781_ = l_Lean_Name_quickLt(v___x_1779_, v___x_1780_);
if (v___x_1781_ == 0)
{
v___y_1774_ = v_as_1749_;
goto v___jp_1773_;
}
else
{
lean_object* v___x_1782_; 
v___x_1782_ = lean_array_fswap(v_as_1749_, v_lo_1750_, v_mid_1766_);
v___y_1774_ = v___x_1782_;
goto v___jp_1773_;
}
v___jp_1767_:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; uint8_t v___x_1771_; 
v___x_1769_ = lean_array_fget_borrowed(v___y_1768_, v_mid_1766_);
v___x_1770_ = lean_array_fget_borrowed(v___y_1768_, v_hi_1751_);
v___x_1771_ = l_Lean_Name_quickLt(v___x_1769_, v___x_1770_);
if (v___x_1771_ == 0)
{
lean_dec(v_mid_1766_);
v___y_1753_ = v___y_1768_;
goto v___jp_1752_;
}
else
{
lean_object* v___x_1772_; 
v___x_1772_ = lean_array_fswap(v___y_1768_, v_mid_1766_, v_hi_1751_);
lean_dec(v_mid_1766_);
v___y_1753_ = v___x_1772_;
goto v___jp_1752_;
}
}
v___jp_1773_:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; uint8_t v___x_1777_; 
v___x_1775_ = lean_array_fget_borrowed(v___y_1774_, v_hi_1751_);
v___x_1776_ = lean_array_fget_borrowed(v___y_1774_, v_lo_1750_);
v___x_1777_ = l_Lean_Name_quickLt(v___x_1775_, v___x_1776_);
if (v___x_1777_ == 0)
{
v___y_1768_ = v___y_1774_;
goto v___jp_1767_;
}
else
{
lean_object* v___x_1778_; 
v___x_1778_ = lean_array_fswap(v___y_1774_, v_lo_1750_, v_hi_1751_);
v___y_1768_ = v___x_1778_;
goto v___jp_1767_;
}
}
}
v___jp_1752_:
{
lean_object* v_pivot_1754_; lean_object* v___x_1755_; lean_object* v_fst_1756_; lean_object* v_snd_1757_; uint8_t v___x_1758_; 
v_pivot_1754_ = lean_array_fget(v___y_1753_, v_hi_1751_);
lean_inc_n(v_lo_1750_, 2);
v___x_1755_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1751_, v_pivot_1754_, v___y_1753_, v_lo_1750_, v_lo_1750_);
lean_dec(v_pivot_1754_);
v_fst_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_fst_1756_);
v_snd_1757_ = lean_ctor_get(v___x_1755_, 1);
lean_inc(v_snd_1757_);
lean_dec_ref(v___x_1755_);
v___x_1758_ = lean_nat_dec_le(v_hi_1751_, v_fst_1756_);
if (v___x_1758_ == 0)
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1759_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1748_, v_snd_1757_, v_lo_1750_, v_fst_1756_);
v___x_1760_ = lean_unsigned_to_nat(1u);
v___x_1761_ = lean_nat_add(v_fst_1756_, v___x_1760_);
lean_dec(v_fst_1756_);
v_as_1749_ = v___x_1759_;
v_lo_1750_ = v___x_1761_;
goto _start;
}
else
{
lean_dec(v_fst_1756_);
lean_dec(v_lo_1750_);
return v_snd_1757_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg___boxed(lean_object* v_n_1783_, lean_object* v_as_1784_, lean_object* v_lo_1785_, lean_object* v_hi_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1783_, v_as_1784_, v_lo_1785_, v_hi_1786_);
lean_dec(v_hi_1786_);
lean_dec(v_n_1783_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(lean_object* v_env_1788_, lean_object* v_as_1789_, size_t v_i_1790_, size_t v_stop_1791_, lean_object* v_b_1792_){
_start:
{
lean_object* v___y_1794_; uint8_t v___x_1798_; 
v___x_1798_ = lean_usize_dec_eq(v_i_1790_, v_stop_1791_);
if (v___x_1798_ == 0)
{
lean_object* v___x_1799_; uint8_t v___x_1800_; lean_object* v___x_1801_; uint8_t v___x_1802_; 
v___x_1799_ = lean_array_uget_borrowed(v_as_1789_, v_i_1790_);
v___x_1800_ = 1;
lean_inc_ref(v_env_1788_);
v___x_1801_ = l_Lean_Environment_setExporting(v_env_1788_, v___x_1800_);
lean_inc(v___x_1799_);
v___x_1802_ = l_Lean_Environment_contains(v___x_1801_, v___x_1799_, v___x_1798_);
if (v___x_1802_ == 0)
{
v___y_1794_ = v_b_1792_;
goto v___jp_1793_;
}
else
{
lean_object* v___x_1803_; 
lean_inc(v___x_1799_);
v___x_1803_ = lean_array_push(v_b_1792_, v___x_1799_);
v___y_1794_ = v___x_1803_;
goto v___jp_1793_;
}
}
else
{
lean_dec_ref(v_env_1788_);
return v_b_1792_;
}
v___jp_1793_:
{
size_t v___x_1795_; size_t v___x_1796_; 
v___x_1795_ = ((size_t)1ULL);
v___x_1796_ = lean_usize_add(v_i_1790_, v___x_1795_);
v_i_1790_ = v___x_1796_;
v_b_1792_ = v___y_1794_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2___boxed(lean_object* v_env_1804_, lean_object* v_as_1805_, lean_object* v_i_1806_, lean_object* v_stop_1807_, lean_object* v_b_1808_){
_start:
{
size_t v_i_boxed_1809_; size_t v_stop_boxed_1810_; lean_object* v_res_1811_; 
v_i_boxed_1809_ = lean_unbox_usize(v_i_1806_);
lean_dec(v_i_1806_);
v_stop_boxed_1810_ = lean_unbox_usize(v_stop_1807_);
lean_dec(v_stop_1807_);
v_res_1811_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1804_, v_as_1805_, v_i_boxed_1809_, v_stop_boxed_1810_, v_b_1808_);
lean_dec_ref(v_as_1805_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(lean_object* v_init_1812_, lean_object* v_x_1813_){
_start:
{
if (lean_obj_tag(v_x_1813_) == 0)
{
lean_object* v_k_1814_; lean_object* v_l_1815_; lean_object* v_r_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v_k_1814_ = lean_ctor_get(v_x_1813_, 1);
lean_inc(v_k_1814_);
v_l_1815_ = lean_ctor_get(v_x_1813_, 3);
lean_inc(v_l_1815_);
v_r_1816_ = lean_ctor_get(v_x_1813_, 4);
lean_inc(v_r_1816_);
lean_dec_ref_known(v_x_1813_, 5);
v___x_1817_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_1812_, v_l_1815_);
v___x_1818_ = lean_array_push(v___x_1817_, v_k_1814_);
v_init_1812_ = v___x_1818_;
v_x_1813_ = v_r_1816_;
goto _start;
}
else
{
return v_init_1812_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__3(lean_object* v_env_1820_, lean_object* v_es_1821_){
_start:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___y_1825_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___y_1842_; lean_object* v___y_1843_; uint8_t v___x_1845_; 
v___x_1822_ = lean_unsigned_to_nat(0u);
v___x_1823_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
v___x_1839_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v___x_1823_, v_es_1821_);
v___x_1840_ = lean_array_get_size(v___x_1839_);
v___x_1845_ = lean_nat_dec_eq(v___x_1840_, v___x_1822_);
if (v___x_1845_ == 0)
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___y_1849_; uint8_t v___x_1851_; 
v___x_1846_ = lean_unsigned_to_nat(1u);
v___x_1847_ = lean_nat_sub(v___x_1840_, v___x_1846_);
v___x_1851_ = lean_nat_dec_le(v___x_1822_, v___x_1847_);
if (v___x_1851_ == 0)
{
lean_inc(v___x_1847_);
v___y_1849_ = v___x_1847_;
goto v___jp_1848_;
}
else
{
v___y_1849_ = v___x_1822_;
goto v___jp_1848_;
}
v___jp_1848_:
{
uint8_t v___x_1850_; 
v___x_1850_ = lean_nat_dec_le(v___y_1849_, v___x_1847_);
if (v___x_1850_ == 0)
{
lean_dec(v___x_1847_);
lean_inc(v___y_1849_);
v___y_1842_ = v___y_1849_;
v___y_1843_ = v___y_1849_;
goto v___jp_1841_;
}
else
{
v___y_1842_ = v___y_1849_;
v___y_1843_ = v___x_1847_;
goto v___jp_1841_;
}
}
}
else
{
v___y_1825_ = v___x_1839_;
goto v___jp_1824_;
}
v___jp_1824_:
{
lean_object* v___x_1826_; uint8_t v___x_1827_; 
v___x_1826_ = lean_array_get_size(v___y_1825_);
v___x_1827_ = lean_nat_dec_lt(v___x_1822_, v___x_1826_);
if (v___x_1827_ == 0)
{
lean_object* v___x_1828_; 
lean_dec_ref(v_env_1820_);
v___x_1828_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1823_);
lean_ctor_set(v___x_1828_, 1, v___x_1823_);
lean_ctor_set(v___x_1828_, 2, v___y_1825_);
return v___x_1828_;
}
else
{
uint8_t v___x_1829_; 
v___x_1829_ = lean_nat_dec_le(v___x_1826_, v___x_1826_);
if (v___x_1829_ == 0)
{
if (v___x_1827_ == 0)
{
lean_object* v___x_1830_; 
lean_dec_ref(v_env_1820_);
v___x_1830_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1823_);
lean_ctor_set(v___x_1830_, 1, v___x_1823_);
lean_ctor_set(v___x_1830_, 2, v___y_1825_);
return v___x_1830_;
}
else
{
size_t v___x_1831_; size_t v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1831_ = ((size_t)0ULL);
v___x_1832_ = lean_usize_of_nat(v___x_1826_);
v___x_1833_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1820_, v___y_1825_, v___x_1831_, v___x_1832_, v___x_1823_);
lean_inc_ref(v___x_1833_);
v___x_1834_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1833_);
lean_ctor_set(v___x_1834_, 1, v___x_1833_);
lean_ctor_set(v___x_1834_, 2, v___y_1825_);
return v___x_1834_;
}
}
else
{
size_t v___x_1835_; size_t v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1835_ = ((size_t)0ULL);
v___x_1836_ = lean_usize_of_nat(v___x_1826_);
v___x_1837_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1820_, v___y_1825_, v___x_1835_, v___x_1836_, v___x_1823_);
lean_inc_ref(v___x_1837_);
v___x_1838_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1837_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
lean_ctor_set(v___x_1838_, 2, v___y_1825_);
return v___x_1838_;
}
}
}
v___jp_1841_:
{
lean_object* v___x_1844_; 
v___x_1844_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v___x_1840_, v___x_1839_, v___y_1842_, v___y_1843_);
lean_dec(v___y_1843_);
v___y_1825_ = v___x_1844_;
goto v___jp_1824_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4(lean_object* v_name_1852_, lean_object* v_decl_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1857_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_1858_ = l_Lean_MessageData_ofName(v_name_1852_);
v___x_1859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1857_);
lean_ctor_set(v___x_1859_, 1, v___x_1858_);
v___x_1860_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_1861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1859_);
lean_ctor_set(v___x_1861_, 1, v___x_1860_);
v___x_1862_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1861_, v___y_1854_, v___y_1855_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4___boxed(lean_object* v_name_1863_, lean_object* v_decl_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_Lean_registerTagAttribute___lam__4(v_name_1863_, v_decl_1864_, v___y_1865_, v___y_1866_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v_decl_1864_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5(lean_object* v___x_1869_, lean_object* v_x_1870_, lean_object* v_x_1871_){
_start:
{
lean_object* v___x_1873_; 
v___x_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1869_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5___boxed(lean_object* v___x_1874_, lean_object* v_x_1875_, lean_object* v_x_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l_Lean_registerTagAttribute___lam__5(v___x_1874_, v_x_1875_, v_x_1876_);
lean_dec_ref(v_x_1876_);
lean_dec_ref(v_x_1875_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6(lean_object* v___x_1879_){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1879_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6___boxed(lean_object* v___x_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l_Lean_registerTagAttribute___lam__6(v___x_1882_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(lean_object* v_attrName_1885_, lean_object* v_declName_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_){
_start:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; uint8_t v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1890_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1891_ = l_Lean_MessageData_ofName(v_attrName_1885_);
v___x_1892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1890_);
lean_ctor_set(v___x_1892_, 1, v___x_1891_);
v___x_1893_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1892_);
lean_ctor_set(v___x_1894_, 1, v___x_1893_);
v___x_1895_ = 0;
v___x_1896_ = l_Lean_MessageData_ofConstName(v_declName_1886_, v___x_1895_);
v___x_1897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1894_);
lean_ctor_set(v___x_1897_, 1, v___x_1896_);
v___x_1898_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1897_);
lean_ctor_set(v___x_1899_, 1, v___x_1898_);
v___x_1900_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1899_, v___y_1887_, v___y_1888_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg___boxed(lean_object* v_attrName_1901_, lean_object* v_declName_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_1901_, v_declName_1902_, v___y_1903_, v___y_1904_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(lean_object* v_attrName_1907_, lean_object* v_declName_1908_, lean_object* v_asyncPrefix_x3f_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v___y_1914_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1909_) == 0)
{
lean_object* v___x_1927_; 
v___x_1927_ = l_Lean_MessageData_nil;
v___y_1914_ = v___x_1927_;
goto v___jp_1913_;
}
else
{
lean_object* v_val_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
v_val_1928_ = lean_ctor_get(v_asyncPrefix_x3f_1909_, 0);
lean_inc(v_val_1928_);
lean_dec_ref_known(v_asyncPrefix_x3f_1909_, 1);
v___x_1929_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1930_ = l_Lean_MessageData_ofName(v_val_1928_);
v___x_1931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1929_);
lean_ctor_set(v___x_1931_, 1, v___x_1930_);
v___x_1932_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1931_);
lean_ctor_set(v___x_1933_, 1, v___x_1932_);
v___y_1914_ = v___x_1933_;
goto v___jp_1913_;
}
v___jp_1913_:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; uint8_t v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1915_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1916_ = l_Lean_MessageData_ofName(v_attrName_1907_);
v___x_1917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1915_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
v___x_1918_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1917_);
lean_ctor_set(v___x_1919_, 1, v___x_1918_);
v___x_1920_ = 0;
v___x_1921_ = l_Lean_MessageData_ofConstName(v_declName_1908_, v___x_1920_);
v___x_1922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1919_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
v___x_1923_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1922_);
lean_ctor_set(v___x_1924_, 1, v___x_1923_);
v___x_1925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1924_);
lean_ctor_set(v___x_1925_, 1, v___y_1914_);
v___x_1926_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1925_, v___y_1910_, v___y_1911_);
return v___x_1926_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg___boxed(lean_object* v_attrName_1934_, lean_object* v_declName_1935_, lean_object* v_asyncPrefix_x3f_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
lean_object* v_res_1940_; 
v_res_1940_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_1934_, v_declName_1935_, v_asyncPrefix_x3f_1936_, v___y_1937_, v___y_1938_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(lean_object* v_name_1941_, uint8_t v_kind_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___y_1952_; 
v___x_1946_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_1947_ = l_Lean_MessageData_ofName(v_name_1941_);
v___x_1948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1946_);
lean_ctor_set(v___x_1948_, 1, v___x_1947_);
v___x_1949_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_1950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1948_);
lean_ctor_set(v___x_1950_, 1, v___x_1949_);
switch(v_kind_1942_)
{
case 0:
{
lean_object* v___x_1959_; 
v___x_1959_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_1952_ = v___x_1959_;
goto v___jp_1951_;
}
case 1:
{
lean_object* v___x_1960_; 
v___x_1960_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_1952_ = v___x_1960_;
goto v___jp_1951_;
}
default: 
{
lean_object* v___x_1961_; 
v___x_1961_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_1952_ = v___x_1961_;
goto v___jp_1951_;
}
}
v___jp_1951_:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
lean_inc_ref(v___y_1952_);
v___x_1953_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1953_, 0, v___y_1952_);
v___x_1954_ = l_Lean_MessageData_ofFormat(v___x_1953_);
v___x_1955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1950_);
lean_ctor_set(v___x_1955_, 1, v___x_1954_);
v___x_1956_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1955_);
lean_ctor_set(v___x_1957_, 1, v___x_1956_);
v___x_1958_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1957_, v___y_1943_, v___y_1944_);
return v___x_1958_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg___boxed(lean_object* v_name_1962_, lean_object* v_kind_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
uint8_t v_kind_boxed_1967_; lean_object* v_res_1968_; 
v_kind_boxed_1967_ = lean_unbox(v_kind_1963_);
v_res_1968_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_1962_, v_kind_boxed_1967_, v___y_1964_, v___y_1965_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7(lean_object* v_validate_1969_, lean_object* v_a_1970_, lean_object* v_name_1971_, lean_object* v_decl_1972_, lean_object* v_stx_1973_, uint8_t v_kind_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___x_2028_; 
v___x_2028_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_1973_, v___y_1975_, v___y_1976_);
if (lean_obj_tag(v___x_2028_) == 0)
{
uint8_t v___x_2029_; uint8_t v___x_2030_; 
lean_dec_ref_known(v___x_2028_, 1);
v___x_2029_ = 0;
v___x_2030_ = l_Lean_instBEqAttributeKind_beq(v_kind_1974_, v___x_2029_);
if (v___x_2030_ == 0)
{
lean_object* v___x_2031_; 
lean_dec(v_decl_1972_);
lean_dec_ref(v_a_1970_);
lean_dec_ref(v_validate_1969_);
v___x_2031_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_1971_, v_kind_1974_, v___y_1975_, v___y_1976_);
return v___x_2031_;
}
else
{
goto v___jp_2023_;
}
}
else
{
lean_dec(v_decl_1972_);
lean_dec(v_name_1971_);
lean_dec_ref(v_a_1970_);
lean_dec_ref(v_validate_1969_);
return v___x_2028_;
}
v___jp_1978_:
{
lean_object* v___x_1981_; 
lean_inc(v___y_1980_);
lean_inc_ref(v___y_1979_);
lean_inc(v_decl_1972_);
v___x_1981_ = lean_apply_4(v_validate_1969_, v_decl_1972_, v___y_1979_, v___y_1980_, lean_box(0));
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_2012_; 
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_2012_ == 0)
{
lean_object* v_unused_2013_; 
v_unused_2013_ = lean_ctor_get(v___x_1981_, 0);
lean_dec(v_unused_2013_);
v___x_1983_ = v___x_1981_;
v_isShared_1984_ = v_isSharedCheck_2012_;
goto v_resetjp_1982_;
}
else
{
lean_dec(v___x_1981_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_2012_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1985_; lean_object* v_toEnvExtension_1986_; lean_object* v_env_1987_; lean_object* v_nextMacroScope_1988_; lean_object* v_ngen_1989_; lean_object* v_auxDeclNGen_1990_; lean_object* v_traceState_1991_; lean_object* v_recordedDeps_1992_; lean_object* v_messages_1993_; lean_object* v_infoState_1994_; lean_object* v_snapshotTasks_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2010_; 
v___x_1985_ = lean_st_ref_take(v___y_1980_);
v_toEnvExtension_1986_ = lean_ctor_get(v_a_1970_, 0);
v_env_1987_ = lean_ctor_get(v___x_1985_, 0);
v_nextMacroScope_1988_ = lean_ctor_get(v___x_1985_, 1);
v_ngen_1989_ = lean_ctor_get(v___x_1985_, 2);
v_auxDeclNGen_1990_ = lean_ctor_get(v___x_1985_, 3);
v_traceState_1991_ = lean_ctor_get(v___x_1985_, 4);
v_recordedDeps_1992_ = lean_ctor_get(v___x_1985_, 6);
v_messages_1993_ = lean_ctor_get(v___x_1985_, 7);
v_infoState_1994_ = lean_ctor_get(v___x_1985_, 8);
v_snapshotTasks_1995_ = lean_ctor_get(v___x_1985_, 9);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_2010_ == 0)
{
lean_object* v_unused_2011_; 
v_unused_2011_ = lean_ctor_get(v___x_1985_, 5);
lean_dec(v_unused_2011_);
v___x_1997_ = v___x_1985_;
v_isShared_1998_ = v_isSharedCheck_2010_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_snapshotTasks_1995_);
lean_inc(v_infoState_1994_);
lean_inc(v_messages_1993_);
lean_inc(v_recordedDeps_1992_);
lean_inc(v_traceState_1991_);
lean_inc(v_auxDeclNGen_1990_);
lean_inc(v_ngen_1989_);
lean_inc(v_nextMacroScope_1988_);
lean_inc(v_env_1987_);
lean_dec(v___x_1985_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2010_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v_asyncMode_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2004_; 
v_asyncMode_1999_ = lean_ctor_get(v_toEnvExtension_1986_, 2);
lean_inc(v_asyncMode_1999_);
v___x_2000_ = lean_box(0);
lean_inc(v_decl_1972_);
v___x_2001_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_1970_, v_env_1987_, v_decl_1972_, v_asyncMode_1999_, v_decl_1972_);
lean_dec(v_asyncMode_1999_);
v___x_2002_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 5, v___x_2002_);
lean_ctor_set(v___x_1997_, 0, v___x_2001_);
v___x_2004_ = v___x_1997_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v___x_2001_);
lean_ctor_set(v_reuseFailAlloc_2009_, 1, v_nextMacroScope_1988_);
lean_ctor_set(v_reuseFailAlloc_2009_, 2, v_ngen_1989_);
lean_ctor_set(v_reuseFailAlloc_2009_, 3, v_auxDeclNGen_1990_);
lean_ctor_set(v_reuseFailAlloc_2009_, 4, v_traceState_1991_);
lean_ctor_set(v_reuseFailAlloc_2009_, 5, v___x_2002_);
lean_ctor_set(v_reuseFailAlloc_2009_, 6, v_recordedDeps_1992_);
lean_ctor_set(v_reuseFailAlloc_2009_, 7, v_messages_1993_);
lean_ctor_set(v_reuseFailAlloc_2009_, 8, v_infoState_1994_);
lean_ctor_set(v_reuseFailAlloc_2009_, 9, v_snapshotTasks_1995_);
v___x_2004_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
lean_object* v___x_2005_; lean_object* v___x_2007_; 
v___x_2005_ = lean_st_ref_put(v___y_1980_, v___x_2004_);
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 0, v___x_2000_);
v___x_2007_ = v___x_1983_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v___x_2000_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
}
}
else
{
lean_dec(v_decl_1972_);
lean_dec_ref(v_a_1970_);
return v___x_1981_;
}
}
v___jp_2014_:
{
lean_object* v_toEnvExtension_2018_; lean_object* v_asyncMode_2019_; uint8_t v___x_2020_; 
v_toEnvExtension_2018_ = lean_ctor_get(v_a_1970_, 0);
v_asyncMode_2019_ = lean_ctor_get(v_toEnvExtension_2018_, 2);
lean_inc(v_decl_1972_);
lean_inc_ref(v___y_2015_);
v___x_2020_ = l_Lean_EnvExtension_asyncMayModify___redArg(v___y_2015_, v_decl_1972_, v_asyncMode_2019_);
if (v___x_2020_ == 0)
{
lean_object* v___x_2021_; lean_object* v___x_2022_; 
lean_dec_ref(v_a_1970_);
lean_dec_ref(v_validate_1969_);
v___x_2021_ = l_Lean_Environment_asyncPrefix_x3f(v___y_2015_);
v___x_2022_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_name_1971_, v_decl_1972_, v___x_2021_, v___y_2016_, v___y_2017_);
return v___x_2022_;
}
else
{
lean_dec_ref(v___y_2015_);
lean_dec(v_name_1971_);
v___y_1979_ = v___y_2016_;
v___y_1980_ = v___y_2017_;
goto v___jp_1978_;
}
}
v___jp_2023_:
{
lean_object* v___x_2024_; lean_object* v_env_2025_; lean_object* v___x_2026_; 
v___x_2024_ = lean_st_ref_get(v___y_1976_);
v_env_2025_ = lean_ctor_get(v___x_2024_, 0);
lean_inc_ref(v_env_2025_);
lean_dec(v___x_2024_);
v___x_2026_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2025_, v_decl_1972_);
if (lean_obj_tag(v___x_2026_) == 0)
{
v___y_2015_ = v_env_2025_;
v___y_2016_ = v___y_1975_;
v___y_2017_ = v___y_1976_;
goto v___jp_2014_;
}
else
{
lean_object* v___x_2027_; 
lean_dec_ref_known(v___x_2026_, 1);
lean_dec_ref(v_env_2025_);
lean_dec_ref(v_a_1970_);
lean_dec_ref(v_validate_1969_);
v___x_2027_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_1971_, v_decl_1972_, v___y_1975_, v___y_1976_);
return v___x_2027_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7___boxed(lean_object* v_validate_2032_, lean_object* v_a_2033_, lean_object* v_name_2034_, lean_object* v_decl_2035_, lean_object* v_stx_2036_, lean_object* v_kind_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
uint8_t v_kind_boxed_2041_; lean_object* v_res_2042_; 
v_kind_boxed_2041_ = lean_unbox(v_kind_2037_);
v_res_2042_ = l_Lean_registerTagAttribute___lam__7(v_validate_2032_, v_a_2033_, v_name_2034_, v_decl_2035_, v_stx_2036_, v_kind_boxed_2041_, v___y_2038_, v___y_2039_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
return v_res_2042_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__5(void){
_start:
{
lean_object* v___x_2048_; lean_object* v___f_2049_; 
v___x_2048_ = l_Lean_NameSet_empty;
v___f_2049_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__5___boxed), 4, 1);
lean_closure_set(v___f_2049_, 0, v___x_2048_);
return v___f_2049_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__6(void){
_start:
{
lean_object* v___x_2050_; lean_object* v___f_2051_; 
v___x_2050_ = l_Lean_NameSet_empty;
v___f_2051_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__6___boxed), 2, 1);
lean_closure_set(v___f_2051_, 0, v___x_2050_);
return v___f_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute(lean_object* v_name_2054_, lean_object* v_descr_2055_, lean_object* v_validate_2056_, lean_object* v_ref_2057_, uint8_t v_applicationTime_2058_, lean_object* v_asyncMode_2059_){
_start:
{
lean_object* v___f_2061_; lean_object* v___f_2062_; lean_object* v___f_2063_; lean_object* v___f_2064_; lean_object* v___f_2065_; lean_object* v___f_2066_; lean_object* v___f_2067_; lean_object* v___x_2068_; uint8_t v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___f_2061_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__0));
v___f_2062_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__2));
v___f_2063_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__3));
v___f_2064_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__4));
lean_inc(v_name_2054_);
v___f_2065_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__4___boxed), 5, 1);
lean_closure_set(v___f_2065_, 0, v_name_2054_);
v___f_2066_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__5, &l_Lean_registerTagAttribute___closed__5_once, _init_l_Lean_registerTagAttribute___closed__5);
v___f_2067_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__6, &l_Lean_registerTagAttribute___closed__6_once, _init_l_Lean_registerTagAttribute___closed__6);
v___x_2068_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__7));
v___x_2069_ = 0;
lean_inc(v_ref_2057_);
v___x_2070_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_2070_, 0, v_ref_2057_);
lean_ctor_set(v___x_2070_, 1, v___f_2067_);
lean_ctor_set(v___x_2070_, 2, v___f_2066_);
lean_ctor_set(v___x_2070_, 3, v___f_2064_);
lean_ctor_set(v___x_2070_, 4, v___f_2063_);
lean_ctor_set(v___x_2070_, 5, v___f_2062_);
lean_ctor_set(v___x_2070_, 6, v_asyncMode_2059_);
lean_ctor_set(v___x_2070_, 7, v___x_2068_);
lean_ctor_set_uint8(v___x_2070_, sizeof(void*)*8, v___x_2069_);
v___x_2071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2070_);
lean_ctor_set(v___x_2071_, 1, v___f_2061_);
v___x_2072_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2071_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v_a_2073_; lean_object* v___f_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
lean_inc_n(v_a_2073_, 2);
lean_dec_ref_known(v___x_2072_, 1);
lean_inc(v_name_2054_);
v___f_2074_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__7___boxed), 9, 3);
lean_closure_set(v___f_2074_, 0, v_validate_2056_);
lean_closure_set(v___f_2074_, 1, v_a_2073_);
lean_closure_set(v___f_2074_, 2, v_name_2054_);
v___x_2075_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2075_, 0, v_ref_2057_);
lean_ctor_set(v___x_2075_, 1, v_name_2054_);
lean_ctor_set(v___x_2075_, 2, v_descr_2055_);
lean_ctor_set_uint8(v___x_2075_, sizeof(void*)*3, v_applicationTime_2058_);
v___x_2076_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2075_);
lean_ctor_set(v___x_2076_, 1, v___f_2074_);
lean_ctor_set(v___x_2076_, 2, v___f_2065_);
lean_inc_ref(v___x_2076_);
v___x_2077_ = l_Lean_registerBuiltinAttribute(v___x_2076_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2085_; 
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2085_ == 0)
{
lean_object* v_unused_2086_; 
v_unused_2086_ = lean_ctor_get(v___x_2077_, 0);
lean_dec(v_unused_2086_);
v___x_2079_ = v___x_2077_;
v_isShared_2080_ = v_isSharedCheck_2085_;
goto v_resetjp_2078_;
}
else
{
lean_dec(v___x_2077_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2085_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2081_; lean_object* v___x_2083_; 
v___x_2081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2076_);
lean_ctor_set(v___x_2081_, 1, v_a_2073_);
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 0, v___x_2081_);
v___x_2083_ = v___x_2079_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_2081_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
else
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
lean_dec_ref_known(v___x_2076_, 3);
lean_dec(v_a_2073_);
v_a_2087_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2089_ = v___x_2077_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2077_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2090_ == 0)
{
v___x_2092_ = v___x_2089_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
}
else
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2102_; 
lean_dec_ref(v___f_2065_);
lean_dec(v_ref_2057_);
lean_dec_ref(v_validate_2056_);
lean_dec_ref(v_descr_2055_);
lean_dec(v_name_2054_);
v_a_2095_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2097_ = v___x_2072_;
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2072_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2098_ == 0)
{
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_a_2095_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___boxed(lean_object* v_name_2103_, lean_object* v_descr_2104_, lean_object* v_validate_2105_, lean_object* v_ref_2106_, lean_object* v_applicationTime_2107_, lean_object* v_asyncMode_2108_, lean_object* v_a_2109_){
_start:
{
uint8_t v_applicationTime_boxed_2110_; lean_object* v_res_2111_; 
v_applicationTime_boxed_2110_ = lean_unbox(v_applicationTime_2107_);
v_res_2111_ = l_Lean_registerTagAttribute(v_name_2103_, v_descr_2104_, v_validate_2105_, v_ref_2106_, v_applicationTime_boxed_2110_, v_asyncMode_2108_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1(lean_object* v_init_2112_, lean_object* v_t_2113_){
_start:
{
lean_object* v___x_2114_; 
v___x_2114_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_2112_, v_t_2113_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(lean_object* v_n_2115_, lean_object* v_as_2116_, lean_object* v_lo_2117_, lean_object* v_hi_2118_, lean_object* v_w_2119_, lean_object* v_hlo_2120_, lean_object* v_hhi_2121_){
_start:
{
lean_object* v___x_2122_; 
v___x_2122_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_2115_, v_as_2116_, v_lo_2117_, v_hi_2118_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___boxed(lean_object* v_n_2123_, lean_object* v_as_2124_, lean_object* v_lo_2125_, lean_object* v_hi_2126_, lean_object* v_w_2127_, lean_object* v_hlo_2128_, lean_object* v_hhi_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(v_n_2123_, v_as_2124_, v_lo_2125_, v_hi_2126_, v_w_2127_, v_hlo_2128_, v_hhi_2129_);
lean_dec(v_hi_2126_);
lean_dec(v_n_2123_);
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(lean_object* v_00_u03b1_2131_, lean_object* v_attrName_2132_, lean_object* v_declName_2133_, lean_object* v_asyncPrefix_x3f_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v___x_2138_; 
v___x_2138_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_2132_, v_declName_2133_, v_asyncPrefix_x3f_2134_, v___y_2135_, v___y_2136_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___boxed(lean_object* v_00_u03b1_2139_, lean_object* v_attrName_2140_, lean_object* v_declName_2141_, lean_object* v_asyncPrefix_x3f_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_){
_start:
{
lean_object* v_res_2146_; 
v_res_2146_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(v_00_u03b1_2139_, v_attrName_2140_, v_declName_2141_, v_asyncPrefix_x3f_2142_, v___y_2143_, v___y_2144_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2143_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(lean_object* v_00_u03b1_2147_, lean_object* v_attrName_2148_, lean_object* v_declName_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
lean_object* v___x_2153_; 
v___x_2153_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_2148_, v_declName_2149_, v___y_2150_, v___y_2151_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___boxed(lean_object* v_00_u03b1_2154_, lean_object* v_attrName_2155_, lean_object* v_declName_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_){
_start:
{
lean_object* v_res_2160_; 
v_res_2160_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(v_00_u03b1_2154_, v_attrName_2155_, v_declName_2156_, v___y_2157_, v___y_2158_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(lean_object* v_00_u03b1_2161_, lean_object* v_name_2162_, uint8_t v_kind_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
lean_object* v___x_2167_; 
v___x_2167_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2162_, v_kind_2163_, v___y_2164_, v___y_2165_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___boxed(lean_object* v_00_u03b1_2168_, lean_object* v_name_2169_, lean_object* v_kind_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_){
_start:
{
uint8_t v_kind_boxed_2174_; lean_object* v_res_2175_; 
v_kind_boxed_2174_ = lean_unbox(v_kind_2170_);
v_res_2175_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(v_00_u03b1_2168_, v_name_2169_, v_kind_boxed_2174_, v___y_2171_, v___y_2172_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
return v_res_2175_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(lean_object* v_n_2176_, lean_object* v_lo_2177_, lean_object* v_hi_2178_, lean_object* v_hhi_2179_, lean_object* v_pivot_2180_, lean_object* v_as_2181_, lean_object* v_i_2182_, lean_object* v_k_2183_, lean_object* v_ilo_2184_, lean_object* v_ik_2185_, lean_object* v_w_2186_){
_start:
{
lean_object* v___x_2187_; 
v___x_2187_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_2178_, v_pivot_2180_, v_as_2181_, v_i_2182_, v_k_2183_);
return v___x_2187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___boxed(lean_object* v_n_2188_, lean_object* v_lo_2189_, lean_object* v_hi_2190_, lean_object* v_hhi_2191_, lean_object* v_pivot_2192_, lean_object* v_as_2193_, lean_object* v_i_2194_, lean_object* v_k_2195_, lean_object* v_ilo_2196_, lean_object* v_ik_2197_, lean_object* v_w_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(v_n_2188_, v_lo_2189_, v_hi_2190_, v_hhi_2191_, v_pivot_2192_, v_as_2193_, v_i_2194_, v_k_2195_, v_ilo_2196_, v_ik_2197_, v_w_2198_);
lean_dec(v_pivot_2192_);
lean_dec(v_hi_2190_);
lean_dec(v_lo_2189_);
lean_dec(v_n_2188_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__0(lean_object* v_attr_2200_, lean_object* v_decl_2201_, lean_object* v_env_2202_){
_start:
{
lean_object* v_ext_2203_; lean_object* v_toEnvExtension_2204_; lean_object* v_asyncMode_2205_; lean_object* v___x_2206_; 
v_ext_2203_ = lean_ctor_get(v_attr_2200_, 1);
lean_inc_ref(v_ext_2203_);
lean_dec_ref(v_attr_2200_);
v_toEnvExtension_2204_ = lean_ctor_get(v_ext_2203_, 0);
v_asyncMode_2205_ = lean_ctor_get(v_toEnvExtension_2204_, 2);
lean_inc(v_asyncMode_2205_);
lean_inc(v_decl_2201_);
v___x_2206_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2203_, v_env_2202_, v_decl_2201_, v_asyncMode_2205_, v_decl_2201_);
lean_dec(v_asyncMode_2205_);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__1(lean_object* v_modifyEnv_2207_, lean_object* v___f_2208_, lean_object* v_____r_2209_){
_start:
{
lean_object* v___x_2210_; 
v___x_2210_ = lean_apply_1(v_modifyEnv_2207_, v___f_2208_);
return v___x_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__2(lean_object* v_attr_2211_, lean_object* v_env_2212_, lean_object* v_decl_2213_, lean_object* v_inst_2214_, lean_object* v_inst_2215_, lean_object* v_toBind_2216_, lean_object* v___f_2217_, lean_object* v_modifyEnv_2218_, lean_object* v___f_2219_, lean_object* v_____r_2220_){
_start:
{
lean_object* v_ext_2221_; lean_object* v_toEnvExtension_2222_; lean_object* v_attr_2223_; lean_object* v_asyncMode_2224_; uint8_t v___x_2225_; 
v_ext_2221_ = lean_ctor_get(v_attr_2211_, 1);
v_toEnvExtension_2222_ = lean_ctor_get(v_ext_2221_, 0);
lean_inc_ref(v_toEnvExtension_2222_);
v_attr_2223_ = lean_ctor_get(v_attr_2211_, 0);
lean_inc_ref(v_attr_2223_);
lean_dec_ref(v_attr_2211_);
v_asyncMode_2224_ = lean_ctor_get(v_toEnvExtension_2222_, 2);
lean_inc(v_asyncMode_2224_);
lean_dec_ref(v_toEnvExtension_2222_);
lean_inc(v_decl_2213_);
lean_inc_ref(v_env_2212_);
v___x_2225_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2212_, v_decl_2213_, v_asyncMode_2224_);
lean_dec(v_asyncMode_2224_);
if (v___x_2225_ == 0)
{
lean_object* v_toAttributeImplCore_2226_; lean_object* v_name_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
lean_dec_ref(v___f_2219_);
lean_dec(v_modifyEnv_2218_);
v_toAttributeImplCore_2226_ = lean_ctor_get(v_attr_2223_, 0);
lean_inc_ref(v_toAttributeImplCore_2226_);
lean_dec_ref(v_attr_2223_);
v_name_2227_ = lean_ctor_get(v_toAttributeImplCore_2226_, 1);
lean_inc(v_name_2227_);
lean_dec_ref(v_toAttributeImplCore_2226_);
v___x_2228_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2212_);
v___x_2229_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_2214_, v_inst_2215_, v_name_2227_, v_decl_2213_, v___x_2228_);
v___x_2230_ = lean_apply_4(v_toBind_2216_, lean_box(0), lean_box(0), v___x_2229_, v___f_2217_);
return v___x_2230_;
}
else
{
lean_object* v___x_2231_; 
lean_dec_ref(v_attr_2223_);
lean_dec(v___f_2217_);
lean_dec(v_toBind_2216_);
lean_dec_ref(v_inst_2215_);
lean_dec_ref(v_inst_2214_);
lean_dec(v_decl_2213_);
lean_dec_ref(v_env_2212_);
v___x_2231_ = lean_apply_1(v_modifyEnv_2218_, v___f_2219_);
return v___x_2231_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__3(lean_object* v___f_2232_, lean_object* v_____r_2233_){
_start:
{
lean_object* v___x_2234_; 
v___x_2234_ = lean_apply_1(v___f_2232_, v_____r_2233_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__4(lean_object* v_attr_2235_, lean_object* v_decl_2236_, lean_object* v_inst_2237_, lean_object* v_inst_2238_, lean_object* v_toBind_2239_, lean_object* v___f_2240_, lean_object* v_modifyEnv_2241_, lean_object* v___f_2242_, lean_object* v_env_2243_){
_start:
{
lean_object* v___f_2244_; lean_object* v___x_2245_; 
lean_inc_ref(v___f_2242_);
lean_inc(v_modifyEnv_2241_);
lean_inc(v___f_2240_);
lean_inc(v_toBind_2239_);
lean_inc_ref(v_inst_2238_);
lean_inc_ref(v_inst_2237_);
lean_inc(v_decl_2236_);
lean_inc_ref(v_env_2243_);
lean_inc_ref(v_attr_2235_);
v___f_2244_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__2), 10, 9);
lean_closure_set(v___f_2244_, 0, v_attr_2235_);
lean_closure_set(v___f_2244_, 1, v_env_2243_);
lean_closure_set(v___f_2244_, 2, v_decl_2236_);
lean_closure_set(v___f_2244_, 3, v_inst_2237_);
lean_closure_set(v___f_2244_, 4, v_inst_2238_);
lean_closure_set(v___f_2244_, 5, v_toBind_2239_);
lean_closure_set(v___f_2244_, 6, v___f_2240_);
lean_closure_set(v___f_2244_, 7, v_modifyEnv_2241_);
lean_closure_set(v___f_2244_, 8, v___f_2242_);
v___x_2245_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2243_, v_decl_2236_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_object* v___x_2246_; lean_object* v___x_2247_; 
lean_dec_ref(v___f_2244_);
v___x_2246_ = lean_box(0);
v___x_2247_ = l_Lean_TagAttribute_setTag___redArg___lam__2(v_attr_2235_, v_env_2243_, v_decl_2236_, v_inst_2237_, v_inst_2238_, v_toBind_2239_, v___f_2240_, v_modifyEnv_2241_, v___f_2242_, v___x_2246_);
return v___x_2247_;
}
else
{
lean_object* v_attr_2248_; lean_object* v_toAttributeImplCore_2249_; lean_object* v_name_2250_; lean_object* v___f_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
lean_dec_ref_known(v___x_2245_, 1);
lean_dec_ref(v_env_2243_);
lean_dec_ref(v___f_2242_);
lean_dec(v_modifyEnv_2241_);
lean_dec(v___f_2240_);
v_attr_2248_ = lean_ctor_get(v_attr_2235_, 0);
lean_inc_ref(v_attr_2248_);
lean_dec_ref(v_attr_2235_);
v_toAttributeImplCore_2249_ = lean_ctor_get(v_attr_2248_, 0);
lean_inc_ref(v_toAttributeImplCore_2249_);
lean_dec_ref(v_attr_2248_);
v_name_2250_ = lean_ctor_get(v_toAttributeImplCore_2249_, 1);
lean_inc(v_name_2250_);
lean_dec_ref(v_toAttributeImplCore_2249_);
v___f_2251_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2251_, 0, v___f_2244_);
v___x_2252_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_2237_, v_inst_2238_, v_name_2250_, v_decl_2236_);
v___x_2253_ = lean_apply_4(v_toBind_2239_, lean_box(0), lean_box(0), v___x_2252_, v___f_2251_);
return v___x_2253_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg(lean_object* v_inst_2254_, lean_object* v_inst_2255_, lean_object* v_inst_2256_, lean_object* v_attr_2257_, lean_object* v_decl_2258_){
_start:
{
lean_object* v_toBind_2259_; lean_object* v_getEnv_2260_; lean_object* v_modifyEnv_2261_; lean_object* v___f_2262_; lean_object* v___f_2263_; lean_object* v___f_2264_; lean_object* v___x_2265_; 
v_toBind_2259_ = lean_ctor_get(v_inst_2254_, 1);
lean_inc_n(v_toBind_2259_, 2);
v_getEnv_2260_ = lean_ctor_get(v_inst_2256_, 0);
lean_inc(v_getEnv_2260_);
v_modifyEnv_2261_ = lean_ctor_get(v_inst_2256_, 1);
lean_inc_n(v_modifyEnv_2261_, 2);
lean_dec_ref(v_inst_2256_);
lean_inc(v_decl_2258_);
lean_inc_ref(v_attr_2257_);
v___f_2262_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2262_, 0, v_attr_2257_);
lean_closure_set(v___f_2262_, 1, v_decl_2258_);
lean_inc_ref(v___f_2262_);
v___f_2263_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2263_, 0, v_modifyEnv_2261_);
lean_closure_set(v___f_2263_, 1, v___f_2262_);
v___f_2264_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__4), 9, 8);
lean_closure_set(v___f_2264_, 0, v_attr_2257_);
lean_closure_set(v___f_2264_, 1, v_decl_2258_);
lean_closure_set(v___f_2264_, 2, v_inst_2254_);
lean_closure_set(v___f_2264_, 3, v_inst_2255_);
lean_closure_set(v___f_2264_, 4, v_toBind_2259_);
lean_closure_set(v___f_2264_, 5, v___f_2263_);
lean_closure_set(v___f_2264_, 6, v_modifyEnv_2261_);
lean_closure_set(v___f_2264_, 7, v___f_2262_);
v___x_2265_ = lean_apply_4(v_toBind_2259_, lean_box(0), lean_box(0), v_getEnv_2260_, v___f_2264_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag(lean_object* v_m_2266_, lean_object* v_inst_2267_, lean_object* v_inst_2268_, lean_object* v_inst_2269_, lean_object* v_attr_2270_, lean_object* v_decl_2271_){
_start:
{
lean_object* v___x_2272_; 
v___x_2272_ = l_Lean_TagAttribute_setTag___redArg(v_inst_2267_, v_inst_2268_, v_inst_2269_, v_attr_2270_, v_decl_2271_);
return v___x_2272_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(lean_object* v___y_2273_, lean_object* v_as_2274_, lean_object* v_k_2275_, lean_object* v_x_2276_, lean_object* v_x_2277_){
_start:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v_m_2280_; lean_object* v_a_2281_; uint8_t v___x_2282_; 
v___x_2278_ = lean_nat_add(v_x_2276_, v_x_2277_);
v___x_2279_ = lean_unsigned_to_nat(1u);
v_m_2280_ = lean_nat_shiftr(v___x_2278_, v___x_2279_);
lean_dec(v___x_2278_);
v_a_2281_ = lean_array_fget_borrowed(v_as_2274_, v_m_2280_);
v___x_2282_ = l_Lean_Name_quickLt(v_a_2281_, v_k_2275_);
if (v___x_2282_ == 0)
{
lean_object* v___x_2283_; uint8_t v___x_2284_; 
lean_dec(v_x_2277_);
v___x_2283_ = lean_unsigned_to_nat(0u);
v___x_2284_ = l_Lean_Name_quickLt(v_k_2275_, v_a_2281_);
if (v___x_2284_ == 0)
{
uint8_t v___x_2285_; 
lean_dec(v_m_2280_);
lean_dec(v_x_2276_);
v___x_2285_ = lean_nat_dec_le(v___x_2283_, v___y_2273_);
return v___x_2285_;
}
else
{
uint8_t v___x_2286_; lean_object* v___x_2287_; uint8_t v___y_2289_; 
v___x_2286_ = lean_nat_dec_eq(v_m_2280_, v___x_2283_);
v___x_2287_ = lean_nat_sub(v_m_2280_, v___x_2279_);
lean_dec(v_m_2280_);
if (v___x_2286_ == 0)
{
uint8_t v___x_2291_; 
v___x_2291_ = lean_nat_dec_lt(v___x_2287_, v_x_2276_);
v___y_2289_ = v___x_2291_;
goto v___jp_2288_;
}
else
{
v___y_2289_ = v___x_2286_;
goto v___jp_2288_;
}
v___jp_2288_:
{
if (v___y_2289_ == 0)
{
v_x_2277_ = v___x_2287_;
goto _start;
}
else
{
lean_dec(v___x_2287_);
lean_dec(v_x_2276_);
return v___x_2282_;
}
}
}
}
else
{
lean_object* v___x_2292_; uint8_t v___x_2293_; 
lean_dec(v_x_2276_);
v___x_2292_ = lean_nat_add(v_m_2280_, v___x_2279_);
lean_dec(v_m_2280_);
v___x_2293_ = lean_nat_dec_le(v___x_2292_, v_x_2277_);
if (v___x_2293_ == 0)
{
lean_dec(v___x_2292_);
lean_dec(v_x_2277_);
return v___x_2293_;
}
else
{
v_x_2276_ = v___x_2292_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg___boxed(lean_object* v___y_2295_, lean_object* v_as_2296_, lean_object* v_k_2297_, lean_object* v_x_2298_, lean_object* v_x_2299_){
_start:
{
uint8_t v_res_2300_; lean_object* v_r_2301_; 
v_res_2300_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___y_2295_, v_as_2296_, v_k_2297_, v_x_2298_, v_x_2299_);
lean_dec(v_k_2297_);
lean_dec_ref(v_as_2296_);
lean_dec(v___y_2295_);
v_r_2301_ = lean_box(v_res_2300_);
return v_r_2301_;
}
}
LEAN_EXPORT uint8_t l_Lean_TagAttribute_hasTag(lean_object* v_attr_2302_, lean_object* v_env_2303_, lean_object* v_decl_2304_){
_start:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2305_ = lean_box(1);
v___x_2306_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2303_, v_decl_2304_);
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v_ext_2307_; lean_object* v_toEnvExtension_2308_; lean_object* v_asyncMode_2309_; lean_object* v___x_2310_; uint8_t v___x_2311_; 
v_ext_2307_ = lean_ctor_get(v_attr_2302_, 1);
v_toEnvExtension_2308_ = lean_ctor_get(v_ext_2307_, 0);
v_asyncMode_2309_ = lean_ctor_get(v_toEnvExtension_2308_, 2);
lean_inc(v_decl_2304_);
v___x_2310_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2305_, v_ext_2307_, v_env_2303_, v_asyncMode_2309_, v_decl_2304_);
v___x_2311_ = l_Lean_NameSet_contains(v___x_2310_, v_decl_2304_);
lean_dec(v_decl_2304_);
lean_dec(v___x_2310_);
return v___x_2311_;
}
else
{
lean_object* v_val_2312_; lean_object* v_ext_2313_; uint8_t v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; uint8_t v___x_2318_; 
v_val_2312_ = lean_ctor_get(v___x_2306_, 0);
lean_inc(v_val_2312_);
lean_dec_ref_known(v___x_2306_, 1);
v_ext_2313_ = lean_ctor_get(v_attr_2302_, 1);
v___x_2314_ = 0;
v___x_2315_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2305_, v_ext_2313_, v_env_2303_, v_val_2312_, v___x_2314_);
lean_dec(v_val_2312_);
lean_dec_ref(v_env_2303_);
v___x_2316_ = lean_unsigned_to_nat(0u);
v___x_2317_ = lean_array_get_size(v___x_2315_);
v___x_2318_ = lean_nat_dec_lt(v___x_2316_, v___x_2317_);
if (v___x_2318_ == 0)
{
lean_dec_ref(v___x_2315_);
lean_dec(v_decl_2304_);
return v___x_2318_;
}
else
{
lean_object* v___x_2319_; lean_object* v___x_2320_; uint8_t v___x_2321_; 
v___x_2319_ = lean_unsigned_to_nat(1u);
v___x_2320_ = lean_nat_sub(v___x_2317_, v___x_2319_);
v___x_2321_ = lean_nat_dec_le(v___x_2316_, v___x_2320_);
if (v___x_2321_ == 0)
{
lean_dec(v___x_2320_);
lean_dec_ref(v___x_2315_);
lean_dec(v_decl_2304_);
return v___x_2321_;
}
else
{
uint8_t v___x_2322_; 
lean_inc(v___x_2320_);
v___x_2322_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___x_2320_, v___x_2315_, v_decl_2304_, v___x_2316_, v___x_2320_);
lean_dec(v_decl_2304_);
lean_dec_ref(v___x_2315_);
lean_dec(v___x_2320_);
return v___x_2322_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_hasTag___boxed(lean_object* v_attr_2323_, lean_object* v_env_2324_, lean_object* v_decl_2325_){
_start:
{
uint8_t v_res_2326_; lean_object* v_r_2327_; 
v_res_2326_ = l_Lean_TagAttribute_hasTag(v_attr_2323_, v_env_2324_, v_decl_2325_);
lean_dec_ref(v_attr_2323_);
v_r_2327_ = lean_box(v_res_2326_);
return v_r_2327_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(lean_object* v___y_2328_, lean_object* v_as_2329_, lean_object* v_k_2330_, lean_object* v_x_2331_, lean_object* v_x_2332_, lean_object* v_x_2333_){
_start:
{
uint8_t v___x_2334_; 
v___x_2334_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___y_2328_, v_as_2329_, v_k_2330_, v_x_2331_, v_x_2332_);
return v___x_2334_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___boxed(lean_object* v___y_2335_, lean_object* v_as_2336_, lean_object* v_k_2337_, lean_object* v_x_2338_, lean_object* v_x_2339_, lean_object* v_x_2340_){
_start:
{
uint8_t v_res_2341_; lean_object* v_r_2342_; 
v_res_2341_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(v___y_2335_, v_as_2336_, v_k_2337_, v_x_2338_, v_x_2339_, v_x_2340_);
lean_dec(v_k_2337_);
lean_dec_ref(v_as_2336_);
lean_dec(v___y_2335_);
v_r_2342_ = lean_box(v_res_2341_);
return v_r_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0(lean_object* v_x_2343_, lean_object* v___y_2344_){
_start:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2346_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2346_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0___boxed(lean_object* v_x_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_){
_start:
{
lean_object* v_res_2351_; 
v_res_2351_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0(v_x_2348_, v___y_2349_);
lean_dec_ref(v___y_2349_);
lean_dec_ref(v_x_2348_);
return v_res_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1(lean_object* v_s_2352_, lean_object* v_x_2353_){
_start:
{
lean_inc_ref(v_s_2352_);
return v_s_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1___boxed(lean_object* v_s_2354_, lean_object* v_x_2355_){
_start:
{
lean_object* v_res_2356_; 
v_res_2356_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1(v_s_2354_, v_x_2355_);
lean_dec_ref(v_x_2355_);
lean_dec_ref(v_s_2354_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2(lean_object* v_x_2361_, lean_object* v_x_2362_){
_start:
{
lean_object* v___x_2363_; 
v___x_2363_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__1));
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___boxed(lean_object* v_x_2364_, lean_object* v_x_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2(v_x_2364_, v_x_2365_);
lean_dec_ref(v_x_2365_);
lean_dec_ref(v_x_2364_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3(lean_object* v_x_2367_){
_start:
{
lean_object* v___x_2368_; 
v___x_2368_ = lean_box(0);
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3___boxed(lean_object* v_x_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3(v_x_2369_);
lean_dec_ref(v_x_2369_);
return v_res_2370_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4(void){
_start:
{
lean_object* v___f_2375_; lean_object* v___f_2376_; lean_object* v___f_2377_; lean_object* v___f_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___f_2375_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__3));
v___f_2376_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__2));
v___f_2377_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__1));
v___f_2378_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__0));
v___x_2379_ = lean_box(0);
v___x_2380_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_2381_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2380_);
lean_ctor_set(v___x_2381_, 1, v___x_2379_);
lean_ctor_set(v___x_2381_, 2, v___f_2378_);
lean_ctor_set(v___x_2381_, 3, v___f_2377_);
lean_ctor_set(v___x_2381_, 4, v___f_2376_);
lean_ctor_set(v___x_2381_, 5, v___f_2375_);
return v___x_2381_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5(void){
_start:
{
uint8_t v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2382_ = 0;
v___x_2383_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4, &l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4_once, _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4);
v___x_2384_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_2385_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2385_, 0, v___x_2384_);
lean_ctor_set(v___x_2385_, 1, v___x_2383_);
lean_ctor_set_uint8(v___x_2385_, sizeof(void*)*2, v___x_2382_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg(){
_start:
{
lean_object* v___x_2387_; 
v___x_2387_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5, &l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5_once, _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5);
return v___x_2387_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___boxed(lean_object* v___dummy_2388_){
_start:
{
lean_object* v_res_2389_; 
v_res_2389_ = l_Lean_instInhabitedParametricAttribute_default___redArg();
return v_res_2389_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__0(void){
_start:
{
lean_object* v___x_2390_; 
v___x_2390_ = l_Lean_instInhabitedParametricAttribute_default___redArg();
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default(lean_object* v_00_u03b1_2391_){
_start:
{
lean_object* v___x_2392_; 
v___x_2392_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__0, &l_Lean_instInhabitedParametricAttribute_default___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__0);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute___redArg(){
_start:
{
lean_object* v___x_2394_; 
v___x_2394_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__0, &l_Lean_instInhabitedParametricAttribute_default___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__0);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute___redArg___boxed(lean_object* v___dummy_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l_Lean_instInhabitedParametricAttribute___redArg();
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute(lean_object* v_a_2397_){
_start:
{
lean_object* v___x_2398_; 
v___x_2398_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__0, &l_Lean_instInhabitedParametricAttribute_default___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__0);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__0(lean_object* v_x_2399_, lean_object* v_p_2400_){
_start:
{
lean_object* v_fst_2401_; lean_object* v_snd_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2419_; 
v_fst_2401_ = lean_ctor_get(v_x_2399_, 0);
v_snd_2402_ = lean_ctor_get(v_x_2399_, 1);
v_isSharedCheck_2419_ = !lean_is_exclusive(v_x_2399_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2404_ = v_x_2399_;
v_isShared_2405_ = v_isSharedCheck_2419_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_snd_2402_);
lean_inc(v_fst_2401_);
lean_dec(v_x_2399_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2419_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v_fst_2406_; lean_object* v_snd_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2418_; 
v_fst_2406_ = lean_ctor_get(v_p_2400_, 0);
v_snd_2407_ = lean_ctor_get(v_p_2400_, 1);
v_isSharedCheck_2418_ = !lean_is_exclusive(v_p_2400_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2409_ = v_p_2400_;
v_isShared_2410_ = v_isSharedCheck_2418_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_snd_2407_);
lean_inc(v_fst_2406_);
lean_dec(v_p_2400_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2418_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2412_; 
lean_inc(v_fst_2406_);
if (v_isShared_2405_ == 0)
{
lean_ctor_set_tag(v___x_2404_, 1);
lean_ctor_set(v___x_2404_, 1, v_fst_2401_);
lean_ctor_set(v___x_2404_, 0, v_fst_2406_);
v___x_2412_ = v___x_2404_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_fst_2406_);
lean_ctor_set(v_reuseFailAlloc_2417_, 1, v_fst_2401_);
v___x_2412_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
lean_object* v___x_2413_; lean_object* v___x_2415_; 
v___x_2413_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2406_, v_snd_2407_, v_snd_2402_);
if (v_isShared_2410_ == 0)
{
lean_ctor_set(v___x_2409_, 1, v___x_2413_);
lean_ctor_set(v___x_2409_, 0, v___x_2412_);
v___x_2415_ = v___x_2409_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v___x_2412_);
lean_ctor_set(v_reuseFailAlloc_2416_, 1, v___x_2413_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(lean_object* v_init_2420_, lean_object* v_x_2421_){
_start:
{
if (lean_obj_tag(v_x_2421_) == 0)
{
lean_object* v_k_2422_; lean_object* v_v_2423_; lean_object* v_l_2424_; lean_object* v_r_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
v_k_2422_ = lean_ctor_get(v_x_2421_, 1);
v_v_2423_ = lean_ctor_get(v_x_2421_, 2);
v_l_2424_ = lean_ctor_get(v_x_2421_, 3);
v_r_2425_ = lean_ctor_get(v_x_2421_, 4);
v___x_2426_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2420_, v_l_2424_);
lean_inc(v_v_2423_);
lean_inc(v_k_2422_);
v___x_2427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2427_, 0, v_k_2422_);
lean_ctor_set(v___x_2427_, 1, v_v_2423_);
v___x_2428_ = lean_array_push(v___x_2426_, v___x_2427_);
v_init_2420_ = v___x_2428_;
v_x_2421_ = v_r_2425_;
goto _start;
}
else
{
return v_init_2420_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg___boxed(lean_object* v_init_2430_, lean_object* v_x_2431_){
_start:
{
lean_object* v_res_2432_; 
v_res_2432_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2430_, v_x_2431_);
lean_dec(v_x_2431_);
return v_res_2432_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(lean_object* v_snd_2433_, lean_object* v_as_2434_, size_t v_i_2435_, size_t v_stop_2436_, lean_object* v_b_2437_){
_start:
{
lean_object* v___y_2439_; uint8_t v___x_2443_; 
v___x_2443_ = lean_usize_dec_eq(v_i_2435_, v_stop_2436_);
if (v___x_2443_ == 0)
{
lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2444_ = lean_array_uget_borrowed(v_as_2434_, v_i_2435_);
v___x_2445_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_2433_, v___x_2444_);
if (lean_obj_tag(v___x_2445_) == 0)
{
v___y_2439_ = v_b_2437_;
goto v___jp_2438_;
}
else
{
lean_object* v_val_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
v_val_2446_ = lean_ctor_get(v___x_2445_, 0);
lean_inc(v_val_2446_);
lean_dec_ref_known(v___x_2445_, 1);
lean_inc(v___x_2444_);
v___x_2447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2447_, 0, v___x_2444_);
lean_ctor_set(v___x_2447_, 1, v_val_2446_);
v___x_2448_ = lean_array_push(v_b_2437_, v___x_2447_);
v___y_2439_ = v___x_2448_;
goto v___jp_2438_;
}
}
else
{
return v_b_2437_;
}
v___jp_2438_:
{
size_t v___x_2440_; size_t v___x_2441_; 
v___x_2440_ = ((size_t)1ULL);
v___x_2441_ = lean_usize_add(v_i_2435_, v___x_2440_);
v_i_2435_ = v___x_2441_;
v_b_2437_ = v___y_2439_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg___boxed(lean_object* v_snd_2449_, lean_object* v_as_2450_, lean_object* v_i_2451_, lean_object* v_stop_2452_, lean_object* v_b_2453_){
_start:
{
size_t v_i_boxed_2454_; size_t v_stop_boxed_2455_; lean_object* v_res_2456_; 
v_i_boxed_2454_ = lean_unbox_usize(v_i_2451_);
lean_dec(v_i_2451_);
v_stop_boxed_2455_ = lean_unbox_usize(v_stop_2452_);
lean_dec(v_stop_2452_);
v_res_2456_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2449_, v_as_2450_, v_i_boxed_2454_, v_stop_boxed_2455_, v_b_2453_);
lean_dec_ref(v_as_2450_);
lean_dec(v_snd_2449_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(lean_object* v_snd_2457_, lean_object* v_as_2458_, lean_object* v_start_2459_, lean_object* v_stop_2460_){
_start:
{
lean_object* v___x_2461_; uint8_t v___x_2462_; 
v___x_2461_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v___x_2462_ = lean_nat_dec_lt(v_start_2459_, v_stop_2460_);
if (v___x_2462_ == 0)
{
return v___x_2461_;
}
else
{
lean_object* v___x_2463_; uint8_t v___x_2464_; 
v___x_2463_ = lean_array_get_size(v_as_2458_);
v___x_2464_ = lean_nat_dec_le(v_stop_2460_, v___x_2463_);
if (v___x_2464_ == 0)
{
uint8_t v___x_2465_; 
v___x_2465_ = lean_nat_dec_lt(v_start_2459_, v___x_2463_);
if (v___x_2465_ == 0)
{
return v___x_2461_;
}
else
{
size_t v___x_2466_; size_t v___x_2467_; lean_object* v___x_2468_; 
v___x_2466_ = lean_usize_of_nat(v_start_2459_);
v___x_2467_ = lean_usize_of_nat(v___x_2463_);
v___x_2468_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2457_, v_as_2458_, v___x_2466_, v___x_2467_, v___x_2461_);
return v___x_2468_;
}
}
else
{
size_t v___x_2469_; size_t v___x_2470_; lean_object* v___x_2471_; 
v___x_2469_ = lean_usize_of_nat(v_start_2459_);
v___x_2470_ = lean_usize_of_nat(v_stop_2460_);
v___x_2471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2457_, v_as_2458_, v___x_2469_, v___x_2470_, v___x_2461_);
return v___x_2471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg___boxed(lean_object* v_snd_2472_, lean_object* v_as_2473_, lean_object* v_start_2474_, lean_object* v_stop_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2472_, v_as_2473_, v_start_2474_, v_stop_2475_);
lean_dec(v_stop_2475_);
lean_dec(v_start_2474_);
lean_dec_ref(v_as_2473_);
lean_dec(v_snd_2472_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(lean_object* v_hi_2477_, lean_object* v_pivot_2478_, lean_object* v_as_2479_, lean_object* v_i_2480_, lean_object* v_k_2481_){
_start:
{
uint8_t v___x_2482_; 
v___x_2482_ = lean_nat_dec_lt(v_k_2481_, v_hi_2477_);
if (v___x_2482_ == 0)
{
lean_object* v___x_2483_; lean_object* v___x_2484_; 
lean_dec(v_k_2481_);
v___x_2483_ = lean_array_fswap(v_as_2479_, v_i_2480_, v_hi_2477_);
v___x_2484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2484_, 0, v_i_2480_);
lean_ctor_set(v___x_2484_, 1, v___x_2483_);
return v___x_2484_;
}
else
{
lean_object* v___x_2485_; lean_object* v_fst_2486_; lean_object* v_fst_2487_; uint8_t v___x_2488_; 
v___x_2485_ = lean_array_fget_borrowed(v_as_2479_, v_k_2481_);
v_fst_2486_ = lean_ctor_get(v___x_2485_, 0);
v_fst_2487_ = lean_ctor_get(v_pivot_2478_, 0);
v___x_2488_ = l_Lean_Name_quickLt(v_fst_2486_, v_fst_2487_);
if (v___x_2488_ == 0)
{
lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2489_ = lean_unsigned_to_nat(1u);
v___x_2490_ = lean_nat_add(v_k_2481_, v___x_2489_);
lean_dec(v_k_2481_);
v_k_2481_ = v___x_2490_;
goto _start;
}
else
{
lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2492_ = lean_array_fswap(v_as_2479_, v_i_2480_, v_k_2481_);
v___x_2493_ = lean_unsigned_to_nat(1u);
v___x_2494_ = lean_nat_add(v_i_2480_, v___x_2493_);
lean_dec(v_i_2480_);
v___x_2495_ = lean_nat_add(v_k_2481_, v___x_2493_);
lean_dec(v_k_2481_);
v_as_2479_ = v___x_2492_;
v_i_2480_ = v___x_2494_;
v_k_2481_ = v___x_2495_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg___boxed(lean_object* v_hi_2497_, lean_object* v_pivot_2498_, lean_object* v_as_2499_, lean_object* v_i_2500_, lean_object* v_k_2501_){
_start:
{
lean_object* v_res_2502_; 
v_res_2502_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2497_, v_pivot_2498_, v_as_2499_, v_i_2500_, v_k_2501_);
lean_dec_ref(v_pivot_2498_);
lean_dec(v_hi_2497_);
return v_res_2502_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(lean_object* v_a_2503_, lean_object* v_b_2504_){
_start:
{
lean_object* v_fst_2505_; lean_object* v_fst_2506_; uint8_t v___x_2507_; 
v_fst_2505_ = lean_ctor_get(v_a_2503_, 0);
v_fst_2506_ = lean_ctor_get(v_b_2504_, 0);
v___x_2507_ = l_Lean_Name_quickLt(v_fst_2505_, v_fst_2506_);
return v___x_2507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0___boxed(lean_object* v_a_2508_, lean_object* v_b_2509_){
_start:
{
uint8_t v_res_2510_; lean_object* v_r_2511_; 
v_res_2510_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v_a_2508_, v_b_2509_);
lean_dec_ref(v_b_2509_);
lean_dec_ref(v_a_2508_);
v_r_2511_ = lean_box(v_res_2510_);
return v_r_2511_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(lean_object* v_n_2512_, lean_object* v_as_2513_, lean_object* v_lo_2514_, lean_object* v_hi_2515_){
_start:
{
lean_object* v___y_2517_; uint8_t v___x_2527_; 
v___x_2527_ = lean_nat_dec_lt(v_lo_2514_, v_hi_2515_);
if (v___x_2527_ == 0)
{
lean_dec(v_lo_2514_);
return v_as_2513_;
}
else
{
lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v_mid_2530_; lean_object* v___y_2532_; lean_object* v___y_2538_; lean_object* v___x_2543_; lean_object* v___x_2544_; uint8_t v___x_2545_; 
v___x_2528_ = lean_nat_add(v_lo_2514_, v_hi_2515_);
v___x_2529_ = lean_unsigned_to_nat(1u);
v_mid_2530_ = lean_nat_shiftr(v___x_2528_, v___x_2529_);
lean_dec(v___x_2528_);
v___x_2543_ = lean_array_fget_borrowed(v_as_2513_, v_mid_2530_);
v___x_2544_ = lean_array_fget_borrowed(v_as_2513_, v_lo_2514_);
v___x_2545_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2543_, v___x_2544_);
if (v___x_2545_ == 0)
{
v___y_2538_ = v_as_2513_;
goto v___jp_2537_;
}
else
{
lean_object* v___x_2546_; 
v___x_2546_ = lean_array_fswap(v_as_2513_, v_lo_2514_, v_mid_2530_);
v___y_2538_ = v___x_2546_;
goto v___jp_2537_;
}
v___jp_2531_:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; uint8_t v___x_2535_; 
v___x_2533_ = lean_array_fget_borrowed(v___y_2532_, v_mid_2530_);
v___x_2534_ = lean_array_fget_borrowed(v___y_2532_, v_hi_2515_);
v___x_2535_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2533_, v___x_2534_);
if (v___x_2535_ == 0)
{
lean_dec(v_mid_2530_);
v___y_2517_ = v___y_2532_;
goto v___jp_2516_;
}
else
{
lean_object* v___x_2536_; 
v___x_2536_ = lean_array_fswap(v___y_2532_, v_mid_2530_, v_hi_2515_);
lean_dec(v_mid_2530_);
v___y_2517_ = v___x_2536_;
goto v___jp_2516_;
}
}
v___jp_2537_:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; uint8_t v___x_2541_; 
v___x_2539_ = lean_array_fget_borrowed(v___y_2538_, v_hi_2515_);
v___x_2540_ = lean_array_fget_borrowed(v___y_2538_, v_lo_2514_);
v___x_2541_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2539_, v___x_2540_);
if (v___x_2541_ == 0)
{
v___y_2532_ = v___y_2538_;
goto v___jp_2531_;
}
else
{
lean_object* v___x_2542_; 
v___x_2542_ = lean_array_fswap(v___y_2538_, v_lo_2514_, v_hi_2515_);
v___y_2532_ = v___x_2542_;
goto v___jp_2531_;
}
}
}
v___jp_2516_:
{
lean_object* v_pivot_2518_; lean_object* v___x_2519_; lean_object* v_fst_2520_; lean_object* v_snd_2521_; uint8_t v___x_2522_; 
v_pivot_2518_ = lean_array_fget(v___y_2517_, v_hi_2515_);
lean_inc_n(v_lo_2514_, 2);
v___x_2519_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2515_, v_pivot_2518_, v___y_2517_, v_lo_2514_, v_lo_2514_);
lean_dec(v_pivot_2518_);
v_fst_2520_ = lean_ctor_get(v___x_2519_, 0);
lean_inc(v_fst_2520_);
v_snd_2521_ = lean_ctor_get(v___x_2519_, 1);
lean_inc(v_snd_2521_);
lean_dec_ref(v___x_2519_);
v___x_2522_ = lean_nat_dec_le(v_hi_2515_, v_fst_2520_);
if (v___x_2522_ == 0)
{
lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2523_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2512_, v_snd_2521_, v_lo_2514_, v_fst_2520_);
v___x_2524_ = lean_unsigned_to_nat(1u);
v___x_2525_ = lean_nat_add(v_fst_2520_, v___x_2524_);
lean_dec(v_fst_2520_);
v_as_2513_ = v___x_2523_;
v_lo_2514_ = v___x_2525_;
goto _start;
}
else
{
lean_dec(v_fst_2520_);
lean_dec(v_lo_2514_);
return v_snd_2521_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___boxed(lean_object* v_n_2547_, lean_object* v_as_2548_, lean_object* v_lo_2549_, lean_object* v_hi_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2547_, v_as_2548_, v_lo_2549_, v_hi_2550_);
lean_dec(v_hi_2550_);
lean_dec(v_n_2547_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(lean_object* v_filterExport_2552_, lean_object* v_env_2553_, lean_object* v_as_2554_, size_t v_i_2555_, size_t v_stop_2556_, lean_object* v_b_2557_){
_start:
{
lean_object* v___y_2559_; uint8_t v___x_2563_; 
v___x_2563_ = lean_usize_dec_eq(v_i_2555_, v_stop_2556_);
if (v___x_2563_ == 0)
{
lean_object* v___x_2564_; lean_object* v_fst_2565_; lean_object* v_snd_2566_; lean_object* v___x_2567_; uint8_t v___x_2568_; 
v___x_2564_ = lean_array_uget_borrowed(v_as_2554_, v_i_2555_);
v_fst_2565_ = lean_ctor_get(v___x_2564_, 0);
v_snd_2566_ = lean_ctor_get(v___x_2564_, 1);
lean_inc_ref(v_filterExport_2552_);
lean_inc(v_snd_2566_);
lean_inc(v_fst_2565_);
lean_inc_ref(v_env_2553_);
v___x_2567_ = lean_apply_3(v_filterExport_2552_, v_env_2553_, v_fst_2565_, v_snd_2566_);
v___x_2568_ = lean_unbox(v___x_2567_);
if (v___x_2568_ == 0)
{
v___y_2559_ = v_b_2557_;
goto v___jp_2558_;
}
else
{
lean_object* v___x_2569_; 
lean_inc(v___x_2564_);
v___x_2569_ = lean_array_push(v_b_2557_, v___x_2564_);
v___y_2559_ = v___x_2569_;
goto v___jp_2558_;
}
}
else
{
lean_dec_ref(v_env_2553_);
lean_dec_ref(v_filterExport_2552_);
return v_b_2557_;
}
v___jp_2558_:
{
size_t v___x_2560_; size_t v___x_2561_; 
v___x_2560_ = ((size_t)1ULL);
v___x_2561_ = lean_usize_add(v_i_2555_, v___x_2560_);
v_i_2555_ = v___x_2561_;
v_b_2557_ = v___y_2559_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg___boxed(lean_object* v_filterExport_2570_, lean_object* v_env_2571_, lean_object* v_as_2572_, lean_object* v_i_2573_, lean_object* v_stop_2574_, lean_object* v_b_2575_){
_start:
{
size_t v_i_boxed_2576_; size_t v_stop_boxed_2577_; lean_object* v_res_2578_; 
v_i_boxed_2576_ = lean_unbox_usize(v_i_2573_);
lean_dec(v_i_2573_);
v_stop_boxed_2577_ = lean_unbox_usize(v_stop_2574_);
lean_dec(v_stop_2574_);
v_res_2578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2570_, v_env_2571_, v_as_2572_, v_i_boxed_2576_, v_stop_boxed_2577_, v_b_2575_);
lean_dec_ref(v_as_2572_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1(lean_object* v_filterExport_2579_, uint8_t v_preserveOrder_2580_, lean_object* v_env_2581_, lean_object* v_x_2582_){
_start:
{
lean_object* v___y_2584_; 
if (v_preserveOrder_2580_ == 0)
{
lean_object* v_snd_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v_r_2603_; lean_object* v___x_2604_; lean_object* v___y_2606_; lean_object* v___y_2607_; uint8_t v___x_2609_; 
v_snd_2600_ = lean_ctor_get(v_x_2582_, 1);
lean_inc(v_snd_2600_);
lean_dec_ref(v_x_2582_);
v___x_2601_ = lean_unsigned_to_nat(0u);
v___x_2602_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v_r_2603_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v___x_2602_, v_snd_2600_);
lean_dec(v_snd_2600_);
v___x_2604_ = lean_array_get_size(v_r_2603_);
v___x_2609_ = lean_nat_dec_eq(v___x_2604_, v___x_2601_);
if (v___x_2609_ == 0)
{
lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___y_2613_; uint8_t v___x_2615_; 
v___x_2610_ = lean_unsigned_to_nat(1u);
v___x_2611_ = lean_nat_sub(v___x_2604_, v___x_2610_);
v___x_2615_ = lean_nat_dec_le(v___x_2601_, v___x_2611_);
if (v___x_2615_ == 0)
{
lean_inc(v___x_2611_);
v___y_2613_ = v___x_2611_;
goto v___jp_2612_;
}
else
{
v___y_2613_ = v___x_2601_;
goto v___jp_2612_;
}
v___jp_2612_:
{
uint8_t v___x_2614_; 
v___x_2614_ = lean_nat_dec_le(v___y_2613_, v___x_2611_);
if (v___x_2614_ == 0)
{
lean_dec(v___x_2611_);
lean_inc(v___y_2613_);
v___y_2606_ = v___y_2613_;
v___y_2607_ = v___y_2613_;
goto v___jp_2605_;
}
else
{
v___y_2606_ = v___y_2613_;
v___y_2607_ = v___x_2611_;
goto v___jp_2605_;
}
}
}
else
{
v___y_2584_ = v_r_2603_;
goto v___jp_2583_;
}
v___jp_2605_:
{
lean_object* v___x_2608_; 
v___x_2608_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v___x_2604_, v_r_2603_, v___y_2606_, v___y_2607_);
lean_dec(v___y_2607_);
v___y_2584_ = v___x_2608_;
goto v___jp_2583_;
}
}
else
{
lean_object* v_fst_2616_; lean_object* v_snd_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; 
v_fst_2616_ = lean_ctor_get(v_x_2582_, 0);
lean_inc(v_fst_2616_);
v_snd_2617_ = lean_ctor_get(v_x_2582_, 1);
lean_inc(v_snd_2617_);
lean_dec_ref(v_x_2582_);
v___x_2618_ = lean_array_mk(v_fst_2616_);
v___x_2619_ = l_Array_reverse___redArg(v___x_2618_);
v___x_2620_ = lean_unsigned_to_nat(0u);
v___x_2621_ = lean_array_get_size(v___x_2619_);
v___x_2622_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2617_, v___x_2619_, v___x_2620_, v___x_2621_);
lean_dec_ref(v___x_2619_);
lean_dec(v_snd_2617_);
v___y_2584_ = v___x_2622_;
goto v___jp_2583_;
}
v___jp_2583_:
{
lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; uint8_t v___x_2588_; 
v___x_2585_ = lean_unsigned_to_nat(0u);
v___x_2586_ = lean_array_get_size(v___y_2584_);
v___x_2587_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v___x_2588_ = lean_nat_dec_lt(v___x_2585_, v___x_2586_);
if (v___x_2588_ == 0)
{
lean_object* v___x_2589_; 
lean_dec_ref(v_env_2581_);
lean_dec_ref(v_filterExport_2579_);
v___x_2589_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2589_, 0, v___x_2587_);
lean_ctor_set(v___x_2589_, 1, v___x_2587_);
lean_ctor_set(v___x_2589_, 2, v___y_2584_);
return v___x_2589_;
}
else
{
uint8_t v___x_2590_; 
v___x_2590_ = lean_nat_dec_le(v___x_2586_, v___x_2586_);
if (v___x_2590_ == 0)
{
if (v___x_2588_ == 0)
{
lean_object* v___x_2591_; 
lean_dec_ref(v_env_2581_);
lean_dec_ref(v_filterExport_2579_);
v___x_2591_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2587_);
lean_ctor_set(v___x_2591_, 1, v___x_2587_);
lean_ctor_set(v___x_2591_, 2, v___y_2584_);
return v___x_2591_;
}
else
{
size_t v___x_2592_; size_t v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2592_ = ((size_t)0ULL);
v___x_2593_ = lean_usize_of_nat(v___x_2586_);
v___x_2594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2579_, v_env_2581_, v___y_2584_, v___x_2592_, v___x_2593_, v___x_2587_);
lean_inc_ref(v___x_2594_);
v___x_2595_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2594_);
lean_ctor_set(v___x_2595_, 1, v___x_2594_);
lean_ctor_set(v___x_2595_, 2, v___y_2584_);
return v___x_2595_;
}
}
else
{
size_t v___x_2596_; size_t v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2596_ = ((size_t)0ULL);
v___x_2597_ = lean_usize_of_nat(v___x_2586_);
v___x_2598_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2579_, v_env_2581_, v___y_2584_, v___x_2596_, v___x_2597_, v___x_2587_);
lean_inc_ref(v___x_2598_);
v___x_2599_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2598_);
lean_ctor_set(v___x_2599_, 1, v___x_2598_);
lean_ctor_set(v___x_2599_, 2, v___y_2584_);
return v___x_2599_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed(lean_object* v_filterExport_2623_, lean_object* v_preserveOrder_2624_, lean_object* v_env_2625_, lean_object* v_x_2626_){
_start:
{
uint8_t v_preserveOrder_boxed_2627_; lean_object* v_res_2628_; 
v_preserveOrder_boxed_2627_ = lean_unbox(v_preserveOrder_2624_);
v_res_2628_ = l_Lean_registerParametricAttributeExt___redArg___lam__1(v_filterExport_2623_, v_preserveOrder_boxed_2627_, v_env_2625_, v_x_2626_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__2(lean_object* v_x_2638_){
_start:
{
lean_object* v_snd_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2653_; 
v_snd_2639_ = lean_ctor_get(v_x_2638_, 1);
v_isSharedCheck_2653_ = !lean_is_exclusive(v_x_2638_);
if (v_isSharedCheck_2653_ == 0)
{
lean_object* v_unused_2654_; 
v_unused_2654_ = lean_ctor_get(v_x_2638_, 0);
lean_dec(v_unused_2654_);
v___x_2641_ = v_x_2638_;
v_isShared_2642_ = v_isSharedCheck_2653_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_snd_2639_);
lean_dec(v_x_2638_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2653_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2643_; lean_object* v___y_2645_; 
v___x_2643_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__3));
if (lean_obj_tag(v_snd_2639_) == 0)
{
lean_object* v_size_2651_; 
v_size_2651_ = lean_ctor_get(v_snd_2639_, 0);
lean_inc(v_size_2651_);
lean_dec_ref_known(v_snd_2639_, 5);
v___y_2645_ = v_size_2651_;
goto v___jp_2644_;
}
else
{
lean_object* v___x_2652_; 
v___x_2652_ = lean_unsigned_to_nat(0u);
v___y_2645_ = v___x_2652_;
goto v___jp_2644_;
}
v___jp_2644_:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2649_; 
v___x_2646_ = l_Nat_reprFast(v___y_2645_);
v___x_2647_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2647_, 0, v___x_2646_);
if (v_isShared_2642_ == 0)
{
lean_ctor_set_tag(v___x_2641_, 5);
lean_ctor_set(v___x_2641_, 1, v___x_2647_);
lean_ctor_set(v___x_2641_, 0, v___x_2643_);
v___x_2649_ = v___x_2641_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v___x_2643_);
lean_ctor_set(v_reuseFailAlloc_2650_, 1, v___x_2647_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3(lean_object* v_x_2655_){
_start:
{
lean_object* v___x_2656_; 
v___x_2656_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
return v___x_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3___boxed(lean_object* v_x_2657_){
_start:
{
lean_object* v_res_2658_; 
v_res_2658_ = l_Lean_registerParametricAttributeExt___redArg___lam__3(v_x_2657_);
lean_dec_ref(v_x_2657_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4(lean_object* v___x_2659_){
_start:
{
lean_object* v___x_2661_; 
v___x_2661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2661_, 0, v___x_2659_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4___boxed(lean_object* v___x_2662_, lean_object* v___y_2663_){
_start:
{
lean_object* v_res_2664_; 
v_res_2664_ = l_Lean_registerParametricAttributeExt___redArg___lam__4(v___x_2662_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5(lean_object* v___x_2665_, lean_object* v_x_2666_, lean_object* v___y_2667_){
_start:
{
lean_object* v___x_2669_; 
v___x_2669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2665_);
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5___boxed(lean_object* v___x_2670_, lean_object* v_x_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
lean_object* v_res_2674_; 
v_res_2674_ = l_Lean_registerParametricAttributeExt___redArg___lam__5(v___x_2670_, v_x_2671_, v___y_2672_);
lean_dec_ref(v___y_2672_);
lean_dec_ref(v_x_2671_);
return v_res_2674_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg(lean_object* v_ref_2685_, uint8_t v_preserveOrder_2686_, lean_object* v_filterExport_2687_){
_start:
{
lean_object* v___f_2689_; lean_object* v___x_2690_; lean_object* v___f_2691_; lean_object* v___f_2692_; lean_object* v___f_2693_; lean_object* v___f_2694_; lean_object* v___f_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; uint8_t v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___f_2689_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__0));
v___x_2690_ = lean_box(v_preserveOrder_2686_);
v___f_2691_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2691_, 0, v_filterExport_2687_);
lean_closure_set(v___f_2691_, 1, v___x_2690_);
v___f_2692_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__1));
v___f_2693_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__2));
v___f_2694_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__4));
v___f_2695_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__5));
v___x_2696_ = lean_box(2);
v___x_2697_ = lean_box(0);
v___x_2698_ = 0;
v___x_2699_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_2699_, 0, v_ref_2685_);
lean_ctor_set(v___x_2699_, 1, v___f_2694_);
lean_ctor_set(v___x_2699_, 2, v___f_2695_);
lean_ctor_set(v___x_2699_, 3, v___f_2689_);
lean_ctor_set(v___x_2699_, 4, v___f_2691_);
lean_ctor_set(v___x_2699_, 5, v___f_2692_);
lean_ctor_set(v___x_2699_, 6, v___x_2696_);
lean_ctor_set(v___x_2699_, 7, v___x_2697_);
lean_ctor_set_uint8(v___x_2699_, sizeof(void*)*8, v___x_2698_);
v___x_2700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2699_);
lean_ctor_set(v___x_2700_, 1, v___f_2693_);
v___x_2701_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2700_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___boxed(lean_object* v_ref_2702_, lean_object* v_preserveOrder_2703_, lean_object* v_filterExport_2704_, lean_object* v_a_2705_){
_start:
{
uint8_t v_preserveOrder_boxed_2706_; lean_object* v_res_2707_; 
v_preserveOrder_boxed_2706_ = lean_unbox(v_preserveOrder_2703_);
v_res_2707_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_2702_, v_preserveOrder_boxed_2706_, v_filterExport_2704_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt(lean_object* v_00_u03b1_2708_, lean_object* v_ref_2709_, uint8_t v_preserveOrder_2710_, lean_object* v_filterExport_2711_){
_start:
{
lean_object* v___x_2713_; 
v___x_2713_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_2709_, v_preserveOrder_2710_, v_filterExport_2711_);
return v___x_2713_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___boxed(lean_object* v_00_u03b1_2714_, lean_object* v_ref_2715_, lean_object* v_preserveOrder_2716_, lean_object* v_filterExport_2717_, lean_object* v_a_2718_){
_start:
{
uint8_t v_preserveOrder_boxed_2719_; lean_object* v_res_2720_; 
v_preserveOrder_boxed_2719_ = lean_unbox(v_preserveOrder_2716_);
v_res_2720_ = l_Lean_registerParametricAttributeExt(v_00_u03b1_2714_, v_ref_2715_, v_preserveOrder_boxed_2719_, v_filterExport_2717_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(lean_object* v_00_u03b1_2721_, lean_object* v_filterExport_2722_, lean_object* v_env_2723_, lean_object* v_as_2724_, size_t v_i_2725_, size_t v_stop_2726_, lean_object* v_b_2727_){
_start:
{
lean_object* v___x_2728_; 
v___x_2728_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2722_, v_env_2723_, v_as_2724_, v_i_2725_, v_stop_2726_, v_b_2727_);
return v___x_2728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___boxed(lean_object* v_00_u03b1_2729_, lean_object* v_filterExport_2730_, lean_object* v_env_2731_, lean_object* v_as_2732_, lean_object* v_i_2733_, lean_object* v_stop_2734_, lean_object* v_b_2735_){
_start:
{
size_t v_i_boxed_2736_; size_t v_stop_boxed_2737_; lean_object* v_res_2738_; 
v_i_boxed_2736_ = lean_unbox_usize(v_i_2733_);
lean_dec(v_i_2733_);
v_stop_boxed_2737_ = lean_unbox_usize(v_stop_2734_);
lean_dec(v_stop_2734_);
v_res_2738_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(v_00_u03b1_2729_, v_filterExport_2730_, v_env_2731_, v_as_2732_, v_i_boxed_2736_, v_stop_boxed_2737_, v_b_2735_);
lean_dec_ref(v_as_2732_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(lean_object* v_init_2739_, lean_object* v_t_2740_){
_start:
{
lean_object* v___x_2741_; 
v___x_2741_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2739_, v_t_2740_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg___boxed(lean_object* v_init_2742_, lean_object* v_t_2743_){
_start:
{
lean_object* v_res_2744_; 
v_res_2744_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(v_init_2742_, v_t_2743_);
lean_dec(v_t_2743_);
return v_res_2744_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(lean_object* v_00_u03b1_2745_, lean_object* v_init_2746_, lean_object* v_t_2747_){
_start:
{
lean_object* v___x_2748_; 
v___x_2748_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2746_, v_t_2747_);
return v___x_2748_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___boxed(lean_object* v_00_u03b1_2749_, lean_object* v_init_2750_, lean_object* v_t_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(v_00_u03b1_2749_, v_init_2750_, v_t_2751_);
lean_dec(v_t_2751_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(lean_object* v_00_u03b1_2753_, lean_object* v_n_2754_, lean_object* v_as_2755_, lean_object* v_lo_2756_, lean_object* v_hi_2757_, lean_object* v_w_2758_, lean_object* v_hlo_2759_, lean_object* v_hhi_2760_){
_start:
{
lean_object* v___x_2761_; 
v___x_2761_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2754_, v_as_2755_, v_lo_2756_, v_hi_2757_);
return v___x_2761_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___boxed(lean_object* v_00_u03b1_2762_, lean_object* v_n_2763_, lean_object* v_as_2764_, lean_object* v_lo_2765_, lean_object* v_hi_2766_, lean_object* v_w_2767_, lean_object* v_hlo_2768_, lean_object* v_hhi_2769_){
_start:
{
lean_object* v_res_2770_; 
v_res_2770_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(v_00_u03b1_2762_, v_n_2763_, v_as_2764_, v_lo_2765_, v_hi_2766_, v_w_2767_, v_hlo_2768_, v_hhi_2769_);
lean_dec(v_hi_2766_);
lean_dec(v_n_2763_);
return v_res_2770_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(lean_object* v_00_u03b1_2771_, lean_object* v_snd_2772_, lean_object* v_as_2773_, lean_object* v_start_2774_, lean_object* v_stop_2775_){
_start:
{
lean_object* v___x_2776_; 
v___x_2776_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2772_, v_as_2773_, v_start_2774_, v_stop_2775_);
return v___x_2776_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___boxed(lean_object* v_00_u03b1_2777_, lean_object* v_snd_2778_, lean_object* v_as_2779_, lean_object* v_start_2780_, lean_object* v_stop_2781_){
_start:
{
lean_object* v_res_2782_; 
v_res_2782_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(v_00_u03b1_2777_, v_snd_2778_, v_as_2779_, v_start_2780_, v_stop_2781_);
lean_dec(v_stop_2781_);
lean_dec(v_start_2780_);
lean_dec_ref(v_as_2779_);
lean_dec(v_snd_2778_);
return v_res_2782_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(lean_object* v_00_u03b1_2783_, lean_object* v_init_2784_, lean_object* v_x_2785_){
_start:
{
lean_object* v___x_2786_; 
v___x_2786_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2784_, v_x_2785_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2787_, lean_object* v_init_2788_, lean_object* v_x_2789_){
_start:
{
lean_object* v_res_2790_; 
v_res_2790_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(v_00_u03b1_2787_, v_init_2788_, v_x_2789_);
lean_dec(v_x_2789_);
return v_res_2790_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(lean_object* v_00_u03b1_2791_, lean_object* v_n_2792_, lean_object* v_lo_2793_, lean_object* v_hi_2794_, lean_object* v_hhi_2795_, lean_object* v_pivot_2796_, lean_object* v_as_2797_, lean_object* v_i_2798_, lean_object* v_k_2799_, lean_object* v_ilo_2800_, lean_object* v_ik_2801_, lean_object* v_w_2802_){
_start:
{
lean_object* v___x_2803_; 
v___x_2803_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2794_, v_pivot_2796_, v_as_2797_, v_i_2798_, v_k_2799_);
return v___x_2803_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2804_, lean_object* v_n_2805_, lean_object* v_lo_2806_, lean_object* v_hi_2807_, lean_object* v_hhi_2808_, lean_object* v_pivot_2809_, lean_object* v_as_2810_, lean_object* v_i_2811_, lean_object* v_k_2812_, lean_object* v_ilo_2813_, lean_object* v_ik_2814_, lean_object* v_w_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(v_00_u03b1_2804_, v_n_2805_, v_lo_2806_, v_hi_2807_, v_hhi_2808_, v_pivot_2809_, v_as_2810_, v_i_2811_, v_k_2812_, v_ilo_2813_, v_ik_2814_, v_w_2815_);
lean_dec_ref(v_pivot_2809_);
lean_dec(v_hi_2807_);
lean_dec(v_lo_2806_);
lean_dec(v_n_2805_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(lean_object* v_00_u03b1_2817_, lean_object* v_snd_2818_, lean_object* v_as_2819_, size_t v_i_2820_, size_t v_stop_2821_, lean_object* v_b_2822_){
_start:
{
lean_object* v___x_2823_; 
v___x_2823_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2818_, v_as_2819_, v_i_2820_, v_stop_2821_, v_b_2822_);
return v___x_2823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2824_, lean_object* v_snd_2825_, lean_object* v_as_2826_, lean_object* v_i_2827_, lean_object* v_stop_2828_, lean_object* v_b_2829_){
_start:
{
size_t v_i_boxed_2830_; size_t v_stop_boxed_2831_; lean_object* v_res_2832_; 
v_i_boxed_2830_ = lean_unbox_usize(v_i_2827_);
lean_dec(v_i_2827_);
v_stop_boxed_2831_ = lean_unbox_usize(v_stop_2828_);
lean_dec(v_stop_2828_);
v_res_2832_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(v_00_u03b1_2824_, v_snd_2825_, v_as_2826_, v_i_boxed_2830_, v_stop_boxed_2831_, v_b_2829_);
lean_dec_ref(v_as_2826_);
lean_dec(v_snd_2825_);
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(lean_object* v_env_2833_, lean_object* v___y_2834_){
_start:
{
lean_object* v___x_2836_; lean_object* v_nextMacroScope_2837_; lean_object* v_ngen_2838_; lean_object* v_auxDeclNGen_2839_; lean_object* v_traceState_2840_; lean_object* v_recordedDeps_2841_; lean_object* v_messages_2842_; lean_object* v_infoState_2843_; lean_object* v_snapshotTasks_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2855_; 
v___x_2836_ = lean_st_ref_take(v___y_2834_);
v_nextMacroScope_2837_ = lean_ctor_get(v___x_2836_, 1);
v_ngen_2838_ = lean_ctor_get(v___x_2836_, 2);
v_auxDeclNGen_2839_ = lean_ctor_get(v___x_2836_, 3);
v_traceState_2840_ = lean_ctor_get(v___x_2836_, 4);
v_recordedDeps_2841_ = lean_ctor_get(v___x_2836_, 6);
v_messages_2842_ = lean_ctor_get(v___x_2836_, 7);
v_infoState_2843_ = lean_ctor_get(v___x_2836_, 8);
v_snapshotTasks_2844_ = lean_ctor_get(v___x_2836_, 9);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2855_ == 0)
{
lean_object* v_unused_2856_; lean_object* v_unused_2857_; 
v_unused_2856_ = lean_ctor_get(v___x_2836_, 5);
lean_dec(v_unused_2856_);
v_unused_2857_ = lean_ctor_get(v___x_2836_, 0);
lean_dec(v_unused_2857_);
v___x_2846_ = v___x_2836_;
v_isShared_2847_ = v_isSharedCheck_2855_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_snapshotTasks_2844_);
lean_inc(v_infoState_2843_);
lean_inc(v_messages_2842_);
lean_inc(v_recordedDeps_2841_);
lean_inc(v_traceState_2840_);
lean_inc(v_auxDeclNGen_2839_);
lean_inc(v_ngen_2838_);
lean_inc(v_nextMacroScope_2837_);
lean_dec(v___x_2836_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2855_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2851_; 
v___x_2848_ = lean_box(0);
v___x_2849_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
if (v_isShared_2847_ == 0)
{
lean_ctor_set(v___x_2846_, 5, v___x_2849_);
lean_ctor_set(v___x_2846_, 0, v_env_2833_);
v___x_2851_ = v___x_2846_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_env_2833_);
lean_ctor_set(v_reuseFailAlloc_2854_, 1, v_nextMacroScope_2837_);
lean_ctor_set(v_reuseFailAlloc_2854_, 2, v_ngen_2838_);
lean_ctor_set(v_reuseFailAlloc_2854_, 3, v_auxDeclNGen_2839_);
lean_ctor_set(v_reuseFailAlloc_2854_, 4, v_traceState_2840_);
lean_ctor_set(v_reuseFailAlloc_2854_, 5, v___x_2849_);
lean_ctor_set(v_reuseFailAlloc_2854_, 6, v_recordedDeps_2841_);
lean_ctor_set(v_reuseFailAlloc_2854_, 7, v_messages_2842_);
lean_ctor_set(v_reuseFailAlloc_2854_, 8, v_infoState_2843_);
lean_ctor_set(v_reuseFailAlloc_2854_, 9, v_snapshotTasks_2844_);
v___x_2851_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___x_2852_ = lean_st_ref_put(v___y_2834_, v___x_2851_);
v___x_2853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2848_);
return v___x_2853_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg___boxed(lean_object* v_env_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_){
_start:
{
lean_object* v_res_2861_; 
v_res_2861_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v_env_2858_, v___y_2859_);
lean_dec(v___y_2859_);
return v_res_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0(lean_object* v_env_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_){
_start:
{
lean_object* v___x_2866_; 
v___x_2866_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v_env_2862_, v___y_2864_);
return v___x_2866_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___boxed(lean_object* v_env_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_){
_start:
{
lean_object* v_res_2871_; 
v_res_2871_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0(v_env_2867_, v___y_2868_, v___y_2869_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
return v_res_2871_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__0(lean_object* v_getParam_2872_, lean_object* v_ext_2873_, lean_object* v_afterSet_2874_, lean_object* v_toAttributeImplCore_2875_, lean_object* v_decl_2876_, lean_object* v_stx_2877_, uint8_t v_kind_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; uint8_t v___y_2887_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; uint8_t v___x_2937_; uint8_t v___x_2938_; 
v___x_2937_ = 0;
v___x_2938_ = l_Lean_instBEqAttributeKind_beq(v_kind_2878_, v___x_2937_);
if (v___x_2938_ == 0)
{
lean_object* v_name_2939_; lean_object* v___x_2940_; 
lean_dec(v_stx_2877_);
lean_dec(v_decl_2876_);
lean_dec_ref(v_afterSet_2874_);
lean_dec_ref(v_ext_2873_);
lean_dec_ref(v_getParam_2872_);
v_name_2939_ = lean_ctor_get(v_toAttributeImplCore_2875_, 1);
lean_inc(v_name_2939_);
lean_dec_ref(v_toAttributeImplCore_2875_);
v___x_2940_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2939_, v_kind_2878_, v___y_2879_, v___y_2880_);
return v___x_2940_;
}
else
{
goto v___jp_2931_;
}
v___jp_2882_:
{
if (v___y_2887_ == 0)
{
lean_object* v___x_2888_; 
lean_dec_ref(v___y_2884_);
v___x_2888_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v___y_2883_, v___y_2885_);
return v___x_2888_;
}
else
{
lean_dec_ref(v___y_2883_);
return v___y_2884_;
}
}
v___jp_2889_:
{
lean_object* v___x_2893_; 
lean_inc(v___y_2892_);
lean_inc_ref(v___y_2891_);
lean_inc(v_decl_2876_);
v___x_2893_ = lean_apply_5(v_getParam_2872_, v_decl_2876_, v_stx_2877_, v___y_2891_, v___y_2892_, lean_box(0));
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_object* v_a_2894_; lean_object* v___x_2895_; lean_object* v_toEnvExtension_2896_; lean_object* v_env_2897_; lean_object* v_nextMacroScope_2898_; lean_object* v_ngen_2899_; lean_object* v_auxDeclNGen_2900_; lean_object* v_traceState_2901_; lean_object* v_recordedDeps_2902_; lean_object* v_messages_2903_; lean_object* v_infoState_2904_; lean_object* v_snapshotTasks_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2921_; 
v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
lean_inc(v_a_2894_);
lean_dec_ref_known(v___x_2893_, 1);
v___x_2895_ = lean_st_ref_take(v___y_2892_);
v_toEnvExtension_2896_ = lean_ctor_get(v_ext_2873_, 0);
v_env_2897_ = lean_ctor_get(v___x_2895_, 0);
v_nextMacroScope_2898_ = lean_ctor_get(v___x_2895_, 1);
v_ngen_2899_ = lean_ctor_get(v___x_2895_, 2);
v_auxDeclNGen_2900_ = lean_ctor_get(v___x_2895_, 3);
v_traceState_2901_ = lean_ctor_get(v___x_2895_, 4);
v_recordedDeps_2902_ = lean_ctor_get(v___x_2895_, 6);
v_messages_2903_ = lean_ctor_get(v___x_2895_, 7);
v_infoState_2904_ = lean_ctor_get(v___x_2895_, 8);
v_snapshotTasks_2905_ = lean_ctor_get(v___x_2895_, 9);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2921_ == 0)
{
lean_object* v_unused_2922_; 
v_unused_2922_ = lean_ctor_get(v___x_2895_, 5);
lean_dec(v_unused_2922_);
v___x_2907_ = v___x_2895_;
v_isShared_2908_ = v_isSharedCheck_2921_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_snapshotTasks_2905_);
lean_inc(v_infoState_2904_);
lean_inc(v_messages_2903_);
lean_inc(v_recordedDeps_2902_);
lean_inc(v_traceState_2901_);
lean_inc(v_auxDeclNGen_2900_);
lean_inc(v_ngen_2899_);
lean_inc(v_nextMacroScope_2898_);
lean_inc(v_env_2897_);
lean_dec(v___x_2895_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2921_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v_asyncMode_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2914_; 
v_asyncMode_2909_ = lean_ctor_get(v_toEnvExtension_2896_, 2);
lean_inc(v_asyncMode_2909_);
lean_inc(v_a_2894_);
lean_inc_n(v_decl_2876_, 2);
v___x_2910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2910_, 0, v_decl_2876_);
lean_ctor_set(v___x_2910_, 1, v_a_2894_);
v___x_2911_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2873_, v_env_2897_, v___x_2910_, v_asyncMode_2909_, v_decl_2876_);
lean_dec(v_asyncMode_2909_);
v___x_2912_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 5, v___x_2912_);
lean_ctor_set(v___x_2907_, 0, v___x_2911_);
v___x_2914_ = v___x_2907_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v___x_2911_);
lean_ctor_set(v_reuseFailAlloc_2920_, 1, v_nextMacroScope_2898_);
lean_ctor_set(v_reuseFailAlloc_2920_, 2, v_ngen_2899_);
lean_ctor_set(v_reuseFailAlloc_2920_, 3, v_auxDeclNGen_2900_);
lean_ctor_set(v_reuseFailAlloc_2920_, 4, v_traceState_2901_);
lean_ctor_set(v_reuseFailAlloc_2920_, 5, v___x_2912_);
lean_ctor_set(v_reuseFailAlloc_2920_, 6, v_recordedDeps_2902_);
lean_ctor_set(v_reuseFailAlloc_2920_, 7, v_messages_2903_);
lean_ctor_set(v_reuseFailAlloc_2920_, 8, v_infoState_2904_);
lean_ctor_set(v_reuseFailAlloc_2920_, 9, v_snapshotTasks_2905_);
v___x_2914_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
lean_object* v___x_2915_; lean_object* v___x_2916_; 
v___x_2915_ = lean_st_ref_put(v___y_2892_, v___x_2914_);
lean_inc(v___y_2892_);
lean_inc_ref(v___y_2891_);
v___x_2916_ = lean_apply_5(v_afterSet_2874_, v_decl_2876_, v_a_2894_, v___y_2891_, v___y_2892_, lean_box(0));
if (lean_obj_tag(v___x_2916_) == 0)
{
lean_dec_ref(v___y_2890_);
return v___x_2916_;
}
else
{
lean_object* v_a_2917_; uint8_t v___x_2918_; 
v_a_2917_ = lean_ctor_get(v___x_2916_, 0);
lean_inc(v_a_2917_);
v___x_2918_ = l_Lean_Exception_isInterrupt(v_a_2917_);
if (v___x_2918_ == 0)
{
uint8_t v___x_2919_; 
v___x_2919_ = l_Lean_Exception_isRuntime(v_a_2917_);
v___y_2883_ = v___y_2890_;
v___y_2884_ = v___x_2916_;
v___y_2885_ = v___y_2892_;
v___y_2886_ = v___y_2891_;
v___y_2887_ = v___x_2919_;
goto v___jp_2882_;
}
else
{
lean_dec(v_a_2917_);
v___y_2883_ = v___y_2890_;
v___y_2884_ = v___x_2916_;
v___y_2885_ = v___y_2892_;
v___y_2886_ = v___y_2891_;
v___y_2887_ = v___x_2918_;
goto v___jp_2882_;
}
}
}
}
}
else
{
lean_object* v_a_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2930_; 
lean_dec_ref(v___y_2890_);
lean_dec(v_decl_2876_);
lean_dec_ref(v_afterSet_2874_);
lean_dec_ref(v_ext_2873_);
v_a_2923_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2930_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2925_ = v___x_2893_;
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_a_2923_);
lean_dec(v___x_2893_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2928_; 
if (v_isShared_2926_ == 0)
{
v___x_2928_ = v___x_2925_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_a_2923_);
v___x_2928_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
return v___x_2928_;
}
}
}
}
v___jp_2931_:
{
lean_object* v___x_2932_; lean_object* v_env_2933_; lean_object* v___x_2934_; 
v___x_2932_ = lean_st_ref_get(v___y_2880_);
v_env_2933_ = lean_ctor_get(v___x_2932_, 0);
lean_inc_ref(v_env_2933_);
lean_dec(v___x_2932_);
v___x_2934_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2933_, v_decl_2876_);
if (lean_obj_tag(v___x_2934_) == 0)
{
lean_dec_ref(v_toAttributeImplCore_2875_);
v___y_2890_ = v_env_2933_;
v___y_2891_ = v___y_2879_;
v___y_2892_ = v___y_2880_;
goto v___jp_2889_;
}
else
{
lean_object* v_name_2935_; lean_object* v___x_2936_; 
lean_dec_ref_known(v___x_2934_, 1);
lean_dec_ref(v_env_2933_);
lean_dec(v_stx_2877_);
lean_dec_ref(v_afterSet_2874_);
lean_dec_ref(v_ext_2873_);
lean_dec_ref(v_getParam_2872_);
v_name_2935_ = lean_ctor_get(v_toAttributeImplCore_2875_, 1);
lean_inc(v_name_2935_);
lean_dec_ref(v_toAttributeImplCore_2875_);
v___x_2936_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_2935_, v_decl_2876_, v___y_2879_, v___y_2880_);
return v___x_2936_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__0___boxed(lean_object* v_getParam_2941_, lean_object* v_ext_2942_, lean_object* v_afterSet_2943_, lean_object* v_toAttributeImplCore_2944_, lean_object* v_decl_2945_, lean_object* v_stx_2946_, lean_object* v_kind_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_){
_start:
{
uint8_t v_kind_boxed_2951_; lean_object* v_res_2952_; 
v_kind_boxed_2951_ = lean_unbox(v_kind_2947_);
v_res_2952_ = l_Lean_registerParametricAttributeForExt___redArg___lam__0(v_getParam_2941_, v_ext_2942_, v_afterSet_2943_, v_toAttributeImplCore_2944_, v_decl_2945_, v_stx_2946_, v_kind_boxed_2951_, v___y_2948_, v___y_2949_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
return v_res_2952_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1(lean_object* v_toAttributeImplCore_2953_, lean_object* v_decl_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_){
_start:
{
lean_object* v_name_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
v_name_2958_ = lean_ctor_get(v_toAttributeImplCore_2953_, 1);
lean_inc(v_name_2958_);
lean_dec_ref(v_toAttributeImplCore_2953_);
v___x_2959_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_2960_ = l_Lean_MessageData_ofName(v_name_2958_);
v___x_2961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2961_, 0, v___x_2959_);
lean_ctor_set(v___x_2961_, 1, v___x_2960_);
v___x_2962_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_2963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2961_);
lean_ctor_set(v___x_2963_, 1, v___x_2962_);
v___x_2964_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_2963_, v___y_2955_, v___y_2956_);
return v___x_2964_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed(lean_object* v_toAttributeImplCore_2965_, lean_object* v_decl_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_){
_start:
{
lean_object* v_res_2970_; 
v_res_2970_ = l_Lean_registerParametricAttributeForExt___redArg___lam__1(v_toAttributeImplCore_2965_, v_decl_2966_, v___y_2967_, v___y_2968_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec(v_decl_2966_);
return v_res_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg(lean_object* v_impl_2971_, lean_object* v_ext_2972_){
_start:
{
lean_object* v_toAttributeImplCore_2974_; lean_object* v_getParam_2975_; lean_object* v_afterSet_2976_; uint8_t v_preserveOrder_2977_; lean_object* v___f_2978_; lean_object* v___f_2979_; lean_object* v_attrImpl_2980_; lean_object* v___x_2981_; 
v_toAttributeImplCore_2974_ = lean_ctor_get(v_impl_2971_, 0);
lean_inc_ref_n(v_toAttributeImplCore_2974_, 3);
v_getParam_2975_ = lean_ctor_get(v_impl_2971_, 1);
lean_inc_ref(v_getParam_2975_);
v_afterSet_2976_ = lean_ctor_get(v_impl_2971_, 2);
lean_inc_ref(v_afterSet_2976_);
v_preserveOrder_2977_ = lean_ctor_get_uint8(v_impl_2971_, sizeof(void*)*4);
lean_dec_ref(v_impl_2971_);
lean_inc_ref(v_ext_2972_);
v___f_2978_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2978_, 0, v_getParam_2975_);
lean_closure_set(v___f_2978_, 1, v_ext_2972_);
lean_closure_set(v___f_2978_, 2, v_afterSet_2976_);
lean_closure_set(v___f_2978_, 3, v_toAttributeImplCore_2974_);
v___f_2979_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed), 5, 1);
lean_closure_set(v___f_2979_, 0, v_toAttributeImplCore_2974_);
v_attrImpl_2980_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_attrImpl_2980_, 0, v_toAttributeImplCore_2974_);
lean_ctor_set(v_attrImpl_2980_, 1, v___f_2978_);
lean_ctor_set(v_attrImpl_2980_, 2, v___f_2979_);
lean_inc_ref(v_attrImpl_2980_);
v___x_2981_ = l_Lean_registerBuiltinAttribute(v_attrImpl_2980_);
if (lean_obj_tag(v___x_2981_) == 0)
{
lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2989_; 
v_isSharedCheck_2989_ = !lean_is_exclusive(v___x_2981_);
if (v_isSharedCheck_2989_ == 0)
{
lean_object* v_unused_2990_; 
v_unused_2990_ = lean_ctor_get(v___x_2981_, 0);
lean_dec(v_unused_2990_);
v___x_2983_ = v___x_2981_;
v_isShared_2984_ = v_isSharedCheck_2989_;
goto v_resetjp_2982_;
}
else
{
lean_dec(v___x_2981_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2989_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2985_; lean_object* v___x_2987_; 
v___x_2985_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2985_, 0, v_attrImpl_2980_);
lean_ctor_set(v___x_2985_, 1, v_ext_2972_);
lean_ctor_set_uint8(v___x_2985_, sizeof(void*)*2, v_preserveOrder_2977_);
if (v_isShared_2984_ == 0)
{
lean_ctor_set(v___x_2983_, 0, v___x_2985_);
v___x_2987_ = v___x_2983_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v___x_2985_);
v___x_2987_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
return v___x_2987_;
}
}
}
else
{
lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_2998_; 
lean_dec_ref_known(v_attrImpl_2980_, 3);
lean_dec_ref(v_ext_2972_);
v_a_2991_ = lean_ctor_get(v___x_2981_, 0);
v_isSharedCheck_2998_ = !lean_is_exclusive(v___x_2981_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2993_ = v___x_2981_;
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_dec(v___x_2981_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2996_; 
if (v_isShared_2994_ == 0)
{
v___x_2996_ = v___x_2993_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_a_2991_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
return v___x_2996_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___boxed(lean_object* v_impl_2999_, lean_object* v_ext_3000_, lean_object* v_a_3001_){
_start:
{
lean_object* v_res_3002_; 
v_res_3002_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_2999_, v_ext_3000_);
return v_res_3002_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt(lean_object* v_00_u03b1_3003_, lean_object* v_impl_3004_, lean_object* v_ext_3005_){
_start:
{
lean_object* v___x_3007_; 
v___x_3007_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3004_, v_ext_3005_);
return v___x_3007_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___boxed(lean_object* v_00_u03b1_3008_, lean_object* v_impl_3009_, lean_object* v_ext_3010_, lean_object* v_a_3011_){
_start:
{
lean_object* v_res_3012_; 
v_res_3012_ = l_Lean_registerParametricAttributeForExt(v_00_u03b1_3008_, v_impl_3009_, v_ext_3010_);
return v_res_3012_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg(lean_object* v_impl_3013_){
_start:
{
lean_object* v_toAttributeImplCore_3015_; uint8_t v_preserveOrder_3016_; lean_object* v_filterExport_3017_; lean_object* v_ref_3018_; lean_object* v___x_3019_; 
v_toAttributeImplCore_3015_ = lean_ctor_get(v_impl_3013_, 0);
v_preserveOrder_3016_ = lean_ctor_get_uint8(v_impl_3013_, sizeof(void*)*4);
v_filterExport_3017_ = lean_ctor_get(v_impl_3013_, 3);
v_ref_3018_ = lean_ctor_get(v_toAttributeImplCore_3015_, 0);
lean_inc_ref(v_filterExport_3017_);
lean_inc(v_ref_3018_);
v___x_3019_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_3018_, v_preserveOrder_3016_, v_filterExport_3017_);
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_object* v_a_3020_; lean_object* v___x_3021_; 
v_a_3020_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_a_3020_);
lean_dec_ref_known(v___x_3019_, 1);
v___x_3021_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3013_, v_a_3020_);
return v___x_3021_;
}
else
{
lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3029_; 
lean_dec_ref(v_impl_3013_);
v_a_3022_ = lean_ctor_get(v___x_3019_, 0);
v_isSharedCheck_3029_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_3024_ = v___x_3019_;
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_dec(v___x_3019_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v___x_3027_; 
if (v_isShared_3025_ == 0)
{
v___x_3027_ = v___x_3024_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v_a_3022_);
v___x_3027_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
return v___x_3027_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___boxed(lean_object* v_impl_3030_, lean_object* v_a_3031_){
_start:
{
lean_object* v_res_3032_; 
v_res_3032_ = l_Lean_registerParametricAttribute___redArg(v_impl_3030_);
return v_res_3032_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute(lean_object* v_00_u03b1_3033_, lean_object* v_impl_3034_){
_start:
{
lean_object* v___x_3036_; 
v___x_3036_ = l_Lean_registerParametricAttribute___redArg(v_impl_3034_);
return v___x_3036_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___boxed(lean_object* v_00_u03b1_3037_, lean_object* v_impl_3038_, lean_object* v_a_3039_){
_start:
{
lean_object* v_res_3040_; 
v_res_3040_ = l_Lean_registerParametricAttribute(v_00_u03b1_3037_, v_impl_3038_);
return v_res_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1(lean_object* v_decl_3041_, lean_object* v___x_3042_, lean_object* v___x_3043_, lean_object* v_a_3044_, lean_object* v_x_3045_, lean_object* v___y_3046_){
_start:
{
lean_object* v_fst_3047_; uint8_t v___x_3048_; 
v_fst_3047_ = lean_ctor_get(v_a_3044_, 0);
v___x_3048_ = lean_name_eq(v_fst_3047_, v_decl_3041_);
if (v___x_3048_ == 0)
{
lean_object* v___x_3049_; 
lean_dec_ref(v_a_3044_);
v___x_3049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3042_);
return v___x_3049_;
}
else
{
lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; 
lean_dec_ref(v___x_3042_);
v___x_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3050_, 0, v_a_3044_);
v___x_3051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3050_);
v___x_3052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3051_);
lean_ctor_set(v___x_3052_, 1, v___x_3043_);
v___x_3053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3052_);
return v___x_3053_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1___boxed(lean_object* v_decl_3054_, lean_object* v___x_3055_, lean_object* v___x_3056_, lean_object* v_a_3057_, lean_object* v_x_3058_, lean_object* v___y_3059_){
_start:
{
lean_object* v_res_3060_; 
v_res_3060_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1(v_decl_3054_, v___x_3055_, v___x_3056_, v_a_3057_, v_x_3058_, v___y_3059_);
lean_dec_ref(v___y_3059_);
lean_dec(v_decl_3054_);
return v_res_3060_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(lean_object* v_inst_3088_, lean_object* v_ext_3089_, uint8_t v_preserveOrder_3090_, lean_object* v_env_3091_, lean_object* v_decl_3092_){
_start:
{
lean_object* v___y_3094_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3105_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0));
v___x_3106_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3091_, v_decl_3092_);
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_object* v_toEnvExtension_3107_; lean_object* v_asyncMode_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v_snd_3111_; lean_object* v___x_3112_; 
lean_dec(v_inst_3088_);
v_toEnvExtension_3107_ = lean_ctor_get(v_ext_3089_, 0);
v_asyncMode_3108_ = lean_ctor_get(v_toEnvExtension_3107_, 2);
v___x_3109_ = lean_box(0);
v___x_3110_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3105_, v_ext_3089_, v_env_3091_, v_asyncMode_3108_, v___x_3109_);
v_snd_3111_ = lean_ctor_get(v___x_3110_, 1);
lean_inc(v_snd_3111_);
lean_dec(v___x_3110_);
v___x_3112_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3111_, v_decl_3092_);
lean_dec(v_decl_3092_);
lean_dec(v_snd_3111_);
return v___x_3112_;
}
else
{
if (v_preserveOrder_3090_ == 0)
{
lean_object* v_val_3113_; uint8_t v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; uint8_t v___x_3118_; 
v_val_3113_ = lean_ctor_get(v___x_3106_, 0);
lean_inc(v_val_3113_);
lean_dec_ref_known(v___x_3106_, 1);
v___x_3114_ = 0;
v___x_3115_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3105_, v_ext_3089_, v_env_3091_, v_val_3113_, v___x_3114_);
lean_dec(v_val_3113_);
lean_dec_ref(v_env_3091_);
v___x_3116_ = lean_unsigned_to_nat(0u);
v___x_3117_ = lean_array_get_size(v___x_3115_);
v___x_3118_ = lean_nat_dec_lt(v___x_3116_, v___x_3117_);
if (v___x_3118_ == 0)
{
lean_object* v___x_3119_; 
lean_dec_ref(v___x_3115_);
lean_dec(v_decl_3092_);
lean_dec(v_inst_3088_);
v___x_3119_ = lean_box(0);
return v___x_3119_;
}
else
{
lean_object* v___x_3120_; lean_object* v___x_3121_; uint8_t v___x_3122_; 
v___x_3120_ = lean_unsigned_to_nat(1u);
v___x_3121_ = lean_nat_sub(v___x_3117_, v___x_3120_);
v___x_3122_ = lean_nat_dec_le(v___x_3116_, v___x_3121_);
if (v___x_3122_ == 0)
{
lean_object* v___x_3123_; 
lean_dec(v___x_3121_);
lean_dec_ref(v___x_3115_);
lean_dec(v_decl_3092_);
lean_dec(v_inst_3088_);
v___x_3123_ = lean_box(0);
return v___x_3123_;
}
else
{
lean_object* v___f_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
v___f_3124_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1));
v___x_3125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3125_, 0, v_decl_3092_);
lean_ctor_set(v___x_3125_, 1, v_inst_3088_);
v___x_3126_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2));
v___x_3127_ = l_Array_binSearchAux___redArg(v___f_3124_, v___x_3126_, v___x_3115_, v___x_3125_, v___x_3116_, v___x_3121_);
lean_dec_ref(v___x_3115_);
v___y_3094_ = v___x_3127_;
goto v___jp_3093_;
}
}
}
else
{
lean_object* v_val_3128_; uint8_t v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___f_3135_; size_t v_sz_3136_; size_t v___x_3137_; lean_object* v___x_3138_; lean_object* v_fst_3139_; 
lean_dec(v_inst_3088_);
v_val_3128_ = lean_ctor_get(v___x_3106_, 0);
lean_inc(v_val_3128_);
lean_dec_ref_known(v___x_3106_, 1);
v___x_3129_ = 0;
v___x_3130_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3105_, v_ext_3089_, v_env_3091_, v_val_3128_, v___x_3129_);
lean_dec(v_val_3128_);
lean_dec_ref(v_env_3091_);
v___x_3131_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__12));
v___x_3132_ = lean_box(0);
v___x_3133_ = lean_box(0);
v___x_3134_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__13));
v___f_3135_ = lean_alloc_closure((void*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_3135_, 0, v_decl_3092_);
lean_closure_set(v___f_3135_, 1, v___x_3134_);
lean_closure_set(v___f_3135_, 2, v___x_3133_);
v_sz_3136_ = lean_array_size(v___x_3130_);
v___x_3137_ = ((size_t)0ULL);
v___x_3138_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3131_, v___x_3130_, v___f_3135_, v_sz_3136_, v___x_3137_, v___x_3134_);
v_fst_3139_ = lean_ctor_get(v___x_3138_, 0);
lean_inc(v_fst_3139_);
lean_dec(v___x_3138_);
if (lean_obj_tag(v_fst_3139_) == 0)
{
return v___x_3132_;
}
else
{
lean_object* v_val_3140_; 
v_val_3140_ = lean_ctor_get(v_fst_3139_, 0);
lean_inc(v_val_3140_);
lean_dec_ref_known(v_fst_3139_, 1);
v___y_3094_ = v_val_3140_;
goto v___jp_3093_;
}
}
}
v___jp_3093_:
{
if (lean_obj_tag(v___y_3094_) == 0)
{
lean_object* v___x_3095_; 
v___x_3095_ = lean_box(0);
return v___x_3095_;
}
else
{
lean_object* v_val_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3104_; 
v_val_3096_ = lean_ctor_get(v___y_3094_, 0);
v_isSharedCheck_3104_ = !lean_is_exclusive(v___y_3094_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3098_ = v___y_3094_;
v_isShared_3099_ = v_isSharedCheck_3104_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_val_3096_);
lean_dec(v___y_3094_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3104_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
lean_object* v_snd_3100_; lean_object* v___x_3102_; 
v_snd_3100_ = lean_ctor_get(v_val_3096_, 1);
lean_inc(v_snd_3100_);
lean_dec(v_val_3096_);
if (v_isShared_3099_ == 0)
{
lean_ctor_set(v___x_3098_, 0, v_snd_3100_);
v___x_3102_ = v___x_3098_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v_snd_3100_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
return v___x_3102_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___boxed(lean_object* v_inst_3141_, lean_object* v_ext_3142_, lean_object* v_preserveOrder_3143_, lean_object* v_env_3144_, lean_object* v_decl_3145_){
_start:
{
uint8_t v_preserveOrder_boxed_3146_; lean_object* v_res_3147_; 
v_preserveOrder_boxed_3146_ = lean_unbox(v_preserveOrder_3143_);
v_res_3147_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3141_, v_ext_3142_, v_preserveOrder_boxed_3146_, v_env_3144_, v_decl_3145_);
lean_dec_ref(v_ext_3142_);
return v_res_3147_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f(lean_object* v_00_u03b1_3148_, lean_object* v_inst_3149_, lean_object* v_ext_3150_, uint8_t v_preserveOrder_3151_, lean_object* v_env_3152_, lean_object* v_decl_3153_){
_start:
{
lean_object* v___x_3154_; 
v___x_3154_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3149_, v_ext_3150_, v_preserveOrder_3151_, v_env_3152_, v_decl_3153_);
return v___x_3154_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___boxed(lean_object* v_00_u03b1_3155_, lean_object* v_inst_3156_, lean_object* v_ext_3157_, lean_object* v_preserveOrder_3158_, lean_object* v_env_3159_, lean_object* v_decl_3160_){
_start:
{
uint8_t v_preserveOrder_boxed_3161_; lean_object* v_res_3162_; 
v_preserveOrder_boxed_3161_ = lean_unbox(v_preserveOrder_3158_);
v_res_3162_ = l_Lean_ParametricAttribute_getParamFromExt_x3f(v_00_u03b1_3155_, v_inst_3156_, v_ext_3157_, v_preserveOrder_boxed_3161_, v_env_3159_, v_decl_3160_);
lean_dec_ref(v_ext_3157_);
return v_res_3162_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object* v_inst_3163_, lean_object* v_attr_3164_, lean_object* v_env_3165_, lean_object* v_decl_3166_){
_start:
{
lean_object* v_ext_3167_; uint8_t v_preserveOrder_3168_; lean_object* v___x_3169_; 
v_ext_3167_ = lean_ctor_get(v_attr_3164_, 1);
v_preserveOrder_3168_ = lean_ctor_get_uint8(v_attr_3164_, sizeof(void*)*2);
v___x_3169_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3163_, v_ext_3167_, v_preserveOrder_3168_, v_env_3165_, v_decl_3166_);
return v___x_3169_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___boxed(lean_object* v_inst_3170_, lean_object* v_attr_3171_, lean_object* v_env_3172_, lean_object* v_decl_3173_){
_start:
{
lean_object* v_res_3174_; 
v_res_3174_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3170_, v_attr_3171_, v_env_3172_, v_decl_3173_);
lean_dec_ref(v_attr_3171_);
return v_res_3174_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f(lean_object* v_00_u03b1_3175_, lean_object* v_inst_3176_, lean_object* v_attr_3177_, lean_object* v_env_3178_, lean_object* v_decl_3179_){
_start:
{
lean_object* v___x_3180_; 
v___x_3180_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3176_, v_attr_3177_, v_env_3178_, v_decl_3179_);
return v___x_3180_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___boxed(lean_object* v_00_u03b1_3181_, lean_object* v_inst_3182_, lean_object* v_attr_3183_, lean_object* v_env_3184_, lean_object* v_decl_3185_){
_start:
{
lean_object* v_res_3186_; 
v_res_3186_ = l_Lean_ParametricAttribute_getParam_x3f(v_00_u03b1_3181_, v_inst_3182_, v_attr_3183_, v_env_3184_, v_decl_3185_);
lean_dec_ref(v_attr_3183_);
return v_res_3186_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt___redArg(lean_object* v_ext_3191_, lean_object* v_attr_3192_, lean_object* v_env_3193_, lean_object* v_decl_3194_, lean_object* v_param_3195_){
_start:
{
lean_object* v___x_3196_; 
v___x_3196_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3193_, v_decl_3194_);
if (lean_obj_tag(v___x_3196_) == 0)
{
lean_object* v_toEnvExtension_3197_; lean_object* v_asyncMode_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v_snd_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3232_; 
v_toEnvExtension_3197_ = lean_ctor_get(v_ext_3191_, 0);
v_asyncMode_3198_ = lean_ctor_get(v_toEnvExtension_3197_, 2);
lean_inc(v_asyncMode_3198_);
v___x_3199_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0));
v___x_3200_ = lean_box(0);
lean_inc_ref(v_env_3193_);
v___x_3201_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3199_, v_ext_3191_, v_env_3193_, v_asyncMode_3198_, v___x_3200_);
v_snd_3202_ = lean_ctor_get(v___x_3201_, 1);
v_isSharedCheck_3232_ = !lean_is_exclusive(v___x_3201_);
if (v_isSharedCheck_3232_ == 0)
{
lean_object* v_unused_3233_; 
v_unused_3233_ = lean_ctor_get(v___x_3201_, 0);
lean_dec(v_unused_3233_);
v___x_3204_ = v___x_3201_;
v_isShared_3205_ = v_isSharedCheck_3232_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_snd_3202_);
lean_dec(v___x_3201_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3232_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3206_; 
v___x_3206_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3202_, v_decl_3194_);
lean_dec(v_snd_3202_);
if (lean_obj_tag(v___x_3206_) == 0)
{
lean_object* v___x_3208_; 
lean_dec_ref(v_attr_3192_);
if (v_isShared_3205_ == 0)
{
lean_ctor_set(v___x_3204_, 1, v_param_3195_);
lean_ctor_set(v___x_3204_, 0, v_decl_3194_);
v___x_3208_ = v___x_3204_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_decl_3194_);
lean_ctor_set(v_reuseFailAlloc_3211_, 1, v_param_3195_);
v___x_3208_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
lean_object* v___x_3209_; lean_object* v___x_3210_; 
v___x_3209_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_3191_, v_env_3193_, v___x_3208_, v_asyncMode_3198_, v___x_3200_);
lean_dec(v_asyncMode_3198_);
v___x_3210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3210_, 0, v___x_3209_);
return v___x_3210_;
}
}
else
{
lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3230_; 
lean_del_object(v___x_3204_);
lean_dec(v_asyncMode_3198_);
lean_dec(v_param_3195_);
lean_dec_ref(v_env_3193_);
lean_dec_ref(v_ext_3191_);
v_isSharedCheck_3230_ = !lean_is_exclusive(v___x_3206_);
if (v_isSharedCheck_3230_ == 0)
{
lean_object* v_unused_3231_; 
v_unused_3231_ = lean_ctor_get(v___x_3206_, 0);
lean_dec(v_unused_3231_);
v___x_3213_ = v___x_3206_;
v_isShared_3214_ = v_isSharedCheck_3230_;
goto v_resetjp_3212_;
}
else
{
lean_dec(v___x_3206_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3230_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v_toAttributeImplCore_3215_; lean_object* v_name_3216_; uint8_t v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3228_; 
v_toAttributeImplCore_3215_ = lean_ctor_get(v_attr_3192_, 0);
lean_inc_ref(v_toAttributeImplCore_3215_);
lean_dec_ref(v_attr_3192_);
v_name_3216_ = lean_ctor_get(v_toAttributeImplCore_3215_, 1);
lean_inc(v_name_3216_);
lean_dec_ref(v_toAttributeImplCore_3215_);
v___x_3217_ = 1;
v___x_3218_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0));
v___x_3219_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3216_, v___x_3217_);
v___x_3220_ = lean_string_append(v___x_3218_, v___x_3219_);
lean_dec_ref(v___x_3219_);
v___x_3221_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1));
v___x_3222_ = lean_string_append(v___x_3220_, v___x_3221_);
v___x_3223_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3194_, v___x_3217_);
v___x_3224_ = lean_string_append(v___x_3222_, v___x_3223_);
lean_dec_ref(v___x_3223_);
v___x_3225_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__2));
v___x_3226_ = lean_string_append(v___x_3224_, v___x_3225_);
if (v_isShared_3214_ == 0)
{
lean_ctor_set_tag(v___x_3213_, 0);
lean_ctor_set(v___x_3213_, 0, v___x_3226_);
v___x_3228_ = v___x_3213_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v___x_3226_);
v___x_3228_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
return v___x_3228_;
}
}
}
}
}
else
{
lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3252_; 
lean_dec(v_param_3195_);
lean_dec_ref(v_env_3193_);
lean_dec_ref(v_ext_3191_);
v_isSharedCheck_3252_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3252_ == 0)
{
lean_object* v_unused_3253_; 
v_unused_3253_ = lean_ctor_get(v___x_3196_, 0);
lean_dec(v_unused_3253_);
v___x_3235_ = v___x_3196_;
v_isShared_3236_ = v_isSharedCheck_3252_;
goto v_resetjp_3234_;
}
else
{
lean_dec(v___x_3196_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3252_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
lean_object* v_toAttributeImplCore_3237_; lean_object* v_name_3238_; uint8_t v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3250_; 
v_toAttributeImplCore_3237_ = lean_ctor_get(v_attr_3192_, 0);
lean_inc_ref(v_toAttributeImplCore_3237_);
lean_dec_ref(v_attr_3192_);
v_name_3238_ = lean_ctor_get(v_toAttributeImplCore_3237_, 1);
lean_inc(v_name_3238_);
lean_dec_ref(v_toAttributeImplCore_3237_);
v___x_3239_ = 1;
v___x_3240_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0));
v___x_3241_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3238_, v___x_3239_);
v___x_3242_ = lean_string_append(v___x_3240_, v___x_3241_);
lean_dec_ref(v___x_3241_);
v___x_3243_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1));
v___x_3244_ = lean_string_append(v___x_3242_, v___x_3243_);
v___x_3245_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3194_, v___x_3239_);
v___x_3246_ = lean_string_append(v___x_3244_, v___x_3245_);
lean_dec_ref(v___x_3245_);
v___x_3247_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__3));
v___x_3248_ = lean_string_append(v___x_3246_, v___x_3247_);
if (v_isShared_3236_ == 0)
{
lean_ctor_set_tag(v___x_3235_, 0);
lean_ctor_set(v___x_3235_, 0, v___x_3248_);
v___x_3250_ = v___x_3235_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v___x_3248_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt(lean_object* v_00_u03b1_3254_, lean_object* v_ext_3255_, lean_object* v_attr_3256_, lean_object* v_env_3257_, lean_object* v_decl_3258_, lean_object* v_param_3259_){
_start:
{
lean_object* v___x_3260_; 
v___x_3260_ = l_Lean_ParametricAttribute_setParamFromExt___redArg(v_ext_3255_, v_attr_3256_, v_env_3257_, v_decl_3258_, v_param_3259_);
return v___x_3260_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object* v_attr_3261_, lean_object* v_env_3262_, lean_object* v_decl_3263_, lean_object* v_param_3264_){
_start:
{
lean_object* v_attr_3265_; lean_object* v_ext_3266_; lean_object* v___x_3267_; 
v_attr_3265_ = lean_ctor_get(v_attr_3261_, 0);
lean_inc_ref(v_attr_3265_);
v_ext_3266_ = lean_ctor_get(v_attr_3261_, 1);
lean_inc_ref(v_ext_3266_);
lean_dec_ref(v_attr_3261_);
v___x_3267_ = l_Lean_ParametricAttribute_setParamFromExt___redArg(v_ext_3266_, v_attr_3265_, v_env_3262_, v_decl_3263_, v_param_3264_);
return v___x_3267_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam(lean_object* v_00_u03b1_3268_, lean_object* v_attr_3269_, lean_object* v_env_3270_, lean_object* v_decl_3271_, lean_object* v_param_3272_){
_start:
{
lean_object* v___x_3273_; 
v___x_3273_ = l_Lean_ParametricAttribute_setParam___redArg(v_attr_3269_, v_env_3270_, v_decl_3271_, v_param_3272_);
return v___x_3273_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0(lean_object* v_x_3274_, lean_object* v___y_3275_){
_start:
{
lean_object* v___x_3277_; lean_object* v___x_3278_; 
v___x_3277_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_3278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3278_, 0, v___x_3277_);
return v___x_3278_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0___boxed(lean_object* v_x_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_){
_start:
{
lean_object* v_res_3282_; 
v_res_3282_ = l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0(v_x_3279_, v___y_3280_);
lean_dec_ref(v___y_3280_);
lean_dec_ref(v_x_3279_);
return v_res_3282_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1(lean_object* v_s_3283_, lean_object* v_x_3284_){
_start:
{
lean_inc(v_s_3283_);
return v_s_3283_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1___boxed(lean_object* v_s_3285_, lean_object* v_x_3286_){
_start:
{
lean_object* v_res_3287_; 
v_res_3287_ = l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1(v_s_3285_, v_x_3286_);
lean_dec_ref(v_x_3286_);
lean_dec(v_s_3285_);
return v_res_3287_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2(lean_object* v_x_3288_, lean_object* v_x_3289_){
_start:
{
lean_object* v___x_3290_; 
v___x_3290_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__1));
return v___x_3290_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2___boxed(lean_object* v_x_3291_, lean_object* v_x_3292_){
_start:
{
lean_object* v_res_3293_; 
v_res_3293_ = l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2(v_x_3291_, v_x_3292_);
lean_dec(v_x_3292_);
lean_dec_ref(v_x_3291_);
return v_res_3293_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3(void){
_start:
{
lean_object* v___f_3297_; lean_object* v___f_3298_; lean_object* v___f_3299_; lean_object* v___f_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; 
v___f_3297_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_3298_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___redArg___closed__2));
v___f_3299_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___redArg___closed__1));
v___f_3300_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___redArg___closed__0));
v___x_3301_ = lean_box(0);
v___x_3302_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_3303_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3303_, 0, v___x_3302_);
lean_ctor_set(v___x_3303_, 1, v___x_3301_);
lean_ctor_set(v___x_3303_, 2, v___f_3300_);
lean_ctor_set(v___x_3303_, 3, v___f_3299_);
lean_ctor_set(v___x_3303_, 4, v___f_3298_);
lean_ctor_set(v___x_3303_, 5, v___f_3297_);
return v___x_3303_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4(void){
_start:
{
lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; 
v___x_3304_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3, &l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3_once, _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3);
v___x_3305_ = lean_box(0);
v___x_3306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3305_);
lean_ctor_set(v___x_3306_, 1, v___x_3304_);
return v___x_3306_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg(){
_start:
{
lean_object* v___x_3308_; 
v___x_3308_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4, &l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4_once, _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4);
return v___x_3308_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___boxed(lean_object* v___dummy_3309_){
_start:
{
lean_object* v_res_3310_; 
v_res_3310_ = l_Lean_instInhabitedEnumAttributes_default___redArg();
return v_res_3310_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__0(void){
_start:
{
lean_object* v___x_3311_; 
v___x_3311_ = l_Lean_instInhabitedEnumAttributes_default___redArg();
return v___x_3311_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default(lean_object* v_00_u03b1_3312_){
_start:
{
lean_object* v___x_3313_; 
v___x_3313_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__0, &l_Lean_instInhabitedEnumAttributes_default___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__0);
return v___x_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes___redArg(){
_start:
{
lean_object* v___x_3315_; 
v___x_3315_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__0, &l_Lean_instInhabitedEnumAttributes_default___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__0);
return v___x_3315_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes___redArg___boxed(lean_object* v___dummy_3316_){
_start:
{
lean_object* v_res_3317_; 
v_res_3317_ = l_Lean_instInhabitedEnumAttributes___redArg();
return v_res_3317_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes(lean_object* v_a_3318_){
_start:
{
lean_object* v___x_3319_; 
v___x_3319_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__0, &l_Lean_instInhabitedEnumAttributes_default___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__0);
return v___x_3319_;
}
}
static lean_object* _init_l_Lean_registerEnumAttributes___auto__1(void){
_start:
{
lean_object* v___x_3320_; 
v___x_3320_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_3320_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0(lean_object* v_x_3321_){
_start:
{
lean_object* v___x_3322_; 
v___x_3322_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
return v___x_3322_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0___boxed(lean_object* v_x_3323_){
_start:
{
lean_object* v_res_3324_; 
v_res_3324_ = l_Lean_registerEnumAttributes___redArg___lam__0(v_x_3323_);
lean_dec(v_x_3323_);
return v_res_3324_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(lean_object* v_newState_3325_, lean_object* v_x_3326_, lean_object* v_x_3327_){
_start:
{
if (lean_obj_tag(v_x_3327_) == 0)
{
return v_x_3326_;
}
else
{
lean_object* v_head_3328_; lean_object* v_tail_3329_; lean_object* v___x_3330_; 
v_head_3328_ = lean_ctor_get(v_x_3327_, 0);
lean_inc(v_head_3328_);
v_tail_3329_ = lean_ctor_get(v_x_3327_, 1);
lean_inc(v_tail_3329_);
lean_dec_ref_known(v_x_3327_, 2);
v___x_3330_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_3325_, v_head_3328_);
if (lean_obj_tag(v___x_3330_) == 1)
{
lean_object* v_val_3331_; lean_object* v___x_3332_; 
v_val_3331_ = lean_ctor_get(v___x_3330_, 0);
lean_inc(v_val_3331_);
lean_dec_ref_known(v___x_3330_, 1);
v___x_3332_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_3328_, v_val_3331_, v_x_3326_);
v_x_3326_ = v___x_3332_;
v_x_3327_ = v_tail_3329_;
goto _start;
}
else
{
lean_dec(v___x_3330_);
lean_dec(v_head_3328_);
v_x_3327_ = v_tail_3329_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg___boxed(lean_object* v_newState_3335_, lean_object* v_x_3336_, lean_object* v_x_3337_){
_start:
{
lean_object* v_res_3338_; 
v_res_3338_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3335_, v_x_3336_, v_x_3337_);
lean_dec(v_newState_3335_);
return v_res_3338_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1(lean_object* v_x_3339_, lean_object* v_newState_3340_, lean_object* v_consts_3341_, lean_object* v_st_3342_){
_start:
{
lean_object* v___x_3343_; 
v___x_3343_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3340_, v_st_3342_, v_consts_3341_);
return v___x_3343_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1___boxed(lean_object* v_x_3344_, lean_object* v_newState_3345_, lean_object* v_consts_3346_, lean_object* v_st_3347_){
_start:
{
lean_object* v_res_3348_; 
v_res_3348_ = l_Lean_registerEnumAttributes___redArg___lam__1(v_x_3344_, v_newState_3345_, v_consts_3346_, v_st_3347_);
lean_dec(v_newState_3345_);
lean_dec(v_x_3344_);
return v_res_3348_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__2(lean_object* v_s_3358_){
_start:
{
lean_object* v___x_3359_; lean_object* v___y_3361_; 
v___x_3359_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___lam__2___closed__3));
if (lean_obj_tag(v_s_3358_) == 0)
{
lean_object* v_size_3365_; 
v_size_3365_ = lean_ctor_get(v_s_3358_, 0);
lean_inc(v_size_3365_);
lean_dec_ref_known(v_s_3358_, 5);
v___y_3361_ = v_size_3365_;
goto v___jp_3360_;
}
else
{
lean_object* v___x_3366_; 
v___x_3366_ = lean_unsigned_to_nat(0u);
v___y_3361_ = v___x_3366_;
goto v___jp_3360_;
}
v___jp_3360_:
{
lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; 
v___x_3362_ = l_Nat_reprFast(v___y_3361_);
v___x_3363_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3363_, 0, v___x_3362_);
v___x_3364_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3359_);
lean_ctor_set(v___x_3364_, 1, v___x_3363_);
return v___x_3364_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(lean_object* v_env_3367_, lean_object* v_as_3368_, size_t v_i_3369_, size_t v_stop_3370_, lean_object* v_b_3371_){
_start:
{
lean_object* v___y_3373_; uint8_t v___x_3377_; 
v___x_3377_ = lean_usize_dec_eq(v_i_3369_, v_stop_3370_);
if (v___x_3377_ == 0)
{
lean_object* v___x_3378_; lean_object* v_fst_3379_; uint8_t v___x_3380_; lean_object* v___x_3381_; uint8_t v___x_3382_; 
v___x_3378_ = lean_array_uget_borrowed(v_as_3368_, v_i_3369_);
v_fst_3379_ = lean_ctor_get(v___x_3378_, 0);
v___x_3380_ = 1;
lean_inc_ref(v_env_3367_);
v___x_3381_ = l_Lean_Environment_setExporting(v_env_3367_, v___x_3380_);
lean_inc(v_fst_3379_);
v___x_3382_ = l_Lean_Environment_contains(v___x_3381_, v_fst_3379_, v___x_3377_);
if (v___x_3382_ == 0)
{
v___y_3373_ = v_b_3371_;
goto v___jp_3372_;
}
else
{
lean_object* v___x_3383_; 
lean_inc(v___x_3378_);
v___x_3383_ = lean_array_push(v_b_3371_, v___x_3378_);
v___y_3373_ = v___x_3383_;
goto v___jp_3372_;
}
}
else
{
lean_dec_ref(v_env_3367_);
return v_b_3371_;
}
v___jp_3372_:
{
size_t v___x_3374_; size_t v___x_3375_; 
v___x_3374_ = ((size_t)1ULL);
v___x_3375_ = lean_usize_add(v_i_3369_, v___x_3374_);
v_i_3369_ = v___x_3375_;
v_b_3371_ = v___y_3373_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg___boxed(lean_object* v_env_3384_, lean_object* v_as_3385_, lean_object* v_i_3386_, lean_object* v_stop_3387_, lean_object* v_b_3388_){
_start:
{
size_t v_i_boxed_3389_; size_t v_stop_boxed_3390_; lean_object* v_res_3391_; 
v_i_boxed_3389_ = lean_unbox_usize(v_i_3386_);
lean_dec(v_i_3386_);
v_stop_boxed_3390_ = lean_unbox_usize(v_stop_3387_);
lean_dec(v_stop_3387_);
v_res_3391_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3384_, v_as_3385_, v_i_boxed_3389_, v_stop_boxed_3390_, v_b_3388_);
lean_dec_ref(v_as_3385_);
return v_res_3391_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3(lean_object* v_env_3392_, lean_object* v_m_3393_){
_start:
{
lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___y_3397_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___y_3414_; lean_object* v___y_3415_; uint8_t v___x_3417_; 
v___x_3394_ = lean_unsigned_to_nat(0u);
v___x_3395_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v___x_3411_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v___x_3395_, v_m_3393_);
v___x_3412_ = lean_array_get_size(v___x_3411_);
v___x_3417_ = lean_nat_dec_eq(v___x_3412_, v___x_3394_);
if (v___x_3417_ == 0)
{
lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___y_3421_; uint8_t v___x_3423_; 
v___x_3418_ = lean_unsigned_to_nat(1u);
v___x_3419_ = lean_nat_sub(v___x_3412_, v___x_3418_);
v___x_3423_ = lean_nat_dec_le(v___x_3394_, v___x_3419_);
if (v___x_3423_ == 0)
{
lean_inc(v___x_3419_);
v___y_3421_ = v___x_3419_;
goto v___jp_3420_;
}
else
{
v___y_3421_ = v___x_3394_;
goto v___jp_3420_;
}
v___jp_3420_:
{
uint8_t v___x_3422_; 
v___x_3422_ = lean_nat_dec_le(v___y_3421_, v___x_3419_);
if (v___x_3422_ == 0)
{
lean_dec(v___x_3419_);
lean_inc(v___y_3421_);
v___y_3414_ = v___y_3421_;
v___y_3415_ = v___y_3421_;
goto v___jp_3413_;
}
else
{
v___y_3414_ = v___y_3421_;
v___y_3415_ = v___x_3419_;
goto v___jp_3413_;
}
}
}
else
{
v___y_3397_ = v___x_3411_;
goto v___jp_3396_;
}
v___jp_3396_:
{
lean_object* v___x_3398_; uint8_t v___x_3399_; 
v___x_3398_ = lean_array_get_size(v___y_3397_);
v___x_3399_ = lean_nat_dec_lt(v___x_3394_, v___x_3398_);
if (v___x_3399_ == 0)
{
lean_object* v___x_3400_; 
lean_dec_ref(v_env_3392_);
v___x_3400_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3400_, 0, v___x_3395_);
lean_ctor_set(v___x_3400_, 1, v___x_3395_);
lean_ctor_set(v___x_3400_, 2, v___y_3397_);
return v___x_3400_;
}
else
{
uint8_t v___x_3401_; 
v___x_3401_ = lean_nat_dec_le(v___x_3398_, v___x_3398_);
if (v___x_3401_ == 0)
{
if (v___x_3399_ == 0)
{
lean_object* v___x_3402_; 
lean_dec_ref(v_env_3392_);
v___x_3402_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3395_);
lean_ctor_set(v___x_3402_, 1, v___x_3395_);
lean_ctor_set(v___x_3402_, 2, v___y_3397_);
return v___x_3402_;
}
else
{
size_t v___x_3403_; size_t v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; 
v___x_3403_ = ((size_t)0ULL);
v___x_3404_ = lean_usize_of_nat(v___x_3398_);
v___x_3405_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3392_, v___y_3397_, v___x_3403_, v___x_3404_, v___x_3395_);
lean_inc_ref(v___x_3405_);
v___x_3406_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3406_, 0, v___x_3405_);
lean_ctor_set(v___x_3406_, 1, v___x_3405_);
lean_ctor_set(v___x_3406_, 2, v___y_3397_);
return v___x_3406_;
}
}
else
{
size_t v___x_3407_; size_t v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3407_ = ((size_t)0ULL);
v___x_3408_ = lean_usize_of_nat(v___x_3398_);
v___x_3409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3392_, v___y_3397_, v___x_3407_, v___x_3408_, v___x_3395_);
lean_inc_ref(v___x_3409_);
v___x_3410_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3410_, 0, v___x_3409_);
lean_ctor_set(v___x_3410_, 1, v___x_3409_);
lean_ctor_set(v___x_3410_, 2, v___y_3397_);
return v___x_3410_;
}
}
}
v___jp_3413_:
{
lean_object* v___x_3416_; 
v___x_3416_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v___x_3412_, v___x_3411_, v___y_3414_, v___y_3415_);
lean_dec(v___y_3415_);
v___y_3397_ = v___x_3416_;
goto v___jp_3396_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3___boxed(lean_object* v_env_3424_, lean_object* v_m_3425_){
_start:
{
lean_object* v_res_3426_; 
v_res_3426_ = l_Lean_registerEnumAttributes___redArg___lam__3(v_env_3424_, v_m_3425_);
lean_dec(v_m_3425_);
return v_res_3426_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__4(lean_object* v_s_3427_, lean_object* v_p_3428_){
_start:
{
lean_object* v_fst_3429_; lean_object* v_snd_3430_; lean_object* v___x_3431_; 
v_fst_3429_ = lean_ctor_get(v_p_3428_, 0);
lean_inc(v_fst_3429_);
v_snd_3430_ = lean_ctor_get(v_p_3428_, 1);
lean_inc(v_snd_3430_);
lean_dec_ref(v_p_3428_);
v___x_3431_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3429_, v_snd_3430_, v_s_3427_);
return v___x_3431_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6(lean_object* v___x_3432_, lean_object* v_x_3433_, lean_object* v_x_3434_){
_start:
{
lean_object* v___x_3436_; 
v___x_3436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3432_);
return v___x_3436_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6___boxed(lean_object* v___x_3437_, lean_object* v_x_3438_, lean_object* v_x_3439_, lean_object* v___y_3440_){
_start:
{
lean_object* v_res_3441_; 
v_res_3441_ = l_Lean_registerEnumAttributes___redArg___lam__6(v___x_3437_, v_x_3438_, v_x_3439_);
lean_dec_ref(v_x_3439_);
lean_dec_ref(v_x_3438_);
return v_res_3441_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3(lean_object* v_as_3442_){
_start:
{
if (lean_obj_tag(v_as_3442_) == 0)
{
lean_object* v___x_3444_; lean_object* v___x_3445_; 
v___x_3444_ = lean_box(0);
v___x_3445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3445_, 0, v___x_3444_);
return v___x_3445_;
}
else
{
lean_object* v_head_3446_; lean_object* v_tail_3447_; lean_object* v___x_3448_; 
v_head_3446_ = lean_ctor_get(v_as_3442_, 0);
lean_inc(v_head_3446_);
v_tail_3447_ = lean_ctor_get(v_as_3442_, 1);
lean_inc(v_tail_3447_);
lean_dec_ref_known(v_as_3442_, 2);
v___x_3448_ = l_Lean_registerBuiltinAttribute(v_head_3446_);
if (lean_obj_tag(v___x_3448_) == 0)
{
lean_dec_ref_known(v___x_3448_, 1);
v_as_3442_ = v_tail_3447_;
goto _start;
}
else
{
lean_dec(v_tail_3447_);
return v___x_3448_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3___boxed(lean_object* v_as_3450_, lean_object* v___y_3451_){
_start:
{
lean_object* v_res_3452_; 
v_res_3452_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v_as_3450_);
return v_res_3452_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(lean_object* v_validate_3453_, lean_object* v_snd_3454_, lean_object* v_a_3455_, lean_object* v_fst_3456_, lean_object* v_decl_3457_, lean_object* v_stx_3458_, uint8_t v_kind_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_){
_start:
{
lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v___x_3505_; 
v___x_3505_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_3458_, v___y_3460_, v___y_3461_);
if (lean_obj_tag(v___x_3505_) == 0)
{
uint8_t v___x_3506_; uint8_t v___x_3507_; 
lean_dec_ref_known(v___x_3505_, 1);
v___x_3506_ = 0;
v___x_3507_ = l_Lean_instBEqAttributeKind_beq(v_kind_3459_, v___x_3506_);
if (v___x_3507_ == 0)
{
lean_object* v___x_3508_; 
lean_dec(v_decl_3457_);
lean_dec_ref(v_a_3455_);
lean_dec(v_snd_3454_);
lean_dec_ref(v_validate_3453_);
v___x_3508_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_fst_3456_, v_kind_3459_, v___y_3460_, v___y_3461_);
return v___x_3508_;
}
else
{
goto v___jp_3500_;
}
}
else
{
lean_dec(v_decl_3457_);
lean_dec(v_fst_3456_);
lean_dec_ref(v_a_3455_);
lean_dec(v_snd_3454_);
lean_dec_ref(v_validate_3453_);
return v___x_3505_;
}
v___jp_3463_:
{
lean_object* v___x_3466_; 
lean_inc(v___y_3465_);
lean_inc_ref(v___y_3464_);
lean_inc(v_snd_3454_);
lean_inc(v_decl_3457_);
v___x_3466_ = lean_apply_5(v_validate_3453_, v_decl_3457_, v_snd_3454_, v___y_3464_, v___y_3465_, lean_box(0));
if (lean_obj_tag(v___x_3466_) == 0)
{
lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3498_; 
v_isSharedCheck_3498_ = !lean_is_exclusive(v___x_3466_);
if (v_isSharedCheck_3498_ == 0)
{
lean_object* v_unused_3499_; 
v_unused_3499_ = lean_ctor_get(v___x_3466_, 0);
lean_dec(v_unused_3499_);
v___x_3468_ = v___x_3466_;
v_isShared_3469_ = v_isSharedCheck_3498_;
goto v_resetjp_3467_;
}
else
{
lean_dec(v___x_3466_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3498_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
lean_object* v___x_3470_; lean_object* v_toEnvExtension_3471_; lean_object* v_env_3472_; lean_object* v_nextMacroScope_3473_; lean_object* v_ngen_3474_; lean_object* v_auxDeclNGen_3475_; lean_object* v_traceState_3476_; lean_object* v_recordedDeps_3477_; lean_object* v_messages_3478_; lean_object* v_infoState_3479_; lean_object* v_snapshotTasks_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3496_; 
v___x_3470_ = lean_st_ref_take(v___y_3465_);
v_toEnvExtension_3471_ = lean_ctor_get(v_a_3455_, 0);
v_env_3472_ = lean_ctor_get(v___x_3470_, 0);
v_nextMacroScope_3473_ = lean_ctor_get(v___x_3470_, 1);
v_ngen_3474_ = lean_ctor_get(v___x_3470_, 2);
v_auxDeclNGen_3475_ = lean_ctor_get(v___x_3470_, 3);
v_traceState_3476_ = lean_ctor_get(v___x_3470_, 4);
v_recordedDeps_3477_ = lean_ctor_get(v___x_3470_, 6);
v_messages_3478_ = lean_ctor_get(v___x_3470_, 7);
v_infoState_3479_ = lean_ctor_get(v___x_3470_, 8);
v_snapshotTasks_3480_ = lean_ctor_get(v___x_3470_, 9);
v_isSharedCheck_3496_ = !lean_is_exclusive(v___x_3470_);
if (v_isSharedCheck_3496_ == 0)
{
lean_object* v_unused_3497_; 
v_unused_3497_ = lean_ctor_get(v___x_3470_, 5);
lean_dec(v_unused_3497_);
v___x_3482_ = v___x_3470_;
v_isShared_3483_ = v_isSharedCheck_3496_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_snapshotTasks_3480_);
lean_inc(v_infoState_3479_);
lean_inc(v_messages_3478_);
lean_inc(v_recordedDeps_3477_);
lean_inc(v_traceState_3476_);
lean_inc(v_auxDeclNGen_3475_);
lean_inc(v_ngen_3474_);
lean_inc(v_nextMacroScope_3473_);
lean_inc(v_env_3472_);
lean_dec(v___x_3470_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3496_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v_asyncMode_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3490_; 
v_asyncMode_3484_ = lean_ctor_get(v_toEnvExtension_3471_, 2);
lean_inc(v_asyncMode_3484_);
v___x_3485_ = lean_box(0);
lean_inc(v_decl_3457_);
v___x_3486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3486_, 0, v_decl_3457_);
lean_ctor_set(v___x_3486_, 1, v_snd_3454_);
v___x_3487_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_3455_, v_env_3472_, v___x_3486_, v_asyncMode_3484_, v_decl_3457_);
lean_dec(v_asyncMode_3484_);
v___x_3488_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
if (v_isShared_3483_ == 0)
{
lean_ctor_set(v___x_3482_, 5, v___x_3488_);
lean_ctor_set(v___x_3482_, 0, v___x_3487_);
v___x_3490_ = v___x_3482_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v___x_3487_);
lean_ctor_set(v_reuseFailAlloc_3495_, 1, v_nextMacroScope_3473_);
lean_ctor_set(v_reuseFailAlloc_3495_, 2, v_ngen_3474_);
lean_ctor_set(v_reuseFailAlloc_3495_, 3, v_auxDeclNGen_3475_);
lean_ctor_set(v_reuseFailAlloc_3495_, 4, v_traceState_3476_);
lean_ctor_set(v_reuseFailAlloc_3495_, 5, v___x_3488_);
lean_ctor_set(v_reuseFailAlloc_3495_, 6, v_recordedDeps_3477_);
lean_ctor_set(v_reuseFailAlloc_3495_, 7, v_messages_3478_);
lean_ctor_set(v_reuseFailAlloc_3495_, 8, v_infoState_3479_);
lean_ctor_set(v_reuseFailAlloc_3495_, 9, v_snapshotTasks_3480_);
v___x_3490_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
lean_object* v___x_3491_; lean_object* v___x_3493_; 
v___x_3491_ = lean_st_ref_put(v___y_3465_, v___x_3490_);
if (v_isShared_3469_ == 0)
{
lean_ctor_set(v___x_3468_, 0, v___x_3485_);
v___x_3493_ = v___x_3468_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v___x_3485_);
v___x_3493_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
return v___x_3493_;
}
}
}
}
}
else
{
lean_dec(v_decl_3457_);
lean_dec_ref(v_a_3455_);
lean_dec(v_snd_3454_);
return v___x_3466_;
}
}
v___jp_3500_:
{
lean_object* v___x_3501_; lean_object* v_env_3502_; lean_object* v___x_3503_; 
v___x_3501_ = lean_st_ref_get(v___y_3461_);
v_env_3502_ = lean_ctor_get(v___x_3501_, 0);
lean_inc_ref(v_env_3502_);
lean_dec(v___x_3501_);
v___x_3503_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3502_, v_decl_3457_);
lean_dec_ref(v_env_3502_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_dec(v_fst_3456_);
v___y_3464_ = v___y_3460_;
v___y_3465_ = v___y_3461_;
goto v___jp_3463_;
}
else
{
lean_object* v___x_3504_; 
lean_dec_ref_known(v___x_3503_, 1);
lean_dec_ref(v_a_3455_);
lean_dec(v_snd_3454_);
lean_dec_ref(v_validate_3453_);
v___x_3504_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_fst_3456_, v_decl_3457_, v___y_3460_, v___y_3461_);
return v___x_3504_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed(lean_object* v_validate_3509_, lean_object* v_snd_3510_, lean_object* v_a_3511_, lean_object* v_fst_3512_, lean_object* v_decl_3513_, lean_object* v_stx_3514_, lean_object* v_kind_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_){
_start:
{
uint8_t v_kind_boxed_3519_; lean_object* v_res_3520_; 
v_kind_boxed_3519_ = lean_unbox(v_kind_3515_);
v_res_3520_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(v_validate_3509_, v_snd_3510_, v_a_3511_, v_fst_3512_, v_decl_3513_, v_stx_3514_, v_kind_boxed_3519_, v___y_3516_, v___y_3517_);
lean_dec(v___y_3517_);
lean_dec_ref(v___y_3516_);
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(lean_object* v_fst_3521_, lean_object* v_decl_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_){
_start:
{
lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; 
v___x_3526_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_3527_ = l_Lean_MessageData_ofName(v_fst_3521_);
v___x_3528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3528_, 0, v___x_3526_);
lean_ctor_set(v___x_3528_, 1, v___x_3527_);
v___x_3529_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_3530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3530_, 0, v___x_3528_);
lean_ctor_set(v___x_3530_, 1, v___x_3529_);
v___x_3531_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_3530_, v___y_3523_, v___y_3524_);
return v___x_3531_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed(lean_object* v_fst_3532_, lean_object* v_decl_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_){
_start:
{
lean_object* v_res_3537_; 
v_res_3537_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(v_fst_3532_, v_decl_3533_, v___y_3534_, v___y_3535_);
lean_dec(v___y_3535_);
lean_dec_ref(v___y_3534_);
lean_dec(v_decl_3533_);
return v_res_3537_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(lean_object* v_validate_3538_, lean_object* v_a_3539_, lean_object* v_ref_3540_, uint8_t v_applicationTime_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_){
_start:
{
if (lean_obj_tag(v_a_3542_) == 0)
{
lean_object* v___x_3544_; 
lean_dec(v_ref_3540_);
lean_dec_ref(v_a_3539_);
lean_dec_ref(v_validate_3538_);
v___x_3544_ = l_List_reverse___redArg(v_a_3543_);
return v___x_3544_;
}
else
{
lean_object* v_head_3545_; lean_object* v_snd_3546_; lean_object* v_tail_3547_; lean_object* v___x_3549_; uint8_t v_isShared_3550_; uint8_t v_isSharedCheck_3562_; 
v_head_3545_ = lean_ctor_get(v_a_3542_, 0);
lean_inc(v_head_3545_);
v_snd_3546_ = lean_ctor_get(v_head_3545_, 1);
lean_inc(v_snd_3546_);
v_tail_3547_ = lean_ctor_get(v_a_3542_, 1);
v_isSharedCheck_3562_ = !lean_is_exclusive(v_a_3542_);
if (v_isSharedCheck_3562_ == 0)
{
lean_object* v_unused_3563_; 
v_unused_3563_ = lean_ctor_get(v_a_3542_, 0);
lean_dec(v_unused_3563_);
v___x_3549_ = v_a_3542_;
v_isShared_3550_ = v_isSharedCheck_3562_;
goto v_resetjp_3548_;
}
else
{
lean_inc(v_tail_3547_);
lean_dec(v_a_3542_);
v___x_3549_ = lean_box(0);
v_isShared_3550_ = v_isSharedCheck_3562_;
goto v_resetjp_3548_;
}
v_resetjp_3548_:
{
lean_object* v_fst_3551_; lean_object* v_fst_3552_; lean_object* v_snd_3553_; lean_object* v___f_3554_; lean_object* v___f_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3559_; 
v_fst_3551_ = lean_ctor_get(v_head_3545_, 0);
lean_inc_n(v_fst_3551_, 3);
lean_dec(v_head_3545_);
v_fst_3552_ = lean_ctor_get(v_snd_3546_, 0);
lean_inc(v_fst_3552_);
v_snd_3553_ = lean_ctor_get(v_snd_3546_, 1);
lean_inc(v_snd_3553_);
lean_dec(v_snd_3546_);
v___f_3554_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3554_, 0, v_fst_3551_);
lean_inc_ref(v_a_3539_);
lean_inc_ref(v_validate_3538_);
v___f_3555_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3555_, 0, v_validate_3538_);
lean_closure_set(v___f_3555_, 1, v_snd_3553_);
lean_closure_set(v___f_3555_, 2, v_a_3539_);
lean_closure_set(v___f_3555_, 3, v_fst_3551_);
lean_inc(v_ref_3540_);
v___x_3556_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3556_, 0, v_ref_3540_);
lean_ctor_set(v___x_3556_, 1, v_fst_3551_);
lean_ctor_set(v___x_3556_, 2, v_fst_3552_);
lean_ctor_set_uint8(v___x_3556_, sizeof(void*)*3, v_applicationTime_3541_);
v___x_3557_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3556_);
lean_ctor_set(v___x_3557_, 1, v___f_3555_);
lean_ctor_set(v___x_3557_, 2, v___f_3554_);
if (v_isShared_3550_ == 0)
{
lean_ctor_set(v___x_3549_, 1, v_a_3543_);
lean_ctor_set(v___x_3549_, 0, v___x_3557_);
v___x_3559_ = v___x_3549_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v___x_3557_);
lean_ctor_set(v_reuseFailAlloc_3561_, 1, v_a_3543_);
v___x_3559_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
v_a_3542_ = v_tail_3547_;
v_a_3543_ = v___x_3559_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___boxed(lean_object* v_validate_3564_, lean_object* v_a_3565_, lean_object* v_ref_3566_, lean_object* v_applicationTime_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_){
_start:
{
uint8_t v_applicationTime_boxed_3570_; lean_object* v_res_3571_; 
v_applicationTime_boxed_3570_ = lean_unbox(v_applicationTime_3567_);
v_res_3571_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3564_, v_a_3565_, v_ref_3566_, v_applicationTime_boxed_3570_, v_a_3568_, v_a_3569_);
return v_res_3571_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg(lean_object* v_attrDescrs_3585_, lean_object* v_validate_3586_, uint8_t v_applicationTime_3587_, lean_object* v_ref_3588_){
_start:
{
lean_object* v___f_3590_; lean_object* v___f_3591_; lean_object* v___f_3592_; lean_object* v___f_3593_; lean_object* v___f_3594_; lean_object* v___f_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; uint8_t v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; 
v___f_3590_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__0));
v___f_3591_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__2));
v___f_3592_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__3));
v___f_3593_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__4));
v___f_3594_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__5));
v___f_3595_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__6));
v___x_3596_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__7));
v___x_3597_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__8));
v___x_3598_ = 0;
lean_inc(v_ref_3588_);
v___x_3599_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_3599_, 0, v_ref_3588_);
lean_ctor_set(v___x_3599_, 1, v___f_3594_);
lean_ctor_set(v___x_3599_, 2, v___f_3595_);
lean_ctor_set(v___x_3599_, 3, v___f_3593_);
lean_ctor_set(v___x_3599_, 4, v___f_3592_);
lean_ctor_set(v___x_3599_, 5, v___f_3591_);
lean_ctor_set(v___x_3599_, 6, v___x_3596_);
lean_ctor_set(v___x_3599_, 7, v___x_3597_);
lean_ctor_set_uint8(v___x_3599_, sizeof(void*)*8, v___x_3598_);
v___x_3600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3600_, 0, v___x_3599_);
lean_ctor_set(v___x_3600_, 1, v___f_3590_);
v___x_3601_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3600_);
if (lean_obj_tag(v___x_3601_) == 0)
{
lean_object* v_a_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; 
v_a_3602_ = lean_ctor_get(v___x_3601_, 0);
lean_inc_n(v_a_3602_, 2);
lean_dec_ref_known(v___x_3601_, 1);
v___x_3603_ = lean_box(0);
v___x_3604_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3586_, v_a_3602_, v_ref_3588_, v_applicationTime_3587_, v_attrDescrs_3585_, v___x_3603_);
lean_inc(v___x_3604_);
v___x_3605_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v___x_3604_);
if (lean_obj_tag(v___x_3605_) == 0)
{
lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3613_; 
v_isSharedCheck_3613_ = !lean_is_exclusive(v___x_3605_);
if (v_isSharedCheck_3613_ == 0)
{
lean_object* v_unused_3614_; 
v_unused_3614_ = lean_ctor_get(v___x_3605_, 0);
lean_dec(v_unused_3614_);
v___x_3607_ = v___x_3605_;
v_isShared_3608_ = v_isSharedCheck_3613_;
goto v_resetjp_3606_;
}
else
{
lean_dec(v___x_3605_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3613_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
lean_object* v___x_3609_; lean_object* v___x_3611_; 
v___x_3609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3604_);
lean_ctor_set(v___x_3609_, 1, v_a_3602_);
if (v_isShared_3608_ == 0)
{
lean_ctor_set(v___x_3607_, 0, v___x_3609_);
v___x_3611_ = v___x_3607_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v___x_3609_);
v___x_3611_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
return v___x_3611_;
}
}
}
else
{
lean_object* v_a_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3622_; 
lean_dec(v___x_3604_);
lean_dec(v_a_3602_);
v_a_3615_ = lean_ctor_get(v___x_3605_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v___x_3605_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3617_ = v___x_3605_;
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_a_3615_);
lean_dec(v___x_3605_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
lean_object* v___x_3620_; 
if (v_isShared_3618_ == 0)
{
v___x_3620_ = v___x_3617_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_a_3615_);
v___x_3620_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
return v___x_3620_;
}
}
}
}
else
{
lean_object* v_a_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3630_; 
lean_dec(v_ref_3588_);
lean_dec_ref(v_validate_3586_);
lean_dec(v_attrDescrs_3585_);
v_a_3623_ = lean_ctor_get(v___x_3601_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3625_ = v___x_3601_;
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_a_3623_);
lean_dec(v___x_3601_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
lean_object* v___x_3628_; 
if (v_isShared_3626_ == 0)
{
v___x_3628_ = v___x_3625_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v_a_3623_);
v___x_3628_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
return v___x_3628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___boxed(lean_object* v_attrDescrs_3631_, lean_object* v_validate_3632_, lean_object* v_applicationTime_3633_, lean_object* v_ref_3634_, lean_object* v_a_3635_){
_start:
{
uint8_t v_applicationTime_boxed_3636_; lean_object* v_res_3637_; 
v_applicationTime_boxed_3636_ = lean_unbox(v_applicationTime_3633_);
v_res_3637_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3631_, v_validate_3632_, v_applicationTime_boxed_3636_, v_ref_3634_);
return v_res_3637_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes(lean_object* v_00_u03b1_3638_, lean_object* v_attrDescrs_3639_, lean_object* v_validate_3640_, uint8_t v_applicationTime_3641_, lean_object* v_ref_3642_){
_start:
{
lean_object* v___x_3644_; 
v___x_3644_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3639_, v_validate_3640_, v_applicationTime_3641_, v_ref_3642_);
return v___x_3644_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___boxed(lean_object* v_00_u03b1_3645_, lean_object* v_attrDescrs_3646_, lean_object* v_validate_3647_, lean_object* v_applicationTime_3648_, lean_object* v_ref_3649_, lean_object* v_a_3650_){
_start:
{
uint8_t v_applicationTime_boxed_3651_; lean_object* v_res_3652_; 
v_applicationTime_boxed_3651_ = lean_unbox(v_applicationTime_3648_);
v_res_3652_ = l_Lean_registerEnumAttributes(v_00_u03b1_3645_, v_attrDescrs_3646_, v_validate_3647_, v_applicationTime_boxed_3651_, v_ref_3649_);
return v_res_3652_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(lean_object* v_00_u03b1_3653_, lean_object* v_env_3654_, lean_object* v_as_3655_, size_t v_i_3656_, size_t v_stop_3657_, lean_object* v_b_3658_){
_start:
{
lean_object* v___x_3659_; 
v___x_3659_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3654_, v_as_3655_, v_i_3656_, v_stop_3657_, v_b_3658_);
return v___x_3659_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___boxed(lean_object* v_00_u03b1_3660_, lean_object* v_env_3661_, lean_object* v_as_3662_, lean_object* v_i_3663_, lean_object* v_stop_3664_, lean_object* v_b_3665_){
_start:
{
size_t v_i_boxed_3666_; size_t v_stop_boxed_3667_; lean_object* v_res_3668_; 
v_i_boxed_3666_ = lean_unbox_usize(v_i_3663_);
lean_dec(v_i_3663_);
v_stop_boxed_3667_ = lean_unbox_usize(v_stop_3664_);
lean_dec(v_stop_3664_);
v_res_3668_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(v_00_u03b1_3660_, v_env_3661_, v_as_3662_, v_i_boxed_3666_, v_stop_boxed_3667_, v_b_3665_);
lean_dec_ref(v_as_3662_);
return v_res_3668_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(lean_object* v_00_u03b1_3669_, lean_object* v_newState_3670_, lean_object* v_x_3671_, lean_object* v_x_3672_){
_start:
{
lean_object* v___x_3673_; 
v___x_3673_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3670_, v_x_3671_, v_x_3672_);
return v___x_3673_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___boxed(lean_object* v_00_u03b1_3674_, lean_object* v_newState_3675_, lean_object* v_x_3676_, lean_object* v_x_3677_){
_start:
{
lean_object* v_res_3678_; 
v_res_3678_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(v_00_u03b1_3674_, v_newState_3675_, v_x_3676_, v_x_3677_);
lean_dec(v_newState_3675_);
return v_res_3678_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(lean_object* v_00_u03b1_3679_, lean_object* v_validate_3680_, lean_object* v_a_3681_, lean_object* v_ref_3682_, uint8_t v_applicationTime_3683_, lean_object* v_a_3684_, lean_object* v_a_3685_){
_start:
{
lean_object* v___x_3686_; 
v___x_3686_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3680_, v_a_3681_, v_ref_3682_, v_applicationTime_3683_, v_a_3684_, v_a_3685_);
return v___x_3686_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___boxed(lean_object* v_00_u03b1_3687_, lean_object* v_validate_3688_, lean_object* v_a_3689_, lean_object* v_ref_3690_, lean_object* v_applicationTime_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_){
_start:
{
uint8_t v_applicationTime_boxed_3694_; lean_object* v_res_3695_; 
v_applicationTime_boxed_3694_ = lean_unbox(v_applicationTime_3691_);
v_res_3695_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(v_00_u03b1_3687_, v_validate_3688_, v_a_3689_, v_ref_3690_, v_applicationTime_boxed_3694_, v_a_3692_, v_a_3693_);
return v_res_3695_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue___redArg(lean_object* v_inst_3696_, lean_object* v_attr_3697_, lean_object* v_env_3698_, lean_object* v_decl_3699_){
_start:
{
lean_object* v___x_3700_; lean_object* v___x_3701_; 
v___x_3700_ = lean_box(1);
v___x_3701_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3698_, v_decl_3699_);
if (lean_obj_tag(v___x_3701_) == 0)
{
lean_object* v_ext_3702_; lean_object* v_toEnvExtension_3703_; lean_object* v_asyncMode_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; 
lean_dec(v_inst_3696_);
v_ext_3702_ = lean_ctor_get(v_attr_3697_, 1);
lean_inc_ref(v_ext_3702_);
lean_dec_ref(v_attr_3697_);
v_toEnvExtension_3703_ = lean_ctor_get(v_ext_3702_, 0);
v_asyncMode_3704_ = lean_ctor_get(v_toEnvExtension_3703_, 2);
lean_inc(v_asyncMode_3704_);
lean_inc(v_decl_3699_);
v___x_3705_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3700_, v_ext_3702_, v_env_3698_, v_asyncMode_3704_, v_decl_3699_);
lean_dec(v_asyncMode_3704_);
lean_dec_ref(v_ext_3702_);
v___x_3706_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3705_, v_decl_3699_);
lean_dec(v_decl_3699_);
lean_dec(v___x_3705_);
return v___x_3706_;
}
else
{
lean_object* v_val_3707_; lean_object* v_ext_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3738_; 
v_val_3707_ = lean_ctor_get(v___x_3701_, 0);
lean_inc(v_val_3707_);
lean_dec_ref_known(v___x_3701_, 1);
v_ext_3708_ = lean_ctor_get(v_attr_3697_, 1);
v_isSharedCheck_3738_ = !lean_is_exclusive(v_attr_3697_);
if (v_isSharedCheck_3738_ == 0)
{
lean_object* v_unused_3739_; 
v_unused_3739_ = lean_ctor_get(v_attr_3697_, 0);
lean_dec(v_unused_3739_);
v___x_3710_ = v_attr_3697_;
v_isShared_3711_ = v_isSharedCheck_3738_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_ext_3708_);
lean_dec(v_attr_3697_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3738_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
uint8_t v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; uint8_t v___x_3716_; 
v___x_3712_ = 0;
v___x_3713_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3700_, v_ext_3708_, v_env_3698_, v_val_3707_, v___x_3712_);
lean_dec(v_val_3707_);
lean_dec_ref(v_env_3698_);
lean_dec_ref(v_ext_3708_);
v___x_3714_ = lean_unsigned_to_nat(0u);
v___x_3715_ = lean_array_get_size(v___x_3713_);
v___x_3716_ = lean_nat_dec_lt(v___x_3714_, v___x_3715_);
if (v___x_3716_ == 0)
{
lean_object* v___x_3717_; 
lean_dec_ref(v___x_3713_);
lean_del_object(v___x_3710_);
lean_dec(v_decl_3699_);
lean_dec(v_inst_3696_);
v___x_3717_ = lean_box(0);
return v___x_3717_;
}
else
{
lean_object* v___x_3718_; lean_object* v___x_3719_; uint8_t v___x_3720_; 
v___x_3718_ = lean_unsigned_to_nat(1u);
v___x_3719_ = lean_nat_sub(v___x_3715_, v___x_3718_);
v___x_3720_ = lean_nat_dec_le(v___x_3714_, v___x_3719_);
if (v___x_3720_ == 0)
{
lean_object* v___x_3721_; 
lean_dec(v___x_3719_);
lean_dec_ref(v___x_3713_);
lean_del_object(v___x_3710_);
lean_dec(v_decl_3699_);
lean_dec(v_inst_3696_);
v___x_3721_ = lean_box(0);
return v___x_3721_;
}
else
{
lean_object* v___f_3722_; lean_object* v___x_3724_; 
v___f_3722_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1));
if (v_isShared_3711_ == 0)
{
lean_ctor_set(v___x_3710_, 1, v_inst_3696_);
lean_ctor_set(v___x_3710_, 0, v_decl_3699_);
v___x_3724_ = v___x_3710_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v_decl_3699_);
lean_ctor_set(v_reuseFailAlloc_3737_, 1, v_inst_3696_);
v___x_3724_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
lean_object* v___x_3725_; lean_object* v___x_3726_; 
v___x_3725_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2));
v___x_3726_ = l_Array_binSearchAux___redArg(v___f_3722_, v___x_3725_, v___x_3713_, v___x_3724_, v___x_3714_, v___x_3719_);
lean_dec_ref(v___x_3713_);
if (lean_obj_tag(v___x_3726_) == 0)
{
lean_object* v___x_3727_; 
v___x_3727_ = lean_box(0);
return v___x_3727_;
}
else
{
lean_object* v_val_3728_; lean_object* v___x_3730_; uint8_t v_isShared_3731_; uint8_t v_isSharedCheck_3736_; 
v_val_3728_ = lean_ctor_get(v___x_3726_, 0);
v_isSharedCheck_3736_ = !lean_is_exclusive(v___x_3726_);
if (v_isSharedCheck_3736_ == 0)
{
v___x_3730_ = v___x_3726_;
v_isShared_3731_ = v_isSharedCheck_3736_;
goto v_resetjp_3729_;
}
else
{
lean_inc(v_val_3728_);
lean_dec(v___x_3726_);
v___x_3730_ = lean_box(0);
v_isShared_3731_ = v_isSharedCheck_3736_;
goto v_resetjp_3729_;
}
v_resetjp_3729_:
{
lean_object* v_snd_3732_; lean_object* v___x_3734_; 
v_snd_3732_ = lean_ctor_get(v_val_3728_, 1);
lean_inc(v_snd_3732_);
lean_dec(v_val_3728_);
if (v_isShared_3731_ == 0)
{
lean_ctor_set(v___x_3730_, 0, v_snd_3732_);
v___x_3734_ = v___x_3730_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v_snd_3732_);
v___x_3734_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3733_;
}
v_reusejp_3733_:
{
return v___x_3734_;
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
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue(lean_object* v_00_u03b1_3740_, lean_object* v_inst_3741_, lean_object* v_attr_3742_, lean_object* v_env_3743_, lean_object* v_decl_3744_){
_start:
{
lean_object* v___x_3745_; 
v___x_3745_ = l_Lean_EnumAttributes_getValue___redArg(v_inst_3741_, v_attr_3742_, v_env_3743_, v_decl_3744_);
return v___x_3745_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue___redArg(lean_object* v_attrs_3754_, lean_object* v_env_3755_, lean_object* v_decl_3756_, lean_object* v_val_3757_){
_start:
{
lean_object* v_ext_3758_; lean_object* v___x_3760_; uint8_t v_isShared_3761_; uint8_t v_isSharedCheck_3821_; 
v_ext_3758_ = lean_ctor_get(v_attrs_3754_, 1);
v_isSharedCheck_3821_ = !lean_is_exclusive(v_attrs_3754_);
if (v_isSharedCheck_3821_ == 0)
{
lean_object* v_unused_3822_; 
v_unused_3822_ = lean_ctor_get(v_attrs_3754_, 0);
lean_dec(v_unused_3822_);
v___x_3760_ = v_attrs_3754_;
v_isShared_3761_ = v_isSharedCheck_3821_;
goto v_resetjp_3759_;
}
else
{
lean_inc(v_ext_3758_);
lean_dec(v_attrs_3754_);
v___x_3760_ = lean_box(0);
v_isShared_3761_ = v_isSharedCheck_3821_;
goto v_resetjp_3759_;
}
v_resetjp_3759_:
{
lean_object* v_toEnvExtension_3762_; lean_object* v_name_3763_; lean_object* v___x_3764_; uint8_t v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v_pfx_3773_; lean_object* v___x_3774_; 
v_toEnvExtension_3762_ = lean_ctor_get(v_ext_3758_, 0);
v_name_3763_ = lean_ctor_get(v_ext_3758_, 1);
v___x_3764_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__0));
v___x_3765_ = 1;
lean_inc(v_name_3763_);
v___x_3766_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3763_, v___x_3765_);
v___x_3767_ = lean_string_append(v___x_3764_, v___x_3766_);
lean_dec_ref(v___x_3766_);
v___x_3768_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__1));
v___x_3769_ = lean_string_append(v___x_3767_, v___x_3768_);
lean_inc(v_decl_3756_);
v___x_3770_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3756_, v___x_3765_);
v___x_3771_ = lean_string_append(v___x_3769_, v___x_3770_);
lean_dec_ref(v___x_3770_);
v___x_3772_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v_pfx_3773_ = lean_string_append(v___x_3771_, v___x_3772_);
v___x_3774_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3755_, v_decl_3756_);
if (lean_obj_tag(v___x_3774_) == 0)
{
lean_object* v_asyncMode_3775_; uint8_t v___x_3776_; 
v_asyncMode_3775_ = lean_ctor_get(v_toEnvExtension_3762_, 2);
lean_inc(v_asyncMode_3775_);
lean_inc(v_decl_3756_);
lean_inc_ref(v_env_3755_);
v___x_3776_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_3755_, v_decl_3756_, v_asyncMode_3775_);
if (v___x_3776_ == 0)
{
lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___y_3780_; lean_object* v___x_3784_; 
lean_dec(v_asyncMode_3775_);
lean_del_object(v___x_3760_);
lean_dec_ref(v_ext_3758_);
lean_dec(v_val_3757_);
lean_dec(v_decl_3756_);
v___x_3777_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__2));
v___x_3778_ = lean_string_append(v_pfx_3773_, v___x_3777_);
v___x_3784_ = l_Lean_Environment_asyncPrefix_x3f(v_env_3755_);
if (lean_obj_tag(v___x_3784_) == 0)
{
lean_object* v___x_3785_; 
v___x_3785_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__3));
v___y_3780_ = v___x_3785_;
goto v___jp_3779_;
}
else
{
lean_object* v_val_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; 
v_val_3786_ = lean_ctor_get(v___x_3784_, 0);
lean_inc(v_val_3786_);
lean_dec_ref_known(v___x_3784_, 1);
v___x_3787_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__4));
v___x_3788_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3786_, v___x_3765_);
v___x_3789_ = l_addParenHeuristic(v___x_3788_);
v___x_3790_ = lean_string_append(v___x_3787_, v___x_3789_);
lean_dec_ref(v___x_3789_);
v___x_3791_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__5));
v___x_3792_ = lean_string_append(v___x_3790_, v___x_3791_);
v___y_3780_ = v___x_3792_;
goto v___jp_3779_;
}
v___jp_3779_:
{
lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; 
v___x_3781_ = lean_string_append(v___x_3778_, v___y_3780_);
lean_dec_ref(v___y_3780_);
v___x_3782_ = lean_string_append(v___x_3781_, v___x_3772_);
v___x_3783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3783_, 0, v___x_3782_);
return v___x_3783_;
}
}
else
{
lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; 
v___x_3793_ = lean_box(1);
lean_inc(v_decl_3756_);
lean_inc_ref(v_env_3755_);
v___x_3794_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3793_, v_ext_3758_, v_env_3755_, v_asyncMode_3775_, v_decl_3756_);
v___x_3795_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3794_, v_decl_3756_);
lean_dec(v___x_3794_);
if (lean_obj_tag(v___x_3795_) == 0)
{
lean_object* v___x_3797_; 
lean_dec_ref(v_pfx_3773_);
lean_inc(v_decl_3756_);
if (v_isShared_3761_ == 0)
{
lean_ctor_set(v___x_3760_, 1, v_val_3757_);
lean_ctor_set(v___x_3760_, 0, v_decl_3756_);
v___x_3797_ = v___x_3760_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v_decl_3756_);
lean_ctor_set(v_reuseFailAlloc_3800_, 1, v_val_3757_);
v___x_3797_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
lean_object* v___x_3798_; lean_object* v___x_3799_; 
v___x_3798_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_3758_, v_env_3755_, v___x_3797_, v_asyncMode_3775_, v_decl_3756_);
lean_dec(v_asyncMode_3775_);
v___x_3799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3799_, 0, v___x_3798_);
return v___x_3799_;
}
}
else
{
lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3809_; 
lean_dec(v_asyncMode_3775_);
lean_del_object(v___x_3760_);
lean_dec_ref(v_ext_3758_);
lean_dec(v_val_3757_);
lean_dec(v_decl_3756_);
lean_dec_ref(v_env_3755_);
v_isSharedCheck_3809_ = !lean_is_exclusive(v___x_3795_);
if (v_isSharedCheck_3809_ == 0)
{
lean_object* v_unused_3810_; 
v_unused_3810_ = lean_ctor_get(v___x_3795_, 0);
lean_dec(v_unused_3810_);
v___x_3802_ = v___x_3795_;
v_isShared_3803_ = v_isSharedCheck_3809_;
goto v_resetjp_3801_;
}
else
{
lean_dec(v___x_3795_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3809_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3807_; 
v___x_3804_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__6));
v___x_3805_ = lean_string_append(v_pfx_3773_, v___x_3804_);
if (v_isShared_3803_ == 0)
{
lean_ctor_set_tag(v___x_3802_, 0);
lean_ctor_set(v___x_3802_, 0, v___x_3805_);
v___x_3807_ = v___x_3802_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v___x_3805_);
v___x_3807_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
return v___x_3807_;
}
}
}
}
}
else
{
lean_object* v___x_3812_; uint8_t v_isShared_3813_; uint8_t v_isSharedCheck_3819_; 
lean_del_object(v___x_3760_);
lean_dec_ref(v_ext_3758_);
lean_dec(v_val_3757_);
lean_dec(v_decl_3756_);
lean_dec_ref(v_env_3755_);
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3774_);
if (v_isSharedCheck_3819_ == 0)
{
lean_object* v_unused_3820_; 
v_unused_3820_ = lean_ctor_get(v___x_3774_, 0);
lean_dec(v_unused_3820_);
v___x_3812_ = v___x_3774_;
v_isShared_3813_ = v_isSharedCheck_3819_;
goto v_resetjp_3811_;
}
else
{
lean_dec(v___x_3774_);
v___x_3812_ = lean_box(0);
v_isShared_3813_ = v_isSharedCheck_3819_;
goto v_resetjp_3811_;
}
v_resetjp_3811_:
{
lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3817_; 
v___x_3814_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__7));
v___x_3815_ = lean_string_append(v_pfx_3773_, v___x_3814_);
if (v_isShared_3813_ == 0)
{
lean_ctor_set_tag(v___x_3812_, 0);
lean_ctor_set(v___x_3812_, 0, v___x_3815_);
v___x_3817_ = v___x_3812_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v___x_3815_);
v___x_3817_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
return v___x_3817_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue(lean_object* v_00_u03b1_3823_, lean_object* v_attrs_3824_, lean_object* v_env_3825_, lean_object* v_decl_3826_, lean_object* v_val_3827_){
_start:
{
lean_object* v___x_3828_; 
v___x_3828_ = l_Lean_EnumAttributes_setValue___redArg(v_attrs_3824_, v_env_3825_, v_decl_3826_, v_val_3827_);
return v___x_3828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; 
v___x_3830_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3831_ = lean_st_mk_ref(v___x_3830_);
v___x_3832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3832_, 0, v___x_3831_);
return v___x_3832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2____boxed(lean_object* v_a_3833_){
_start:
{
lean_object* v_res_3834_; 
v_res_3834_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_();
return v_res_3834_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder(lean_object* v_builderId_3837_, lean_object* v_builder_3838_){
_start:
{
lean_object* v___x_3840_; lean_object* v___x_3841_; uint8_t v___x_3842_; 
v___x_3840_ = l_Lean_attributeImplBuilderTableRef;
v___x_3841_ = lean_st_ref_get(v___x_3840_);
v___x_3842_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_3841_, v_builderId_3837_);
lean_dec(v___x_3841_);
if (v___x_3842_ == 0)
{
lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; 
v___x_3843_ = lean_st_ref_take(v___x_3840_);
v___x_3844_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_3843_, v_builderId_3837_, v_builder_3838_);
v___x_3845_ = lean_st_ref_put(v___x_3840_, v___x_3844_);
v___x_3846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3846_, 0, v___x_3845_);
return v___x_3846_;
}
else
{
lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; 
lean_dec_ref(v_builder_3838_);
v___x_3847_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__0));
v___x_3848_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3837_, v___x_3842_);
v___x_3849_ = lean_string_append(v___x_3847_, v___x_3848_);
lean_dec_ref(v___x_3848_);
v___x_3850_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__1));
v___x_3851_ = lean_string_append(v___x_3849_, v___x_3850_);
v___x_3852_ = lean_mk_io_user_error(v___x_3851_);
v___x_3853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3853_, 0, v___x_3852_);
return v___x_3853_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder___boxed(lean_object* v_builderId_3854_, lean_object* v_builder_3855_, lean_object* v_a_3856_){
_start:
{
lean_object* v_res_3857_; 
v_res_3857_ = l_Lean_registerAttributeImplBuilder(v_builderId_3854_, v_builder_3855_);
return v_res_3857_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(lean_object* v_e_3858_){
_start:
{
if (lean_obj_tag(v_e_3858_) == 0)
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3868_; 
v_a_3860_ = lean_ctor_get(v_e_3858_, 0);
v_isSharedCheck_3868_ = !lean_is_exclusive(v_e_3858_);
if (v_isSharedCheck_3868_ == 0)
{
v___x_3862_ = v_e_3858_;
v_isShared_3863_ = v_isSharedCheck_3868_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v_e_3858_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3868_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3864_; lean_object* v___x_3866_; 
v___x_3864_ = lean_mk_io_user_error(v_a_3860_);
if (v_isShared_3863_ == 0)
{
lean_ctor_set_tag(v___x_3862_, 1);
lean_ctor_set(v___x_3862_, 0, v___x_3864_);
v___x_3866_ = v___x_3862_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v___x_3864_);
v___x_3866_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
return v___x_3866_;
}
}
}
else
{
lean_object* v_a_3869_; lean_object* v___x_3871_; uint8_t v_isShared_3872_; uint8_t v_isSharedCheck_3876_; 
v_a_3869_ = lean_ctor_get(v_e_3858_, 0);
v_isSharedCheck_3876_ = !lean_is_exclusive(v_e_3858_);
if (v_isSharedCheck_3876_ == 0)
{
v___x_3871_ = v_e_3858_;
v_isShared_3872_ = v_isSharedCheck_3876_;
goto v_resetjp_3870_;
}
else
{
lean_inc(v_a_3869_);
lean_dec(v_e_3858_);
v___x_3871_ = lean_box(0);
v_isShared_3872_ = v_isSharedCheck_3876_;
goto v_resetjp_3870_;
}
v_resetjp_3870_:
{
lean_object* v___x_3874_; 
if (v_isShared_3872_ == 0)
{
lean_ctor_set_tag(v___x_3871_, 0);
v___x_3874_ = v___x_3871_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3875_; 
v_reuseFailAlloc_3875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3875_, 0, v_a_3869_);
v___x_3874_ = v_reuseFailAlloc_3875_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
return v___x_3874_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg___boxed(lean_object* v_e_3877_, lean_object* v_a_3878_){
_start:
{
lean_object* v_res_3879_; 
v_res_3879_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3877_);
return v_res_3879_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(lean_object* v_00_u03b1_3880_, lean_object* v_e_3881_){
_start:
{
lean_object* v___x_3883_; 
v___x_3883_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3881_);
return v___x_3883_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___boxed(lean_object* v_00_u03b1_3884_, lean_object* v_e_3885_, lean_object* v_a_3886_){
_start:
{
lean_object* v_res_3887_; 
v_res_3887_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(v_00_u03b1_3884_, v_e_3885_);
return v_res_3887_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(lean_object* v_a_3888_, lean_object* v_x_3889_){
_start:
{
if (lean_obj_tag(v_x_3889_) == 0)
{
lean_object* v___x_3890_; 
v___x_3890_ = lean_box(0);
return v___x_3890_;
}
else
{
lean_object* v_key_3891_; lean_object* v_value_3892_; lean_object* v_tail_3893_; uint8_t v___x_3894_; 
v_key_3891_ = lean_ctor_get(v_x_3889_, 0);
v_value_3892_ = lean_ctor_get(v_x_3889_, 1);
v_tail_3893_ = lean_ctor_get(v_x_3889_, 2);
v___x_3894_ = lean_name_eq(v_key_3891_, v_a_3888_);
if (v___x_3894_ == 0)
{
v_x_3889_ = v_tail_3893_;
goto _start;
}
else
{
lean_object* v___x_3896_; 
lean_inc(v_value_3892_);
v___x_3896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3896_, 0, v_value_3892_);
return v___x_3896_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg___boxed(lean_object* v_a_3897_, lean_object* v_x_3898_){
_start:
{
lean_object* v_res_3899_; 
v_res_3899_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3897_, v_x_3898_);
lean_dec(v_x_3898_);
lean_dec(v_a_3897_);
return v_res_3899_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(lean_object* v_m_3900_, lean_object* v_a_3901_){
_start:
{
lean_object* v_buckets_3902_; lean_object* v___x_3903_; uint64_t v___y_3905_; 
v_buckets_3902_ = lean_ctor_get(v_m_3900_, 1);
v___x_3903_ = lean_array_get_size(v_buckets_3902_);
if (lean_obj_tag(v_a_3901_) == 0)
{
uint64_t v___x_3919_; 
v___x_3919_ = 1723ULL;
v___y_3905_ = v___x_3919_;
goto v___jp_3904_;
}
else
{
uint64_t v_hash_3920_; 
v_hash_3920_ = lean_ctor_get_uint64(v_a_3901_, sizeof(void*)*2);
v___y_3905_ = v_hash_3920_;
goto v___jp_3904_;
}
v___jp_3904_:
{
uint64_t v___x_3906_; uint64_t v___x_3907_; uint64_t v_fold_3908_; uint64_t v___x_3909_; uint64_t v___x_3910_; uint64_t v___x_3911_; size_t v___x_3912_; size_t v___x_3913_; size_t v___x_3914_; size_t v___x_3915_; size_t v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; 
v___x_3906_ = 32ULL;
v___x_3907_ = lean_uint64_shift_right(v___y_3905_, v___x_3906_);
v_fold_3908_ = lean_uint64_xor(v___y_3905_, v___x_3907_);
v___x_3909_ = 16ULL;
v___x_3910_ = lean_uint64_shift_right(v_fold_3908_, v___x_3909_);
v___x_3911_ = lean_uint64_xor(v_fold_3908_, v___x_3910_);
v___x_3912_ = lean_uint64_to_usize(v___x_3911_);
v___x_3913_ = lean_usize_of_nat(v___x_3903_);
v___x_3914_ = ((size_t)1ULL);
v___x_3915_ = lean_usize_sub(v___x_3913_, v___x_3914_);
v___x_3916_ = lean_usize_land(v___x_3912_, v___x_3915_);
v___x_3917_ = lean_array_uget_borrowed(v_buckets_3902_, v___x_3916_);
v___x_3918_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3901_, v___x_3917_);
return v___x_3918_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg___boxed(lean_object* v_m_3921_, lean_object* v_a_3922_){
_start:
{
lean_object* v_res_3923_; 
v_res_3923_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3921_, v_a_3922_);
lean_dec(v_a_3922_);
lean_dec_ref(v_m_3921_);
return v_res_3923_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry(lean_object* v_e_3925_){
_start:
{
lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v_builderId_3929_; lean_object* v_ref_3930_; lean_object* v_args_3931_; lean_object* v___x_3932_; 
v___x_3927_ = l_Lean_attributeImplBuilderTableRef;
v___x_3928_ = lean_st_ref_get(v___x_3927_);
v_builderId_3929_ = lean_ctor_get(v_e_3925_, 0);
lean_inc(v_builderId_3929_);
v_ref_3930_ = lean_ctor_get(v_e_3925_, 1);
lean_inc(v_ref_3930_);
v_args_3931_ = lean_ctor_get(v_e_3925_, 2);
lean_inc(v_args_3931_);
lean_dec_ref(v_e_3925_);
v___x_3932_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_3928_, v_builderId_3929_);
lean_dec(v___x_3928_);
if (lean_obj_tag(v___x_3932_) == 0)
{
lean_object* v___x_3933_; uint8_t v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; 
lean_dec(v_args_3931_);
lean_dec(v_ref_3930_);
v___x_3933_ = ((lean_object*)(l_Lean_mkAttributeImplOfEntry___closed__0));
v___x_3934_ = 1;
v___x_3935_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3929_, v___x_3934_);
v___x_3936_ = lean_string_append(v___x_3933_, v___x_3935_);
lean_dec_ref(v___x_3935_);
v___x_3937_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3938_ = lean_string_append(v___x_3936_, v___x_3937_);
v___x_3939_ = lean_mk_io_user_error(v___x_3938_);
v___x_3940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3940_, 0, v___x_3939_);
return v___x_3940_;
}
else
{
lean_object* v_val_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; 
lean_dec(v_builderId_3929_);
v_val_3941_ = lean_ctor_get(v___x_3932_, 0);
lean_inc(v_val_3941_);
lean_dec_ref_known(v___x_3932_, 1);
v___x_3942_ = lean_apply_2(v_val_3941_, v_ref_3930_, v_args_3931_);
v___x_3943_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v___x_3942_);
return v___x_3943_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry___boxed(lean_object* v_e_3944_, lean_object* v_a_3945_){
_start:
{
lean_object* v_res_3946_; 
v_res_3946_ = l_Lean_mkAttributeImplOfEntry(v_e_3944_);
return v_res_3946_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(lean_object* v_00_u03b2_3947_, lean_object* v_m_3948_, lean_object* v_a_3949_){
_start:
{
lean_object* v___x_3950_; 
v___x_3950_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3948_, v_a_3949_);
return v___x_3950_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___boxed(lean_object* v_00_u03b2_3951_, lean_object* v_m_3952_, lean_object* v_a_3953_){
_start:
{
lean_object* v_res_3954_; 
v_res_3954_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(v_00_u03b2_3951_, v_m_3952_, v_a_3953_);
lean_dec(v_a_3953_);
lean_dec_ref(v_m_3952_);
return v_res_3954_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(lean_object* v_00_u03b2_3955_, lean_object* v_a_3956_, lean_object* v_x_3957_){
_start:
{
lean_object* v___x_3958_; 
v___x_3958_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3956_, v_x_3957_);
return v___x_3958_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3959_, lean_object* v_a_3960_, lean_object* v_x_3961_){
_start:
{
lean_object* v_res_3962_; 
v_res_3962_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(v_00_u03b2_3959_, v_a_3960_, v_x_3961_);
lean_dec(v_x_3961_);
lean_dec(v_a_3960_);
return v_res_3962_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0(void){
_start:
{
lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; 
v___x_3963_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3964_ = lean_box(0);
v___x_3965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3965_, 0, v___x_3964_);
lean_ctor_set(v___x_3965_, 1, v___x_3963_);
return v___x_3965_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default(void){
_start:
{
lean_object* v___x_3966_; 
v___x_3966_ = lean_obj_once(&l_Lean_instInhabitedAttributeExtensionState_default___closed__0, &l_Lean_instInhabitedAttributeExtensionState_default___closed__0_once, _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0);
return v___x_3966_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState(void){
_start:
{
lean_object* v___x_3967_; 
v___x_3967_ = l_Lean_instInhabitedAttributeExtensionState_default;
return v___x_3967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial(){
_start:
{
lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; 
v___x_3969_ = l_Lean_attributeMapRef;
v___x_3970_ = lean_st_ref_get(v___x_3969_);
v___x_3971_ = lean_box(0);
v___x_3972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3971_);
lean_ctor_set(v___x_3972_, 1, v___x_3970_);
v___x_3973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3973_, 0, v___x_3972_);
return v___x_3973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed(lean_object* v_a_3974_){
_start:
{
lean_object* v_res_3975_; 
v_res_3975_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial();
return v_res_3975_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe(lean_object* v_env_3981_, lean_object* v_opts_3982_, lean_object* v_declName_3983_){
_start:
{
uint8_t v___x_3986_; lean_object* v___x_3987_; 
v___x_3986_ = 0;
lean_inc(v_declName_3983_);
lean_inc_ref(v_env_3981_);
v___x_3987_ = l_Lean_Environment_find_x3f(v_env_3981_, v_declName_3983_, v___x_3986_);
if (lean_obj_tag(v___x_3987_) == 0)
{
lean_object* v___x_3988_; uint8_t v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; 
lean_dec_ref(v_env_3981_);
v___x_3988_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__2));
v___x_3989_ = 1;
v___x_3990_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_3983_, v___x_3989_);
v___x_3991_ = lean_string_append(v___x_3988_, v___x_3990_);
lean_dec_ref(v___x_3990_);
v___x_3992_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3993_ = lean_string_append(v___x_3991_, v___x_3992_);
v___x_3994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3994_, 0, v___x_3993_);
return v___x_3994_;
}
else
{
lean_object* v_val_3995_; lean_object* v___x_3996_; 
v_val_3995_ = lean_ctor_get(v___x_3987_, 0);
lean_inc(v_val_3995_);
lean_dec_ref_known(v___x_3987_, 1);
v___x_3996_ = l_Lean_ConstantInfo_type(v_val_3995_);
lean_dec(v_val_3995_);
if (lean_obj_tag(v___x_3996_) == 4)
{
lean_object* v_declName_3997_; 
v_declName_3997_ = lean_ctor_get(v___x_3996_, 0);
lean_inc(v_declName_3997_);
lean_dec_ref_known(v___x_3996_, 2);
if (lean_obj_tag(v_declName_3997_) == 1)
{
lean_object* v_pre_3998_; 
v_pre_3998_ = lean_ctor_get(v_declName_3997_, 0);
lean_inc(v_pre_3998_);
if (lean_obj_tag(v_pre_3998_) == 1)
{
lean_object* v_pre_3999_; 
v_pre_3999_ = lean_ctor_get(v_pre_3998_, 0);
if (lean_obj_tag(v_pre_3999_) == 0)
{
lean_object* v_str_4000_; lean_object* v_str_4001_; lean_object* v___x_4002_; uint8_t v___x_4003_; 
v_str_4000_ = lean_ctor_get(v_declName_3997_, 1);
lean_inc_ref(v_str_4000_);
lean_dec_ref_known(v_declName_3997_, 2);
v_str_4001_ = lean_ctor_get(v_pre_3998_, 1);
lean_inc_ref(v_str_4001_);
lean_dec_ref_known(v_pre_3998_, 2);
v___x_4002_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__0));
v___x_4003_ = lean_string_dec_eq(v_str_4001_, v___x_4002_);
lean_dec_ref(v_str_4001_);
if (v___x_4003_ == 0)
{
lean_dec_ref(v_str_4000_);
lean_dec(v_declName_3983_);
lean_dec_ref(v_env_3981_);
goto v___jp_3984_;
}
else
{
lean_object* v___x_4004_; uint8_t v___x_4005_; 
v___x_4004_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__3));
v___x_4005_ = lean_string_dec_eq(v_str_4000_, v___x_4004_);
lean_dec_ref(v_str_4000_);
if (v___x_4005_ == 0)
{
lean_dec(v_declName_3983_);
lean_dec_ref(v_env_3981_);
goto v___jp_3984_;
}
else
{
lean_object* v___x_4006_; 
v___x_4006_ = l_Lean_Environment_evalConst___redArg(v_env_3981_, v_opts_3982_, v_declName_3983_, v___x_4005_);
lean_dec(v_declName_3983_);
lean_dec_ref(v_env_3981_);
return v___x_4006_;
}
}
}
else
{
lean_dec_ref_known(v_pre_3998_, 2);
lean_dec_ref_known(v_declName_3997_, 2);
lean_dec(v_declName_3983_);
lean_dec_ref(v_env_3981_);
goto v___jp_3984_;
}
}
else
{
lean_dec(v_pre_3998_);
lean_dec_ref_known(v_declName_3997_, 2);
lean_dec(v_declName_3983_);
lean_dec_ref(v_env_3981_);
goto v___jp_3984_;
}
}
else
{
lean_dec(v_declName_3997_);
lean_dec(v_declName_3983_);
lean_dec_ref(v_env_3981_);
goto v___jp_3984_;
}
}
else
{
lean_dec_ref(v___x_3996_);
lean_dec(v_declName_3983_);
lean_dec_ref(v_env_3981_);
goto v___jp_3984_;
}
}
v___jp_3984_:
{
lean_object* v___x_3985_; 
v___x_3985_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__1));
return v___x_3985_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___boxed(lean_object* v_env_4007_, lean_object* v_opts_4008_, lean_object* v_declName_4009_){
_start:
{
lean_object* v_res_4010_; 
v_res_4010_ = l_Lean_mkAttributeImplOfConstantUnsafe(v_env_4007_, v_opts_4008_, v_declName_4009_);
lean_dec_ref(v_opts_4008_);
return v_res_4010_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(lean_object* v_as_4011_, size_t v_i_4012_, size_t v_stop_4013_, lean_object* v_b_4014_){
_start:
{
uint8_t v___x_4016_; 
v___x_4016_ = lean_usize_dec_eq(v_i_4012_, v_stop_4013_);
if (v___x_4016_ == 0)
{
lean_object* v___x_4017_; lean_object* v___x_4018_; 
v___x_4017_ = lean_array_uget_borrowed(v_as_4011_, v_i_4012_);
lean_inc(v___x_4017_);
v___x_4018_ = l_Lean_mkAttributeImplOfEntry(v___x_4017_);
if (lean_obj_tag(v___x_4018_) == 0)
{
lean_object* v_a_4019_; lean_object* v_toAttributeImplCore_4020_; lean_object* v_name_4021_; lean_object* v___x_4022_; size_t v___x_4023_; size_t v___x_4024_; 
v_a_4019_ = lean_ctor_get(v___x_4018_, 0);
lean_inc(v_a_4019_);
lean_dec_ref_known(v___x_4018_, 1);
v_toAttributeImplCore_4020_ = lean_ctor_get(v_a_4019_, 0);
v_name_4021_ = lean_ctor_get(v_toAttributeImplCore_4020_, 1);
lean_inc(v_name_4021_);
v___x_4022_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_b_4014_, v_name_4021_, v_a_4019_);
v___x_4023_ = ((size_t)1ULL);
v___x_4024_ = lean_usize_add(v_i_4012_, v___x_4023_);
v_i_4012_ = v___x_4024_;
v_b_4014_ = v___x_4022_;
goto _start;
}
else
{
lean_object* v_a_4026_; lean_object* v___x_4028_; uint8_t v_isShared_4029_; uint8_t v_isSharedCheck_4033_; 
lean_dec_ref(v_b_4014_);
v_a_4026_ = lean_ctor_get(v___x_4018_, 0);
v_isSharedCheck_4033_ = !lean_is_exclusive(v___x_4018_);
if (v_isSharedCheck_4033_ == 0)
{
v___x_4028_ = v___x_4018_;
v_isShared_4029_ = v_isSharedCheck_4033_;
goto v_resetjp_4027_;
}
else
{
lean_inc(v_a_4026_);
lean_dec(v___x_4018_);
v___x_4028_ = lean_box(0);
v_isShared_4029_ = v_isSharedCheck_4033_;
goto v_resetjp_4027_;
}
v_resetjp_4027_:
{
lean_object* v___x_4031_; 
if (v_isShared_4029_ == 0)
{
v___x_4031_ = v___x_4028_;
goto v_reusejp_4030_;
}
else
{
lean_object* v_reuseFailAlloc_4032_; 
v_reuseFailAlloc_4032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4032_, 0, v_a_4026_);
v___x_4031_ = v_reuseFailAlloc_4032_;
goto v_reusejp_4030_;
}
v_reusejp_4030_:
{
return v___x_4031_;
}
}
}
}
else
{
lean_object* v___x_4034_; 
v___x_4034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4034_, 0, v_b_4014_);
return v___x_4034_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg___boxed(lean_object* v_as_4035_, lean_object* v_i_4036_, lean_object* v_stop_4037_, lean_object* v_b_4038_, lean_object* v___y_4039_){
_start:
{
size_t v_i_boxed_4040_; size_t v_stop_boxed_4041_; lean_object* v_res_4042_; 
v_i_boxed_4040_ = lean_unbox_usize(v_i_4036_);
lean_dec(v_i_4036_);
v_stop_boxed_4041_ = lean_unbox_usize(v_stop_4037_);
lean_dec(v_stop_4037_);
v_res_4042_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4035_, v_i_boxed_4040_, v_stop_boxed_4041_, v_b_4038_);
lean_dec_ref(v_as_4035_);
return v_res_4042_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(lean_object* v_as_4043_, size_t v_i_4044_, size_t v_stop_4045_, lean_object* v_b_4046_, lean_object* v___y_4047_){
_start:
{
lean_object* v_a_4050_; lean_object* v___y_4055_; uint8_t v___x_4057_; 
v___x_4057_ = lean_usize_dec_eq(v_i_4044_, v_stop_4045_);
if (v___x_4057_ == 0)
{
lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; uint8_t v___x_4061_; 
v___x_4058_ = lean_array_uget_borrowed(v_as_4043_, v_i_4044_);
v___x_4059_ = lean_unsigned_to_nat(0u);
v___x_4060_ = lean_array_get_size(v___x_4058_);
v___x_4061_ = lean_nat_dec_lt(v___x_4059_, v___x_4060_);
if (v___x_4061_ == 0)
{
v_a_4050_ = v_b_4046_;
goto v___jp_4049_;
}
else
{
uint8_t v___x_4062_; 
v___x_4062_ = lean_nat_dec_le(v___x_4060_, v___x_4060_);
if (v___x_4062_ == 0)
{
if (v___x_4061_ == 0)
{
v_a_4050_ = v_b_4046_;
goto v___jp_4049_;
}
else
{
size_t v___x_4063_; size_t v___x_4064_; lean_object* v___x_4065_; 
v___x_4063_ = ((size_t)0ULL);
v___x_4064_ = lean_usize_of_nat(v___x_4060_);
v___x_4065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_4058_, v___x_4063_, v___x_4064_, v_b_4046_);
v___y_4055_ = v___x_4065_;
goto v___jp_4054_;
}
}
else
{
size_t v___x_4066_; size_t v___x_4067_; lean_object* v___x_4068_; 
v___x_4066_ = ((size_t)0ULL);
v___x_4067_ = lean_usize_of_nat(v___x_4060_);
v___x_4068_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_4058_, v___x_4066_, v___x_4067_, v_b_4046_);
v___y_4055_ = v___x_4068_;
goto v___jp_4054_;
}
}
}
else
{
lean_object* v___x_4069_; 
v___x_4069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4069_, 0, v_b_4046_);
return v___x_4069_;
}
v___jp_4049_:
{
size_t v___x_4051_; size_t v___x_4052_; 
v___x_4051_ = ((size_t)1ULL);
v___x_4052_ = lean_usize_add(v_i_4044_, v___x_4051_);
v_i_4044_ = v___x_4052_;
v_b_4046_ = v_a_4050_;
goto _start;
}
v___jp_4054_:
{
if (lean_obj_tag(v___y_4055_) == 0)
{
lean_object* v_a_4056_; 
v_a_4056_ = lean_ctor_get(v___y_4055_, 0);
lean_inc(v_a_4056_);
lean_dec_ref_known(v___y_4055_, 1);
v_a_4050_ = v_a_4056_;
goto v___jp_4049_;
}
else
{
return v___y_4055_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1___boxed(lean_object* v_as_4070_, lean_object* v_i_4071_, lean_object* v_stop_4072_, lean_object* v_b_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_){
_start:
{
size_t v_i_boxed_4076_; size_t v_stop_boxed_4077_; lean_object* v_res_4078_; 
v_i_boxed_4076_ = lean_unbox_usize(v_i_4071_);
lean_dec(v_i_4071_);
v_stop_boxed_4077_ = lean_unbox_usize(v_stop_4072_);
lean_dec(v_stop_4072_);
v_res_4078_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_as_4070_, v_i_boxed_4076_, v_stop_boxed_4077_, v_b_4073_, v___y_4074_);
lean_dec_ref(v___y_4074_);
lean_dec_ref(v_as_4070_);
return v_res_4078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(lean_object* v_es_4079_, lean_object* v_a_4080_){
_start:
{
lean_object* v_a_4083_; lean_object* v___y_4088_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; uint8_t v___x_4102_; 
v___x_4098_ = l_Lean_attributeMapRef;
v___x_4099_ = lean_st_ref_get(v___x_4098_);
v___x_4100_ = lean_unsigned_to_nat(0u);
v___x_4101_ = lean_array_get_size(v_es_4079_);
v___x_4102_ = lean_nat_dec_lt(v___x_4100_, v___x_4101_);
if (v___x_4102_ == 0)
{
v_a_4083_ = v___x_4099_;
goto v___jp_4082_;
}
else
{
uint8_t v___x_4103_; 
v___x_4103_ = lean_nat_dec_le(v___x_4101_, v___x_4101_);
if (v___x_4103_ == 0)
{
if (v___x_4102_ == 0)
{
v_a_4083_ = v___x_4099_;
goto v___jp_4082_;
}
else
{
size_t v___x_4104_; size_t v___x_4105_; lean_object* v___x_4106_; 
v___x_4104_ = ((size_t)0ULL);
v___x_4105_ = lean_usize_of_nat(v___x_4101_);
v___x_4106_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_4079_, v___x_4104_, v___x_4105_, v___x_4099_, v_a_4080_);
v___y_4088_ = v___x_4106_;
goto v___jp_4087_;
}
}
else
{
size_t v___x_4107_; size_t v___x_4108_; lean_object* v___x_4109_; 
v___x_4107_ = ((size_t)0ULL);
v___x_4108_ = lean_usize_of_nat(v___x_4101_);
v___x_4109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_4079_, v___x_4107_, v___x_4108_, v___x_4099_, v_a_4080_);
v___y_4088_ = v___x_4109_;
goto v___jp_4087_;
}
}
v___jp_4082_:
{
lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; 
v___x_4084_ = lean_box(0);
v___x_4085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4085_, 0, v___x_4084_);
lean_ctor_set(v___x_4085_, 1, v_a_4083_);
v___x_4086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4086_, 0, v___x_4085_);
return v___x_4086_;
}
v___jp_4087_:
{
if (lean_obj_tag(v___y_4088_) == 0)
{
lean_object* v_a_4089_; 
v_a_4089_ = lean_ctor_get(v___y_4088_, 0);
lean_inc(v_a_4089_);
lean_dec_ref_known(v___y_4088_, 1);
v_a_4083_ = v_a_4089_;
goto v___jp_4082_;
}
else
{
lean_object* v_a_4090_; lean_object* v___x_4092_; uint8_t v_isShared_4093_; uint8_t v_isSharedCheck_4097_; 
v_a_4090_ = lean_ctor_get(v___y_4088_, 0);
v_isSharedCheck_4097_ = !lean_is_exclusive(v___y_4088_);
if (v_isSharedCheck_4097_ == 0)
{
v___x_4092_ = v___y_4088_;
v_isShared_4093_ = v_isSharedCheck_4097_;
goto v_resetjp_4091_;
}
else
{
lean_inc(v_a_4090_);
lean_dec(v___y_4088_);
v___x_4092_ = lean_box(0);
v_isShared_4093_ = v_isSharedCheck_4097_;
goto v_resetjp_4091_;
}
v_resetjp_4091_:
{
lean_object* v___x_4095_; 
if (v_isShared_4093_ == 0)
{
v___x_4095_ = v___x_4092_;
goto v_reusejp_4094_;
}
else
{
lean_object* v_reuseFailAlloc_4096_; 
v_reuseFailAlloc_4096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4096_, 0, v_a_4090_);
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
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported___boxed(lean_object* v_es_4110_, lean_object* v_a_4111_, lean_object* v_a_4112_){
_start:
{
lean_object* v_res_4113_; 
v_res_4113_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(v_es_4110_, v_a_4111_);
lean_dec_ref(v_a_4111_);
lean_dec_ref(v_es_4110_);
return v_res_4113_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(lean_object* v_as_4114_, size_t v_i_4115_, size_t v_stop_4116_, lean_object* v_b_4117_, lean_object* v___y_4118_){
_start:
{
lean_object* v___x_4120_; 
v___x_4120_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4114_, v_i_4115_, v_stop_4116_, v_b_4117_);
return v___x_4120_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___boxed(lean_object* v_as_4121_, lean_object* v_i_4122_, lean_object* v_stop_4123_, lean_object* v_b_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_){
_start:
{
size_t v_i_boxed_4127_; size_t v_stop_boxed_4128_; lean_object* v_res_4129_; 
v_i_boxed_4127_ = lean_unbox_usize(v_i_4122_);
lean_dec(v_i_4122_);
v_stop_boxed_4128_ = lean_unbox_usize(v_stop_4123_);
lean_dec(v_stop_4123_);
v_res_4129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(v_as_4121_, v_i_boxed_4127_, v_stop_boxed_4128_, v_b_4124_, v___y_4125_);
lean_dec_ref(v___y_4125_);
lean_dec_ref(v_as_4121_);
return v_res_4129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_addAttrEntry(lean_object* v_s_4130_, lean_object* v_e_4131_){
_start:
{
lean_object* v_snd_4132_; lean_object* v_toAttributeImplCore_4133_; lean_object* v_fst_4134_; lean_object* v___x_4136_; uint8_t v_isShared_4137_; uint8_t v_isSharedCheck_4152_; 
v_snd_4132_ = lean_ctor_get(v_e_4131_, 1);
lean_inc(v_snd_4132_);
v_toAttributeImplCore_4133_ = lean_ctor_get(v_snd_4132_, 0);
v_fst_4134_ = lean_ctor_get(v_e_4131_, 0);
v_isSharedCheck_4152_ = !lean_is_exclusive(v_e_4131_);
if (v_isSharedCheck_4152_ == 0)
{
lean_object* v_unused_4153_; 
v_unused_4153_ = lean_ctor_get(v_e_4131_, 1);
lean_dec(v_unused_4153_);
v___x_4136_ = v_e_4131_;
v_isShared_4137_ = v_isSharedCheck_4152_;
goto v_resetjp_4135_;
}
else
{
lean_inc(v_fst_4134_);
lean_dec(v_e_4131_);
v___x_4136_ = lean_box(0);
v_isShared_4137_ = v_isSharedCheck_4152_;
goto v_resetjp_4135_;
}
v_resetjp_4135_:
{
lean_object* v_newEntries_4138_; lean_object* v_map_4139_; lean_object* v___x_4141_; uint8_t v_isShared_4142_; uint8_t v_isSharedCheck_4151_; 
v_newEntries_4138_ = lean_ctor_get(v_s_4130_, 0);
v_map_4139_ = lean_ctor_get(v_s_4130_, 1);
v_isSharedCheck_4151_ = !lean_is_exclusive(v_s_4130_);
if (v_isSharedCheck_4151_ == 0)
{
v___x_4141_ = v_s_4130_;
v_isShared_4142_ = v_isSharedCheck_4151_;
goto v_resetjp_4140_;
}
else
{
lean_inc(v_map_4139_);
lean_inc(v_newEntries_4138_);
lean_dec(v_s_4130_);
v___x_4141_ = lean_box(0);
v_isShared_4142_ = v_isSharedCheck_4151_;
goto v_resetjp_4140_;
}
v_resetjp_4140_:
{
lean_object* v_name_4143_; lean_object* v___x_4145_; 
v_name_4143_ = lean_ctor_get(v_toAttributeImplCore_4133_, 1);
lean_inc(v_name_4143_);
if (v_isShared_4137_ == 0)
{
lean_ctor_set_tag(v___x_4136_, 1);
lean_ctor_set(v___x_4136_, 1, v_newEntries_4138_);
v___x_4145_ = v___x_4136_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4150_; 
v_reuseFailAlloc_4150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4150_, 0, v_fst_4134_);
lean_ctor_set(v_reuseFailAlloc_4150_, 1, v_newEntries_4138_);
v___x_4145_ = v_reuseFailAlloc_4150_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
lean_object* v___x_4146_; lean_object* v___x_4148_; 
v___x_4146_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4139_, v_name_4143_, v_snd_4132_);
if (v_isShared_4142_ == 0)
{
lean_ctor_set(v___x_4141_, 1, v___x_4146_);
lean_ctor_set(v___x_4141_, 0, v___x_4145_);
v___x_4148_ = v___x_4141_;
goto v_reusejp_4147_;
}
else
{
lean_object* v_reuseFailAlloc_4149_; 
v_reuseFailAlloc_4149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4149_, 0, v___x_4145_);
lean_ctor_set(v_reuseFailAlloc_4149_, 1, v___x_4146_);
v___x_4148_ = v_reuseFailAlloc_4149_;
goto v_reusejp_4147_;
}
v_reusejp_4147_:
{
return v___x_4148_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_x_4154_, lean_object* v_s_4155_){
_start:
{
lean_object* v_newEntries_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; 
v_newEntries_4156_ = lean_ctor_get(v_s_4155_, 0);
lean_inc(v_newEntries_4156_);
lean_dec_ref(v_s_4155_);
v___x_4157_ = l_List_reverse___redArg(v_newEntries_4156_);
v___x_4158_ = lean_array_mk(v___x_4157_);
lean_inc_ref_n(v___x_4158_, 2);
v___x_4159_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4159_, 0, v___x_4158_);
lean_ctor_set(v___x_4159_, 1, v___x_4158_);
lean_ctor_set(v___x_4159_, 2, v___x_4158_);
return v___x_4159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_x_4160_, lean_object* v_s_4161_){
_start:
{
lean_object* v_res_4162_; 
v_res_4162_ = l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(v_x_4160_, v_s_4161_);
lean_dec_ref(v_x_4160_);
return v_res_4162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4163_){
_start:
{
lean_object* v_newEntries_4164_; lean_object* v___x_4166_; uint8_t v_isShared_4167_; uint8_t v_isSharedCheck_4175_; 
v_newEntries_4164_ = lean_ctor_get(v_s_4163_, 0);
v_isSharedCheck_4175_ = !lean_is_exclusive(v_s_4163_);
if (v_isSharedCheck_4175_ == 0)
{
lean_object* v_unused_4176_; 
v_unused_4176_ = lean_ctor_get(v_s_4163_, 1);
lean_dec(v_unused_4176_);
v___x_4166_ = v_s_4163_;
v_isShared_4167_ = v_isSharedCheck_4175_;
goto v_resetjp_4165_;
}
else
{
lean_inc(v_newEntries_4164_);
lean_dec(v_s_4163_);
v___x_4166_ = lean_box(0);
v_isShared_4167_ = v_isSharedCheck_4175_;
goto v_resetjp_4165_;
}
v_resetjp_4165_:
{
lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4173_; 
v___x_4168_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__4));
v___x_4169_ = l_List_lengthTR___redArg(v_newEntries_4164_);
lean_dec(v_newEntries_4164_);
v___x_4170_ = l_Nat_reprFast(v___x_4169_);
v___x_4171_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4171_, 0, v___x_4170_);
if (v_isShared_4167_ == 0)
{
lean_ctor_set_tag(v___x_4166_, 5);
lean_ctor_set(v___x_4166_, 1, v___x_4171_);
lean_ctor_set(v___x_4166_, 0, v___x_4168_);
v___x_4173_ = v___x_4166_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v___x_4168_);
lean_ctor_set(v_reuseFailAlloc_4174_, 1, v___x_4171_);
v___x_4173_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
return v___x_4173_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4177_){
_start:
{
lean_object* v_newEntries_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; 
v_newEntries_4178_ = lean_ctor_get(v_s_4177_, 0);
lean_inc(v_newEntries_4178_);
lean_dec_ref(v_s_4177_);
v___x_4179_ = l_List_reverse___redArg(v_newEntries_4178_);
v___x_4180_ = lean_array_mk(v___x_4179_);
return v___x_4180_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___f_4193_; lean_object* v___f_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; 
v___x_4190_ = 0;
v___x_4191_ = lean_box(0);
v___x_4192_ = lean_box(2);
v___f_4193_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___f_4194_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4195_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4196_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4197_ = lean_alloc_closure((void*)(l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed), 1, 0);
v___x_4198_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4199_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_4199_, 0, v___x_4198_);
lean_ctor_set(v___x_4199_, 1, v___x_4197_);
lean_ctor_set(v___x_4199_, 2, v___x_4196_);
lean_ctor_set(v___x_4199_, 3, v___x_4195_);
lean_ctor_set(v___x_4199_, 4, v___f_4194_);
lean_ctor_set(v___x_4199_, 5, v___f_4193_);
lean_ctor_set(v___x_4199_, 6, v___x_4192_);
lean_ctor_set(v___x_4199_, 7, v___x_4191_);
lean_ctor_set_uint8(v___x_4199_, sizeof(void*)*8, v___x_4190_);
return v___x_4199_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; 
v___f_4200_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4201_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4202_, 0, v___x_4201_);
lean_ctor_set(v___x_4202_, 1, v___f_4200_);
return v___x_4202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4204_; lean_object* v___x_4205_; 
v___x_4204_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4205_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_4204_);
return v___x_4205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_a_4206_){
_start:
{
lean_object* v_res_4207_; 
v_res_4207_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_();
return v_res_4207_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute(lean_object* v_n_4208_){
_start:
{
lean_object* v___x_4210_; lean_object* v___x_4211_; uint8_t v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; 
v___x_4210_ = l_Lean_attributeMapRef;
v___x_4211_ = lean_st_ref_get(v___x_4210_);
v___x_4212_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_4211_, v_n_4208_);
lean_dec(v___x_4211_);
v___x_4213_ = lean_box(v___x_4212_);
v___x_4214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4214_, 0, v___x_4213_);
return v___x_4214_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute___boxed(lean_object* v_n_4215_, lean_object* v_a_4216_){
_start:
{
lean_object* v_res_4217_; 
v_res_4217_ = l_Lean_isBuiltinAttribute(v_n_4215_);
lean_dec(v_n_4215_);
return v_res_4217_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(lean_object* v_x_4218_, lean_object* v_x_4219_){
_start:
{
if (lean_obj_tag(v_x_4219_) == 0)
{
return v_x_4218_;
}
else
{
lean_object* v_key_4220_; lean_object* v_tail_4221_; lean_object* v___x_4222_; 
v_key_4220_ = lean_ctor_get(v_x_4219_, 0);
v_tail_4221_ = lean_ctor_get(v_x_4219_, 2);
lean_inc(v_key_4220_);
v___x_4222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4222_, 0, v_key_4220_);
lean_ctor_set(v___x_4222_, 1, v_x_4218_);
v_x_4218_ = v___x_4222_;
v_x_4219_ = v_tail_4221_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0___boxed(lean_object* v_x_4224_, lean_object* v_x_4225_){
_start:
{
lean_object* v_res_4226_; 
v_res_4226_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_x_4224_, v_x_4225_);
lean_dec(v_x_4225_);
return v_res_4226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(lean_object* v_as_4227_, size_t v_i_4228_, size_t v_stop_4229_, lean_object* v_b_4230_){
_start:
{
uint8_t v___x_4231_; 
v___x_4231_ = lean_usize_dec_eq(v_i_4228_, v_stop_4229_);
if (v___x_4231_ == 0)
{
lean_object* v___x_4232_; lean_object* v___x_4233_; size_t v___x_4234_; size_t v___x_4235_; 
v___x_4232_ = lean_array_uget_borrowed(v_as_4227_, v_i_4228_);
v___x_4233_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_b_4230_, v___x_4232_);
v___x_4234_ = ((size_t)1ULL);
v___x_4235_ = lean_usize_add(v_i_4228_, v___x_4234_);
v_i_4228_ = v___x_4235_;
v_b_4230_ = v___x_4233_;
goto _start;
}
else
{
return v_b_4230_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1___boxed(lean_object* v_as_4237_, lean_object* v_i_4238_, lean_object* v_stop_4239_, lean_object* v_b_4240_){
_start:
{
size_t v_i_boxed_4241_; size_t v_stop_boxed_4242_; lean_object* v_res_4243_; 
v_i_boxed_4241_ = lean_unbox_usize(v_i_4238_);
lean_dec(v_i_4238_);
v_stop_boxed_4242_ = lean_unbox_usize(v_stop_4239_);
lean_dec(v_stop_4239_);
v_res_4243_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_as_4237_, v_i_boxed_4241_, v_stop_boxed_4242_, v_b_4240_);
lean_dec_ref(v_as_4237_);
return v_res_4243_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames(){
_start:
{
lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v_buckets_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; uint8_t v___x_4251_; 
v___x_4245_ = l_Lean_attributeMapRef;
v___x_4246_ = lean_st_ref_get(v___x_4245_);
v_buckets_4247_ = lean_ctor_get(v___x_4246_, 1);
lean_inc_ref(v_buckets_4247_);
lean_dec(v___x_4246_);
v___x_4248_ = lean_box(0);
v___x_4249_ = lean_unsigned_to_nat(0u);
v___x_4250_ = lean_array_get_size(v_buckets_4247_);
v___x_4251_ = lean_nat_dec_lt(v___x_4249_, v___x_4250_);
if (v___x_4251_ == 0)
{
lean_object* v___x_4252_; 
lean_dec_ref(v_buckets_4247_);
v___x_4252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4252_, 0, v___x_4248_);
return v___x_4252_;
}
else
{
size_t v___x_4253_; size_t v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; 
v___x_4253_ = ((size_t)0ULL);
v___x_4254_ = lean_usize_of_nat(v___x_4250_);
v___x_4255_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4247_, v___x_4253_, v___x_4254_, v___x_4248_);
lean_dec_ref(v_buckets_4247_);
v___x_4256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4256_, 0, v___x_4255_);
return v___x_4256_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames___boxed(lean_object* v_a_4257_){
_start:
{
lean_object* v_res_4258_; 
v_res_4258_ = l_Lean_getBuiltinAttributeNames();
return v_res_4258_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl(lean_object* v_attrName_4260_){
_start:
{
lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; 
v___x_4262_ = l_Lean_attributeMapRef;
v___x_4263_ = lean_st_ref_get(v___x_4262_);
v___x_4264_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_4263_, v_attrName_4260_);
lean_dec(v___x_4263_);
if (lean_obj_tag(v___x_4264_) == 0)
{
lean_object* v___x_4265_; uint8_t v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; 
v___x_4265_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4266_ = 1;
v___x_4267_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4260_, v___x_4266_);
v___x_4268_ = lean_string_append(v___x_4265_, v___x_4267_);
lean_dec_ref(v___x_4267_);
v___x_4269_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4270_ = lean_string_append(v___x_4268_, v___x_4269_);
v___x_4271_ = lean_mk_io_user_error(v___x_4270_);
v___x_4272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4272_, 0, v___x_4271_);
return v___x_4272_;
}
else
{
lean_object* v_val_4273_; lean_object* v___x_4275_; uint8_t v_isShared_4276_; uint8_t v_isSharedCheck_4280_; 
lean_dec(v_attrName_4260_);
v_val_4273_ = lean_ctor_get(v___x_4264_, 0);
v_isSharedCheck_4280_ = !lean_is_exclusive(v___x_4264_);
if (v_isSharedCheck_4280_ == 0)
{
v___x_4275_ = v___x_4264_;
v_isShared_4276_ = v_isSharedCheck_4280_;
goto v_resetjp_4274_;
}
else
{
lean_inc(v_val_4273_);
lean_dec(v___x_4264_);
v___x_4275_ = lean_box(0);
v_isShared_4276_ = v_isSharedCheck_4280_;
goto v_resetjp_4274_;
}
v_resetjp_4274_:
{
lean_object* v___x_4278_; 
if (v_isShared_4276_ == 0)
{
lean_ctor_set_tag(v___x_4275_, 0);
v___x_4278_ = v___x_4275_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4279_; 
v_reuseFailAlloc_4279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4279_, 0, v_val_4273_);
v___x_4278_ = v_reuseFailAlloc_4279_;
goto v_reusejp_4277_;
}
v_reusejp_4277_:
{
return v___x_4278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl___boxed(lean_object* v_attrName_4281_, lean_object* v_a_4282_){
_start:
{
lean_object* v_res_4283_; 
v_res_4283_ = l_Lean_getBuiltinAttributeImpl(v_attrName_4281_);
return v_res_4283_;
}
}
LEAN_EXPORT uint8_t l_Lean_isAttribute(lean_object* v_env_4284_, lean_object* v_attrName_4285_){
_start:
{
lean_object* v___x_4286_; lean_object* v_toEnvExtension_4287_; lean_object* v_asyncMode_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v_map_4292_; uint8_t v___x_4293_; 
v___x_4286_ = l_Lean_attributeExtension;
v_toEnvExtension_4287_ = lean_ctor_get(v___x_4286_, 0);
v_asyncMode_4288_ = lean_ctor_get(v_toEnvExtension_4287_, 2);
v___x_4289_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4290_ = lean_box(0);
v___x_4291_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4289_, v___x_4286_, v_env_4284_, v_asyncMode_4288_, v___x_4290_);
v_map_4292_ = lean_ctor_get(v___x_4291_, 1);
lean_inc_ref(v_map_4292_);
lean_dec(v___x_4291_);
v___x_4293_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4292_, v_attrName_4285_);
lean_dec_ref(v_map_4292_);
return v___x_4293_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAttribute___boxed(lean_object* v_env_4294_, lean_object* v_attrName_4295_){
_start:
{
uint8_t v_res_4296_; lean_object* v_r_4297_; 
v_res_4296_ = l_Lean_isAttribute(v_env_4294_, v_attrName_4295_);
lean_dec(v_attrName_4295_);
v_r_4297_ = lean_box(v_res_4296_);
return v_r_4297_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeNames(lean_object* v_env_4298_){
_start:
{
lean_object* v___x_4299_; lean_object* v_toEnvExtension_4300_; lean_object* v_asyncMode_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v_map_4305_; lean_object* v_buckets_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; uint8_t v___x_4310_; 
v___x_4299_ = l_Lean_attributeExtension;
v_toEnvExtension_4300_ = lean_ctor_get(v___x_4299_, 0);
v_asyncMode_4301_ = lean_ctor_get(v_toEnvExtension_4300_, 2);
v___x_4302_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4303_ = lean_box(0);
v___x_4304_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4302_, v___x_4299_, v_env_4298_, v_asyncMode_4301_, v___x_4303_);
v_map_4305_ = lean_ctor_get(v___x_4304_, 1);
lean_inc_ref(v_map_4305_);
lean_dec(v___x_4304_);
v_buckets_4306_ = lean_ctor_get(v_map_4305_, 1);
lean_inc_ref(v_buckets_4306_);
lean_dec_ref(v_map_4305_);
v___x_4307_ = lean_box(0);
v___x_4308_ = lean_unsigned_to_nat(0u);
v___x_4309_ = lean_array_get_size(v_buckets_4306_);
v___x_4310_ = lean_nat_dec_lt(v___x_4308_, v___x_4309_);
if (v___x_4310_ == 0)
{
lean_dec_ref(v_buckets_4306_);
return v___x_4307_;
}
else
{
size_t v___x_4311_; size_t v___x_4312_; lean_object* v___x_4313_; 
v___x_4311_ = ((size_t)0ULL);
v___x_4312_ = lean_usize_of_nat(v___x_4309_);
v___x_4313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4306_, v___x_4311_, v___x_4312_, v___x_4307_);
lean_dec_ref(v_buckets_4306_);
return v___x_4313_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeImpl(lean_object* v_env_4314_, lean_object* v_attrName_4315_){
_start:
{
lean_object* v___x_4316_; lean_object* v_toEnvExtension_4317_; lean_object* v_asyncMode_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v_map_4322_; lean_object* v___x_4323_; 
v___x_4316_ = l_Lean_attributeExtension;
v_toEnvExtension_4317_ = lean_ctor_get(v___x_4316_, 0);
v_asyncMode_4318_ = lean_ctor_get(v_toEnvExtension_4317_, 2);
v___x_4319_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4320_ = lean_box(0);
v___x_4321_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4319_, v___x_4316_, v_env_4314_, v_asyncMode_4318_, v___x_4320_);
v_map_4322_ = lean_ctor_get(v___x_4321_, 1);
lean_inc_ref(v_map_4322_);
lean_dec(v___x_4321_);
v___x_4323_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_map_4322_, v_attrName_4315_);
lean_dec_ref(v_map_4322_);
if (lean_obj_tag(v___x_4323_) == 0)
{
lean_object* v___x_4324_; uint8_t v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; 
v___x_4324_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4325_ = 1;
v___x_4326_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4315_, v___x_4325_);
v___x_4327_ = lean_string_append(v___x_4324_, v___x_4326_);
lean_dec_ref(v___x_4326_);
v___x_4328_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4329_ = lean_string_append(v___x_4327_, v___x_4328_);
v___x_4330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4330_, 0, v___x_4329_);
return v___x_4330_;
}
else
{
lean_object* v_val_4331_; lean_object* v___x_4333_; uint8_t v_isShared_4334_; uint8_t v_isSharedCheck_4338_; 
lean_dec(v_attrName_4315_);
v_val_4331_ = lean_ctor_get(v___x_4323_, 0);
v_isSharedCheck_4338_ = !lean_is_exclusive(v___x_4323_);
if (v_isSharedCheck_4338_ == 0)
{
v___x_4333_ = v___x_4323_;
v_isShared_4334_ = v_isSharedCheck_4338_;
goto v_resetjp_4332_;
}
else
{
lean_inc(v_val_4331_);
lean_dec(v___x_4323_);
v___x_4333_ = lean_box(0);
v_isShared_4334_ = v_isSharedCheck_4338_;
goto v_resetjp_4332_;
}
v_resetjp_4332_:
{
lean_object* v___x_4336_; 
if (v_isShared_4334_ == 0)
{
v___x_4336_ = v___x_4333_;
goto v_reusejp_4335_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4337_, 0, v_val_4331_);
v___x_4336_ = v_reuseFailAlloc_4337_;
goto v_reusejp_4335_;
}
v_reusejp_4335_:
{
return v___x_4336_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder(lean_object* v_env_4339_, lean_object* v_builderId_4340_, lean_object* v_ref_4341_, lean_object* v_args_4342_){
_start:
{
lean_object* v_entry_4344_; lean_object* v___x_4345_; 
v_entry_4344_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_entry_4344_, 0, v_builderId_4340_);
lean_ctor_set(v_entry_4344_, 1, v_ref_4341_);
lean_ctor_set(v_entry_4344_, 2, v_args_4342_);
lean_inc_ref(v_entry_4344_);
v___x_4345_ = l_Lean_mkAttributeImplOfEntry(v_entry_4344_);
if (lean_obj_tag(v___x_4345_) == 0)
{
lean_object* v_a_4346_; lean_object* v___x_4348_; uint8_t v_isShared_4349_; uint8_t v_isSharedCheck_4371_; 
v_a_4346_ = lean_ctor_get(v___x_4345_, 0);
v_isSharedCheck_4371_ = !lean_is_exclusive(v___x_4345_);
if (v_isSharedCheck_4371_ == 0)
{
v___x_4348_ = v___x_4345_;
v_isShared_4349_ = v_isSharedCheck_4371_;
goto v_resetjp_4347_;
}
else
{
lean_inc(v_a_4346_);
lean_dec(v___x_4345_);
v___x_4348_ = lean_box(0);
v_isShared_4349_ = v_isSharedCheck_4371_;
goto v_resetjp_4347_;
}
v_resetjp_4347_:
{
lean_object* v_toAttributeImplCore_4350_; lean_object* v_name_4351_; uint8_t v___x_4352_; 
v_toAttributeImplCore_4350_ = lean_ctor_get(v_a_4346_, 0);
v_name_4351_ = lean_ctor_get(v_toAttributeImplCore_4350_, 1);
lean_inc_ref(v_env_4339_);
v___x_4352_ = l_Lean_isAttribute(v_env_4339_, v_name_4351_);
if (v___x_4352_ == 0)
{
lean_object* v___x_4353_; lean_object* v_toEnvExtension_4354_; lean_object* v_asyncMode_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4360_; 
v___x_4353_ = l_Lean_attributeExtension;
v_toEnvExtension_4354_ = lean_ctor_get(v___x_4353_, 0);
v_asyncMode_4355_ = lean_ctor_get(v_toEnvExtension_4354_, 2);
v___x_4356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4356_, 0, v_entry_4344_);
lean_ctor_set(v___x_4356_, 1, v_a_4346_);
v___x_4357_ = lean_box(0);
v___x_4358_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_4353_, v_env_4339_, v___x_4356_, v_asyncMode_4355_, v___x_4357_);
if (v_isShared_4349_ == 0)
{
lean_ctor_set(v___x_4348_, 0, v___x_4358_);
v___x_4360_ = v___x_4348_;
goto v_reusejp_4359_;
}
else
{
lean_object* v_reuseFailAlloc_4361_; 
v_reuseFailAlloc_4361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4361_, 0, v___x_4358_);
v___x_4360_ = v_reuseFailAlloc_4361_;
goto v_reusejp_4359_;
}
v_reusejp_4359_:
{
return v___x_4360_;
}
}
else
{
lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4369_; 
lean_inc(v_name_4351_);
lean_dec(v_a_4346_);
lean_dec_ref_known(v_entry_4344_, 3);
lean_dec_ref(v_env_4339_);
v___x_4362_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_4363_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4351_, v___x_4352_);
v___x_4364_ = lean_string_append(v___x_4362_, v___x_4363_);
lean_dec_ref(v___x_4363_);
v___x_4365_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_4366_ = lean_string_append(v___x_4364_, v___x_4365_);
v___x_4367_ = lean_mk_io_user_error(v___x_4366_);
if (v_isShared_4349_ == 0)
{
lean_ctor_set_tag(v___x_4348_, 1);
lean_ctor_set(v___x_4348_, 0, v___x_4367_);
v___x_4369_ = v___x_4348_;
goto v_reusejp_4368_;
}
else
{
lean_object* v_reuseFailAlloc_4370_; 
v_reuseFailAlloc_4370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4370_, 0, v___x_4367_);
v___x_4369_ = v_reuseFailAlloc_4370_;
goto v_reusejp_4368_;
}
v_reusejp_4368_:
{
return v___x_4369_;
}
}
}
}
else
{
lean_object* v_a_4372_; lean_object* v___x_4374_; uint8_t v_isShared_4375_; uint8_t v_isSharedCheck_4379_; 
lean_dec_ref_known(v_entry_4344_, 3);
lean_dec_ref(v_env_4339_);
v_a_4372_ = lean_ctor_get(v___x_4345_, 0);
v_isSharedCheck_4379_ = !lean_is_exclusive(v___x_4345_);
if (v_isSharedCheck_4379_ == 0)
{
v___x_4374_ = v___x_4345_;
v_isShared_4375_ = v_isSharedCheck_4379_;
goto v_resetjp_4373_;
}
else
{
lean_inc(v_a_4372_);
lean_dec(v___x_4345_);
v___x_4374_ = lean_box(0);
v_isShared_4375_ = v_isSharedCheck_4379_;
goto v_resetjp_4373_;
}
v_resetjp_4373_:
{
lean_object* v___x_4377_; 
if (v_isShared_4375_ == 0)
{
v___x_4377_ = v___x_4374_;
goto v_reusejp_4376_;
}
else
{
lean_object* v_reuseFailAlloc_4378_; 
v_reuseFailAlloc_4378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4378_, 0, v_a_4372_);
v___x_4377_ = v_reuseFailAlloc_4378_;
goto v_reusejp_4376_;
}
v_reusejp_4376_:
{
return v___x_4377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___boxed(lean_object* v_env_4380_, lean_object* v_builderId_4381_, lean_object* v_ref_4382_, lean_object* v_args_4383_, lean_object* v_a_4384_){
_start:
{
lean_object* v_res_4385_; 
v_res_4385_ = l_Lean_registerAttributeOfBuilder(v_env_4380_, v_builderId_4381_, v_ref_4382_, v_args_4383_);
return v_res_4385_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(lean_object* v_x_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_){
_start:
{
if (lean_obj_tag(v_x_4386_) == 0)
{
lean_object* v_a_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; 
v_a_4390_ = lean_ctor_get(v_x_4386_, 0);
lean_inc(v_a_4390_);
lean_dec_ref_known(v_x_4386_, 1);
v___x_4391_ = l_Lean_stringToMessageData(v_a_4390_);
v___x_4392_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_4391_, v___y_4387_, v___y_4388_);
return v___x_4392_;
}
else
{
lean_object* v_a_4393_; lean_object* v___x_4395_; uint8_t v_isShared_4396_; uint8_t v_isSharedCheck_4400_; 
v_a_4393_ = lean_ctor_get(v_x_4386_, 0);
v_isSharedCheck_4400_ = !lean_is_exclusive(v_x_4386_);
if (v_isSharedCheck_4400_ == 0)
{
v___x_4395_ = v_x_4386_;
v_isShared_4396_ = v_isSharedCheck_4400_;
goto v_resetjp_4394_;
}
else
{
lean_inc(v_a_4393_);
lean_dec(v_x_4386_);
v___x_4395_ = lean_box(0);
v_isShared_4396_ = v_isSharedCheck_4400_;
goto v_resetjp_4394_;
}
v_resetjp_4394_:
{
lean_object* v___x_4398_; 
if (v_isShared_4396_ == 0)
{
lean_ctor_set_tag(v___x_4395_, 0);
v___x_4398_ = v___x_4395_;
goto v_reusejp_4397_;
}
else
{
lean_object* v_reuseFailAlloc_4399_; 
v_reuseFailAlloc_4399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4399_, 0, v_a_4393_);
v___x_4398_ = v_reuseFailAlloc_4399_;
goto v_reusejp_4397_;
}
v_reusejp_4397_:
{
return v___x_4398_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg___boxed(lean_object* v_x_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_){
_start:
{
lean_object* v_res_4405_; 
v_res_4405_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4401_, v___y_4402_, v___y_4403_);
lean_dec(v___y_4403_);
lean_dec_ref(v___y_4402_);
return v_res_4405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add(lean_object* v_declName_4406_, lean_object* v_attrName_4407_, lean_object* v_stx_4408_, uint8_t v_kind_4409_, lean_object* v_a_4410_, lean_object* v_a_4411_){
_start:
{
lean_object* v___x_4413_; lean_object* v_env_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; 
v___x_4413_ = lean_st_ref_get(v_a_4411_);
v_env_4414_ = lean_ctor_get(v___x_4413_, 0);
lean_inc_ref(v_env_4414_);
lean_dec(v___x_4413_);
v___x_4415_ = l_Lean_getAttributeImpl(v_env_4414_, v_attrName_4407_);
v___x_4416_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4415_, v_a_4410_, v_a_4411_);
if (lean_obj_tag(v___x_4416_) == 0)
{
lean_object* v_a_4417_; lean_object* v_add_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; 
v_a_4417_ = lean_ctor_get(v___x_4416_, 0);
lean_inc(v_a_4417_);
lean_dec_ref_known(v___x_4416_, 1);
v_add_4418_ = lean_ctor_get(v_a_4417_, 1);
lean_inc_ref(v_add_4418_);
lean_dec(v_a_4417_);
v___x_4419_ = lean_box(v_kind_4409_);
lean_inc(v_a_4411_);
lean_inc_ref(v_a_4410_);
v___x_4420_ = lean_apply_6(v_add_4418_, v_declName_4406_, v_stx_4408_, v___x_4419_, v_a_4410_, v_a_4411_, lean_box(0));
return v___x_4420_;
}
else
{
lean_object* v_a_4421_; lean_object* v___x_4423_; uint8_t v_isShared_4424_; uint8_t v_isSharedCheck_4428_; 
lean_dec(v_stx_4408_);
lean_dec(v_declName_4406_);
v_a_4421_ = lean_ctor_get(v___x_4416_, 0);
v_isSharedCheck_4428_ = !lean_is_exclusive(v___x_4416_);
if (v_isSharedCheck_4428_ == 0)
{
v___x_4423_ = v___x_4416_;
v_isShared_4424_ = v_isSharedCheck_4428_;
goto v_resetjp_4422_;
}
else
{
lean_inc(v_a_4421_);
lean_dec(v___x_4416_);
v___x_4423_ = lean_box(0);
v_isShared_4424_ = v_isSharedCheck_4428_;
goto v_resetjp_4422_;
}
v_resetjp_4422_:
{
lean_object* v___x_4426_; 
if (v_isShared_4424_ == 0)
{
v___x_4426_ = v___x_4423_;
goto v_reusejp_4425_;
}
else
{
lean_object* v_reuseFailAlloc_4427_; 
v_reuseFailAlloc_4427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4427_, 0, v_a_4421_);
v___x_4426_ = v_reuseFailAlloc_4427_;
goto v_reusejp_4425_;
}
v_reusejp_4425_:
{
return v___x_4426_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add___boxed(lean_object* v_declName_4429_, lean_object* v_attrName_4430_, lean_object* v_stx_4431_, lean_object* v_kind_4432_, lean_object* v_a_4433_, lean_object* v_a_4434_, lean_object* v_a_4435_){
_start:
{
uint8_t v_kind_boxed_4436_; lean_object* v_res_4437_; 
v_kind_boxed_4436_ = lean_unbox(v_kind_4432_);
v_res_4437_ = l_Lean_Attribute_add(v_declName_4429_, v_attrName_4430_, v_stx_4431_, v_kind_boxed_4436_, v_a_4433_, v_a_4434_);
lean_dec(v_a_4434_);
lean_dec_ref(v_a_4433_);
return v_res_4437_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(lean_object* v_00_u03b1_4438_, lean_object* v_x_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_){
_start:
{
lean_object* v___x_4443_; 
v___x_4443_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4439_, v___y_4440_, v___y_4441_);
return v___x_4443_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___boxed(lean_object* v_00_u03b1_4444_, lean_object* v_x_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_){
_start:
{
lean_object* v_res_4449_; 
v_res_4449_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(v_00_u03b1_4444_, v_x_4445_, v___y_4446_, v___y_4447_);
lean_dec(v___y_4447_);
lean_dec_ref(v___y_4446_);
return v_res_4449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase(lean_object* v_declName_4450_, lean_object* v_attrName_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_){
_start:
{
lean_object* v___x_4455_; lean_object* v_env_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; 
v___x_4455_ = lean_st_ref_get(v_a_4453_);
v_env_4456_ = lean_ctor_get(v___x_4455_, 0);
lean_inc_ref(v_env_4456_);
lean_dec(v___x_4455_);
v___x_4457_ = l_Lean_getAttributeImpl(v_env_4456_, v_attrName_4451_);
v___x_4458_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4457_, v_a_4452_, v_a_4453_);
if (lean_obj_tag(v___x_4458_) == 0)
{
lean_object* v_a_4459_; lean_object* v_erase_4460_; lean_object* v___x_4461_; 
v_a_4459_ = lean_ctor_get(v___x_4458_, 0);
lean_inc(v_a_4459_);
lean_dec_ref_known(v___x_4458_, 1);
v_erase_4460_ = lean_ctor_get(v_a_4459_, 2);
lean_inc_ref(v_erase_4460_);
lean_dec(v_a_4459_);
lean_inc(v_a_4453_);
lean_inc_ref(v_a_4452_);
v___x_4461_ = lean_apply_4(v_erase_4460_, v_declName_4450_, v_a_4452_, v_a_4453_, lean_box(0));
return v___x_4461_;
}
else
{
lean_object* v_a_4462_; lean_object* v___x_4464_; uint8_t v_isShared_4465_; uint8_t v_isSharedCheck_4469_; 
lean_dec(v_declName_4450_);
v_a_4462_ = lean_ctor_get(v___x_4458_, 0);
v_isSharedCheck_4469_ = !lean_is_exclusive(v___x_4458_);
if (v_isSharedCheck_4469_ == 0)
{
v___x_4464_ = v___x_4458_;
v_isShared_4465_ = v_isSharedCheck_4469_;
goto v_resetjp_4463_;
}
else
{
lean_inc(v_a_4462_);
lean_dec(v___x_4458_);
v___x_4464_ = lean_box(0);
v_isShared_4465_ = v_isSharedCheck_4469_;
goto v_resetjp_4463_;
}
v_resetjp_4463_:
{
lean_object* v___x_4467_; 
if (v_isShared_4465_ == 0)
{
v___x_4467_ = v___x_4464_;
goto v_reusejp_4466_;
}
else
{
lean_object* v_reuseFailAlloc_4468_; 
v_reuseFailAlloc_4468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4468_, 0, v_a_4462_);
v___x_4467_ = v_reuseFailAlloc_4468_;
goto v_reusejp_4466_;
}
v_reusejp_4466_:
{
return v___x_4467_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase___boxed(lean_object* v_declName_4470_, lean_object* v_attrName_4471_, lean_object* v_a_4472_, lean_object* v_a_4473_, lean_object* v_a_4474_){
_start:
{
lean_object* v_res_4475_; 
v_res_4475_ = l_Lean_Attribute_erase(v_declName_4470_, v_attrName_4471_, v_a_4472_, v_a_4473_);
lean_dec(v_a_4473_);
lean_dec_ref(v_a_4472_);
return v_res_4475_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(lean_object* v_x_4476_, lean_object* v_x_4477_){
_start:
{
if (lean_obj_tag(v_x_4477_) == 0)
{
return v_x_4476_;
}
else
{
lean_object* v_key_4478_; lean_object* v_value_4479_; lean_object* v_tail_4480_; lean_object* v_newEntries_4481_; lean_object* v_map_4482_; uint8_t v___x_4483_; 
v_key_4478_ = lean_ctor_get(v_x_4477_, 0);
lean_inc(v_key_4478_);
v_value_4479_ = lean_ctor_get(v_x_4477_, 1);
lean_inc(v_value_4479_);
v_tail_4480_ = lean_ctor_get(v_x_4477_, 2);
lean_inc(v_tail_4480_);
lean_dec_ref_known(v_x_4477_, 3);
v_newEntries_4481_ = lean_ctor_get(v_x_4476_, 0);
v_map_4482_ = lean_ctor_get(v_x_4476_, 1);
v___x_4483_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4482_, v_key_4478_);
if (v___x_4483_ == 0)
{
lean_object* v___x_4485_; uint8_t v_isShared_4486_; uint8_t v_isSharedCheck_4492_; 
lean_inc_ref(v_map_4482_);
lean_inc(v_newEntries_4481_);
v_isSharedCheck_4492_ = !lean_is_exclusive(v_x_4476_);
if (v_isSharedCheck_4492_ == 0)
{
lean_object* v_unused_4493_; lean_object* v_unused_4494_; 
v_unused_4493_ = lean_ctor_get(v_x_4476_, 1);
lean_dec(v_unused_4493_);
v_unused_4494_ = lean_ctor_get(v_x_4476_, 0);
lean_dec(v_unused_4494_);
v___x_4485_ = v_x_4476_;
v_isShared_4486_ = v_isSharedCheck_4492_;
goto v_resetjp_4484_;
}
else
{
lean_dec(v_x_4476_);
v___x_4485_ = lean_box(0);
v_isShared_4486_ = v_isSharedCheck_4492_;
goto v_resetjp_4484_;
}
v_resetjp_4484_:
{
lean_object* v___x_4487_; lean_object* v___x_4489_; 
v___x_4487_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4482_, v_key_4478_, v_value_4479_);
if (v_isShared_4486_ == 0)
{
lean_ctor_set(v___x_4485_, 1, v___x_4487_);
v___x_4489_ = v___x_4485_;
goto v_reusejp_4488_;
}
else
{
lean_object* v_reuseFailAlloc_4491_; 
v_reuseFailAlloc_4491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4491_, 0, v_newEntries_4481_);
lean_ctor_set(v_reuseFailAlloc_4491_, 1, v___x_4487_);
v___x_4489_ = v_reuseFailAlloc_4491_;
goto v_reusejp_4488_;
}
v_reusejp_4488_:
{
v_x_4476_ = v___x_4489_;
v_x_4477_ = v_tail_4480_;
goto _start;
}
}
}
else
{
lean_dec(v_value_4479_);
lean_dec(v_key_4478_);
v_x_4477_ = v_tail_4480_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(lean_object* v_as_4496_, size_t v_i_4497_, size_t v_stop_4498_, lean_object* v_b_4499_){
_start:
{
uint8_t v___x_4500_; 
v___x_4500_ = lean_usize_dec_eq(v_i_4497_, v_stop_4498_);
if (v___x_4500_ == 0)
{
lean_object* v___x_4501_; lean_object* v___x_4502_; size_t v___x_4503_; size_t v___x_4504_; 
v___x_4501_ = lean_array_uget_borrowed(v_as_4496_, v_i_4497_);
lean_inc(v___x_4501_);
v___x_4502_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(v_b_4499_, v___x_4501_);
v___x_4503_ = ((size_t)1ULL);
v___x_4504_ = lean_usize_add(v_i_4497_, v___x_4503_);
v_i_4497_ = v___x_4504_;
v_b_4499_ = v___x_4502_;
goto _start;
}
else
{
return v_b_4499_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1___boxed(lean_object* v_as_4506_, lean_object* v_i_4507_, lean_object* v_stop_4508_, lean_object* v_b_4509_){
_start:
{
size_t v_i_boxed_4510_; size_t v_stop_boxed_4511_; lean_object* v_res_4512_; 
v_i_boxed_4510_ = lean_unbox_usize(v_i_4507_);
lean_dec(v_i_4507_);
v_stop_boxed_4511_ = lean_unbox_usize(v_stop_4508_);
lean_dec(v_stop_4508_);
v_res_4512_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_as_4506_, v_i_boxed_4510_, v_stop_boxed_4511_, v_b_4509_);
lean_dec_ref(v_as_4506_);
return v_res_4512_;
}
}
LEAN_EXPORT lean_object* lean_update_env_attributes(lean_object* v_env_4513_){
_start:
{
lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___y_4520_; lean_object* v_toEnvExtension_4523_; lean_object* v_asyncMode_4524_; lean_object* v_buckets_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; uint8_t v___x_4530_; 
v___x_4515_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4516_ = l_Lean_attributeMapRef;
v___x_4517_ = lean_st_ref_get(v___x_4516_);
v___x_4518_ = l_Lean_attributeExtension;
v_toEnvExtension_4523_ = lean_ctor_get(v___x_4518_, 0);
v_asyncMode_4524_ = lean_ctor_get(v_toEnvExtension_4523_, 2);
v_buckets_4525_ = lean_ctor_get(v___x_4517_, 1);
lean_inc_ref(v_buckets_4525_);
lean_dec(v___x_4517_);
v___x_4526_ = lean_box(0);
lean_inc_ref(v_env_4513_);
v___x_4527_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4515_, v___x_4518_, v_env_4513_, v_asyncMode_4524_, v___x_4526_);
v___x_4528_ = lean_unsigned_to_nat(0u);
v___x_4529_ = lean_array_get_size(v_buckets_4525_);
v___x_4530_ = lean_nat_dec_lt(v___x_4528_, v___x_4529_);
if (v___x_4530_ == 0)
{
lean_dec_ref(v_buckets_4525_);
v___y_4520_ = v___x_4527_;
goto v___jp_4519_;
}
else
{
size_t v___x_4531_; size_t v___x_4532_; lean_object* v___x_4533_; 
v___x_4531_ = ((size_t)0ULL);
v___x_4532_ = lean_usize_of_nat(v___x_4529_);
v___x_4533_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_buckets_4525_, v___x_4531_, v___x_4532_, v___x_4527_);
lean_dec_ref(v_buckets_4525_);
v___y_4520_ = v___x_4533_;
goto v___jp_4519_;
}
v___jp_4519_:
{
lean_object* v___x_4521_; lean_object* v___x_4522_; 
v___x_4521_ = l_Lean_PersistentEnvExtension_setState___redArg(v___x_4518_, v_env_4513_, v___y_4520_);
v___x_4522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4522_, 0, v___x_4521_);
return v___x_4522_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___boxed(lean_object* v_env_4534_, lean_object* v_a_4535_){
_start:
{
lean_object* v_res_4536_; 
v_res_4536_ = lean_update_env_attributes(v_env_4534_);
return v_res_4536_;
}
}
LEAN_EXPORT lean_object* lean_get_num_attributes(){
_start:
{
lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v_size_4540_; lean_object* v___x_4541_; 
v___x_4538_ = l_Lean_attributeMapRef;
v___x_4539_ = lean_st_ref_get(v___x_4538_);
v_size_4540_ = lean_ctor_get(v___x_4539_, 0);
lean_inc(v_size_4540_);
lean_dec(v___x_4539_);
v___x_4541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4541_, 0, v_size_4540_);
return v___x_4541_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNumBuiltinAttributesImpl___boxed(lean_object* v_a_4542_){
_start:
{
lean_object* v_res_4543_; 
v_res_4543_ = lean_get_num_attributes();
return v_res_4543_;
}
}
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_MetaAttr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Attributes(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_MetaAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedAttributeApplicationTime_default = _init_l_Lean_instInhabitedAttributeApplicationTime_default();
l_Lean_instInhabitedAttributeApplicationTime = _init_l_Lean_instInhabitedAttributeApplicationTime();
l_Lean_instInhabitedAttributeKind_default = _init_l_Lean_instInhabitedAttributeKind_default();
l_Lean_instInhabitedAttributeKind = _init_l_Lean_instInhabitedAttributeKind();
res = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_attributeMapRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_attributeMapRef);
lean_dec_ref(res);
l_Lean_instInhabitedTagAttribute_default = _init_l_Lean_instInhabitedTagAttribute_default();
lean_mark_persistent(l_Lean_instInhabitedTagAttribute_default);
l_Lean_instInhabitedTagAttribute = _init_l_Lean_instInhabitedTagAttribute();
lean_mark_persistent(l_Lean_instInhabitedTagAttribute);
res = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_attributeImplBuilderTableRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_attributeImplBuilderTableRef);
lean_dec_ref(res);
l_Lean_instInhabitedAttributeExtensionState_default = _init_l_Lean_instInhabitedAttributeExtensionState_default();
lean_mark_persistent(l_Lean_instInhabitedAttributeExtensionState_default);
l_Lean_instInhabitedAttributeExtensionState = _init_l_Lean_instInhabitedAttributeExtensionState();
lean_mark_persistent(l_Lean_instInhabitedAttributeExtensionState);
res = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_attributeExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_attributeExtension);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Attributes(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lean_AttributeImplCore_ref___autoParam = _init_l_Lean_AttributeImplCore_ref___autoParam();
lean_mark_persistent(l_Lean_AttributeImplCore_ref___autoParam);
l_Lean_registerTagAttribute___auto__1 = _init_l_Lean_registerTagAttribute___auto__1();
lean_mark_persistent(l_Lean_registerTagAttribute___auto__1);
l_Lean_registerEnumAttributes___auto__1 = _init_l_Lean_registerEnumAttributes___auto__1();
lean_mark_persistent(l_Lean_registerEnumAttributes___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_CoreM(uint8_t builtin);
lean_object* initialize_Lean_Compiler_MetaAttr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Attributes(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_MetaAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Attributes(builtin);
}
#ifdef __cplusplus
}
#endif
