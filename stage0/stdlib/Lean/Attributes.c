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
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t l_Lean_EnvExtension_asyncMayModify___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_asyncPrefix_x3f(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
extern lean_object* l_Lean_instInhabitedMessageData_default;
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Array_reverse___redArg(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_instInhabitedEnvExtension_default(lean_object*);
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
static lean_once_cell_t l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__1___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0_value),((lean_object*)&l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0_value),((lean_object*)&l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0_value)}};
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__1 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lean_instInhabitedParametricAttribute_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedParametricAttribute_default___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___closed__0_value;
static const lean_closure_object l_Lean_instInhabitedParametricAttribute_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedParametricAttribute_default___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___closed__1_value;
static const lean_closure_object l_Lean_instInhabitedParametricAttribute_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedParametricAttribute_default___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___closed__2 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___closed__2_value;
static const lean_closure_object l_Lean_instInhabitedParametricAttribute_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedParametricAttribute_default___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___closed__3 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___closed__3_value;
static lean_once_cell_t l_Lean_instInhabitedParametricAttribute_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedParametricAttribute_default___closed__4;
static lean_once_cell_t l_Lean_instInhabitedParametricAttribute_default___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedParametricAttribute_default___closed__5;
static lean_once_cell_t l_Lean_instInhabitedParametricAttribute_default___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedParametricAttribute_default___closed__6;
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default(lean_object*);
static lean_once_cell_t l_Lean_instInhabitedParametricAttribute___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedParametricAttribute___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instInhabitedEnumAttributes_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedEnumAttributes_default___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedEnumAttributes_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedEnumAttributes_default___closed__0_value;
static const lean_closure_object l_Lean_instInhabitedEnumAttributes_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedEnumAttributes_default___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedEnumAttributes_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedEnumAttributes_default___closed__1_value;
static const lean_closure_object l_Lean_instInhabitedEnumAttributes_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedEnumAttributes_default___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedEnumAttributes_default___closed__2 = (const lean_object*)&l_Lean_instInhabitedEnumAttributes_default___closed__2_value;
static lean_once_cell_t l_Lean_instInhabitedEnumAttributes_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedEnumAttributes_default___closed__3;
static lean_once_cell_t l_Lean_instInhabitedEnumAttributes_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedEnumAttributes_default___closed__4;
static lean_once_cell_t l_Lean_instInhabitedEnumAttributes_default___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedEnumAttributes_default___closed__5;
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default(lean_object*);
static lean_once_cell_t l_Lean_instInhabitedEnumAttributes___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedEnumAttributes___closed__0;
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
static const lean_closure_object l_Lean_registerEnumAttributes___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerTagAttribute___lam__5___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
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
lean_object* v___x_82_; lean_object* v_toCold_83_; lean_object* v_env_84_; lean_object* v_ref_85_; lean_object* v_options_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_82_ = lean_st_ref_get(v___y_80_);
v_toCold_83_ = lean_ctor_get(v___y_79_, 0);
v_env_84_ = lean_ctor_get(v___x_82_, 0);
lean_inc_ref(v_env_84_);
lean_dec(v___x_82_);
v_ref_85_ = lean_ctor_get(v___y_79_, 2);
v_options_86_ = lean_ctor_get(v_toCold_83_, 2);
lean_inc_ref(v_options_86_);
v___x_87_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_87_, 0, v_env_84_);
lean_ctor_set(v___x_87_, 1, v_options_86_);
v___x_88_ = lean_apply_2(v_x_78_, v___x_87_, lean_box(0));
if (lean_obj_tag(v___x_88_) == 0)
{
lean_object* v_a_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_96_; 
v_a_89_ = lean_ctor_get(v___x_88_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v___x_88_);
if (v_isSharedCheck_96_ == 0)
{
v___x_91_ = v___x_88_;
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_a_89_);
lean_dec(v___x_88_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_94_; 
if (v_isShared_92_ == 0)
{
v___x_94_ = v___x_91_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_a_89_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
else
{
lean_object* v_a_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_108_; 
v_a_97_ = lean_ctor_get(v___x_88_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_88_);
if (v_isSharedCheck_108_ == 0)
{
v___x_99_ = v___x_88_;
v_isShared_100_ = v_isSharedCheck_108_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_a_97_);
lean_dec(v___x_88_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_108_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_106_; 
v___x_101_ = lean_io_error_to_string(v_a_97_);
v___x_102_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
v___x_103_ = l_Lean_MessageData_ofFormat(v___x_102_);
lean_inc(v_ref_85_);
v___x_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_104_, 0, v_ref_85_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 0, v___x_104_);
v___x_106_ = v___x_99_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v___x_104_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLiftImportMAttrM___lam__0___boxed(lean_object* v_00_u03b1_109_, lean_object* v_x_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_instMonadLiftImportMAttrM___lam__0(v_00_u03b1_109_, v_x_110_, v___y_111_, v___y_112_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
return v_res_114_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__12(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__10));
v___x_144_ = l_Lean_mkAtom(v___x_143_);
return v___x_144_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__13(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_145_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__12, &l_Lean_AttributeImplCore_ref___autoParam___closed__12_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__12);
v___x_146_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_147_ = lean_array_push(v___x_146_, v___x_145_);
return v___x_147_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__18(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__17));
v___x_157_ = l_Lean_mkAtom(v___x_156_);
return v___x_157_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__19(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_158_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__18, &l_Lean_AttributeImplCore_ref___autoParam___closed__18_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__18);
v___x_159_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_160_ = lean_array_push(v___x_159_, v___x_158_);
return v___x_160_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__20(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_161_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__19, &l_Lean_AttributeImplCore_ref___autoParam___closed__19_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__19);
v___x_162_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__16));
v___x_163_ = lean_box(2);
v___x_164_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v___x_162_);
lean_ctor_set(v___x_164_, 2, v___x_161_);
return v___x_164_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__21(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_165_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__20, &l_Lean_AttributeImplCore_ref___autoParam___closed__20_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__20);
v___x_166_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__13, &l_Lean_AttributeImplCore_ref___autoParam___closed__13_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__13);
v___x_167_ = lean_array_push(v___x_166_, v___x_165_);
return v___x_167_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__22(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_168_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__21, &l_Lean_AttributeImplCore_ref___autoParam___closed__21_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__21);
v___x_169_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__11));
v___x_170_ = lean_box(2);
v___x_171_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v___x_169_);
lean_ctor_set(v___x_171_, 2, v___x_168_);
return v___x_171_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__23(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_172_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__22, &l_Lean_AttributeImplCore_ref___autoParam___closed__22_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__22);
v___x_173_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_174_ = lean_array_push(v___x_173_, v___x_172_);
return v___x_174_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__24(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_175_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__23, &l_Lean_AttributeImplCore_ref___autoParam___closed__23_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__23);
v___x_176_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__9));
v___x_177_ = lean_box(2);
v___x_178_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
lean_ctor_set(v___x_178_, 1, v___x_176_);
lean_ctor_set(v___x_178_, 2, v___x_175_);
return v___x_178_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__25(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_179_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__24, &l_Lean_AttributeImplCore_ref___autoParam___closed__24_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__24);
v___x_180_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_181_ = lean_array_push(v___x_180_, v___x_179_);
return v___x_181_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__26(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_182_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__25, &l_Lean_AttributeImplCore_ref___autoParam___closed__25_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__25);
v___x_183_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__7));
v___x_184_ = lean_box(2);
v___x_185_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
lean_ctor_set(v___x_185_, 1, v___x_183_);
lean_ctor_set(v___x_185_, 2, v___x_182_);
return v___x_185_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__27(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_186_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__26, &l_Lean_AttributeImplCore_ref___autoParam___closed__26_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__26);
v___x_187_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_188_ = lean_array_push(v___x_187_, v___x_186_);
return v___x_188_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_189_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__27, &l_Lean_AttributeImplCore_ref___autoParam___closed__27_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__27);
v___x_190_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__4));
v___x_191_ = lean_box(2);
v___x_192_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v___x_190_);
lean_ctor_set(v___x_192_, 2, v___x_189_);
return v___x_192_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam(void){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorIdx(uint8_t v_x_208_){
_start:
{
switch(v_x_208_)
{
case 0:
{
lean_object* v___x_209_; 
v___x_209_ = lean_unsigned_to_nat(0u);
return v___x_209_;
}
case 1:
{
lean_object* v___x_210_; 
v___x_210_ = lean_unsigned_to_nat(1u);
return v___x_210_;
}
default: 
{
lean_object* v___x_211_; 
v___x_211_ = lean_unsigned_to_nat(2u);
return v___x_211_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorIdx___boxed(lean_object* v_x_212_){
_start:
{
uint8_t v_x_boxed_213_; lean_object* v_res_214_; 
v_x_boxed_213_ = lean_unbox(v_x_212_);
v_res_214_ = l_Lean_AttributeKind_ctorIdx(v_x_boxed_213_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___redArg(lean_object* v_k_215_){
_start:
{
lean_inc(v_k_215_);
return v_k_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___redArg___boxed(lean_object* v_k_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lean_AttributeKind_ctorElim___redArg(v_k_216_);
lean_dec(v_k_216_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim(lean_object* v_motive_218_, lean_object* v_ctorIdx_219_, uint8_t v_t_220_, lean_object* v_h_221_, lean_object* v_k_222_){
_start:
{
lean_inc(v_k_222_);
return v_k_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___boxed(lean_object* v_motive_223_, lean_object* v_ctorIdx_224_, lean_object* v_t_225_, lean_object* v_h_226_, lean_object* v_k_227_){
_start:
{
uint8_t v_t_boxed_228_; lean_object* v_res_229_; 
v_t_boxed_228_ = lean_unbox(v_t_225_);
v_res_229_ = l_Lean_AttributeKind_ctorElim(v_motive_223_, v_ctorIdx_224_, v_t_boxed_228_, v_h_226_, v_k_227_);
lean_dec(v_k_227_);
lean_dec(v_ctorIdx_224_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim___redArg(lean_object* v_global_230_){
_start:
{
lean_inc(v_global_230_);
return v_global_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim___redArg___boxed(lean_object* v_global_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_AttributeKind_global_elim___redArg(v_global_231_);
lean_dec(v_global_231_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim(lean_object* v_motive_233_, uint8_t v_t_234_, lean_object* v_h_235_, lean_object* v_global_236_){
_start:
{
lean_inc(v_global_236_);
return v_global_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim___boxed(lean_object* v_motive_237_, lean_object* v_t_238_, lean_object* v_h_239_, lean_object* v_global_240_){
_start:
{
uint8_t v_t_boxed_241_; lean_object* v_res_242_; 
v_t_boxed_241_ = lean_unbox(v_t_238_);
v_res_242_ = l_Lean_AttributeKind_global_elim(v_motive_237_, v_t_boxed_241_, v_h_239_, v_global_240_);
lean_dec(v_global_240_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim___redArg(lean_object* v_local_243_){
_start:
{
lean_inc(v_local_243_);
return v_local_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim___redArg___boxed(lean_object* v_local_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_AttributeKind_local_elim___redArg(v_local_244_);
lean_dec(v_local_244_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim(lean_object* v_motive_246_, uint8_t v_t_247_, lean_object* v_h_248_, lean_object* v_local_249_){
_start:
{
lean_inc(v_local_249_);
return v_local_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim___boxed(lean_object* v_motive_250_, lean_object* v_t_251_, lean_object* v_h_252_, lean_object* v_local_253_){
_start:
{
uint8_t v_t_boxed_254_; lean_object* v_res_255_; 
v_t_boxed_254_ = lean_unbox(v_t_251_);
v_res_255_ = l_Lean_AttributeKind_local_elim(v_motive_250_, v_t_boxed_254_, v_h_252_, v_local_253_);
lean_dec(v_local_253_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___redArg(lean_object* v_scoped_256_){
_start:
{
lean_inc(v_scoped_256_);
return v_scoped_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___redArg___boxed(lean_object* v_scoped_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_AttributeKind_scoped_elim___redArg(v_scoped_257_);
lean_dec(v_scoped_257_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim(lean_object* v_motive_259_, uint8_t v_t_260_, lean_object* v_h_261_, lean_object* v_scoped_262_){
_start:
{
lean_inc(v_scoped_262_);
return v_scoped_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___boxed(lean_object* v_motive_263_, lean_object* v_t_264_, lean_object* v_h_265_, lean_object* v_scoped_266_){
_start:
{
uint8_t v_t_boxed_267_; lean_object* v_res_268_; 
v_t_boxed_267_ = lean_unbox(v_t_264_);
v_res_268_ = l_Lean_AttributeKind_scoped_elim(v_motive_263_, v_t_boxed_267_, v_h_265_, v_scoped_266_);
lean_dec(v_scoped_266_);
return v_res_268_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t v_x_269_, uint8_t v_y_270_){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; uint8_t v___x_273_; 
v___x_271_ = l_Lean_AttributeKind_ctorIdx(v_x_269_);
v___x_272_ = l_Lean_AttributeKind_ctorIdx(v_y_270_);
v___x_273_ = lean_nat_dec_eq(v___x_271_, v___x_272_);
lean_dec(v___x_272_);
lean_dec(v___x_271_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqAttributeKind_beq___boxed(lean_object* v_x_274_, lean_object* v_y_275_){
_start:
{
uint8_t v_x_21__boxed_276_; uint8_t v_y_22__boxed_277_; uint8_t v_res_278_; lean_object* v_r_279_; 
v_x_21__boxed_276_ = lean_unbox(v_x_274_);
v_y_22__boxed_277_ = lean_unbox(v_y_275_);
v_res_278_ = l_Lean_instBEqAttributeKind_beq(v_x_21__boxed_276_, v_y_22__boxed_277_);
v_r_279_ = lean_box(v_res_278_);
return v_r_279_;
}
}
static uint8_t _init_l_Lean_instInhabitedAttributeKind_default(void){
_start:
{
uint8_t v___x_282_; 
v___x_282_ = 0;
return v___x_282_;
}
}
static uint8_t _init_l_Lean_instInhabitedAttributeKind(void){
_start:
{
uint8_t v___x_283_; 
v___x_283_ = 0;
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringAttributeKind___lam__0(uint8_t v_x_287_){
_start:
{
switch(v_x_287_)
{
case 0:
{
lean_object* v___x_288_; 
v___x_288_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
return v___x_288_;
}
case 1:
{
lean_object* v___x_289_; 
v___x_289_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
return v___x_289_;
}
default: 
{
lean_object* v___x_290_; 
v___x_290_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
return v___x_290_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringAttributeKind___lam__0___boxed(lean_object* v_x_291_){
_start:
{
uint8_t v_x_36__boxed_292_; lean_object* v_res_293_; 
v_x_36__boxed_292_ = lean_unbox(v_x_291_);
v_res_293_ = l_Lean_instToStringAttributeKind___lam__0(v_x_36__boxed_292_);
return v_res_293_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_296_ = l_Lean_instInhabitedMessageData_default;
v___x_297_ = lean_box(0);
v___x_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
lean_ctor_set(v___x_298_, 1, v___x_296_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__0(lean_object* v_x_299_, lean_object* v___y_300_, uint8_t v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0, &l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0);
v___x_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__0___boxed(lean_object* v_x_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
uint8_t v___y_1006__boxed_313_; lean_object* v_res_314_; 
v___y_1006__boxed_313_ = lean_unbox(v___y_309_);
v_res_314_ = l_Lean_instInhabitedAttributeImpl_default___lam__0(v_x_307_, v___y_308_, v___y_1006__boxed_313_, v___y_310_, v___y_311_);
lean_dec(v___y_311_);
lean_dec_ref(v___y_310_);
lean_dec(v___y_308_);
lean_dec(v_x_307_);
return v_res_314_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_315_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0);
v___x_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
return v___x_317_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_318_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1);
v___x_319_ = lean_unsigned_to_nat(0u);
v___x_320_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
lean_ctor_set(v___x_320_, 2, v___x_319_);
lean_ctor_set(v___x_320_, 3, v___x_319_);
lean_ctor_set(v___x_320_, 4, v___x_318_);
lean_ctor_set(v___x_320_, 5, v___x_318_);
lean_ctor_set(v___x_320_, 6, v___x_318_);
lean_ctor_set(v___x_320_, 7, v___x_318_);
lean_ctor_set(v___x_320_, 8, v___x_318_);
lean_ctor_set(v___x_320_, 9, v___x_318_);
lean_ctor_set(v___x_320_, 10, v___x_318_);
return v___x_320_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_321_ = lean_unsigned_to_nat(32u);
v___x_322_ = lean_mk_empty_array_with_capacity(v___x_321_);
v___x_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
return v___x_323_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_324_ = ((size_t)5ULL);
v___x_325_ = lean_unsigned_to_nat(0u);
v___x_326_ = lean_unsigned_to_nat(32u);
v___x_327_ = lean_mk_empty_array_with_capacity(v___x_326_);
v___x_328_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3);
v___x_329_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_329_, 0, v___x_328_);
lean_ctor_set(v___x_329_, 1, v___x_327_);
lean_ctor_set(v___x_329_, 2, v___x_325_);
lean_ctor_set(v___x_329_, 3, v___x_325_);
lean_ctor_set_usize(v___x_329_, 4, v___x_324_);
return v___x_329_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_330_ = lean_box(1);
v___x_331_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4);
v___x_332_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1);
v___x_333_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v___x_331_);
lean_ctor_set(v___x_333_, 2, v___x_330_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(lean_object* v_msgData_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
lean_object* v___x_338_; lean_object* v_toCold_339_; lean_object* v_env_340_; lean_object* v_options_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_338_ = lean_st_ref_get(v___y_336_);
v_toCold_339_ = lean_ctor_get(v___y_335_, 0);
v_env_340_ = lean_ctor_get(v___x_338_, 0);
lean_inc_ref(v_env_340_);
lean_dec(v___x_338_);
v_options_341_ = lean_ctor_get(v_toCold_339_, 2);
v___x_342_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2);
v___x_343_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_341_);
v___x_344_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_344_, 0, v_env_340_);
lean_ctor_set(v___x_344_, 1, v___x_342_);
lean_ctor_set(v___x_344_, 2, v___x_343_);
lean_ctor_set(v___x_344_, 3, v_options_341_);
v___x_345_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
lean_ctor_set(v___x_345_, 1, v_msgData_334_);
v___x_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___boxed(lean_object* v_msgData_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v_msgData_347_, v___y_348_, v___y_349_);
lean_dec(v___y_349_);
lean_dec_ref(v___y_348_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(lean_object* v_msg_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v_ref_356_; lean_object* v___x_357_; lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_366_; 
v_ref_356_ = lean_ctor_get(v___y_353_, 2);
v___x_357_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v_msg_352_, v___y_353_, v___y_354_);
v_a_358_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_366_ == 0)
{
v___x_360_ = v___x_357_;
v_isShared_361_ = v_isSharedCheck_366_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_357_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_366_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_362_; lean_object* v___x_364_; 
lean_inc(v_ref_356_);
v___x_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_362_, 0, v_ref_356_);
lean_ctor_set(v___x_362_, 1, v_a_358_);
if (v_isShared_361_ == 0)
{
lean_ctor_set_tag(v___x_360_, 1);
lean_ctor_set(v___x_360_, 0, v___x_362_);
v___x_364_ = v___x_360_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_362_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg___boxed(lean_object* v_msg_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v_msg_367_, v___y_368_, v___y_369_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
return v_res_371_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__0));
v___x_374_ = l_Lean_stringToMessageData(v___x_373_);
return v___x_374_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__2));
v___x_377_ = l_Lean_stringToMessageData(v___x_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1(lean_object* v___x_378_, lean_object* v_decl_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_name_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v_name_383_ = lean_ctor_get(v___x_378_, 1);
lean_inc(v_name_383_);
lean_dec_ref(v___x_378_);
v___x_384_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_385_ = l_Lean_MessageData_ofName(v_name_383_);
v___x_386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_384_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
v___x_387_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_386_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
v___x_389_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_388_, v___y_380_, v___y_381_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1___boxed(lean_object* v___x_390_, lean_object* v_decl_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_instInhabitedAttributeImpl_default___lam__1(v___x_390_, v_decl_391_, v___y_392_, v___y_393_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v_decl_391_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0(lean_object* v_00_u03b1_404_, lean_object* v_msg_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v_msg_405_, v___y_406_, v___y_407_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___boxed(lean_object* v_00_u03b1_410_, lean_object* v_msg_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0(v_00_u03b1_410_, v_msg_411_, v___y_412_, v___y_413_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
return v_res_415_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_417_ = lean_box(0);
v___x_418_ = lean_unsigned_to_nat(16u);
v___x_419_ = lean_mk_array(v___x_418_, v___x_417_);
return v___x_419_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_420_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_421_ = lean_unsigned_to_nat(0u);
v___x_422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
lean_ctor_set(v___x_422_, 1, v___x_420_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_424_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_425_ = lean_st_mk_ref(v___x_424_);
v___x_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2____boxed(lean_object* v_a_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_();
return v_res_428_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(lean_object* v_a_429_, lean_object* v_x_430_){
_start:
{
if (lean_obj_tag(v_x_430_) == 0)
{
uint8_t v___x_431_; 
v___x_431_ = 0;
return v___x_431_;
}
else
{
lean_object* v_key_432_; lean_object* v_tail_433_; uint8_t v___x_434_; 
v_key_432_ = lean_ctor_get(v_x_430_, 0);
v_tail_433_ = lean_ctor_get(v_x_430_, 2);
v___x_434_ = lean_name_eq(v_key_432_, v_a_429_);
if (v___x_434_ == 0)
{
v_x_430_ = v_tail_433_;
goto _start;
}
else
{
return v___x_434_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg___boxed(lean_object* v_a_436_, lean_object* v_x_437_){
_start:
{
uint8_t v_res_438_; lean_object* v_r_439_; 
v_res_438_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_436_, v_x_437_);
lean_dec(v_x_437_);
lean_dec(v_a_436_);
v_r_439_ = lean_box(v_res_438_);
return v_r_439_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(lean_object* v_m_440_, lean_object* v_a_441_){
_start:
{
lean_object* v_buckets_442_; lean_object* v___x_443_; uint64_t v___y_445_; 
v_buckets_442_ = lean_ctor_get(v_m_440_, 1);
v___x_443_ = lean_array_get_size(v_buckets_442_);
if (lean_obj_tag(v_a_441_) == 0)
{
uint64_t v___x_459_; 
v___x_459_ = 1723ULL;
v___y_445_ = v___x_459_;
goto v___jp_444_;
}
else
{
uint64_t v_hash_460_; 
v_hash_460_ = lean_ctor_get_uint64(v_a_441_, sizeof(void*)*2);
v___y_445_ = v_hash_460_;
goto v___jp_444_;
}
v___jp_444_:
{
uint64_t v___x_446_; uint64_t v___x_447_; uint64_t v_fold_448_; uint64_t v___x_449_; uint64_t v___x_450_; uint64_t v___x_451_; size_t v___x_452_; size_t v___x_453_; size_t v___x_454_; size_t v___x_455_; size_t v___x_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_446_ = 32ULL;
v___x_447_ = lean_uint64_shift_right(v___y_445_, v___x_446_);
v_fold_448_ = lean_uint64_xor(v___y_445_, v___x_447_);
v___x_449_ = 16ULL;
v___x_450_ = lean_uint64_shift_right(v_fold_448_, v___x_449_);
v___x_451_ = lean_uint64_xor(v_fold_448_, v___x_450_);
v___x_452_ = lean_uint64_to_usize(v___x_451_);
v___x_453_ = lean_usize_of_nat(v___x_443_);
v___x_454_ = ((size_t)1ULL);
v___x_455_ = lean_usize_sub(v___x_453_, v___x_454_);
v___x_456_ = lean_usize_land(v___x_452_, v___x_455_);
v___x_457_ = lean_array_uget_borrowed(v_buckets_442_, v___x_456_);
v___x_458_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_441_, v___x_457_);
return v___x_458_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___boxed(lean_object* v_m_461_, lean_object* v_a_462_){
_start:
{
uint8_t v_res_463_; lean_object* v_r_464_; 
v_res_463_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_m_461_, v_a_462_);
lean_dec(v_a_462_);
lean_dec_ref(v_m_461_);
v_r_464_ = lean_box(v_res_463_);
return v_r_464_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(lean_object* v_a_465_, lean_object* v_b_466_, lean_object* v_x_467_){
_start:
{
if (lean_obj_tag(v_x_467_) == 0)
{
lean_dec(v_b_466_);
lean_dec(v_a_465_);
return v_x_467_;
}
else
{
lean_object* v_key_468_; lean_object* v_value_469_; lean_object* v_tail_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_482_; 
v_key_468_ = lean_ctor_get(v_x_467_, 0);
v_value_469_ = lean_ctor_get(v_x_467_, 1);
v_tail_470_ = lean_ctor_get(v_x_467_, 2);
v_isSharedCheck_482_ = !lean_is_exclusive(v_x_467_);
if (v_isSharedCheck_482_ == 0)
{
v___x_472_ = v_x_467_;
v_isShared_473_ = v_isSharedCheck_482_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_tail_470_);
lean_inc(v_value_469_);
lean_inc(v_key_468_);
lean_dec(v_x_467_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_482_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
uint8_t v___x_474_; 
v___x_474_ = lean_name_eq(v_key_468_, v_a_465_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; lean_object* v___x_477_; 
v___x_475_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(v_a_465_, v_b_466_, v_tail_470_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 2, v___x_475_);
v___x_477_ = v___x_472_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_key_468_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v_value_469_);
lean_ctor_set(v_reuseFailAlloc_478_, 2, v___x_475_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
else
{
lean_object* v___x_480_; 
lean_dec(v_value_469_);
lean_dec(v_key_468_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 1, v_b_466_);
lean_ctor_set(v___x_472_, 0, v_a_465_);
v___x_480_ = v___x_472_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_465_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v_b_466_);
lean_ctor_set(v_reuseFailAlloc_481_, 2, v_tail_470_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_483_, lean_object* v_x_484_){
_start:
{
if (lean_obj_tag(v_x_484_) == 0)
{
return v_x_483_;
}
else
{
lean_object* v_key_485_; lean_object* v_value_486_; lean_object* v_tail_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_513_; 
v_key_485_ = lean_ctor_get(v_x_484_, 0);
v_value_486_ = lean_ctor_get(v_x_484_, 1);
v_tail_487_ = lean_ctor_get(v_x_484_, 2);
v_isSharedCheck_513_ = !lean_is_exclusive(v_x_484_);
if (v_isSharedCheck_513_ == 0)
{
v___x_489_ = v_x_484_;
v_isShared_490_ = v_isSharedCheck_513_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_tail_487_);
lean_inc(v_value_486_);
lean_inc(v_key_485_);
lean_dec(v_x_484_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_513_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_491_; uint64_t v___y_493_; 
v___x_491_ = lean_array_get_size(v_x_483_);
if (lean_obj_tag(v_key_485_) == 0)
{
uint64_t v___x_511_; 
v___x_511_ = 1723ULL;
v___y_493_ = v___x_511_;
goto v___jp_492_;
}
else
{
uint64_t v_hash_512_; 
v_hash_512_ = lean_ctor_get_uint64(v_key_485_, sizeof(void*)*2);
v___y_493_ = v_hash_512_;
goto v___jp_492_;
}
v___jp_492_:
{
uint64_t v___x_494_; uint64_t v___x_495_; uint64_t v_fold_496_; uint64_t v___x_497_; uint64_t v___x_498_; uint64_t v___x_499_; size_t v___x_500_; size_t v___x_501_; size_t v___x_502_; size_t v___x_503_; size_t v___x_504_; lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_494_ = 32ULL;
v___x_495_ = lean_uint64_shift_right(v___y_493_, v___x_494_);
v_fold_496_ = lean_uint64_xor(v___y_493_, v___x_495_);
v___x_497_ = 16ULL;
v___x_498_ = lean_uint64_shift_right(v_fold_496_, v___x_497_);
v___x_499_ = lean_uint64_xor(v_fold_496_, v___x_498_);
v___x_500_ = lean_uint64_to_usize(v___x_499_);
v___x_501_ = lean_usize_of_nat(v___x_491_);
v___x_502_ = ((size_t)1ULL);
v___x_503_ = lean_usize_sub(v___x_501_, v___x_502_);
v___x_504_ = lean_usize_land(v___x_500_, v___x_503_);
v___x_505_ = lean_array_uget_borrowed(v_x_483_, v___x_504_);
lean_inc(v___x_505_);
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 2, v___x_505_);
v___x_507_ = v___x_489_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_key_485_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v_value_486_);
lean_ctor_set(v_reuseFailAlloc_510_, 2, v___x_505_);
v___x_507_ = v_reuseFailAlloc_510_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_508_; 
v___x_508_ = lean_array_uset(v_x_483_, v___x_504_, v___x_507_);
v_x_483_ = v___x_508_;
v_x_484_ = v_tail_487_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(lean_object* v_i_514_, lean_object* v_source_515_, lean_object* v_target_516_){
_start:
{
lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_517_ = lean_array_get_size(v_source_515_);
v___x_518_ = lean_nat_dec_lt(v_i_514_, v___x_517_);
if (v___x_518_ == 0)
{
lean_dec_ref(v_source_515_);
lean_dec(v_i_514_);
return v_target_516_;
}
else
{
lean_object* v_es_519_; lean_object* v___x_520_; lean_object* v_source_521_; lean_object* v_target_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v_es_519_ = lean_array_fget(v_source_515_, v_i_514_);
v___x_520_ = lean_box(0);
v_source_521_ = lean_array_fset(v_source_515_, v_i_514_, v___x_520_);
v_target_522_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(v_target_516_, v_es_519_);
v___x_523_ = lean_unsigned_to_nat(1u);
v___x_524_ = lean_nat_add(v_i_514_, v___x_523_);
lean_dec(v_i_514_);
v_i_514_ = v___x_524_;
v_source_515_ = v_source_521_;
v_target_516_ = v_target_522_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(lean_object* v_data_526_){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v_nbuckets_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_527_ = lean_array_get_size(v_data_526_);
v___x_528_ = lean_unsigned_to_nat(2u);
v_nbuckets_529_ = lean_nat_mul(v___x_527_, v___x_528_);
v___x_530_ = lean_unsigned_to_nat(0u);
v___x_531_ = lean_box(0);
v___x_532_ = lean_mk_array(v_nbuckets_529_, v___x_531_);
v___x_533_ = lean_array_propagate_mark(v_data_526_, v___x_532_);
v___x_534_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(v___x_530_, v_data_526_, v___x_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(lean_object* v_m_535_, lean_object* v_a_536_, lean_object* v_b_537_){
_start:
{
lean_object* v_size_538_; lean_object* v_buckets_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_585_; 
v_size_538_ = lean_ctor_get(v_m_535_, 0);
v_buckets_539_ = lean_ctor_get(v_m_535_, 1);
v_isSharedCheck_585_ = !lean_is_exclusive(v_m_535_);
if (v_isSharedCheck_585_ == 0)
{
v___x_541_ = v_m_535_;
v_isShared_542_ = v_isSharedCheck_585_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_buckets_539_);
lean_inc(v_size_538_);
lean_dec(v_m_535_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_585_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_543_; uint64_t v___y_545_; 
v___x_543_ = lean_array_get_size(v_buckets_539_);
if (lean_obj_tag(v_a_536_) == 0)
{
uint64_t v___x_583_; 
v___x_583_ = 1723ULL;
v___y_545_ = v___x_583_;
goto v___jp_544_;
}
else
{
uint64_t v_hash_584_; 
v_hash_584_ = lean_ctor_get_uint64(v_a_536_, sizeof(void*)*2);
v___y_545_ = v_hash_584_;
goto v___jp_544_;
}
v___jp_544_:
{
uint64_t v___x_546_; uint64_t v___x_547_; uint64_t v_fold_548_; uint64_t v___x_549_; uint64_t v___x_550_; uint64_t v___x_551_; size_t v___x_552_; size_t v___x_553_; size_t v___x_554_; size_t v___x_555_; size_t v___x_556_; lean_object* v_bkt_557_; uint8_t v___x_558_; 
v___x_546_ = 32ULL;
v___x_547_ = lean_uint64_shift_right(v___y_545_, v___x_546_);
v_fold_548_ = lean_uint64_xor(v___y_545_, v___x_547_);
v___x_549_ = 16ULL;
v___x_550_ = lean_uint64_shift_right(v_fold_548_, v___x_549_);
v___x_551_ = lean_uint64_xor(v_fold_548_, v___x_550_);
v___x_552_ = lean_uint64_to_usize(v___x_551_);
v___x_553_ = lean_usize_of_nat(v___x_543_);
v___x_554_ = ((size_t)1ULL);
v___x_555_ = lean_usize_sub(v___x_553_, v___x_554_);
v___x_556_ = lean_usize_land(v___x_552_, v___x_555_);
v_bkt_557_ = lean_array_uget_borrowed(v_buckets_539_, v___x_556_);
v___x_558_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_536_, v_bkt_557_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; lean_object* v_size_x27_560_; lean_object* v___x_561_; lean_object* v_buckets_x27_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; uint8_t v___x_568_; 
v___x_559_ = lean_unsigned_to_nat(1u);
v_size_x27_560_ = lean_nat_add(v_size_538_, v___x_559_);
lean_dec(v_size_538_);
lean_inc(v_bkt_557_);
v___x_561_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_561_, 0, v_a_536_);
lean_ctor_set(v___x_561_, 1, v_b_537_);
lean_ctor_set(v___x_561_, 2, v_bkt_557_);
v_buckets_x27_562_ = lean_array_uset(v_buckets_539_, v___x_556_, v___x_561_);
v___x_563_ = lean_unsigned_to_nat(4u);
v___x_564_ = lean_nat_mul(v_size_x27_560_, v___x_563_);
v___x_565_ = lean_unsigned_to_nat(3u);
v___x_566_ = lean_nat_div(v___x_564_, v___x_565_);
lean_dec(v___x_564_);
v___x_567_ = lean_array_get_size(v_buckets_x27_562_);
v___x_568_ = lean_nat_dec_le(v___x_566_, v___x_567_);
lean_dec(v___x_566_);
if (v___x_568_ == 0)
{
lean_object* v_val_569_; lean_object* v___x_571_; 
v_val_569_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(v_buckets_x27_562_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 1, v_val_569_);
lean_ctor_set(v___x_541_, 0, v_size_x27_560_);
v___x_571_ = v___x_541_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_size_x27_560_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_val_569_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
else
{
lean_object* v___x_574_; 
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 1, v_buckets_x27_562_);
lean_ctor_set(v___x_541_, 0, v_size_x27_560_);
v___x_574_ = v___x_541_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_size_x27_560_);
lean_ctor_set(v_reuseFailAlloc_575_, 1, v_buckets_x27_562_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
else
{
lean_object* v___x_576_; lean_object* v_buckets_x27_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_581_; 
lean_inc(v_bkt_557_);
v___x_576_ = lean_box(0);
v_buckets_x27_577_ = lean_array_uset(v_buckets_539_, v___x_556_, v___x_576_);
v___x_578_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(v_a_536_, v_b_537_, v_bkt_557_);
v___x_579_ = lean_array_uset(v_buckets_x27_577_, v___x_556_, v___x_578_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 1, v___x_579_);
v___x_581_ = v___x_541_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_size_538_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v___x_579_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_registerBuiltinAttribute___closed__1(void){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_587_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__0));
v___x_588_ = lean_mk_io_user_error(v___x_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerBuiltinAttribute(lean_object* v_attr_591_){
_start:
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v_toAttributeImplCore_595_; lean_object* v_name_596_; uint8_t v___x_597_; 
v___x_593_ = l_Lean_attributeMapRef;
v___x_594_ = lean_st_ref_get(v___x_593_);
v_toAttributeImplCore_595_ = lean_ctor_get(v_attr_591_, 0);
v_name_596_ = lean_ctor_get(v_toAttributeImplCore_595_, 1);
lean_inc(v_name_596_);
v___x_597_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_594_, v_name_596_);
lean_dec(v___x_594_);
if (v___x_597_ == 0)
{
uint8_t v___x_598_; 
v___x_598_ = l_Lean_initializing();
if (v___x_598_ == 0)
{
lean_object* v___x_599_; lean_object* v___x_600_; 
lean_dec(v_name_596_);
lean_dec_ref(v_attr_591_);
v___x_599_ = lean_obj_once(&l_Lean_registerBuiltinAttribute___closed__1, &l_Lean_registerBuiltinAttribute___closed__1_once, _init_l_Lean_registerBuiltinAttribute___closed__1);
v___x_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
return v___x_600_;
}
else
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_601_ = lean_st_ref_take(v___x_593_);
v___x_602_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_601_, v_name_596_, v_attr_591_);
v___x_603_ = lean_st_ref_put(v___x_593_, v___x_602_);
v___x_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
return v___x_604_;
}
}
else
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
lean_dec_ref(v_attr_591_);
v___x_605_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_606_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_596_, v___x_597_);
v___x_607_ = lean_string_append(v___x_605_, v___x_606_);
lean_dec_ref(v___x_606_);
v___x_608_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_609_ = lean_string_append(v___x_607_, v___x_608_);
v___x_610_ = lean_mk_io_user_error(v___x_609_);
v___x_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
return v___x_611_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerBuiltinAttribute___boxed(lean_object* v_attr_612_, lean_object* v_a_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_registerBuiltinAttribute(v_attr_612_);
return v_res_614_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0(lean_object* v_00_u03b2_615_, lean_object* v_m_616_, lean_object* v_a_617_){
_start:
{
uint8_t v___x_618_; 
v___x_618_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_m_616_, v_a_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___boxed(lean_object* v_00_u03b2_619_, lean_object* v_m_620_, lean_object* v_a_621_){
_start:
{
uint8_t v_res_622_; lean_object* v_r_623_; 
v_res_622_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0(v_00_u03b2_619_, v_m_620_, v_a_621_);
lean_dec(v_a_621_);
lean_dec_ref(v_m_620_);
v_r_623_ = lean_box(v_res_622_);
return v_r_623_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1(lean_object* v_00_u03b2_624_, lean_object* v_m_625_, lean_object* v_a_626_, lean_object* v_b_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_m_625_, v_a_626_, v_b_627_);
return v___x_628_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0(lean_object* v_00_u03b2_629_, lean_object* v_a_630_, lean_object* v_x_631_){
_start:
{
uint8_t v___x_632_; 
v___x_632_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_630_, v_x_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___boxed(lean_object* v_00_u03b2_633_, lean_object* v_a_634_, lean_object* v_x_635_){
_start:
{
uint8_t v_res_636_; lean_object* v_r_637_; 
v_res_636_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0(v_00_u03b2_633_, v_a_634_, v_x_635_);
lean_dec(v_x_635_);
lean_dec(v_a_634_);
v_r_637_ = lean_box(v_res_636_);
return v_r_637_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2(lean_object* v_00_u03b2_638_, lean_object* v_data_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(v_data_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3(lean_object* v_00_u03b2_641_, lean_object* v_a_642_, lean_object* v_b_643_, lean_object* v_x_644_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(v_a_642_, v_b_643_, v_x_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_646_, lean_object* v_i_647_, lean_object* v_source_648_, lean_object* v_target_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(v_i_647_, v_source_648_, v_target_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_651_, lean_object* v_x_652_, lean_object* v_x_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(v_x_652_, v_x_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(lean_object* v_ref_655_, lean_object* v_msg_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v_toCold_660_; lean_object* v_currRecDepth_661_; lean_object* v_ref_662_; uint8_t v_diag_663_; uint8_t v_suppressElabErrors_664_; lean_object* v_ref_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v_toCold_660_ = lean_ctor_get(v___y_657_, 0);
v_currRecDepth_661_ = lean_ctor_get(v___y_657_, 1);
v_ref_662_ = lean_ctor_get(v___y_657_, 2);
v_diag_663_ = lean_ctor_get_uint8(v___y_657_, sizeof(void*)*3);
v_suppressElabErrors_664_ = lean_ctor_get_uint8(v___y_657_, sizeof(void*)*3 + 1);
v_ref_665_ = l_Lean_replaceRef(v_ref_655_, v_ref_662_);
lean_inc(v_currRecDepth_661_);
lean_inc_ref(v_toCold_660_);
v___x_666_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_666_, 0, v_toCold_660_);
lean_ctor_set(v___x_666_, 1, v_currRecDepth_661_);
lean_ctor_set(v___x_666_, 2, v_ref_665_);
lean_ctor_set_uint8(v___x_666_, sizeof(void*)*3, v_diag_663_);
lean_ctor_set_uint8(v___x_666_, sizeof(void*)*3 + 1, v_suppressElabErrors_664_);
v___x_667_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v_msg_656_, v___x_666_, v___y_658_);
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
lean_object* v___x_1140_; lean_object* v_env_1141_; lean_object* v_nextMacroScope_1142_; lean_object* v_ngen_1143_; lean_object* v_auxDeclNGen_1144_; lean_object* v_traceState_1145_; lean_object* v_messages_1146_; lean_object* v_infoState_1147_; lean_object* v_snapshotTasks_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1159_; 
v___x_1140_ = lean_st_ref_take(v___y_1135_);
v_env_1141_ = lean_ctor_get(v___x_1140_, 0);
v_nextMacroScope_1142_ = lean_ctor_get(v___x_1140_, 1);
v_ngen_1143_ = lean_ctor_get(v___x_1140_, 2);
v_auxDeclNGen_1144_ = lean_ctor_get(v___x_1140_, 3);
v_traceState_1145_ = lean_ctor_get(v___x_1140_, 4);
v_messages_1146_ = lean_ctor_get(v___x_1140_, 6);
v_infoState_1147_ = lean_ctor_get(v___x_1140_, 7);
v_snapshotTasks_1148_ = lean_ctor_get(v___x_1140_, 8);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1159_ == 0)
{
lean_object* v_unused_1160_; 
v_unused_1160_ = lean_ctor_get(v___x_1140_, 5);
lean_dec(v_unused_1160_);
v___x_1150_ = v___x_1140_;
v_isShared_1151_ = v_isSharedCheck_1159_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_snapshotTasks_1148_);
lean_inc(v_infoState_1147_);
lean_inc(v_messages_1146_);
lean_inc(v_traceState_1145_);
lean_inc(v_auxDeclNGen_1144_);
lean_inc(v_ngen_1143_);
lean_inc(v_nextMacroScope_1142_);
lean_inc(v_env_1141_);
lean_dec(v___x_1140_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1159_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1152_; lean_object* v___x_1154_; 
v___x_1152_ = l_Lean_Environment_setExporting(v_env_1141_, v_isExporting_1136_);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 5, v___x_1137_);
lean_ctor_set(v___x_1150_, 0, v___x_1152_);
v___x_1154_ = v___x_1150_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1152_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v_nextMacroScope_1142_);
lean_ctor_set(v_reuseFailAlloc_1158_, 2, v_ngen_1143_);
lean_ctor_set(v_reuseFailAlloc_1158_, 3, v_auxDeclNGen_1144_);
lean_ctor_set(v_reuseFailAlloc_1158_, 4, v_traceState_1145_);
lean_ctor_set(v_reuseFailAlloc_1158_, 5, v___x_1137_);
lean_ctor_set(v_reuseFailAlloc_1158_, 6, v_messages_1146_);
lean_ctor_set(v_reuseFailAlloc_1158_, 7, v_infoState_1147_);
lean_ctor_set(v_reuseFailAlloc_1158_, 8, v_snapshotTasks_1148_);
v___x_1154_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1155_ = lean_st_ref_put(v___y_1135_, v___x_1154_);
v___x_1156_ = lean_box(0);
v___x_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
return v___x_1157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0___boxed(lean_object* v___y_1161_, lean_object* v_isExporting_1162_, lean_object* v___x_1163_, lean_object* v_a_x3f_1164_, lean_object* v___y_1165_){
_start:
{
uint8_t v_isExporting_boxed_1166_; lean_object* v_res_1167_; 
v_isExporting_boxed_1166_ = lean_unbox(v_isExporting_1162_);
v_res_1167_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1161_, v_isExporting_boxed_1166_, v___x_1163_, v_a_x3f_1164_);
lean_dec(v_a_x3f_1164_);
lean_dec(v___y_1161_);
return v_res_1167_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1168_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1169_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0);
v___x_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1169_);
return v___x_1170_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1171_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
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
lean_object* v___x_1234_; 
lean_inc(v___y_1176_);
lean_inc_ref(v___y_1175_);
v___x_1234_ = lean_apply_3(v_x_1173_, v___y_1175_, v___y_1176_, lean_box(0));
return v___x_1234_;
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
lean_object* v___x_1235_; 
lean_inc(v___y_1176_);
lean_inc_ref(v___y_1175_);
v___x_1235_ = lean_apply_3(v_x_1173_, v___y_1175_, v___y_1176_, lean_box(0));
return v___x_1235_;
}
}
v___jp_1184_:
{
lean_object* v___x_1185_; lean_object* v_env_1186_; lean_object* v_nextMacroScope_1187_; lean_object* v_ngen_1188_; lean_object* v_auxDeclNGen_1189_; lean_object* v_traceState_1190_; lean_object* v_messages_1191_; lean_object* v_infoState_1192_; lean_object* v_snapshotTasks_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1232_; 
v___x_1185_ = lean_st_ref_take(v___y_1176_);
v_env_1186_ = lean_ctor_get(v___x_1185_, 0);
v_nextMacroScope_1187_ = lean_ctor_get(v___x_1185_, 1);
v_ngen_1188_ = lean_ctor_get(v___x_1185_, 2);
v_auxDeclNGen_1189_ = lean_ctor_get(v___x_1185_, 3);
v_traceState_1190_ = lean_ctor_get(v___x_1185_, 4);
v_messages_1191_ = lean_ctor_get(v___x_1185_, 6);
v_infoState_1192_ = lean_ctor_get(v___x_1185_, 7);
v_snapshotTasks_1193_ = lean_ctor_get(v___x_1185_, 8);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1232_ == 0)
{
lean_object* v_unused_1233_; 
v_unused_1233_ = lean_ctor_get(v___x_1185_, 5);
lean_dec(v_unused_1233_);
v___x_1195_ = v___x_1185_;
v_isShared_1196_ = v_isSharedCheck_1232_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_snapshotTasks_1193_);
lean_inc(v_infoState_1192_);
lean_inc(v_messages_1191_);
lean_inc(v_traceState_1190_);
lean_inc(v_auxDeclNGen_1189_);
lean_inc(v_ngen_1188_);
lean_inc(v_nextMacroScope_1187_);
lean_inc(v_env_1186_);
lean_dec(v___x_1185_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1232_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1200_; 
v___x_1197_ = l_Lean_Environment_setExporting(v_env_1186_, v_isExporting_1174_);
v___x_1198_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 5, v___x_1198_);
lean_ctor_set(v___x_1195_, 0, v___x_1197_);
v___x_1200_ = v___x_1195_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1197_);
lean_ctor_set(v_reuseFailAlloc_1231_, 1, v_nextMacroScope_1187_);
lean_ctor_set(v_reuseFailAlloc_1231_, 2, v_ngen_1188_);
lean_ctor_set(v_reuseFailAlloc_1231_, 3, v_auxDeclNGen_1189_);
lean_ctor_set(v_reuseFailAlloc_1231_, 4, v_traceState_1190_);
lean_ctor_set(v_reuseFailAlloc_1231_, 5, v___x_1198_);
lean_ctor_set(v_reuseFailAlloc_1231_, 6, v_messages_1191_);
lean_ctor_set(v_reuseFailAlloc_1231_, 7, v_infoState_1192_);
lean_ctor_set(v_reuseFailAlloc_1231_, 8, v_snapshotTasks_1193_);
v___x_1200_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
lean_object* v___x_1201_; lean_object* v_r_1202_; 
v___x_1201_ = lean_st_ref_put(v___y_1176_, v___x_1200_);
lean_inc(v___y_1176_);
lean_inc_ref(v___y_1175_);
v_r_1202_ = lean_apply_3(v_x_1173_, v___y_1175_, v___y_1176_, lean_box(0));
if (lean_obj_tag(v_r_1202_) == 0)
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1219_; 
v_a_1203_ = lean_ctor_get(v_r_1202_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v_r_1202_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1205_ = v_r_1202_;
v_isShared_1206_ = v_isSharedCheck_1219_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v_r_1202_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1219_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
lean_inc(v_a_1203_);
if (v_isShared_1206_ == 0)
{
lean_ctor_set_tag(v___x_1205_, 1);
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_a_1203_);
v___x_1208_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
lean_object* v___x_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
v___x_1209_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1176_, v_isExporting_1183_, v___x_1198_, v___x_1208_);
lean_dec_ref(v___x_1208_);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1216_ == 0)
{
lean_object* v_unused_1217_; 
v_unused_1217_ = lean_ctor_get(v___x_1209_, 0);
lean_dec(v_unused_1217_);
v___x_1211_ = v___x_1209_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_dec(v___x_1209_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 0, v_a_1203_);
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1203_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
}
else
{
lean_object* v_a_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1229_; 
v_a_1220_ = lean_ctor_get(v_r_1202_, 0);
lean_inc(v_a_1220_);
lean_dec_ref_known(v_r_1202_, 1);
v___x_1221_ = lean_box(0);
v___x_1222_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1176_, v_isExporting_1183_, v___x_1198_, v___x_1221_);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1229_ == 0)
{
lean_object* v_unused_1230_; 
v_unused_1230_ = lean_ctor_get(v___x_1222_, 0);
lean_dec(v_unused_1230_);
v___x_1224_ = v___x_1222_;
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
else
{
lean_dec(v___x_1222_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
lean_ctor_set_tag(v___x_1224_, 1);
lean_ctor_set(v___x_1224_, 0, v_a_1220_);
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_a_1220_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___boxed(lean_object* v_x_1236_, lean_object* v_isExporting_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
uint8_t v_isExporting_boxed_1241_; lean_object* v_res_1242_; 
v_isExporting_boxed_1241_ = lean_unbox(v_isExporting_1237_);
v_res_1242_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1236_, v_isExporting_boxed_1241_, v___y_1238_, v___y_1239_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(lean_object* v_00_u03b1_1243_, lean_object* v_x_1244_, uint8_t v_isExporting_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v___x_1249_; 
v___x_1249_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1244_, v_isExporting_1245_, v___y_1246_, v___y_1247_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___boxed(lean_object* v_00_u03b1_1250_, lean_object* v_x_1251_, lean_object* v_isExporting_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
uint8_t v_isExporting_boxed_1256_; lean_object* v_res_1257_; 
v_isExporting_boxed_1256_ = lean_unbox(v_isExporting_1252_);
v_res_1257_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(v_00_u03b1_1250_, v_x_1251_, v_isExporting_boxed_1256_, v___y_1253_, v___y_1254_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
return v_res_1257_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(lean_object* v_opts_1258_, lean_object* v_opt_1259_){
_start:
{
lean_object* v_name_1260_; lean_object* v_defValue_1261_; lean_object* v_map_1262_; lean_object* v___x_1263_; 
v_name_1260_ = lean_ctor_get(v_opt_1259_, 0);
v_defValue_1261_ = lean_ctor_get(v_opt_1259_, 1);
v_map_1262_ = lean_ctor_get(v_opts_1258_, 0);
v___x_1263_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1262_, v_name_1260_);
if (lean_obj_tag(v___x_1263_) == 0)
{
uint8_t v___x_1264_; 
v___x_1264_ = lean_unbox(v_defValue_1261_);
return v___x_1264_;
}
else
{
lean_object* v_val_1265_; 
v_val_1265_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_val_1265_);
lean_dec_ref_known(v___x_1263_, 1);
if (lean_obj_tag(v_val_1265_) == 1)
{
uint8_t v_v_1266_; 
v_v_1266_ = lean_ctor_get_uint8(v_val_1265_, 0);
lean_dec_ref_known(v_val_1265_, 0);
return v_v_1266_;
}
else
{
uint8_t v___x_1267_; 
lean_dec(v_val_1265_);
v___x_1267_ = lean_unbox(v_defValue_1261_);
return v___x_1267_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3___boxed(lean_object* v_opts_1268_, lean_object* v_opt_1269_){
_start:
{
uint8_t v_res_1270_; lean_object* v_r_1271_; 
v_res_1270_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_opts_1268_, v_opt_1269_);
lean_dec_ref(v_opt_1269_);
lean_dec_ref(v_opts_1268_);
v_r_1271_ = lean_box(v_res_1270_);
return v_r_1271_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(uint8_t v_suppressElabErrors_1279_, uint8_t v___y_1280_, lean_object* v_x_1281_){
_start:
{
if (lean_obj_tag(v_x_1281_) == 1)
{
lean_object* v_pre_1282_; 
v_pre_1282_ = lean_ctor_get(v_x_1281_, 0);
switch(lean_obj_tag(v_pre_1282_))
{
case 1:
{
lean_object* v_pre_1283_; 
v_pre_1283_ = lean_ctor_get(v_pre_1282_, 0);
switch(lean_obj_tag(v_pre_1283_))
{
case 0:
{
lean_object* v_str_1284_; lean_object* v_str_1285_; lean_object* v___x_1286_; uint8_t v___x_1287_; 
v_str_1284_ = lean_ctor_get(v_x_1281_, 1);
v_str_1285_ = lean_ctor_get(v_pre_1282_, 1);
v___x_1286_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__0));
v___x_1287_ = lean_string_dec_eq(v_str_1285_, v___x_1286_);
if (v___x_1287_ == 0)
{
lean_object* v___x_1288_; uint8_t v___x_1289_; 
v___x_1288_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__2));
v___x_1289_ = lean_string_dec_eq(v_str_1285_, v___x_1288_);
if (v___x_1289_ == 0)
{
return v___x_1289_;
}
else
{
lean_object* v___x_1290_; uint8_t v___x_1291_; 
v___x_1290_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__1));
v___x_1291_ = lean_string_dec_eq(v_str_1284_, v___x_1290_);
if (v___x_1291_ == 0)
{
return v___x_1291_;
}
else
{
return v_suppressElabErrors_1279_;
}
}
}
else
{
lean_object* v___x_1292_; uint8_t v___x_1293_; 
v___x_1292_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__2));
v___x_1293_ = lean_string_dec_eq(v_str_1284_, v___x_1292_);
if (v___x_1293_ == 0)
{
return v___x_1293_;
}
else
{
return v_suppressElabErrors_1279_;
}
}
}
case 1:
{
lean_object* v_pre_1294_; 
v_pre_1294_ = lean_ctor_get(v_pre_1283_, 0);
if (lean_obj_tag(v_pre_1294_) == 0)
{
lean_object* v_str_1295_; lean_object* v_str_1296_; lean_object* v_str_1297_; lean_object* v___x_1298_; uint8_t v___x_1299_; 
v_str_1295_ = lean_ctor_get(v_x_1281_, 1);
v_str_1296_ = lean_ctor_get(v_pre_1282_, 1);
v_str_1297_ = lean_ctor_get(v_pre_1283_, 1);
v___x_1298_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__3));
v___x_1299_ = lean_string_dec_eq(v_str_1297_, v___x_1298_);
if (v___x_1299_ == 0)
{
return v___x_1299_;
}
else
{
lean_object* v___x_1300_; uint8_t v___x_1301_; 
v___x_1300_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__4));
v___x_1301_ = lean_string_dec_eq(v_str_1296_, v___x_1300_);
if (v___x_1301_ == 0)
{
return v___x_1301_;
}
else
{
lean_object* v___x_1302_; uint8_t v___x_1303_; 
v___x_1302_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__5));
v___x_1303_ = lean_string_dec_eq(v_str_1295_, v___x_1302_);
if (v___x_1303_ == 0)
{
return v___x_1303_;
}
else
{
return v_suppressElabErrors_1279_;
}
}
}
}
else
{
return v___y_1280_;
}
}
default: 
{
return v___y_1280_;
}
}
}
case 0:
{
lean_object* v_str_1304_; lean_object* v___x_1305_; uint8_t v___x_1306_; 
v_str_1304_ = lean_ctor_get(v_x_1281_, 1);
v___x_1305_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__6));
v___x_1306_ = lean_string_dec_eq(v_str_1304_, v___x_1305_);
if (v___x_1306_ == 0)
{
return v___x_1306_;
}
else
{
return v_suppressElabErrors_1279_;
}
}
default: 
{
return v___y_1280_;
}
}
}
else
{
return v___y_1280_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed(lean_object* v_suppressElabErrors_1307_, lean_object* v___y_1308_, lean_object* v_x_1309_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1310_; uint8_t v___y_5018__boxed_1311_; uint8_t v_res_1312_; lean_object* v_r_1313_; 
v_suppressElabErrors_boxed_1310_ = lean_unbox(v_suppressElabErrors_1307_);
v___y_5018__boxed_1311_ = lean_unbox(v___y_1308_);
v_res_1312_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(v_suppressElabErrors_boxed_1310_, v___y_5018__boxed_1311_, v_x_1309_);
lean_dec(v_x_1309_);
v_r_1313_ = lean_box(v_res_1312_);
return v_r_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(lean_object* v_ref_1314_, lean_object* v_msgData_1315_, uint8_t v_severity_1316_, uint8_t v_isSilent_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
uint8_t v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1324_; uint8_t v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1359_; lean_object* v___y_1360_; uint8_t v___y_1361_; lean_object* v___y_1362_; uint8_t v___y_1363_; lean_object* v___y_1364_; uint8_t v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1384_; lean_object* v___y_1385_; uint8_t v___y_1386_; uint8_t v___y_1387_; uint8_t v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1395_; lean_object* v___y_1396_; uint8_t v___y_1397_; lean_object* v___y_1398_; uint8_t v___y_1399_; lean_object* v___y_1400_; uint8_t v___y_1401_; uint8_t v___x_1406_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; uint8_t v___y_1411_; lean_object* v___y_1412_; uint8_t v___y_1413_; uint8_t v___y_1414_; uint8_t v___y_1416_; uint8_t v___x_1432_; 
v___x_1406_ = 2;
v___x_1432_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1316_, v___x_1406_);
if (v___x_1432_ == 0)
{
v___y_1416_ = v___x_1432_;
goto v___jp_1415_;
}
else
{
uint8_t v___x_1433_; 
lean_inc_ref(v_msgData_1315_);
v___x_1433_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1315_);
v___y_1416_ = v___x_1433_;
goto v___jp_1415_;
}
v___jp_1321_:
{
lean_object* v___x_1331_; lean_object* v_toCold_1332_; lean_object* v_currNamespace_1333_; lean_object* v_openDecls_1334_; lean_object* v_env_1335_; lean_object* v_nextMacroScope_1336_; lean_object* v_ngen_1337_; lean_object* v_auxDeclNGen_1338_; lean_object* v_traceState_1339_; lean_object* v_cache_1340_; lean_object* v_messages_1341_; lean_object* v_infoState_1342_; lean_object* v_snapshotTasks_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1357_; 
v___x_1331_ = lean_st_ref_take(v___y_1330_);
v_toCold_1332_ = lean_ctor_get(v___y_1329_, 0);
v_currNamespace_1333_ = lean_ctor_get(v_toCold_1332_, 4);
v_openDecls_1334_ = lean_ctor_get(v_toCold_1332_, 5);
v_env_1335_ = lean_ctor_get(v___x_1331_, 0);
v_nextMacroScope_1336_ = lean_ctor_get(v___x_1331_, 1);
v_ngen_1337_ = lean_ctor_get(v___x_1331_, 2);
v_auxDeclNGen_1338_ = lean_ctor_get(v___x_1331_, 3);
v_traceState_1339_ = lean_ctor_get(v___x_1331_, 4);
v_cache_1340_ = lean_ctor_get(v___x_1331_, 5);
v_messages_1341_ = lean_ctor_get(v___x_1331_, 6);
v_infoState_1342_ = lean_ctor_get(v___x_1331_, 7);
v_snapshotTasks_1343_ = lean_ctor_get(v___x_1331_, 8);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1345_ = v___x_1331_;
v_isShared_1346_ = v_isSharedCheck_1357_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_snapshotTasks_1343_);
lean_inc(v_infoState_1342_);
lean_inc(v_messages_1341_);
lean_inc(v_cache_1340_);
lean_inc(v_traceState_1339_);
lean_inc(v_auxDeclNGen_1338_);
lean_inc(v_ngen_1337_);
lean_inc(v_nextMacroScope_1336_);
lean_inc(v_env_1335_);
lean_dec(v___x_1331_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1357_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1352_; 
lean_inc(v_openDecls_1334_);
lean_inc(v_currNamespace_1333_);
v___x_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1347_, 0, v_currNamespace_1333_);
lean_ctor_set(v___x_1347_, 1, v_openDecls_1334_);
v___x_1348_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1347_);
lean_ctor_set(v___x_1348_, 1, v___y_1323_);
lean_inc_ref(v___y_1324_);
lean_inc_ref(v___y_1327_);
v___x_1349_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1349_, 0, v___y_1327_);
lean_ctor_set(v___x_1349_, 1, v___y_1326_);
lean_ctor_set(v___x_1349_, 2, v___y_1328_);
lean_ctor_set(v___x_1349_, 3, v___y_1324_);
lean_ctor_set(v___x_1349_, 4, v___x_1348_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*5, v___y_1325_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*5 + 1, v___y_1322_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*5 + 2, v_isSilent_1317_);
v___x_1350_ = l_Lean_MessageLog_add(v___x_1349_, v_messages_1341_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 6, v___x_1350_);
v___x_1352_ = v___x_1345_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_env_1335_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_nextMacroScope_1336_);
lean_ctor_set(v_reuseFailAlloc_1356_, 2, v_ngen_1337_);
lean_ctor_set(v_reuseFailAlloc_1356_, 3, v_auxDeclNGen_1338_);
lean_ctor_set(v_reuseFailAlloc_1356_, 4, v_traceState_1339_);
lean_ctor_set(v_reuseFailAlloc_1356_, 5, v_cache_1340_);
lean_ctor_set(v_reuseFailAlloc_1356_, 6, v___x_1350_);
lean_ctor_set(v_reuseFailAlloc_1356_, 7, v_infoState_1342_);
lean_ctor_set(v_reuseFailAlloc_1356_, 8, v_snapshotTasks_1343_);
v___x_1352_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1353_ = lean_st_ref_put(v___y_1330_, v___x_1352_);
v___x_1354_ = lean_box(0);
v___x_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1354_);
return v___x_1355_;
}
}
}
v___jp_1358_:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1382_; 
v___x_1367_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1315_);
v___x_1368_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v___x_1367_, v___y_1318_, v___y_1319_);
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1371_ = v___x_1368_;
v_isShared_1372_ = v_isSharedCheck_1382_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1368_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1382_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
lean_inc_ref_n(v___y_1362_, 2);
v___x_1373_ = l_Lean_FileMap_toPosition(v___y_1362_, v___y_1360_);
lean_dec(v___y_1360_);
v___x_1374_ = l_Lean_FileMap_toPosition(v___y_1362_, v___y_1366_);
lean_dec(v___y_1366_);
v___x_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1374_);
v___x_1376_ = ((lean_object*)(l_Lean_instInhabitedAttributeImplCore_default___closed__3));
if (v___y_1363_ == 0)
{
lean_del_object(v___x_1371_);
lean_dec_ref(v___y_1359_);
v___y_1322_ = v___y_1361_;
v___y_1323_ = v_a_1369_;
v___y_1324_ = v___x_1376_;
v___y_1325_ = v___y_1365_;
v___y_1326_ = v___x_1373_;
v___y_1327_ = v___y_1364_;
v___y_1328_ = v___x_1375_;
v___y_1329_ = v___y_1318_;
v___y_1330_ = v___y_1319_;
goto v___jp_1321_;
}
else
{
uint8_t v___x_1377_; 
lean_inc(v_a_1369_);
v___x_1377_ = l_Lean_MessageData_hasTag(v___y_1359_, v_a_1369_);
if (v___x_1377_ == 0)
{
lean_object* v___x_1378_; lean_object* v___x_1380_; 
lean_dec_ref_known(v___x_1375_, 1);
lean_dec_ref(v___x_1373_);
lean_dec(v_a_1369_);
v___x_1378_ = lean_box(0);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 0, v___x_1378_);
v___x_1380_ = v___x_1371_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1378_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
else
{
lean_del_object(v___x_1371_);
v___y_1322_ = v___y_1361_;
v___y_1323_ = v_a_1369_;
v___y_1324_ = v___x_1376_;
v___y_1325_ = v___y_1365_;
v___y_1326_ = v___x_1373_;
v___y_1327_ = v___y_1364_;
v___y_1328_ = v___x_1375_;
v___y_1329_ = v___y_1318_;
v___y_1330_ = v___y_1319_;
goto v___jp_1321_;
}
}
}
}
v___jp_1383_:
{
lean_object* v___x_1392_; 
v___x_1392_ = l_Lean_Syntax_getTailPos_x3f(v___y_1390_, v___y_1388_);
lean_dec(v___y_1390_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_inc(v___y_1391_);
v___y_1359_ = v___y_1384_;
v___y_1360_ = v___y_1391_;
v___y_1361_ = v___y_1386_;
v___y_1362_ = v___y_1385_;
v___y_1363_ = v___y_1387_;
v___y_1364_ = v___y_1389_;
v___y_1365_ = v___y_1388_;
v___y_1366_ = v___y_1391_;
goto v___jp_1358_;
}
else
{
lean_object* v_val_1393_; 
v_val_1393_ = lean_ctor_get(v___x_1392_, 0);
lean_inc(v_val_1393_);
lean_dec_ref_known(v___x_1392_, 1);
v___y_1359_ = v___y_1384_;
v___y_1360_ = v___y_1391_;
v___y_1361_ = v___y_1386_;
v___y_1362_ = v___y_1385_;
v___y_1363_ = v___y_1387_;
v___y_1364_ = v___y_1389_;
v___y_1365_ = v___y_1388_;
v___y_1366_ = v_val_1393_;
goto v___jp_1358_;
}
}
v___jp_1394_:
{
lean_object* v_ref_1402_; lean_object* v___x_1403_; 
v_ref_1402_ = l_Lean_replaceRef(v_ref_1314_, v___y_1400_);
v___x_1403_ = l_Lean_Syntax_getPos_x3f(v_ref_1402_, v___y_1399_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_object* v___x_1404_; 
v___x_1404_ = lean_unsigned_to_nat(0u);
v___y_1384_ = v___y_1395_;
v___y_1385_ = v___y_1396_;
v___y_1386_ = v___y_1401_;
v___y_1387_ = v___y_1397_;
v___y_1388_ = v___y_1399_;
v___y_1389_ = v___y_1398_;
v___y_1390_ = v_ref_1402_;
v___y_1391_ = v___x_1404_;
goto v___jp_1383_;
}
else
{
lean_object* v_val_1405_; 
v_val_1405_ = lean_ctor_get(v___x_1403_, 0);
lean_inc(v_val_1405_);
lean_dec_ref_known(v___x_1403_, 1);
v___y_1384_ = v___y_1395_;
v___y_1385_ = v___y_1396_;
v___y_1386_ = v___y_1401_;
v___y_1387_ = v___y_1397_;
v___y_1388_ = v___y_1399_;
v___y_1389_ = v___y_1398_;
v___y_1390_ = v_ref_1402_;
v___y_1391_ = v_val_1405_;
goto v___jp_1383_;
}
}
v___jp_1407_:
{
if (v___y_1414_ == 0)
{
v___y_1395_ = v___y_1409_;
v___y_1396_ = v___y_1408_;
v___y_1397_ = v___y_1411_;
v___y_1398_ = v___y_1410_;
v___y_1399_ = v___y_1413_;
v___y_1400_ = v___y_1412_;
v___y_1401_ = v_severity_1316_;
goto v___jp_1394_;
}
else
{
v___y_1395_ = v___y_1409_;
v___y_1396_ = v___y_1408_;
v___y_1397_ = v___y_1411_;
v___y_1398_ = v___y_1410_;
v___y_1399_ = v___y_1413_;
v___y_1400_ = v___y_1412_;
v___y_1401_ = v___x_1406_;
goto v___jp_1394_;
}
}
v___jp_1415_:
{
if (v___y_1416_ == 0)
{
lean_object* v_toCold_1417_; lean_object* v_ref_1418_; uint8_t v_suppressElabErrors_1419_; lean_object* v_fileName_1420_; lean_object* v_fileMap_1421_; lean_object* v_options_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___f_1425_; uint8_t v___x_1426_; uint8_t v___x_1427_; 
v_toCold_1417_ = lean_ctor_get(v___y_1318_, 0);
v_ref_1418_ = lean_ctor_get(v___y_1318_, 2);
v_suppressElabErrors_1419_ = lean_ctor_get_uint8(v___y_1318_, sizeof(void*)*3 + 1);
v_fileName_1420_ = lean_ctor_get(v_toCold_1417_, 0);
v_fileMap_1421_ = lean_ctor_get(v_toCold_1417_, 1);
v_options_1422_ = lean_ctor_get(v_toCold_1417_, 2);
v___x_1423_ = lean_box(v_suppressElabErrors_1419_);
v___x_1424_ = lean_box(v___y_1416_);
v___f_1425_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1425_, 0, v___x_1423_);
lean_closure_set(v___f_1425_, 1, v___x_1424_);
v___x_1426_ = 1;
v___x_1427_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1316_, v___x_1426_);
if (v___x_1427_ == 0)
{
v___y_1408_ = v_fileMap_1421_;
v___y_1409_ = v___f_1425_;
v___y_1410_ = v_fileName_1420_;
v___y_1411_ = v_suppressElabErrors_1419_;
v___y_1412_ = v_ref_1418_;
v___y_1413_ = v___y_1416_;
v___y_1414_ = v___x_1427_;
goto v___jp_1407_;
}
else
{
lean_object* v___x_1428_; uint8_t v___x_1429_; 
v___x_1428_ = l_Lean_warningAsError;
v___x_1429_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_options_1422_, v___x_1428_);
v___y_1408_ = v_fileMap_1421_;
v___y_1409_ = v___f_1425_;
v___y_1410_ = v_fileName_1420_;
v___y_1411_ = v_suppressElabErrors_1419_;
v___y_1412_ = v_ref_1418_;
v___y_1413_ = v___y_1416_;
v___y_1414_ = v___x_1429_;
goto v___jp_1407_;
}
}
else
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
lean_dec_ref(v_msgData_1315_);
v___x_1430_ = lean_box(0);
v___x_1431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1430_);
return v___x_1431_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___boxed(lean_object* v_ref_1434_, lean_object* v_msgData_1435_, lean_object* v_severity_1436_, lean_object* v_isSilent_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
uint8_t v_severity_boxed_1441_; uint8_t v_isSilent_boxed_1442_; lean_object* v_res_1443_; 
v_severity_boxed_1441_ = lean_unbox(v_severity_1436_);
v_isSilent_boxed_1442_ = lean_unbox(v_isSilent_1437_);
v_res_1443_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1434_, v_msgData_1435_, v_severity_boxed_1441_, v_isSilent_boxed_1442_, v___y_1438_, v___y_1439_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec(v_ref_1434_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(lean_object* v_msgData_1444_, uint8_t v_severity_1445_, uint8_t v_isSilent_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v_ref_1450_; lean_object* v___x_1451_; 
v_ref_1450_ = lean_ctor_get(v___y_1447_, 2);
v___x_1451_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1450_, v_msgData_1444_, v_severity_1445_, v_isSilent_1446_, v___y_1447_, v___y_1448_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5___boxed(lean_object* v_msgData_1452_, lean_object* v_severity_1453_, lean_object* v_isSilent_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
uint8_t v_severity_boxed_1458_; uint8_t v_isSilent_boxed_1459_; lean_object* v_res_1460_; 
v_severity_boxed_1458_ = lean_unbox(v_severity_1453_);
v_isSilent_boxed_1459_ = lean_unbox(v_isSilent_1454_);
v_res_1460_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1452_, v_severity_boxed_1458_, v_isSilent_boxed_1459_, v___y_1455_, v___y_1456_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(lean_object* v_msgData_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
uint8_t v___x_1465_; uint8_t v___x_1466_; lean_object* v___x_1467_; 
v___x_1465_ = 1;
v___x_1466_ = 0;
v___x_1467_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1461_, v___x_1465_, v___x_1466_, v___y_1462_, v___y_1463_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1___boxed(lean_object* v_msgData_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v_msgData_1468_, v___y_1469_, v___y_1470_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(lean_object* v_opt_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v_toCold_1476_; lean_object* v_options_1477_; uint8_t v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v_toCold_1476_ = lean_ctor_get(v___y_1474_, 0);
v_options_1477_ = lean_ctor_get(v_toCold_1476_, 2);
v___x_1478_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_options_1477_, v_opt_1473_);
v___x_1479_ = lean_box(v___x_1478_);
v___x_1480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1480_, 0, v___x_1479_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg___boxed(lean_object* v_opt_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1481_, v___y_1482_);
lean_dec_ref(v___y_1482_);
lean_dec_ref(v_opt_1481_);
return v_res_1484_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1486_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__0));
v___x_1487_ = l_Lean_stringToMessageData(v___x_1486_);
return v___x_1487_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1489_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__2));
v___x_1490_ = l_Lean_stringToMessageData(v___x_1489_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(lean_object* v_id_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_){
_start:
{
lean_object* v___x_1495_; lean_object* v_env_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1518_; 
v___x_1495_ = lean_st_ref_get(v___y_1493_);
v_env_1496_ = lean_ctor_get(v___x_1495_, 0);
lean_inc_ref(v_env_1496_);
lean_dec(v___x_1495_);
v___x_1497_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1498_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v___x_1497_, v___y_1492_);
v_a_1499_ = lean_ctor_get(v___x_1498_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1501_ = v___x_1498_;
v_isShared_1502_ = v_isSharedCheck_1518_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1498_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1518_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
uint8_t v_isExporting_1508_; 
v_isExporting_1508_ = lean_ctor_get_uint8(v_env_1496_, sizeof(void*)*8);
lean_dec_ref(v_env_1496_);
if (v_isExporting_1508_ == 0)
{
lean_dec(v_a_1499_);
lean_dec(v_id_1491_);
goto v___jp_1503_;
}
else
{
uint8_t v___x_1509_; 
v___x_1509_ = l_Lean_isPrivateName(v_id_1491_);
if (v___x_1509_ == 0)
{
lean_dec(v_a_1499_);
lean_dec(v_id_1491_);
goto v___jp_1503_;
}
else
{
uint8_t v___x_1510_; 
v___x_1510_ = lean_unbox(v_a_1499_);
lean_dec(v_a_1499_);
if (v___x_1510_ == 0)
{
lean_dec(v_id_1491_);
goto v___jp_1503_;
}
else
{
lean_object* v___x_1511_; uint8_t v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
lean_del_object(v___x_1501_);
v___x_1511_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1);
v___x_1512_ = 0;
v___x_1513_ = l_Lean_MessageData_ofConstName(v_id_1491_, v___x_1512_);
v___x_1514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1511_);
lean_ctor_set(v___x_1514_, 1, v___x_1513_);
v___x_1515_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3);
v___x_1516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1514_);
lean_ctor_set(v___x_1516_, 1, v___x_1515_);
v___x_1517_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v___x_1516_, v___y_1492_, v___y_1493_);
return v___x_1517_;
}
}
}
v___jp_1503_:
{
lean_object* v___x_1504_; lean_object* v___x_1506_; 
v___x_1504_ = lean_box(0);
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 0, v___x_1504_);
v___x_1506_ = v___x_1501_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1504_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___boxed(lean_object* v_id_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_id_1519_, v___y_1520_, v___y_1521_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
return v_res_1523_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1525_ = ((lean_object*)(l_Lean_ensureAttrDeclIsPublic___lam__0___closed__0));
v___x_1526_ = l_Lean_stringToMessageData(v___x_1525_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0(lean_object* v_declName_1527_, uint8_t v_isModule_1528_, lean_object* v_attrName_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
lean_object* v___x_1533_; 
lean_inc(v_declName_1527_);
v___x_1533_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_declName_1527_, v___y_1530_, v___y_1531_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v___x_1534_; lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1555_; 
lean_dec_ref_known(v___x_1533_, 1);
lean_inc(v_declName_1527_);
v___x_1534_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_declName_1527_, v_isModule_1528_, v___y_1531_);
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1537_ = v___x_1534_;
v_isShared_1538_ = v_isSharedCheck_1555_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1534_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1555_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
uint8_t v___x_1539_; 
v___x_1539_ = lean_unbox(v_a_1535_);
if (v___x_1539_ == 0)
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; uint8_t v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
lean_del_object(v___x_1537_);
v___x_1540_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1541_ = l_Lean_MessageData_ofName(v_attrName_1529_);
v___x_1542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1540_);
lean_ctor_set(v___x_1542_, 1, v___x_1541_);
v___x_1543_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1542_);
lean_ctor_set(v___x_1544_, 1, v___x_1543_);
v___x_1545_ = lean_unbox(v_a_1535_);
lean_dec(v_a_1535_);
v___x_1546_ = l_Lean_MessageData_ofConstName(v_declName_1527_, v___x_1545_);
v___x_1547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1544_);
lean_ctor_set(v___x_1547_, 1, v___x_1546_);
v___x_1548_ = lean_obj_once(&l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1, &l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1_once, _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1);
v___x_1549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1547_);
lean_ctor_set(v___x_1549_, 1, v___x_1548_);
v___x_1550_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1549_, v___y_1530_, v___y_1531_);
return v___x_1550_;
}
else
{
lean_object* v___x_1551_; lean_object* v___x_1553_; 
lean_dec(v_a_1535_);
lean_dec(v_attrName_1529_);
lean_dec(v_declName_1527_);
v___x_1551_ = lean_box(0);
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 0, v___x_1551_);
v___x_1553_ = v___x_1537_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1551_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
}
else
{
lean_dec(v_attrName_1529_);
lean_dec(v_declName_1527_);
return v___x_1533_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0___boxed(lean_object* v_declName_1556_, lean_object* v_isModule_1557_, lean_object* v_attrName_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_){
_start:
{
uint8_t v_isModule_boxed_1562_; lean_object* v_res_1563_; 
v_isModule_boxed_1562_ = lean_unbox(v_isModule_1557_);
v_res_1563_ = l_Lean_ensureAttrDeclIsPublic___lam__0(v_declName_1556_, v_isModule_boxed_1562_, v_attrName_1558_, v___y_1559_, v___y_1560_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic(lean_object* v_attrName_1564_, lean_object* v_declName_1565_, uint8_t v_attrKind_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_){
_start:
{
lean_object* v___x_1570_; lean_object* v_env_1574_; lean_object* v___x_1575_; uint8_t v_isModule_1576_; 
v___x_1570_ = lean_st_ref_get(v_a_1568_);
v_env_1574_ = lean_ctor_get(v___x_1570_, 0);
lean_inc_ref(v_env_1574_);
lean_dec(v___x_1570_);
v___x_1575_ = l_Lean_Environment_header(v_env_1574_);
lean_dec_ref(v_env_1574_);
v_isModule_1576_ = lean_ctor_get_uint8(v___x_1575_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1575_);
if (v_isModule_1576_ == 0)
{
lean_dec(v_declName_1565_);
lean_dec(v_attrName_1564_);
goto v___jp_1571_;
}
else
{
uint8_t v___x_1577_; uint8_t v___x_1578_; 
v___x_1577_ = 1;
v___x_1578_ = l_Lean_instBEqAttributeKind_beq(v_attrKind_1566_, v___x_1577_);
if (v___x_1578_ == 0)
{
lean_object* v___x_1579_; lean_object* v___f_1580_; lean_object* v___x_1581_; 
v___x_1579_ = lean_box(v_isModule_1576_);
v___f_1580_ = lean_alloc_closure((void*)(l_Lean_ensureAttrDeclIsPublic___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1580_, 0, v_declName_1565_);
lean_closure_set(v___f_1580_, 1, v___x_1579_);
lean_closure_set(v___f_1580_, 2, v_attrName_1564_);
v___x_1581_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v___f_1580_, v_isModule_1576_, v_a_1567_, v_a_1568_);
return v___x_1581_;
}
else
{
lean_dec(v_declName_1565_);
lean_dec(v_attrName_1564_);
goto v___jp_1571_;
}
}
v___jp_1571_:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1572_ = lean_box(0);
v___x_1573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1572_);
return v___x_1573_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___boxed(lean_object* v_attrName_1582_, lean_object* v_declName_1583_, lean_object* v_attrKind_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_){
_start:
{
uint8_t v_attrKind_boxed_1588_; lean_object* v_res_1589_; 
v_attrKind_boxed_1588_ = lean_unbox(v_attrKind_1584_);
v_res_1589_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1582_, v_declName_1583_, v_attrKind_boxed_1588_, v_a_1585_, v_a_1586_);
lean_dec(v_a_1586_);
lean_dec_ref(v_a_1585_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(lean_object* v_opt_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1590_, v___y_1591_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___boxed(lean_object* v_opt_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(v_opt_1595_, v___y_1596_, v___y_1597_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
lean_dec_ref(v_opt_1595_);
return v_res_1599_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsMeta___closed__1(void){
_start:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1601_ = ((lean_object*)(l_Lean_ensureAttrDeclIsMeta___closed__0));
v___x_1602_ = l_Lean_stringToMessageData(v___x_1601_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object* v_attrName_1603_, lean_object* v_declName_1604_, uint8_t v_attrKind_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_){
_start:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v_env_1611_; lean_object* v___x_1612_; uint8_t v_isModule_1613_; 
v___x_1609_ = lean_st_ref_get(v_a_1607_);
v___x_1610_ = lean_st_ref_get(v_a_1607_);
v_env_1611_ = lean_ctor_get(v___x_1609_, 0);
lean_inc_ref(v_env_1611_);
lean_dec(v___x_1609_);
v___x_1612_ = l_Lean_Environment_header(v_env_1611_);
lean_dec_ref(v_env_1611_);
v_isModule_1613_ = lean_ctor_get_uint8(v___x_1612_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1612_);
if (v_isModule_1613_ == 0)
{
lean_object* v___x_1614_; 
lean_dec(v___x_1610_);
v___x_1614_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1603_, v_declName_1604_, v_attrKind_1605_, v_a_1606_, v_a_1607_);
return v___x_1614_;
}
else
{
lean_object* v_env_1615_; uint8_t v___x_1616_; 
v_env_1615_ = lean_ctor_get(v___x_1610_, 0);
lean_inc_ref(v_env_1615_);
lean_dec(v___x_1610_);
lean_inc(v_declName_1604_);
v___x_1616_ = l_Lean_isMarkedMeta(v_env_1615_, v_declName_1604_);
if (v___x_1616_ == 0)
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1617_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1618_ = l_Lean_MessageData_ofName(v_attrName_1603_);
v___x_1619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1617_);
lean_ctor_set(v___x_1619_, 1, v___x_1618_);
v___x_1620_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1619_);
lean_ctor_set(v___x_1621_, 1, v___x_1620_);
v___x_1622_ = l_Lean_MessageData_ofConstName(v_declName_1604_, v___x_1616_);
v___x_1623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1621_);
lean_ctor_set(v___x_1623_, 1, v___x_1622_);
v___x_1624_ = lean_obj_once(&l_Lean_ensureAttrDeclIsMeta___closed__1, &l_Lean_ensureAttrDeclIsMeta___closed__1_once, _init_l_Lean_ensureAttrDeclIsMeta___closed__1);
v___x_1625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1623_);
lean_ctor_set(v___x_1625_, 1, v___x_1624_);
v___x_1626_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1625_, v_a_1606_, v_a_1607_);
return v___x_1626_;
}
else
{
lean_object* v___x_1627_; 
v___x_1627_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1603_, v_declName_1604_, v_attrKind_1605_, v_a_1606_, v_a_1607_);
return v___x_1627_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta___boxed(lean_object* v_attrName_1628_, lean_object* v_declName_1629_, lean_object* v_attrKind_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_){
_start:
{
uint8_t v_attrKind_boxed_1634_; lean_object* v_res_1635_; 
v_attrKind_boxed_1634_ = lean_unbox(v_attrKind_1630_);
v_res_1635_ = l_Lean_ensureAttrDeclIsMeta(v_attrName_1628_, v_declName_1629_, v_attrKind_boxed_1634_, v_a_1631_, v_a_1632_);
lean_dec(v_a_1632_);
lean_dec_ref(v_a_1631_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0(lean_object* v_x_1639_, lean_object* v___y_1640_){
_start:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1642_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0___boxed(lean_object* v_x_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l_Lean_instInhabitedTagAttribute_default___lam__0(v_x_1644_, v___y_1645_);
lean_dec_ref(v___y_1645_);
lean_dec_ref(v_x_1644_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1(lean_object* v_s_1648_, lean_object* v_x_1649_){
_start:
{
lean_inc(v_s_1648_);
return v_s_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1___boxed(lean_object* v_s_1650_, lean_object* v_x_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_Lean_instInhabitedTagAttribute_default___lam__1(v_s_1650_, v_x_1651_);
lean_dec(v_x_1651_);
lean_dec(v_s_1650_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2(lean_object* v_x_1657_, lean_object* v_x_1658_){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__1));
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2___boxed(lean_object* v_x_1660_, lean_object* v_x_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_Lean_instInhabitedTagAttribute_default___lam__2(v_x_1660_, v_x_1661_);
lean_dec(v_x_1661_);
lean_dec_ref(v_x_1660_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3(lean_object* v_x_1663_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = lean_box(0);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3___boxed(lean_object* v_x_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l_Lean_instInhabitedTagAttribute_default___lam__3(v_x_1665_);
lean_dec(v_x_1665_);
return v_res_1666_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_1671_; 
v___x_1671_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_1671_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_1672_; lean_object* v___f_1673_; lean_object* v___f_1674_; lean_object* v___f_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___f_1672_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_1673_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__2));
v___f_1674_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__1));
v___f_1675_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__0));
v___x_1676_ = lean_box(0);
v___x_1677_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_1678_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1677_);
lean_ctor_set(v___x_1678_, 1, v___x_1676_);
lean_ctor_set(v___x_1678_, 2, v___f_1675_);
lean_ctor_set(v___x_1678_, 3, v___f_1674_);
lean_ctor_set(v___x_1678_, 4, v___f_1673_);
lean_ctor_set(v___x_1678_, 5, v___f_1672_);
return v___x_1678_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__6(void){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1679_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__5, &l_Lean_instInhabitedTagAttribute_default___closed__5_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__5);
v___x_1680_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_1681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1680_);
lean_ctor_set(v___x_1681_, 1, v___x_1679_);
return v___x_1681_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default(void){
_start:
{
lean_object* v___x_1682_; 
v___x_1682_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__6, &l_Lean_instInhabitedTagAttribute_default___closed__6_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__6);
return v___x_1682_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute(void){
_start:
{
lean_object* v___x_1683_; 
v___x_1683_ = l_Lean_instInhabitedTagAttribute_default;
return v___x_1683_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___auto__1(void){
_start:
{
lean_object* v___x_1684_; 
v___x_1684_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0(lean_object* v_x_1685_){
_start:
{
lean_object* v___x_1686_; 
v___x_1686_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0___boxed(lean_object* v_x_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_Lean_registerTagAttribute___lam__0(v_x_1687_);
lean_dec(v_x_1687_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0(lean_object* v_newState_1689_, lean_object* v_x_1690_, lean_object* v_x_1691_){
_start:
{
if (lean_obj_tag(v_x_1691_) == 0)
{
return v_x_1690_;
}
else
{
lean_object* v_head_1692_; lean_object* v_tail_1693_; uint8_t v___x_1694_; 
v_head_1692_ = lean_ctor_get(v_x_1691_, 0);
lean_inc(v_head_1692_);
v_tail_1693_ = lean_ctor_get(v_x_1691_, 1);
lean_inc(v_tail_1693_);
lean_dec_ref_known(v_x_1691_, 2);
v___x_1694_ = l_Lean_NameSet_contains(v_newState_1689_, v_head_1692_);
if (v___x_1694_ == 0)
{
lean_dec(v_head_1692_);
v_x_1691_ = v_tail_1693_;
goto _start;
}
else
{
lean_object* v___x_1696_; 
v___x_1696_ = l_Lean_NameSet_insert(v_x_1690_, v_head_1692_);
v_x_1690_ = v___x_1696_;
v_x_1691_ = v_tail_1693_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0___boxed(lean_object* v_newState_1698_, lean_object* v_x_1699_, lean_object* v_x_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1698_, v_x_1699_, v_x_1700_);
lean_dec(v_newState_1698_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1(lean_object* v_x_1702_, lean_object* v_newState_1703_, lean_object* v_newConsts_1704_, lean_object* v_s_1705_){
_start:
{
lean_object* v___x_1706_; 
v___x_1706_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1703_, v_s_1705_, v_newConsts_1704_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1___boxed(lean_object* v_x_1707_, lean_object* v_newState_1708_, lean_object* v_newConsts_1709_, lean_object* v_s_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l_Lean_registerTagAttribute___lam__1(v_x_1707_, v_newState_1708_, v_newConsts_1709_, v_s_1710_);
lean_dec(v_newState_1708_);
lean_dec(v_x_1707_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__2(lean_object* v_s_1724_){
_start:
{
lean_object* v___x_1725_; lean_object* v___y_1727_; 
v___x_1725_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__5));
if (lean_obj_tag(v_s_1724_) == 0)
{
lean_object* v_size_1731_; 
v_size_1731_ = lean_ctor_get(v_s_1724_, 0);
lean_inc(v_size_1731_);
lean_dec_ref_known(v_s_1724_, 5);
v___y_1727_ = v_size_1731_;
goto v___jp_1726_;
}
else
{
lean_object* v___x_1732_; 
v___x_1732_ = lean_unsigned_to_nat(0u);
v___y_1727_ = v___x_1732_;
goto v___jp_1726_;
}
v___jp_1726_:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1728_ = l_Nat_reprFast(v___y_1727_);
v___x_1729_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1728_);
v___x_1730_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1725_);
lean_ctor_set(v___x_1730_, 1, v___x_1729_);
return v___x_1730_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(lean_object* v_hi_1733_, lean_object* v_pivot_1734_, lean_object* v_as_1735_, lean_object* v_i_1736_, lean_object* v_k_1737_){
_start:
{
uint8_t v___x_1738_; 
v___x_1738_ = lean_nat_dec_lt(v_k_1737_, v_hi_1733_);
if (v___x_1738_ == 0)
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
lean_dec(v_k_1737_);
v___x_1739_ = lean_array_fswap(v_as_1735_, v_i_1736_, v_hi_1733_);
v___x_1740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1740_, 0, v_i_1736_);
lean_ctor_set(v___x_1740_, 1, v___x_1739_);
return v___x_1740_;
}
else
{
lean_object* v___x_1741_; uint8_t v___x_1742_; 
v___x_1741_ = lean_array_fget_borrowed(v_as_1735_, v_k_1737_);
v___x_1742_ = l_Lean_Name_quickLt(v___x_1741_, v_pivot_1734_);
if (v___x_1742_ == 0)
{
lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1743_ = lean_unsigned_to_nat(1u);
v___x_1744_ = lean_nat_add(v_k_1737_, v___x_1743_);
lean_dec(v_k_1737_);
v_k_1737_ = v___x_1744_;
goto _start;
}
else
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1746_ = lean_array_fswap(v_as_1735_, v_i_1736_, v_k_1737_);
v___x_1747_ = lean_unsigned_to_nat(1u);
v___x_1748_ = lean_nat_add(v_i_1736_, v___x_1747_);
lean_dec(v_i_1736_);
v___x_1749_ = lean_nat_add(v_k_1737_, v___x_1747_);
lean_dec(v_k_1737_);
v_as_1735_ = v___x_1746_;
v_i_1736_ = v___x_1748_;
v_k_1737_ = v___x_1749_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg___boxed(lean_object* v_hi_1751_, lean_object* v_pivot_1752_, lean_object* v_as_1753_, lean_object* v_i_1754_, lean_object* v_k_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1751_, v_pivot_1752_, v_as_1753_, v_i_1754_, v_k_1755_);
lean_dec(v_pivot_1752_);
lean_dec(v_hi_1751_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(lean_object* v_n_1757_, lean_object* v_as_1758_, lean_object* v_lo_1759_, lean_object* v_hi_1760_){
_start:
{
lean_object* v___y_1762_; uint8_t v___x_1772_; 
v___x_1772_ = lean_nat_dec_lt(v_lo_1759_, v_hi_1760_);
if (v___x_1772_ == 0)
{
lean_dec(v_lo_1759_);
return v_as_1758_;
}
else
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v_mid_1775_; lean_object* v___y_1777_; lean_object* v___y_1783_; lean_object* v___x_1788_; lean_object* v___x_1789_; uint8_t v___x_1790_; 
v___x_1773_ = lean_nat_add(v_lo_1759_, v_hi_1760_);
v___x_1774_ = lean_unsigned_to_nat(1u);
v_mid_1775_ = lean_nat_shiftr(v___x_1773_, v___x_1774_);
lean_dec(v___x_1773_);
v___x_1788_ = lean_array_fget_borrowed(v_as_1758_, v_mid_1775_);
v___x_1789_ = lean_array_fget_borrowed(v_as_1758_, v_lo_1759_);
v___x_1790_ = l_Lean_Name_quickLt(v___x_1788_, v___x_1789_);
if (v___x_1790_ == 0)
{
v___y_1783_ = v_as_1758_;
goto v___jp_1782_;
}
else
{
lean_object* v___x_1791_; 
v___x_1791_ = lean_array_fswap(v_as_1758_, v_lo_1759_, v_mid_1775_);
v___y_1783_ = v___x_1791_;
goto v___jp_1782_;
}
v___jp_1776_:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; uint8_t v___x_1780_; 
v___x_1778_ = lean_array_fget_borrowed(v___y_1777_, v_mid_1775_);
v___x_1779_ = lean_array_fget_borrowed(v___y_1777_, v_hi_1760_);
v___x_1780_ = l_Lean_Name_quickLt(v___x_1778_, v___x_1779_);
if (v___x_1780_ == 0)
{
lean_dec(v_mid_1775_);
v___y_1762_ = v___y_1777_;
goto v___jp_1761_;
}
else
{
lean_object* v___x_1781_; 
v___x_1781_ = lean_array_fswap(v___y_1777_, v_mid_1775_, v_hi_1760_);
lean_dec(v_mid_1775_);
v___y_1762_ = v___x_1781_;
goto v___jp_1761_;
}
}
v___jp_1782_:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; uint8_t v___x_1786_; 
v___x_1784_ = lean_array_fget_borrowed(v___y_1783_, v_hi_1760_);
v___x_1785_ = lean_array_fget_borrowed(v___y_1783_, v_lo_1759_);
v___x_1786_ = l_Lean_Name_quickLt(v___x_1784_, v___x_1785_);
if (v___x_1786_ == 0)
{
v___y_1777_ = v___y_1783_;
goto v___jp_1776_;
}
else
{
lean_object* v___x_1787_; 
v___x_1787_ = lean_array_fswap(v___y_1783_, v_lo_1759_, v_hi_1760_);
v___y_1777_ = v___x_1787_;
goto v___jp_1776_;
}
}
}
v___jp_1761_:
{
lean_object* v_pivot_1763_; lean_object* v___x_1764_; lean_object* v_fst_1765_; lean_object* v_snd_1766_; uint8_t v___x_1767_; 
v_pivot_1763_ = lean_array_fget(v___y_1762_, v_hi_1760_);
lean_inc_n(v_lo_1759_, 2);
v___x_1764_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1760_, v_pivot_1763_, v___y_1762_, v_lo_1759_, v_lo_1759_);
lean_dec(v_pivot_1763_);
v_fst_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_fst_1765_);
v_snd_1766_ = lean_ctor_get(v___x_1764_, 1);
lean_inc(v_snd_1766_);
lean_dec_ref(v___x_1764_);
v___x_1767_ = lean_nat_dec_le(v_hi_1760_, v_fst_1765_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1768_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1757_, v_snd_1766_, v_lo_1759_, v_fst_1765_);
v___x_1769_ = lean_unsigned_to_nat(1u);
v___x_1770_ = lean_nat_add(v_fst_1765_, v___x_1769_);
lean_dec(v_fst_1765_);
v_as_1758_ = v___x_1768_;
v_lo_1759_ = v___x_1770_;
goto _start;
}
else
{
lean_dec(v_fst_1765_);
lean_dec(v_lo_1759_);
return v_snd_1766_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg___boxed(lean_object* v_n_1792_, lean_object* v_as_1793_, lean_object* v_lo_1794_, lean_object* v_hi_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1792_, v_as_1793_, v_lo_1794_, v_hi_1795_);
lean_dec(v_hi_1795_);
lean_dec(v_n_1792_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(lean_object* v_env_1797_, lean_object* v_as_1798_, size_t v_i_1799_, size_t v_stop_1800_, lean_object* v_b_1801_){
_start:
{
lean_object* v___y_1803_; uint8_t v___x_1807_; 
v___x_1807_ = lean_usize_dec_eq(v_i_1799_, v_stop_1800_);
if (v___x_1807_ == 0)
{
lean_object* v___x_1808_; uint8_t v___x_1809_; lean_object* v___x_1810_; uint8_t v___x_1811_; 
v___x_1808_ = lean_array_uget_borrowed(v_as_1798_, v_i_1799_);
v___x_1809_ = 1;
lean_inc_ref(v_env_1797_);
v___x_1810_ = l_Lean_Environment_setExporting(v_env_1797_, v___x_1809_);
lean_inc(v___x_1808_);
v___x_1811_ = l_Lean_Environment_contains(v___x_1810_, v___x_1808_, v___x_1807_);
if (v___x_1811_ == 0)
{
v___y_1803_ = v_b_1801_;
goto v___jp_1802_;
}
else
{
lean_object* v___x_1812_; 
lean_inc(v___x_1808_);
v___x_1812_ = lean_array_push(v_b_1801_, v___x_1808_);
v___y_1803_ = v___x_1812_;
goto v___jp_1802_;
}
}
else
{
lean_dec_ref(v_env_1797_);
return v_b_1801_;
}
v___jp_1802_:
{
size_t v___x_1804_; size_t v___x_1805_; 
v___x_1804_ = ((size_t)1ULL);
v___x_1805_ = lean_usize_add(v_i_1799_, v___x_1804_);
v_i_1799_ = v___x_1805_;
v_b_1801_ = v___y_1803_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2___boxed(lean_object* v_env_1813_, lean_object* v_as_1814_, lean_object* v_i_1815_, lean_object* v_stop_1816_, lean_object* v_b_1817_){
_start:
{
size_t v_i_boxed_1818_; size_t v_stop_boxed_1819_; lean_object* v_res_1820_; 
v_i_boxed_1818_ = lean_unbox_usize(v_i_1815_);
lean_dec(v_i_1815_);
v_stop_boxed_1819_ = lean_unbox_usize(v_stop_1816_);
lean_dec(v_stop_1816_);
v_res_1820_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1813_, v_as_1814_, v_i_boxed_1818_, v_stop_boxed_1819_, v_b_1817_);
lean_dec_ref(v_as_1814_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(lean_object* v_init_1821_, lean_object* v_x_1822_){
_start:
{
if (lean_obj_tag(v_x_1822_) == 0)
{
lean_object* v_k_1823_; lean_object* v_l_1824_; lean_object* v_r_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
v_k_1823_ = lean_ctor_get(v_x_1822_, 1);
lean_inc(v_k_1823_);
v_l_1824_ = lean_ctor_get(v_x_1822_, 3);
lean_inc(v_l_1824_);
v_r_1825_ = lean_ctor_get(v_x_1822_, 4);
lean_inc(v_r_1825_);
lean_dec_ref_known(v_x_1822_, 5);
v___x_1826_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_1821_, v_l_1824_);
v___x_1827_ = lean_array_push(v___x_1826_, v_k_1823_);
v_init_1821_ = v___x_1827_;
v_x_1822_ = v_r_1825_;
goto _start;
}
else
{
return v_init_1821_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__3(lean_object* v_env_1829_, lean_object* v_es_1830_){
_start:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___y_1834_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___y_1851_; lean_object* v___y_1852_; uint8_t v___x_1854_; 
v___x_1831_ = lean_unsigned_to_nat(0u);
v___x_1832_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
v___x_1848_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v___x_1832_, v_es_1830_);
v___x_1849_ = lean_array_get_size(v___x_1848_);
v___x_1854_ = lean_nat_dec_eq(v___x_1849_, v___x_1831_);
if (v___x_1854_ == 0)
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___y_1858_; uint8_t v___x_1860_; 
v___x_1855_ = lean_unsigned_to_nat(1u);
v___x_1856_ = lean_nat_sub(v___x_1849_, v___x_1855_);
v___x_1860_ = lean_nat_dec_le(v___x_1831_, v___x_1856_);
if (v___x_1860_ == 0)
{
lean_inc(v___x_1856_);
v___y_1858_ = v___x_1856_;
goto v___jp_1857_;
}
else
{
v___y_1858_ = v___x_1831_;
goto v___jp_1857_;
}
v___jp_1857_:
{
uint8_t v___x_1859_; 
v___x_1859_ = lean_nat_dec_le(v___y_1858_, v___x_1856_);
if (v___x_1859_ == 0)
{
lean_dec(v___x_1856_);
lean_inc(v___y_1858_);
v___y_1851_ = v___y_1858_;
v___y_1852_ = v___y_1858_;
goto v___jp_1850_;
}
else
{
v___y_1851_ = v___y_1858_;
v___y_1852_ = v___x_1856_;
goto v___jp_1850_;
}
}
}
else
{
v___y_1834_ = v___x_1848_;
goto v___jp_1833_;
}
v___jp_1833_:
{
lean_object* v___x_1835_; uint8_t v___x_1836_; 
v___x_1835_ = lean_array_get_size(v___y_1834_);
v___x_1836_ = lean_nat_dec_lt(v___x_1831_, v___x_1835_);
if (v___x_1836_ == 0)
{
lean_object* v___x_1837_; 
lean_dec_ref(v_env_1829_);
v___x_1837_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1832_);
lean_ctor_set(v___x_1837_, 1, v___x_1832_);
lean_ctor_set(v___x_1837_, 2, v___y_1834_);
return v___x_1837_;
}
else
{
uint8_t v___x_1838_; 
v___x_1838_ = lean_nat_dec_le(v___x_1835_, v___x_1835_);
if (v___x_1838_ == 0)
{
if (v___x_1836_ == 0)
{
lean_object* v___x_1839_; 
lean_dec_ref(v_env_1829_);
v___x_1839_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1832_);
lean_ctor_set(v___x_1839_, 1, v___x_1832_);
lean_ctor_set(v___x_1839_, 2, v___y_1834_);
return v___x_1839_;
}
else
{
size_t v___x_1840_; size_t v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1840_ = ((size_t)0ULL);
v___x_1841_ = lean_usize_of_nat(v___x_1835_);
v___x_1842_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1829_, v___y_1834_, v___x_1840_, v___x_1841_, v___x_1832_);
lean_inc_ref(v___x_1842_);
v___x_1843_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1842_);
lean_ctor_set(v___x_1843_, 1, v___x_1842_);
lean_ctor_set(v___x_1843_, 2, v___y_1834_);
return v___x_1843_;
}
}
else
{
size_t v___x_1844_; size_t v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1844_ = ((size_t)0ULL);
v___x_1845_ = lean_usize_of_nat(v___x_1835_);
v___x_1846_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1829_, v___y_1834_, v___x_1844_, v___x_1845_, v___x_1832_);
lean_inc_ref(v___x_1846_);
v___x_1847_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1846_);
lean_ctor_set(v___x_1847_, 1, v___x_1846_);
lean_ctor_set(v___x_1847_, 2, v___y_1834_);
return v___x_1847_;
}
}
}
v___jp_1850_:
{
lean_object* v___x_1853_; 
v___x_1853_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v___x_1849_, v___x_1848_, v___y_1851_, v___y_1852_);
lean_dec(v___y_1852_);
v___y_1834_ = v___x_1853_;
goto v___jp_1833_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4(lean_object* v___x_1861_, lean_object* v_x_1862_, lean_object* v_x_1863_){
_start:
{
lean_object* v___x_1865_; 
v___x_1865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1861_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4___boxed(lean_object* v___x_1866_, lean_object* v_x_1867_, lean_object* v_x_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l_Lean_registerTagAttribute___lam__4(v___x_1866_, v_x_1867_, v_x_1868_);
lean_dec_ref(v_x_1868_);
lean_dec_ref(v_x_1867_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5(lean_object* v___x_1871_){
_start:
{
lean_object* v___x_1873_; 
v___x_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1871_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5___boxed(lean_object* v___x_1874_, lean_object* v___y_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_Lean_registerTagAttribute___lam__5(v___x_1874_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6(lean_object* v_name_1877_, lean_object* v_decl_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1882_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_1883_ = l_Lean_MessageData_ofName(v_name_1877_);
v___x_1884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1882_);
lean_ctor_set(v___x_1884_, 1, v___x_1883_);
v___x_1885_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_1886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1884_);
lean_ctor_set(v___x_1886_, 1, v___x_1885_);
v___x_1887_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1886_, v___y_1879_, v___y_1880_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6___boxed(lean_object* v_name_1888_, lean_object* v_decl_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v_res_1893_; 
v_res_1893_ = l_Lean_registerTagAttribute___lam__6(v_name_1888_, v_decl_1889_, v___y_1890_, v___y_1891_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v_decl_1889_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(lean_object* v_attrName_1894_, lean_object* v_declName_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; uint8_t v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1899_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1900_ = l_Lean_MessageData_ofName(v_attrName_1894_);
v___x_1901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1899_);
lean_ctor_set(v___x_1901_, 1, v___x_1900_);
v___x_1902_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1901_);
lean_ctor_set(v___x_1903_, 1, v___x_1902_);
v___x_1904_ = 0;
v___x_1905_ = l_Lean_MessageData_ofConstName(v_declName_1895_, v___x_1904_);
v___x_1906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1903_);
lean_ctor_set(v___x_1906_, 1, v___x_1905_);
v___x_1907_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1906_);
lean_ctor_set(v___x_1908_, 1, v___x_1907_);
v___x_1909_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1908_, v___y_1896_, v___y_1897_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg___boxed(lean_object* v_attrName_1910_, lean_object* v_declName_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_){
_start:
{
lean_object* v_res_1915_; 
v_res_1915_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_1910_, v_declName_1911_, v___y_1912_, v___y_1913_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(lean_object* v_attrName_1916_, lean_object* v_declName_1917_, lean_object* v_asyncPrefix_x3f_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v___y_1923_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1918_) == 0)
{
lean_object* v___x_1936_; 
v___x_1936_ = l_Lean_MessageData_nil;
v___y_1923_ = v___x_1936_;
goto v___jp_1922_;
}
else
{
lean_object* v_val_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v_val_1937_ = lean_ctor_get(v_asyncPrefix_x3f_1918_, 0);
lean_inc(v_val_1937_);
lean_dec_ref_known(v_asyncPrefix_x3f_1918_, 1);
v___x_1938_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1939_ = l_Lean_MessageData_ofName(v_val_1937_);
v___x_1940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1938_);
lean_ctor_set(v___x_1940_, 1, v___x_1939_);
v___x_1941_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1940_);
lean_ctor_set(v___x_1942_, 1, v___x_1941_);
v___y_1923_ = v___x_1942_;
goto v___jp_1922_;
}
v___jp_1922_:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; uint8_t v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1924_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1925_ = l_Lean_MessageData_ofName(v_attrName_1916_);
v___x_1926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1924_);
lean_ctor_set(v___x_1926_, 1, v___x_1925_);
v___x_1927_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1926_);
lean_ctor_set(v___x_1928_, 1, v___x_1927_);
v___x_1929_ = 0;
v___x_1930_ = l_Lean_MessageData_ofConstName(v_declName_1917_, v___x_1929_);
v___x_1931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1928_);
lean_ctor_set(v___x_1931_, 1, v___x_1930_);
v___x_1932_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1931_);
lean_ctor_set(v___x_1933_, 1, v___x_1932_);
v___x_1934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1933_);
lean_ctor_set(v___x_1934_, 1, v___y_1923_);
v___x_1935_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1934_, v___y_1919_, v___y_1920_);
return v___x_1935_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg___boxed(lean_object* v_attrName_1943_, lean_object* v_declName_1944_, lean_object* v_asyncPrefix_x3f_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_1943_, v_declName_1944_, v_asyncPrefix_x3f_1945_, v___y_1946_, v___y_1947_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(lean_object* v_name_1950_, uint8_t v_kind_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___y_1961_; 
v___x_1955_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_1956_ = l_Lean_MessageData_ofName(v_name_1950_);
v___x_1957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1955_);
lean_ctor_set(v___x_1957_, 1, v___x_1956_);
v___x_1958_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_1959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1957_);
lean_ctor_set(v___x_1959_, 1, v___x_1958_);
switch(v_kind_1951_)
{
case 0:
{
lean_object* v___x_1968_; 
v___x_1968_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_1961_ = v___x_1968_;
goto v___jp_1960_;
}
case 1:
{
lean_object* v___x_1969_; 
v___x_1969_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_1961_ = v___x_1969_;
goto v___jp_1960_;
}
default: 
{
lean_object* v___x_1970_; 
v___x_1970_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_1961_ = v___x_1970_;
goto v___jp_1960_;
}
}
v___jp_1960_:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; 
lean_inc_ref(v___y_1961_);
v___x_1962_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1962_, 0, v___y_1961_);
v___x_1963_ = l_Lean_MessageData_ofFormat(v___x_1962_);
v___x_1964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1959_);
lean_ctor_set(v___x_1964_, 1, v___x_1963_);
v___x_1965_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1964_);
lean_ctor_set(v___x_1966_, 1, v___x_1965_);
v___x_1967_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1966_, v___y_1952_, v___y_1953_);
return v___x_1967_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg___boxed(lean_object* v_name_1971_, lean_object* v_kind_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
uint8_t v_kind_boxed_1976_; lean_object* v_res_1977_; 
v_kind_boxed_1976_ = lean_unbox(v_kind_1972_);
v_res_1977_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_1971_, v_kind_boxed_1976_, v___y_1973_, v___y_1974_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7(lean_object* v_validate_1978_, lean_object* v_a_1979_, lean_object* v_name_1980_, lean_object* v_decl_1981_, lean_object* v_stx_1982_, uint8_t v_kind_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_2023_; lean_object* v___y_2024_; lean_object* v___y_2025_; lean_object* v___y_2032_; lean_object* v___y_2033_; lean_object* v___x_2038_; 
v___x_2038_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_1982_, v___y_1984_, v___y_1985_);
if (lean_obj_tag(v___x_2038_) == 0)
{
uint8_t v___x_2039_; uint8_t v___x_2040_; 
lean_dec_ref_known(v___x_2038_, 1);
v___x_2039_ = 0;
v___x_2040_ = l_Lean_instBEqAttributeKind_beq(v_kind_1983_, v___x_2039_);
if (v___x_2040_ == 0)
{
lean_object* v___x_2041_; 
lean_dec(v_decl_1981_);
lean_dec_ref(v_a_1979_);
lean_dec_ref(v_validate_1978_);
v___x_2041_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_1980_, v_kind_1983_, v___y_1984_, v___y_1985_);
return v___x_2041_;
}
else
{
v___y_2032_ = v___y_1984_;
v___y_2033_ = v___y_1985_;
goto v___jp_2031_;
}
}
else
{
lean_dec(v_decl_1981_);
lean_dec(v_name_1980_);
lean_dec_ref(v_a_1979_);
lean_dec_ref(v_validate_1978_);
return v___x_2038_;
}
v___jp_1987_:
{
lean_object* v___x_1990_; 
lean_inc(v___y_1989_);
lean_inc_ref(v___y_1988_);
lean_inc(v_decl_1981_);
v___x_1990_ = lean_apply_4(v_validate_1978_, v_decl_1981_, v___y_1988_, v___y_1989_, lean_box(0));
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2020_; 
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2020_ == 0)
{
lean_object* v_unused_2021_; 
v_unused_2021_ = lean_ctor_get(v___x_1990_, 0);
lean_dec(v_unused_2021_);
v___x_1992_ = v___x_1990_;
v_isShared_1993_ = v_isSharedCheck_2020_;
goto v_resetjp_1991_;
}
else
{
lean_dec(v___x_1990_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2020_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1994_; lean_object* v_toEnvExtension_1995_; lean_object* v_env_1996_; lean_object* v_nextMacroScope_1997_; lean_object* v_ngen_1998_; lean_object* v_auxDeclNGen_1999_; lean_object* v_traceState_2000_; lean_object* v_messages_2001_; lean_object* v_infoState_2002_; lean_object* v_snapshotTasks_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2018_; 
v___x_1994_ = lean_st_ref_take(v___y_1989_);
v_toEnvExtension_1995_ = lean_ctor_get(v_a_1979_, 0);
v_env_1996_ = lean_ctor_get(v___x_1994_, 0);
v_nextMacroScope_1997_ = lean_ctor_get(v___x_1994_, 1);
v_ngen_1998_ = lean_ctor_get(v___x_1994_, 2);
v_auxDeclNGen_1999_ = lean_ctor_get(v___x_1994_, 3);
v_traceState_2000_ = lean_ctor_get(v___x_1994_, 4);
v_messages_2001_ = lean_ctor_get(v___x_1994_, 6);
v_infoState_2002_ = lean_ctor_get(v___x_1994_, 7);
v_snapshotTasks_2003_ = lean_ctor_get(v___x_1994_, 8);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2018_ == 0)
{
lean_object* v_unused_2019_; 
v_unused_2019_ = lean_ctor_get(v___x_1994_, 5);
lean_dec(v_unused_2019_);
v___x_2005_ = v___x_1994_;
v_isShared_2006_ = v_isSharedCheck_2018_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_snapshotTasks_2003_);
lean_inc(v_infoState_2002_);
lean_inc(v_messages_2001_);
lean_inc(v_traceState_2000_);
lean_inc(v_auxDeclNGen_1999_);
lean_inc(v_ngen_1998_);
lean_inc(v_nextMacroScope_1997_);
lean_inc(v_env_1996_);
lean_dec(v___x_1994_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2018_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v_asyncMode_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2011_; 
v_asyncMode_2007_ = lean_ctor_get(v_toEnvExtension_1995_, 2);
lean_inc(v_asyncMode_2007_);
lean_inc(v_decl_1981_);
v___x_2008_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_1979_, v_env_1996_, v_decl_1981_, v_asyncMode_2007_, v_decl_1981_);
lean_dec(v_asyncMode_2007_);
v___x_2009_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 5, v___x_2009_);
lean_ctor_set(v___x_2005_, 0, v___x_2008_);
v___x_2011_ = v___x_2005_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_2008_);
lean_ctor_set(v_reuseFailAlloc_2017_, 1, v_nextMacroScope_1997_);
lean_ctor_set(v_reuseFailAlloc_2017_, 2, v_ngen_1998_);
lean_ctor_set(v_reuseFailAlloc_2017_, 3, v_auxDeclNGen_1999_);
lean_ctor_set(v_reuseFailAlloc_2017_, 4, v_traceState_2000_);
lean_ctor_set(v_reuseFailAlloc_2017_, 5, v___x_2009_);
lean_ctor_set(v_reuseFailAlloc_2017_, 6, v_messages_2001_);
lean_ctor_set(v_reuseFailAlloc_2017_, 7, v_infoState_2002_);
lean_ctor_set(v_reuseFailAlloc_2017_, 8, v_snapshotTasks_2003_);
v___x_2011_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2015_; 
v___x_2012_ = lean_st_ref_put(v___y_1989_, v___x_2011_);
v___x_2013_ = lean_box(0);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 0, v___x_2013_);
v___x_2015_ = v___x_1992_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2013_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
}
}
else
{
lean_dec(v_decl_1981_);
lean_dec_ref(v_a_1979_);
return v___x_1990_;
}
}
v___jp_2022_:
{
lean_object* v_toEnvExtension_2026_; lean_object* v_asyncMode_2027_; uint8_t v___x_2028_; 
v_toEnvExtension_2026_ = lean_ctor_get(v_a_1979_, 0);
v_asyncMode_2027_ = lean_ctor_get(v_toEnvExtension_2026_, 2);
lean_inc(v_decl_1981_);
lean_inc_ref(v___y_2023_);
v___x_2028_ = l_Lean_EnvExtension_asyncMayModify___redArg(v___y_2023_, v_decl_1981_, v_asyncMode_2027_);
if (v___x_2028_ == 0)
{
lean_object* v___x_2029_; lean_object* v___x_2030_; 
lean_dec_ref(v_a_1979_);
lean_dec_ref(v_validate_1978_);
v___x_2029_ = l_Lean_Environment_asyncPrefix_x3f(v___y_2023_);
v___x_2030_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_name_1980_, v_decl_1981_, v___x_2029_, v___y_2024_, v___y_2025_);
return v___x_2030_;
}
else
{
lean_dec_ref(v___y_2023_);
lean_dec(v_name_1980_);
v___y_1988_ = v___y_2024_;
v___y_1989_ = v___y_2025_;
goto v___jp_1987_;
}
}
v___jp_2031_:
{
lean_object* v___x_2034_; lean_object* v_env_2035_; lean_object* v___x_2036_; 
v___x_2034_ = lean_st_ref_get(v___y_2033_);
v_env_2035_ = lean_ctor_get(v___x_2034_, 0);
lean_inc_ref(v_env_2035_);
lean_dec(v___x_2034_);
v___x_2036_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2035_, v_decl_1981_);
if (lean_obj_tag(v___x_2036_) == 0)
{
v___y_2023_ = v_env_2035_;
v___y_2024_ = v___y_2032_;
v___y_2025_ = v___y_2033_;
goto v___jp_2022_;
}
else
{
lean_object* v___x_2037_; 
lean_dec_ref_known(v___x_2036_, 1);
lean_dec_ref(v_env_2035_);
lean_dec_ref(v_a_1979_);
lean_dec_ref(v_validate_1978_);
v___x_2037_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_1980_, v_decl_1981_, v___y_2032_, v___y_2033_);
return v___x_2037_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7___boxed(lean_object* v_validate_2042_, lean_object* v_a_2043_, lean_object* v_name_2044_, lean_object* v_decl_2045_, lean_object* v_stx_2046_, lean_object* v_kind_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
uint8_t v_kind_boxed_2051_; lean_object* v_res_2052_; 
v_kind_boxed_2051_ = lean_unbox(v_kind_2047_);
v_res_2052_ = l_Lean_registerTagAttribute___lam__7(v_validate_2042_, v_a_2043_, v_name_2044_, v_decl_2045_, v_stx_2046_, v_kind_boxed_2051_, v___y_2048_, v___y_2049_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
return v_res_2052_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__5(void){
_start:
{
lean_object* v___x_2058_; lean_object* v___f_2059_; 
v___x_2058_ = l_Lean_NameSet_empty;
v___f_2059_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__4___boxed), 4, 1);
lean_closure_set(v___f_2059_, 0, v___x_2058_);
return v___f_2059_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__6(void){
_start:
{
lean_object* v___x_2060_; lean_object* v___f_2061_; 
v___x_2060_ = l_Lean_NameSet_empty;
v___f_2061_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__5___boxed), 2, 1);
lean_closure_set(v___f_2061_, 0, v___x_2060_);
return v___f_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute(lean_object* v_name_2064_, lean_object* v_descr_2065_, lean_object* v_validate_2066_, lean_object* v_ref_2067_, uint8_t v_applicationTime_2068_, lean_object* v_asyncMode_2069_){
_start:
{
lean_object* v___f_2071_; lean_object* v___f_2072_; lean_object* v___f_2073_; lean_object* v___f_2074_; lean_object* v___f_2075_; lean_object* v___f_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___f_2071_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__0));
v___f_2072_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__2));
v___f_2073_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__3));
v___f_2074_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__4));
v___f_2075_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__5, &l_Lean_registerTagAttribute___closed__5_once, _init_l_Lean_registerTagAttribute___closed__5);
v___f_2076_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__6, &l_Lean_registerTagAttribute___closed__6_once, _init_l_Lean_registerTagAttribute___closed__6);
v___x_2077_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__7));
lean_inc(v_ref_2067_);
v___x_2078_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2078_, 0, v_ref_2067_);
lean_ctor_set(v___x_2078_, 1, v___f_2076_);
lean_ctor_set(v___x_2078_, 2, v___f_2075_);
lean_ctor_set(v___x_2078_, 3, v___f_2074_);
lean_ctor_set(v___x_2078_, 4, v___f_2073_);
lean_ctor_set(v___x_2078_, 5, v___f_2072_);
lean_ctor_set(v___x_2078_, 6, v_asyncMode_2069_);
lean_ctor_set(v___x_2078_, 7, v___x_2077_);
v___x_2079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2078_);
lean_ctor_set(v___x_2079_, 1, v___f_2071_);
v___x_2080_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2079_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v_a_2081_; lean_object* v___f_2082_; lean_object* v___f_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; 
v_a_2081_ = lean_ctor_get(v___x_2080_, 0);
lean_inc_n(v_a_2081_, 2);
lean_dec_ref_known(v___x_2080_, 1);
lean_inc_n(v_name_2064_, 2);
v___f_2082_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__6___boxed), 5, 1);
lean_closure_set(v___f_2082_, 0, v_name_2064_);
v___f_2083_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__7___boxed), 9, 3);
lean_closure_set(v___f_2083_, 0, v_validate_2066_);
lean_closure_set(v___f_2083_, 1, v_a_2081_);
lean_closure_set(v___f_2083_, 2, v_name_2064_);
v___x_2084_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2084_, 0, v_ref_2067_);
lean_ctor_set(v___x_2084_, 1, v_name_2064_);
lean_ctor_set(v___x_2084_, 2, v_descr_2065_);
lean_ctor_set_uint8(v___x_2084_, sizeof(void*)*3, v_applicationTime_2068_);
v___x_2085_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2084_);
lean_ctor_set(v___x_2085_, 1, v___f_2083_);
lean_ctor_set(v___x_2085_, 2, v___f_2082_);
lean_inc_ref(v___x_2085_);
v___x_2086_ = l_Lean_registerBuiltinAttribute(v___x_2085_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2094_; 
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2094_ == 0)
{
lean_object* v_unused_2095_; 
v_unused_2095_ = lean_ctor_get(v___x_2086_, 0);
lean_dec(v_unused_2095_);
v___x_2088_ = v___x_2086_;
v_isShared_2089_ = v_isSharedCheck_2094_;
goto v_resetjp_2087_;
}
else
{
lean_dec(v___x_2086_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2094_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2090_; lean_object* v___x_2092_; 
v___x_2090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2085_);
lean_ctor_set(v___x_2090_, 1, v_a_2081_);
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 0, v___x_2090_);
v___x_2092_ = v___x_2088_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v___x_2090_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
else
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
lean_dec_ref_known(v___x_2085_, 3);
lean_dec(v_a_2081_);
v_a_2096_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2098_ = v___x_2086_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2086_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2099_ == 0)
{
v___x_2101_ = v___x_2098_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_a_2096_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
else
{
lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2111_; 
lean_dec(v_ref_2067_);
lean_dec_ref(v_validate_2066_);
lean_dec_ref(v_descr_2065_);
lean_dec(v_name_2064_);
v_a_2104_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2106_ = v___x_2080_;
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___x_2080_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2109_; 
if (v_isShared_2107_ == 0)
{
v___x_2109_ = v___x_2106_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_a_2104_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___boxed(lean_object* v_name_2112_, lean_object* v_descr_2113_, lean_object* v_validate_2114_, lean_object* v_ref_2115_, lean_object* v_applicationTime_2116_, lean_object* v_asyncMode_2117_, lean_object* v_a_2118_){
_start:
{
uint8_t v_applicationTime_boxed_2119_; lean_object* v_res_2120_; 
v_applicationTime_boxed_2119_ = lean_unbox(v_applicationTime_2116_);
v_res_2120_ = l_Lean_registerTagAttribute(v_name_2112_, v_descr_2113_, v_validate_2114_, v_ref_2115_, v_applicationTime_boxed_2119_, v_asyncMode_2117_);
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1(lean_object* v_init_2121_, lean_object* v_t_2122_){
_start:
{
lean_object* v___x_2123_; 
v___x_2123_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_2121_, v_t_2122_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(lean_object* v_n_2124_, lean_object* v_as_2125_, lean_object* v_lo_2126_, lean_object* v_hi_2127_, lean_object* v_w_2128_, lean_object* v_hlo_2129_, lean_object* v_hhi_2130_){
_start:
{
lean_object* v___x_2131_; 
v___x_2131_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_2124_, v_as_2125_, v_lo_2126_, v_hi_2127_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___boxed(lean_object* v_n_2132_, lean_object* v_as_2133_, lean_object* v_lo_2134_, lean_object* v_hi_2135_, lean_object* v_w_2136_, lean_object* v_hlo_2137_, lean_object* v_hhi_2138_){
_start:
{
lean_object* v_res_2139_; 
v_res_2139_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(v_n_2132_, v_as_2133_, v_lo_2134_, v_hi_2135_, v_w_2136_, v_hlo_2137_, v_hhi_2138_);
lean_dec(v_hi_2135_);
lean_dec(v_n_2132_);
return v_res_2139_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(lean_object* v_00_u03b1_2140_, lean_object* v_attrName_2141_, lean_object* v_declName_2142_, lean_object* v_asyncPrefix_x3f_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_){
_start:
{
lean_object* v___x_2147_; 
v___x_2147_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_2141_, v_declName_2142_, v_asyncPrefix_x3f_2143_, v___y_2144_, v___y_2145_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___boxed(lean_object* v_00_u03b1_2148_, lean_object* v_attrName_2149_, lean_object* v_declName_2150_, lean_object* v_asyncPrefix_x3f_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_){
_start:
{
lean_object* v_res_2155_; 
v_res_2155_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(v_00_u03b1_2148_, v_attrName_2149_, v_declName_2150_, v_asyncPrefix_x3f_2151_, v___y_2152_, v___y_2153_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(lean_object* v_00_u03b1_2156_, lean_object* v_attrName_2157_, lean_object* v_declName_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_){
_start:
{
lean_object* v___x_2162_; 
v___x_2162_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_2157_, v_declName_2158_, v___y_2159_, v___y_2160_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___boxed(lean_object* v_00_u03b1_2163_, lean_object* v_attrName_2164_, lean_object* v_declName_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_){
_start:
{
lean_object* v_res_2169_; 
v_res_2169_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(v_00_u03b1_2163_, v_attrName_2164_, v_declName_2165_, v___y_2166_, v___y_2167_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(lean_object* v_00_u03b1_2170_, lean_object* v_name_2171_, uint8_t v_kind_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
lean_object* v___x_2176_; 
v___x_2176_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2171_, v_kind_2172_, v___y_2173_, v___y_2174_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___boxed(lean_object* v_00_u03b1_2177_, lean_object* v_name_2178_, lean_object* v_kind_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
uint8_t v_kind_boxed_2183_; lean_object* v_res_2184_; 
v_kind_boxed_2183_ = lean_unbox(v_kind_2179_);
v_res_2184_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(v_00_u03b1_2177_, v_name_2178_, v_kind_boxed_2183_, v___y_2180_, v___y_2181_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
return v_res_2184_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(lean_object* v_n_2185_, lean_object* v_lo_2186_, lean_object* v_hi_2187_, lean_object* v_hhi_2188_, lean_object* v_pivot_2189_, lean_object* v_as_2190_, lean_object* v_i_2191_, lean_object* v_k_2192_, lean_object* v_ilo_2193_, lean_object* v_ik_2194_, lean_object* v_w_2195_){
_start:
{
lean_object* v___x_2196_; 
v___x_2196_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_2187_, v_pivot_2189_, v_as_2190_, v_i_2191_, v_k_2192_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___boxed(lean_object* v_n_2197_, lean_object* v_lo_2198_, lean_object* v_hi_2199_, lean_object* v_hhi_2200_, lean_object* v_pivot_2201_, lean_object* v_as_2202_, lean_object* v_i_2203_, lean_object* v_k_2204_, lean_object* v_ilo_2205_, lean_object* v_ik_2206_, lean_object* v_w_2207_){
_start:
{
lean_object* v_res_2208_; 
v_res_2208_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(v_n_2197_, v_lo_2198_, v_hi_2199_, v_hhi_2200_, v_pivot_2201_, v_as_2202_, v_i_2203_, v_k_2204_, v_ilo_2205_, v_ik_2206_, v_w_2207_);
lean_dec(v_pivot_2201_);
lean_dec(v_hi_2199_);
lean_dec(v_lo_2198_);
lean_dec(v_n_2197_);
return v_res_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__0(lean_object* v_attr_2209_, lean_object* v_decl_2210_, lean_object* v_env_2211_){
_start:
{
lean_object* v_ext_2212_; lean_object* v_toEnvExtension_2213_; lean_object* v_asyncMode_2214_; lean_object* v___x_2215_; 
v_ext_2212_ = lean_ctor_get(v_attr_2209_, 1);
lean_inc_ref(v_ext_2212_);
lean_dec_ref(v_attr_2209_);
v_toEnvExtension_2213_ = lean_ctor_get(v_ext_2212_, 0);
v_asyncMode_2214_ = lean_ctor_get(v_toEnvExtension_2213_, 2);
lean_inc(v_asyncMode_2214_);
lean_inc(v_decl_2210_);
v___x_2215_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2212_, v_env_2211_, v_decl_2210_, v_asyncMode_2214_, v_decl_2210_);
lean_dec(v_asyncMode_2214_);
return v___x_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__1(lean_object* v_modifyEnv_2216_, lean_object* v___f_2217_, lean_object* v_____r_2218_){
_start:
{
lean_object* v___x_2219_; 
v___x_2219_ = lean_apply_1(v_modifyEnv_2216_, v___f_2217_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__2(lean_object* v_attr_2220_, lean_object* v_env_2221_, lean_object* v_decl_2222_, lean_object* v_inst_2223_, lean_object* v_inst_2224_, lean_object* v_toBind_2225_, lean_object* v___f_2226_, lean_object* v_modifyEnv_2227_, lean_object* v___f_2228_, lean_object* v_____r_2229_){
_start:
{
lean_object* v_ext_2230_; lean_object* v_toEnvExtension_2231_; lean_object* v_attr_2232_; lean_object* v_asyncMode_2233_; uint8_t v___x_2234_; 
v_ext_2230_ = lean_ctor_get(v_attr_2220_, 1);
v_toEnvExtension_2231_ = lean_ctor_get(v_ext_2230_, 0);
lean_inc_ref(v_toEnvExtension_2231_);
v_attr_2232_ = lean_ctor_get(v_attr_2220_, 0);
lean_inc_ref(v_attr_2232_);
lean_dec_ref(v_attr_2220_);
v_asyncMode_2233_ = lean_ctor_get(v_toEnvExtension_2231_, 2);
lean_inc(v_asyncMode_2233_);
lean_dec_ref(v_toEnvExtension_2231_);
lean_inc(v_decl_2222_);
lean_inc_ref(v_env_2221_);
v___x_2234_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2221_, v_decl_2222_, v_asyncMode_2233_);
lean_dec(v_asyncMode_2233_);
if (v___x_2234_ == 0)
{
lean_object* v_toAttributeImplCore_2235_; lean_object* v_name_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
lean_dec_ref(v___f_2228_);
lean_dec(v_modifyEnv_2227_);
v_toAttributeImplCore_2235_ = lean_ctor_get(v_attr_2232_, 0);
lean_inc_ref(v_toAttributeImplCore_2235_);
lean_dec_ref(v_attr_2232_);
v_name_2236_ = lean_ctor_get(v_toAttributeImplCore_2235_, 1);
lean_inc(v_name_2236_);
lean_dec_ref(v_toAttributeImplCore_2235_);
v___x_2237_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2221_);
v___x_2238_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_2223_, v_inst_2224_, v_name_2236_, v_decl_2222_, v___x_2237_);
v___x_2239_ = lean_apply_4(v_toBind_2225_, lean_box(0), lean_box(0), v___x_2238_, v___f_2226_);
return v___x_2239_;
}
else
{
lean_object* v___x_2240_; 
lean_dec_ref(v_attr_2232_);
lean_dec(v___f_2226_);
lean_dec(v_toBind_2225_);
lean_dec_ref(v_inst_2224_);
lean_dec_ref(v_inst_2223_);
lean_dec(v_decl_2222_);
lean_dec_ref(v_env_2221_);
v___x_2240_ = lean_apply_1(v_modifyEnv_2227_, v___f_2228_);
return v___x_2240_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__3(lean_object* v___f_2241_, lean_object* v_____r_2242_){
_start:
{
lean_object* v___x_2243_; 
v___x_2243_ = lean_apply_1(v___f_2241_, v_____r_2242_);
return v___x_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__4(lean_object* v_attr_2244_, lean_object* v_decl_2245_, lean_object* v_inst_2246_, lean_object* v_inst_2247_, lean_object* v_toBind_2248_, lean_object* v___f_2249_, lean_object* v_modifyEnv_2250_, lean_object* v___f_2251_, lean_object* v_env_2252_){
_start:
{
lean_object* v___f_2253_; lean_object* v___x_2254_; 
lean_inc_ref(v___f_2251_);
lean_inc(v_modifyEnv_2250_);
lean_inc(v___f_2249_);
lean_inc(v_toBind_2248_);
lean_inc_ref(v_inst_2247_);
lean_inc_ref(v_inst_2246_);
lean_inc(v_decl_2245_);
lean_inc_ref(v_env_2252_);
lean_inc_ref(v_attr_2244_);
v___f_2253_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__2), 10, 9);
lean_closure_set(v___f_2253_, 0, v_attr_2244_);
lean_closure_set(v___f_2253_, 1, v_env_2252_);
lean_closure_set(v___f_2253_, 2, v_decl_2245_);
lean_closure_set(v___f_2253_, 3, v_inst_2246_);
lean_closure_set(v___f_2253_, 4, v_inst_2247_);
lean_closure_set(v___f_2253_, 5, v_toBind_2248_);
lean_closure_set(v___f_2253_, 6, v___f_2249_);
lean_closure_set(v___f_2253_, 7, v_modifyEnv_2250_);
lean_closure_set(v___f_2253_, 8, v___f_2251_);
v___x_2254_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2252_, v_decl_2245_);
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
lean_dec_ref(v___f_2253_);
v___x_2255_ = lean_box(0);
v___x_2256_ = l_Lean_TagAttribute_setTag___redArg___lam__2(v_attr_2244_, v_env_2252_, v_decl_2245_, v_inst_2246_, v_inst_2247_, v_toBind_2248_, v___f_2249_, v_modifyEnv_2250_, v___f_2251_, v___x_2255_);
return v___x_2256_;
}
else
{
lean_object* v_attr_2257_; lean_object* v_toAttributeImplCore_2258_; lean_object* v_name_2259_; lean_object* v___f_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
lean_dec_ref_known(v___x_2254_, 1);
lean_dec_ref(v_env_2252_);
lean_dec_ref(v___f_2251_);
lean_dec(v_modifyEnv_2250_);
lean_dec(v___f_2249_);
v_attr_2257_ = lean_ctor_get(v_attr_2244_, 0);
lean_inc_ref(v_attr_2257_);
lean_dec_ref(v_attr_2244_);
v_toAttributeImplCore_2258_ = lean_ctor_get(v_attr_2257_, 0);
lean_inc_ref(v_toAttributeImplCore_2258_);
lean_dec_ref(v_attr_2257_);
v_name_2259_ = lean_ctor_get(v_toAttributeImplCore_2258_, 1);
lean_inc(v_name_2259_);
lean_dec_ref(v_toAttributeImplCore_2258_);
v___f_2260_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2260_, 0, v___f_2253_);
v___x_2261_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_2246_, v_inst_2247_, v_name_2259_, v_decl_2245_);
v___x_2262_ = lean_apply_4(v_toBind_2248_, lean_box(0), lean_box(0), v___x_2261_, v___f_2260_);
return v___x_2262_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg(lean_object* v_inst_2263_, lean_object* v_inst_2264_, lean_object* v_inst_2265_, lean_object* v_attr_2266_, lean_object* v_decl_2267_){
_start:
{
lean_object* v_toBind_2268_; lean_object* v_getEnv_2269_; lean_object* v_modifyEnv_2270_; lean_object* v___f_2271_; lean_object* v___f_2272_; lean_object* v___f_2273_; lean_object* v___x_2274_; 
v_toBind_2268_ = lean_ctor_get(v_inst_2263_, 1);
lean_inc_n(v_toBind_2268_, 2);
v_getEnv_2269_ = lean_ctor_get(v_inst_2265_, 0);
lean_inc(v_getEnv_2269_);
v_modifyEnv_2270_ = lean_ctor_get(v_inst_2265_, 1);
lean_inc_n(v_modifyEnv_2270_, 2);
lean_dec_ref(v_inst_2265_);
lean_inc(v_decl_2267_);
lean_inc_ref(v_attr_2266_);
v___f_2271_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2271_, 0, v_attr_2266_);
lean_closure_set(v___f_2271_, 1, v_decl_2267_);
lean_inc_ref(v___f_2271_);
v___f_2272_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2272_, 0, v_modifyEnv_2270_);
lean_closure_set(v___f_2272_, 1, v___f_2271_);
v___f_2273_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__4), 9, 8);
lean_closure_set(v___f_2273_, 0, v_attr_2266_);
lean_closure_set(v___f_2273_, 1, v_decl_2267_);
lean_closure_set(v___f_2273_, 2, v_inst_2263_);
lean_closure_set(v___f_2273_, 3, v_inst_2264_);
lean_closure_set(v___f_2273_, 4, v_toBind_2268_);
lean_closure_set(v___f_2273_, 5, v___f_2272_);
lean_closure_set(v___f_2273_, 6, v_modifyEnv_2270_);
lean_closure_set(v___f_2273_, 7, v___f_2271_);
v___x_2274_ = lean_apply_4(v_toBind_2268_, lean_box(0), lean_box(0), v_getEnv_2269_, v___f_2273_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag(lean_object* v_m_2275_, lean_object* v_inst_2276_, lean_object* v_inst_2277_, lean_object* v_inst_2278_, lean_object* v_attr_2279_, lean_object* v_decl_2280_){
_start:
{
lean_object* v___x_2281_; 
v___x_2281_ = l_Lean_TagAttribute_setTag___redArg(v_inst_2276_, v_inst_2277_, v_inst_2278_, v_attr_2279_, v_decl_2280_);
return v___x_2281_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(lean_object* v___y_2282_, lean_object* v_as_2283_, lean_object* v_k_2284_, lean_object* v_x_2285_, lean_object* v_x_2286_){
_start:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v_m_2289_; lean_object* v_a_2290_; uint8_t v___x_2291_; 
v___x_2287_ = lean_nat_add(v_x_2285_, v_x_2286_);
v___x_2288_ = lean_unsigned_to_nat(1u);
v_m_2289_ = lean_nat_shiftr(v___x_2287_, v___x_2288_);
lean_dec(v___x_2287_);
v_a_2290_ = lean_array_fget_borrowed(v_as_2283_, v_m_2289_);
v___x_2291_ = l_Lean_Name_quickLt(v_a_2290_, v_k_2284_);
if (v___x_2291_ == 0)
{
lean_object* v___x_2292_; uint8_t v___x_2293_; 
lean_dec(v_x_2286_);
v___x_2292_ = lean_unsigned_to_nat(0u);
v___x_2293_ = l_Lean_Name_quickLt(v_k_2284_, v_a_2290_);
if (v___x_2293_ == 0)
{
uint8_t v___x_2294_; 
lean_dec(v_m_2289_);
lean_dec(v_x_2285_);
v___x_2294_ = lean_nat_dec_le(v___x_2292_, v___y_2282_);
return v___x_2294_;
}
else
{
uint8_t v___x_2295_; lean_object* v___x_2296_; uint8_t v___y_2298_; 
v___x_2295_ = lean_nat_dec_eq(v_m_2289_, v___x_2292_);
v___x_2296_ = lean_nat_sub(v_m_2289_, v___x_2288_);
lean_dec(v_m_2289_);
if (v___x_2295_ == 0)
{
uint8_t v___x_2300_; 
v___x_2300_ = lean_nat_dec_lt(v___x_2296_, v_x_2285_);
v___y_2298_ = v___x_2300_;
goto v___jp_2297_;
}
else
{
v___y_2298_ = v___x_2295_;
goto v___jp_2297_;
}
v___jp_2297_:
{
if (v___y_2298_ == 0)
{
v_x_2286_ = v___x_2296_;
goto _start;
}
else
{
lean_dec(v___x_2296_);
lean_dec(v_x_2285_);
return v___x_2291_;
}
}
}
}
else
{
lean_object* v___x_2301_; uint8_t v___x_2302_; 
lean_dec(v_x_2285_);
v___x_2301_ = lean_nat_add(v_m_2289_, v___x_2288_);
lean_dec(v_m_2289_);
v___x_2302_ = lean_nat_dec_le(v___x_2301_, v_x_2286_);
if (v___x_2302_ == 0)
{
lean_dec(v___x_2301_);
lean_dec(v_x_2286_);
return v___x_2302_;
}
else
{
v_x_2285_ = v___x_2301_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg___boxed(lean_object* v___y_2304_, lean_object* v_as_2305_, lean_object* v_k_2306_, lean_object* v_x_2307_, lean_object* v_x_2308_){
_start:
{
uint8_t v_res_2309_; lean_object* v_r_2310_; 
v_res_2309_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___y_2304_, v_as_2305_, v_k_2306_, v_x_2307_, v_x_2308_);
lean_dec(v_k_2306_);
lean_dec_ref(v_as_2305_);
lean_dec(v___y_2304_);
v_r_2310_ = lean_box(v_res_2309_);
return v_r_2310_;
}
}
LEAN_EXPORT uint8_t l_Lean_TagAttribute_hasTag(lean_object* v_attr_2311_, lean_object* v_env_2312_, lean_object* v_decl_2313_){
_start:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2314_ = lean_box(1);
v___x_2315_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2312_, v_decl_2313_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_ext_2316_; lean_object* v_toEnvExtension_2317_; lean_object* v_asyncMode_2318_; lean_object* v___x_2319_; uint8_t v___x_2320_; 
v_ext_2316_ = lean_ctor_get(v_attr_2311_, 1);
v_toEnvExtension_2317_ = lean_ctor_get(v_ext_2316_, 0);
v_asyncMode_2318_ = lean_ctor_get(v_toEnvExtension_2317_, 2);
lean_inc(v_decl_2313_);
v___x_2319_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2314_, v_ext_2316_, v_env_2312_, v_asyncMode_2318_, v_decl_2313_);
v___x_2320_ = l_Lean_NameSet_contains(v___x_2319_, v_decl_2313_);
lean_dec(v_decl_2313_);
lean_dec(v___x_2319_);
return v___x_2320_;
}
else
{
lean_object* v_val_2321_; lean_object* v_ext_2322_; uint8_t v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; uint8_t v___x_2327_; 
v_val_2321_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_val_2321_);
lean_dec_ref_known(v___x_2315_, 1);
v_ext_2322_ = lean_ctor_get(v_attr_2311_, 1);
v___x_2323_ = 0;
v___x_2324_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2314_, v_ext_2322_, v_env_2312_, v_val_2321_, v___x_2323_);
lean_dec(v_val_2321_);
lean_dec_ref(v_env_2312_);
v___x_2325_ = lean_unsigned_to_nat(0u);
v___x_2326_ = lean_array_get_size(v___x_2324_);
v___x_2327_ = lean_nat_dec_lt(v___x_2325_, v___x_2326_);
if (v___x_2327_ == 0)
{
lean_dec_ref(v___x_2324_);
lean_dec(v_decl_2313_);
return v___x_2327_;
}
else
{
lean_object* v___x_2328_; lean_object* v___x_2329_; uint8_t v___x_2330_; 
v___x_2328_ = lean_unsigned_to_nat(1u);
v___x_2329_ = lean_nat_sub(v___x_2326_, v___x_2328_);
v___x_2330_ = lean_nat_dec_le(v___x_2325_, v___x_2329_);
if (v___x_2330_ == 0)
{
lean_dec(v___x_2329_);
lean_dec_ref(v___x_2324_);
lean_dec(v_decl_2313_);
return v___x_2330_;
}
else
{
uint8_t v___x_2331_; 
lean_inc(v___x_2329_);
v___x_2331_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___x_2329_, v___x_2324_, v_decl_2313_, v___x_2325_, v___x_2329_);
lean_dec(v_decl_2313_);
lean_dec_ref(v___x_2324_);
lean_dec(v___x_2329_);
return v___x_2331_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_hasTag___boxed(lean_object* v_attr_2332_, lean_object* v_env_2333_, lean_object* v_decl_2334_){
_start:
{
uint8_t v_res_2335_; lean_object* v_r_2336_; 
v_res_2335_ = l_Lean_TagAttribute_hasTag(v_attr_2332_, v_env_2333_, v_decl_2334_);
lean_dec_ref(v_attr_2332_);
v_r_2336_ = lean_box(v_res_2335_);
return v_r_2336_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(lean_object* v___y_2337_, lean_object* v_as_2338_, lean_object* v_k_2339_, lean_object* v_x_2340_, lean_object* v_x_2341_, lean_object* v_x_2342_){
_start:
{
uint8_t v___x_2343_; 
v___x_2343_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___y_2337_, v_as_2338_, v_k_2339_, v_x_2340_, v_x_2341_);
return v___x_2343_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___boxed(lean_object* v___y_2344_, lean_object* v_as_2345_, lean_object* v_k_2346_, lean_object* v_x_2347_, lean_object* v_x_2348_, lean_object* v_x_2349_){
_start:
{
uint8_t v_res_2350_; lean_object* v_r_2351_; 
v_res_2350_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(v___y_2344_, v_as_2345_, v_k_2346_, v_x_2347_, v_x_2348_, v_x_2349_);
lean_dec(v_k_2346_);
lean_dec_ref(v_as_2345_);
lean_dec(v___y_2344_);
v_r_2351_ = lean_box(v_res_2350_);
return v_r_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__0(lean_object* v_x_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2355_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2355_);
return v___x_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__0___boxed(lean_object* v_x_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_){
_start:
{
lean_object* v_res_2360_; 
v_res_2360_ = l_Lean_instInhabitedParametricAttribute_default___lam__0(v_x_2357_, v___y_2358_);
lean_dec_ref(v___y_2358_);
lean_dec_ref(v_x_2357_);
return v_res_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__1(lean_object* v_s_2361_, lean_object* v_x_2362_){
_start:
{
lean_inc_ref(v_s_2361_);
return v_s_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__1___boxed(lean_object* v_s_2363_, lean_object* v_x_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l_Lean_instInhabitedParametricAttribute_default___lam__1(v_s_2363_, v_x_2364_);
lean_dec_ref(v_x_2364_);
lean_dec_ref(v_s_2363_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2(lean_object* v_x_2370_, lean_object* v_x_2371_){
_start:
{
lean_object* v___x_2372_; 
v___x_2372_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__1));
return v___x_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2___boxed(lean_object* v_x_2373_, lean_object* v_x_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l_Lean_instInhabitedParametricAttribute_default___lam__2(v_x_2373_, v_x_2374_);
lean_dec_ref(v_x_2374_);
lean_dec_ref(v_x_2373_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3(lean_object* v_x_2376_){
_start:
{
lean_object* v___x_2377_; 
v___x_2377_ = lean_box(0);
return v___x_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3___boxed(lean_object* v_x_2378_){
_start:
{
lean_object* v_res_2379_; 
v_res_2379_ = l_Lean_instInhabitedParametricAttribute_default___lam__3(v_x_2378_);
lean_dec_ref(v_x_2378_);
return v_res_2379_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_2384_; 
v___x_2384_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_2384_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_2385_; lean_object* v___f_2386_; lean_object* v___f_2387_; lean_object* v___f_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___f_2385_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__3));
v___f_2386_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__2));
v___f_2387_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__1));
v___f_2388_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__0));
v___x_2389_ = lean_box(0);
v___x_2390_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__4, &l_Lean_instInhabitedParametricAttribute_default___closed__4_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__4);
v___x_2391_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2390_);
lean_ctor_set(v___x_2391_, 1, v___x_2389_);
lean_ctor_set(v___x_2391_, 2, v___f_2388_);
lean_ctor_set(v___x_2391_, 3, v___f_2387_);
lean_ctor_set(v___x_2391_, 4, v___f_2386_);
lean_ctor_set(v___x_2391_, 5, v___f_2385_);
return v___x_2391_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__6(void){
_start:
{
uint8_t v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2392_ = 0;
v___x_2393_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__5, &l_Lean_instInhabitedParametricAttribute_default___closed__5_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__5);
v___x_2394_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_2395_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2395_, 0, v___x_2394_);
lean_ctor_set(v___x_2395_, 1, v___x_2393_);
lean_ctor_set_uint8(v___x_2395_, sizeof(void*)*2, v___x_2392_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default(lean_object* v_00_u03b1_2396_){
_start:
{
lean_object* v___x_2397_; 
v___x_2397_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__6, &l_Lean_instInhabitedParametricAttribute_default___closed__6_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__6);
return v___x_2397_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute___closed__0(void){
_start:
{
lean_object* v___x_2398_; 
v___x_2398_ = l_Lean_instInhabitedParametricAttribute_default(lean_box(0));
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute(lean_object* v_a_2399_){
_start:
{
lean_object* v___x_2400_; 
v___x_2400_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute___closed__0, &l_Lean_instInhabitedParametricAttribute___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute___closed__0);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__0(lean_object* v_x_2401_, lean_object* v_p_2402_){
_start:
{
lean_object* v_fst_2403_; lean_object* v_snd_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2421_; 
v_fst_2403_ = lean_ctor_get(v_x_2401_, 0);
v_snd_2404_ = lean_ctor_get(v_x_2401_, 1);
v_isSharedCheck_2421_ = !lean_is_exclusive(v_x_2401_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2406_ = v_x_2401_;
v_isShared_2407_ = v_isSharedCheck_2421_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_snd_2404_);
lean_inc(v_fst_2403_);
lean_dec(v_x_2401_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2421_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v_fst_2408_; lean_object* v_snd_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2420_; 
v_fst_2408_ = lean_ctor_get(v_p_2402_, 0);
v_snd_2409_ = lean_ctor_get(v_p_2402_, 1);
v_isSharedCheck_2420_ = !lean_is_exclusive(v_p_2402_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2411_ = v_p_2402_;
v_isShared_2412_ = v_isSharedCheck_2420_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_snd_2409_);
lean_inc(v_fst_2408_);
lean_dec(v_p_2402_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2420_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2414_; 
lean_inc(v_fst_2408_);
if (v_isShared_2407_ == 0)
{
lean_ctor_set_tag(v___x_2406_, 1);
lean_ctor_set(v___x_2406_, 1, v_fst_2403_);
lean_ctor_set(v___x_2406_, 0, v_fst_2408_);
v___x_2414_ = v___x_2406_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_fst_2408_);
lean_ctor_set(v_reuseFailAlloc_2419_, 1, v_fst_2403_);
v___x_2414_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
lean_object* v___x_2415_; lean_object* v___x_2417_; 
v___x_2415_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2408_, v_snd_2409_, v_snd_2404_);
if (v_isShared_2412_ == 0)
{
lean_ctor_set(v___x_2411_, 1, v___x_2415_);
lean_ctor_set(v___x_2411_, 0, v___x_2414_);
v___x_2417_ = v___x_2411_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2414_);
lean_ctor_set(v_reuseFailAlloc_2418_, 1, v___x_2415_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(lean_object* v_init_2422_, lean_object* v_x_2423_){
_start:
{
if (lean_obj_tag(v_x_2423_) == 0)
{
lean_object* v_k_2424_; lean_object* v_v_2425_; lean_object* v_l_2426_; lean_object* v_r_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; 
v_k_2424_ = lean_ctor_get(v_x_2423_, 1);
v_v_2425_ = lean_ctor_get(v_x_2423_, 2);
v_l_2426_ = lean_ctor_get(v_x_2423_, 3);
v_r_2427_ = lean_ctor_get(v_x_2423_, 4);
v___x_2428_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2422_, v_l_2426_);
lean_inc(v_v_2425_);
lean_inc(v_k_2424_);
v___x_2429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2429_, 0, v_k_2424_);
lean_ctor_set(v___x_2429_, 1, v_v_2425_);
v___x_2430_ = lean_array_push(v___x_2428_, v___x_2429_);
v_init_2422_ = v___x_2430_;
v_x_2423_ = v_r_2427_;
goto _start;
}
else
{
return v_init_2422_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg___boxed(lean_object* v_init_2432_, lean_object* v_x_2433_){
_start:
{
lean_object* v_res_2434_; 
v_res_2434_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2432_, v_x_2433_);
lean_dec(v_x_2433_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(lean_object* v_snd_2435_, lean_object* v_as_2436_, size_t v_i_2437_, size_t v_stop_2438_, lean_object* v_b_2439_){
_start:
{
lean_object* v___y_2441_; uint8_t v___x_2445_; 
v___x_2445_ = lean_usize_dec_eq(v_i_2437_, v_stop_2438_);
if (v___x_2445_ == 0)
{
lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2446_ = lean_array_uget_borrowed(v_as_2436_, v_i_2437_);
v___x_2447_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_2435_, v___x_2446_);
if (lean_obj_tag(v___x_2447_) == 0)
{
v___y_2441_ = v_b_2439_;
goto v___jp_2440_;
}
else
{
lean_object* v_val_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; 
v_val_2448_ = lean_ctor_get(v___x_2447_, 0);
lean_inc(v_val_2448_);
lean_dec_ref_known(v___x_2447_, 1);
lean_inc(v___x_2446_);
v___x_2449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2449_, 0, v___x_2446_);
lean_ctor_set(v___x_2449_, 1, v_val_2448_);
v___x_2450_ = lean_array_push(v_b_2439_, v___x_2449_);
v___y_2441_ = v___x_2450_;
goto v___jp_2440_;
}
}
else
{
return v_b_2439_;
}
v___jp_2440_:
{
size_t v___x_2442_; size_t v___x_2443_; 
v___x_2442_ = ((size_t)1ULL);
v___x_2443_ = lean_usize_add(v_i_2437_, v___x_2442_);
v_i_2437_ = v___x_2443_;
v_b_2439_ = v___y_2441_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg___boxed(lean_object* v_snd_2451_, lean_object* v_as_2452_, lean_object* v_i_2453_, lean_object* v_stop_2454_, lean_object* v_b_2455_){
_start:
{
size_t v_i_boxed_2456_; size_t v_stop_boxed_2457_; lean_object* v_res_2458_; 
v_i_boxed_2456_ = lean_unbox_usize(v_i_2453_);
lean_dec(v_i_2453_);
v_stop_boxed_2457_ = lean_unbox_usize(v_stop_2454_);
lean_dec(v_stop_2454_);
v_res_2458_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2451_, v_as_2452_, v_i_boxed_2456_, v_stop_boxed_2457_, v_b_2455_);
lean_dec_ref(v_as_2452_);
lean_dec(v_snd_2451_);
return v_res_2458_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(lean_object* v_snd_2459_, lean_object* v_as_2460_, lean_object* v_start_2461_, lean_object* v_stop_2462_){
_start:
{
lean_object* v___x_2463_; uint8_t v___x_2464_; 
v___x_2463_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_2464_ = lean_nat_dec_lt(v_start_2461_, v_stop_2462_);
if (v___x_2464_ == 0)
{
return v___x_2463_;
}
else
{
lean_object* v___x_2465_; uint8_t v___x_2466_; 
v___x_2465_ = lean_array_get_size(v_as_2460_);
v___x_2466_ = lean_nat_dec_le(v_stop_2462_, v___x_2465_);
if (v___x_2466_ == 0)
{
uint8_t v___x_2467_; 
v___x_2467_ = lean_nat_dec_lt(v_start_2461_, v___x_2465_);
if (v___x_2467_ == 0)
{
return v___x_2463_;
}
else
{
size_t v___x_2468_; size_t v___x_2469_; lean_object* v___x_2470_; 
v___x_2468_ = lean_usize_of_nat(v_start_2461_);
v___x_2469_ = lean_usize_of_nat(v___x_2465_);
v___x_2470_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2459_, v_as_2460_, v___x_2468_, v___x_2469_, v___x_2463_);
return v___x_2470_;
}
}
else
{
size_t v___x_2471_; size_t v___x_2472_; lean_object* v___x_2473_; 
v___x_2471_ = lean_usize_of_nat(v_start_2461_);
v___x_2472_ = lean_usize_of_nat(v_stop_2462_);
v___x_2473_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2459_, v_as_2460_, v___x_2471_, v___x_2472_, v___x_2463_);
return v___x_2473_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg___boxed(lean_object* v_snd_2474_, lean_object* v_as_2475_, lean_object* v_start_2476_, lean_object* v_stop_2477_){
_start:
{
lean_object* v_res_2478_; 
v_res_2478_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2474_, v_as_2475_, v_start_2476_, v_stop_2477_);
lean_dec(v_stop_2477_);
lean_dec(v_start_2476_);
lean_dec_ref(v_as_2475_);
lean_dec(v_snd_2474_);
return v_res_2478_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(lean_object* v_hi_2479_, lean_object* v_pivot_2480_, lean_object* v_as_2481_, lean_object* v_i_2482_, lean_object* v_k_2483_){
_start:
{
uint8_t v___x_2484_; 
v___x_2484_ = lean_nat_dec_lt(v_k_2483_, v_hi_2479_);
if (v___x_2484_ == 0)
{
lean_object* v___x_2485_; lean_object* v___x_2486_; 
lean_dec(v_k_2483_);
v___x_2485_ = lean_array_fswap(v_as_2481_, v_i_2482_, v_hi_2479_);
v___x_2486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2486_, 0, v_i_2482_);
lean_ctor_set(v___x_2486_, 1, v___x_2485_);
return v___x_2486_;
}
else
{
lean_object* v___x_2487_; lean_object* v_fst_2488_; lean_object* v_fst_2489_; uint8_t v___x_2490_; 
v___x_2487_ = lean_array_fget_borrowed(v_as_2481_, v_k_2483_);
v_fst_2488_ = lean_ctor_get(v___x_2487_, 0);
v_fst_2489_ = lean_ctor_get(v_pivot_2480_, 0);
v___x_2490_ = l_Lean_Name_quickLt(v_fst_2488_, v_fst_2489_);
if (v___x_2490_ == 0)
{
lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2491_ = lean_unsigned_to_nat(1u);
v___x_2492_ = lean_nat_add(v_k_2483_, v___x_2491_);
lean_dec(v_k_2483_);
v_k_2483_ = v___x_2492_;
goto _start;
}
else
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2494_ = lean_array_fswap(v_as_2481_, v_i_2482_, v_k_2483_);
v___x_2495_ = lean_unsigned_to_nat(1u);
v___x_2496_ = lean_nat_add(v_i_2482_, v___x_2495_);
lean_dec(v_i_2482_);
v___x_2497_ = lean_nat_add(v_k_2483_, v___x_2495_);
lean_dec(v_k_2483_);
v_as_2481_ = v___x_2494_;
v_i_2482_ = v___x_2496_;
v_k_2483_ = v___x_2497_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg___boxed(lean_object* v_hi_2499_, lean_object* v_pivot_2500_, lean_object* v_as_2501_, lean_object* v_i_2502_, lean_object* v_k_2503_){
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2499_, v_pivot_2500_, v_as_2501_, v_i_2502_, v_k_2503_);
lean_dec_ref(v_pivot_2500_);
lean_dec(v_hi_2499_);
return v_res_2504_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(lean_object* v_a_2505_, lean_object* v_b_2506_){
_start:
{
lean_object* v_fst_2507_; lean_object* v_fst_2508_; uint8_t v___x_2509_; 
v_fst_2507_ = lean_ctor_get(v_a_2505_, 0);
v_fst_2508_ = lean_ctor_get(v_b_2506_, 0);
v___x_2509_ = l_Lean_Name_quickLt(v_fst_2507_, v_fst_2508_);
return v___x_2509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0___boxed(lean_object* v_a_2510_, lean_object* v_b_2511_){
_start:
{
uint8_t v_res_2512_; lean_object* v_r_2513_; 
v_res_2512_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v_a_2510_, v_b_2511_);
lean_dec_ref(v_b_2511_);
lean_dec_ref(v_a_2510_);
v_r_2513_ = lean_box(v_res_2512_);
return v_r_2513_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(lean_object* v_n_2514_, lean_object* v_as_2515_, lean_object* v_lo_2516_, lean_object* v_hi_2517_){
_start:
{
lean_object* v___y_2519_; uint8_t v___x_2529_; 
v___x_2529_ = lean_nat_dec_lt(v_lo_2516_, v_hi_2517_);
if (v___x_2529_ == 0)
{
lean_dec(v_lo_2516_);
return v_as_2515_;
}
else
{
lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v_mid_2532_; lean_object* v___y_2534_; lean_object* v___y_2540_; lean_object* v___x_2545_; lean_object* v___x_2546_; uint8_t v___x_2547_; 
v___x_2530_ = lean_nat_add(v_lo_2516_, v_hi_2517_);
v___x_2531_ = lean_unsigned_to_nat(1u);
v_mid_2532_ = lean_nat_shiftr(v___x_2530_, v___x_2531_);
lean_dec(v___x_2530_);
v___x_2545_ = lean_array_fget_borrowed(v_as_2515_, v_mid_2532_);
v___x_2546_ = lean_array_fget_borrowed(v_as_2515_, v_lo_2516_);
v___x_2547_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2545_, v___x_2546_);
if (v___x_2547_ == 0)
{
v___y_2540_ = v_as_2515_;
goto v___jp_2539_;
}
else
{
lean_object* v___x_2548_; 
v___x_2548_ = lean_array_fswap(v_as_2515_, v_lo_2516_, v_mid_2532_);
v___y_2540_ = v___x_2548_;
goto v___jp_2539_;
}
v___jp_2533_:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; uint8_t v___x_2537_; 
v___x_2535_ = lean_array_fget_borrowed(v___y_2534_, v_mid_2532_);
v___x_2536_ = lean_array_fget_borrowed(v___y_2534_, v_hi_2517_);
v___x_2537_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2535_, v___x_2536_);
if (v___x_2537_ == 0)
{
lean_dec(v_mid_2532_);
v___y_2519_ = v___y_2534_;
goto v___jp_2518_;
}
else
{
lean_object* v___x_2538_; 
v___x_2538_ = lean_array_fswap(v___y_2534_, v_mid_2532_, v_hi_2517_);
lean_dec(v_mid_2532_);
v___y_2519_ = v___x_2538_;
goto v___jp_2518_;
}
}
v___jp_2539_:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; uint8_t v___x_2543_; 
v___x_2541_ = lean_array_fget_borrowed(v___y_2540_, v_hi_2517_);
v___x_2542_ = lean_array_fget_borrowed(v___y_2540_, v_lo_2516_);
v___x_2543_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2541_, v___x_2542_);
if (v___x_2543_ == 0)
{
v___y_2534_ = v___y_2540_;
goto v___jp_2533_;
}
else
{
lean_object* v___x_2544_; 
v___x_2544_ = lean_array_fswap(v___y_2540_, v_lo_2516_, v_hi_2517_);
v___y_2534_ = v___x_2544_;
goto v___jp_2533_;
}
}
}
v___jp_2518_:
{
lean_object* v_pivot_2520_; lean_object* v___x_2521_; lean_object* v_fst_2522_; lean_object* v_snd_2523_; uint8_t v___x_2524_; 
v_pivot_2520_ = lean_array_fget(v___y_2519_, v_hi_2517_);
lean_inc_n(v_lo_2516_, 2);
v___x_2521_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2517_, v_pivot_2520_, v___y_2519_, v_lo_2516_, v_lo_2516_);
lean_dec(v_pivot_2520_);
v_fst_2522_ = lean_ctor_get(v___x_2521_, 0);
lean_inc(v_fst_2522_);
v_snd_2523_ = lean_ctor_get(v___x_2521_, 1);
lean_inc(v_snd_2523_);
lean_dec_ref(v___x_2521_);
v___x_2524_ = lean_nat_dec_le(v_hi_2517_, v_fst_2522_);
if (v___x_2524_ == 0)
{
lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2525_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2514_, v_snd_2523_, v_lo_2516_, v_fst_2522_);
v___x_2526_ = lean_unsigned_to_nat(1u);
v___x_2527_ = lean_nat_add(v_fst_2522_, v___x_2526_);
lean_dec(v_fst_2522_);
v_as_2515_ = v___x_2525_;
v_lo_2516_ = v___x_2527_;
goto _start;
}
else
{
lean_dec(v_fst_2522_);
lean_dec(v_lo_2516_);
return v_snd_2523_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___boxed(lean_object* v_n_2549_, lean_object* v_as_2550_, lean_object* v_lo_2551_, lean_object* v_hi_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2549_, v_as_2550_, v_lo_2551_, v_hi_2552_);
lean_dec(v_hi_2552_);
lean_dec(v_n_2549_);
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(lean_object* v_filterExport_2554_, lean_object* v_env_2555_, lean_object* v_as_2556_, size_t v_i_2557_, size_t v_stop_2558_, lean_object* v_b_2559_){
_start:
{
lean_object* v___y_2561_; uint8_t v___x_2565_; 
v___x_2565_ = lean_usize_dec_eq(v_i_2557_, v_stop_2558_);
if (v___x_2565_ == 0)
{
lean_object* v___x_2566_; lean_object* v_fst_2567_; lean_object* v_snd_2568_; lean_object* v___x_2569_; uint8_t v___x_2570_; 
v___x_2566_ = lean_array_uget_borrowed(v_as_2556_, v_i_2557_);
v_fst_2567_ = lean_ctor_get(v___x_2566_, 0);
v_snd_2568_ = lean_ctor_get(v___x_2566_, 1);
lean_inc_ref(v_filterExport_2554_);
lean_inc(v_snd_2568_);
lean_inc(v_fst_2567_);
lean_inc_ref(v_env_2555_);
v___x_2569_ = lean_apply_3(v_filterExport_2554_, v_env_2555_, v_fst_2567_, v_snd_2568_);
v___x_2570_ = lean_unbox(v___x_2569_);
if (v___x_2570_ == 0)
{
v___y_2561_ = v_b_2559_;
goto v___jp_2560_;
}
else
{
lean_object* v___x_2571_; 
lean_inc(v___x_2566_);
v___x_2571_ = lean_array_push(v_b_2559_, v___x_2566_);
v___y_2561_ = v___x_2571_;
goto v___jp_2560_;
}
}
else
{
lean_dec_ref(v_env_2555_);
lean_dec_ref(v_filterExport_2554_);
return v_b_2559_;
}
v___jp_2560_:
{
size_t v___x_2562_; size_t v___x_2563_; 
v___x_2562_ = ((size_t)1ULL);
v___x_2563_ = lean_usize_add(v_i_2557_, v___x_2562_);
v_i_2557_ = v___x_2563_;
v_b_2559_ = v___y_2561_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg___boxed(lean_object* v_filterExport_2572_, lean_object* v_env_2573_, lean_object* v_as_2574_, lean_object* v_i_2575_, lean_object* v_stop_2576_, lean_object* v_b_2577_){
_start:
{
size_t v_i_boxed_2578_; size_t v_stop_boxed_2579_; lean_object* v_res_2580_; 
v_i_boxed_2578_ = lean_unbox_usize(v_i_2575_);
lean_dec(v_i_2575_);
v_stop_boxed_2579_ = lean_unbox_usize(v_stop_2576_);
lean_dec(v_stop_2576_);
v_res_2580_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2572_, v_env_2573_, v_as_2574_, v_i_boxed_2578_, v_stop_boxed_2579_, v_b_2577_);
lean_dec_ref(v_as_2574_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1(lean_object* v_filterExport_2581_, uint8_t v_preserveOrder_2582_, lean_object* v_env_2583_, lean_object* v_x_2584_){
_start:
{
lean_object* v___y_2586_; 
if (v_preserveOrder_2582_ == 0)
{
lean_object* v_snd_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v_r_2605_; lean_object* v___x_2606_; lean_object* v___y_2608_; lean_object* v___y_2609_; uint8_t v___x_2611_; 
v_snd_2602_ = lean_ctor_get(v_x_2584_, 1);
lean_inc(v_snd_2602_);
lean_dec_ref(v_x_2584_);
v___x_2603_ = lean_unsigned_to_nat(0u);
v___x_2604_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v_r_2605_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v___x_2604_, v_snd_2602_);
lean_dec(v_snd_2602_);
v___x_2606_ = lean_array_get_size(v_r_2605_);
v___x_2611_ = lean_nat_dec_eq(v___x_2606_, v___x_2603_);
if (v___x_2611_ == 0)
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___y_2615_; uint8_t v___x_2617_; 
v___x_2612_ = lean_unsigned_to_nat(1u);
v___x_2613_ = lean_nat_sub(v___x_2606_, v___x_2612_);
v___x_2617_ = lean_nat_dec_le(v___x_2603_, v___x_2613_);
if (v___x_2617_ == 0)
{
lean_inc(v___x_2613_);
v___y_2615_ = v___x_2613_;
goto v___jp_2614_;
}
else
{
v___y_2615_ = v___x_2603_;
goto v___jp_2614_;
}
v___jp_2614_:
{
uint8_t v___x_2616_; 
v___x_2616_ = lean_nat_dec_le(v___y_2615_, v___x_2613_);
if (v___x_2616_ == 0)
{
lean_dec(v___x_2613_);
lean_inc(v___y_2615_);
v___y_2608_ = v___y_2615_;
v___y_2609_ = v___y_2615_;
goto v___jp_2607_;
}
else
{
v___y_2608_ = v___y_2615_;
v___y_2609_ = v___x_2613_;
goto v___jp_2607_;
}
}
}
else
{
v___y_2586_ = v_r_2605_;
goto v___jp_2585_;
}
v___jp_2607_:
{
lean_object* v___x_2610_; 
v___x_2610_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v___x_2606_, v_r_2605_, v___y_2608_, v___y_2609_);
lean_dec(v___y_2609_);
v___y_2586_ = v___x_2610_;
goto v___jp_2585_;
}
}
else
{
lean_object* v_fst_2618_; lean_object* v_snd_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
v_fst_2618_ = lean_ctor_get(v_x_2584_, 0);
lean_inc(v_fst_2618_);
v_snd_2619_ = lean_ctor_get(v_x_2584_, 1);
lean_inc(v_snd_2619_);
lean_dec_ref(v_x_2584_);
v___x_2620_ = lean_array_mk(v_fst_2618_);
v___x_2621_ = l_Array_reverse___redArg(v___x_2620_);
v___x_2622_ = lean_unsigned_to_nat(0u);
v___x_2623_ = lean_array_get_size(v___x_2621_);
v___x_2624_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2619_, v___x_2621_, v___x_2622_, v___x_2623_);
lean_dec_ref(v___x_2621_);
lean_dec(v_snd_2619_);
v___y_2586_ = v___x_2624_;
goto v___jp_2585_;
}
v___jp_2585_:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; uint8_t v___x_2590_; 
v___x_2587_ = lean_unsigned_to_nat(0u);
v___x_2588_ = lean_array_get_size(v___y_2586_);
v___x_2589_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_2590_ = lean_nat_dec_lt(v___x_2587_, v___x_2588_);
if (v___x_2590_ == 0)
{
lean_object* v___x_2591_; 
lean_dec_ref(v_env_2583_);
lean_dec_ref(v_filterExport_2581_);
v___x_2591_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2589_);
lean_ctor_set(v___x_2591_, 1, v___x_2589_);
lean_ctor_set(v___x_2591_, 2, v___y_2586_);
return v___x_2591_;
}
else
{
uint8_t v___x_2592_; 
v___x_2592_ = lean_nat_dec_le(v___x_2588_, v___x_2588_);
if (v___x_2592_ == 0)
{
if (v___x_2590_ == 0)
{
lean_object* v___x_2593_; 
lean_dec_ref(v_env_2583_);
lean_dec_ref(v_filterExport_2581_);
v___x_2593_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2593_, 0, v___x_2589_);
lean_ctor_set(v___x_2593_, 1, v___x_2589_);
lean_ctor_set(v___x_2593_, 2, v___y_2586_);
return v___x_2593_;
}
else
{
size_t v___x_2594_; size_t v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2594_ = ((size_t)0ULL);
v___x_2595_ = lean_usize_of_nat(v___x_2588_);
v___x_2596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2581_, v_env_2583_, v___y_2586_, v___x_2594_, v___x_2595_, v___x_2589_);
lean_inc_ref(v___x_2596_);
v___x_2597_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2596_);
lean_ctor_set(v___x_2597_, 1, v___x_2596_);
lean_ctor_set(v___x_2597_, 2, v___y_2586_);
return v___x_2597_;
}
}
else
{
size_t v___x_2598_; size_t v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2598_ = ((size_t)0ULL);
v___x_2599_ = lean_usize_of_nat(v___x_2588_);
v___x_2600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2581_, v_env_2583_, v___y_2586_, v___x_2598_, v___x_2599_, v___x_2589_);
lean_inc_ref(v___x_2600_);
v___x_2601_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2600_);
lean_ctor_set(v___x_2601_, 1, v___x_2600_);
lean_ctor_set(v___x_2601_, 2, v___y_2586_);
return v___x_2601_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed(lean_object* v_filterExport_2625_, lean_object* v_preserveOrder_2626_, lean_object* v_env_2627_, lean_object* v_x_2628_){
_start:
{
uint8_t v_preserveOrder_boxed_2629_; lean_object* v_res_2630_; 
v_preserveOrder_boxed_2629_ = lean_unbox(v_preserveOrder_2626_);
v_res_2630_ = l_Lean_registerParametricAttributeExt___redArg___lam__1(v_filterExport_2625_, v_preserveOrder_boxed_2629_, v_env_2627_, v_x_2628_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__2(lean_object* v_x_2640_){
_start:
{
lean_object* v_snd_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2655_; 
v_snd_2641_ = lean_ctor_get(v_x_2640_, 1);
v_isSharedCheck_2655_ = !lean_is_exclusive(v_x_2640_);
if (v_isSharedCheck_2655_ == 0)
{
lean_object* v_unused_2656_; 
v_unused_2656_ = lean_ctor_get(v_x_2640_, 0);
lean_dec(v_unused_2656_);
v___x_2643_ = v_x_2640_;
v_isShared_2644_ = v_isSharedCheck_2655_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_snd_2641_);
lean_dec(v_x_2640_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2655_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2645_; lean_object* v___y_2647_; 
v___x_2645_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__3));
if (lean_obj_tag(v_snd_2641_) == 0)
{
lean_object* v_size_2653_; 
v_size_2653_ = lean_ctor_get(v_snd_2641_, 0);
lean_inc(v_size_2653_);
lean_dec_ref_known(v_snd_2641_, 5);
v___y_2647_ = v_size_2653_;
goto v___jp_2646_;
}
else
{
lean_object* v___x_2654_; 
v___x_2654_ = lean_unsigned_to_nat(0u);
v___y_2647_ = v___x_2654_;
goto v___jp_2646_;
}
v___jp_2646_:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2651_; 
v___x_2648_ = l_Nat_reprFast(v___y_2647_);
v___x_2649_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2649_, 0, v___x_2648_);
if (v_isShared_2644_ == 0)
{
lean_ctor_set_tag(v___x_2643_, 5);
lean_ctor_set(v___x_2643_, 1, v___x_2649_);
lean_ctor_set(v___x_2643_, 0, v___x_2645_);
v___x_2651_ = v___x_2643_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v___x_2645_);
lean_ctor_set(v_reuseFailAlloc_2652_, 1, v___x_2649_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3(lean_object* v_x_2657_){
_start:
{
lean_object* v___x_2658_; 
v___x_2658_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3___boxed(lean_object* v_x_2659_){
_start:
{
lean_object* v_res_2660_; 
v_res_2660_ = l_Lean_registerParametricAttributeExt___redArg___lam__3(v_x_2659_);
lean_dec_ref(v_x_2659_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4(lean_object* v___x_2661_){
_start:
{
lean_object* v___x_2663_; 
v___x_2663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2663_, 0, v___x_2661_);
return v___x_2663_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4___boxed(lean_object* v___x_2664_, lean_object* v___y_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l_Lean_registerParametricAttributeExt___redArg___lam__4(v___x_2664_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5(lean_object* v___x_2667_, lean_object* v_x_2668_, lean_object* v___y_2669_){
_start:
{
lean_object* v___x_2671_; 
v___x_2671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2667_);
return v___x_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5___boxed(lean_object* v___x_2672_, lean_object* v_x_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_){
_start:
{
lean_object* v_res_2676_; 
v_res_2676_ = l_Lean_registerParametricAttributeExt___redArg___lam__5(v___x_2672_, v_x_2673_, v___y_2674_);
lean_dec_ref(v___y_2674_);
lean_dec_ref(v_x_2673_);
return v_res_2676_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg(lean_object* v_ref_2687_, uint8_t v_preserveOrder_2688_, lean_object* v_filterExport_2689_){
_start:
{
lean_object* v___f_2691_; lean_object* v___x_2692_; lean_object* v___f_2693_; lean_object* v___f_2694_; lean_object* v___f_2695_; lean_object* v___f_2696_; lean_object* v___f_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___f_2691_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__0));
v___x_2692_ = lean_box(v_preserveOrder_2688_);
v___f_2693_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2693_, 0, v_filterExport_2689_);
lean_closure_set(v___f_2693_, 1, v___x_2692_);
v___f_2694_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__1));
v___f_2695_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__2));
v___f_2696_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__4));
v___f_2697_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__5));
v___x_2698_ = lean_box(2);
v___x_2699_ = lean_box(0);
v___x_2700_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2700_, 0, v_ref_2687_);
lean_ctor_set(v___x_2700_, 1, v___f_2696_);
lean_ctor_set(v___x_2700_, 2, v___f_2697_);
lean_ctor_set(v___x_2700_, 3, v___f_2691_);
lean_ctor_set(v___x_2700_, 4, v___f_2693_);
lean_ctor_set(v___x_2700_, 5, v___f_2694_);
lean_ctor_set(v___x_2700_, 6, v___x_2698_);
lean_ctor_set(v___x_2700_, 7, v___x_2699_);
v___x_2701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2700_);
lean_ctor_set(v___x_2701_, 1, v___f_2695_);
v___x_2702_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2701_);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___boxed(lean_object* v_ref_2703_, lean_object* v_preserveOrder_2704_, lean_object* v_filterExport_2705_, lean_object* v_a_2706_){
_start:
{
uint8_t v_preserveOrder_boxed_2707_; lean_object* v_res_2708_; 
v_preserveOrder_boxed_2707_ = lean_unbox(v_preserveOrder_2704_);
v_res_2708_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_2703_, v_preserveOrder_boxed_2707_, v_filterExport_2705_);
return v_res_2708_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt(lean_object* v_00_u03b1_2709_, lean_object* v_ref_2710_, uint8_t v_preserveOrder_2711_, lean_object* v_filterExport_2712_){
_start:
{
lean_object* v___x_2714_; 
v___x_2714_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_2710_, v_preserveOrder_2711_, v_filterExport_2712_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___boxed(lean_object* v_00_u03b1_2715_, lean_object* v_ref_2716_, lean_object* v_preserveOrder_2717_, lean_object* v_filterExport_2718_, lean_object* v_a_2719_){
_start:
{
uint8_t v_preserveOrder_boxed_2720_; lean_object* v_res_2721_; 
v_preserveOrder_boxed_2720_ = lean_unbox(v_preserveOrder_2717_);
v_res_2721_ = l_Lean_registerParametricAttributeExt(v_00_u03b1_2715_, v_ref_2716_, v_preserveOrder_boxed_2720_, v_filterExport_2718_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(lean_object* v_00_u03b1_2722_, lean_object* v_filterExport_2723_, lean_object* v_env_2724_, lean_object* v_as_2725_, size_t v_i_2726_, size_t v_stop_2727_, lean_object* v_b_2728_){
_start:
{
lean_object* v___x_2729_; 
v___x_2729_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2723_, v_env_2724_, v_as_2725_, v_i_2726_, v_stop_2727_, v_b_2728_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___boxed(lean_object* v_00_u03b1_2730_, lean_object* v_filterExport_2731_, lean_object* v_env_2732_, lean_object* v_as_2733_, lean_object* v_i_2734_, lean_object* v_stop_2735_, lean_object* v_b_2736_){
_start:
{
size_t v_i_boxed_2737_; size_t v_stop_boxed_2738_; lean_object* v_res_2739_; 
v_i_boxed_2737_ = lean_unbox_usize(v_i_2734_);
lean_dec(v_i_2734_);
v_stop_boxed_2738_ = lean_unbox_usize(v_stop_2735_);
lean_dec(v_stop_2735_);
v_res_2739_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(v_00_u03b1_2730_, v_filterExport_2731_, v_env_2732_, v_as_2733_, v_i_boxed_2737_, v_stop_boxed_2738_, v_b_2736_);
lean_dec_ref(v_as_2733_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(lean_object* v_init_2740_, lean_object* v_t_2741_){
_start:
{
lean_object* v___x_2742_; 
v___x_2742_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2740_, v_t_2741_);
return v___x_2742_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg___boxed(lean_object* v_init_2743_, lean_object* v_t_2744_){
_start:
{
lean_object* v_res_2745_; 
v_res_2745_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(v_init_2743_, v_t_2744_);
lean_dec(v_t_2744_);
return v_res_2745_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(lean_object* v_00_u03b1_2746_, lean_object* v_init_2747_, lean_object* v_t_2748_){
_start:
{
lean_object* v___x_2749_; 
v___x_2749_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2747_, v_t_2748_);
return v___x_2749_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___boxed(lean_object* v_00_u03b1_2750_, lean_object* v_init_2751_, lean_object* v_t_2752_){
_start:
{
lean_object* v_res_2753_; 
v_res_2753_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(v_00_u03b1_2750_, v_init_2751_, v_t_2752_);
lean_dec(v_t_2752_);
return v_res_2753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(lean_object* v_00_u03b1_2754_, lean_object* v_n_2755_, lean_object* v_as_2756_, lean_object* v_lo_2757_, lean_object* v_hi_2758_, lean_object* v_w_2759_, lean_object* v_hlo_2760_, lean_object* v_hhi_2761_){
_start:
{
lean_object* v___x_2762_; 
v___x_2762_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2755_, v_as_2756_, v_lo_2757_, v_hi_2758_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___boxed(lean_object* v_00_u03b1_2763_, lean_object* v_n_2764_, lean_object* v_as_2765_, lean_object* v_lo_2766_, lean_object* v_hi_2767_, lean_object* v_w_2768_, lean_object* v_hlo_2769_, lean_object* v_hhi_2770_){
_start:
{
lean_object* v_res_2771_; 
v_res_2771_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(v_00_u03b1_2763_, v_n_2764_, v_as_2765_, v_lo_2766_, v_hi_2767_, v_w_2768_, v_hlo_2769_, v_hhi_2770_);
lean_dec(v_hi_2767_);
lean_dec(v_n_2764_);
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(lean_object* v_00_u03b1_2772_, lean_object* v_snd_2773_, lean_object* v_as_2774_, lean_object* v_start_2775_, lean_object* v_stop_2776_){
_start:
{
lean_object* v___x_2777_; 
v___x_2777_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2773_, v_as_2774_, v_start_2775_, v_stop_2776_);
return v___x_2777_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___boxed(lean_object* v_00_u03b1_2778_, lean_object* v_snd_2779_, lean_object* v_as_2780_, lean_object* v_start_2781_, lean_object* v_stop_2782_){
_start:
{
lean_object* v_res_2783_; 
v_res_2783_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(v_00_u03b1_2778_, v_snd_2779_, v_as_2780_, v_start_2781_, v_stop_2782_);
lean_dec(v_stop_2782_);
lean_dec(v_start_2781_);
lean_dec_ref(v_as_2780_);
lean_dec(v_snd_2779_);
return v_res_2783_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(lean_object* v_00_u03b1_2784_, lean_object* v_init_2785_, lean_object* v_x_2786_){
_start:
{
lean_object* v___x_2787_; 
v___x_2787_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2785_, v_x_2786_);
return v___x_2787_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2788_, lean_object* v_init_2789_, lean_object* v_x_2790_){
_start:
{
lean_object* v_res_2791_; 
v_res_2791_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(v_00_u03b1_2788_, v_init_2789_, v_x_2790_);
lean_dec(v_x_2790_);
return v_res_2791_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(lean_object* v_00_u03b1_2792_, lean_object* v_n_2793_, lean_object* v_lo_2794_, lean_object* v_hi_2795_, lean_object* v_hhi_2796_, lean_object* v_pivot_2797_, lean_object* v_as_2798_, lean_object* v_i_2799_, lean_object* v_k_2800_, lean_object* v_ilo_2801_, lean_object* v_ik_2802_, lean_object* v_w_2803_){
_start:
{
lean_object* v___x_2804_; 
v___x_2804_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2795_, v_pivot_2797_, v_as_2798_, v_i_2799_, v_k_2800_);
return v___x_2804_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2805_, lean_object* v_n_2806_, lean_object* v_lo_2807_, lean_object* v_hi_2808_, lean_object* v_hhi_2809_, lean_object* v_pivot_2810_, lean_object* v_as_2811_, lean_object* v_i_2812_, lean_object* v_k_2813_, lean_object* v_ilo_2814_, lean_object* v_ik_2815_, lean_object* v_w_2816_){
_start:
{
lean_object* v_res_2817_; 
v_res_2817_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(v_00_u03b1_2805_, v_n_2806_, v_lo_2807_, v_hi_2808_, v_hhi_2809_, v_pivot_2810_, v_as_2811_, v_i_2812_, v_k_2813_, v_ilo_2814_, v_ik_2815_, v_w_2816_);
lean_dec_ref(v_pivot_2810_);
lean_dec(v_hi_2808_);
lean_dec(v_lo_2807_);
lean_dec(v_n_2806_);
return v_res_2817_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(lean_object* v_00_u03b1_2818_, lean_object* v_snd_2819_, lean_object* v_as_2820_, size_t v_i_2821_, size_t v_stop_2822_, lean_object* v_b_2823_){
_start:
{
lean_object* v___x_2824_; 
v___x_2824_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2819_, v_as_2820_, v_i_2821_, v_stop_2822_, v_b_2823_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2825_, lean_object* v_snd_2826_, lean_object* v_as_2827_, lean_object* v_i_2828_, lean_object* v_stop_2829_, lean_object* v_b_2830_){
_start:
{
size_t v_i_boxed_2831_; size_t v_stop_boxed_2832_; lean_object* v_res_2833_; 
v_i_boxed_2831_ = lean_unbox_usize(v_i_2828_);
lean_dec(v_i_2828_);
v_stop_boxed_2832_ = lean_unbox_usize(v_stop_2829_);
lean_dec(v_stop_2829_);
v_res_2833_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(v_00_u03b1_2825_, v_snd_2826_, v_as_2827_, v_i_boxed_2831_, v_stop_boxed_2832_, v_b_2830_);
lean_dec_ref(v_as_2827_);
lean_dec(v_snd_2826_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(lean_object* v_env_2834_, lean_object* v___y_2835_){
_start:
{
lean_object* v___x_2837_; lean_object* v_nextMacroScope_2838_; lean_object* v_ngen_2839_; lean_object* v_auxDeclNGen_2840_; lean_object* v_traceState_2841_; lean_object* v_messages_2842_; lean_object* v_infoState_2843_; lean_object* v_snapshotTasks_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2855_; 
v___x_2837_ = lean_st_ref_take(v___y_2835_);
v_nextMacroScope_2838_ = lean_ctor_get(v___x_2837_, 1);
v_ngen_2839_ = lean_ctor_get(v___x_2837_, 2);
v_auxDeclNGen_2840_ = lean_ctor_get(v___x_2837_, 3);
v_traceState_2841_ = lean_ctor_get(v___x_2837_, 4);
v_messages_2842_ = lean_ctor_get(v___x_2837_, 6);
v_infoState_2843_ = lean_ctor_get(v___x_2837_, 7);
v_snapshotTasks_2844_ = lean_ctor_get(v___x_2837_, 8);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2855_ == 0)
{
lean_object* v_unused_2856_; lean_object* v_unused_2857_; 
v_unused_2856_ = lean_ctor_get(v___x_2837_, 5);
lean_dec(v_unused_2856_);
v_unused_2857_ = lean_ctor_get(v___x_2837_, 0);
lean_dec(v_unused_2857_);
v___x_2846_ = v___x_2837_;
v_isShared_2847_ = v_isSharedCheck_2855_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_snapshotTasks_2844_);
lean_inc(v_infoState_2843_);
lean_inc(v_messages_2842_);
lean_inc(v_traceState_2841_);
lean_inc(v_auxDeclNGen_2840_);
lean_inc(v_ngen_2839_);
lean_inc(v_nextMacroScope_2838_);
lean_dec(v___x_2837_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2855_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
lean_object* v___x_2848_; lean_object* v___x_2850_; 
v___x_2848_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2847_ == 0)
{
lean_ctor_set(v___x_2846_, 5, v___x_2848_);
lean_ctor_set(v___x_2846_, 0, v_env_2834_);
v___x_2850_ = v___x_2846_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_env_2834_);
lean_ctor_set(v_reuseFailAlloc_2854_, 1, v_nextMacroScope_2838_);
lean_ctor_set(v_reuseFailAlloc_2854_, 2, v_ngen_2839_);
lean_ctor_set(v_reuseFailAlloc_2854_, 3, v_auxDeclNGen_2840_);
lean_ctor_set(v_reuseFailAlloc_2854_, 4, v_traceState_2841_);
lean_ctor_set(v_reuseFailAlloc_2854_, 5, v___x_2848_);
lean_ctor_set(v_reuseFailAlloc_2854_, 6, v_messages_2842_);
lean_ctor_set(v_reuseFailAlloc_2854_, 7, v_infoState_2843_);
lean_ctor_set(v_reuseFailAlloc_2854_, 8, v_snapshotTasks_2844_);
v___x_2850_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___x_2851_ = lean_st_ref_put(v___y_2835_, v___x_2850_);
v___x_2852_ = lean_box(0);
v___x_2853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2852_);
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
lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; uint8_t v___y_2887_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; uint8_t v___x_2936_; uint8_t v___x_2937_; 
v___x_2936_ = 0;
v___x_2937_ = l_Lean_instBEqAttributeKind_beq(v_kind_2878_, v___x_2936_);
if (v___x_2937_ == 0)
{
lean_object* v_name_2938_; lean_object* v___x_2939_; 
lean_dec(v_stx_2877_);
lean_dec(v_decl_2876_);
lean_dec_ref(v_afterSet_2874_);
lean_dec_ref(v_ext_2873_);
lean_dec_ref(v_getParam_2872_);
v_name_2938_ = lean_ctor_get(v_toAttributeImplCore_2875_, 1);
lean_inc(v_name_2938_);
lean_dec_ref(v_toAttributeImplCore_2875_);
v___x_2939_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2938_, v_kind_2878_, v___y_2879_, v___y_2880_);
return v___x_2939_;
}
else
{
goto v___jp_2930_;
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
lean_object* v_a_2894_; lean_object* v___x_2895_; lean_object* v_toEnvExtension_2896_; lean_object* v_env_2897_; lean_object* v_nextMacroScope_2898_; lean_object* v_ngen_2899_; lean_object* v_auxDeclNGen_2900_; lean_object* v_traceState_2901_; lean_object* v_messages_2902_; lean_object* v_infoState_2903_; lean_object* v_snapshotTasks_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2920_; 
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
v_messages_2902_ = lean_ctor_get(v___x_2895_, 6);
v_infoState_2903_ = lean_ctor_get(v___x_2895_, 7);
v_snapshotTasks_2904_ = lean_ctor_get(v___x_2895_, 8);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2920_ == 0)
{
lean_object* v_unused_2921_; 
v_unused_2921_ = lean_ctor_get(v___x_2895_, 5);
lean_dec(v_unused_2921_);
v___x_2906_ = v___x_2895_;
v_isShared_2907_ = v_isSharedCheck_2920_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_snapshotTasks_2904_);
lean_inc(v_infoState_2903_);
lean_inc(v_messages_2902_);
lean_inc(v_traceState_2901_);
lean_inc(v_auxDeclNGen_2900_);
lean_inc(v_ngen_2899_);
lean_inc(v_nextMacroScope_2898_);
lean_inc(v_env_2897_);
lean_dec(v___x_2895_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2920_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v_asyncMode_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2913_; 
v_asyncMode_2908_ = lean_ctor_get(v_toEnvExtension_2896_, 2);
lean_inc(v_asyncMode_2908_);
lean_inc(v_a_2894_);
lean_inc_n(v_decl_2876_, 2);
v___x_2909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2909_, 0, v_decl_2876_);
lean_ctor_set(v___x_2909_, 1, v_a_2894_);
v___x_2910_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2873_, v_env_2897_, v___x_2909_, v_asyncMode_2908_, v_decl_2876_);
lean_dec(v_asyncMode_2908_);
v___x_2911_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2907_ == 0)
{
lean_ctor_set(v___x_2906_, 5, v___x_2911_);
lean_ctor_set(v___x_2906_, 0, v___x_2910_);
v___x_2913_ = v___x_2906_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v___x_2910_);
lean_ctor_set(v_reuseFailAlloc_2919_, 1, v_nextMacroScope_2898_);
lean_ctor_set(v_reuseFailAlloc_2919_, 2, v_ngen_2899_);
lean_ctor_set(v_reuseFailAlloc_2919_, 3, v_auxDeclNGen_2900_);
lean_ctor_set(v_reuseFailAlloc_2919_, 4, v_traceState_2901_);
lean_ctor_set(v_reuseFailAlloc_2919_, 5, v___x_2911_);
lean_ctor_set(v_reuseFailAlloc_2919_, 6, v_messages_2902_);
lean_ctor_set(v_reuseFailAlloc_2919_, 7, v_infoState_2903_);
lean_ctor_set(v_reuseFailAlloc_2919_, 8, v_snapshotTasks_2904_);
v___x_2913_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2914_ = lean_st_ref_put(v___y_2892_, v___x_2913_);
lean_inc(v___y_2892_);
lean_inc_ref(v___y_2891_);
v___x_2915_ = lean_apply_5(v_afterSet_2874_, v_decl_2876_, v_a_2894_, v___y_2891_, v___y_2892_, lean_box(0));
if (lean_obj_tag(v___x_2915_) == 0)
{
lean_dec_ref(v___y_2890_);
return v___x_2915_;
}
else
{
lean_object* v_a_2916_; uint8_t v___x_2917_; 
v_a_2916_ = lean_ctor_get(v___x_2915_, 0);
lean_inc(v_a_2916_);
v___x_2917_ = l_Lean_Exception_isInterrupt(v_a_2916_);
if (v___x_2917_ == 0)
{
uint8_t v___x_2918_; 
v___x_2918_ = l_Lean_Exception_isRuntime(v_a_2916_);
v___y_2883_ = v___y_2890_;
v___y_2884_ = v___x_2915_;
v___y_2885_ = v___y_2892_;
v___y_2886_ = v___y_2891_;
v___y_2887_ = v___x_2918_;
goto v___jp_2882_;
}
else
{
lean_dec(v_a_2916_);
v___y_2883_ = v___y_2890_;
v___y_2884_ = v___x_2915_;
v___y_2885_ = v___y_2892_;
v___y_2886_ = v___y_2891_;
v___y_2887_ = v___x_2917_;
goto v___jp_2882_;
}
}
}
}
}
else
{
lean_object* v_a_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2929_; 
lean_dec_ref(v___y_2890_);
lean_dec(v_decl_2876_);
lean_dec_ref(v_afterSet_2874_);
lean_dec_ref(v_ext_2873_);
v_a_2922_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2924_ = v___x_2893_;
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_a_2922_);
lean_dec(v___x_2893_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2927_; 
if (v_isShared_2925_ == 0)
{
v___x_2927_ = v___x_2924_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_a_2922_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
}
v___jp_2930_:
{
lean_object* v___x_2931_; lean_object* v_env_2932_; lean_object* v___x_2933_; 
v___x_2931_ = lean_st_ref_get(v___y_2880_);
v_env_2932_ = lean_ctor_get(v___x_2931_, 0);
lean_inc_ref(v_env_2932_);
lean_dec(v___x_2931_);
v___x_2933_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2932_, v_decl_2876_);
if (lean_obj_tag(v___x_2933_) == 0)
{
lean_dec_ref(v_toAttributeImplCore_2875_);
v___y_2890_ = v_env_2932_;
v___y_2891_ = v___y_2879_;
v___y_2892_ = v___y_2880_;
goto v___jp_2889_;
}
else
{
lean_object* v_name_2934_; lean_object* v___x_2935_; 
lean_dec_ref_known(v___x_2933_, 1);
lean_dec_ref(v_env_2932_);
lean_dec(v_stx_2877_);
lean_dec_ref(v_afterSet_2874_);
lean_dec_ref(v_ext_2873_);
lean_dec_ref(v_getParam_2872_);
v_name_2934_ = lean_ctor_get(v_toAttributeImplCore_2875_, 1);
lean_inc(v_name_2934_);
lean_dec_ref(v_toAttributeImplCore_2875_);
v___x_2935_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_2934_, v_decl_2876_, v___y_2879_, v___y_2880_);
return v___x_2935_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__0___boxed(lean_object* v_getParam_2940_, lean_object* v_ext_2941_, lean_object* v_afterSet_2942_, lean_object* v_toAttributeImplCore_2943_, lean_object* v_decl_2944_, lean_object* v_stx_2945_, lean_object* v_kind_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_){
_start:
{
uint8_t v_kind_boxed_2950_; lean_object* v_res_2951_; 
v_kind_boxed_2950_ = lean_unbox(v_kind_2946_);
v_res_2951_ = l_Lean_registerParametricAttributeForExt___redArg___lam__0(v_getParam_2940_, v_ext_2941_, v_afterSet_2942_, v_toAttributeImplCore_2943_, v_decl_2944_, v_stx_2945_, v_kind_boxed_2950_, v___y_2947_, v___y_2948_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1(lean_object* v_toAttributeImplCore_2952_, lean_object* v_decl_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_){
_start:
{
lean_object* v_name_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v_name_2957_ = lean_ctor_get(v_toAttributeImplCore_2952_, 1);
lean_inc(v_name_2957_);
lean_dec_ref(v_toAttributeImplCore_2952_);
v___x_2958_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_2959_ = l_Lean_MessageData_ofName(v_name_2957_);
v___x_2960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2958_);
lean_ctor_set(v___x_2960_, 1, v___x_2959_);
v___x_2961_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_2962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2960_);
lean_ctor_set(v___x_2962_, 1, v___x_2961_);
v___x_2963_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_2962_, v___y_2954_, v___y_2955_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed(lean_object* v_toAttributeImplCore_2964_, lean_object* v_decl_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_){
_start:
{
lean_object* v_res_2969_; 
v_res_2969_ = l_Lean_registerParametricAttributeForExt___redArg___lam__1(v_toAttributeImplCore_2964_, v_decl_2965_, v___y_2966_, v___y_2967_);
lean_dec(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec(v_decl_2965_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg(lean_object* v_impl_2970_, lean_object* v_ext_2971_){
_start:
{
lean_object* v_toAttributeImplCore_2973_; lean_object* v_getParam_2974_; lean_object* v_afterSet_2975_; uint8_t v_preserveOrder_2976_; lean_object* v___f_2977_; lean_object* v___f_2978_; lean_object* v_attrImpl_2979_; lean_object* v___x_2980_; 
v_toAttributeImplCore_2973_ = lean_ctor_get(v_impl_2970_, 0);
lean_inc_ref_n(v_toAttributeImplCore_2973_, 3);
v_getParam_2974_ = lean_ctor_get(v_impl_2970_, 1);
lean_inc_ref(v_getParam_2974_);
v_afterSet_2975_ = lean_ctor_get(v_impl_2970_, 2);
lean_inc_ref(v_afterSet_2975_);
v_preserveOrder_2976_ = lean_ctor_get_uint8(v_impl_2970_, sizeof(void*)*4);
lean_dec_ref(v_impl_2970_);
lean_inc_ref(v_ext_2971_);
v___f_2977_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2977_, 0, v_getParam_2974_);
lean_closure_set(v___f_2977_, 1, v_ext_2971_);
lean_closure_set(v___f_2977_, 2, v_afterSet_2975_);
lean_closure_set(v___f_2977_, 3, v_toAttributeImplCore_2973_);
v___f_2978_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed), 5, 1);
lean_closure_set(v___f_2978_, 0, v_toAttributeImplCore_2973_);
v_attrImpl_2979_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_attrImpl_2979_, 0, v_toAttributeImplCore_2973_);
lean_ctor_set(v_attrImpl_2979_, 1, v___f_2977_);
lean_ctor_set(v_attrImpl_2979_, 2, v___f_2978_);
lean_inc_ref(v_attrImpl_2979_);
v___x_2980_ = l_Lean_registerBuiltinAttribute(v_attrImpl_2979_);
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_2988_; 
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_2988_ == 0)
{
lean_object* v_unused_2989_; 
v_unused_2989_ = lean_ctor_get(v___x_2980_, 0);
lean_dec(v_unused_2989_);
v___x_2982_ = v___x_2980_;
v_isShared_2983_ = v_isSharedCheck_2988_;
goto v_resetjp_2981_;
}
else
{
lean_dec(v___x_2980_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_2988_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2984_; lean_object* v___x_2986_; 
v___x_2984_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2984_, 0, v_attrImpl_2979_);
lean_ctor_set(v___x_2984_, 1, v_ext_2971_);
lean_ctor_set_uint8(v___x_2984_, sizeof(void*)*2, v_preserveOrder_2976_);
if (v_isShared_2983_ == 0)
{
lean_ctor_set(v___x_2982_, 0, v___x_2984_);
v___x_2986_ = v___x_2982_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v___x_2984_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
return v___x_2986_;
}
}
}
else
{
lean_object* v_a_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_2997_; 
lean_dec_ref_known(v_attrImpl_2979_, 3);
lean_dec_ref(v_ext_2971_);
v_a_2990_ = lean_ctor_get(v___x_2980_, 0);
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2992_ = v___x_2980_;
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_a_2990_);
lean_dec(v___x_2980_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2995_; 
if (v_isShared_2993_ == 0)
{
v___x_2995_ = v___x_2992_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_a_2990_);
v___x_2995_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
return v___x_2995_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___boxed(lean_object* v_impl_2998_, lean_object* v_ext_2999_, lean_object* v_a_3000_){
_start:
{
lean_object* v_res_3001_; 
v_res_3001_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_2998_, v_ext_2999_);
return v_res_3001_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt(lean_object* v_00_u03b1_3002_, lean_object* v_impl_3003_, lean_object* v_ext_3004_){
_start:
{
lean_object* v___x_3006_; 
v___x_3006_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3003_, v_ext_3004_);
return v___x_3006_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___boxed(lean_object* v_00_u03b1_3007_, lean_object* v_impl_3008_, lean_object* v_ext_3009_, lean_object* v_a_3010_){
_start:
{
lean_object* v_res_3011_; 
v_res_3011_ = l_Lean_registerParametricAttributeForExt(v_00_u03b1_3007_, v_impl_3008_, v_ext_3009_);
return v_res_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg(lean_object* v_impl_3012_){
_start:
{
lean_object* v_toAttributeImplCore_3014_; uint8_t v_preserveOrder_3015_; lean_object* v_filterExport_3016_; lean_object* v_ref_3017_; lean_object* v___x_3018_; 
v_toAttributeImplCore_3014_ = lean_ctor_get(v_impl_3012_, 0);
v_preserveOrder_3015_ = lean_ctor_get_uint8(v_impl_3012_, sizeof(void*)*4);
v_filterExport_3016_ = lean_ctor_get(v_impl_3012_, 3);
v_ref_3017_ = lean_ctor_get(v_toAttributeImplCore_3014_, 0);
lean_inc_ref(v_filterExport_3016_);
lean_inc(v_ref_3017_);
v___x_3018_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_3017_, v_preserveOrder_3015_, v_filterExport_3016_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v_a_3019_; lean_object* v___x_3020_; 
v_a_3019_ = lean_ctor_get(v___x_3018_, 0);
lean_inc(v_a_3019_);
lean_dec_ref_known(v___x_3018_, 1);
v___x_3020_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3012_, v_a_3019_);
return v___x_3020_;
}
else
{
lean_object* v_a_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3028_; 
lean_dec_ref(v_impl_3012_);
v_a_3021_ = lean_ctor_get(v___x_3018_, 0);
v_isSharedCheck_3028_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3023_ = v___x_3018_;
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_a_3021_);
lean_dec(v___x_3018_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v___x_3026_; 
if (v_isShared_3024_ == 0)
{
v___x_3026_ = v___x_3023_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_a_3021_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
return v___x_3026_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___boxed(lean_object* v_impl_3029_, lean_object* v_a_3030_){
_start:
{
lean_object* v_res_3031_; 
v_res_3031_ = l_Lean_registerParametricAttribute___redArg(v_impl_3029_);
return v_res_3031_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute(lean_object* v_00_u03b1_3032_, lean_object* v_impl_3033_){
_start:
{
lean_object* v___x_3035_; 
v___x_3035_ = l_Lean_registerParametricAttribute___redArg(v_impl_3033_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___boxed(lean_object* v_00_u03b1_3036_, lean_object* v_impl_3037_, lean_object* v_a_3038_){
_start:
{
lean_object* v_res_3039_; 
v_res_3039_ = l_Lean_registerParametricAttribute(v_00_u03b1_3036_, v_impl_3037_);
return v_res_3039_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1(lean_object* v_decl_3040_, lean_object* v___x_3041_, lean_object* v___x_3042_, lean_object* v_a_3043_, lean_object* v_x_3044_, lean_object* v___y_3045_){
_start:
{
lean_object* v_fst_3046_; uint8_t v___x_3047_; 
v_fst_3046_ = lean_ctor_get(v_a_3043_, 0);
v___x_3047_ = lean_name_eq(v_fst_3046_, v_decl_3040_);
if (v___x_3047_ == 0)
{
lean_object* v___x_3048_; 
lean_dec_ref(v_a_3043_);
v___x_3048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3041_);
return v___x_3048_;
}
else
{
lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; 
lean_dec_ref(v___x_3041_);
v___x_3049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3049_, 0, v_a_3043_);
v___x_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3050_, 0, v___x_3049_);
v___x_3051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3050_);
lean_ctor_set(v___x_3051_, 1, v___x_3042_);
v___x_3052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3051_);
return v___x_3052_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1___boxed(lean_object* v_decl_3053_, lean_object* v___x_3054_, lean_object* v___x_3055_, lean_object* v_a_3056_, lean_object* v_x_3057_, lean_object* v___y_3058_){
_start:
{
lean_object* v_res_3059_; 
v_res_3059_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1(v_decl_3053_, v___x_3054_, v___x_3055_, v_a_3056_, v_x_3057_, v___y_3058_);
lean_dec_ref(v___y_3058_);
lean_dec(v_decl_3053_);
return v_res_3059_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(lean_object* v_inst_3087_, lean_object* v_ext_3088_, uint8_t v_preserveOrder_3089_, lean_object* v_env_3090_, lean_object* v_decl_3091_){
_start:
{
lean_object* v___y_3093_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3104_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0));
v___x_3105_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3090_, v_decl_3091_);
if (lean_obj_tag(v___x_3105_) == 0)
{
lean_object* v_toEnvExtension_3106_; lean_object* v_asyncMode_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v_snd_3110_; lean_object* v___x_3111_; 
lean_dec(v_inst_3087_);
v_toEnvExtension_3106_ = lean_ctor_get(v_ext_3088_, 0);
v_asyncMode_3107_ = lean_ctor_get(v_toEnvExtension_3106_, 2);
v___x_3108_ = lean_box(0);
v___x_3109_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3104_, v_ext_3088_, v_env_3090_, v_asyncMode_3107_, v___x_3108_);
v_snd_3110_ = lean_ctor_get(v___x_3109_, 1);
lean_inc(v_snd_3110_);
lean_dec(v___x_3109_);
v___x_3111_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3110_, v_decl_3091_);
lean_dec(v_decl_3091_);
lean_dec(v_snd_3110_);
return v___x_3111_;
}
else
{
if (v_preserveOrder_3089_ == 0)
{
lean_object* v_val_3112_; uint8_t v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; uint8_t v___x_3117_; 
v_val_3112_ = lean_ctor_get(v___x_3105_, 0);
lean_inc(v_val_3112_);
lean_dec_ref_known(v___x_3105_, 1);
v___x_3113_ = 0;
v___x_3114_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3104_, v_ext_3088_, v_env_3090_, v_val_3112_, v___x_3113_);
lean_dec(v_val_3112_);
lean_dec_ref(v_env_3090_);
v___x_3115_ = lean_unsigned_to_nat(0u);
v___x_3116_ = lean_array_get_size(v___x_3114_);
v___x_3117_ = lean_nat_dec_lt(v___x_3115_, v___x_3116_);
if (v___x_3117_ == 0)
{
lean_object* v___x_3118_; 
lean_dec_ref(v___x_3114_);
lean_dec(v_decl_3091_);
lean_dec(v_inst_3087_);
v___x_3118_ = lean_box(0);
return v___x_3118_;
}
else
{
lean_object* v___x_3119_; lean_object* v___x_3120_; uint8_t v___x_3121_; 
v___x_3119_ = lean_unsigned_to_nat(1u);
v___x_3120_ = lean_nat_sub(v___x_3116_, v___x_3119_);
v___x_3121_ = lean_nat_dec_le(v___x_3115_, v___x_3120_);
if (v___x_3121_ == 0)
{
lean_object* v___x_3122_; 
lean_dec(v___x_3120_);
lean_dec_ref(v___x_3114_);
lean_dec(v_decl_3091_);
lean_dec(v_inst_3087_);
v___x_3122_ = lean_box(0);
return v___x_3122_;
}
else
{
lean_object* v___f_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___f_3123_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1));
v___x_3124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3124_, 0, v_decl_3091_);
lean_ctor_set(v___x_3124_, 1, v_inst_3087_);
v___x_3125_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2));
v___x_3126_ = l_Array_binSearchAux___redArg(v___f_3123_, v___x_3125_, v___x_3114_, v___x_3124_, v___x_3115_, v___x_3120_);
lean_dec_ref(v___x_3114_);
v___y_3093_ = v___x_3126_;
goto v___jp_3092_;
}
}
}
else
{
lean_object* v_val_3127_; uint8_t v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___f_3134_; size_t v_sz_3135_; size_t v___x_3136_; lean_object* v___x_3137_; lean_object* v_fst_3138_; 
lean_dec(v_inst_3087_);
v_val_3127_ = lean_ctor_get(v___x_3105_, 0);
lean_inc(v_val_3127_);
lean_dec_ref_known(v___x_3105_, 1);
v___x_3128_ = 0;
v___x_3129_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3104_, v_ext_3088_, v_env_3090_, v_val_3127_, v___x_3128_);
lean_dec(v_val_3127_);
lean_dec_ref(v_env_3090_);
v___x_3130_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__12));
v___x_3131_ = lean_box(0);
v___x_3132_ = lean_box(0);
v___x_3133_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__13));
v___f_3134_ = lean_alloc_closure((void*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_3134_, 0, v_decl_3091_);
lean_closure_set(v___f_3134_, 1, v___x_3133_);
lean_closure_set(v___f_3134_, 2, v___x_3132_);
v_sz_3135_ = lean_array_size(v___x_3129_);
v___x_3136_ = ((size_t)0ULL);
v___x_3137_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3130_, v___x_3129_, v___f_3134_, v_sz_3135_, v___x_3136_, v___x_3133_);
v_fst_3138_ = lean_ctor_get(v___x_3137_, 0);
lean_inc(v_fst_3138_);
lean_dec(v___x_3137_);
if (lean_obj_tag(v_fst_3138_) == 0)
{
return v___x_3131_;
}
else
{
lean_object* v_val_3139_; 
v_val_3139_ = lean_ctor_get(v_fst_3138_, 0);
lean_inc(v_val_3139_);
lean_dec_ref_known(v_fst_3138_, 1);
v___y_3093_ = v_val_3139_;
goto v___jp_3092_;
}
}
}
v___jp_3092_:
{
if (lean_obj_tag(v___y_3093_) == 0)
{
lean_object* v___x_3094_; 
v___x_3094_ = lean_box(0);
return v___x_3094_;
}
else
{
lean_object* v_val_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3103_; 
v_val_3095_ = lean_ctor_get(v___y_3093_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___y_3093_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3097_ = v___y_3093_;
v_isShared_3098_ = v_isSharedCheck_3103_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_val_3095_);
lean_dec(v___y_3093_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3103_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v_snd_3099_; lean_object* v___x_3101_; 
v_snd_3099_ = lean_ctor_get(v_val_3095_, 1);
lean_inc(v_snd_3099_);
lean_dec(v_val_3095_);
if (v_isShared_3098_ == 0)
{
lean_ctor_set(v___x_3097_, 0, v_snd_3099_);
v___x_3101_ = v___x_3097_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v_snd_3099_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___boxed(lean_object* v_inst_3140_, lean_object* v_ext_3141_, lean_object* v_preserveOrder_3142_, lean_object* v_env_3143_, lean_object* v_decl_3144_){
_start:
{
uint8_t v_preserveOrder_boxed_3145_; lean_object* v_res_3146_; 
v_preserveOrder_boxed_3145_ = lean_unbox(v_preserveOrder_3142_);
v_res_3146_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3140_, v_ext_3141_, v_preserveOrder_boxed_3145_, v_env_3143_, v_decl_3144_);
lean_dec_ref(v_ext_3141_);
return v_res_3146_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f(lean_object* v_00_u03b1_3147_, lean_object* v_inst_3148_, lean_object* v_ext_3149_, uint8_t v_preserveOrder_3150_, lean_object* v_env_3151_, lean_object* v_decl_3152_){
_start:
{
lean_object* v___x_3153_; 
v___x_3153_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3148_, v_ext_3149_, v_preserveOrder_3150_, v_env_3151_, v_decl_3152_);
return v___x_3153_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___boxed(lean_object* v_00_u03b1_3154_, lean_object* v_inst_3155_, lean_object* v_ext_3156_, lean_object* v_preserveOrder_3157_, lean_object* v_env_3158_, lean_object* v_decl_3159_){
_start:
{
uint8_t v_preserveOrder_boxed_3160_; lean_object* v_res_3161_; 
v_preserveOrder_boxed_3160_ = lean_unbox(v_preserveOrder_3157_);
v_res_3161_ = l_Lean_ParametricAttribute_getParamFromExt_x3f(v_00_u03b1_3154_, v_inst_3155_, v_ext_3156_, v_preserveOrder_boxed_3160_, v_env_3158_, v_decl_3159_);
lean_dec_ref(v_ext_3156_);
return v_res_3161_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object* v_inst_3162_, lean_object* v_attr_3163_, lean_object* v_env_3164_, lean_object* v_decl_3165_){
_start:
{
lean_object* v_ext_3166_; uint8_t v_preserveOrder_3167_; lean_object* v___x_3168_; 
v_ext_3166_ = lean_ctor_get(v_attr_3163_, 1);
v_preserveOrder_3167_ = lean_ctor_get_uint8(v_attr_3163_, sizeof(void*)*2);
v___x_3168_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3162_, v_ext_3166_, v_preserveOrder_3167_, v_env_3164_, v_decl_3165_);
return v___x_3168_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___boxed(lean_object* v_inst_3169_, lean_object* v_attr_3170_, lean_object* v_env_3171_, lean_object* v_decl_3172_){
_start:
{
lean_object* v_res_3173_; 
v_res_3173_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3169_, v_attr_3170_, v_env_3171_, v_decl_3172_);
lean_dec_ref(v_attr_3170_);
return v_res_3173_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f(lean_object* v_00_u03b1_3174_, lean_object* v_inst_3175_, lean_object* v_attr_3176_, lean_object* v_env_3177_, lean_object* v_decl_3178_){
_start:
{
lean_object* v___x_3179_; 
v___x_3179_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3175_, v_attr_3176_, v_env_3177_, v_decl_3178_);
return v___x_3179_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___boxed(lean_object* v_00_u03b1_3180_, lean_object* v_inst_3181_, lean_object* v_attr_3182_, lean_object* v_env_3183_, lean_object* v_decl_3184_){
_start:
{
lean_object* v_res_3185_; 
v_res_3185_ = l_Lean_ParametricAttribute_getParam_x3f(v_00_u03b1_3180_, v_inst_3181_, v_attr_3182_, v_env_3183_, v_decl_3184_);
lean_dec_ref(v_attr_3182_);
return v_res_3185_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt___redArg(lean_object* v_ext_3190_, lean_object* v_attr_3191_, lean_object* v_env_3192_, lean_object* v_decl_3193_, lean_object* v_param_3194_){
_start:
{
lean_object* v___x_3195_; 
v___x_3195_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3192_, v_decl_3193_);
if (lean_obj_tag(v___x_3195_) == 0)
{
lean_object* v_toEnvExtension_3196_; lean_object* v_asyncMode_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v_snd_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3231_; 
v_toEnvExtension_3196_ = lean_ctor_get(v_ext_3190_, 0);
v_asyncMode_3197_ = lean_ctor_get(v_toEnvExtension_3196_, 2);
lean_inc(v_asyncMode_3197_);
v___x_3198_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0));
v___x_3199_ = lean_box(0);
lean_inc_ref(v_env_3192_);
v___x_3200_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3198_, v_ext_3190_, v_env_3192_, v_asyncMode_3197_, v___x_3199_);
v_snd_3201_ = lean_ctor_get(v___x_3200_, 1);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3231_ == 0)
{
lean_object* v_unused_3232_; 
v_unused_3232_ = lean_ctor_get(v___x_3200_, 0);
lean_dec(v_unused_3232_);
v___x_3203_ = v___x_3200_;
v_isShared_3204_ = v_isSharedCheck_3231_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_snd_3201_);
lean_dec(v___x_3200_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3231_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___x_3205_; 
v___x_3205_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3201_, v_decl_3193_);
lean_dec(v_snd_3201_);
if (lean_obj_tag(v___x_3205_) == 0)
{
lean_object* v___x_3207_; 
lean_dec_ref(v_attr_3191_);
if (v_isShared_3204_ == 0)
{
lean_ctor_set(v___x_3203_, 1, v_param_3194_);
lean_ctor_set(v___x_3203_, 0, v_decl_3193_);
v___x_3207_ = v___x_3203_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_decl_3193_);
lean_ctor_set(v_reuseFailAlloc_3210_, 1, v_param_3194_);
v___x_3207_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; 
v___x_3208_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_3190_, v_env_3192_, v___x_3207_, v_asyncMode_3197_, v___x_3199_);
lean_dec(v_asyncMode_3197_);
v___x_3209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3209_, 0, v___x_3208_);
return v___x_3209_;
}
}
else
{
lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3229_; 
lean_del_object(v___x_3203_);
lean_dec(v_asyncMode_3197_);
lean_dec(v_param_3194_);
lean_dec_ref(v_env_3192_);
lean_dec_ref(v_ext_3190_);
v_isSharedCheck_3229_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3229_ == 0)
{
lean_object* v_unused_3230_; 
v_unused_3230_ = lean_ctor_get(v___x_3205_, 0);
lean_dec(v_unused_3230_);
v___x_3212_ = v___x_3205_;
v_isShared_3213_ = v_isSharedCheck_3229_;
goto v_resetjp_3211_;
}
else
{
lean_dec(v___x_3205_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3229_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v_toAttributeImplCore_3214_; lean_object* v_name_3215_; uint8_t v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3227_; 
v_toAttributeImplCore_3214_ = lean_ctor_get(v_attr_3191_, 0);
lean_inc_ref(v_toAttributeImplCore_3214_);
lean_dec_ref(v_attr_3191_);
v_name_3215_ = lean_ctor_get(v_toAttributeImplCore_3214_, 1);
lean_inc(v_name_3215_);
lean_dec_ref(v_toAttributeImplCore_3214_);
v___x_3216_ = 1;
v___x_3217_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0));
v___x_3218_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3215_, v___x_3216_);
v___x_3219_ = lean_string_append(v___x_3217_, v___x_3218_);
lean_dec_ref(v___x_3218_);
v___x_3220_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1));
v___x_3221_ = lean_string_append(v___x_3219_, v___x_3220_);
v___x_3222_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3193_, v___x_3216_);
v___x_3223_ = lean_string_append(v___x_3221_, v___x_3222_);
lean_dec_ref(v___x_3222_);
v___x_3224_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__2));
v___x_3225_ = lean_string_append(v___x_3223_, v___x_3224_);
if (v_isShared_3213_ == 0)
{
lean_ctor_set_tag(v___x_3212_, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3225_);
v___x_3227_ = v___x_3212_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v___x_3225_);
v___x_3227_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
return v___x_3227_;
}
}
}
}
}
else
{
lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3251_; 
lean_dec(v_param_3194_);
lean_dec_ref(v_env_3192_);
lean_dec_ref(v_ext_3190_);
v_isSharedCheck_3251_ = !lean_is_exclusive(v___x_3195_);
if (v_isSharedCheck_3251_ == 0)
{
lean_object* v_unused_3252_; 
v_unused_3252_ = lean_ctor_get(v___x_3195_, 0);
lean_dec(v_unused_3252_);
v___x_3234_ = v___x_3195_;
v_isShared_3235_ = v_isSharedCheck_3251_;
goto v_resetjp_3233_;
}
else
{
lean_dec(v___x_3195_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3251_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v_toAttributeImplCore_3236_; lean_object* v_name_3237_; uint8_t v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3249_; 
v_toAttributeImplCore_3236_ = lean_ctor_get(v_attr_3191_, 0);
lean_inc_ref(v_toAttributeImplCore_3236_);
lean_dec_ref(v_attr_3191_);
v_name_3237_ = lean_ctor_get(v_toAttributeImplCore_3236_, 1);
lean_inc(v_name_3237_);
lean_dec_ref(v_toAttributeImplCore_3236_);
v___x_3238_ = 1;
v___x_3239_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0));
v___x_3240_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3237_, v___x_3238_);
v___x_3241_ = lean_string_append(v___x_3239_, v___x_3240_);
lean_dec_ref(v___x_3240_);
v___x_3242_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1));
v___x_3243_ = lean_string_append(v___x_3241_, v___x_3242_);
v___x_3244_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3193_, v___x_3238_);
v___x_3245_ = lean_string_append(v___x_3243_, v___x_3244_);
lean_dec_ref(v___x_3244_);
v___x_3246_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__3));
v___x_3247_ = lean_string_append(v___x_3245_, v___x_3246_);
if (v_isShared_3235_ == 0)
{
lean_ctor_set_tag(v___x_3234_, 0);
lean_ctor_set(v___x_3234_, 0, v___x_3247_);
v___x_3249_ = v___x_3234_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v___x_3247_);
v___x_3249_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
return v___x_3249_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt(lean_object* v_00_u03b1_3253_, lean_object* v_ext_3254_, lean_object* v_attr_3255_, lean_object* v_env_3256_, lean_object* v_decl_3257_, lean_object* v_param_3258_){
_start:
{
lean_object* v___x_3259_; 
v___x_3259_ = l_Lean_ParametricAttribute_setParamFromExt___redArg(v_ext_3254_, v_attr_3255_, v_env_3256_, v_decl_3257_, v_param_3258_);
return v___x_3259_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object* v_attr_3260_, lean_object* v_env_3261_, lean_object* v_decl_3262_, lean_object* v_param_3263_){
_start:
{
lean_object* v_attr_3264_; lean_object* v_ext_3265_; lean_object* v___x_3266_; 
v_attr_3264_ = lean_ctor_get(v_attr_3260_, 0);
lean_inc_ref(v_attr_3264_);
v_ext_3265_ = lean_ctor_get(v_attr_3260_, 1);
lean_inc_ref(v_ext_3265_);
lean_dec_ref(v_attr_3260_);
v___x_3266_ = l_Lean_ParametricAttribute_setParamFromExt___redArg(v_ext_3265_, v_attr_3264_, v_env_3261_, v_decl_3262_, v_param_3263_);
return v___x_3266_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam(lean_object* v_00_u03b1_3267_, lean_object* v_attr_3268_, lean_object* v_env_3269_, lean_object* v_decl_3270_, lean_object* v_param_3271_){
_start:
{
lean_object* v___x_3272_; 
v___x_3272_ = l_Lean_ParametricAttribute_setParam___redArg(v_attr_3268_, v_env_3269_, v_decl_3270_, v_param_3271_);
return v___x_3272_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__0(lean_object* v_x_3273_, lean_object* v___y_3274_){
_start:
{
lean_object* v___x_3276_; lean_object* v___x_3277_; 
v___x_3276_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_3277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3277_, 0, v___x_3276_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__0___boxed(lean_object* v_x_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_){
_start:
{
lean_object* v_res_3281_; 
v_res_3281_ = l_Lean_instInhabitedEnumAttributes_default___lam__0(v_x_3278_, v___y_3279_);
lean_dec_ref(v___y_3279_);
lean_dec_ref(v_x_3278_);
return v_res_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__1(lean_object* v_s_3282_, lean_object* v_x_3283_){
_start:
{
lean_inc(v_s_3282_);
return v_s_3282_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__1___boxed(lean_object* v_s_3284_, lean_object* v_x_3285_){
_start:
{
lean_object* v_res_3286_; 
v_res_3286_ = l_Lean_instInhabitedEnumAttributes_default___lam__1(v_s_3284_, v_x_3285_);
lean_dec_ref(v_x_3285_);
lean_dec(v_s_3284_);
return v_res_3286_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2(lean_object* v_x_3287_, lean_object* v_x_3288_){
_start:
{
lean_object* v___x_3289_; 
v___x_3289_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__1));
return v___x_3289_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2___boxed(lean_object* v_x_3290_, lean_object* v_x_3291_){
_start:
{
lean_object* v_res_3292_; 
v_res_3292_ = l_Lean_instInhabitedEnumAttributes_default___lam__2(v_x_3290_, v_x_3291_);
lean_dec(v_x_3291_);
lean_dec_ref(v_x_3290_);
return v_res_3292_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__3(void){
_start:
{
lean_object* v___x_3296_; 
v___x_3296_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_3296_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__4(void){
_start:
{
lean_object* v___f_3297_; lean_object* v___f_3298_; lean_object* v___f_3299_; lean_object* v___f_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; 
v___f_3297_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_3298_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__2));
v___f_3299_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__1));
v___f_3300_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__0));
v___x_3301_ = lean_box(0);
v___x_3302_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__3, &l_Lean_instInhabitedEnumAttributes_default___closed__3_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__3);
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
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__5(void){
_start:
{
lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; 
v___x_3304_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__4, &l_Lean_instInhabitedEnumAttributes_default___closed__4_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__4);
v___x_3305_ = lean_box(0);
v___x_3306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3305_);
lean_ctor_set(v___x_3306_, 1, v___x_3304_);
return v___x_3306_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default(lean_object* v_00_u03b1_3307_){
_start:
{
lean_object* v___x_3308_; 
v___x_3308_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__5, &l_Lean_instInhabitedEnumAttributes_default___closed__5_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__5);
return v___x_3308_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes___closed__0(void){
_start:
{
lean_object* v___x_3309_; 
v___x_3309_ = l_Lean_instInhabitedEnumAttributes_default(lean_box(0));
return v___x_3309_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes(lean_object* v_a_3310_){
_start:
{
lean_object* v___x_3311_; 
v___x_3311_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes___closed__0, &l_Lean_instInhabitedEnumAttributes___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes___closed__0);
return v___x_3311_;
}
}
static lean_object* _init_l_Lean_registerEnumAttributes___auto__1(void){
_start:
{
lean_object* v___x_3312_; 
v___x_3312_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0(lean_object* v_x_3313_){
_start:
{
lean_object* v___x_3314_; 
v___x_3314_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
return v___x_3314_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0___boxed(lean_object* v_x_3315_){
_start:
{
lean_object* v_res_3316_; 
v_res_3316_ = l_Lean_registerEnumAttributes___redArg___lam__0(v_x_3315_);
lean_dec(v_x_3315_);
return v_res_3316_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(lean_object* v_newState_3317_, lean_object* v_x_3318_, lean_object* v_x_3319_){
_start:
{
if (lean_obj_tag(v_x_3319_) == 0)
{
return v_x_3318_;
}
else
{
lean_object* v_head_3320_; lean_object* v_tail_3321_; lean_object* v___x_3322_; 
v_head_3320_ = lean_ctor_get(v_x_3319_, 0);
lean_inc(v_head_3320_);
v_tail_3321_ = lean_ctor_get(v_x_3319_, 1);
lean_inc(v_tail_3321_);
lean_dec_ref_known(v_x_3319_, 2);
v___x_3322_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_3317_, v_head_3320_);
if (lean_obj_tag(v___x_3322_) == 1)
{
lean_object* v_val_3323_; lean_object* v___x_3324_; 
v_val_3323_ = lean_ctor_get(v___x_3322_, 0);
lean_inc(v_val_3323_);
lean_dec_ref_known(v___x_3322_, 1);
v___x_3324_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_3320_, v_val_3323_, v_x_3318_);
v_x_3318_ = v___x_3324_;
v_x_3319_ = v_tail_3321_;
goto _start;
}
else
{
lean_dec(v___x_3322_);
lean_dec(v_head_3320_);
v_x_3319_ = v_tail_3321_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg___boxed(lean_object* v_newState_3327_, lean_object* v_x_3328_, lean_object* v_x_3329_){
_start:
{
lean_object* v_res_3330_; 
v_res_3330_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3327_, v_x_3328_, v_x_3329_);
lean_dec(v_newState_3327_);
return v_res_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1(lean_object* v_x_3331_, lean_object* v_newState_3332_, lean_object* v_consts_3333_, lean_object* v_st_3334_){
_start:
{
lean_object* v___x_3335_; 
v___x_3335_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3332_, v_st_3334_, v_consts_3333_);
return v___x_3335_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1___boxed(lean_object* v_x_3336_, lean_object* v_newState_3337_, lean_object* v_consts_3338_, lean_object* v_st_3339_){
_start:
{
lean_object* v_res_3340_; 
v_res_3340_ = l_Lean_registerEnumAttributes___redArg___lam__1(v_x_3336_, v_newState_3337_, v_consts_3338_, v_st_3339_);
lean_dec(v_newState_3337_);
lean_dec(v_x_3336_);
return v_res_3340_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__2(lean_object* v_s_3350_){
_start:
{
lean_object* v___x_3351_; lean_object* v___y_3353_; 
v___x_3351_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___lam__2___closed__3));
if (lean_obj_tag(v_s_3350_) == 0)
{
lean_object* v_size_3357_; 
v_size_3357_ = lean_ctor_get(v_s_3350_, 0);
lean_inc(v_size_3357_);
lean_dec_ref_known(v_s_3350_, 5);
v___y_3353_ = v_size_3357_;
goto v___jp_3352_;
}
else
{
lean_object* v___x_3358_; 
v___x_3358_ = lean_unsigned_to_nat(0u);
v___y_3353_ = v___x_3358_;
goto v___jp_3352_;
}
v___jp_3352_:
{
lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
v___x_3354_ = l_Nat_reprFast(v___y_3353_);
v___x_3355_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3355_, 0, v___x_3354_);
v___x_3356_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3356_, 0, v___x_3351_);
lean_ctor_set(v___x_3356_, 1, v___x_3355_);
return v___x_3356_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(lean_object* v_env_3359_, lean_object* v_as_3360_, size_t v_i_3361_, size_t v_stop_3362_, lean_object* v_b_3363_){
_start:
{
lean_object* v___y_3365_; uint8_t v___x_3369_; 
v___x_3369_ = lean_usize_dec_eq(v_i_3361_, v_stop_3362_);
if (v___x_3369_ == 0)
{
lean_object* v___x_3370_; lean_object* v_fst_3371_; uint8_t v___x_3372_; lean_object* v___x_3373_; uint8_t v___x_3374_; 
v___x_3370_ = lean_array_uget_borrowed(v_as_3360_, v_i_3361_);
v_fst_3371_ = lean_ctor_get(v___x_3370_, 0);
v___x_3372_ = 1;
lean_inc_ref(v_env_3359_);
v___x_3373_ = l_Lean_Environment_setExporting(v_env_3359_, v___x_3372_);
lean_inc(v_fst_3371_);
v___x_3374_ = l_Lean_Environment_contains(v___x_3373_, v_fst_3371_, v___x_3369_);
if (v___x_3374_ == 0)
{
v___y_3365_ = v_b_3363_;
goto v___jp_3364_;
}
else
{
lean_object* v___x_3375_; 
lean_inc(v___x_3370_);
v___x_3375_ = lean_array_push(v_b_3363_, v___x_3370_);
v___y_3365_ = v___x_3375_;
goto v___jp_3364_;
}
}
else
{
lean_dec_ref(v_env_3359_);
return v_b_3363_;
}
v___jp_3364_:
{
size_t v___x_3366_; size_t v___x_3367_; 
v___x_3366_ = ((size_t)1ULL);
v___x_3367_ = lean_usize_add(v_i_3361_, v___x_3366_);
v_i_3361_ = v___x_3367_;
v_b_3363_ = v___y_3365_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg___boxed(lean_object* v_env_3376_, lean_object* v_as_3377_, lean_object* v_i_3378_, lean_object* v_stop_3379_, lean_object* v_b_3380_){
_start:
{
size_t v_i_boxed_3381_; size_t v_stop_boxed_3382_; lean_object* v_res_3383_; 
v_i_boxed_3381_ = lean_unbox_usize(v_i_3378_);
lean_dec(v_i_3378_);
v_stop_boxed_3382_ = lean_unbox_usize(v_stop_3379_);
lean_dec(v_stop_3379_);
v_res_3383_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3376_, v_as_3377_, v_i_boxed_3381_, v_stop_boxed_3382_, v_b_3380_);
lean_dec_ref(v_as_3377_);
return v_res_3383_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3(lean_object* v_env_3384_, lean_object* v_m_3385_){
_start:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___y_3389_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___y_3406_; lean_object* v___y_3407_; uint8_t v___x_3409_; 
v___x_3386_ = lean_unsigned_to_nat(0u);
v___x_3387_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_3403_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v___x_3387_, v_m_3385_);
v___x_3404_ = lean_array_get_size(v___x_3403_);
v___x_3409_ = lean_nat_dec_eq(v___x_3404_, v___x_3386_);
if (v___x_3409_ == 0)
{
lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___y_3413_; uint8_t v___x_3415_; 
v___x_3410_ = lean_unsigned_to_nat(1u);
v___x_3411_ = lean_nat_sub(v___x_3404_, v___x_3410_);
v___x_3415_ = lean_nat_dec_le(v___x_3386_, v___x_3411_);
if (v___x_3415_ == 0)
{
lean_inc(v___x_3411_);
v___y_3413_ = v___x_3411_;
goto v___jp_3412_;
}
else
{
v___y_3413_ = v___x_3386_;
goto v___jp_3412_;
}
v___jp_3412_:
{
uint8_t v___x_3414_; 
v___x_3414_ = lean_nat_dec_le(v___y_3413_, v___x_3411_);
if (v___x_3414_ == 0)
{
lean_dec(v___x_3411_);
lean_inc(v___y_3413_);
v___y_3406_ = v___y_3413_;
v___y_3407_ = v___y_3413_;
goto v___jp_3405_;
}
else
{
v___y_3406_ = v___y_3413_;
v___y_3407_ = v___x_3411_;
goto v___jp_3405_;
}
}
}
else
{
v___y_3389_ = v___x_3403_;
goto v___jp_3388_;
}
v___jp_3388_:
{
lean_object* v___x_3390_; uint8_t v___x_3391_; 
v___x_3390_ = lean_array_get_size(v___y_3389_);
v___x_3391_ = lean_nat_dec_lt(v___x_3386_, v___x_3390_);
if (v___x_3391_ == 0)
{
lean_object* v___x_3392_; 
lean_dec_ref(v_env_3384_);
v___x_3392_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3392_, 0, v___x_3387_);
lean_ctor_set(v___x_3392_, 1, v___x_3387_);
lean_ctor_set(v___x_3392_, 2, v___y_3389_);
return v___x_3392_;
}
else
{
uint8_t v___x_3393_; 
v___x_3393_ = lean_nat_dec_le(v___x_3390_, v___x_3390_);
if (v___x_3393_ == 0)
{
if (v___x_3391_ == 0)
{
lean_object* v___x_3394_; 
lean_dec_ref(v_env_3384_);
v___x_3394_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3394_, 0, v___x_3387_);
lean_ctor_set(v___x_3394_, 1, v___x_3387_);
lean_ctor_set(v___x_3394_, 2, v___y_3389_);
return v___x_3394_;
}
else
{
size_t v___x_3395_; size_t v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; 
v___x_3395_ = ((size_t)0ULL);
v___x_3396_ = lean_usize_of_nat(v___x_3390_);
v___x_3397_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3384_, v___y_3389_, v___x_3395_, v___x_3396_, v___x_3387_);
lean_inc_ref(v___x_3397_);
v___x_3398_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3398_, 0, v___x_3397_);
lean_ctor_set(v___x_3398_, 1, v___x_3397_);
lean_ctor_set(v___x_3398_, 2, v___y_3389_);
return v___x_3398_;
}
}
else
{
size_t v___x_3399_; size_t v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3399_ = ((size_t)0ULL);
v___x_3400_ = lean_usize_of_nat(v___x_3390_);
v___x_3401_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3384_, v___y_3389_, v___x_3399_, v___x_3400_, v___x_3387_);
lean_inc_ref(v___x_3401_);
v___x_3402_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3401_);
lean_ctor_set(v___x_3402_, 1, v___x_3401_);
lean_ctor_set(v___x_3402_, 2, v___y_3389_);
return v___x_3402_;
}
}
}
v___jp_3405_:
{
lean_object* v___x_3408_; 
v___x_3408_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v___x_3404_, v___x_3403_, v___y_3406_, v___y_3407_);
lean_dec(v___y_3407_);
v___y_3389_ = v___x_3408_;
goto v___jp_3388_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3___boxed(lean_object* v_env_3416_, lean_object* v_m_3417_){
_start:
{
lean_object* v_res_3418_; 
v_res_3418_ = l_Lean_registerEnumAttributes___redArg___lam__3(v_env_3416_, v_m_3417_);
lean_dec(v_m_3417_);
return v_res_3418_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__4(lean_object* v_s_3419_, lean_object* v_p_3420_){
_start:
{
lean_object* v_fst_3421_; lean_object* v_snd_3422_; lean_object* v___x_3423_; 
v_fst_3421_ = lean_ctor_get(v_p_3420_, 0);
lean_inc(v_fst_3421_);
v_snd_3422_ = lean_ctor_get(v_p_3420_, 1);
lean_inc(v_snd_3422_);
lean_dec_ref(v_p_3420_);
v___x_3423_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3421_, v_snd_3422_, v_s_3419_);
return v___x_3423_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6(lean_object* v___x_3424_, lean_object* v_x_3425_, lean_object* v_x_3426_){
_start:
{
lean_object* v___x_3428_; 
v___x_3428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3428_, 0, v___x_3424_);
return v___x_3428_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6___boxed(lean_object* v___x_3429_, lean_object* v_x_3430_, lean_object* v_x_3431_, lean_object* v___y_3432_){
_start:
{
lean_object* v_res_3433_; 
v_res_3433_ = l_Lean_registerEnumAttributes___redArg___lam__6(v___x_3429_, v_x_3430_, v_x_3431_);
lean_dec_ref(v_x_3431_);
lean_dec_ref(v_x_3430_);
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3(lean_object* v_as_3434_){
_start:
{
if (lean_obj_tag(v_as_3434_) == 0)
{
lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___x_3436_ = lean_box(0);
v___x_3437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3436_);
return v___x_3437_;
}
else
{
lean_object* v_head_3438_; lean_object* v_tail_3439_; lean_object* v___x_3440_; 
v_head_3438_ = lean_ctor_get(v_as_3434_, 0);
lean_inc(v_head_3438_);
v_tail_3439_ = lean_ctor_get(v_as_3434_, 1);
lean_inc(v_tail_3439_);
lean_dec_ref_known(v_as_3434_, 2);
v___x_3440_ = l_Lean_registerBuiltinAttribute(v_head_3438_);
if (lean_obj_tag(v___x_3440_) == 0)
{
lean_dec_ref_known(v___x_3440_, 1);
v_as_3434_ = v_tail_3439_;
goto _start;
}
else
{
lean_dec(v_tail_3439_);
return v___x_3440_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3___boxed(lean_object* v_as_3442_, lean_object* v___y_3443_){
_start:
{
lean_object* v_res_3444_; 
v_res_3444_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v_as_3442_);
return v_res_3444_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(lean_object* v_validate_3445_, lean_object* v_snd_3446_, lean_object* v_a_3447_, lean_object* v_fst_3448_, lean_object* v_decl_3449_, lean_object* v_stx_3450_, uint8_t v_kind_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_){
_start:
{
lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___x_3498_; 
v___x_3498_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_3450_, v___y_3452_, v___y_3453_);
if (lean_obj_tag(v___x_3498_) == 0)
{
uint8_t v___x_3499_; uint8_t v___x_3500_; 
lean_dec_ref_known(v___x_3498_, 1);
v___x_3499_ = 0;
v___x_3500_ = l_Lean_instBEqAttributeKind_beq(v_kind_3451_, v___x_3499_);
if (v___x_3500_ == 0)
{
lean_object* v___x_3501_; 
lean_dec(v_decl_3449_);
lean_dec_ref(v_a_3447_);
lean_dec(v_snd_3446_);
lean_dec_ref(v_validate_3445_);
v___x_3501_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_fst_3448_, v_kind_3451_, v___y_3452_, v___y_3453_);
return v___x_3501_;
}
else
{
v___y_3492_ = v___y_3452_;
v___y_3493_ = v___y_3453_;
goto v___jp_3491_;
}
}
else
{
lean_dec(v_decl_3449_);
lean_dec(v_fst_3448_);
lean_dec_ref(v_a_3447_);
lean_dec(v_snd_3446_);
lean_dec_ref(v_validate_3445_);
return v___x_3498_;
}
v___jp_3455_:
{
lean_object* v___x_3458_; 
lean_inc(v___y_3457_);
lean_inc_ref(v___y_3456_);
lean_inc(v_snd_3446_);
lean_inc(v_decl_3449_);
v___x_3458_ = lean_apply_5(v_validate_3445_, v_decl_3449_, v_snd_3446_, v___y_3456_, v___y_3457_, lean_box(0));
if (lean_obj_tag(v___x_3458_) == 0)
{
lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3489_; 
v_isSharedCheck_3489_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3489_ == 0)
{
lean_object* v_unused_3490_; 
v_unused_3490_ = lean_ctor_get(v___x_3458_, 0);
lean_dec(v_unused_3490_);
v___x_3460_ = v___x_3458_;
v_isShared_3461_ = v_isSharedCheck_3489_;
goto v_resetjp_3459_;
}
else
{
lean_dec(v___x_3458_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3489_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v___x_3462_; lean_object* v_toEnvExtension_3463_; lean_object* v_env_3464_; lean_object* v_nextMacroScope_3465_; lean_object* v_ngen_3466_; lean_object* v_auxDeclNGen_3467_; lean_object* v_traceState_3468_; lean_object* v_messages_3469_; lean_object* v_infoState_3470_; lean_object* v_snapshotTasks_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3487_; 
v___x_3462_ = lean_st_ref_take(v___y_3457_);
v_toEnvExtension_3463_ = lean_ctor_get(v_a_3447_, 0);
v_env_3464_ = lean_ctor_get(v___x_3462_, 0);
v_nextMacroScope_3465_ = lean_ctor_get(v___x_3462_, 1);
v_ngen_3466_ = lean_ctor_get(v___x_3462_, 2);
v_auxDeclNGen_3467_ = lean_ctor_get(v___x_3462_, 3);
v_traceState_3468_ = lean_ctor_get(v___x_3462_, 4);
v_messages_3469_ = lean_ctor_get(v___x_3462_, 6);
v_infoState_3470_ = lean_ctor_get(v___x_3462_, 7);
v_snapshotTasks_3471_ = lean_ctor_get(v___x_3462_, 8);
v_isSharedCheck_3487_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3487_ == 0)
{
lean_object* v_unused_3488_; 
v_unused_3488_ = lean_ctor_get(v___x_3462_, 5);
lean_dec(v_unused_3488_);
v___x_3473_ = v___x_3462_;
v_isShared_3474_ = v_isSharedCheck_3487_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_snapshotTasks_3471_);
lean_inc(v_infoState_3470_);
lean_inc(v_messages_3469_);
lean_inc(v_traceState_3468_);
lean_inc(v_auxDeclNGen_3467_);
lean_inc(v_ngen_3466_);
lean_inc(v_nextMacroScope_3465_);
lean_inc(v_env_3464_);
lean_dec(v___x_3462_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3487_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v_asyncMode_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3480_; 
v_asyncMode_3475_ = lean_ctor_get(v_toEnvExtension_3463_, 2);
lean_inc(v_asyncMode_3475_);
lean_inc(v_decl_3449_);
v___x_3476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3476_, 0, v_decl_3449_);
lean_ctor_set(v___x_3476_, 1, v_snd_3446_);
v___x_3477_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_3447_, v_env_3464_, v___x_3476_, v_asyncMode_3475_, v_decl_3449_);
lean_dec(v_asyncMode_3475_);
v___x_3478_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_3474_ == 0)
{
lean_ctor_set(v___x_3473_, 5, v___x_3478_);
lean_ctor_set(v___x_3473_, 0, v___x_3477_);
v___x_3480_ = v___x_3473_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v___x_3477_);
lean_ctor_set(v_reuseFailAlloc_3486_, 1, v_nextMacroScope_3465_);
lean_ctor_set(v_reuseFailAlloc_3486_, 2, v_ngen_3466_);
lean_ctor_set(v_reuseFailAlloc_3486_, 3, v_auxDeclNGen_3467_);
lean_ctor_set(v_reuseFailAlloc_3486_, 4, v_traceState_3468_);
lean_ctor_set(v_reuseFailAlloc_3486_, 5, v___x_3478_);
lean_ctor_set(v_reuseFailAlloc_3486_, 6, v_messages_3469_);
lean_ctor_set(v_reuseFailAlloc_3486_, 7, v_infoState_3470_);
lean_ctor_set(v_reuseFailAlloc_3486_, 8, v_snapshotTasks_3471_);
v___x_3480_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3484_; 
v___x_3481_ = lean_st_ref_put(v___y_3457_, v___x_3480_);
v___x_3482_ = lean_box(0);
if (v_isShared_3461_ == 0)
{
lean_ctor_set(v___x_3460_, 0, v___x_3482_);
v___x_3484_ = v___x_3460_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v___x_3482_);
v___x_3484_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
return v___x_3484_;
}
}
}
}
}
else
{
lean_dec(v_decl_3449_);
lean_dec_ref(v_a_3447_);
lean_dec(v_snd_3446_);
return v___x_3458_;
}
}
v___jp_3491_:
{
lean_object* v___x_3494_; lean_object* v_env_3495_; lean_object* v___x_3496_; 
v___x_3494_ = lean_st_ref_get(v___y_3493_);
v_env_3495_ = lean_ctor_get(v___x_3494_, 0);
lean_inc_ref(v_env_3495_);
lean_dec(v___x_3494_);
v___x_3496_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3495_, v_decl_3449_);
lean_dec_ref(v_env_3495_);
if (lean_obj_tag(v___x_3496_) == 0)
{
lean_dec(v_fst_3448_);
v___y_3456_ = v___y_3492_;
v___y_3457_ = v___y_3493_;
goto v___jp_3455_;
}
else
{
lean_object* v___x_3497_; 
lean_dec_ref_known(v___x_3496_, 1);
lean_dec_ref(v_a_3447_);
lean_dec(v_snd_3446_);
lean_dec_ref(v_validate_3445_);
v___x_3497_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_fst_3448_, v_decl_3449_, v___y_3492_, v___y_3493_);
return v___x_3497_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed(lean_object* v_validate_3502_, lean_object* v_snd_3503_, lean_object* v_a_3504_, lean_object* v_fst_3505_, lean_object* v_decl_3506_, lean_object* v_stx_3507_, lean_object* v_kind_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_){
_start:
{
uint8_t v_kind_boxed_3512_; lean_object* v_res_3513_; 
v_kind_boxed_3512_ = lean_unbox(v_kind_3508_);
v_res_3513_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(v_validate_3502_, v_snd_3503_, v_a_3504_, v_fst_3505_, v_decl_3506_, v_stx_3507_, v_kind_boxed_3512_, v___y_3509_, v___y_3510_);
lean_dec(v___y_3510_);
lean_dec_ref(v___y_3509_);
return v_res_3513_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(lean_object* v_fst_3514_, lean_object* v_decl_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_){
_start:
{
lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; 
v___x_3519_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_3520_ = l_Lean_MessageData_ofName(v_fst_3514_);
v___x_3521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3519_);
lean_ctor_set(v___x_3521_, 1, v___x_3520_);
v___x_3522_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_3523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3523_, 0, v___x_3521_);
lean_ctor_set(v___x_3523_, 1, v___x_3522_);
v___x_3524_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_3523_, v___y_3516_, v___y_3517_);
return v___x_3524_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed(lean_object* v_fst_3525_, lean_object* v_decl_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_){
_start:
{
lean_object* v_res_3530_; 
v_res_3530_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(v_fst_3525_, v_decl_3526_, v___y_3527_, v___y_3528_);
lean_dec(v___y_3528_);
lean_dec_ref(v___y_3527_);
lean_dec(v_decl_3526_);
return v_res_3530_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(lean_object* v_validate_3531_, lean_object* v_a_3532_, lean_object* v_ref_3533_, uint8_t v_applicationTime_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_){
_start:
{
if (lean_obj_tag(v_a_3535_) == 0)
{
lean_object* v___x_3537_; 
lean_dec(v_ref_3533_);
lean_dec_ref(v_a_3532_);
lean_dec_ref(v_validate_3531_);
v___x_3537_ = l_List_reverse___redArg(v_a_3536_);
return v___x_3537_;
}
else
{
lean_object* v_head_3538_; lean_object* v_snd_3539_; lean_object* v_tail_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3555_; 
v_head_3538_ = lean_ctor_get(v_a_3535_, 0);
lean_inc(v_head_3538_);
v_snd_3539_ = lean_ctor_get(v_head_3538_, 1);
lean_inc(v_snd_3539_);
v_tail_3540_ = lean_ctor_get(v_a_3535_, 1);
v_isSharedCheck_3555_ = !lean_is_exclusive(v_a_3535_);
if (v_isSharedCheck_3555_ == 0)
{
lean_object* v_unused_3556_; 
v_unused_3556_ = lean_ctor_get(v_a_3535_, 0);
lean_dec(v_unused_3556_);
v___x_3542_ = v_a_3535_;
v_isShared_3543_ = v_isSharedCheck_3555_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_tail_3540_);
lean_dec(v_a_3535_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3555_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v_fst_3544_; lean_object* v_fst_3545_; lean_object* v_snd_3546_; lean_object* v___f_3547_; lean_object* v___f_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3552_; 
v_fst_3544_ = lean_ctor_get(v_head_3538_, 0);
lean_inc_n(v_fst_3544_, 3);
lean_dec(v_head_3538_);
v_fst_3545_ = lean_ctor_get(v_snd_3539_, 0);
lean_inc(v_fst_3545_);
v_snd_3546_ = lean_ctor_get(v_snd_3539_, 1);
lean_inc(v_snd_3546_);
lean_dec(v_snd_3539_);
v___f_3547_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3547_, 0, v_fst_3544_);
lean_inc_ref(v_a_3532_);
lean_inc_ref(v_validate_3531_);
v___f_3548_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3548_, 0, v_validate_3531_);
lean_closure_set(v___f_3548_, 1, v_snd_3546_);
lean_closure_set(v___f_3548_, 2, v_a_3532_);
lean_closure_set(v___f_3548_, 3, v_fst_3544_);
lean_inc(v_ref_3533_);
v___x_3549_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3549_, 0, v_ref_3533_);
lean_ctor_set(v___x_3549_, 1, v_fst_3544_);
lean_ctor_set(v___x_3549_, 2, v_fst_3545_);
lean_ctor_set_uint8(v___x_3549_, sizeof(void*)*3, v_applicationTime_3534_);
v___x_3550_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3550_, 0, v___x_3549_);
lean_ctor_set(v___x_3550_, 1, v___f_3548_);
lean_ctor_set(v___x_3550_, 2, v___f_3547_);
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 1, v_a_3536_);
lean_ctor_set(v___x_3542_, 0, v___x_3550_);
v___x_3552_ = v___x_3542_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v___x_3550_);
lean_ctor_set(v_reuseFailAlloc_3554_, 1, v_a_3536_);
v___x_3552_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
v_a_3535_ = v_tail_3540_;
v_a_3536_ = v___x_3552_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___boxed(lean_object* v_validate_3557_, lean_object* v_a_3558_, lean_object* v_ref_3559_, lean_object* v_applicationTime_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_){
_start:
{
uint8_t v_applicationTime_boxed_3563_; lean_object* v_res_3564_; 
v_applicationTime_boxed_3563_ = lean_unbox(v_applicationTime_3560_);
v_res_3564_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3557_, v_a_3558_, v_ref_3559_, v_applicationTime_boxed_3563_, v_a_3561_, v_a_3562_);
return v_res_3564_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg(lean_object* v_attrDescrs_3578_, lean_object* v_validate_3579_, uint8_t v_applicationTime_3580_, lean_object* v_ref_3581_){
_start:
{
lean_object* v___f_3583_; lean_object* v___f_3584_; lean_object* v___f_3585_; lean_object* v___f_3586_; lean_object* v___f_3587_; lean_object* v___f_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; 
v___f_3583_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__0));
v___f_3584_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__2));
v___f_3585_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__3));
v___f_3586_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__4));
v___f_3587_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__5));
v___f_3588_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__6));
v___x_3589_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__7));
v___x_3590_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__8));
lean_inc(v_ref_3581_);
v___x_3591_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3591_, 0, v_ref_3581_);
lean_ctor_set(v___x_3591_, 1, v___f_3587_);
lean_ctor_set(v___x_3591_, 2, v___f_3588_);
lean_ctor_set(v___x_3591_, 3, v___f_3586_);
lean_ctor_set(v___x_3591_, 4, v___f_3585_);
lean_ctor_set(v___x_3591_, 5, v___f_3584_);
lean_ctor_set(v___x_3591_, 6, v___x_3589_);
lean_ctor_set(v___x_3591_, 7, v___x_3590_);
v___x_3592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3592_, 0, v___x_3591_);
lean_ctor_set(v___x_3592_, 1, v___f_3583_);
v___x_3593_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3592_);
if (lean_obj_tag(v___x_3593_) == 0)
{
lean_object* v_a_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; 
v_a_3594_ = lean_ctor_get(v___x_3593_, 0);
lean_inc_n(v_a_3594_, 2);
lean_dec_ref_known(v___x_3593_, 1);
v___x_3595_ = lean_box(0);
v___x_3596_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3579_, v_a_3594_, v_ref_3581_, v_applicationTime_3580_, v_attrDescrs_3578_, v___x_3595_);
lean_inc(v___x_3596_);
v___x_3597_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v___x_3596_);
if (lean_obj_tag(v___x_3597_) == 0)
{
lean_object* v___x_3599_; uint8_t v_isShared_3600_; uint8_t v_isSharedCheck_3605_; 
v_isSharedCheck_3605_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3605_ == 0)
{
lean_object* v_unused_3606_; 
v_unused_3606_ = lean_ctor_get(v___x_3597_, 0);
lean_dec(v_unused_3606_);
v___x_3599_ = v___x_3597_;
v_isShared_3600_ = v_isSharedCheck_3605_;
goto v_resetjp_3598_;
}
else
{
lean_dec(v___x_3597_);
v___x_3599_ = lean_box(0);
v_isShared_3600_ = v_isSharedCheck_3605_;
goto v_resetjp_3598_;
}
v_resetjp_3598_:
{
lean_object* v___x_3601_; lean_object* v___x_3603_; 
v___x_3601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3601_, 0, v___x_3596_);
lean_ctor_set(v___x_3601_, 1, v_a_3594_);
if (v_isShared_3600_ == 0)
{
lean_ctor_set(v___x_3599_, 0, v___x_3601_);
v___x_3603_ = v___x_3599_;
goto v_reusejp_3602_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v___x_3601_);
v___x_3603_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3602_;
}
v_reusejp_3602_:
{
return v___x_3603_;
}
}
}
else
{
lean_object* v_a_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3614_; 
lean_dec(v___x_3596_);
lean_dec(v_a_3594_);
v_a_3607_ = lean_ctor_get(v___x_3597_, 0);
v_isSharedCheck_3614_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3609_ = v___x_3597_;
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_a_3607_);
lean_dec(v___x_3597_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v___x_3612_; 
if (v_isShared_3610_ == 0)
{
v___x_3612_ = v___x_3609_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_a_3607_);
v___x_3612_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
return v___x_3612_;
}
}
}
}
else
{
lean_object* v_a_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3622_; 
lean_dec(v_ref_3581_);
lean_dec_ref(v_validate_3579_);
lean_dec(v_attrDescrs_3578_);
v_a_3615_ = lean_ctor_get(v___x_3593_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v___x_3593_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3617_ = v___x_3593_;
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_a_3615_);
lean_dec(v___x_3593_);
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
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___boxed(lean_object* v_attrDescrs_3623_, lean_object* v_validate_3624_, lean_object* v_applicationTime_3625_, lean_object* v_ref_3626_, lean_object* v_a_3627_){
_start:
{
uint8_t v_applicationTime_boxed_3628_; lean_object* v_res_3629_; 
v_applicationTime_boxed_3628_ = lean_unbox(v_applicationTime_3625_);
v_res_3629_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3623_, v_validate_3624_, v_applicationTime_boxed_3628_, v_ref_3626_);
return v_res_3629_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes(lean_object* v_00_u03b1_3630_, lean_object* v_attrDescrs_3631_, lean_object* v_validate_3632_, uint8_t v_applicationTime_3633_, lean_object* v_ref_3634_){
_start:
{
lean_object* v___x_3636_; 
v___x_3636_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3631_, v_validate_3632_, v_applicationTime_3633_, v_ref_3634_);
return v___x_3636_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___boxed(lean_object* v_00_u03b1_3637_, lean_object* v_attrDescrs_3638_, lean_object* v_validate_3639_, lean_object* v_applicationTime_3640_, lean_object* v_ref_3641_, lean_object* v_a_3642_){
_start:
{
uint8_t v_applicationTime_boxed_3643_; lean_object* v_res_3644_; 
v_applicationTime_boxed_3643_ = lean_unbox(v_applicationTime_3640_);
v_res_3644_ = l_Lean_registerEnumAttributes(v_00_u03b1_3637_, v_attrDescrs_3638_, v_validate_3639_, v_applicationTime_boxed_3643_, v_ref_3641_);
return v_res_3644_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(lean_object* v_00_u03b1_3645_, lean_object* v_env_3646_, lean_object* v_as_3647_, size_t v_i_3648_, size_t v_stop_3649_, lean_object* v_b_3650_){
_start:
{
lean_object* v___x_3651_; 
v___x_3651_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3646_, v_as_3647_, v_i_3648_, v_stop_3649_, v_b_3650_);
return v___x_3651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___boxed(lean_object* v_00_u03b1_3652_, lean_object* v_env_3653_, lean_object* v_as_3654_, lean_object* v_i_3655_, lean_object* v_stop_3656_, lean_object* v_b_3657_){
_start:
{
size_t v_i_boxed_3658_; size_t v_stop_boxed_3659_; lean_object* v_res_3660_; 
v_i_boxed_3658_ = lean_unbox_usize(v_i_3655_);
lean_dec(v_i_3655_);
v_stop_boxed_3659_ = lean_unbox_usize(v_stop_3656_);
lean_dec(v_stop_3656_);
v_res_3660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(v_00_u03b1_3652_, v_env_3653_, v_as_3654_, v_i_boxed_3658_, v_stop_boxed_3659_, v_b_3657_);
lean_dec_ref(v_as_3654_);
return v_res_3660_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(lean_object* v_00_u03b1_3661_, lean_object* v_newState_3662_, lean_object* v_x_3663_, lean_object* v_x_3664_){
_start:
{
lean_object* v___x_3665_; 
v___x_3665_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3662_, v_x_3663_, v_x_3664_);
return v___x_3665_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___boxed(lean_object* v_00_u03b1_3666_, lean_object* v_newState_3667_, lean_object* v_x_3668_, lean_object* v_x_3669_){
_start:
{
lean_object* v_res_3670_; 
v_res_3670_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(v_00_u03b1_3666_, v_newState_3667_, v_x_3668_, v_x_3669_);
lean_dec(v_newState_3667_);
return v_res_3670_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(lean_object* v_00_u03b1_3671_, lean_object* v_validate_3672_, lean_object* v_a_3673_, lean_object* v_ref_3674_, uint8_t v_applicationTime_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_){
_start:
{
lean_object* v___x_3678_; 
v___x_3678_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3672_, v_a_3673_, v_ref_3674_, v_applicationTime_3675_, v_a_3676_, v_a_3677_);
return v___x_3678_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___boxed(lean_object* v_00_u03b1_3679_, lean_object* v_validate_3680_, lean_object* v_a_3681_, lean_object* v_ref_3682_, lean_object* v_applicationTime_3683_, lean_object* v_a_3684_, lean_object* v_a_3685_){
_start:
{
uint8_t v_applicationTime_boxed_3686_; lean_object* v_res_3687_; 
v_applicationTime_boxed_3686_ = lean_unbox(v_applicationTime_3683_);
v_res_3687_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(v_00_u03b1_3679_, v_validate_3680_, v_a_3681_, v_ref_3682_, v_applicationTime_boxed_3686_, v_a_3684_, v_a_3685_);
return v_res_3687_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue___redArg(lean_object* v_inst_3688_, lean_object* v_attr_3689_, lean_object* v_env_3690_, lean_object* v_decl_3691_){
_start:
{
lean_object* v___x_3692_; lean_object* v___x_3693_; 
v___x_3692_ = lean_box(1);
v___x_3693_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3690_, v_decl_3691_);
if (lean_obj_tag(v___x_3693_) == 0)
{
lean_object* v_ext_3694_; lean_object* v_toEnvExtension_3695_; lean_object* v_asyncMode_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; 
lean_dec(v_inst_3688_);
v_ext_3694_ = lean_ctor_get(v_attr_3689_, 1);
lean_inc_ref(v_ext_3694_);
lean_dec_ref(v_attr_3689_);
v_toEnvExtension_3695_ = lean_ctor_get(v_ext_3694_, 0);
v_asyncMode_3696_ = lean_ctor_get(v_toEnvExtension_3695_, 2);
lean_inc(v_asyncMode_3696_);
lean_inc(v_decl_3691_);
v___x_3697_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3692_, v_ext_3694_, v_env_3690_, v_asyncMode_3696_, v_decl_3691_);
lean_dec(v_asyncMode_3696_);
lean_dec_ref(v_ext_3694_);
v___x_3698_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3697_, v_decl_3691_);
lean_dec(v_decl_3691_);
lean_dec(v___x_3697_);
return v___x_3698_;
}
else
{
lean_object* v_val_3699_; lean_object* v_ext_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3730_; 
v_val_3699_ = lean_ctor_get(v___x_3693_, 0);
lean_inc(v_val_3699_);
lean_dec_ref_known(v___x_3693_, 1);
v_ext_3700_ = lean_ctor_get(v_attr_3689_, 1);
v_isSharedCheck_3730_ = !lean_is_exclusive(v_attr_3689_);
if (v_isSharedCheck_3730_ == 0)
{
lean_object* v_unused_3731_; 
v_unused_3731_ = lean_ctor_get(v_attr_3689_, 0);
lean_dec(v_unused_3731_);
v___x_3702_ = v_attr_3689_;
v_isShared_3703_ = v_isSharedCheck_3730_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_ext_3700_);
lean_dec(v_attr_3689_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3730_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
uint8_t v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; uint8_t v___x_3708_; 
v___x_3704_ = 0;
v___x_3705_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3692_, v_ext_3700_, v_env_3690_, v_val_3699_, v___x_3704_);
lean_dec(v_val_3699_);
lean_dec_ref(v_env_3690_);
lean_dec_ref(v_ext_3700_);
v___x_3706_ = lean_unsigned_to_nat(0u);
v___x_3707_ = lean_array_get_size(v___x_3705_);
v___x_3708_ = lean_nat_dec_lt(v___x_3706_, v___x_3707_);
if (v___x_3708_ == 0)
{
lean_object* v___x_3709_; 
lean_dec_ref(v___x_3705_);
lean_del_object(v___x_3702_);
lean_dec(v_decl_3691_);
lean_dec(v_inst_3688_);
v___x_3709_ = lean_box(0);
return v___x_3709_;
}
else
{
lean_object* v___x_3710_; lean_object* v___x_3711_; uint8_t v___x_3712_; 
v___x_3710_ = lean_unsigned_to_nat(1u);
v___x_3711_ = lean_nat_sub(v___x_3707_, v___x_3710_);
v___x_3712_ = lean_nat_dec_le(v___x_3706_, v___x_3711_);
if (v___x_3712_ == 0)
{
lean_object* v___x_3713_; 
lean_dec(v___x_3711_);
lean_dec_ref(v___x_3705_);
lean_del_object(v___x_3702_);
lean_dec(v_decl_3691_);
lean_dec(v_inst_3688_);
v___x_3713_ = lean_box(0);
return v___x_3713_;
}
else
{
lean_object* v___f_3714_; lean_object* v___x_3716_; 
v___f_3714_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1));
if (v_isShared_3703_ == 0)
{
lean_ctor_set(v___x_3702_, 1, v_inst_3688_);
lean_ctor_set(v___x_3702_, 0, v_decl_3691_);
v___x_3716_ = v___x_3702_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v_decl_3691_);
lean_ctor_set(v_reuseFailAlloc_3729_, 1, v_inst_3688_);
v___x_3716_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
lean_object* v___x_3717_; lean_object* v___x_3718_; 
v___x_3717_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2));
v___x_3718_ = l_Array_binSearchAux___redArg(v___f_3714_, v___x_3717_, v___x_3705_, v___x_3716_, v___x_3706_, v___x_3711_);
lean_dec_ref(v___x_3705_);
if (lean_obj_tag(v___x_3718_) == 0)
{
lean_object* v___x_3719_; 
v___x_3719_ = lean_box(0);
return v___x_3719_;
}
else
{
lean_object* v_val_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3728_; 
v_val_3720_ = lean_ctor_get(v___x_3718_, 0);
v_isSharedCheck_3728_ = !lean_is_exclusive(v___x_3718_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3722_ = v___x_3718_;
v_isShared_3723_ = v_isSharedCheck_3728_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_val_3720_);
lean_dec(v___x_3718_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3728_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v_snd_3724_; lean_object* v___x_3726_; 
v_snd_3724_ = lean_ctor_get(v_val_3720_, 1);
lean_inc(v_snd_3724_);
lean_dec(v_val_3720_);
if (v_isShared_3723_ == 0)
{
lean_ctor_set(v___x_3722_, 0, v_snd_3724_);
v___x_3726_ = v___x_3722_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_snd_3724_);
v___x_3726_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
return v___x_3726_;
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
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue(lean_object* v_00_u03b1_3732_, lean_object* v_inst_3733_, lean_object* v_attr_3734_, lean_object* v_env_3735_, lean_object* v_decl_3736_){
_start:
{
lean_object* v___x_3737_; 
v___x_3737_ = l_Lean_EnumAttributes_getValue___redArg(v_inst_3733_, v_attr_3734_, v_env_3735_, v_decl_3736_);
return v___x_3737_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue___redArg(lean_object* v_attrs_3746_, lean_object* v_env_3747_, lean_object* v_decl_3748_, lean_object* v_val_3749_){
_start:
{
lean_object* v_ext_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3813_; 
v_ext_3750_ = lean_ctor_get(v_attrs_3746_, 1);
v_isSharedCheck_3813_ = !lean_is_exclusive(v_attrs_3746_);
if (v_isSharedCheck_3813_ == 0)
{
lean_object* v_unused_3814_; 
v_unused_3814_ = lean_ctor_get(v_attrs_3746_, 0);
lean_dec(v_unused_3814_);
v___x_3752_ = v_attrs_3746_;
v_isShared_3753_ = v_isSharedCheck_3813_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_ext_3750_);
lean_dec(v_attrs_3746_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3813_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v_toEnvExtension_3754_; lean_object* v_name_3755_; lean_object* v___x_3756_; uint8_t v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v_pfx_3765_; lean_object* v___x_3766_; 
v_toEnvExtension_3754_ = lean_ctor_get(v_ext_3750_, 0);
v_name_3755_ = lean_ctor_get(v_ext_3750_, 1);
v___x_3756_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__0));
v___x_3757_ = 1;
lean_inc(v_name_3755_);
v___x_3758_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3755_, v___x_3757_);
v___x_3759_ = lean_string_append(v___x_3756_, v___x_3758_);
lean_dec_ref(v___x_3758_);
v___x_3760_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__1));
v___x_3761_ = lean_string_append(v___x_3759_, v___x_3760_);
lean_inc(v_decl_3748_);
v___x_3762_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3748_, v___x_3757_);
v___x_3763_ = lean_string_append(v___x_3761_, v___x_3762_);
lean_dec_ref(v___x_3762_);
v___x_3764_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v_pfx_3765_ = lean_string_append(v___x_3763_, v___x_3764_);
v___x_3766_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3747_, v_decl_3748_);
if (lean_obj_tag(v___x_3766_) == 0)
{
lean_object* v_asyncMode_3767_; uint8_t v___x_3768_; 
v_asyncMode_3767_ = lean_ctor_get(v_toEnvExtension_3754_, 2);
lean_inc(v_asyncMode_3767_);
lean_inc(v_decl_3748_);
lean_inc_ref(v_env_3747_);
v___x_3768_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_3747_, v_decl_3748_, v_asyncMode_3767_);
if (v___x_3768_ == 0)
{
lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___y_3772_; lean_object* v___x_3776_; 
lean_dec(v_asyncMode_3767_);
lean_del_object(v___x_3752_);
lean_dec_ref(v_ext_3750_);
lean_dec(v_val_3749_);
lean_dec(v_decl_3748_);
v___x_3769_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__2));
v___x_3770_ = lean_string_append(v_pfx_3765_, v___x_3769_);
v___x_3776_ = l_Lean_Environment_asyncPrefix_x3f(v_env_3747_);
if (lean_obj_tag(v___x_3776_) == 0)
{
lean_object* v___x_3777_; 
v___x_3777_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__3));
v___y_3772_ = v___x_3777_;
goto v___jp_3771_;
}
else
{
lean_object* v_val_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; 
v_val_3778_ = lean_ctor_get(v___x_3776_, 0);
lean_inc(v_val_3778_);
lean_dec_ref_known(v___x_3776_, 1);
v___x_3779_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__4));
v___x_3780_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3778_, v___x_3757_);
v___x_3781_ = l_addParenHeuristic(v___x_3780_);
v___x_3782_ = lean_string_append(v___x_3779_, v___x_3781_);
lean_dec_ref(v___x_3781_);
v___x_3783_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__5));
v___x_3784_ = lean_string_append(v___x_3782_, v___x_3783_);
v___y_3772_ = v___x_3784_;
goto v___jp_3771_;
}
v___jp_3771_:
{
lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; 
v___x_3773_ = lean_string_append(v___x_3770_, v___y_3772_);
lean_dec_ref(v___y_3772_);
v___x_3774_ = lean_string_append(v___x_3773_, v___x_3764_);
v___x_3775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3775_, 0, v___x_3774_);
return v___x_3775_;
}
}
else
{
lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; 
v___x_3785_ = lean_box(1);
lean_inc(v_decl_3748_);
lean_inc_ref(v_env_3747_);
v___x_3786_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3785_, v_ext_3750_, v_env_3747_, v_asyncMode_3767_, v_decl_3748_);
v___x_3787_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3786_, v_decl_3748_);
lean_dec(v___x_3786_);
if (lean_obj_tag(v___x_3787_) == 0)
{
lean_object* v___x_3789_; 
lean_dec_ref(v_pfx_3765_);
lean_inc(v_decl_3748_);
if (v_isShared_3753_ == 0)
{
lean_ctor_set(v___x_3752_, 1, v_val_3749_);
lean_ctor_set(v___x_3752_, 0, v_decl_3748_);
v___x_3789_ = v___x_3752_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v_decl_3748_);
lean_ctor_set(v_reuseFailAlloc_3792_, 1, v_val_3749_);
v___x_3789_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
lean_object* v___x_3790_; lean_object* v___x_3791_; 
v___x_3790_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_3750_, v_env_3747_, v___x_3789_, v_asyncMode_3767_, v_decl_3748_);
lean_dec(v_asyncMode_3767_);
v___x_3791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3791_, 0, v___x_3790_);
return v___x_3791_;
}
}
else
{
lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3801_; 
lean_dec(v_asyncMode_3767_);
lean_del_object(v___x_3752_);
lean_dec_ref(v_ext_3750_);
lean_dec(v_val_3749_);
lean_dec(v_decl_3748_);
lean_dec_ref(v_env_3747_);
v_isSharedCheck_3801_ = !lean_is_exclusive(v___x_3787_);
if (v_isSharedCheck_3801_ == 0)
{
lean_object* v_unused_3802_; 
v_unused_3802_ = lean_ctor_get(v___x_3787_, 0);
lean_dec(v_unused_3802_);
v___x_3794_ = v___x_3787_;
v_isShared_3795_ = v_isSharedCheck_3801_;
goto v_resetjp_3793_;
}
else
{
lean_dec(v___x_3787_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3801_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3799_; 
v___x_3796_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__6));
v___x_3797_ = lean_string_append(v_pfx_3765_, v___x_3796_);
if (v_isShared_3795_ == 0)
{
lean_ctor_set_tag(v___x_3794_, 0);
lean_ctor_set(v___x_3794_, 0, v___x_3797_);
v___x_3799_ = v___x_3794_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v___x_3797_);
v___x_3799_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
return v___x_3799_;
}
}
}
}
}
else
{
lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3811_; 
lean_del_object(v___x_3752_);
lean_dec_ref(v_ext_3750_);
lean_dec(v_val_3749_);
lean_dec(v_decl_3748_);
lean_dec_ref(v_env_3747_);
v_isSharedCheck_3811_ = !lean_is_exclusive(v___x_3766_);
if (v_isSharedCheck_3811_ == 0)
{
lean_object* v_unused_3812_; 
v_unused_3812_ = lean_ctor_get(v___x_3766_, 0);
lean_dec(v_unused_3812_);
v___x_3804_ = v___x_3766_;
v_isShared_3805_ = v_isSharedCheck_3811_;
goto v_resetjp_3803_;
}
else
{
lean_dec(v___x_3766_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3811_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3809_; 
v___x_3806_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__7));
v___x_3807_ = lean_string_append(v_pfx_3765_, v___x_3806_);
if (v_isShared_3805_ == 0)
{
lean_ctor_set_tag(v___x_3804_, 0);
lean_ctor_set(v___x_3804_, 0, v___x_3807_);
v___x_3809_ = v___x_3804_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v___x_3807_);
v___x_3809_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
return v___x_3809_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue(lean_object* v_00_u03b1_3815_, lean_object* v_attrs_3816_, lean_object* v_env_3817_, lean_object* v_decl_3818_, lean_object* v_val_3819_){
_start:
{
lean_object* v___x_3820_; 
v___x_3820_ = l_Lean_EnumAttributes_setValue___redArg(v_attrs_3816_, v_env_3817_, v_decl_3818_, v_val_3819_);
return v___x_3820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; 
v___x_3822_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3823_ = lean_st_mk_ref(v___x_3822_);
v___x_3824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3824_, 0, v___x_3823_);
return v___x_3824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2____boxed(lean_object* v_a_3825_){
_start:
{
lean_object* v_res_3826_; 
v_res_3826_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_();
return v_res_3826_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder(lean_object* v_builderId_3829_, lean_object* v_builder_3830_){
_start:
{
lean_object* v___x_3832_; lean_object* v___x_3833_; uint8_t v___x_3834_; 
v___x_3832_ = l_Lean_attributeImplBuilderTableRef;
v___x_3833_ = lean_st_ref_get(v___x_3832_);
v___x_3834_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_3833_, v_builderId_3829_);
lean_dec(v___x_3833_);
if (v___x_3834_ == 0)
{
lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; 
v___x_3835_ = lean_st_ref_take(v___x_3832_);
v___x_3836_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_3835_, v_builderId_3829_, v_builder_3830_);
v___x_3837_ = lean_st_ref_put(v___x_3832_, v___x_3836_);
v___x_3838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3838_, 0, v___x_3837_);
return v___x_3838_;
}
else
{
lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; 
lean_dec_ref(v_builder_3830_);
v___x_3839_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__0));
v___x_3840_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3829_, v___x_3834_);
v___x_3841_ = lean_string_append(v___x_3839_, v___x_3840_);
lean_dec_ref(v___x_3840_);
v___x_3842_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__1));
v___x_3843_ = lean_string_append(v___x_3841_, v___x_3842_);
v___x_3844_ = lean_mk_io_user_error(v___x_3843_);
v___x_3845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3845_, 0, v___x_3844_);
return v___x_3845_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder___boxed(lean_object* v_builderId_3846_, lean_object* v_builder_3847_, lean_object* v_a_3848_){
_start:
{
lean_object* v_res_3849_; 
v_res_3849_ = l_Lean_registerAttributeImplBuilder(v_builderId_3846_, v_builder_3847_);
return v_res_3849_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(lean_object* v_e_3850_){
_start:
{
if (lean_obj_tag(v_e_3850_) == 0)
{
lean_object* v_a_3852_; lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3860_; 
v_a_3852_ = lean_ctor_get(v_e_3850_, 0);
v_isSharedCheck_3860_ = !lean_is_exclusive(v_e_3850_);
if (v_isSharedCheck_3860_ == 0)
{
v___x_3854_ = v_e_3850_;
v_isShared_3855_ = v_isSharedCheck_3860_;
goto v_resetjp_3853_;
}
else
{
lean_inc(v_a_3852_);
lean_dec(v_e_3850_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3860_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
lean_object* v___x_3856_; lean_object* v___x_3858_; 
v___x_3856_ = lean_mk_io_user_error(v_a_3852_);
if (v_isShared_3855_ == 0)
{
lean_ctor_set_tag(v___x_3854_, 1);
lean_ctor_set(v___x_3854_, 0, v___x_3856_);
v___x_3858_ = v___x_3854_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3859_; 
v_reuseFailAlloc_3859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3859_, 0, v___x_3856_);
v___x_3858_ = v_reuseFailAlloc_3859_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
return v___x_3858_;
}
}
}
else
{
lean_object* v_a_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3868_; 
v_a_3861_ = lean_ctor_get(v_e_3850_, 0);
v_isSharedCheck_3868_ = !lean_is_exclusive(v_e_3850_);
if (v_isSharedCheck_3868_ == 0)
{
v___x_3863_ = v_e_3850_;
v_isShared_3864_ = v_isSharedCheck_3868_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_a_3861_);
lean_dec(v_e_3850_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3868_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
lean_object* v___x_3866_; 
if (v_isShared_3864_ == 0)
{
lean_ctor_set_tag(v___x_3863_, 0);
v___x_3866_ = v___x_3863_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v_a_3861_);
v___x_3866_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
return v___x_3866_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg___boxed(lean_object* v_e_3869_, lean_object* v_a_3870_){
_start:
{
lean_object* v_res_3871_; 
v_res_3871_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3869_);
return v_res_3871_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(lean_object* v_00_u03b1_3872_, lean_object* v_e_3873_){
_start:
{
lean_object* v___x_3875_; 
v___x_3875_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3873_);
return v___x_3875_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___boxed(lean_object* v_00_u03b1_3876_, lean_object* v_e_3877_, lean_object* v_a_3878_){
_start:
{
lean_object* v_res_3879_; 
v_res_3879_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(v_00_u03b1_3876_, v_e_3877_);
return v_res_3879_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(lean_object* v_a_3880_, lean_object* v_x_3881_){
_start:
{
if (lean_obj_tag(v_x_3881_) == 0)
{
lean_object* v___x_3882_; 
v___x_3882_ = lean_box(0);
return v___x_3882_;
}
else
{
lean_object* v_key_3883_; lean_object* v_value_3884_; lean_object* v_tail_3885_; uint8_t v___x_3886_; 
v_key_3883_ = lean_ctor_get(v_x_3881_, 0);
v_value_3884_ = lean_ctor_get(v_x_3881_, 1);
v_tail_3885_ = lean_ctor_get(v_x_3881_, 2);
v___x_3886_ = lean_name_eq(v_key_3883_, v_a_3880_);
if (v___x_3886_ == 0)
{
v_x_3881_ = v_tail_3885_;
goto _start;
}
else
{
lean_object* v___x_3888_; 
lean_inc(v_value_3884_);
v___x_3888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3888_, 0, v_value_3884_);
return v___x_3888_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg___boxed(lean_object* v_a_3889_, lean_object* v_x_3890_){
_start:
{
lean_object* v_res_3891_; 
v_res_3891_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3889_, v_x_3890_);
lean_dec(v_x_3890_);
lean_dec(v_a_3889_);
return v_res_3891_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(lean_object* v_m_3892_, lean_object* v_a_3893_){
_start:
{
lean_object* v_buckets_3894_; lean_object* v___x_3895_; uint64_t v___y_3897_; 
v_buckets_3894_ = lean_ctor_get(v_m_3892_, 1);
v___x_3895_ = lean_array_get_size(v_buckets_3894_);
if (lean_obj_tag(v_a_3893_) == 0)
{
uint64_t v___x_3911_; 
v___x_3911_ = 1723ULL;
v___y_3897_ = v___x_3911_;
goto v___jp_3896_;
}
else
{
uint64_t v_hash_3912_; 
v_hash_3912_ = lean_ctor_get_uint64(v_a_3893_, sizeof(void*)*2);
v___y_3897_ = v_hash_3912_;
goto v___jp_3896_;
}
v___jp_3896_:
{
uint64_t v___x_3898_; uint64_t v___x_3899_; uint64_t v_fold_3900_; uint64_t v___x_3901_; uint64_t v___x_3902_; uint64_t v___x_3903_; size_t v___x_3904_; size_t v___x_3905_; size_t v___x_3906_; size_t v___x_3907_; size_t v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; 
v___x_3898_ = 32ULL;
v___x_3899_ = lean_uint64_shift_right(v___y_3897_, v___x_3898_);
v_fold_3900_ = lean_uint64_xor(v___y_3897_, v___x_3899_);
v___x_3901_ = 16ULL;
v___x_3902_ = lean_uint64_shift_right(v_fold_3900_, v___x_3901_);
v___x_3903_ = lean_uint64_xor(v_fold_3900_, v___x_3902_);
v___x_3904_ = lean_uint64_to_usize(v___x_3903_);
v___x_3905_ = lean_usize_of_nat(v___x_3895_);
v___x_3906_ = ((size_t)1ULL);
v___x_3907_ = lean_usize_sub(v___x_3905_, v___x_3906_);
v___x_3908_ = lean_usize_land(v___x_3904_, v___x_3907_);
v___x_3909_ = lean_array_uget_borrowed(v_buckets_3894_, v___x_3908_);
v___x_3910_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3893_, v___x_3909_);
return v___x_3910_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg___boxed(lean_object* v_m_3913_, lean_object* v_a_3914_){
_start:
{
lean_object* v_res_3915_; 
v_res_3915_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3913_, v_a_3914_);
lean_dec(v_a_3914_);
lean_dec_ref(v_m_3913_);
return v_res_3915_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry(lean_object* v_e_3917_){
_start:
{
lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v_builderId_3921_; lean_object* v_ref_3922_; lean_object* v_args_3923_; lean_object* v___x_3924_; 
v___x_3919_ = l_Lean_attributeImplBuilderTableRef;
v___x_3920_ = lean_st_ref_get(v___x_3919_);
v_builderId_3921_ = lean_ctor_get(v_e_3917_, 0);
lean_inc(v_builderId_3921_);
v_ref_3922_ = lean_ctor_get(v_e_3917_, 1);
lean_inc(v_ref_3922_);
v_args_3923_ = lean_ctor_get(v_e_3917_, 2);
lean_inc(v_args_3923_);
lean_dec_ref(v_e_3917_);
v___x_3924_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_3920_, v_builderId_3921_);
lean_dec(v___x_3920_);
if (lean_obj_tag(v___x_3924_) == 0)
{
lean_object* v___x_3925_; uint8_t v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; 
lean_dec(v_args_3923_);
lean_dec(v_ref_3922_);
v___x_3925_ = ((lean_object*)(l_Lean_mkAttributeImplOfEntry___closed__0));
v___x_3926_ = 1;
v___x_3927_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3921_, v___x_3926_);
v___x_3928_ = lean_string_append(v___x_3925_, v___x_3927_);
lean_dec_ref(v___x_3927_);
v___x_3929_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3930_ = lean_string_append(v___x_3928_, v___x_3929_);
v___x_3931_ = lean_mk_io_user_error(v___x_3930_);
v___x_3932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3932_, 0, v___x_3931_);
return v___x_3932_;
}
else
{
lean_object* v_val_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; 
lean_dec(v_builderId_3921_);
v_val_3933_ = lean_ctor_get(v___x_3924_, 0);
lean_inc(v_val_3933_);
lean_dec_ref_known(v___x_3924_, 1);
v___x_3934_ = lean_apply_2(v_val_3933_, v_ref_3922_, v_args_3923_);
v___x_3935_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v___x_3934_);
return v___x_3935_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry___boxed(lean_object* v_e_3936_, lean_object* v_a_3937_){
_start:
{
lean_object* v_res_3938_; 
v_res_3938_ = l_Lean_mkAttributeImplOfEntry(v_e_3936_);
return v_res_3938_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(lean_object* v_00_u03b2_3939_, lean_object* v_m_3940_, lean_object* v_a_3941_){
_start:
{
lean_object* v___x_3942_; 
v___x_3942_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3940_, v_a_3941_);
return v___x_3942_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___boxed(lean_object* v_00_u03b2_3943_, lean_object* v_m_3944_, lean_object* v_a_3945_){
_start:
{
lean_object* v_res_3946_; 
v_res_3946_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(v_00_u03b2_3943_, v_m_3944_, v_a_3945_);
lean_dec(v_a_3945_);
lean_dec_ref(v_m_3944_);
return v_res_3946_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(lean_object* v_00_u03b2_3947_, lean_object* v_a_3948_, lean_object* v_x_3949_){
_start:
{
lean_object* v___x_3950_; 
v___x_3950_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3948_, v_x_3949_);
return v___x_3950_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3951_, lean_object* v_a_3952_, lean_object* v_x_3953_){
_start:
{
lean_object* v_res_3954_; 
v_res_3954_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(v_00_u03b2_3951_, v_a_3952_, v_x_3953_);
lean_dec(v_x_3953_);
lean_dec(v_a_3952_);
return v_res_3954_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0(void){
_start:
{
lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; 
v___x_3955_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3956_ = lean_box(0);
v___x_3957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3957_, 0, v___x_3956_);
lean_ctor_set(v___x_3957_, 1, v___x_3955_);
return v___x_3957_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default(void){
_start:
{
lean_object* v___x_3958_; 
v___x_3958_ = lean_obj_once(&l_Lean_instInhabitedAttributeExtensionState_default___closed__0, &l_Lean_instInhabitedAttributeExtensionState_default___closed__0_once, _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0);
return v___x_3958_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState(void){
_start:
{
lean_object* v___x_3959_; 
v___x_3959_ = l_Lean_instInhabitedAttributeExtensionState_default;
return v___x_3959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial(){
_start:
{
lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; 
v___x_3961_ = l_Lean_attributeMapRef;
v___x_3962_ = lean_st_ref_get(v___x_3961_);
v___x_3963_ = lean_box(0);
v___x_3964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3964_, 0, v___x_3963_);
lean_ctor_set(v___x_3964_, 1, v___x_3962_);
v___x_3965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3965_, 0, v___x_3964_);
return v___x_3965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed(lean_object* v_a_3966_){
_start:
{
lean_object* v_res_3967_; 
v_res_3967_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial();
return v_res_3967_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe(lean_object* v_env_3973_, lean_object* v_opts_3974_, lean_object* v_declName_3975_){
_start:
{
uint8_t v___x_3978_; lean_object* v___x_3979_; 
v___x_3978_ = 0;
lean_inc(v_declName_3975_);
lean_inc_ref(v_env_3973_);
v___x_3979_ = l_Lean_Environment_find_x3f(v_env_3973_, v_declName_3975_, v___x_3978_);
if (lean_obj_tag(v___x_3979_) == 0)
{
lean_object* v___x_3980_; uint8_t v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; 
lean_dec_ref(v_env_3973_);
v___x_3980_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__2));
v___x_3981_ = 1;
v___x_3982_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_3975_, v___x_3981_);
v___x_3983_ = lean_string_append(v___x_3980_, v___x_3982_);
lean_dec_ref(v___x_3982_);
v___x_3984_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3985_ = lean_string_append(v___x_3983_, v___x_3984_);
v___x_3986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3986_, 0, v___x_3985_);
return v___x_3986_;
}
else
{
lean_object* v_val_3987_; lean_object* v___x_3988_; 
v_val_3987_ = lean_ctor_get(v___x_3979_, 0);
lean_inc(v_val_3987_);
lean_dec_ref_known(v___x_3979_, 1);
v___x_3988_ = l_Lean_ConstantInfo_type(v_val_3987_);
lean_dec(v_val_3987_);
if (lean_obj_tag(v___x_3988_) == 4)
{
lean_object* v_declName_3989_; 
v_declName_3989_ = lean_ctor_get(v___x_3988_, 0);
lean_inc(v_declName_3989_);
lean_dec_ref_known(v___x_3988_, 2);
if (lean_obj_tag(v_declName_3989_) == 1)
{
lean_object* v_pre_3990_; 
v_pre_3990_ = lean_ctor_get(v_declName_3989_, 0);
lean_inc(v_pre_3990_);
if (lean_obj_tag(v_pre_3990_) == 1)
{
lean_object* v_pre_3991_; 
v_pre_3991_ = lean_ctor_get(v_pre_3990_, 0);
if (lean_obj_tag(v_pre_3991_) == 0)
{
lean_object* v_str_3992_; lean_object* v_str_3993_; lean_object* v___x_3994_; uint8_t v___x_3995_; 
v_str_3992_ = lean_ctor_get(v_declName_3989_, 1);
lean_inc_ref(v_str_3992_);
lean_dec_ref_known(v_declName_3989_, 2);
v_str_3993_ = lean_ctor_get(v_pre_3990_, 1);
lean_inc_ref(v_str_3993_);
lean_dec_ref_known(v_pre_3990_, 2);
v___x_3994_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__0));
v___x_3995_ = lean_string_dec_eq(v_str_3993_, v___x_3994_);
lean_dec_ref(v_str_3993_);
if (v___x_3995_ == 0)
{
lean_dec_ref(v_str_3992_);
lean_dec(v_declName_3975_);
lean_dec_ref(v_env_3973_);
goto v___jp_3976_;
}
else
{
lean_object* v___x_3996_; uint8_t v___x_3997_; 
v___x_3996_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__3));
v___x_3997_ = lean_string_dec_eq(v_str_3992_, v___x_3996_);
lean_dec_ref(v_str_3992_);
if (v___x_3997_ == 0)
{
lean_dec(v_declName_3975_);
lean_dec_ref(v_env_3973_);
goto v___jp_3976_;
}
else
{
lean_object* v___x_3998_; 
v___x_3998_ = l_Lean_Environment_evalConst___redArg(v_env_3973_, v_opts_3974_, v_declName_3975_, v___x_3997_);
lean_dec(v_declName_3975_);
lean_dec_ref(v_env_3973_);
return v___x_3998_;
}
}
}
else
{
lean_dec_ref_known(v_pre_3990_, 2);
lean_dec_ref_known(v_declName_3989_, 2);
lean_dec(v_declName_3975_);
lean_dec_ref(v_env_3973_);
goto v___jp_3976_;
}
}
else
{
lean_dec(v_pre_3990_);
lean_dec_ref_known(v_declName_3989_, 2);
lean_dec(v_declName_3975_);
lean_dec_ref(v_env_3973_);
goto v___jp_3976_;
}
}
else
{
lean_dec(v_declName_3989_);
lean_dec(v_declName_3975_);
lean_dec_ref(v_env_3973_);
goto v___jp_3976_;
}
}
else
{
lean_dec_ref(v___x_3988_);
lean_dec(v_declName_3975_);
lean_dec_ref(v_env_3973_);
goto v___jp_3976_;
}
}
v___jp_3976_:
{
lean_object* v___x_3977_; 
v___x_3977_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__1));
return v___x_3977_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___boxed(lean_object* v_env_3999_, lean_object* v_opts_4000_, lean_object* v_declName_4001_){
_start:
{
lean_object* v_res_4002_; 
v_res_4002_ = l_Lean_mkAttributeImplOfConstantUnsafe(v_env_3999_, v_opts_4000_, v_declName_4001_);
lean_dec_ref(v_opts_4000_);
return v_res_4002_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(lean_object* v_as_4003_, size_t v_i_4004_, size_t v_stop_4005_, lean_object* v_b_4006_){
_start:
{
uint8_t v___x_4008_; 
v___x_4008_ = lean_usize_dec_eq(v_i_4004_, v_stop_4005_);
if (v___x_4008_ == 0)
{
lean_object* v___x_4009_; lean_object* v___x_4010_; 
v___x_4009_ = lean_array_uget_borrowed(v_as_4003_, v_i_4004_);
lean_inc(v___x_4009_);
v___x_4010_ = l_Lean_mkAttributeImplOfEntry(v___x_4009_);
if (lean_obj_tag(v___x_4010_) == 0)
{
lean_object* v_a_4011_; lean_object* v_toAttributeImplCore_4012_; lean_object* v_name_4013_; lean_object* v___x_4014_; size_t v___x_4015_; size_t v___x_4016_; 
v_a_4011_ = lean_ctor_get(v___x_4010_, 0);
lean_inc(v_a_4011_);
lean_dec_ref_known(v___x_4010_, 1);
v_toAttributeImplCore_4012_ = lean_ctor_get(v_a_4011_, 0);
v_name_4013_ = lean_ctor_get(v_toAttributeImplCore_4012_, 1);
lean_inc(v_name_4013_);
v___x_4014_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_b_4006_, v_name_4013_, v_a_4011_);
v___x_4015_ = ((size_t)1ULL);
v___x_4016_ = lean_usize_add(v_i_4004_, v___x_4015_);
v_i_4004_ = v___x_4016_;
v_b_4006_ = v___x_4014_;
goto _start;
}
else
{
lean_object* v_a_4018_; lean_object* v___x_4020_; uint8_t v_isShared_4021_; uint8_t v_isSharedCheck_4025_; 
lean_dec_ref(v_b_4006_);
v_a_4018_ = lean_ctor_get(v___x_4010_, 0);
v_isSharedCheck_4025_ = !lean_is_exclusive(v___x_4010_);
if (v_isSharedCheck_4025_ == 0)
{
v___x_4020_ = v___x_4010_;
v_isShared_4021_ = v_isSharedCheck_4025_;
goto v_resetjp_4019_;
}
else
{
lean_inc(v_a_4018_);
lean_dec(v___x_4010_);
v___x_4020_ = lean_box(0);
v_isShared_4021_ = v_isSharedCheck_4025_;
goto v_resetjp_4019_;
}
v_resetjp_4019_:
{
lean_object* v___x_4023_; 
if (v_isShared_4021_ == 0)
{
v___x_4023_ = v___x_4020_;
goto v_reusejp_4022_;
}
else
{
lean_object* v_reuseFailAlloc_4024_; 
v_reuseFailAlloc_4024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4024_, 0, v_a_4018_);
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
else
{
lean_object* v___x_4026_; 
v___x_4026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4026_, 0, v_b_4006_);
return v___x_4026_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg___boxed(lean_object* v_as_4027_, lean_object* v_i_4028_, lean_object* v_stop_4029_, lean_object* v_b_4030_, lean_object* v___y_4031_){
_start:
{
size_t v_i_boxed_4032_; size_t v_stop_boxed_4033_; lean_object* v_res_4034_; 
v_i_boxed_4032_ = lean_unbox_usize(v_i_4028_);
lean_dec(v_i_4028_);
v_stop_boxed_4033_ = lean_unbox_usize(v_stop_4029_);
lean_dec(v_stop_4029_);
v_res_4034_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4027_, v_i_boxed_4032_, v_stop_boxed_4033_, v_b_4030_);
lean_dec_ref(v_as_4027_);
return v_res_4034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(lean_object* v_as_4035_, size_t v_i_4036_, size_t v_stop_4037_, lean_object* v_b_4038_, lean_object* v___y_4039_){
_start:
{
lean_object* v_a_4042_; lean_object* v___y_4047_; uint8_t v___x_4049_; 
v___x_4049_ = lean_usize_dec_eq(v_i_4036_, v_stop_4037_);
if (v___x_4049_ == 0)
{
lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; uint8_t v___x_4053_; 
v___x_4050_ = lean_array_uget_borrowed(v_as_4035_, v_i_4036_);
v___x_4051_ = lean_unsigned_to_nat(0u);
v___x_4052_ = lean_array_get_size(v___x_4050_);
v___x_4053_ = lean_nat_dec_lt(v___x_4051_, v___x_4052_);
if (v___x_4053_ == 0)
{
v_a_4042_ = v_b_4038_;
goto v___jp_4041_;
}
else
{
uint8_t v___x_4054_; 
v___x_4054_ = lean_nat_dec_le(v___x_4052_, v___x_4052_);
if (v___x_4054_ == 0)
{
if (v___x_4053_ == 0)
{
v_a_4042_ = v_b_4038_;
goto v___jp_4041_;
}
else
{
size_t v___x_4055_; size_t v___x_4056_; lean_object* v___x_4057_; 
v___x_4055_ = ((size_t)0ULL);
v___x_4056_ = lean_usize_of_nat(v___x_4052_);
v___x_4057_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_4050_, v___x_4055_, v___x_4056_, v_b_4038_);
v___y_4047_ = v___x_4057_;
goto v___jp_4046_;
}
}
else
{
size_t v___x_4058_; size_t v___x_4059_; lean_object* v___x_4060_; 
v___x_4058_ = ((size_t)0ULL);
v___x_4059_ = lean_usize_of_nat(v___x_4052_);
v___x_4060_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_4050_, v___x_4058_, v___x_4059_, v_b_4038_);
v___y_4047_ = v___x_4060_;
goto v___jp_4046_;
}
}
}
else
{
lean_object* v___x_4061_; 
v___x_4061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4061_, 0, v_b_4038_);
return v___x_4061_;
}
v___jp_4041_:
{
size_t v___x_4043_; size_t v___x_4044_; 
v___x_4043_ = ((size_t)1ULL);
v___x_4044_ = lean_usize_add(v_i_4036_, v___x_4043_);
v_i_4036_ = v___x_4044_;
v_b_4038_ = v_a_4042_;
goto _start;
}
v___jp_4046_:
{
if (lean_obj_tag(v___y_4047_) == 0)
{
lean_object* v_a_4048_; 
v_a_4048_ = lean_ctor_get(v___y_4047_, 0);
lean_inc(v_a_4048_);
lean_dec_ref_known(v___y_4047_, 1);
v_a_4042_ = v_a_4048_;
goto v___jp_4041_;
}
else
{
return v___y_4047_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1___boxed(lean_object* v_as_4062_, lean_object* v_i_4063_, lean_object* v_stop_4064_, lean_object* v_b_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_){
_start:
{
size_t v_i_boxed_4068_; size_t v_stop_boxed_4069_; lean_object* v_res_4070_; 
v_i_boxed_4068_ = lean_unbox_usize(v_i_4063_);
lean_dec(v_i_4063_);
v_stop_boxed_4069_ = lean_unbox_usize(v_stop_4064_);
lean_dec(v_stop_4064_);
v_res_4070_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_as_4062_, v_i_boxed_4068_, v_stop_boxed_4069_, v_b_4065_, v___y_4066_);
lean_dec_ref(v___y_4066_);
lean_dec_ref(v_as_4062_);
return v_res_4070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(lean_object* v_es_4071_, lean_object* v_a_4072_){
_start:
{
lean_object* v_a_4075_; lean_object* v___y_4080_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; uint8_t v___x_4094_; 
v___x_4090_ = l_Lean_attributeMapRef;
v___x_4091_ = lean_st_ref_get(v___x_4090_);
v___x_4092_ = lean_unsigned_to_nat(0u);
v___x_4093_ = lean_array_get_size(v_es_4071_);
v___x_4094_ = lean_nat_dec_lt(v___x_4092_, v___x_4093_);
if (v___x_4094_ == 0)
{
v_a_4075_ = v___x_4091_;
goto v___jp_4074_;
}
else
{
uint8_t v___x_4095_; 
v___x_4095_ = lean_nat_dec_le(v___x_4093_, v___x_4093_);
if (v___x_4095_ == 0)
{
if (v___x_4094_ == 0)
{
v_a_4075_ = v___x_4091_;
goto v___jp_4074_;
}
else
{
size_t v___x_4096_; size_t v___x_4097_; lean_object* v___x_4098_; 
v___x_4096_ = ((size_t)0ULL);
v___x_4097_ = lean_usize_of_nat(v___x_4093_);
v___x_4098_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_4071_, v___x_4096_, v___x_4097_, v___x_4091_, v_a_4072_);
v___y_4080_ = v___x_4098_;
goto v___jp_4079_;
}
}
else
{
size_t v___x_4099_; size_t v___x_4100_; lean_object* v___x_4101_; 
v___x_4099_ = ((size_t)0ULL);
v___x_4100_ = lean_usize_of_nat(v___x_4093_);
v___x_4101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_4071_, v___x_4099_, v___x_4100_, v___x_4091_, v_a_4072_);
v___y_4080_ = v___x_4101_;
goto v___jp_4079_;
}
}
v___jp_4074_:
{
lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4076_ = lean_box(0);
v___x_4077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4077_, 0, v___x_4076_);
lean_ctor_set(v___x_4077_, 1, v_a_4075_);
v___x_4078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4078_, 0, v___x_4077_);
return v___x_4078_;
}
v___jp_4079_:
{
if (lean_obj_tag(v___y_4080_) == 0)
{
lean_object* v_a_4081_; 
v_a_4081_ = lean_ctor_get(v___y_4080_, 0);
lean_inc(v_a_4081_);
lean_dec_ref_known(v___y_4080_, 1);
v_a_4075_ = v_a_4081_;
goto v___jp_4074_;
}
else
{
lean_object* v_a_4082_; lean_object* v___x_4084_; uint8_t v_isShared_4085_; uint8_t v_isSharedCheck_4089_; 
v_a_4082_ = lean_ctor_get(v___y_4080_, 0);
v_isSharedCheck_4089_ = !lean_is_exclusive(v___y_4080_);
if (v_isSharedCheck_4089_ == 0)
{
v___x_4084_ = v___y_4080_;
v_isShared_4085_ = v_isSharedCheck_4089_;
goto v_resetjp_4083_;
}
else
{
lean_inc(v_a_4082_);
lean_dec(v___y_4080_);
v___x_4084_ = lean_box(0);
v_isShared_4085_ = v_isSharedCheck_4089_;
goto v_resetjp_4083_;
}
v_resetjp_4083_:
{
lean_object* v___x_4087_; 
if (v_isShared_4085_ == 0)
{
v___x_4087_ = v___x_4084_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v_a_4082_);
v___x_4087_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
return v___x_4087_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported___boxed(lean_object* v_es_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_){
_start:
{
lean_object* v_res_4105_; 
v_res_4105_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(v_es_4102_, v_a_4103_);
lean_dec_ref(v_a_4103_);
lean_dec_ref(v_es_4102_);
return v_res_4105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(lean_object* v_as_4106_, size_t v_i_4107_, size_t v_stop_4108_, lean_object* v_b_4109_, lean_object* v___y_4110_){
_start:
{
lean_object* v___x_4112_; 
v___x_4112_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4106_, v_i_4107_, v_stop_4108_, v_b_4109_);
return v___x_4112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___boxed(lean_object* v_as_4113_, lean_object* v_i_4114_, lean_object* v_stop_4115_, lean_object* v_b_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_){
_start:
{
size_t v_i_boxed_4119_; size_t v_stop_boxed_4120_; lean_object* v_res_4121_; 
v_i_boxed_4119_ = lean_unbox_usize(v_i_4114_);
lean_dec(v_i_4114_);
v_stop_boxed_4120_ = lean_unbox_usize(v_stop_4115_);
lean_dec(v_stop_4115_);
v_res_4121_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(v_as_4113_, v_i_boxed_4119_, v_stop_boxed_4120_, v_b_4116_, v___y_4117_);
lean_dec_ref(v___y_4117_);
lean_dec_ref(v_as_4113_);
return v_res_4121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_addAttrEntry(lean_object* v_s_4122_, lean_object* v_e_4123_){
_start:
{
lean_object* v_snd_4124_; lean_object* v_toAttributeImplCore_4125_; lean_object* v_fst_4126_; lean_object* v___x_4128_; uint8_t v_isShared_4129_; uint8_t v_isSharedCheck_4144_; 
v_snd_4124_ = lean_ctor_get(v_e_4123_, 1);
lean_inc(v_snd_4124_);
v_toAttributeImplCore_4125_ = lean_ctor_get(v_snd_4124_, 0);
v_fst_4126_ = lean_ctor_get(v_e_4123_, 0);
v_isSharedCheck_4144_ = !lean_is_exclusive(v_e_4123_);
if (v_isSharedCheck_4144_ == 0)
{
lean_object* v_unused_4145_; 
v_unused_4145_ = lean_ctor_get(v_e_4123_, 1);
lean_dec(v_unused_4145_);
v___x_4128_ = v_e_4123_;
v_isShared_4129_ = v_isSharedCheck_4144_;
goto v_resetjp_4127_;
}
else
{
lean_inc(v_fst_4126_);
lean_dec(v_e_4123_);
v___x_4128_ = lean_box(0);
v_isShared_4129_ = v_isSharedCheck_4144_;
goto v_resetjp_4127_;
}
v_resetjp_4127_:
{
lean_object* v_newEntries_4130_; lean_object* v_map_4131_; lean_object* v___x_4133_; uint8_t v_isShared_4134_; uint8_t v_isSharedCheck_4143_; 
v_newEntries_4130_ = lean_ctor_get(v_s_4122_, 0);
v_map_4131_ = lean_ctor_get(v_s_4122_, 1);
v_isSharedCheck_4143_ = !lean_is_exclusive(v_s_4122_);
if (v_isSharedCheck_4143_ == 0)
{
v___x_4133_ = v_s_4122_;
v_isShared_4134_ = v_isSharedCheck_4143_;
goto v_resetjp_4132_;
}
else
{
lean_inc(v_map_4131_);
lean_inc(v_newEntries_4130_);
lean_dec(v_s_4122_);
v___x_4133_ = lean_box(0);
v_isShared_4134_ = v_isSharedCheck_4143_;
goto v_resetjp_4132_;
}
v_resetjp_4132_:
{
lean_object* v_name_4135_; lean_object* v___x_4137_; 
v_name_4135_ = lean_ctor_get(v_toAttributeImplCore_4125_, 1);
lean_inc(v_name_4135_);
if (v_isShared_4129_ == 0)
{
lean_ctor_set_tag(v___x_4128_, 1);
lean_ctor_set(v___x_4128_, 1, v_newEntries_4130_);
v___x_4137_ = v___x_4128_;
goto v_reusejp_4136_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v_fst_4126_);
lean_ctor_set(v_reuseFailAlloc_4142_, 1, v_newEntries_4130_);
v___x_4137_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4136_;
}
v_reusejp_4136_:
{
lean_object* v___x_4138_; lean_object* v___x_4140_; 
v___x_4138_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4131_, v_name_4135_, v_snd_4124_);
if (v_isShared_4134_ == 0)
{
lean_ctor_set(v___x_4133_, 1, v___x_4138_);
lean_ctor_set(v___x_4133_, 0, v___x_4137_);
v___x_4140_ = v___x_4133_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v___x_4137_);
lean_ctor_set(v_reuseFailAlloc_4141_, 1, v___x_4138_);
v___x_4140_ = v_reuseFailAlloc_4141_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
return v___x_4140_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_x_4146_, lean_object* v_s_4147_){
_start:
{
lean_object* v_newEntries_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; 
v_newEntries_4148_ = lean_ctor_get(v_s_4147_, 0);
lean_inc(v_newEntries_4148_);
lean_dec_ref(v_s_4147_);
v___x_4149_ = l_List_reverse___redArg(v_newEntries_4148_);
v___x_4150_ = lean_array_mk(v___x_4149_);
lean_inc_ref_n(v___x_4150_, 2);
v___x_4151_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4151_, 0, v___x_4150_);
lean_ctor_set(v___x_4151_, 1, v___x_4150_);
lean_ctor_set(v___x_4151_, 2, v___x_4150_);
return v___x_4151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_x_4152_, lean_object* v_s_4153_){
_start:
{
lean_object* v_res_4154_; 
v_res_4154_ = l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(v_x_4152_, v_s_4153_);
lean_dec_ref(v_x_4152_);
return v_res_4154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4155_){
_start:
{
lean_object* v_newEntries_4156_; lean_object* v___x_4158_; uint8_t v_isShared_4159_; uint8_t v_isSharedCheck_4167_; 
v_newEntries_4156_ = lean_ctor_get(v_s_4155_, 0);
v_isSharedCheck_4167_ = !lean_is_exclusive(v_s_4155_);
if (v_isSharedCheck_4167_ == 0)
{
lean_object* v_unused_4168_; 
v_unused_4168_ = lean_ctor_get(v_s_4155_, 1);
lean_dec(v_unused_4168_);
v___x_4158_ = v_s_4155_;
v_isShared_4159_ = v_isSharedCheck_4167_;
goto v_resetjp_4157_;
}
else
{
lean_inc(v_newEntries_4156_);
lean_dec(v_s_4155_);
v___x_4158_ = lean_box(0);
v_isShared_4159_ = v_isSharedCheck_4167_;
goto v_resetjp_4157_;
}
v_resetjp_4157_:
{
lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4165_; 
v___x_4160_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__4));
v___x_4161_ = l_List_lengthTR___redArg(v_newEntries_4156_);
lean_dec(v_newEntries_4156_);
v___x_4162_ = l_Nat_reprFast(v___x_4161_);
v___x_4163_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4163_, 0, v___x_4162_);
if (v_isShared_4159_ == 0)
{
lean_ctor_set_tag(v___x_4158_, 5);
lean_ctor_set(v___x_4158_, 1, v___x_4163_);
lean_ctor_set(v___x_4158_, 0, v___x_4160_);
v___x_4165_ = v___x_4158_;
goto v_reusejp_4164_;
}
else
{
lean_object* v_reuseFailAlloc_4166_; 
v_reuseFailAlloc_4166_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4166_, 0, v___x_4160_);
lean_ctor_set(v_reuseFailAlloc_4166_, 1, v___x_4163_);
v___x_4165_ = v_reuseFailAlloc_4166_;
goto v_reusejp_4164_;
}
v_reusejp_4164_:
{
return v___x_4165_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4169_){
_start:
{
lean_object* v_newEntries_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; 
v_newEntries_4170_ = lean_ctor_get(v_s_4169_, 0);
lean_inc(v_newEntries_4170_);
lean_dec_ref(v_s_4169_);
v___x_4171_ = l_List_reverse___redArg(v_newEntries_4170_);
v___x_4172_ = lean_array_mk(v___x_4171_);
return v___x_4172_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___f_4184_; lean_object* v___f_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; 
v___x_4182_ = lean_box(0);
v___x_4183_ = lean_box(2);
v___f_4184_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___f_4185_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4186_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4187_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4188_ = lean_alloc_closure((void*)(l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed), 1, 0);
v___x_4189_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4190_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_4190_, 0, v___x_4189_);
lean_ctor_set(v___x_4190_, 1, v___x_4188_);
lean_ctor_set(v___x_4190_, 2, v___x_4187_);
lean_ctor_set(v___x_4190_, 3, v___x_4186_);
lean_ctor_set(v___x_4190_, 4, v___f_4185_);
lean_ctor_set(v___x_4190_, 5, v___f_4184_);
lean_ctor_set(v___x_4190_, 6, v___x_4183_);
lean_ctor_set(v___x_4190_, 7, v___x_4182_);
return v___x_4190_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; 
v___f_4191_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4192_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4193_, 0, v___x_4192_);
lean_ctor_set(v___x_4193_, 1, v___f_4191_);
return v___x_4193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4195_; lean_object* v___x_4196_; 
v___x_4195_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4196_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_4195_);
return v___x_4196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_a_4197_){
_start:
{
lean_object* v_res_4198_; 
v_res_4198_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_();
return v_res_4198_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute(lean_object* v_n_4199_){
_start:
{
lean_object* v___x_4201_; lean_object* v___x_4202_; uint8_t v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; 
v___x_4201_ = l_Lean_attributeMapRef;
v___x_4202_ = lean_st_ref_get(v___x_4201_);
v___x_4203_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_4202_, v_n_4199_);
lean_dec(v___x_4202_);
v___x_4204_ = lean_box(v___x_4203_);
v___x_4205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4205_, 0, v___x_4204_);
return v___x_4205_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute___boxed(lean_object* v_n_4206_, lean_object* v_a_4207_){
_start:
{
lean_object* v_res_4208_; 
v_res_4208_ = l_Lean_isBuiltinAttribute(v_n_4206_);
lean_dec(v_n_4206_);
return v_res_4208_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(lean_object* v_x_4209_, lean_object* v_x_4210_){
_start:
{
if (lean_obj_tag(v_x_4210_) == 0)
{
return v_x_4209_;
}
else
{
lean_object* v_key_4211_; lean_object* v_tail_4212_; lean_object* v___x_4213_; 
v_key_4211_ = lean_ctor_get(v_x_4210_, 0);
v_tail_4212_ = lean_ctor_get(v_x_4210_, 2);
lean_inc(v_key_4211_);
v___x_4213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4213_, 0, v_key_4211_);
lean_ctor_set(v___x_4213_, 1, v_x_4209_);
v_x_4209_ = v___x_4213_;
v_x_4210_ = v_tail_4212_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0___boxed(lean_object* v_x_4215_, lean_object* v_x_4216_){
_start:
{
lean_object* v_res_4217_; 
v_res_4217_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_x_4215_, v_x_4216_);
lean_dec(v_x_4216_);
return v_res_4217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(lean_object* v_as_4218_, size_t v_i_4219_, size_t v_stop_4220_, lean_object* v_b_4221_){
_start:
{
uint8_t v___x_4222_; 
v___x_4222_ = lean_usize_dec_eq(v_i_4219_, v_stop_4220_);
if (v___x_4222_ == 0)
{
lean_object* v___x_4223_; lean_object* v___x_4224_; size_t v___x_4225_; size_t v___x_4226_; 
v___x_4223_ = lean_array_uget_borrowed(v_as_4218_, v_i_4219_);
v___x_4224_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_b_4221_, v___x_4223_);
v___x_4225_ = ((size_t)1ULL);
v___x_4226_ = lean_usize_add(v_i_4219_, v___x_4225_);
v_i_4219_ = v___x_4226_;
v_b_4221_ = v___x_4224_;
goto _start;
}
else
{
return v_b_4221_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1___boxed(lean_object* v_as_4228_, lean_object* v_i_4229_, lean_object* v_stop_4230_, lean_object* v_b_4231_){
_start:
{
size_t v_i_boxed_4232_; size_t v_stop_boxed_4233_; lean_object* v_res_4234_; 
v_i_boxed_4232_ = lean_unbox_usize(v_i_4229_);
lean_dec(v_i_4229_);
v_stop_boxed_4233_ = lean_unbox_usize(v_stop_4230_);
lean_dec(v_stop_4230_);
v_res_4234_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_as_4228_, v_i_boxed_4232_, v_stop_boxed_4233_, v_b_4231_);
lean_dec_ref(v_as_4228_);
return v_res_4234_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames(){
_start:
{
lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v_buckets_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; uint8_t v___x_4242_; 
v___x_4236_ = l_Lean_attributeMapRef;
v___x_4237_ = lean_st_ref_get(v___x_4236_);
v_buckets_4238_ = lean_ctor_get(v___x_4237_, 1);
lean_inc_ref(v_buckets_4238_);
lean_dec(v___x_4237_);
v___x_4239_ = lean_box(0);
v___x_4240_ = lean_unsigned_to_nat(0u);
v___x_4241_ = lean_array_get_size(v_buckets_4238_);
v___x_4242_ = lean_nat_dec_lt(v___x_4240_, v___x_4241_);
if (v___x_4242_ == 0)
{
lean_object* v___x_4243_; 
lean_dec_ref(v_buckets_4238_);
v___x_4243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4243_, 0, v___x_4239_);
return v___x_4243_;
}
else
{
size_t v___x_4244_; size_t v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; 
v___x_4244_ = ((size_t)0ULL);
v___x_4245_ = lean_usize_of_nat(v___x_4241_);
v___x_4246_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4238_, v___x_4244_, v___x_4245_, v___x_4239_);
lean_dec_ref(v_buckets_4238_);
v___x_4247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4247_, 0, v___x_4246_);
return v___x_4247_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames___boxed(lean_object* v_a_4248_){
_start:
{
lean_object* v_res_4249_; 
v_res_4249_ = l_Lean_getBuiltinAttributeNames();
return v_res_4249_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl(lean_object* v_attrName_4251_){
_start:
{
lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; 
v___x_4253_ = l_Lean_attributeMapRef;
v___x_4254_ = lean_st_ref_get(v___x_4253_);
v___x_4255_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_4254_, v_attrName_4251_);
lean_dec(v___x_4254_);
if (lean_obj_tag(v___x_4255_) == 0)
{
lean_object* v___x_4256_; uint8_t v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; 
v___x_4256_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4257_ = 1;
v___x_4258_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4251_, v___x_4257_);
v___x_4259_ = lean_string_append(v___x_4256_, v___x_4258_);
lean_dec_ref(v___x_4258_);
v___x_4260_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4261_ = lean_string_append(v___x_4259_, v___x_4260_);
v___x_4262_ = lean_mk_io_user_error(v___x_4261_);
v___x_4263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4263_, 0, v___x_4262_);
return v___x_4263_;
}
else
{
lean_object* v_val_4264_; lean_object* v___x_4266_; uint8_t v_isShared_4267_; uint8_t v_isSharedCheck_4271_; 
lean_dec(v_attrName_4251_);
v_val_4264_ = lean_ctor_get(v___x_4255_, 0);
v_isSharedCheck_4271_ = !lean_is_exclusive(v___x_4255_);
if (v_isSharedCheck_4271_ == 0)
{
v___x_4266_ = v___x_4255_;
v_isShared_4267_ = v_isSharedCheck_4271_;
goto v_resetjp_4265_;
}
else
{
lean_inc(v_val_4264_);
lean_dec(v___x_4255_);
v___x_4266_ = lean_box(0);
v_isShared_4267_ = v_isSharedCheck_4271_;
goto v_resetjp_4265_;
}
v_resetjp_4265_:
{
lean_object* v___x_4269_; 
if (v_isShared_4267_ == 0)
{
lean_ctor_set_tag(v___x_4266_, 0);
v___x_4269_ = v___x_4266_;
goto v_reusejp_4268_;
}
else
{
lean_object* v_reuseFailAlloc_4270_; 
v_reuseFailAlloc_4270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4270_, 0, v_val_4264_);
v___x_4269_ = v_reuseFailAlloc_4270_;
goto v_reusejp_4268_;
}
v_reusejp_4268_:
{
return v___x_4269_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl___boxed(lean_object* v_attrName_4272_, lean_object* v_a_4273_){
_start:
{
lean_object* v_res_4274_; 
v_res_4274_ = l_Lean_getBuiltinAttributeImpl(v_attrName_4272_);
return v_res_4274_;
}
}
LEAN_EXPORT uint8_t l_Lean_isAttribute(lean_object* v_env_4275_, lean_object* v_attrName_4276_){
_start:
{
lean_object* v___x_4277_; lean_object* v_toEnvExtension_4278_; lean_object* v_asyncMode_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v_map_4283_; uint8_t v___x_4284_; 
v___x_4277_ = l_Lean_attributeExtension;
v_toEnvExtension_4278_ = lean_ctor_get(v___x_4277_, 0);
v_asyncMode_4279_ = lean_ctor_get(v_toEnvExtension_4278_, 2);
v___x_4280_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4281_ = lean_box(0);
v___x_4282_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4280_, v___x_4277_, v_env_4275_, v_asyncMode_4279_, v___x_4281_);
v_map_4283_ = lean_ctor_get(v___x_4282_, 1);
lean_inc_ref(v_map_4283_);
lean_dec(v___x_4282_);
v___x_4284_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4283_, v_attrName_4276_);
lean_dec_ref(v_map_4283_);
return v___x_4284_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAttribute___boxed(lean_object* v_env_4285_, lean_object* v_attrName_4286_){
_start:
{
uint8_t v_res_4287_; lean_object* v_r_4288_; 
v_res_4287_ = l_Lean_isAttribute(v_env_4285_, v_attrName_4286_);
lean_dec(v_attrName_4286_);
v_r_4288_ = lean_box(v_res_4287_);
return v_r_4288_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeNames(lean_object* v_env_4289_){
_start:
{
lean_object* v___x_4290_; lean_object* v_toEnvExtension_4291_; lean_object* v_asyncMode_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v_map_4296_; lean_object* v_buckets_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; uint8_t v___x_4301_; 
v___x_4290_ = l_Lean_attributeExtension;
v_toEnvExtension_4291_ = lean_ctor_get(v___x_4290_, 0);
v_asyncMode_4292_ = lean_ctor_get(v_toEnvExtension_4291_, 2);
v___x_4293_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4294_ = lean_box(0);
v___x_4295_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4293_, v___x_4290_, v_env_4289_, v_asyncMode_4292_, v___x_4294_);
v_map_4296_ = lean_ctor_get(v___x_4295_, 1);
lean_inc_ref(v_map_4296_);
lean_dec(v___x_4295_);
v_buckets_4297_ = lean_ctor_get(v_map_4296_, 1);
lean_inc_ref(v_buckets_4297_);
lean_dec_ref(v_map_4296_);
v___x_4298_ = lean_box(0);
v___x_4299_ = lean_unsigned_to_nat(0u);
v___x_4300_ = lean_array_get_size(v_buckets_4297_);
v___x_4301_ = lean_nat_dec_lt(v___x_4299_, v___x_4300_);
if (v___x_4301_ == 0)
{
lean_dec_ref(v_buckets_4297_);
return v___x_4298_;
}
else
{
size_t v___x_4302_; size_t v___x_4303_; lean_object* v___x_4304_; 
v___x_4302_ = ((size_t)0ULL);
v___x_4303_ = lean_usize_of_nat(v___x_4300_);
v___x_4304_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4297_, v___x_4302_, v___x_4303_, v___x_4298_);
lean_dec_ref(v_buckets_4297_);
return v___x_4304_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeImpl(lean_object* v_env_4305_, lean_object* v_attrName_4306_){
_start:
{
lean_object* v___x_4307_; lean_object* v_toEnvExtension_4308_; lean_object* v_asyncMode_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v_map_4313_; lean_object* v___x_4314_; 
v___x_4307_ = l_Lean_attributeExtension;
v_toEnvExtension_4308_ = lean_ctor_get(v___x_4307_, 0);
v_asyncMode_4309_ = lean_ctor_get(v_toEnvExtension_4308_, 2);
v___x_4310_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4311_ = lean_box(0);
v___x_4312_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4310_, v___x_4307_, v_env_4305_, v_asyncMode_4309_, v___x_4311_);
v_map_4313_ = lean_ctor_get(v___x_4312_, 1);
lean_inc_ref(v_map_4313_);
lean_dec(v___x_4312_);
v___x_4314_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_map_4313_, v_attrName_4306_);
lean_dec_ref(v_map_4313_);
if (lean_obj_tag(v___x_4314_) == 0)
{
lean_object* v___x_4315_; uint8_t v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; 
v___x_4315_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4316_ = 1;
v___x_4317_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4306_, v___x_4316_);
v___x_4318_ = lean_string_append(v___x_4315_, v___x_4317_);
lean_dec_ref(v___x_4317_);
v___x_4319_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4320_ = lean_string_append(v___x_4318_, v___x_4319_);
v___x_4321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4321_, 0, v___x_4320_);
return v___x_4321_;
}
else
{
lean_object* v_val_4322_; lean_object* v___x_4324_; uint8_t v_isShared_4325_; uint8_t v_isSharedCheck_4329_; 
lean_dec(v_attrName_4306_);
v_val_4322_ = lean_ctor_get(v___x_4314_, 0);
v_isSharedCheck_4329_ = !lean_is_exclusive(v___x_4314_);
if (v_isSharedCheck_4329_ == 0)
{
v___x_4324_ = v___x_4314_;
v_isShared_4325_ = v_isSharedCheck_4329_;
goto v_resetjp_4323_;
}
else
{
lean_inc(v_val_4322_);
lean_dec(v___x_4314_);
v___x_4324_ = lean_box(0);
v_isShared_4325_ = v_isSharedCheck_4329_;
goto v_resetjp_4323_;
}
v_resetjp_4323_:
{
lean_object* v___x_4327_; 
if (v_isShared_4325_ == 0)
{
v___x_4327_ = v___x_4324_;
goto v_reusejp_4326_;
}
else
{
lean_object* v_reuseFailAlloc_4328_; 
v_reuseFailAlloc_4328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4328_, 0, v_val_4322_);
v___x_4327_ = v_reuseFailAlloc_4328_;
goto v_reusejp_4326_;
}
v_reusejp_4326_:
{
return v___x_4327_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder(lean_object* v_env_4330_, lean_object* v_builderId_4331_, lean_object* v_ref_4332_, lean_object* v_args_4333_){
_start:
{
lean_object* v_entry_4335_; lean_object* v___x_4336_; 
v_entry_4335_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_entry_4335_, 0, v_builderId_4331_);
lean_ctor_set(v_entry_4335_, 1, v_ref_4332_);
lean_ctor_set(v_entry_4335_, 2, v_args_4333_);
lean_inc_ref(v_entry_4335_);
v___x_4336_ = l_Lean_mkAttributeImplOfEntry(v_entry_4335_);
if (lean_obj_tag(v___x_4336_) == 0)
{
lean_object* v_a_4337_; lean_object* v___x_4339_; uint8_t v_isShared_4340_; uint8_t v_isSharedCheck_4362_; 
v_a_4337_ = lean_ctor_get(v___x_4336_, 0);
v_isSharedCheck_4362_ = !lean_is_exclusive(v___x_4336_);
if (v_isSharedCheck_4362_ == 0)
{
v___x_4339_ = v___x_4336_;
v_isShared_4340_ = v_isSharedCheck_4362_;
goto v_resetjp_4338_;
}
else
{
lean_inc(v_a_4337_);
lean_dec(v___x_4336_);
v___x_4339_ = lean_box(0);
v_isShared_4340_ = v_isSharedCheck_4362_;
goto v_resetjp_4338_;
}
v_resetjp_4338_:
{
lean_object* v_toAttributeImplCore_4341_; lean_object* v_name_4342_; uint8_t v___x_4343_; 
v_toAttributeImplCore_4341_ = lean_ctor_get(v_a_4337_, 0);
v_name_4342_ = lean_ctor_get(v_toAttributeImplCore_4341_, 1);
lean_inc_ref(v_env_4330_);
v___x_4343_ = l_Lean_isAttribute(v_env_4330_, v_name_4342_);
if (v___x_4343_ == 0)
{
lean_object* v___x_4344_; lean_object* v_toEnvExtension_4345_; lean_object* v_asyncMode_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4351_; 
v___x_4344_ = l_Lean_attributeExtension;
v_toEnvExtension_4345_ = lean_ctor_get(v___x_4344_, 0);
v_asyncMode_4346_ = lean_ctor_get(v_toEnvExtension_4345_, 2);
v___x_4347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4347_, 0, v_entry_4335_);
lean_ctor_set(v___x_4347_, 1, v_a_4337_);
v___x_4348_ = lean_box(0);
v___x_4349_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_4344_, v_env_4330_, v___x_4347_, v_asyncMode_4346_, v___x_4348_);
if (v_isShared_4340_ == 0)
{
lean_ctor_set(v___x_4339_, 0, v___x_4349_);
v___x_4351_ = v___x_4339_;
goto v_reusejp_4350_;
}
else
{
lean_object* v_reuseFailAlloc_4352_; 
v_reuseFailAlloc_4352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4352_, 0, v___x_4349_);
v___x_4351_ = v_reuseFailAlloc_4352_;
goto v_reusejp_4350_;
}
v_reusejp_4350_:
{
return v___x_4351_;
}
}
else
{
lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4360_; 
lean_inc(v_name_4342_);
lean_dec(v_a_4337_);
lean_dec_ref_known(v_entry_4335_, 3);
lean_dec_ref(v_env_4330_);
v___x_4353_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_4354_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4342_, v___x_4343_);
v___x_4355_ = lean_string_append(v___x_4353_, v___x_4354_);
lean_dec_ref(v___x_4354_);
v___x_4356_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_4357_ = lean_string_append(v___x_4355_, v___x_4356_);
v___x_4358_ = lean_mk_io_user_error(v___x_4357_);
if (v_isShared_4340_ == 0)
{
lean_ctor_set_tag(v___x_4339_, 1);
lean_ctor_set(v___x_4339_, 0, v___x_4358_);
v___x_4360_ = v___x_4339_;
goto v_reusejp_4359_;
}
else
{
lean_object* v_reuseFailAlloc_4361_; 
v_reuseFailAlloc_4361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4361_, 0, v___x_4358_);
v___x_4360_ = v_reuseFailAlloc_4361_;
goto v_reusejp_4359_;
}
v_reusejp_4359_:
{
return v___x_4360_;
}
}
}
}
else
{
lean_object* v_a_4363_; lean_object* v___x_4365_; uint8_t v_isShared_4366_; uint8_t v_isSharedCheck_4370_; 
lean_dec_ref_known(v_entry_4335_, 3);
lean_dec_ref(v_env_4330_);
v_a_4363_ = lean_ctor_get(v___x_4336_, 0);
v_isSharedCheck_4370_ = !lean_is_exclusive(v___x_4336_);
if (v_isSharedCheck_4370_ == 0)
{
v___x_4365_ = v___x_4336_;
v_isShared_4366_ = v_isSharedCheck_4370_;
goto v_resetjp_4364_;
}
else
{
lean_inc(v_a_4363_);
lean_dec(v___x_4336_);
v___x_4365_ = lean_box(0);
v_isShared_4366_ = v_isSharedCheck_4370_;
goto v_resetjp_4364_;
}
v_resetjp_4364_:
{
lean_object* v___x_4368_; 
if (v_isShared_4366_ == 0)
{
v___x_4368_ = v___x_4365_;
goto v_reusejp_4367_;
}
else
{
lean_object* v_reuseFailAlloc_4369_; 
v_reuseFailAlloc_4369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4369_, 0, v_a_4363_);
v___x_4368_ = v_reuseFailAlloc_4369_;
goto v_reusejp_4367_;
}
v_reusejp_4367_:
{
return v___x_4368_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___boxed(lean_object* v_env_4371_, lean_object* v_builderId_4372_, lean_object* v_ref_4373_, lean_object* v_args_4374_, lean_object* v_a_4375_){
_start:
{
lean_object* v_res_4376_; 
v_res_4376_ = l_Lean_registerAttributeOfBuilder(v_env_4371_, v_builderId_4372_, v_ref_4373_, v_args_4374_);
return v_res_4376_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(lean_object* v_x_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_){
_start:
{
if (lean_obj_tag(v_x_4377_) == 0)
{
lean_object* v_a_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; 
v_a_4381_ = lean_ctor_get(v_x_4377_, 0);
lean_inc(v_a_4381_);
lean_dec_ref_known(v_x_4377_, 1);
v___x_4382_ = l_Lean_stringToMessageData(v_a_4381_);
v___x_4383_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_4382_, v___y_4378_, v___y_4379_);
return v___x_4383_;
}
else
{
lean_object* v_a_4384_; lean_object* v___x_4386_; uint8_t v_isShared_4387_; uint8_t v_isSharedCheck_4391_; 
v_a_4384_ = lean_ctor_get(v_x_4377_, 0);
v_isSharedCheck_4391_ = !lean_is_exclusive(v_x_4377_);
if (v_isSharedCheck_4391_ == 0)
{
v___x_4386_ = v_x_4377_;
v_isShared_4387_ = v_isSharedCheck_4391_;
goto v_resetjp_4385_;
}
else
{
lean_inc(v_a_4384_);
lean_dec(v_x_4377_);
v___x_4386_ = lean_box(0);
v_isShared_4387_ = v_isSharedCheck_4391_;
goto v_resetjp_4385_;
}
v_resetjp_4385_:
{
lean_object* v___x_4389_; 
if (v_isShared_4387_ == 0)
{
lean_ctor_set_tag(v___x_4386_, 0);
v___x_4389_ = v___x_4386_;
goto v_reusejp_4388_;
}
else
{
lean_object* v_reuseFailAlloc_4390_; 
v_reuseFailAlloc_4390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4390_, 0, v_a_4384_);
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
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg___boxed(lean_object* v_x_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_){
_start:
{
lean_object* v_res_4396_; 
v_res_4396_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4392_, v___y_4393_, v___y_4394_);
lean_dec(v___y_4394_);
lean_dec_ref(v___y_4393_);
return v_res_4396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add(lean_object* v_declName_4397_, lean_object* v_attrName_4398_, lean_object* v_stx_4399_, uint8_t v_kind_4400_, lean_object* v_a_4401_, lean_object* v_a_4402_){
_start:
{
lean_object* v___x_4404_; lean_object* v_env_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; 
v___x_4404_ = lean_st_ref_get(v_a_4402_);
v_env_4405_ = lean_ctor_get(v___x_4404_, 0);
lean_inc_ref(v_env_4405_);
lean_dec(v___x_4404_);
v___x_4406_ = l_Lean_getAttributeImpl(v_env_4405_, v_attrName_4398_);
v___x_4407_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4406_, v_a_4401_, v_a_4402_);
if (lean_obj_tag(v___x_4407_) == 0)
{
lean_object* v_a_4408_; lean_object* v_add_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; 
v_a_4408_ = lean_ctor_get(v___x_4407_, 0);
lean_inc(v_a_4408_);
lean_dec_ref_known(v___x_4407_, 1);
v_add_4409_ = lean_ctor_get(v_a_4408_, 1);
lean_inc_ref(v_add_4409_);
lean_dec(v_a_4408_);
v___x_4410_ = lean_box(v_kind_4400_);
lean_inc(v_a_4402_);
lean_inc_ref(v_a_4401_);
v___x_4411_ = lean_apply_6(v_add_4409_, v_declName_4397_, v_stx_4399_, v___x_4410_, v_a_4401_, v_a_4402_, lean_box(0));
return v___x_4411_;
}
else
{
lean_object* v_a_4412_; lean_object* v___x_4414_; uint8_t v_isShared_4415_; uint8_t v_isSharedCheck_4419_; 
lean_dec(v_stx_4399_);
lean_dec(v_declName_4397_);
v_a_4412_ = lean_ctor_get(v___x_4407_, 0);
v_isSharedCheck_4419_ = !lean_is_exclusive(v___x_4407_);
if (v_isSharedCheck_4419_ == 0)
{
v___x_4414_ = v___x_4407_;
v_isShared_4415_ = v_isSharedCheck_4419_;
goto v_resetjp_4413_;
}
else
{
lean_inc(v_a_4412_);
lean_dec(v___x_4407_);
v___x_4414_ = lean_box(0);
v_isShared_4415_ = v_isSharedCheck_4419_;
goto v_resetjp_4413_;
}
v_resetjp_4413_:
{
lean_object* v___x_4417_; 
if (v_isShared_4415_ == 0)
{
v___x_4417_ = v___x_4414_;
goto v_reusejp_4416_;
}
else
{
lean_object* v_reuseFailAlloc_4418_; 
v_reuseFailAlloc_4418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4418_, 0, v_a_4412_);
v___x_4417_ = v_reuseFailAlloc_4418_;
goto v_reusejp_4416_;
}
v_reusejp_4416_:
{
return v___x_4417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add___boxed(lean_object* v_declName_4420_, lean_object* v_attrName_4421_, lean_object* v_stx_4422_, lean_object* v_kind_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_, lean_object* v_a_4426_){
_start:
{
uint8_t v_kind_boxed_4427_; lean_object* v_res_4428_; 
v_kind_boxed_4427_ = lean_unbox(v_kind_4423_);
v_res_4428_ = l_Lean_Attribute_add(v_declName_4420_, v_attrName_4421_, v_stx_4422_, v_kind_boxed_4427_, v_a_4424_, v_a_4425_);
lean_dec(v_a_4425_);
lean_dec_ref(v_a_4424_);
return v_res_4428_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(lean_object* v_00_u03b1_4429_, lean_object* v_x_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_){
_start:
{
lean_object* v___x_4434_; 
v___x_4434_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4430_, v___y_4431_, v___y_4432_);
return v___x_4434_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___boxed(lean_object* v_00_u03b1_4435_, lean_object* v_x_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_){
_start:
{
lean_object* v_res_4440_; 
v_res_4440_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(v_00_u03b1_4435_, v_x_4436_, v___y_4437_, v___y_4438_);
lean_dec(v___y_4438_);
lean_dec_ref(v___y_4437_);
return v_res_4440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase(lean_object* v_declName_4441_, lean_object* v_attrName_4442_, lean_object* v_a_4443_, lean_object* v_a_4444_){
_start:
{
lean_object* v___x_4446_; lean_object* v_env_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; 
v___x_4446_ = lean_st_ref_get(v_a_4444_);
v_env_4447_ = lean_ctor_get(v___x_4446_, 0);
lean_inc_ref(v_env_4447_);
lean_dec(v___x_4446_);
v___x_4448_ = l_Lean_getAttributeImpl(v_env_4447_, v_attrName_4442_);
v___x_4449_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4448_, v_a_4443_, v_a_4444_);
if (lean_obj_tag(v___x_4449_) == 0)
{
lean_object* v_a_4450_; lean_object* v_erase_4451_; lean_object* v___x_4452_; 
v_a_4450_ = lean_ctor_get(v___x_4449_, 0);
lean_inc(v_a_4450_);
lean_dec_ref_known(v___x_4449_, 1);
v_erase_4451_ = lean_ctor_get(v_a_4450_, 2);
lean_inc_ref(v_erase_4451_);
lean_dec(v_a_4450_);
lean_inc(v_a_4444_);
lean_inc_ref(v_a_4443_);
v___x_4452_ = lean_apply_4(v_erase_4451_, v_declName_4441_, v_a_4443_, v_a_4444_, lean_box(0));
return v___x_4452_;
}
else
{
lean_object* v_a_4453_; lean_object* v___x_4455_; uint8_t v_isShared_4456_; uint8_t v_isSharedCheck_4460_; 
lean_dec(v_declName_4441_);
v_a_4453_ = lean_ctor_get(v___x_4449_, 0);
v_isSharedCheck_4460_ = !lean_is_exclusive(v___x_4449_);
if (v_isSharedCheck_4460_ == 0)
{
v___x_4455_ = v___x_4449_;
v_isShared_4456_ = v_isSharedCheck_4460_;
goto v_resetjp_4454_;
}
else
{
lean_inc(v_a_4453_);
lean_dec(v___x_4449_);
v___x_4455_ = lean_box(0);
v_isShared_4456_ = v_isSharedCheck_4460_;
goto v_resetjp_4454_;
}
v_resetjp_4454_:
{
lean_object* v___x_4458_; 
if (v_isShared_4456_ == 0)
{
v___x_4458_ = v___x_4455_;
goto v_reusejp_4457_;
}
else
{
lean_object* v_reuseFailAlloc_4459_; 
v_reuseFailAlloc_4459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4459_, 0, v_a_4453_);
v___x_4458_ = v_reuseFailAlloc_4459_;
goto v_reusejp_4457_;
}
v_reusejp_4457_:
{
return v___x_4458_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase___boxed(lean_object* v_declName_4461_, lean_object* v_attrName_4462_, lean_object* v_a_4463_, lean_object* v_a_4464_, lean_object* v_a_4465_){
_start:
{
lean_object* v_res_4466_; 
v_res_4466_ = l_Lean_Attribute_erase(v_declName_4461_, v_attrName_4462_, v_a_4463_, v_a_4464_);
lean_dec(v_a_4464_);
lean_dec_ref(v_a_4463_);
return v_res_4466_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(lean_object* v_x_4467_, lean_object* v_x_4468_){
_start:
{
if (lean_obj_tag(v_x_4468_) == 0)
{
return v_x_4467_;
}
else
{
lean_object* v_key_4469_; lean_object* v_value_4470_; lean_object* v_tail_4471_; lean_object* v_newEntries_4472_; lean_object* v_map_4473_; uint8_t v___x_4474_; 
v_key_4469_ = lean_ctor_get(v_x_4468_, 0);
lean_inc(v_key_4469_);
v_value_4470_ = lean_ctor_get(v_x_4468_, 1);
lean_inc(v_value_4470_);
v_tail_4471_ = lean_ctor_get(v_x_4468_, 2);
lean_inc(v_tail_4471_);
lean_dec_ref_known(v_x_4468_, 3);
v_newEntries_4472_ = lean_ctor_get(v_x_4467_, 0);
v_map_4473_ = lean_ctor_get(v_x_4467_, 1);
v___x_4474_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4473_, v_key_4469_);
if (v___x_4474_ == 0)
{
lean_object* v___x_4476_; uint8_t v_isShared_4477_; uint8_t v_isSharedCheck_4483_; 
lean_inc_ref(v_map_4473_);
lean_inc(v_newEntries_4472_);
v_isSharedCheck_4483_ = !lean_is_exclusive(v_x_4467_);
if (v_isSharedCheck_4483_ == 0)
{
lean_object* v_unused_4484_; lean_object* v_unused_4485_; 
v_unused_4484_ = lean_ctor_get(v_x_4467_, 1);
lean_dec(v_unused_4484_);
v_unused_4485_ = lean_ctor_get(v_x_4467_, 0);
lean_dec(v_unused_4485_);
v___x_4476_ = v_x_4467_;
v_isShared_4477_ = v_isSharedCheck_4483_;
goto v_resetjp_4475_;
}
else
{
lean_dec(v_x_4467_);
v___x_4476_ = lean_box(0);
v_isShared_4477_ = v_isSharedCheck_4483_;
goto v_resetjp_4475_;
}
v_resetjp_4475_:
{
lean_object* v___x_4478_; lean_object* v___x_4480_; 
v___x_4478_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4473_, v_key_4469_, v_value_4470_);
if (v_isShared_4477_ == 0)
{
lean_ctor_set(v___x_4476_, 1, v___x_4478_);
v___x_4480_ = v___x_4476_;
goto v_reusejp_4479_;
}
else
{
lean_object* v_reuseFailAlloc_4482_; 
v_reuseFailAlloc_4482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4482_, 0, v_newEntries_4472_);
lean_ctor_set(v_reuseFailAlloc_4482_, 1, v___x_4478_);
v___x_4480_ = v_reuseFailAlloc_4482_;
goto v_reusejp_4479_;
}
v_reusejp_4479_:
{
v_x_4467_ = v___x_4480_;
v_x_4468_ = v_tail_4471_;
goto _start;
}
}
}
else
{
lean_dec(v_value_4470_);
lean_dec(v_key_4469_);
v_x_4468_ = v_tail_4471_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(lean_object* v_as_4487_, size_t v_i_4488_, size_t v_stop_4489_, lean_object* v_b_4490_){
_start:
{
uint8_t v___x_4491_; 
v___x_4491_ = lean_usize_dec_eq(v_i_4488_, v_stop_4489_);
if (v___x_4491_ == 0)
{
lean_object* v___x_4492_; lean_object* v___x_4493_; size_t v___x_4494_; size_t v___x_4495_; 
v___x_4492_ = lean_array_uget_borrowed(v_as_4487_, v_i_4488_);
lean_inc(v___x_4492_);
v___x_4493_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(v_b_4490_, v___x_4492_);
v___x_4494_ = ((size_t)1ULL);
v___x_4495_ = lean_usize_add(v_i_4488_, v___x_4494_);
v_i_4488_ = v___x_4495_;
v_b_4490_ = v___x_4493_;
goto _start;
}
else
{
return v_b_4490_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1___boxed(lean_object* v_as_4497_, lean_object* v_i_4498_, lean_object* v_stop_4499_, lean_object* v_b_4500_){
_start:
{
size_t v_i_boxed_4501_; size_t v_stop_boxed_4502_; lean_object* v_res_4503_; 
v_i_boxed_4501_ = lean_unbox_usize(v_i_4498_);
lean_dec(v_i_4498_);
v_stop_boxed_4502_ = lean_unbox_usize(v_stop_4499_);
lean_dec(v_stop_4499_);
v_res_4503_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_as_4497_, v_i_boxed_4501_, v_stop_boxed_4502_, v_b_4500_);
lean_dec_ref(v_as_4497_);
return v_res_4503_;
}
}
LEAN_EXPORT lean_object* lean_update_env_attributes(lean_object* v_env_4504_){
_start:
{
lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___y_4510_; lean_object* v_toEnvExtension_4513_; lean_object* v_asyncMode_4514_; lean_object* v_buckets_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; uint8_t v___x_4521_; 
v___x_4506_ = l_Lean_attributeMapRef;
v___x_4507_ = lean_st_ref_get(v___x_4506_);
v___x_4508_ = l_Lean_attributeExtension;
v_toEnvExtension_4513_ = lean_ctor_get(v___x_4508_, 0);
v_asyncMode_4514_ = lean_ctor_get(v_toEnvExtension_4513_, 2);
v_buckets_4515_ = lean_ctor_get(v___x_4507_, 1);
lean_inc_ref(v_buckets_4515_);
lean_dec(v___x_4507_);
v___x_4516_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4517_ = lean_box(0);
lean_inc_ref(v_env_4504_);
v___x_4518_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4516_, v___x_4508_, v_env_4504_, v_asyncMode_4514_, v___x_4517_);
v___x_4519_ = lean_unsigned_to_nat(0u);
v___x_4520_ = lean_array_get_size(v_buckets_4515_);
v___x_4521_ = lean_nat_dec_lt(v___x_4519_, v___x_4520_);
if (v___x_4521_ == 0)
{
lean_dec_ref(v_buckets_4515_);
v___y_4510_ = v___x_4518_;
goto v___jp_4509_;
}
else
{
size_t v___x_4522_; size_t v___x_4523_; lean_object* v___x_4524_; 
v___x_4522_ = ((size_t)0ULL);
v___x_4523_ = lean_usize_of_nat(v___x_4520_);
v___x_4524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_buckets_4515_, v___x_4522_, v___x_4523_, v___x_4518_);
lean_dec_ref(v_buckets_4515_);
v___y_4510_ = v___x_4524_;
goto v___jp_4509_;
}
v___jp_4509_:
{
lean_object* v___x_4511_; lean_object* v___x_4512_; 
v___x_4511_ = l_Lean_PersistentEnvExtension_setState___redArg(v___x_4508_, v_env_4504_, v___y_4510_);
v___x_4512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4512_, 0, v___x_4511_);
return v___x_4512_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___boxed(lean_object* v_env_4525_, lean_object* v_a_4526_){
_start:
{
lean_object* v_res_4527_; 
v_res_4527_ = lean_update_env_attributes(v_env_4525_);
return v_res_4527_;
}
}
LEAN_EXPORT lean_object* lean_get_num_attributes(){
_start:
{
lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v_size_4531_; lean_object* v___x_4532_; 
v___x_4529_ = l_Lean_attributeMapRef;
v___x_4530_ = lean_st_ref_get(v___x_4529_);
v_size_4531_ = lean_ctor_get(v___x_4530_, 0);
lean_inc(v_size_4531_);
lean_dec(v___x_4530_);
v___x_4532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4532_, 0, v_size_4531_);
return v___x_4532_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNumBuiltinAttributesImpl___boxed(lean_object* v_a_4533_){
_start:
{
lean_object* v_res_4534_; 
v_res_4534_ = lean_get_num_attributes();
return v_res_4534_;
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
